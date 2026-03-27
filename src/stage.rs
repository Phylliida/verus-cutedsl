/// Stage-based GPU kernel composition with explicit barriers.
///
/// Models a GPU kernel as a tree of barrier-separated parallel operations.
/// This is **phase-based verification** — each barrier interval is verified
/// independently for race-freedom, and Hoare-style invariants at barrier
/// points provide compositional functional correctness.
///
/// Key design decisions:
/// - Barriers are **explicit** (developer-placed), not implicit between stages.
///   Adjacent Maps without a Barrier fuse — no sync overhead.
/// - Barriers are **workgroup-scoped** by default (~20 cycles). Grid scope
///   available for rare cooperative-groups use cases.
/// - `Map` and `Scan` are atomic proof-level statements. Their internal
///   thread-level correctness (scatter injectivity, scan algorithm correctness)
///   is established separately in KernelSpec / scan proofs.
///
/// Literature basis:
/// - GPUVerify (Betts et al., OOPSLA 2012) — barrier-interval analysis
/// - Barrier Invariants (Chong et al., OOPSLA 2013) — Hoare-style predicates at barriers
/// - Kojima & Igarashi (ACM TOCL 2017) — full Hoare logic for SIMT programs
/// - Faial (Cogumbreiro et al., CAV 2021) — compositional per-phase analysis

use vstd::prelude::*;
use crate::arith_expr::*;
use crate::kernel::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Shared state model
// ══════════════════════════════════════════════════════════════

/// Shared state: a collection of named integer buffers.
/// This models both shared memory and global memory visible to a workgroup.
/// Each buffer is a Seq<int> indexed by position.
pub struct SharedState {
    pub buffers: Seq<Seq<int>>,
    pub workgroup_size: nat,
}

impl SharedState {
    pub open spec fn num_buffers(&self) -> nat {
        self.buffers.len()
    }

    pub open spec fn buffer_len(&self, buf: nat) -> nat
        recommends buf < self.num_buffers(),
    {
        self.buffers[buf as int].len()
    }

    /// Read a value from a buffer.
    pub open spec fn read(&self, buf: nat, idx: nat) -> int
        recommends buf < self.num_buffers(), idx < self.buffer_len(buf),
    {
        self.buffers[buf as int][idx as int]
    }

    /// Write a value to a buffer, producing a new state.
    pub open spec fn write(&self, buf: nat, idx: nat, val: int) -> SharedState
        recommends buf < self.num_buffers(), idx < self.buffer_len(buf),
    {
        SharedState {
            buffers: self.buffers.update(buf as int,
                self.buffers[buf as int].update(idx as int, val)),
            workgroup_size: self.workgroup_size,
        }
    }

    /// Bulk-update a buffer with a complete new sequence.
    pub open spec fn set_buffer(&self, buf: nat, data: Seq<int>) -> SharedState
        recommends buf < self.num_buffers(),
    {
        SharedState {
            buffers: self.buffers.update(buf as int, data),
            workgroup_size: self.workgroup_size,
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Barrier scope
// ══════════════════════════════════════════════════════════════

/// Scope of a barrier synchronization.
pub enum BarrierScope {
    /// Workgroup-level barrier (__syncthreads / workgroupBarrier).
    /// All threads in the workgroup must reach this point before any proceeds.
    /// Cheap (~20 cycles). The default and common case.
    Workgroup,
    /// Grid-level barrier (cooperative groups grid_group::sync).
    /// All threads in the entire dispatch must synchronize.
    /// Expensive. Requires cooperative kernel launch. Rare.
    Grid,
}

// ══════════════════════════════════════════════════════════════
// Stage: composable kernel building block
// ══════════════════════════════════════════════════════════════

/// A GPU kernel as a tree of composable stages.
///
/// Barriers are explicit — the developer places them where cross-thread
/// communication occurs. Adjacent Maps without a Barrier between them
/// fuse with no synchronization overhead.
///
/// Verification is compositional:
/// - Between barriers: race-freedom (scatter injectivity from KernelSpec)
/// - At barriers: Hoare-style invariants (StatePredicate)
/// - Loops: inductive invariants checked at barriers inside the body
pub enum Stage {
    /// Parallel map: each thread `t` in `[0, workgroup_size)` where `guard(t) != 0`
    /// writes `compute(t)` to `output_buf[scatter(t)]` for each output.
    ///
    /// Uses the existing verified KernelSpec. Scatter injectivity guarantees
    /// no data races within a single Map.
    ///
    /// `input_bufs` maps KernelSpec's logical input array indices to SharedState buffer indices.
    /// `output_bufs` maps KernelSpec's logical output indices to SharedState buffer indices.
    Map {
        spec: KernelSpec,
        input_bufs: Seq<nat>,
        output_bufs: Seq<nat>,
    },

    /// Parallel inclusive prefix sum on a buffer.
    ///
    /// Replaces `buffer[i]` with `buffer[0] + buffer[1] + ... + buffer[i]`.
    /// Uses existing verified scan algorithms (Hillis-Steele, Blelloch, Brent-Kung).
    /// The scan is an atomic operation — internal barrier management is encapsulated.
    Scan {
        buffer: nat,
    },

    /// Explicit barrier with a postcondition (invariant) on shared state.
    ///
    /// This is the ONLY synchronization point in the model. After a barrier,
    /// all prior writes by all threads in the scope are visible to all threads.
    ///
    /// The `post` predicate must hold after the barrier — this is the Hoare-logic
    /// assertion that enables compositional verification.
    Barrier {
        scope: BarrierScope,
        post: spec_fn(SharedState) -> bool,
    },

    /// Sequential composition. Stages execute in order.
    ///
    /// **No implicit barriers** between stages. Adjacent Maps without an
    /// intervening Barrier are fused — data flows thread-locally.
    /// The developer must insert Barrier stages where cross-thread
    /// communication occurs.
    Seq {
        stages: Seq<Stage>,
    },

    /// Bounded loop. The body executes `bound` times.
    ///
    /// `bound` is evaluated once from the initial state before the loop starts.
    /// The `invariant` is an inductive predicate checked at Barrier stages
    /// inside the body: it must hold initially and be preserved by each iteration.
    ///
    /// Note: no data-dependent early exit. If needed, add LoopWhile variant later.
    Loop {
        bound: nat,
        body: Box<Stage>,
        invariant: spec_fn(SharedState, nat) -> bool,
    },
}

// ══════════════════════════════════════════════════════════════
// Stage evaluation semantics
// ══════════════════════════════════════════════════════════════

/// Apply a single Map stage to the shared state.
///
/// For each thread `t` in `[0, workgroup_size)` where `guard(t) != 0`:
///   For each output `o`:
///     state.buffers[output_bufs[o]][scatter_o(t)] = compute_o(t, inputs)
///
/// The result is deterministic because scatter injectivity guarantees
/// no two active threads write to the same output index.
pub open spec fn eval_map(
    spec: &KernelSpec,
    input_bufs: Seq<nat>,
    output_bufs: Seq<nat>,
    state: SharedState,
) -> SharedState
    decreases 0nat,
{
    // Build the input arrays from state buffers
    let inputs = Seq::new(input_bufs.len(), |i: int| state.buffers[input_bufs[i] as int]);

    // Apply each output sequentially (order doesn't matter due to scatter injectivity —
    // each output writes to a different buffer or non-overlapping positions)
    eval_map_outputs(spec, &inputs, output_bufs, state, 0)
}

/// Apply Map outputs one at a time, threading state through.
pub open spec fn eval_map_outputs(
    spec: &KernelSpec,
    inputs: &Seq<Seq<int>>,
    output_bufs: Seq<nat>,
    state: SharedState,
    out_idx: nat,
) -> SharedState
    decreases spec.outputs.len() - out_idx,
{
    if out_idx >= spec.outputs.len() {
        state
    } else {
        let new_state = eval_map_single_output(
            spec, inputs, output_bufs[out_idx as int], out_idx, state,
        );
        eval_map_outputs(spec, inputs, output_bufs, new_state, out_idx + 1)
    }
}

/// Apply a single output of a Map across all threads.
pub open spec fn eval_map_single_output(
    spec: &KernelSpec,
    inputs: &Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
) -> SharedState
    decreases state.workgroup_size,
{
    eval_map_threads(spec, inputs, out_buf, out_idx, state, 0)
}

/// Apply a single output for threads [tid, workgroup_size).
pub open spec fn eval_map_threads(
    spec: &KernelSpec,
    inputs: &Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
    tid: nat,
) -> SharedState
    decreases state.workgroup_size - tid,
{
    if tid >= state.workgroup_size {
        state
    } else {
        let env = thread_env_1d(tid);
        let guard_val = arith_eval_with_arrays(&spec.guard, env, *inputs);
        let new_state = if guard_val != 0 {
            let (scatter_idx, compute_val) = eval_output(
                &spec.outputs[out_idx as int], env, *inputs,
            );
            state.write(out_buf, scatter_idx as nat, compute_val)
        } else {
            state
        };
        eval_map_threads(spec, inputs, out_buf, out_idx, new_state, tid + 1)
    }
}

/// Apply a Scan (inclusive prefix sum) to a buffer in the shared state.
///
/// Replaces buffer contents with the inclusive prefix sum.
/// Uses the algebraic spec from scan.rs: result[i] = Σ_{j=0}^{i} buffer[j].
pub open spec fn eval_scan(
    buffer: nat,
    state: SharedState,
) -> SharedState
    recommends buffer < state.num_buffers(),
{
    let data = state.buffers[buffer as int];
    let scanned = Seq::new(data.len(), |i: int|
        sum_range(data, 0, i + 1)
    );
    state.set_buffer(buffer, scanned)
}

/// Sum of data[lo..hi).
pub open spec fn sum_range(data: Seq<int>, lo: int, hi: int) -> int
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo { 0 }
    else { sum_range(data, lo, hi - 1) + data[hi - 1] }
}

/// Evaluate a full Stage tree, producing the final SharedState.
pub open spec fn staged_eval(stage: &Stage, state: SharedState) -> SharedState
    decreases stage,
{
    match stage {
        Stage::Map { spec, input_bufs, output_bufs } => {
            eval_map(spec, *input_bufs, *output_bufs, state)
        },
        Stage::Scan { buffer } => {
            eval_scan(*buffer, state)
        },
        Stage::Barrier { scope, post } => {
            // Barrier is a no-op on state — it just asserts the postcondition holds.
            // The actual synchronization is a hardware concern; at the spec level,
            // our sequential evaluation already ensures writes are ordered.
            state
        },
        Stage::Seq { stages } => {
            eval_seq(stages, state, 0)
        },
        Stage::Loop { bound, body, invariant } => {
            eval_loop(&*body, state, *bound, 0)
        },
    }
}

/// Evaluate a sequence of stages left-to-right.
pub open spec fn eval_seq(stages: &Seq<Stage>, state: SharedState, idx: nat) -> SharedState
    decreases stages.len() - idx,
{
    if idx >= stages.len() {
        state
    } else {
        let new_state = staged_eval(&stages[idx as int], state);
        eval_seq(stages, new_state, idx + 1)
    }
}

/// Evaluate a loop body `bound` times.
pub open spec fn eval_loop(body: &Stage, state: SharedState, bound: nat, iter: nat) -> SharedState
    decreases bound - iter,
{
    if iter >= bound {
        state
    } else {
        let new_state = staged_eval(body, state);
        eval_loop(body, new_state, bound, iter + 1)
    }
}

// ══════════════════════════════════════════════════════════════
// Race-freedom predicates
// ══════════════════════════════════════════════════════════════

/// A Map stage is race-free if its scatter is injective under its guard.
/// This is the per-output scatter_injective predicate from kernel.rs,
/// applied to all outputs.
pub open spec fn map_race_free(
    spec: &KernelSpec,
    input_bufs: Seq<nat>,
    state: &SharedState,
) -> bool {
    let inputs = Seq::new(input_bufs.len(), |i: int| state.buffers[input_bufs[i] as int]);
    forall|o_idx: int, t1: nat, t2: nat|
        0 <= o_idx < spec.outputs.len()
        && t1 < state.workgroup_size
        && t2 < state.workgroup_size
        && t1 != t2
        ==> scatter_injective(
            &spec.outputs[o_idx],
            &spec.guard,
            inputs,
            thread_env_1d(t1),
            thread_env_1d(t2),
        )
}

/// Two adjacent Maps (without a barrier between them) are race-free if:
/// 1. Each Map individually has injective scatter (within-Map race freedom)
/// 2. They write to disjoint output buffers (cross-Map race freedom)
///
/// Condition 2 is sufficient because if they write to different buffers,
/// no thread in Map B can conflict with any thread in Map A.
/// If they share a buffer, a Barrier is needed between them.
pub open spec fn adjacent_maps_race_free(
    bufs_a: Seq<nat>,
    bufs_b: Seq<nat>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < bufs_a.len() && 0 <= j < bufs_b.len()
        ==> bufs_a[i] != bufs_b[j]
}

// ══════════════════════════════════════════════════════════════
// Basic properties
// ══════════════════════════════════════════════════════════════

/// Evaluating an empty sequence is the identity.
pub proof fn lemma_eval_seq_empty(state: SharedState)
    ensures eval_seq(&seq![], state, 0) == state,
{}

/// Evaluating a singleton sequence equals evaluating the stage.
pub proof fn lemma_eval_seq_single(stage: Stage, state: SharedState)
    ensures eval_seq(&seq![stage], state, 0) == staged_eval(&stage, state),
{}

/// A zero-iteration loop is the identity.
pub proof fn lemma_eval_loop_zero(body: Stage, state: SharedState)
    ensures eval_loop(&body, state, 0, 0) == state,
{}

/// A barrier is a no-op on state.
pub proof fn lemma_barrier_noop(scope: BarrierScope, post: spec_fn(SharedState) -> bool, state: SharedState)
    ensures staged_eval(&Stage::Barrier { scope, post }, state) == state,
{}

/// Loop unrolling: one iteration peels off.
pub proof fn lemma_eval_loop_step(body: Stage, state: SharedState, bound: nat, iter: nat)
    requires iter < bound,
    ensures
        eval_loop(&body, state, bound, iter)
            == eval_loop(&body, staged_eval(&body, state), bound, iter + 1),
{}

} // verus!
