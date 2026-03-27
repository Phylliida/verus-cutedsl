/// Stage-based GPU kernel composition with explicit barriers.
///
/// Models a GPU kernel as a tree of barrier-separated parallel operations.
/// This is **phase-based verification** — each barrier interval is verified
/// independently for race-freedom, and Hoare-style invariants at barrier
/// points provide compositional functional correctness.
///
/// Literature basis:
/// - GPUVerify (Betts et al., OOPSLA 2012) — barrier-interval analysis
/// - Barrier Invariants (Chong et al., OOPSLA 2013) — Hoare-style predicates at barriers
/// - Kojima & Igarashi (ACM TOCL 2017) — full Hoare logic for SIMT programs
/// - Faial (Cogumbreiro et al., CAV 2021) — compositional per-phase analysis

use vstd::prelude::*;
use crate::arith_expr::*;
use crate::kernel::*;
use crate::scan::inclusive_scan;

verus! {

// ══════════════════════════════════════════════════════════════
// Shared state model
// ══════════════════════════════════════════════════════════════

/// Shared state: a collection of named integer buffers.
/// Models both shared memory and global memory visible to a workgroup.
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

    pub open spec fn read(&self, buf: nat, idx: nat) -> int
        recommends buf < self.num_buffers(), idx < self.buffer_len(buf),
    {
        self.buffers[buf as int][idx as int]
    }

    pub open spec fn write(&self, buf: nat, idx: nat, val: int) -> SharedState
        recommends buf < self.num_buffers(), idx < self.buffer_len(buf),
    {
        SharedState {
            buffers: self.buffers.update(buf as int,
                self.buffers[buf as int].update(idx as int, val)),
            workgroup_size: self.workgroup_size,
        }
    }

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

pub enum BarrierScope {
    /// Workgroup-level: __syncthreads / workgroupBarrier. Cheap (~20 cycles).
    Workgroup,
    /// Grid-level: cooperative groups grid_group::sync. Expensive, rare.
    Grid,
}

// ══════════════════════════════════════════════════════════════
// Stage: composable kernel building block
//
// Uses binary Seq (first + then) instead of Seq<Stage> so that
// structural recursion works cleanly in Verus — both children
// are sub-terms of the Seq variant.
// ══════════════════════════════════════════════════════════════

pub enum Stage {
    /// No-op: identity on shared state.
    Noop,

    /// Parallel map using a verified KernelSpec.
    /// `input_bufs[i]` = SharedState buffer index for KernelSpec input array i.
    /// `output_bufs[i]` = SharedState buffer index for KernelSpec output i.
    Map {
        spec: KernelSpec,
        input_bufs: Seq<nat>,
        output_bufs: Seq<nat>,
    },

    /// Parallel inclusive prefix sum on a buffer.
    Scan {
        buffer: nat,
    },

    /// Explicit barrier with postcondition.
    /// The ONLY synchronization point. All prior writes become visible.
    Barrier {
        scope: BarrierScope,
        post: spec_fn(SharedState) -> bool,
    },

    /// Binary sequential composition: execute `first`, then `then`.
    /// NO implicit barrier between them — they fuse unless separated by a Barrier.
    /// Build longer sequences with the `stages!` helper or nested Seq.
    Seq {
        first: Box<Stage>,
        then: Box<Stage>,
    },

    /// Bounded loop: execute `body` exactly `bound` times.
    /// `invariant(state, iteration)` is the inductive loop invariant.
    Loop {
        bound: nat,
        body: Box<Stage>,
        invariant: spec_fn(SharedState, nat) -> bool,
    },
}

// ══════════════════════════════════════════════════════════════
// Sequence builder — flat list → nested binary Seq
// ══════════════════════════════════════════════════════════════

/// Build a Stage from a flat list of stages.
/// `seq_stages([a, b, c])` = `Seq(a, Seq(b, c))`.
pub open spec fn seq_stages(stages: Seq<Stage>) -> Stage
    decreases stages.len(),
{
    if stages.len() == 0 {
        Stage::Noop
    } else if stages.len() == 1 {
        stages[0]
    } else {
        Stage::Seq {
            first: Box::new(stages[0]),
            then: Box::new(seq_stages(stages.skip(1))),
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Map evaluation — declarative (order-independent)
//
// The primary spec for Map stages. Each output position gets the
// compute value of its unique writer thread (by scatter injectivity),
// or is unchanged if no thread writes there.
//
// This is the "right" definition — no thread ordering baked in.
// eval_map_threads (below) is the operational version used by the
// exec interpreter; map_determinism proves they agree.
// ══════════════════════════════════════════════════════════════

/// Declarative (order-independent) spec for a single Map output's effect.
/// Position j gets compute(writer) if some thread writes to j, else old value.
/// Well-defined because scatter injectivity guarantees at most one writer.
pub open spec fn map_output_declarative(
    spec: &KernelSpec,
    out_idx: nat,
    inputs: Seq<Seq<int>>,
    old_buf: Seq<int>,
    workgroup_size: nat,
) -> Seq<int> {
    Seq::new(old_buf.len(), |j: int|
        if exists|t: nat| t < workgroup_size
            && arith_eval_with_arrays(&spec.guard, thread_env_1d(t), inputs) != 0
            && arith_eval_with_arrays(&spec.outputs[out_idx as int].scatter,
                thread_env_1d(t), inputs) == j
        {
            let t = choose|t: nat| t < workgroup_size
                && arith_eval_with_arrays(&spec.guard, thread_env_1d(t), inputs) != 0
                && arith_eval_with_arrays(&spec.outputs[out_idx as int].scatter,
                    thread_env_1d(t), inputs) == j;
            arith_eval_with_arrays(&spec.outputs[out_idx as int].compute,
                thread_env_1d(t), inputs)
        } else {
            old_buf[j]
        }
    )
}

/// Apply a Map: declarative evaluation. Inputs captured from initial state,
/// outputs applied sequentially (each output uses the declarative spec).
pub open spec fn eval_map(
    spec: &KernelSpec,
    input_bufs: Seq<nat>,
    output_bufs: Seq<nat>,
    state: SharedState,
) -> SharedState {
    let inputs = Seq::new(input_bufs.len(), |i: int| state.buffers[input_bufs[i] as int]);
    eval_map_outputs(spec, inputs, output_bufs, state, 0)
}

/// Chain output applications. Each output replaces its target buffer
/// with the declarative result.
pub open spec fn eval_map_outputs(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    output_bufs: Seq<nat>,
    state: SharedState,
    out_idx: nat,
) -> SharedState
    decreases spec.outputs.len() - out_idx,
{
    if out_idx >= spec.outputs.len() {
        state
    } else {
        let new_buf = map_output_declarative(
            spec, out_idx, inputs,
            state.buffers[output_bufs[out_idx as int] as int],
            state.workgroup_size,
        );
        let new_state = state.set_buffer(output_bufs[out_idx as int], new_buf);
        eval_map_outputs(spec, inputs, output_bufs, new_state, out_idx + 1)
    }
}

// ══════════════════════════════════════════════════════════════
// Map evaluation — operational (sequential threads, for exec)
//
// eval_map_threads processes threads 0, 1, 2, ... writing to state.
// map_determinism (in stage_lemmas.rs) proves this equals the
// declarative version above.
// ══════════════════════════════════════════════════════════════

/// Operational (sequential) Map evaluation for a single output.
/// Used by the exec interpreter. Proved equivalent to map_output_declarative.
pub open spec fn eval_map_threads(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
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
        let guard_val = arith_eval_with_arrays(&spec.guard, env, inputs);
        let new_state = if guard_val != 0 {
            let (scatter_idx, compute_val) = eval_output(
                &spec.outputs[out_idx as int], env, inputs,
            );
            state.write(out_buf, scatter_idx as nat, compute_val)
        } else {
            state
        };
        eval_map_threads(spec, inputs, out_buf, out_idx, new_state, tid + 1)
    }
}

// ══════════════════════════════════════════════════════════════
// Scan evaluation — uses existing verified inclusive_scan
// ══════════════════════════════════════════════════════════════

/// Apply inclusive prefix sum to a buffer.
/// Uses inclusive_scan::<int> from the verified scan infrastructure.
pub open spec fn eval_scan(buffer: nat, state: SharedState) -> SharedState
    recommends buffer < state.num_buffers(),
{
    let data = state.buffers[buffer as int];
    state.set_buffer(buffer, inclusive_scan::<int>(data))
}

// ══════════════════════════════════════════════════════════════
// Stage evaluation — mutual recursion group
//
// staged_eval + eval_loop are mutually recursive.
// Decreases: (Stage, nat). Follows arith_eval/reduce_sum pattern.
// Binary Seq means both children are structural sub-terms.
// ══════════════════════════════════════════════════════════════

/// Evaluate a Stage tree, producing the final SharedState.
pub open spec fn staged_eval(stage: &Stage, state: SharedState) -> SharedState
    decreases stage, 0nat,
{
    match stage {
        Stage::Noop => state,
        Stage::Map { spec, input_bufs, output_bufs } => {
            eval_map(spec, *input_bufs, *output_bufs, state)
        },
        Stage::Scan { buffer } => {
            eval_scan(*buffer, state)
        },
        Stage::Barrier { scope, post } => {
            // Barrier is a no-op on state at the spec level.
            // Sequential evaluation already ensures write ordering.
            state
        },
        Stage::Seq { first, then } => {
            // Both *first and *then are structural sub-terms of Seq.
            let mid = staged_eval(&**first, state);
            staged_eval(&**then, mid)
        },
        Stage::Loop { bound, body, invariant } => {
            eval_loop(&**body, state, *bound, 0)
        },
    }
}

/// Evaluate a loop body `bound - iter` more times.
/// `body` is the sub-term from Stage::Loop — structurally smaller than the Loop.
pub open spec fn eval_loop(
    body: &Stage, state: SharedState, bound: nat, iter: nat,
) -> SharedState
    decreases body, bound - iter,
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

/// A Map is race-free if scatter is injective under guard for all outputs.
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

/// Two Maps are cross-race-free if they write to disjoint output buffers.
pub open spec fn maps_write_disjoint(bufs_a: Seq<nat>, bufs_b: Seq<nat>) -> bool {
    forall|i: int, j: int|
        0 <= i < bufs_a.len() && 0 <= j < bufs_b.len()
        ==> bufs_a[i] != bufs_b[j]
}

// ══════════════════════════════════════════════════════════════
// Basic properties
// ══════════════════════════════════════════════════════════════

/// Noop is identity.
pub proof fn lemma_noop(state: SharedState)
    ensures staged_eval(&Stage::Noop, state) == state,
{}

/// Barrier is identity on state.
pub proof fn lemma_barrier_noop(
    scope: BarrierScope, post: spec_fn(SharedState) -> bool, state: SharedState,
)
    ensures staged_eval(&Stage::Barrier { scope, post }, state) == state,
{}

/// Zero-iteration loop is identity.
pub proof fn lemma_loop_zero(body: Stage, inv: spec_fn(SharedState, nat) -> bool, state: SharedState)
    ensures staged_eval(&Stage::Loop { bound: 0, body: Box::new(body), invariant: inv }, state) == state,
{
    let stage = Stage::Loop { bound: 0, body: Box::new(body), invariant: inv };
    // Help Z3 see through the match + Box
    assert(staged_eval(&stage, state) == eval_loop(&body, state, 0, 0));
}

/// Seq is composition: eval(Seq(a, b), s) == eval(b, eval(a, s)).
pub proof fn lemma_seq_compose(a: Stage, b: Stage, state: SharedState)
    ensures
        staged_eval(&Stage::Seq { first: Box::new(a), then: Box::new(b) }, state)
            == staged_eval(&b, staged_eval(&a, state)),
{}

/// Loop step: one iteration peels off.
pub proof fn lemma_loop_step(body: &Stage, state: SharedState, bound: nat, iter: nat)
    requires iter < bound,
    ensures
        eval_loop(body, state, bound, iter)
            == eval_loop(body, staged_eval(body, state), bound, iter + 1),
{}

/// eval_loop at bound == iter is identity.
pub proof fn lemma_loop_done(body: &Stage, state: SharedState, n: nat)
    ensures eval_loop(body, state, n, n) == state,
{}

/// Single-iteration loop equals one body evaluation.
pub proof fn lemma_loop_one(body: Stage, inv: spec_fn(SharedState, nat) -> bool, state: SharedState)
    ensures
        staged_eval(&Stage::Loop { bound: 1, body: Box::new(body), invariant: inv }, state)
            == staged_eval(&body, state),
{
    let stage = Stage::Loop { bound: 1, body: Box::new(body), invariant: inv };
    assert(staged_eval(&stage, state) == eval_loop(&body, state, 1, 0));
    assert(eval_loop(&body, state, 1, 0)
        == eval_loop(&body, staged_eval(&body, state), 1, 1));
}

} // verus!
