/// Proof lemmas for Stage-based kernel composition.
///
/// Key theorems:
/// - Loop invariant induction: if inv holds initially and is preserved
///   by each iteration, it holds after the loop.
/// - Loop unrolling / concatenation.
/// - Seq associativity and identity.
/// - Barrier invariant chaining (Hoare-logic-style).
/// - Stage substitution under equivalence.

use vstd::prelude::*;
use crate::stage::*;
use crate::kernel::*;
use crate::arith_expr::*;
use crate::scan::{inclusive_scan, exclusive_scan, reduce};
use verus_algebra::summation::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Loop invariant induction
// ══════════════════════════════════════════════════════════════

/// Core induction: if inv holds at iteration `iter` and each step preserves it,
/// then inv holds after all remaining iterations.
pub proof fn lemma_loop_inv_induction(
    body: &Stage,
    state: SharedState,
    bound: nat,
    iter: nat,
    inv: spec_fn(SharedState, nat) -> bool,
)
    requires
        iter <= bound,
        inv(state, iter),
        forall|s: SharedState, k: nat|
            #[trigger] inv(staged_eval(body, s), k + 1)
            || !(k < bound && inv(s, k)),
    ensures
        inv(eval_loop(body, state, bound, iter), bound),
    decreases bound - iter,
{
    if iter >= bound {
    } else {
        let next_state = staged_eval(body, state);
        assert(inv(next_state, iter + 1));
        lemma_loop_inv_induction(body, next_state, bound, iter + 1, inv);
    }
}

/// Top-level loop invariant theorem: if inv holds initially (at iter 0)
/// and body preserves it, then it holds after the full loop.
pub proof fn lemma_loop_inv(
    body: &Stage,
    state: SharedState,
    bound: nat,
    inv: spec_fn(SharedState, nat) -> bool,
)
    requires
        inv(state, 0),
        forall|s: SharedState, k: nat|
            #[trigger] inv(staged_eval(body, s), k + 1)
            || !(k < bound && inv(s, k)),
    ensures
        inv(eval_loop(body, state, bound, 0), bound),
{
    lemma_loop_inv_induction(body, state, bound, 0, inv);
}

// ══════════════════════════════════════════════════════════════
// Loop unrolling
// ══════════════════════════════════════════════════════════════

/// Peeling one iteration off the front of a loop.
pub proof fn lemma_loop_unroll_one(
    body: &Stage, state: SharedState, bound: nat, iter: nat,
)
    requires iter < bound,
    ensures
        eval_loop(body, state, bound, iter)
            == eval_loop(body, staged_eval(body, state), bound, iter + 1),
{}

// ══════════════════════════════════════════════════════════════
// Seq associativity and identity
// ══════════════════════════════════════════════════════════════

/// Seq is associative: Seq(a, Seq(b, c)) ≡ Seq(Seq(a, b), c).
pub proof fn lemma_seq_assoc(a: Stage, b: Stage, c: Stage, state: SharedState)
    ensures
        staged_eval(
            &Stage::Seq {
                first: Box::new(a),
                then: Box::new(Stage::Seq { first: Box::new(b), then: Box::new(c) }),
            },
            state,
        ) == staged_eval(
            &Stage::Seq {
                first: Box::new(Stage::Seq { first: Box::new(a), then: Box::new(b) }),
                then: Box::new(c),
            },
            state,
        ),
{
    // Help Z3 unfold through the Box layers
    let mid_a = staged_eval(&a, state);
    let mid_ab = staged_eval(&b, mid_a);
    let final_abc = staged_eval(&c, mid_ab);
    // LHS: Seq(a, Seq(b, c))
    lemma_seq_compose(a, Stage::Seq { first: Box::new(b), then: Box::new(c) }, state);
    lemma_seq_compose(b, c, mid_a);
    // RHS: Seq(Seq(a, b), c)
    lemma_seq_compose(Stage::Seq { first: Box::new(a), then: Box::new(b) }, c, state);
    lemma_seq_compose(a, b, state);
}

/// Noop is left identity for Seq.
pub proof fn lemma_seq_noop_left(s: Stage, state: SharedState)
    ensures
        staged_eval(
            &Stage::Seq { first: Box::new(Stage::Noop), then: Box::new(s) },
            state,
        ) == staged_eval(&s, state),
{
    lemma_seq_compose(Stage::Noop, s, state);
    lemma_noop(state);
}

/// Noop is right identity for Seq.
pub proof fn lemma_seq_noop_right(s: Stage, state: SharedState)
    ensures
        staged_eval(
            &Stage::Seq { first: Box::new(s), then: Box::new(Stage::Noop) },
            state,
        ) == staged_eval(&s, state),
{
    lemma_seq_compose(s, Stage::Noop, state);
    lemma_noop(staged_eval(&s, state));
}

// ══════════════════════════════════════════════════════════════
// Barrier invariant chaining
// ══════════════════════════════════════════════════════════════

/// If a stage establishes a postcondition, it holds after Seq(stage, Barrier(post)).
pub proof fn lemma_barrier_post_holds(
    stage: Stage,
    scope: BarrierScope,
    post: spec_fn(SharedState) -> bool,
    state: SharedState,
)
    requires
        post(staged_eval(&stage, state)),
    ensures
        post(staged_eval(
            &Stage::Seq {
                first: Box::new(stage),
                then: Box::new(Stage::Barrier { scope, post }),
            },
            state,
        )),
{
    lemma_seq_compose(stage, Stage::Barrier { scope, post }, state);
    lemma_barrier_noop(scope, post, staged_eval(&stage, state));
}

/// Hoare-style barrier chaining: {pre} stage {post}.
/// If `pre(state)` and `forall s. pre(s) ==> post(eval(stage, s))`,
/// then `post` holds after executing stage.
pub proof fn lemma_barrier_chain(
    stage: Stage,
    pre: spec_fn(SharedState) -> bool,
    post: spec_fn(SharedState) -> bool,
    state: SharedState,
)
    requires
        pre(state),
        forall|s: SharedState| pre(s) ==> #[trigger] post(staged_eval(&stage, s)),
    ensures
        post(staged_eval(
            &Stage::Seq {
                first: Box::new(stage),
                then: Box::new(Stage::Barrier { scope: BarrierScope::Workgroup, post }),
            },
            state,
        )),
{
    // staged_eval(&stage, state) satisfies post by the Hoare triple
    assert(post(staged_eval(&stage, state)));
    lemma_barrier_post_holds(stage, BarrierScope::Workgroup, post, state);
}

// ══════════════════════════════════════════════════════════════
// Stage substitution
// ══════════════════════════════════════════════════════════════

/// If two stages produce the same result after a common prefix,
/// they are interchangeable in Seq(prefix ; stage ; suffix).
pub proof fn lemma_seq_stage_substitution(
    before: Stage,
    a: Stage,
    b: Stage,
    after: Stage,
    state: SharedState,
)
    requires
        staged_eval(&a, staged_eval(&before, state))
            == staged_eval(&b, staged_eval(&before, state)),
    ensures
        staged_eval(
            &Stage::Seq {
                first: Box::new(Stage::Seq { first: Box::new(before), then: Box::new(a) }),
                then: Box::new(after),
            },
            state,
        ) == staged_eval(
            &Stage::Seq {
                first: Box::new(Stage::Seq { first: Box::new(before), then: Box::new(b) }),
                then: Box::new(after),
            },
            state,
        ),
{
    let mid = staged_eval(&before, state);
    // Unfold LHS
    lemma_seq_compose(
        Stage::Seq { first: Box::new(before), then: Box::new(a) },
        after, state);
    lemma_seq_compose(before, a, state);
    // Unfold RHS
    lemma_seq_compose(
        Stage::Seq { first: Box::new(before), then: Box::new(b) },
        after, state);
    lemma_seq_compose(before, b, state);
    // Now both sides = staged_eval(&after, staged_eval(&X, mid))
    // where staged_eval(&a, mid) == staged_eval(&b, mid) by requires.
}

// ══════════════════════════════════════════════════════════════
// Loop + Seq: explicit two-stage loop body
// ══════════════════════════════════════════════════════════════

/// Explicit form of a loop with a two-stage body, for easier reasoning.
/// Each iteration runs a then b.
pub open spec fn eval_loop_two_stage(
    a: &Stage, b: &Stage, state: SharedState, bound: nat, iter: nat,
) -> SharedState
    decreases bound - iter,
{
    if iter >= bound {
        state
    } else {
        let after_a = staged_eval(a, state);
        let after_b = staged_eval(b, after_a);
        eval_loop_two_stage(a, b, after_b, bound, iter + 1)
    }
}

/// A loop whose body is Seq(a, b) unfolds to the explicit two-stage form.
pub proof fn lemma_loop_body_seq(
    a: Stage, b: Stage, state: SharedState, bound: nat, iter: nat,
)
    requires iter <= bound,
    ensures ({
        let body = Stage::Seq { first: Box::new(a), then: Box::new(b) };
        eval_loop(&body, state, bound, iter)
            == eval_loop_two_stage(&a, &b, state, bound, iter)
    }),
    decreases bound - iter,
{
    let body = Stage::Seq { first: Box::new(a), then: Box::new(b) };
    if iter >= bound {
    } else {
        lemma_seq_compose(a, b, state);
        let mid = staged_eval(&b, staged_eval(&a, state));
        assert(staged_eval(&body, state) == mid);
        lemma_loop_body_seq(a, b, mid, bound, iter + 1);
    }
}

// ══════════════════════════════════════════════════════════════
// SharedState frame conditions
// ══════════════════════════════════════════════════════════════

/// Writing to one buffer doesn't affect other buffers.
pub proof fn lemma_write_other_buffer(
    state: SharedState, buf_w: nat, idx: nat, val: int, buf_r: nat,
)
    requires
        buf_w < state.num_buffers(),
        buf_r < state.num_buffers(),
        idx < state.buffer_len(buf_w),
        buf_w != buf_r,
    ensures
        state.write(buf_w, idx, val).buffers[buf_r as int]
            == state.buffers[buf_r as int],
{
}

/// Writing to one position doesn't affect other positions in the same buffer.
pub proof fn lemma_write_other_index(
    state: SharedState, buf: nat, idx_w: nat, val: int, idx_r: nat,
)
    requires
        buf < state.num_buffers(),
        idx_w < state.buffer_len(buf),
        idx_r < state.buffer_len(buf),
        idx_w != idx_r,
    ensures
        state.write(buf, idx_w, val).read(buf, idx_r) == state.read(buf, idx_r),
{
}

/// Writing then reading the same position gives the written value.
pub proof fn lemma_write_read_same(
    state: SharedState, buf: nat, idx: nat, val: int,
)
    requires
        buf < state.num_buffers(),
        idx < state.buffer_len(buf),
    ensures
        state.write(buf, idx, val).read(buf, idx) == val,
{
}

/// set_buffer doesn't affect other buffers.
pub proof fn lemma_set_buffer_other(
    state: SharedState, buf_w: nat, data: Seq<int>, buf_r: nat,
)
    requires
        buf_w < state.num_buffers(),
        buf_r < state.num_buffers(),
        buf_w != buf_r,
    ensures
        state.set_buffer(buf_w, data).buffers[buf_r as int]
            == state.buffers[buf_r as int],
{
}

/// set_buffer then reading gives the new data.
pub proof fn lemma_set_buffer_read(
    state: SharedState, buf: nat, data: Seq<int>, idx: nat,
)
    requires
        buf < state.num_buffers(),
        idx < data.len(),
    ensures
        state.set_buffer(buf, data).read(buf, idx) == data[idx as int],
{
}

/// write preserves num_buffers.
pub proof fn lemma_write_preserves_num_buffers(
    state: SharedState, buf: nat, idx: nat, val: int,
)
    requires buf < state.num_buffers(), idx < state.buffer_len(buf),
    ensures state.write(buf, idx, val).num_buffers() == state.num_buffers(),
{
}

/// set_buffer preserves num_buffers.
pub proof fn lemma_set_buffer_preserves_num_buffers(
    state: SharedState, buf: nat, data: Seq<int>,
)
    requires buf < state.num_buffers(),
    ensures state.set_buffer(buf, data).num_buffers() == state.num_buffers(),
{
}

/// write preserves workgroup_size.
pub proof fn lemma_write_preserves_workgroup_size(
    state: SharedState, buf: nat, idx: nat, val: int,
)
    requires buf < state.num_buffers(), idx < state.buffer_len(buf),
    ensures state.write(buf, idx, val).workgroup_size == state.workgroup_size,
{
}

/// set_buffer preserves workgroup_size.
pub proof fn lemma_set_buffer_preserves_workgroup_size(
    state: SharedState, buf: nat, data: Seq<int>,
)
    requires buf < state.num_buffers(),
    ensures state.set_buffer(buf, data).workgroup_size == state.workgroup_size,
{
}

// ══════════════════════════════════════════════════════════════
// seq_stages correctness
// ══════════════════════════════════════════════════════════════

/// seq_stages of a single stage is that stage.
pub proof fn lemma_seq_stages_single(s: Stage, state: SharedState)
    ensures staged_eval(&seq_stages(seq![s]), state) == staged_eval(&s, state),
{
}

/// seq_stages of two stages is Seq(a, b).
pub proof fn lemma_seq_stages_two(a: Stage, b: Stage, state: SharedState)
    ensures staged_eval(&seq_stages(seq![a, b]), state)
        == staged_eval(&b, staged_eval(&a, state)),
{
    assert(seq![a, b].skip(1) =~= seq![b]);
    assert(seq_stages(seq![b]) == b);
    // Now: seq_stages(seq![a, b]) = Seq(a, b)
    assert(seq_stages(seq![a, b]) == Stage::Seq {
        first: Box::new(a), then: Box::new(b) });
    lemma_seq_compose(a, b, state);
}

/// seq_stages of three stages composes left-to-right.
pub proof fn lemma_seq_stages_three(a: Stage, b: Stage, c: Stage, state: SharedState)
    ensures staged_eval(&seq_stages(seq![a, b, c]), state)
        == staged_eval(&c, staged_eval(&b, staged_eval(&a, state))),
{
    // Help Z3 unfold seq_stages
    assert(seq![a, b, c].skip(1) =~= seq![b, c]);
    let bc = seq_stages(seq![b, c]);
    lemma_seq_compose(a, bc, state);
    lemma_seq_stages_two(b, c, staged_eval(&a, state));
}

// ══════════════════════════════════════════════════════════════
// eval_map unfolding for two-output kernels
// ══════════════════════════════════════════════════════════════

/// For a two-output kernel, eval_map chains two set_buffer calls using
/// map_output_declarative. Both use the same `inputs` (captured from initial state).
/// Works for both distinct and same output buffers — the second output
/// naturally sees the first output's writes in its `old_buf`.
pub proof fn lemma_eval_map_two_outputs(
    spec: &KernelSpec,
    input_bufs: Seq<nat>,
    output_bufs: Seq<nat>,
    state: SharedState,
    thread_dim: &ThreadDim,
)
    requires
        spec.outputs.len() == 2,
        output_bufs.len() == 2,
        forall|i: int| 0 <= i < input_bufs.len() ==>
            (input_bufs[i] as int) < state.buffers.len(),
        forall|i: int| 0 <= i < output_bufs.len() ==>
            (output_bufs[i] as int) < state.buffers.len(),
    ensures ({
        let inputs = Seq::new(input_bufs.len(), |i: int| state.buffers[input_bufs[i] as int]);
        let ws = thread_count(thread_dim, state.workgroup_size);
        let new_buf0 = map_output_declarative(spec, 0, inputs,
            state.buffers[output_bufs[0] as int], ws, thread_dim);
        let after_out0 = state.set_buffer(output_bufs[0], new_buf0);
        let new_buf1 = map_output_declarative(spec, 1, inputs,
            after_out0.buffers[output_bufs[1] as int], ws, thread_dim);
        let after_out1 = after_out0.set_buffer(output_bufs[1], new_buf1);
        eval_map(spec, input_bufs, output_bufs, state, thread_dim) == after_out1
    }),
{
    let inputs = Seq::new(input_bufs.len(), |i: int| state.buffers[input_bufs[i] as int]);
    let ws = thread_count(thread_dim, state.workgroup_size);
    let new_buf0 = map_output_declarative(spec, 0, inputs,
        state.buffers[output_bufs[0] as int], ws, thread_dim);
    let after_out0 = state.set_buffer(output_bufs[0], new_buf0);
    let new_buf1 = map_output_declarative(spec, 1, inputs,
        after_out0.buffers[output_bufs[1] as int], ws, thread_dim);
    let after_out1 = after_out0.set_buffer(output_bufs[1], new_buf1);

    assert(eval_map(spec, input_bufs, output_bufs, state, thread_dim)
        == eval_map_outputs(spec, inputs, output_bufs, state, 0, ws, thread_dim));
    assert(eval_map_outputs(spec, inputs, output_bufs, state, 0, ws, thread_dim)
        == eval_map_outputs(spec, inputs, output_bufs, after_out0, 1, ws, thread_dim));
    assert(eval_map_outputs(spec, inputs, output_bufs, after_out0, 1, ws, thread_dim)
        == eval_map_outputs(spec, inputs, output_bufs, after_out1, 2, ws, thread_dim));
    assert(eval_map_outputs(spec, inputs, output_bufs, after_out1, 2, ws, thread_dim) == after_out1);
}

// ══════════════════════════════════════════════════════════════
// Map determinism proof helpers
//
// map_output_declarative is now the PRIMARY definition in stage.rs.
// eval_map_threads is the OPERATIONAL version for exec.
// These lemmas prove they agree (under scatter injectivity).
// ══════════════════════════════════════════════════════════════

/// Thread t is active and scatters to position j for output out_idx.
pub open spec fn thread_writes_to(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_idx: nat,
    t: nat,
    j: int,
) -> bool {
    arith_eval_with_arrays(&spec.guard, thread_env_1d(t), inputs) != 0
    && arith_eval_with_arrays(&spec.outputs[out_idx as int].scatter,
        thread_env_1d(t), inputs) == j
}

/// No thread in [tid, workgroup_size) writes to position j.
pub open spec fn no_writer_in_range(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_idx: nat,
    j: int,
    tid: nat,
    workgroup_size: nat,
) -> bool {
    forall|t: nat| tid <= t < workgroup_size ==>
        !#[trigger] thread_writes_to(spec, inputs, out_idx, t, j)
}

/// All active threads scatter to valid buffer positions.
pub open spec fn scatter_in_bounds(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_idx: nat,
    buf_len: nat,
    workgroup_size: nat,
) -> bool {
    forall|t: nat| t < workgroup_size
        && arith_eval_with_arrays(&spec.guard, thread_env_1d(t), inputs) != 0
        ==> {
            let idx = arith_eval_with_arrays(
                &spec.outputs[out_idx as int].scatter, thread_env_1d(t), inputs);
            0 <= idx && idx < buf_len as int
        }
}

/// Bundled frame lemma: eval_map_threads preserves ALL non-target properties.
/// One induction instead of four separate lemmas.
///
/// Preserves: buffer lengths, other buffers, workgroup_size, num_buffers.
pub proof fn lemma_eval_map_threads_frame(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
    tid: nat,
)
    requires
        out_buf < state.num_buffers(),
        out_idx < spec.outputs.len(),
        scatter_in_bounds(spec, inputs, out_idx, state.buffer_len(out_buf), state.workgroup_size),
    ensures ({
        let result = eval_map_threads(spec, inputs, out_buf, out_idx, state, tid);
        // Target buffer length preserved
        &&& result.buffers[out_buf as int].len() == state.buffers[out_buf as int].len()
        // Other buffers unchanged
        &&& forall|b: nat| b < state.num_buffers() && b != out_buf ==>
            result.buffers[b as int] == state.buffers[b as int]
        // Structure preserved
        &&& result.workgroup_size == state.workgroup_size
        &&& result.num_buffers() == state.num_buffers()
    }),
    decreases state.workgroup_size - tid,
{
    if tid >= state.workgroup_size {
    } else {
        let env = thread_env_1d(tid);
        let guard_val = arith_eval_with_arrays(&spec.guard, env, inputs);
        if guard_val != 0 {
            let (scatter_idx, compute_val) = eval_output(
                &spec.outputs[out_idx as int], env, inputs);
            assert(0 <= scatter_idx && scatter_idx < state.buffer_len(out_buf) as int);
            let new_state = state.write(out_buf, scatter_idx as nat, compute_val);
            // Frame conditions for single write
            assert forall|b: nat| b < state.num_buffers() && b != out_buf implies
                new_state.buffers[b as int] == state.buffers[b as int]
            by { lemma_write_other_buffer(state, out_buf, scatter_idx as nat, compute_val, b); }
            // Recurse
            lemma_eval_map_threads_frame(
                spec, inputs, out_buf, out_idx, new_state, tid + 1);
        } else {
            lemma_eval_map_threads_frame(
                spec, inputs, out_buf, out_idx, state, tid + 1);
        }
    }
}

/// If no thread in [tid, workgroup_size) writes to position j,
/// then eval_map_threads leaves buffer[j] unchanged.
pub proof fn lemma_eval_map_threads_preserves_non_target(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
    tid: nat,
    j: nat,
)
    requires
        out_buf < state.num_buffers(),
        j < state.buffer_len(out_buf),
        out_idx < spec.outputs.len(),
        no_writer_in_range(spec, inputs, out_idx, j as int, tid, state.workgroup_size),
        scatter_in_bounds(spec, inputs, out_idx, state.buffer_len(out_buf), state.workgroup_size),
    ensures
        eval_map_threads(spec, inputs, out_buf, out_idx, state, tid).read(out_buf, j)
            == state.read(out_buf, j),
    decreases state.workgroup_size - tid,
{
    if tid >= state.workgroup_size {
        // Base: no threads, state unchanged
    } else {
        let env = thread_env_1d(tid);
        let guard_val = arith_eval_with_arrays(&spec.guard, env, inputs);
        // Thread tid does NOT write to j (by no_writer_in_range)
        assert(!thread_writes_to(spec, inputs, out_idx, tid, j as int));

        if guard_val != 0 {
            let (scatter_idx, compute_val) = eval_output(
                &spec.outputs[out_idx as int], env, inputs,
            );
            // scatter_idx is in bounds (from scatter_in_bounds precondition)
            assert(0 <= scatter_idx && scatter_idx < state.buffer_len(out_buf) as int);
            // scatter_idx != j (since tid doesn't write to j)
            assert(scatter_idx != j as int);
            let si = scatter_idx as nat;
            let new_state = state.write(out_buf, si, compute_val);
            // Writing to scatter_idx doesn't affect position j
            lemma_write_other_index(state, out_buf, si, compute_val, j);
            // IH: remaining threads also don't write to j
            lemma_eval_map_threads_preserves_non_target(
                spec, inputs, out_buf, out_idx, new_state, tid + 1, j,
            );
        } else {
            // Guard is 0 — no write, just recurse
            lemma_eval_map_threads_preserves_non_target(
                spec, inputs, out_buf, out_idx, state, tid + 1, j,
            );
        }
    }
}

/// If thread `writer` is the unique active writer to position j among [tid, workgroup_size),
/// then after eval_map_threads, buffer[j] == compute(writer).
pub proof fn lemma_eval_map_threads_writer_wins(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
    tid: nat,
    writer: nat,
    j: nat,
)
    requires
        out_buf < state.num_buffers(),
        j < state.buffer_len(out_buf),
        out_idx < spec.outputs.len(),
        tid <= writer < state.workgroup_size,
        // writer is active and scatters to j
        thread_writes_to(spec, inputs, out_idx, writer, j as int),
        // no OTHER thread in [tid, workgroup_size) writes to j
        forall|t: nat| tid <= t < state.workgroup_size && t != writer ==>
            !#[trigger] thread_writes_to(spec, inputs, out_idx, t, j as int),
        scatter_in_bounds(spec, inputs, out_idx, state.buffer_len(out_buf), state.workgroup_size),
    ensures
        eval_map_threads(spec, inputs, out_buf, out_idx, state, tid).read(out_buf, j)
            == arith_eval_with_arrays(
                &spec.outputs[out_idx as int].compute,
                thread_env_1d(writer), inputs),
    decreases writer - tid,
{
    if tid == writer {
        // This is the writer thread. It writes compute(writer) to position j.
        let env = thread_env_1d(tid);
        let guard_val = arith_eval_with_arrays(&spec.guard, env, inputs);
        assert(guard_val != 0); // writer is active
        let (scatter_idx, compute_val) = eval_output(
            &spec.outputs[out_idx as int], env, inputs,
        );
        assert(scatter_idx == j as int); // writer scatters to j
        assert(0 <= scatter_idx && scatter_idx < state.buffer_len(out_buf) as int);
        let si = scatter_idx as nat;
        assert(si == j);
        let new_state = state.write(out_buf, j, compute_val);
        // After write: new_state.read(out_buf, j) == compute_val
        lemma_write_read_same(state, out_buf, j, compute_val);
        // No thread in [writer+1, workgroup_size) writes to j
        // → eval_map_threads from writer+1 preserves position j
        lemma_eval_map_threads_preserves_non_target(
            spec, inputs, out_buf, out_idx, new_state, tid + 1, j,
        );
    } else {
        // tid < writer. Thread tid does NOT write to j.
        assert(!thread_writes_to(spec, inputs, out_idx, tid, j as int));
        let env = thread_env_1d(tid);
        let guard_val = arith_eval_with_arrays(&spec.guard, env, inputs);
        if guard_val != 0 {
            let (scatter_idx, compute_val) = eval_output(
                &spec.outputs[out_idx as int], env, inputs,
            );
            assert(scatter_idx != j as int);
            assert(0 <= scatter_idx && scatter_idx < state.buffer_len(out_buf) as int);
            let si = scatter_idx as nat;
            let new_state = state.write(out_buf, si, compute_val);
            // IH on new_state from tid+1
            lemma_eval_map_threads_writer_wins(
                spec, inputs, out_buf, out_idx, new_state, tid + 1, writer, j,
            );
        } else {
            // Guard is 0, no write
            lemma_eval_map_threads_writer_wins(
                spec, inputs, out_buf, out_idx, state, tid + 1, writer, j,
            );
        }
    }
}

/// All active thread pairs satisfy scatter_injective for output out_idx.
pub open spec fn all_scatter_injective(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_idx: nat,
    workgroup_size: nat,
) -> bool {
    forall|t1: nat, t2: nat|
        t1 < workgroup_size && t2 < workgroup_size && t1 != t2
        ==> scatter_injective(
            &spec.outputs[out_idx as int], &spec.guard,
            inputs, thread_env_1d(t1), thread_env_1d(t2))
}

/// Per-position map determinism: at position j, eval_map_threads agrees
/// with map_output_declarative.
/// Map determinism for 1D dispatch. For 2D, the same proof works
/// with thread_env_for_dim — left as a follow-up.
proof fn lemma_map_determinism_at(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
    j: nat,
)
    requires
        out_buf < state.num_buffers(),
        j < state.buffer_len(out_buf),
        out_idx < spec.outputs.len(),
        all_scatter_injective(spec, inputs, out_idx, state.workgroup_size),
        scatter_in_bounds(spec, inputs, out_idx, state.buffer_len(out_buf), state.workgroup_size),
    ensures
        eval_map_threads(spec, inputs, out_buf, out_idx, state, 0).read(out_buf, j)
            == map_output_declarative(
                spec, out_idx, inputs,
                state.buffers[out_buf as int], state.workgroup_size,
                &ThreadDim::Dim1D)[j as int],
{
    let ws = state.workgroup_size;
    let old_buf = state.buffers[out_buf as int];
    let dim1d = ThreadDim::Dim1D;

    let decl_val = map_output_declarative(
        spec, out_idx, inputs, old_buf, ws, &dim1d)[j as int];

    if exists|t: nat| t < ws && thread_writes_to(spec, inputs, out_idx, t, j as int) {
        // Some thread writes to j. Pick it.
        let writer = choose|t: nat| t < ws
            && thread_writes_to(spec, inputs, out_idx, t, j as int);

        // Help Z3: writer satisfies the raw exists in map_output_declarative
        assert(arith_eval_with_arrays(&spec.guard, thread_env_1d(writer), inputs) != 0);
        assert(arith_eval_with_arrays(
            &spec.outputs[out_idx as int].scatter,
            thread_env_1d(writer), inputs) == j as int);

        // Prove uniqueness: no other thread writes to j
        assert forall|t: nat|
            0 <= t < ws && t != writer
            implies !#[trigger] thread_writes_to(spec, inputs, out_idx, t, j as int)
        by {
            if thread_writes_to(spec, inputs, out_idx, t, j as int) {
                let env_t = thread_env_1d(t);
                let env_w = thread_env_1d(writer);
                assert(scatter_injective(
                    &spec.outputs[out_idx as int], &spec.guard,
                    inputs, env_t, env_w));
                assert(env_t == env_w);
                assert(env_t[0] == env_w[0]);
            }
        }

        // eval_map_threads gives compute(writer) at position j
        lemma_eval_map_threads_writer_wins(
            spec, inputs, out_buf, out_idx, state, 0, writer, j);
        let compute_w = arith_eval_with_arrays(
            &spec.outputs[out_idx as int].compute,
            thread_env_1d(writer), inputs);
        assert(eval_map_threads(spec, inputs, out_buf, out_idx, state, 0)
            .read(out_buf, j) == compute_w);

        // Bridge: thread_env_for_dim(Dim1D, t) == thread_env_1d(t)
        assert forall|t: nat| thread_env_for_dim(&dim1d, t) == thread_env_1d(t) by {}

        // map_output_declarative: the choose picks some satisfier.
        // Any satisfier must be writer (by uniqueness), so compute value matches.
        let decl_t = choose|t: nat| t < ws
            && arith_eval_with_arrays(&spec.guard, thread_env_for_dim(&dim1d, t), inputs) != 0
            && arith_eval_with_arrays(&spec.outputs[out_idx as int].scatter,
                thread_env_for_dim(&dim1d, t), inputs) == j as int;
        assert(thread_env_for_dim(&dim1d, decl_t) == thread_env_1d(decl_t));
        assert(thread_writes_to(spec, inputs, out_idx, decl_t, j as int));
        if decl_t != writer {
            assert(!thread_writes_to(spec, inputs, out_idx, decl_t, j as int));
        }
        assert(decl_t == writer);
        assert(decl_val == compute_w);
    } else {
        // No thread writes to j
        assert(no_writer_in_range(spec, inputs, out_idx, j as int, 0, ws));
        lemma_eval_map_threads_preserves_non_target(
            spec, inputs, out_buf, out_idx, state, 0, j);
        assert(eval_map_threads(spec, inputs, out_buf, out_idx, state, 0)
            .read(out_buf, j) == old_buf[j as int]);
        // Help Z3: no thread satisfies the raw predicate (with dim1d env) either
        assert forall|t: nat| thread_env_for_dim(&dim1d, t) == thread_env_1d(t) by {}
        assert forall|t: nat| t < ws implies
            !(arith_eval_with_arrays(&spec.guard, #[trigger] thread_env_for_dim(&dim1d, t), inputs) != 0
              && arith_eval_with_arrays(&spec.outputs[out_idx as int].scatter,
                  thread_env_for_dim(&dim1d, t), inputs) == j as int)
        by {
            assert(thread_env_for_dim(&dim1d, t) == thread_env_1d(t));
            assert(!thread_writes_to(spec, inputs, out_idx, t, j as int));
        }
    }
}

/// Map determinism: eval_map_threads (sequential) produces the same buffer
/// as map_output_declarative (order-independent choose-based spec).
///
/// THE key theorem — proves GPU thread execution order doesn't affect results.
/// Map determinism for 1D dispatch.
pub proof fn lemma_map_determinism(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_buf: nat,
    out_idx: nat,
    state: SharedState,
)
    requires
        out_buf < state.num_buffers(),
        out_idx < spec.outputs.len(),
        all_scatter_injective(spec, inputs, out_idx, state.workgroup_size),
        scatter_in_bounds(spec, inputs, out_idx, state.buffer_len(out_buf), state.workgroup_size),
    ensures
        eval_map_threads(spec, inputs, out_buf, out_idx, state, 0).buffers[out_buf as int]
            =~= map_output_declarative(
                spec, out_idx, inputs,
                state.buffers[out_buf as int], state.workgroup_size,
                &ThreadDim::Dim1D),
{
    let old_buf = state.buffers[out_buf as int];
    let result_state = eval_map_threads(spec, inputs, out_buf, out_idx, state, 0);
    let decl = map_output_declarative(spec, out_idx, inputs, old_buf, state.workgroup_size, &ThreadDim::Dim1D);

    // Frame: eval_map_threads preserves buffer structure
    lemma_eval_map_threads_frame(spec, inputs, out_buf, out_idx, state, 0);
    assert(result_state.buffers[out_buf as int].len() == old_buf.len());
    // decl has same length by Seq::new construction
    assert(decl.len() == old_buf.len());

    // Pointwise equality
    assert forall|j: int| 0 <= j < old_buf.len() implies
        result_state.buffers[out_buf as int][j] == decl[j]
    by {
        lemma_map_determinism_at(spec, inputs, out_buf, out_idx, state, j as nat);
        assert(result_state.read(out_buf, j as nat) == result_state.buffers[out_buf as int][j]);
    }
}

// ══════════════════════════════════════════════════════════════
// eval_scan frame conditions
// ══════════════════════════════════════════════════════════════

/// eval_scan preserves other buffers (for any ScanOp).
pub proof fn lemma_eval_scan_preserves_other_buf(
    buffer: nat, op: ScanOp, state: SharedState, other_buf: nat,
)
    requires
        buffer < state.num_buffers(),
        other_buf < state.num_buffers(),
        buffer != other_buf,
    ensures
        eval_scan(buffer, op, state).buffers[other_buf as int]
            == state.buffers[other_buf as int],
{
    // All ScanOps use set_buffer on `buffer`, which doesn't affect other_buf
    match op {
        ScanOp::InclusiveSum => {
            lemma_set_buffer_other(state, buffer,
                inclusive_scan::<int>(state.buffers[buffer as int]), other_buf);
        },
        ScanOp::ExclusiveSum => {
            lemma_set_buffer_other(state, buffer,
                exclusive_scan::<int>(state.buffers[buffer as int]), other_buf);
        },
        ScanOp::ReduceSum => {
            if state.buffers[buffer as int].len() > 0 {
                let data = state.buffers[buffer as int];
                let total = reduce::<int>(data, 0, data.len() as int);
                lemma_set_buffer_other(state, buffer, data.update(0, total), other_buf);
            }
        },
    }
}

/// eval_scan preserves workgroup_size (for any ScanOp).
pub proof fn lemma_eval_scan_preserves_wg_size(buffer: nat, op: ScanOp, state: SharedState)
    requires buffer < state.num_buffers(),
    ensures eval_scan(buffer, op, state).workgroup_size == state.workgroup_size,
{
}

/// eval_scan preserves num_buffers (for any ScanOp).
pub proof fn lemma_eval_scan_preserves_num_bufs(buffer: nat, op: ScanOp, state: SharedState)
    requires buffer < state.num_buffers(),
    ensures eval_scan(buffer, op, state).num_buffers() == state.num_buffers(),
{
    match op {
        ScanOp::InclusiveSum => {
            lemma_set_buffer_preserves_num_buffers(state, buffer,
                inclusive_scan::<int>(state.buffers[buffer as int]));
        },
        ScanOp::ExclusiveSum => {
            lemma_set_buffer_preserves_num_buffers(state, buffer,
                exclusive_scan::<int>(state.buffers[buffer as int]));
        },
        ScanOp::ReduceSum => {
            if state.buffers[buffer as int].len() > 0 {
                let data = state.buffers[buffer as int];
                let total = reduce::<int>(data, 0, data.len() as int);
                lemma_set_buffer_preserves_num_buffers(state, buffer, data.update(0, total));
            }
        },
    }
}

/// eval_scan preserves the length of the scanned buffer (for inclusive/exclusive).
pub proof fn lemma_eval_scan_preserves_buf_len(buffer: nat, op: ScanOp, state: SharedState)
    requires buffer < state.num_buffers(),
    ensures
        eval_scan(buffer, op, state).buffer_len(buffer)
            == state.buffer_len(buffer),
{
}

// ══════════════════════════════════════════════════════════════
// Identity scatter injectivity (generic — works for any kernel)
// ══════════════════════════════════════════════════════════════

/// A kernel where scatter = Var(0) for output `out_idx` is automatically
/// scatter-injective. This is the most common pattern (thread i writes to position i).
pub proof fn lemma_identity_scatter_injective(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_idx: nat,
    workgroup_size: nat,
)
    requires
        out_idx < spec.outputs.len(),
        spec.outputs[out_idx as int].scatter == ArithExpr::Var(0),
    ensures
        all_scatter_injective(spec, inputs, out_idx, workgroup_size),
{
    assert forall|t1: nat, t2: nat|
        t1 < workgroup_size && t2 < workgroup_size && t1 != t2
    implies
        scatter_injective(
            &spec.outputs[out_idx as int], &spec.guard,
            inputs, thread_env_1d(t1), thread_env_1d(t2))
    by {
        // scatter(t1) = Var(0) evaluated at env(t1) = t1
        // scatter(t2) = Var(0) evaluated at env(t2) = t2
        // If t1 != t2, then scatter(t1) != scatter(t2),
        // so the implication in scatter_injective holds vacuously.
    }
}

/// Var(0) scatter is always in bounds when n_pixels <= buffer_len.
pub proof fn lemma_identity_scatter_in_bounds(
    spec: &KernelSpec,
    inputs: Seq<Seq<int>>,
    out_idx: nat,
    n_pixels: nat,
    buf_len: nat,
    workgroup_size: nat,
)
    requires
        out_idx < spec.outputs.len(),
        spec.outputs[out_idx as int].scatter == ArithExpr::Var(0),
        n_pixels <= buf_len,
        // Guard only activates threads < n_pixels
        forall|t: nat| t < workgroup_size
            && arith_eval_with_arrays(&spec.guard, thread_env_1d(t), inputs) != 0
            ==> t < n_pixels,
    ensures
        scatter_in_bounds(spec, inputs, out_idx, buf_len, workgroup_size),
{
}

// ══════════════════════════════════════════════════════════════
// 2D thread environment bridge
// ══════════════════════════════════════════════════════════════

/// thread_env_for_dim(Dim1D, t) == thread_env_1d(t).
/// This allows 1D determinism proofs to apply to Dim1D maps.
pub proof fn lemma_dim1d_env_equals_1d(t: nat)
    ensures thread_env_for_dim(&ThreadDim::Dim1D, t) == thread_env_1d(t),
{
}

/// thread_env_for_dim(Dim2D, t) == thread_env_2d(t % width, t / width).
pub proof fn lemma_dim2d_env(t: nat, width: nat, height: nat)
    requires width > 0,
    ensures thread_env_for_dim(
        &ThreadDim::Dim2D { width, height }, t)
        == thread_env_2d(t % width, t / width),
{
}

// ══════════════════════════════════════════════════════════════
// Loop fusion: two consecutive loops = one loop with summed bounds
// ══════════════════════════════════════════════════════════════

/// Simplified loop: apply body n times. No iter parameter.
pub open spec fn loop_n(body: &Stage, state: SharedState, n: nat) -> SharedState
    decreases n,
{
    if n == 0 { state }
    else { loop_n(body, staged_eval(body, state), (n - 1) as nat) }
}

/// eval_loop(body, state, bound, 0) == loop_n(body, state, bound).
pub proof fn lemma_eval_loop_is_loop_n(
    body: &Stage, state: SharedState, bound: nat,
)
    ensures eval_loop(body, state, bound, 0) == loop_n(body, state, bound),
    decreases bound,
{
    if bound == 0 {
        assert(eval_loop(body, state, 0, 0) == state);
        assert(loop_n(body, state, 0) == state);
    } else {
        let mid = staged_eval(body, state);
        // eval_loop(body, state, bound, 0) = eval_loop(body, mid, bound, 1)
        // loop_n(body, state, bound) = loop_n(body, mid, bound-1)
        // IH: eval_loop(body, mid, bound-1, 0) == loop_n(body, mid, bound-1)
        lemma_eval_loop_is_loop_n(body, mid, (bound - 1) as nat);
        lemma_eval_loop_shift(body, mid, (bound - 1) as nat, 1);
        assert((bound - 1) as nat + 1 == bound);
    }
}

/// General loop shift: eval_loop(body, state, a+b, b) == eval_loop(body, state, a, 0).
/// Both execute exactly `a` iterations of body starting from state.
proof fn lemma_eval_loop_shift(body: &Stage, state: SharedState, a: nat, b: nat)
    ensures eval_loop(body, state, a + b, b) == eval_loop(body, state, a, 0),
    decreases a,
{
    if a == 0 {
        // eval_loop(body, state, b, b) == state (iter >= bound)
        // eval_loop(body, state, 0, 0) == state
    } else {
        let mid = staged_eval(body, state);
        // LHS: eval_loop(body, state, a+b, b) = eval_loop(body, mid, a+b, b+1) [since b < a+b]
        // Apply IH on mid with (a-1, b+1):
        lemma_eval_loop_shift(body, mid, (a - 1) as nat, b + 1);
        // IH gives: eval_loop(body, mid, (a-1)+(b+1), b+1) == eval_loop(body, mid, a-1, 0)
        assert((a - 1) + (b + 1) == a + b);
        // So: eval_loop(body, mid, a+b, b+1) == eval_loop(body, mid, a-1, 0)

        // RHS: eval_loop(body, state, a, 0) = eval_loop(body, mid, a, 1) [since 0 < a]
        // Apply IH on mid with (a-1, 1):
        lemma_eval_loop_shift(body, mid, (a - 1) as nat, 1);
        // IH gives: eval_loop(body, mid, (a-1)+1, 1) == eval_loop(body, mid, a-1, 0)
        assert((a - 1) as nat + 1 == a);
        // So: eval_loop(body, mid, a, 1) == eval_loop(body, mid, a-1, 0)

        // Both sides == eval_loop(body, mid, a-1, 0)
    }
}

/// Loop fusion: loop_n(body, loop_n(body, s, a), b) == loop_n(body, s, a + b).
pub proof fn lemma_loop_n_fusion(
    body: &Stage, state: SharedState, a: nat, b: nat,
)
    ensures loop_n(body, loop_n(body, state, a), b) == loop_n(body, state, a + b),
    decreases a,
{
    if a == 0 {
    } else {
        let mid = staged_eval(body, state);
        lemma_loop_n_fusion(body, mid, (a - 1) as nat, b);
    }
}

/// Two consecutive eval_loops fuse into one.
pub proof fn lemma_loop_fusion(
    body: &Stage, state: SharedState, a: nat, b: nat,
)
    ensures
        eval_loop(body, eval_loop(body, state, a, 0), b, 0)
            == eval_loop(body, state, a + b, 0),
{
    lemma_eval_loop_is_loop_n(body, state, a);
    lemma_eval_loop_is_loop_n(body, loop_n(body, state, a), b);
    lemma_eval_loop_is_loop_n(body, state, a + b);
    lemma_loop_n_fusion(body, state, a, b);
}

// ══════════════════════════════════════════════════════════════
// General seq_stages correctness (inductive)
// ══════════════════════════════════════════════════════════════

/// seq_stages of an empty list is Noop (identity).
pub proof fn lemma_seq_stages_empty(state: SharedState)
    ensures staged_eval(&seq_stages(Seq::<Stage>::empty()), state) == state,
{
}

/// seq_stages distributes: evaluating seq_stages([a] + rest) =
/// evaluating a, then evaluating seq_stages(rest).
pub proof fn lemma_seq_stages_cons(first: Stage, rest: Seq<Stage>, state: SharedState)
    requires rest.len() > 0,
    ensures
        staged_eval(&seq_stages(seq![first].add(rest)), state)
            == staged_eval(&seq_stages(rest), staged_eval(&first, state)),
{
    let full = seq![first].add(rest);
    assert(full.len() >= 2);
    assert(full[0] == first);
    assert(full.skip(1) =~= rest);
    let inner = seq_stages(rest);
    lemma_seq_compose(first, inner, state);
}

// ══════════════════════════════════════════════════════════════
// Map with zero outputs is identity
// ══════════════════════════════════════════════════════════════

/// A Map with no outputs doesn't change the state.
pub proof fn lemma_map_zero_outputs(
    spec: &KernelSpec,
    input_bufs: Seq<nat>,
    output_bufs: Seq<nat>,
    state: SharedState,
    thread_dim: &ThreadDim,
)
    requires
        spec.outputs.len() == 0,
        forall|i: int| 0 <= i < input_bufs.len() ==>
            (input_bufs[i] as int) < state.buffers.len(),
    ensures
        eval_map(spec, input_bufs, output_bufs, state, thread_dim) == state,
{
}

} // verus!
