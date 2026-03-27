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

// ══════════════════════════════════════════════════════════════
// sum_range properties (bridge to existing scan specs)
// ══════════════════════════════════════════════════════════════

/// sum_range is additive: sum[lo..hi) = sum[lo..mid) + sum[mid..hi).
pub proof fn lemma_sum_range_split(data: Seq<int>, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid, mid <= hi, hi <= data.len(),
    ensures sum_range(data, lo, hi) == sum_range(data, lo, mid) + sum_range(data, mid, hi),
    decreases hi - mid,
{
    if mid == hi {
    } else {
        lemma_sum_range_split(data, lo, mid, hi - 1);
    }
}

/// sum_range of empty range is 0.
pub proof fn lemma_sum_range_empty(data: Seq<int>, lo: int)
    ensures sum_range(data, lo, lo) == 0,
{
}

/// sum_range of a single element.
pub proof fn lemma_sum_range_single(data: Seq<int>, i: int)
    requires 0 <= i < data.len(),
    ensures sum_range(data, i, i + 1) == data[i],
{
    // sum_range(data, i, i+1) = sum_range(data, i, i) + data[i] = 0 + data[i]
    assert(sum_range(data, i, i) == 0);
}

// ══════════════════════════════════════════════════════════════
// Map determinism — declarative spec
// ══════════════════════════════════════════════════════════════

/// Declarative (order-independent) spec for a Map's effect on a single output buffer.
/// For each position j: if some active thread scatters to j, the value
/// is that thread's compute result. Otherwise the value is unchanged.
/// Well-defined because scatter injectivity guarantees at most one writer per position.
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

// NOTE: The theorem that eval_map_threads matches map_output_declarative
// (under scatter injectivity) is the map determinism proof.
// It requires induction on workgroup_size with careful reasoning about
// unique writers. This is a meaningful proof that should be done properly
// in a dedicated session — not stubbed with assume(false).

} // verus!
