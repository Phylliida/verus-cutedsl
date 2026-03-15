/// Multi-block scan and compact correctness proofs.
///
/// Proves three-phase block scan correctness:
/// - Block prefix is exclusive scan of block reduces
/// - Three-phase result equals inclusive scan
/// - Overflow bounds for block prefixes and phase 3 additions
///
/// Compact proofs:
/// - compact_indices is exclusive scan of pred_as_int
/// - Scatter disjointness for compact
///
/// Decoupled lookback proofs:
/// - Block 0 reaches Prefix immediately
/// - Lookback correctness via induction
/// - Monotonicity and progress
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_multiblock::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;
// partial_sum and all_partial_sums_bounded now come from crate::scan::*

verus! {

// ============================================================
// Block prefix lemmas
// ============================================================

/// block_exclusive_prefix(data, bs, b) == sum of block_reduces for blocks [0, b).
/// I.e., block_exclusive_prefix = reduce(block_reduces, 0, b).
pub proof fn lemma_block_prefix_is_reduce_sum(data: Seq<int>, block_size: nat, b: nat)
    requires
        block_size > 0,
        b * block_size <= data.len(),
    ensures
        block_exclusive_prefix(data, block_size, b)
            == reduce::<int>(block_reduces(data, block_size, b), 0, b as int),
    decreases b,
{
    if b == 0 {
        lemma_sum_empty::<int>(|j: int| data[j], 0, 0);
        lemma_sum_empty::<int>(|j: int| block_reduces(data, block_size, b)[j], 0, 0);
    } else {
        let prev_b = (b - 1) as nat;
        assert(prev_b * block_size <= b * block_size) by (nonlinear_arith)
            requires prev_b == b - 1, b >= 1, block_size > 0;
        lemma_block_prefix_is_reduce_sum(data, block_size, prev_b);

        let lo = (prev_b * block_size) as int;
        let hi = (b * block_size) as int;
        assert(0 <= lo && lo <= hi && hi <= data.len() as int) by (nonlinear_arith)
            requires prev_b == b - 1, b >= 1, block_size > 0,
                     lo == (prev_b * block_size) as int,
                     hi == (b * block_size) as int,
                     b * block_size <= data.len();
        lemma_sum_split::<int>(|j: int| data[j], 0, lo, hi);

        lemma_sum_peel_last::<int>(
            |j: int| block_reduces(data, block_size, b)[j],
            0, b as int,
        );

        assert(block_start(block_size, prev_b) == prev_b * block_size);
        assert(block_end(data.len(), block_size, prev_b) == b * block_size) by {
            assert((prev_b + 1) * block_size == b * block_size) by (nonlinear_arith)
                requires prev_b == b - 1;
        };

        lemma_sum_congruence::<int>(
            |j: int| block_reduces(data, block_size, prev_b)[j],
            |j: int| block_reduces(data, block_size, b)[j],
            0, prev_b as int,
        );
    }
}

/// Three-phase correctness: block_prefix[b] + local_inclusive = inclusive_scan[i].
/// Direct application of lemma_scan_decomposition.
pub proof fn lemma_three_phase_correct(data: Seq<int>, block_size: nat, b: nat, j: int)
    requires
        block_size > 0,
        b * block_size + j + 1 <= data.len(),
        0 <= j,
    ensures
        inclusive_scan::<int>(data)[(b * block_size + j) as int]
            == block_exclusive_prefix(data, block_size, b)
               + reduce::<int>(data, (b * block_size) as int, (b * block_size + j + 1) as int),
{
    lemma_scan_decomposition::<int>(data, (b * block_size) as int, j);
}

/// block_exclusive_prefix is a partial sum, hence bounded by all_partial_sums_bounded.
pub proof fn lemma_block_prefix_bounded(
    original_data: Seq<i64>, block_size: nat, b: nat,
)
    requires
        block_size > 0,
        b * block_size <= original_data.len(),
        all_partial_sums_bounded(original_data),
    ensures
        i64::MIN as int <= block_exclusive_prefix(as_int_seq(original_data), block_size, b),
        block_exclusive_prefix(as_int_seq(original_data), block_size, b) <= i64::MAX as int,
{
    let int_data = as_int_seq(original_data);
    let hi = (b * block_size) as int;
    assert forall|j: int| 0 <= j < hi implies
        int_data[j] == original_data[j] as int by {}
    lemma_sum_congruence::<int>(
        |j: int| int_data[j],
        |j: int| original_data[j] as int,
        0, hi,
    );
    assert(partial_sum(original_data, 0, hi) == block_exclusive_prefix(int_data, block_size, b));
}

/// Phase 3 overflow: prefix + local inclusive fits in i64.
pub proof fn lemma_phase3_overflow(
    original_data: Seq<i64>, block_size: nat, b: nat, j: int,
)
    requires
        block_size > 0,
        0 <= j,
        (b * block_size) as int + j + 1 <= original_data.len(),
        all_partial_sums_bounded(original_data),
    ensures ({
        let int_data = as_int_seq(original_data);
        let val = block_exclusive_prefix(int_data, block_size, b)
            + reduce::<int>(int_data, (b * block_size) as int, (b * block_size) as int + j + 1);
        i64::MIN as int <= val && val <= i64::MAX as int
    }),
{
    let int_data = as_int_seq(original_data);
    let bs = (b * block_size) as int;
    let hi = bs + j + 1;
    lemma_sum_split::<int>(|k: int| int_data[k], 0, bs, hi);
    assert forall|k: int| 0 <= k < hi implies
        int_data[k] == original_data[k] as int by {}
    lemma_sum_congruence::<int>(
        |k: int| int_data[k],
        |k: int| original_data[k] as int,
        0, hi,
    );
    assert(partial_sum(original_data, 0, hi)
        == block_exclusive_prefix(int_data, block_size, b)
           + reduce::<int>(int_data, bs, hi));
}

/// block_sums (as an i64 sequence) have bounded partial sums when original data does.
/// Proved by showing each block_sum partial sum equals a partial sum of original data.
/// Supports non-evenly-divisible data (ceil_div block count): last block may be short.
pub proof fn lemma_block_sums_bounded(
    original_data: Seq<i64>, block_size: nat, nblocks: nat,
)
    requires
        block_size > 0,
        nblocks > 0,
        ((nblocks - 1) as nat) * block_size < original_data.len(),
        all_partial_sums_bounded(original_data),
    ensures ({
        let block_sums_seq: Seq<i64> = Seq::new(nblocks, |i: int|
            block_reduce(as_int_seq(original_data), block_size, i as nat) as i64);
        all_partial_sums_bounded(block_sums_seq)
    }),
{
    let int_data = as_int_seq(original_data);
    let bs: int = block_size as int;
    let nb: int = nblocks as int;
    let data_len: int = original_data.len() as int;
    let block_sums_seq: Seq<i64> = Seq::new(nblocks, |i: int|
        block_reduce(int_data, block_size, i as nat) as i64);

    // Bridge nat precondition to int — Z3 can bridge nat * nat to int * int directly
    assert((nb - 1) * bs < data_len);

    // Step 1: Each block_reduce fits in i64, so as i64 round-trip preserves value.
    assert forall|j: int| 0 <= j < nb implies
        (#[trigger] block_sums_seq[j] as int) == block_reduce(int_data, block_size, j as nat)
    by {
        lemma_block_reduce_bounded(original_data, int_data, block_size, nblocks, j);
    }

    // Step 2: partial_sum(block_sums_seq, lo, hi) == partial_sum(original_data, lo*bs, hi_end)
    // where hi_end = min(hi*bs, data_len). Since 0 <= lo*bs <= hi_end <= data_len,
    // all_partial_sums_bounded gives the bounds.
    assert forall|lo: int, hi: int| 0 <= lo <= hi <= block_sums_seq.len()
    implies i64::MIN as int <= #[trigger] partial_sum(block_sums_seq, lo, hi)
        && partial_sum(block_sums_seq, lo, hi) <= i64::MAX as int
    by {
        lemma_block_partial_sum_eq(original_data, int_data, block_sums_seq, block_size, nblocks, lo, hi);
        let lo_idx = lo * bs;
        let hi_end = if hi * bs <= data_len { hi * bs } else { data_len };
        // 0 <= lo_idx
        assert(0 <= lo_idx) by (nonlinear_arith)
            requires lo >= 0, bs > 0, lo_idx == lo * bs;
        // hi_end <= data_len (by definition)
        assert(hi_end <= data_len);
        // lo_idx <= hi_end
        if lo < hi {
            // lo < nblocks, so lo*bs <= (nblocks-1)*bs < data_len
            assert(lo_idx < data_len) by (nonlinear_arith)
                requires lo < nb, (nb - 1) * bs < data_len, bs > 0,
                         lo_idx == lo * bs;
            assert(lo_idx <= hi_end) by (nonlinear_arith)
                requires lo <= hi, bs > 0, lo_idx == lo * bs,
                         hi_end == (if hi * bs <= data_len { hi * bs } else { data_len }),
                         lo_idx < data_len;
        } else {
            // lo == hi, both partial sums are 0
            lemma_sum_empty::<int>(|j: int| block_sums_seq[j] as int, lo, hi);
        }
    }
}

/// Helper: block_reduce(int_data, bs, j) fits in i64, so as-i64 round-trips.
/// Handles clamped block_end for short last block.
proof fn lemma_block_reduce_bounded(
    original_data: Seq<i64>, int_data: Seq<int>,
    block_size: nat, nblocks: nat, j: int,
)
    requires
        block_size > 0,
        nblocks > 0,
        ((nblocks - 1) as nat) * block_size < original_data.len(),
        int_data == as_int_seq(original_data),
        all_partial_sums_bounded(original_data),
        0 <= j,
        j < nblocks as int,
    ensures
        block_reduce(int_data, block_size, j as nat) as i64 as int
            == block_reduce(int_data, block_size, j as nat),
{
    let bs: int = block_size as int;
    let data_len: int = original_data.len() as int;
    let lo = j * bs;
    assert(0 <= lo) by (nonlinear_arith) requires j >= 0, bs > 0, lo == j * bs;

    // j*bs <= (nblocks-1)*bs < data_len
    // First bridge nat precondition to int (without nonlinear_arith)
    assert((nblocks as int - 1) * bs < data_len);
    assert(lo < data_len) by (nonlinear_arith)
        requires j < nblocks as int, bs > 0, lo == j * bs,
                 (nblocks as int - 1) * bs < data_len;

    // block_start
    assert(block_start(block_size, j as nat) as int == lo);

    // block_end = min((j+1)*bs, data_len) via clamping
    let be = block_end(original_data.len(), block_size, j as nat) as int;
    // Help Z3: block_end is a conditional on nat, bridge to int
    let ghost raw_nat: nat = (j as nat + 1) * block_size;
    // raw_nat as int == (j+1) * bs (bridge nat product to int product)
    assert(raw_nat as int == (j + 1) * bs);
    assert(raw_nat as int > lo) by (nonlinear_arith)
        requires raw_nat as int == (j + 1) * bs, lo == j * bs, bs > 0;
    if raw_nat <= original_data.len() {
        assert(be == raw_nat as int);
    } else {
        assert(be == data_len);
    }
    assert(lo < be);
    assert(be <= data_len);

    // block_reduce = reduce(int_data, lo, be)
    // Bridge int_data to original_data
    assert forall|k: int| lo <= k < be implies int_data[k] == original_data[k] as int by {}
    lemma_sum_congruence::<int>(
        |k: int| int_data[k], |k: int| original_data[k] as int, lo, be,
    );
    // partial_sum(original_data, lo, be) fits in i64
    assert(i64::MIN as int <= partial_sum(original_data, lo, be)
        && partial_sum(original_data, lo, be) <= i64::MAX as int);
}

/// Helper: partial_sum(block_sums_seq, lo, hi) == partial_sum(original_data, lo*bs, hi_end)
/// where hi_end = min(hi*bs, data_len). Handles clamped last block.
proof fn lemma_block_partial_sum_eq(
    original_data: Seq<i64>, int_data: Seq<int>,
    block_sums_seq: Seq<i64>,
    block_size: nat, nblocks: nat,
    lo: int, hi: int,
)
    requires
        block_size > 0,
        nblocks > 0,
        ((nblocks - 1) as nat) * block_size < original_data.len(),
        int_data == as_int_seq(original_data),
        block_sums_seq.len() == nblocks,
        all_partial_sums_bounded(original_data),
        forall|j: int| 0 <= j < nblocks as int ==>
            (#[trigger] block_sums_seq[j] as int) == block_reduce(int_data, block_size, j as nat),
        0 <= lo <= hi,
        hi <= nblocks as int,
    ensures ({
        let bs = block_size as int;
        let hi_end = if hi * bs <= original_data.len() as int { hi * bs }
                     else { original_data.len() as int };
        partial_sum(block_sums_seq, lo, hi) == partial_sum(original_data, lo * bs, hi_end)
    }),
    decreases hi - lo,
{
    let bs: int = block_size as int;
    let data_len: int = original_data.len() as int;
    let hi_end = if hi * bs <= data_len { hi * bs } else { data_len };

    if lo >= hi {
        lemma_sum_empty::<int>(|j: int| block_sums_seq[j] as int, lo, hi);
        // hi_end: when lo == hi, lo*bs == hi*bs.
        // If hi*bs <= data_len: hi_end = hi*bs = lo*bs, empty range → 0.
        // If hi*bs > data_len: hi_end = data_len < lo*bs, also empty → 0.
        lemma_sum_empty::<int>(|j: int| original_data[j] as int, lo * bs, hi_end);
    } else {
        lemma_block_partial_sum_eq(original_data, int_data, block_sums_seq,
            block_size, nblocks, lo, hi - 1);
        lemma_sum_peel_last::<int>(|j: int| block_sums_seq[j] as int, lo, hi);

        let b = (hi - 1) as nat;
        let b_lo = (hi - 1) * bs;

        // IH gives: partial_sum(block_sums_seq, lo, hi-1) == partial_sum(original_data, lo*bs, prev_end)
        // where prev_end = min((hi-1)*bs, data_len).
        // Since hi-1 < nblocks and (nblocks-1)*bs < data_len: (hi-1)*bs <= (nblocks-1)*bs < data_len
        // So prev_end = (hi-1)*bs = b_lo.
        // Bridge nat precondition to int (Z3 handles nat-int conversion)
        assert((nblocks as int - 1) * bs < data_len);
        assert(b_lo < data_len) by (nonlinear_arith)
            requires hi - 1 < nblocks as int, bs > 0, b_lo == (hi - 1) * bs,
                     (nblocks as int - 1) * bs < data_len;
        // So prev_end = b_lo (the conditional picks b_lo since (hi-1)*bs < data_len)

        // block_start and block_end for block b
        assert(block_start(block_size, b) as int == b_lo);
        // block_end(data_len, bs, b) = min((b+1)*bs, data_len) = min(hi*bs, data_len) = hi_end
        // (b+1)*block_size as int == hi*bs — Z3 bridges nat and int
        let be = block_end(original_data.len(), block_size, b) as int;
        // be == hi_end since block_end = min((b+1)*bs, data_len) and hi_end = min(hi*bs, data_len)
        assert(be == hi_end);

        // block_sums_seq[hi-1] as int == block_reduce(int_data, bs, b)
        //   = reduce(int_data, b_lo, be)
        // Bridge to partial_sum(original_data, b_lo, be)
        assert forall|k: int| b_lo <= k < be implies int_data[k] == original_data[k] as int by {}
        lemma_sum_congruence::<int>(
            |k: int| int_data[k], |k: int| original_data[k] as int, b_lo, be,
        );

        // Split original data sum at b_lo
        let orig_lo = lo * bs;
        assert(0 <= orig_lo) by (nonlinear_arith)
            requires lo >= 0, bs > 0, orig_lo == lo * bs;
        assert(orig_lo <= b_lo) by (nonlinear_arith)
            requires lo <= hi - 1, bs > 0, orig_lo == lo * bs, b_lo == (hi - 1) * bs;
        // b_lo <= be: block_end >= block_start
        let ghost raw_b: nat = (b + 1) * block_size;
        assert(raw_b as int == hi * bs);
        assert(raw_b as int > b_lo) by (nonlinear_arith)
            requires raw_b as int == hi * bs, b_lo == (hi - 1) * bs, bs > 0;
        if raw_b <= original_data.len() {
            assert(be == raw_b as int);
        } else {
            assert(be == data_len);
        }
        assert(b_lo <= be);
        lemma_sum_split::<int>(
            |k: int| original_data[k] as int, orig_lo, b_lo, hi_end,
        );
    }
}

// Compact lemmas moved to proof/scan_lemmas.rs

// ============================================================
// Decoupled lookback lemmas
// ============================================================

/// Block 0 reaches Prefix immediately: its local reduce IS the prefix.
pub proof fn lemma_lookback_block0_prefix(data: Seq<int>, block_size: nat)
    requires
        block_size > 0,
        data.len() >= block_size,
    ensures
        block_reduce(data, block_size, 0) ==
            reduce::<int>(data, 0, block_end(data.len(), block_size, 0) as int),
{
}

/// Lookback correctness: when block b publishes Prefix(v),
/// v = reduce(data, 0, block_end(data.len(), bs, b)).
pub proof fn lemma_lookback_correctness(
    data: Seq<int>, states: Seq<BlockScanState>,
    block_size: nat, block_id: nat,
)
    requires
        block_size > 0,
        block_id < states.len(),
        lookback_state_valid(data, states, block_size),
        is_prefix(states[block_id as int]),
    ensures
        prefix_value(states[block_id as int])
            == reduce::<int>(data, 0, block_end(data.len(), block_size, block_id) as int),
{
}

/// States only advance (Invalid -> Aggregate -> Prefix), never regress.
pub proof fn lemma_lookback_monotonicity(old_state: BlockScanState, new_state: BlockScanState)
    requires state_advanced(old_state, new_state),
    ensures match old_state {
        BlockScanState::Prefix { .. } => is_prefix(new_state),
        _ => true,
    },
{
}

/// Lookback progress: if the immediate predecessor has Prefix,
/// then lookback_accumulate returns the predecessor's Prefix value.
pub proof fn lemma_lookback_progress(
    data: Seq<int>, states: Seq<BlockScanState>,
    block_size: nat, block_id: nat,
)
    requires
        block_size > 0,
        block_id <= states.len(),
        block_id * block_size <= data.len(),
        lookback_state_valid(data, states, block_size),
        block_id > 0 ==> is_prefix(states[(block_id - 1) as int]),
    ensures
        lookback_accumulate(states, block_id)
            == reduce::<int>(data, 0, block_start(block_size, block_id) as int),
{
    if block_id == 0 {
        lemma_sum_empty::<int>(|j: int| data[j], 0, 0);
    } else {
        // predecessor is Prefix(v), lookback_accumulate returns v
        // v = reduce(data, 0, block_end(data.len(), bs, block_id-1))
        // block_end(data.len(), bs, block_id-1) = min(block_id * bs, data.len()) = block_id * bs
        // = block_start(bs, block_id)
        assert(block_end(data.len(), block_size, (block_id - 1) as nat)
            == block_start(block_size, block_id)) by (nonlinear_arith)
            requires
                block_id * block_size <= data.len(),
                block_size > 0,
                block_id >= 1;
    }
}

} // verus!
