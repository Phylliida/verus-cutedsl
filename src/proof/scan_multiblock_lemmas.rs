/// Decoupled lookback proofs:
/// - Block 0 reaches Prefix immediately
/// - Lookback correctness via induction
/// - Monotonicity and progress
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_multiblock::*;

verus! {

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
