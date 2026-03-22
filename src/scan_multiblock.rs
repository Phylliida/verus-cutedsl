/// Multi-block scan and decoupled lookback specs.
///
/// Three-phase block scan for arbitrary-length arrays:
/// 1. Phase 1: Per-block inclusive scan (local reduces)
/// 2. Phase 2: Exclusive scan of block sums
/// 3. Phase 3: Add block prefix to each element
///
/// Decoupled lookback: spec-only GPU single-pass scan model.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::sum;
use crate::scan::*;
use crate::swizzle::pow2;

verus! {

// ============================================================
// Block decomposition helpers
// ============================================================

/// Start index of block b.
pub open spec fn block_start(block_size: nat, b: nat) -> nat {
    b * block_size
}

/// End index of block b (exclusive), clamped to data length.
pub open spec fn block_end(data_len: nat, block_size: nat, b: nat) -> nat {
    let raw = (b + 1) * block_size;
    if raw <= data_len { raw } else { data_len }
}

/// Length of block b (as int to avoid subtraction issues on nat).
pub open spec fn block_len(data_len: nat, block_size: nat, b: nat) -> int
    recommends block_size > 0,
{
    block_end(data_len, block_size, b) as int - block_start(block_size, b) as int
}

// ============================================================
// Block-level reduce and prefix
// ============================================================

/// Reduce (sum) of a single block.
pub open spec fn block_reduce(data: Seq<int>, block_size: nat, b: nat) -> int {
    reduce::<int>(data, block_start(block_size, b) as int, block_end(data.len(), block_size, b) as int)
}

/// Sequence of block reduces.
pub open spec fn block_reduces(data: Seq<int>, block_size: nat, nblocks: nat) -> Seq<int> {
    Seq::new(nblocks, |i: int| block_reduce(data, block_size, i as nat))
}

/// Exclusive prefix of blocks: sum of all data in blocks [0, b).
/// = reduce(data, 0, b * block_size) when b * block_size <= data.len().
pub open spec fn block_exclusive_prefix(data: Seq<int>, block_size: nat, b: nat) -> int {
    reduce::<int>(data, 0, block_start(block_size, b) as int)
}

// ============================================================
// Phase invariants
// ============================================================

/// Phase 1 complete: block_sums[b] == block_reduce(data, block_size, b).
pub open spec fn phase1_complete(
    data: Seq<int>, block_sums: Seq<int>, block_size: nat, nblocks: nat,
) -> bool {
    &&& block_sums.len() == nblocks
    &&& forall|b: int| 0 <= b < nblocks as int ==>
        #[trigger] block_sums[b] == block_reduce(data, block_size, b as nat)
}

/// Phase 2 complete: block_prefixes[b] == block_exclusive_prefix(data, block_size, b).
pub open spec fn phase2_complete(
    data: Seq<int>, block_prefixes: Seq<int>, block_size: nat, nblocks: nat,
) -> bool {
    &&& block_prefixes.len() == nblocks
    &&& forall|b: int| 0 <= b < nblocks as int ==>
        #[trigger] block_prefixes[b] == block_exclusive_prefix(data, block_size, b as nat)
}

/// Three-phase scan correct: output[i] == inclusive_scan(data)[i].
pub open spec fn three_phase_correct(data: Seq<int>, output: Seq<int>, block_size: nat) -> bool {
    &&& output.len() == data.len()
    &&& forall|i: int| 0 <= i < data.len() ==>
        #[trigger] output[i] == inclusive_scan::<int>(data)[i]
}

// pred_as_int_seq now lives in crate::scan

// ============================================================
// Decoupled lookback (spec-only GPU model)
// ============================================================

/// State of a block in decoupled lookback scan.
pub enum BlockScanState {
    /// Not yet computed.
    Invalid,
    /// Local block reduce published (partial result).
    Aggregate { value: int },
    /// Full inclusive prefix published (complete result).
    Prefix { value: int },
}

/// Whether a state is a Prefix variant.
pub open spec fn is_prefix(s: BlockScanState) -> bool {
    matches!(s, BlockScanState::Prefix { .. })
}

/// Whether a block has published (not Invalid).
pub open spec fn is_published(s: BlockScanState) -> bool {
    !matches!(s, BlockScanState::Invalid)
}

/// Extract value from a Prefix state.
pub open spec fn prefix_value(s: BlockScanState) -> int
    recommends is_prefix(s),
{
    match s {
        BlockScanState::Prefix { value } => value,
        _ => 0,  // unreachable under recommends
    }
}

/// State ordering: Invalid < Aggregate < Prefix.
/// States only advance, never regress.
pub open spec fn state_advanced(old_state: BlockScanState, new_state: BlockScanState) -> bool {
    match (old_state, new_state) {
        (BlockScanState::Invalid, _) => true,
        (BlockScanState::Aggregate { .. }, BlockScanState::Aggregate { .. }) => true,
        (BlockScanState::Aggregate { .. }, BlockScanState::Prefix { .. }) => true,
        (BlockScanState::Prefix { .. }, BlockScanState::Prefix { .. }) => true,
        _ => false,
    }
}

/// Invariant: published values match ground truth.
/// Aggregate(v) at block b -> v == block_reduce(data, bs, b).
/// Prefix(v) at block b -> v == reduce(data, 0, block_end(data.len(), bs, b)).
pub open spec fn lookback_state_valid(
    data: Seq<int>, states: Seq<BlockScanState>, block_size: nat,
) -> bool {
    forall|b: int| 0 <= b < states.len() ==> match #[trigger] states[b] {
        BlockScanState::Invalid => true,
        BlockScanState::Aggregate { value } =>
            value == block_reduce(data, block_size, b as nat),
        BlockScanState::Prefix { value } =>
            value == reduce::<int>(data, 0, block_end(data.len(), block_size, b as nat) as int),
    }
}

/// Lookback accumulation: walk backwards from block_id, summing Aggregate values
/// until finding a Prefix, then add the Prefix value.
/// Returns the total prefix sum for block_id (excluding block_id's own data).
pub open spec fn lookback_accumulate(
    states: Seq<BlockScanState>, block_id: nat,
) -> int
    decreases block_id,
{
    if block_id == 0 {
        0  // Block 0 has no predecessors
    } else {
        match states[(block_id - 1) as int] {
            BlockScanState::Prefix { value } => value,
            BlockScanState::Aggregate { value } =>
                lookback_accumulate(states, (block_id - 1) as nat) + value,
            BlockScanState::Invalid => 0,  // shouldn't happen in valid execution
        }
    }
}

} // verus!
