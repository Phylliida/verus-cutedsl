///  Decoupled lookback proofs:
///  - Block 0 reaches Prefix immediately
///  - Lookback correctness via induction
///  - Monotonicity and progress
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_multiblock::*;

verus! {

//  ============================================================
//  Decoupled lookback lemmas
//  ============================================================

///  Block 0 reaches Prefix immediately: its local reduce IS the prefix.
pub proof fn lemma_lookback_block0_prefix(data: Seq<int>, block_size: nat)
    requires
        block_size > 0,
        data.len() >= block_size,
    ensures
        block_reduce(data, block_size, 0) ==
            reduce::<int>(data, 0, block_end(data.len(), block_size, 0) as int),
{
}

///  Lookback correctness: when block b publishes Prefix(v),
///  v = reduce(data, 0, block_end(data.len(), bs, b)).
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

///  States only advance (Invalid -> Aggregate -> Prefix), never regress.
pub proof fn lemma_lookback_monotonicity(old_state: BlockScanState, new_state: BlockScanState)
    requires state_advanced(old_state, new_state),
    ensures match old_state {
        BlockScanState::Prefix { .. } => is_prefix(new_state),
        _ => true,
    },
{
}

///  Lookback progress: if the immediate predecessor has Prefix,
///  then lookback_accumulate returns the predecessor's Prefix value.
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
        //  predecessor is Prefix(v), lookback_accumulate returns v
        //  v = reduce(data, 0, block_end(data.len(), bs, block_id-1))
        //  block_end(data.len(), bs, block_id-1) = min(block_id * bs, data.len()) = block_id * bs
        //  = block_start(bs, block_id)
        assert(block_end(data.len(), block_size, (block_id - 1) as nat)
            == block_start(block_size, block_id)) by (nonlinear_arith)
            requires
                block_id * block_size <= data.len(),
                block_size > 0,
                block_id >= 1;
    }
}

//  ============================================================
//  Three-phase scan correctness
//  ============================================================

///  The three-phase block scan produces the correct inclusive scan.
///
///  Phase 1: each block computes its local inclusive scan and block sum.
///  Phase 2: exclusive scan of block sums gives block prefixes.
///  Phase 3: adding block prefix to each local scan element gives the global scan.
///
///  For element i in block b: output[i] = block_prefix[b] + local_inclusive_scan[i]
///                                      = reduce(data, 0, b*bs) + reduce(data, b*bs, i+1)
///                                      = reduce(data, 0, i+1)
///                                      = inclusive_scan(data)[i]
pub proof fn lemma_three_phase_correct(
    data: Seq<int>, output: Seq<int>,
    block_size: nat, nblocks: nat, block_prefixes: Seq<int>,
)
    requires
        block_size > 0,
        nblocks > 0,
        data.len() > 0,
        //  nblocks covers all data: (nblocks-1)*bs < data.len() <= nblocks*bs
        nblocks * block_size >= data.len(),
        (nblocks - 1) * block_size < data.len(),
        output.len() == data.len(),
        //  Phase 2 is correct
        phase2_complete(data, block_prefixes, block_size, nblocks),
        //  Phase 3: output[i] == block_prefixes[i/bs] + reduce(data, (i/bs)*bs, i+1)
        forall|i: int| 0 <= i < data.len() as int ==> {
            let b = (i as nat) / block_size;
            #[trigger] output[i] == block_prefixes[b as int]
                + reduce::<int>(data, block_start(block_size, b) as int, i + 1)
        },
    ensures
        three_phase_correct(data, output, block_size),
{
    assert forall|i: int| 0 <= i < data.len() as int
    implies #[trigger] output[i] == inclusive_scan::<int>(data)[i]
    by {
        let b = (i as nat) / block_size;
        //  b < nblocks: i < data.len() <= nblocks * block_size, so i / block_size < nblocks
        assert((i as nat) < block_size * nblocks) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(nblocks as int, block_size as int);
        };
        crate::proof::integer_helpers::lemma_div_upper_bound(i as nat, block_size, nblocks);

        //  block_prefixes[b] == reduce(data, 0, b * bs) (from phase2_complete)
        //  output[i] == reduce(data, 0, b*bs) + reduce(data, b*bs, i+1)

        //  Establish bounds for scan_decomposition:
        //  block_start = b * block_size, j = i - b * block_size
        //  Need: 0 <= block_start, 0 <= j, block_start + j + 1 <= data.len()
        let bs_int = block_start(block_size, b) as int;
        let j = i - bs_int;
        //  b * bs <= i (from i / bs == b ... i >= b * bs)
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, block_size as int);
        assert(bs_int <= i);
        assert(j >= 0);
        //  block_start + j + 1 = i + 1 <= data.len()
        assert(bs_int + j + 1 == i + 1);

        crate::proof::scan_lemmas::lemma_scan_decomposition::<int>(data, bs_int, j);
        //  inclusive_scan(data)[i] == reduce(data, 0, bs_int) + reduce(data, bs_int, i+1)
        //                         == block_prefixes[b] + reduce(data, bs_int, i+1)
        //                         == output[i]
    };
}

///  Lookback accumulate correctness: if all predecessors of block_id have
///  published valid states (Aggregate or Prefix), and the chain reaches back
///  to block 0, then lookback_accumulate returns the correct block exclusive prefix.
pub proof fn lemma_lookback_accumulate_correct(
    data: Seq<int>, states: Seq<BlockScanState>,
    block_size: nat, block_id: nat,
)
    requires
        block_size > 0,
        block_id <= states.len(),
        block_id * block_size <= data.len(),
        lookback_state_valid(data, states, block_size),
        //  All predecessors have published (not Invalid)
        forall|b: int| 0 <= b < block_id as int ==>
            is_published(#[trigger] states[b]),
    ensures
        lookback_accumulate(states, block_id)
            == reduce::<int>(data, 0, block_start(block_size, block_id) as int),
    decreases block_id,
{
    if block_id == 0 {
        lemma_sum_empty::<int>(|j: int| data[j], 0, 0);
    } else {
        let prev = (block_id - 1) as nat;
        let bs = block_size;

        //  Key fact: prev == block_id - 1, so (prev+1)*bs = block_id*bs
        assert(prev + 1 == block_id);
        assert((prev + 1) * bs <= data.len());
        assert(block_end(data.len(), bs, prev) == (prev + 1) * bs);
        assert(block_end(data.len(), bs, prev) == block_start(bs, block_id));

        //  Also: prev * bs <= block_id * bs <= data.len()
        assert(prev <= block_id);
        vstd::arithmetic::mul::lemma_mul_inequality(prev as int, block_id as int, bs as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(prev as int, bs as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(block_id as int, bs as int);

        match states[prev as int] {
            BlockScanState::Prefix { value } => {
                //  value == reduce(data, 0, block_end(..., prev))
                //        == reduce(data, 0, block_start(bs, block_id))
            }
            BlockScanState::Aggregate { value } => {
                lemma_lookback_accumulate_correct(data, states, bs, prev);
                //  lookback_accumulate(states, prev) == reduce(data, 0, prev*bs)
                //  value == block_reduce(data, bs, prev) == reduce(data, prev*bs, block_end(..., prev))
                //  Sum: reduce(data, 0, prev*bs) + reduce(data, prev*bs, block_id*bs)
                //     = reduce(data, 0, block_id*bs)
                lemma_sum_split::<int>(
                    |j: int| data[j],
                    0,
                    block_start(bs, prev) as int,
                    block_start(bs, block_id) as int,
                );
            }
            BlockScanState::Invalid => {
                assert(is_published(states[prev as int]));
                assert(false);
            }
        }
    }
}

} //  verus!
