///  Brent-Kung inclusive scan algorithm specs.
///
///  Two phases:
///  1. Up-sweep: identical to tree reduce (log2(n) levels of pairwise combining).
///     After all levels, position n-1 holds the total reduce.
///  2. Down-sweep: (total_levels - 1) levels. At level k (0-indexed), stride = pow2(total_levels - k - 2).
///     For each position j where (j+1) is an odd multiple of stride and j >= stride:
///     new[j] = old[j] + old[j - stride].
///
///  Produces inclusive prefix sum directly. O(n) work, O(2 log n) depth.
///  Requires power-of-2 sized arrays.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::sum;
use crate::scan::*;
use crate::scan_tree::tree_reduce_state;
use crate::swizzle::pow2;

verus! {

//  ============================================================
//  Down-sweep state
//  ============================================================

///  State of the array after k Brent-Kung down-sweep levels.
///
///  k = 0: the tree reduce result (up-sweep complete).
///  k > 0: at each level, stride = pow2(total_levels - k - 1).
///    For each position j where (j+1) % (2*stride) == stride (odd multiple of stride)
///    and j >= stride: new[j] = old[j] + old[j - stride].
pub open spec fn bk_downsweep_state(data: Seq<int>, n: nat, total_levels: nat, k: nat) -> Seq<int>
    recommends n == data.len(), is_power_of_2(n), pow2(total_levels) == n,
    decreases k,
{
    if k == 0 {
        tree_reduce_state(data, n, total_levels)
    } else {
        let prev = bk_downsweep_state(data, n, total_levels, (k - 1) as nat);
        let stride = pow2((total_levels - k - 1) as nat);
        Seq::new(n as nat, |i: int|
            //  Active: (i+1) is odd multiple of stride, and i >= stride
            if (i + 1) % (2 * stride as int) == stride as int && i >= stride as int {
                prev[i] + prev[(i - stride as int) as int]
            } else {
                prev[i]
            }
        )
    }
}

//  ============================================================
//  Expected value and invariant
//  ============================================================

///  Expected value at position j after k Brent-Kung down-sweep levels.
///
///  The key insight: at level k, all positions where pow2(total_levels - k - 1) divides (j+1)
///  hold inclusive_scan[j] = sum(data, 0, j+1).
///  Positions not at the divisibility threshold keep their tree_reduce values.
///
///  At k = total_levels - 1, threshold = pow2(0) = 1 divides everything.
pub open spec fn bk_expected(data: Seq<int>, n: nat, total_levels: nat, k: nat, j: int) -> int
    recommends 0 <= j < n as int,
{
    let threshold = pow2((total_levels - k - 1) as nat);
    if (j + 1) % (threshold as int) == 0 {
        sum::<int>(|i: int| data[i], 0, j + 1)
    } else {
        tree_reduce_state(data, n, total_levels)[j]
    }
}

///  The Brent-Kung down-sweep invariant: state matches expected values at all positions.
pub open spec fn bk_downsweep_invariant(data: Seq<int>, n: nat, total_levels: nat, k: nat) -> bool {
    let state = bk_downsweep_state(data, n, total_levels, k);
    &&& state.len() == n
    &&& forall|j: int| 0 <= j < n as int ==>
        #[trigger] state[j] == bk_expected(data, n, total_levels, k, j)
}

//  ============================================================
//  Result
//  ============================================================

///  The full Brent-Kung result: up-sweep followed by complete down-sweep.
///  total_levels - 1 down-sweep levels (k = 0, ..., total_levels - 2).
///  At k = total_levels - 1 (after total_levels - 1 levels), threshold = pow2(0) = 1
///  divides all (j+1), so every position holds sum(data, 0, j+1) = inclusive_scan(data)[j].
pub open spec fn bk_result(data: Seq<int>, n: nat, total_levels: nat) -> Seq<int>
    recommends n == data.len(), is_power_of_2(n), pow2(total_levels) == n, total_levels > 0,
{
    bk_downsweep_state(data, n, total_levels, (total_levels - 1) as nat)
}

} //  verus!
