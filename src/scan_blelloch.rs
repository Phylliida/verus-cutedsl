///  Blelloch exclusive scan algorithm specs.
///
///  Two phases:
///  1. Up-sweep: identical to tree reduce (log2(n) levels of pairwise combining).
///     After all levels, position n-1 holds the total reduce.
///  2. Down-sweep: set root to 0, then distribute partial sums from root to
///     leaves over log2(n) levels. At each level, active pairs swap and accumulate.
///
///  Produces exclusive prefix sum. O(n) work, O(2 log n) depth.
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

///  State of the array after k down-sweep levels.
///
///  k = 0: up-sweep result with root (position n-1) set to 0.
///  k > 0: after processing level (total_levels - k) with stride pow2(total_levels - k).
///    At each level, for each active pair (left = i - stride, right = i):
///      new_right = old_left + old_right
///      new_left = old_right
///
///  Active positions at level d: right positions where (i+1) % (2*pow2(d)) == 0.
pub open spec fn blelloch_downsweep_state(data: Seq<int>, n: nat, total_levels: nat, k: nat) -> Seq<int>
    recommends n == data.len(), is_power_of_2(n), pow2(total_levels) == n,
    decreases k,
{
    if k == 0 {
        //  After up-sweep, set root (n-1) to 0
        tree_reduce_state(data, n, total_levels).update((n - 1) as int, 0int)
    } else {
        let prev = blelloch_downsweep_state(data, n, total_levels, (k - 1) as nat);
        let stride = pow2((total_levels - k) as nat);
        Seq::new(n as nat, |i: int|
            //  Right position: gets old_left + old_right
            if (i + 1) % (2 * stride as int) == 0 && i >= stride as int {
                prev[i] + prev[(i - stride as int) as int]
            }
            //  Left position: gets old_right (from partner i + stride)
            else if (i + 1) % (2 * stride as int) == stride as int {
                prev[(i + stride as int) as int]
            }
            else {
                prev[i]
            }
        )
    }
}

//  ============================================================
//  Invariant
//  ============================================================

///  Expected value at position j after k down-sweep levels.
///
///  Positions at the current stride (pow2(total_levels - k)) hold exclusive
///  prefix sums: sum(data, 0, j + 1 - stride).
///  Positions not yet reached hold their up-sweep values.
pub open spec fn blelloch_expected(data: Seq<int>, n: nat, total_levels: nat, k: nat, j: int) -> int
    recommends 0 <= j < n as int,
{
    let s = pow2((total_levels - k) as nat);
    if (j + 1) % (s as int) == 0 {
        sum::<int>(|i: int| data[i], 0, j + 1 - s as int)
    } else {
        tree_reduce_state(data, n, total_levels)[j]
    }
}

///  The Blelloch down-sweep invariant: state matches expected values at all positions.
pub open spec fn blelloch_downsweep_invariant(data: Seq<int>, n: nat, total_levels: nat, k: nat) -> bool {
    let state = blelloch_downsweep_state(data, n, total_levels, k);
    &&& state.len() == n
    &&& forall|j: int| 0 <= j < n as int ==>
        #[trigger] state[j] == blelloch_expected(data, n, total_levels, k, j)
}

//  ============================================================
//  Result
//  ============================================================

///  The full Blelloch result: up-sweep followed by complete down-sweep.
///  At k = total_levels, pow2(0) = 1 divides all (j+1), so every position
///  holds sum(data, 0, j + 1 - 1) = sum(data, 0, j) = exclusive_scan(data)[j].
pub open spec fn blelloch_result(data: Seq<int>, n: nat, total_levels: nat) -> Seq<int>
    recommends n == data.len(), is_power_of_2(n), pow2(total_levels) == n,
{
    blelloch_downsweep_state(data, n, total_levels, total_levels)
}

} //  verus!
