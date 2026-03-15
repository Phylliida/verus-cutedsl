/// Tree reduce and Hillis-Steele inclusive scan algorithm specs.
///
/// Tree reduce: log2(n) levels of pairwise combining. At level d, elements at
/// stride pow2(d) accumulate partial sums. After all levels, position n-1 holds
/// the total reduce.
///
/// Hillis-Steele: log2(n) levels where each element adds the element pow2(d)
/// positions before it. After all levels, every position holds its inclusive
/// prefix sum. O(n log n) work, O(log n) depth.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::sum;
use crate::scan::*;
use crate::swizzle::pow2;

verus! {

// ============================================================
// Tree reduce
// ============================================================

/// State of the array after `level` levels of tree reduction.
/// At level 0, state = original data.
/// At level d, position i where (i+1) % pow2(d) == 0 holds
/// sum(data, i+1-pow2(d), i+1).
///
/// This is defined for power-of-2 sized arrays, n = pow2(levels).
/// Only positions at stride pow2(d) are "active" and hold meaningful sums.
pub open spec fn tree_reduce_state(data: Seq<int>, n: nat, level: nat) -> Seq<int>
    recommends n == data.len(),
    decreases level,
{
    if level == 0 {
        data
    } else {
        let prev = tree_reduce_state(data, n, (level - 1) as nat);
        // At level d, active positions are i where (i+1) % pow2(d) == 0.
        // Each active position i adds prev[i - pow2(d-1)] to prev[i].
        let stride = pow2((level - 1) as nat);
        Seq::new(n as nat, |i: int|
            if (i + 1) % (pow2(level) as int) == 0 && i >= stride as int {
                prev[i] + prev[(i - stride as int) as int]
            } else {
                prev[i]
            }
        )
    }
}

/// The invariant maintained by tree reduction: after `level` levels,
/// position i where (i+1) % pow2(level) == 0 holds
/// sum(data, i+1-pow2(level), i+1).
pub open spec fn tree_reduce_invariant(data: Seq<int>, n: nat, level: nat) -> bool {
    let state = tree_reduce_state(data, n, level);
    &&& state.len() == n
    &&& forall|i: int| 0 <= i < n as int && (i + 1) % (pow2(level) as int) == 0
        ==> #[trigger] state[i] == sum::<int>(|j: int| data[j], i + 1 - pow2(level) as int, i + 1)
}

// ============================================================
// Hillis-Steele inclusive scan
// ============================================================

/// State of the array after `level` levels of Hillis-Steele scan.
/// At level 0, state = original data.
/// At each level d, element i adds element (i - pow2(d)) if in bounds.
///
/// Uses double-buffering: reads from previous level, writes to current.
pub open spec fn hillis_steele_state(data: Seq<int>, n: nat, level: nat) -> Seq<int>
    recommends n == data.len(),
    decreases level,
{
    if level == 0 {
        data
    } else {
        let prev = hillis_steele_state(data, n, (level - 1) as nat);
        let stride = pow2((level - 1) as nat);
        Seq::new(n as nat, |i: int|
            if i >= stride as int {
                prev[i] + prev[(i - stride as int) as int]
            } else {
                prev[i]
            }
        )
    }
}

/// The invariant maintained by Hillis-Steele: after `level` levels,
/// element i holds sum(data, max(0, i+1-pow2(level)), i+1).
pub open spec fn hillis_steele_invariant(data: Seq<int>, n: nat, level: nat) -> bool {
    let state = hillis_steele_state(data, n, level);
    &&& state.len() == n
    &&& forall|i: int| 0 <= i < n as int
        ==> {
            let lo = if i + 1 - pow2(level) as int > 0 { i + 1 - pow2(level) as int } else { 0int };
            #[trigger] state[i] == sum::<int>(|j: int| data[j], lo, i + 1)
        }
}

/// When pow2(level) >= n, every element holds its full inclusive prefix sum.
pub open spec fn hillis_steele_complete(data: Seq<int>, n: nat, level: nat) -> bool {
    pow2(level) >= n && hillis_steele_invariant(data, n, level)
    ==> forall|i: int| 0 <= i < n as int
        ==> hillis_steele_state(data, n, level)[i] == inclusive_scan::<int>(as_int_seq_from_ints(data))[i]
}

/// Helper: lift Seq<int> to Seq<int> (identity, for type uniformity with as_int_seq).
pub open spec fn as_int_seq_from_ints(data: Seq<int>) -> Seq<int> {
    data
}

} // verus!
