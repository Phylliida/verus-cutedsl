/// Ground-truth specifications for parallel scan/reduce primitives.
///
/// Generic specs (`reduce`, `inclusive_scan`, `exclusive_scan`) are defined via
/// `sum<R: Ring>` from verus-algebra — the single mathematical source of truth.
/// Since `int` implements `Ring`, these specs can be instantiated directly for
/// integer arithmetic: `reduce::<int>`, `inclusive_scan::<int>`, etc.
///
/// Integer convenience specs (`reduce_int`, `inclusive_scan_int`, `exclusive_scan_int`)
/// wrap the generic specs for `Seq<i64>` input data, interpreting each `i64` as `int`.
///
/// Compact specs (`compact_size`, `compact_result`, `compact_indices`) define
/// stream compaction (filter + pack) as a recursive filter + scan-based indexing.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::sum;
use crate::swizzle::pow2;

verus! {

// ============================================================
// Power-of-2 utilities
// ============================================================

/// Ceiling of log base 2. Smallest k such that pow2(k) >= n.
/// log2_ceil(0) = log2_ceil(1) = 0.
pub open spec fn log2_ceil(n: nat) -> nat
    decreases n,
{
    if n <= 1 { 0 }
    else { 1 + log2_ceil(((n + 1) / 2) as nat) }
}

/// Whether n is a power of 2.
pub open spec fn is_power_of_2(n: nat) -> bool {
    exists|k: nat| pow2(k) == n
}

// ============================================================
// Generic ground-truth specs (any Ring)
// ============================================================

/// Reduce: data[lo] + data[lo+1] + ... + data[hi-1].
pub open spec fn reduce<R: Ring>(data: Seq<R>, lo: int, hi: int) -> R {
    sum::<R>(|i: int| data[i], lo, hi)
}

/// Inclusive prefix sum: result[i] = data[0] + ... + data[i].
pub open spec fn inclusive_scan<R: Ring>(data: Seq<R>) -> Seq<R> {
    Seq::new(data.len(), |i: int| sum::<R>(|j: int| data[j], 0, i + 1))
}

/// Exclusive prefix sum: result[i] = data[0] + ... + data[i-1].
/// result[0] = Ring::zero().
pub open spec fn exclusive_scan<R: Ring>(data: Seq<R>) -> Seq<R> {
    Seq::new(data.len(), |i: int| sum::<R>(|j: int| data[j], 0, i))
}

// ============================================================
// Integer convenience specs (for exec layer with i64 data)
// ============================================================

/// Lift Seq<i64> to Seq<int> for use with generic specs.
pub open spec fn as_int_seq(data: Seq<i64>) -> Seq<int> {
    Seq::new(data.len(), |i: int| data[i] as int)
}

/// Integer reduce: sum of data[lo..hi] interpreted as int.
pub open spec fn reduce_int(data: Seq<i64>, lo: int, hi: int) -> int {
    reduce::<int>(as_int_seq(data), lo, hi)
}

/// Integer inclusive scan.
pub open spec fn inclusive_scan_int(data: Seq<i64>) -> Seq<int> {
    inclusive_scan::<int>(as_int_seq(data))
}

/// Integer exclusive scan.
pub open spec fn exclusive_scan_int(data: Seq<i64>) -> Seq<int> {
    exclusive_scan::<int>(as_int_seq(data))
}

// ============================================================
// Compact/Filter
// ============================================================

/// Number of true values in pred.
pub open spec fn compact_size(pred: Seq<bool>) -> nat
    decreases pred.len(),
{
    if pred.len() == 0 { 0 }
    else {
        compact_size(pred.drop_last())
        + if pred.last() { 1nat } else { 0nat }
    }
}

/// compact_indices[i] = number of true values in pred[0..i].
/// This is the exclusive scan of the predicate interpreted as 0/1.
pub open spec fn compact_indices(pred: Seq<bool>) -> Seq<nat> {
    Seq::new(pred.len(), |i: int| compact_size(pred.take(i)))
}

/// Compact: filtered subsequence preserving order.
pub open spec fn compact_result<T>(data: Seq<T>, pred: Seq<bool>) -> Seq<T>
    recommends data.len() == pred.len(),
    decreases data.len(),
{
    if data.len() == 0 { Seq::empty() }
    else {
        let rest = compact_result(data.drop_last(), pred.drop_last());
        if pred.last() { rest.push(data.last()) }
        else { rest }
    }
}

} // verus!
