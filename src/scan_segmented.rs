/// Spec-level segmented scan and reduce primitives.
///
/// A "segmented" scan partitions data into segments defined by a boolean flag
/// array. `flags[i] == true` starts a new segment at position i.
/// Within each segment, the scan/reduce operates independently.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::sum;

verus! {

// ============================================================
// Segment start: find the beginning of the segment containing position i
// ============================================================

/// The start index of the segment containing position i.
/// flags[i] == true means position i starts a new segment.
/// Position 0 always starts a segment (even if flags[0] is false).
pub open spec fn segment_start(flags: Seq<bool>, i: int) -> int
    decreases (if i > 0 { i } else { 0 }),
{
    if i <= 0 { 0 }
    else if flags[i] { i }
    else { segment_start(flags, i - 1) }
}

// ============================================================
// Segmented inclusive scan
// ============================================================

/// Segmented inclusive scan: prefix sum within each segment.
/// result[i] = data[segment_start(flags, i)] + ... + data[i]
pub open spec fn segmented_inclusive_scan_int(data: Seq<i64>, flags: Seq<bool>) -> Seq<int> {
    Seq::new(data.len(), |i: int|
        sum::<int>(|j: int| data[j] as int, segment_start(flags, i), i + 1))
}

// ============================================================
// Bounded partial sums within segments
// ============================================================

/// All partial sums within every segment fit in i64.
pub open spec fn all_segmented_partial_sums_bounded(data: Seq<i64>, flags: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < data.len() as int ==>
        i64::MIN as int <= #[trigger] segmented_inclusive_scan_int(data, flags)[i]
        && segmented_inclusive_scan_int(data, flags)[i] <= i64::MAX as int
}

} // verus!
