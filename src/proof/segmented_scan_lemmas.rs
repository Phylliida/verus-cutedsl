/// Proof lemmas for segmented scan primitives.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan_segmented::*;

verus! {

/// segment_start is always in [0, i].
pub proof fn lemma_segment_start_bounds(flags: Seq<bool>, i: int)
    requires
        0 <= i,
        i < flags.len() as int,
    ensures
        0 <= segment_start(flags, i),
        segment_start(flags, i) <= i,
    decreases (if i > 0 { i } else { 0 }),
{
    if i <= 0 {
    } else if flags[i] {
    } else {
        lemma_segment_start_bounds(flags, i - 1);
    }
}

/// If flags[i] is true, segment_start(flags, i) == i.
pub proof fn lemma_segment_start_at_flag(flags: Seq<bool>, i: int)
    requires
        0 <= i,
        i < flags.len() as int,
        flags[i],
    ensures
        segment_start(flags, i) == i,
{
    // Immediate from definition: if i > 0 && flags[i], segment_start returns i.
    // If i == 0, it returns 0 == i.
}

/// If flags[i] is false and i > 0, segment_start propagates.
pub proof fn lemma_segment_start_continuity(flags: Seq<bool>, i: int)
    requires
        0 < i,
        i < flags.len() as int,
        !flags[i],
    ensures
        segment_start(flags, i) == segment_start(flags, i - 1),
{
    // Direct from definition.
}

/// Step lemma: at a flag boundary, the scan result is just data[i].
/// Otherwise, scan[i] = scan[i-1] + data[i].
pub proof fn lemma_segmented_scan_step(data: Seq<i64>, flags: Seq<bool>, i: int)
    requires
        data.len() == flags.len(),
        0 < i,
        i < data.len() as int,
    ensures
        flags[i] ==>
            segmented_inclusive_scan_int(data, flags)[i] == data[i] as int,
        !flags[i] ==>
            segmented_inclusive_scan_int(data, flags)[i]
                == segmented_inclusive_scan_int(data, flags)[i - 1] + data[i] as int,
{
    let f = |j: int| data[j] as int;
    if flags[i] {
        // segment_start(flags, i) == i, so sum is over [i, i+1) == data[i]
        lemma_sum_single::<int>(f, i);
    } else {
        // segment_start(flags, i) == segment_start(flags, i-1) == lo
        lemma_segment_start_continuity(flags, i);
        lemma_segment_start_bounds(flags, i);
        let lo = segment_start(flags, i);
        // lo <= i, so lo < i + 1
        lemma_sum_peel_last::<int>(f, lo, i + 1);
    }
}

/// The segmented scan result at position 0 is always data[0].
pub proof fn lemma_segmented_scan_base(data: Seq<i64>, flags: Seq<bool>)
    requires
        data.len() == flags.len(),
        data.len() > 0,
    ensures
        segmented_inclusive_scan_int(data, flags)[0] == data[0] as int,
{
    let f = |j: int| data[j] as int;
    // segment_start(flags, 0) == 0, so sum is over [0, 1) == data[0]
    lemma_sum_single::<int>(f, 0);
}

// ============================================================
// Additional segmented scan properties
// ============================================================

/// segment_start is monotonically non-decreasing.
pub proof fn lemma_segment_start_monotone(flags: Seq<bool>, i: int, j: int)
    requires
        0 <= i <= j,
        j < flags.len() as int,
    ensures
        segment_start(flags, i) <= segment_start(flags, j),
    decreases j - i,
{
    if i == j {
    } else {
        // j > i, so j > 0
        if flags[j] {
            // segment_start(flags, j) == j >= i >= segment_start(flags, i)
            lemma_segment_start_bounds(flags, i);
        } else {
            // segment_start(flags, j) == segment_start(flags, j-1)
            lemma_segment_start_monotone(flags, i, j - 1);
        }
    }
}

/// Within a segment, all positions share the same segment_start.
pub proof fn lemma_same_segment(flags: Seq<bool>, i: int, j: int)
    requires
        0 <= i <= j,
        j < flags.len() as int,
        // No flag between i and j (exclusive of i, inclusive of j when j > i)
        forall|k: int| i < k <= j ==> !#[trigger] flags[k],
        // i is either 0 or a flag
        i == 0 || flags[i],
    ensures
        segment_start(flags, j) == i,
    decreases j - i,
{
    if i == j {
        if i == 0 {
            // segment_start(flags, 0) == 0 == i
        } else {
            // flags[i] is true
            lemma_segment_start_at_flag(flags, i);
        }
    } else {
        // j > i, flags[j] is false (from forall)
        assert(!flags[j]);
        lemma_segment_start_continuity(flags, j);
        lemma_same_segment(flags, i, j - 1);
    }
}

/// The segmented scan within a segment equals the non-segmented sum
/// from segment_start to i+1.
/// This is essentially the definition, but useful as a standalone lemma.
pub proof fn lemma_segmented_scan_is_segment_sum(data: Seq<i64>, flags: Seq<bool>, i: int)
    requires
        data.len() == flags.len(),
        0 <= i,
        i < data.len() as int,
    ensures
        segmented_inclusive_scan_int(data, flags)[i]
            == sum::<int>(|j: int| data[j] as int, segment_start(flags, i), i + 1),
{
    // Direct from definition
}

/// At a segment boundary (flags[i] == true), the scan resets to data[i].
pub proof fn lemma_segmented_scan_reset(data: Seq<i64>, flags: Seq<bool>, i: int)
    requires
        data.len() == flags.len(),
        0 <= i,
        i < data.len() as int,
        i == 0 || flags[i],
    ensures
        segmented_inclusive_scan_int(data, flags)[i] == data[i] as int,
{
    if i == 0 {
        lemma_segmented_scan_base(data, flags);
    } else {
        lemma_segmented_scan_step(data, flags, i);
    }
}

/// Segment start is always a valid flag position (within bounds).
pub proof fn lemma_segment_start_in_range(flags: Seq<bool>, i: int)
    requires
        0 <= i,
        i < flags.len() as int,
    ensures
        0 <= segment_start(flags, i),
        segment_start(flags, i) < flags.len() as int,
{
    lemma_segment_start_bounds(flags, i);
}

/// The segmented scan result is non-negative when all data is non-negative
/// and we're at a segment boundary.
pub proof fn lemma_segmented_scan_nonneg_at_boundary(data: Seq<i64>, flags: Seq<bool>, i: int)
    requires
        data.len() == flags.len(),
        0 <= i,
        i < data.len() as int,
        i == 0 || flags[i],
        data[i] >= 0,
    ensures
        segmented_inclusive_scan_int(data, flags)[i] >= 0,
{
    lemma_segmented_scan_reset(data, flags, i);
}

} // verus!
