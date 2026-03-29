///  Runtime segmented inclusive scan and reduce.
use vstd::prelude::*;
use verus_algebra::summation::*;
use crate::scan_segmented::*;
use crate::proof::segmented_scan_lemmas::*;

verus! {

///  Segmented inclusive scan for i64 data.
///  Within each segment (delimited by flags), computes prefix sums independently.
pub fn segmented_inclusive_scan_i64_exec(
    data: &Vec<i64>,
    flags: &Vec<bool>,
) -> (output: Vec<i64>)
    requires
        data@.len() == flags@.len(),
        data@.len() > 0,
        data@.len() <= i64::MAX as nat,
        all_segmented_partial_sums_bounded(data@, flags@),
    ensures
        output@.len() == data@.len(),
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i] as int == segmented_inclusive_scan_int(data@, flags@)[i],
{
    let n = data.len();
    let mut output: Vec<i64> = Vec::new();

    //  First element: always data[0] (segment_start(flags, 0) == 0)
    let first = data[0];
    output.push(first);
    proof {
        lemma_segmented_scan_base(data@, flags@);
    }

    let mut idx: usize = 1;
    while idx < n
        invariant
            1 <= idx <= n,
            n == data@.len(),
            n == flags@.len(),
            output@.len() == idx as nat,
            data@.len() <= i64::MAX as nat,
            all_segmented_partial_sums_bounded(data@, flags@),
            forall|i: int| 0 <= i < idx as int ==>
                output@[i] as int == segmented_inclusive_scan_int(data@, flags@)[i],
        decreases n - idx,
    {
        if flags[idx] {
            //  New segment starts: result is just data[idx]
            let val = data[idx];
            output.push(val);
            proof {
                lemma_segmented_scan_step(data@, flags@, idx as int);
            }
        } else {
            //  Continue segment: result is prev_acc + data[idx]
            let prev = output[(idx - 1) as usize];
            let val = data[idx];
            proof {
                lemma_segmented_scan_step(data@, flags@, idx as int);
                //  prev as int == scan[idx-1]
                //  scan[idx] == scan[idx-1] + data[idx] as int
                //  So prev + val fits in i64 because scan[idx] is bounded.
            }
            let sum: i64 = prev + val;
            output.push(sum);
        }
        idx = idx + 1;
    }
    output
}

///  Segmented reduce: sum within each segment.
///  Returns a vector of the same length as data, where the last element of each
///  segment contains the segment's total. (Callers extract segment totals by
///  checking flags or taking the last element.)
///
///  Simpler API: returns the inclusive scan itself — the reduce value for each
///  segment is at its last position.
pub fn segmented_reduce_i64_exec(
    data: &Vec<i64>,
    flags: &Vec<bool>,
) -> (output: Vec<i64>)
    requires
        data@.len() == flags@.len(),
        data@.len() > 0,
        data@.len() <= i64::MAX as nat,
        all_segmented_partial_sums_bounded(data@, flags@),
    ensures
        output@.len() == data@.len(),
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i] as int == segmented_inclusive_scan_int(data@, flags@)[i],
{
    //  Segmented reduce is just the segmented inclusive scan —
    //  the reduce value for each segment is at its last position.
    segmented_inclusive_scan_i64_exec(data, flags)
}

} //  verus!
