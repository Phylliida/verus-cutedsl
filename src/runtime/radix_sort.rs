/// Runtime radix sort implementation.
///
/// LSB-first binary radix sort using exclusive scan for rank computation.
/// Each step stably partitions data by one bit position.
use vstd::prelude::*;
use crate::swizzle::pow2;
use crate::scan::*;
// pred_as_int_seq now comes from crate::scan::*
use crate::radix_sort::*;
use crate::proof::scan_lemmas::*;
// compact lemmas now come from crate::proof::scan_lemmas::*
use crate::proof::radix_sort_lemmas::*;
use crate::proof::swizzle_lemmas::{lemma_pow2_positive, lemma_pow2_monotone};
use crate::proof::integer_helpers::*;
use crate::proof::permutation_lemmas::lemma_finite_pigeonhole;
use crate::runtime::scan::*;
use crate::runtime::scan_multiblock::*;

verus! {

/// Convert a Vec<u64> view to a Seq<nat>.
pub open spec fn as_nat_seq(data: Seq<u64>) -> Seq<nat> {
    Seq::new(data.len(), |i: int| data[i] as nat)
}

/// Single radix sort step: stable partition by bit at position `pos`.
/// `shift` must equal pow2(pos) — threaded from the outer loop to avoid recomputation.
pub fn radix_step_exec(data: &Vec<u64>, output: &mut Vec<u64>, pos: u64, shift: u64)
    requires
        old(output)@.len() == data@.len(),
        data@.len() > 0,
        data@.len() <= i64::MAX as nat,
        pos < 64,
        shift as nat == pow2(pos as nat),
        shift > 0,
    ensures
        output@.len() == data@.len(),
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i] as nat == #[trigger] radix_step(as_nat_seq(data@), pos as nat)[i],
{
    let n = data.len() as u64;
    let data_len = data.len();

    let ghost spec_data = as_nat_seq(data@);
    let ghost spec_pred = pred_bit(spec_data, pos as nat);

    // Step 1: Build pred_vec and pred_int
    let mut pred_vec: Vec<bool> = Vec::new();
    let mut pred_int: Vec<i64> = Vec::new();
    let mut pi: u64 = 0;
    while pi < n
        invariant
            pi <= n,
            pred_vec@.len() == pi as nat,
            pred_int@.len() == pi as nat,
            data@.len() == n as nat,
            n as int == data_len as int,
            pos < 64,
            shift as nat == pow2(pos as nat),
            shift > 0,
            spec_data == as_nat_seq(data@),
            spec_pred == pred_bit(spec_data, pos as nat),
            forall|j: int| 0 <= j < pi as int ==>
                #[trigger] pred_vec@[j] == spec_pred[j],
            forall|j: int| 0 <= j < pi as int ==>
                #[trigger] pred_int@[j] == (if spec_pred[j] { 1i64 } else { 0i64 }),
        decreases n - pi,
    {
        let val = data[pi as usize];
        let bit_val = (val / shift) % 2;
        let is_one: bool = bit_val == 1;
        let bit_int: i64 = if is_one { 1i64 } else { 0i64 };
        proof {
            assert(val as nat == spec_data[pi as int]);
            lemma_bit_at_binary(spec_data[pi as int], pos as nat);
        }
        pred_vec.push(is_one);
        pred_int.push(bit_int);
        pi = pi + 1;
    }

    // Step 2: Save last pred, then scan
    let last_pred = pred_int[(n - 1) as usize];

    proof {
        lemma_pred_01_partial_sums_bounded_inner(pred_int@, n);
    }

    let scan_result = exclusive_scan_i64_exec(&pred_int);

    // Step 3: Compute total_ones and count_zeros
    let scan_last = scan_result[(n - 1) as usize];
    proof {
        // Bridge scan_last to bounded value
        lemma_exclusive_scan_01_bound(pred_int@, n);
        assert(last_pred == 0i64 || last_pred == 1i64);
    }
    let total_ones: i64 = scan_last + last_pred;
    let count_zeros_val: i64 = (n as i64) - total_ones;

    // Step 4: Bridge scan_result to compact_indices
    proof {
        assert(0 <= count_zeros_val);
        lemma_count_zeros_bridge(
            pred_int@, spec_pred, spec_data,
            pos as nat, n, total_ones, count_zeros_val,
        );
        // Establish compact_indices bridge for all j
        assert forall|j: int| 0 <= j < n as int implies
            scan_result@[j] as int == #[trigger] compact_indices(spec_pred)[j] as int
        by {
            lemma_compact_indices_bridge_single(
                pred_int@, scan_result@, spec_pred, j, n,
            );
        }
    }

    // Step 5: Scatter loop
    let mut si: u64 = 0;
    while si < n
        invariant
            si <= n,
            output@.len() == n as nat,
            data@.len() == n as nat,
            scan_result@.len() == n as nat,
            pred_vec@.len() == n as nat,
            n <= i64::MAX as u64,
            n > 0,
            n as int == data_len as int,
            pos < 64,
            spec_data == as_nat_seq(data@),
            spec_pred == pred_bit(spec_data, pos as nat),
            count_zeros_val >= 0,
            (count_zeros_val as nat) == count_zeros(spec_data, pos as nat),
            forall|j: int| 0 <= j < n as int ==>
                pred_vec@[j] == spec_pred[j],
            forall|j: int| 0 <= j < n as int ==>
                scan_result@[j] as int == #[trigger] compact_indices(spec_pred)[j] as int,
            // Each already-scattered element is correct
            forall|j: int| 0 <= j < si as int ==>
                (#[trigger] output@[radix_scatter_dest(spec_data, pos as nat, j as nat) as int]) as nat == spec_data[j],
        decreases n - si,
    {
        let val = data[si as usize];
        let rank = scan_result[si as usize];
        let is_one = pred_vec[si as usize];

        proof {
            lemma_bit_at_binary(spec_data[si as int], pos as nat);
            // Trigger the invariant for si
            let ci_si = compact_indices(spec_pred)[si as int];
            assert(scan_result@[si as int] as int == ci_si as int);
            assert(rank as int == ci_si as int);
            assert(rank >= 0);
        }

        let dest: u64;
        if !is_one {
            proof {
                lemma_compact_indices_le_i(spec_pred, si as int);
                assert(!spec_pred[si as int]);
            }
            dest = si - (rank as u64);
        } else {
            proof {
                assert(spec_pred[si as int]);
                lemma_radix_scatter_in_bounds(spec_data, pos as nat, si as nat);
            }
            dest = (count_zeros_val as u64) + (rank as u64);
        }

        proof {
            assert(dest as nat == radix_scatter_dest(spec_data, pos as nat, si as nat));
            lemma_radix_scatter_in_bounds(spec_data, pos as nat, si as nat);
            assert((dest as nat) < n as nat);
        }

        let ghost old_output = output@;
        output.set(dest as usize, val);

        proof {
            assert(output@[dest as int] == val);
            assert(val as nat == spec_data[si as int]);
            // Prove old elements preserved
            assert forall|j: int| 0 <= j < si as int implies
                (#[trigger] output@[radix_scatter_dest(spec_data, pos as nat, j as nat) as int]) as nat == spec_data[j]
            by {
                let d = radix_scatter_dest(spec_data, pos as nat, j as nat);
                lemma_radix_scatter_in_bounds(spec_data, pos as nat, j as nat);
                lemma_radix_scatter_injective(spec_data, pos as nat, j as nat, si as nat);
                assert(d != dest as nat);
                assert(d as int != dest as int);
                assert(output@[d as int] == old_output[d as int]);
            }
        }

        si = si + 1;
    }

    // Final: connect to radix_step
    proof {
        lemma_radix_step_len(spec_data, pos as nat);
        assert forall|i: int| 0 <= i < n as int implies
            output@[i] as nat == #[trigger] radix_step(spec_data, pos as nat)[i]
        by {
            // Find j that scatters to position i
            lemma_radix_scatter_surjective(spec_data, pos as nat, i);
            let j = choose|j: nat| j < spec_data.len()
                && radix_scatter_dest(spec_data, pos as nat, j) as int == i;
            // Trigger the scatter loop invariant with j
            let j_int: int = j as int;
            assert(0 <= j_int && j_int < n as int);
            let d_j = radix_scatter_dest(spec_data, pos as nat, j_int as nat);
            assert(d_j as int == i);
            // From scatter invariant: output@[d_j as int] as nat == spec_data[j_int]
            assert(output@[d_j as int] as nat == spec_data[j_int]);
            assert(output@[i] as nat == spec_data[j_int]);
            // radix_step side
            lemma_radix_scatter_produces_step(spec_data, pos as nat, j);
            assert(radix_step(spec_data, pos as nat)[i] == spec_data[j_int]);
        }
    }
}

// ============================================================
// Helper proof functions
// ============================================================

/// Prove all_partial_sums_bounded for 0/1 i64 array.
proof fn lemma_pred_01_partial_sums_bounded_inner(data: Seq<i64>, n: u64)
    requires
        data.len() == n as nat,
        n <= i64::MAX as u64,
        forall|j: int| 0 <= j < n as int ==>
            (data[j] == 0i64 || data[j] == 1i64),
    ensures
        all_partial_sums_bounded(data),
{
    assert forall|lo: int, hi: int| 0 <= lo <= hi <= data.len()
    implies i64::MIN as int <= #[trigger] partial_sum(data, lo, hi)
        && partial_sum(data, lo, hi) <= i64::MAX as int
    by {
        lemma_pred_01_sum_bounded(data, lo, hi, n);
    }
}

/// Partial sums of 0/1 values are in [0, hi-lo].
proof fn lemma_pred_01_sum_bounded(data: Seq<i64>, lo: int, hi: int, n: u64)
    requires
        data.len() == n as nat,
        0 <= lo, lo <= hi, hi <= n as int,
        n <= i64::MAX as u64,
        forall|j: int| 0 <= j < n as int ==> (data[j] == 0i64 || data[j] == 1i64),
    ensures
        0 <= partial_sum(data, lo, hi),
        partial_sum(data, lo, hi) <= (hi - lo),
    decreases hi - lo,
{
    if lo == hi {
        verus_algebra::summation::lemma_sum_empty::<int>(|j: int| data[j] as int, lo, hi);
    } else {
        verus_algebra::summation::lemma_sum_peel_last::<int>(|j: int| data[j] as int, lo, hi);
        lemma_pred_01_sum_bounded(data, lo, hi - 1, n);
    }
}

/// Exclusive scan of 0/1 array: last element is bounded.
proof fn lemma_exclusive_scan_01_bound(data: Seq<i64>, n: u64)
    requires
        data.len() == n as nat,
        n > 0,
        n <= i64::MAX as u64,
        forall|j: int| 0 <= j < n as int ==> (data[j] == 0i64 || data[j] == 1i64),
    ensures
        0 <= exclusive_scan_int(data)[(n - 1) as int],
        exclusive_scan_int(data)[(n - 1) as int] <= (n - 1) as int,
{
    // exclusive_scan_int(data)[n-1] = sum(|j| as_int_seq(data)[j], 0, n-1)
    // = sum(|j| data[j] as int, 0, n-1) [by congruence]
    // = partial_sum(data, 0, n-1)
    lemma_pred_01_sum_bounded(data, 0, (n - 1) as int, n);
    // partial_sum(data, 0, n-1) in [0, n-1]
    // Need: exclusive_scan_int(data)[n-1] == partial_sum(data, 0, n-1)
    // exclusive_scan_int(data)[n-1] = exclusive_scan::<int>(as_int_seq(data))[n-1]
    //   = sum(|j| as_int_seq(data)[j], 0, n-1)
    // partial_sum(data, 0, n-1) = sum(|j| data[j] as int, 0, n-1)
    // These are equal since as_int_seq(data)[j] == data[j] as int
    assert forall|j: int| 0 <= j < (n - 1) as int implies
        as_int_seq(data)[j] == data[j] as int
    by {}
    verus_algebra::summation::lemma_sum_congruence::<int>(
        |j: int| as_int_seq(data)[j],
        |j: int| data[j] as int,
        0, (n - 1) as int,
    );
}

/// Bridge pred_int[si] to compact_indices[si] (single element).
proof fn lemma_compact_indices_bridge_single(
    original_pred_int: Seq<i64>,
    pred_int_scanned: Seq<i64>,
    spec_pred: Seq<bool>,
    si: int,
    n: u64,
)
    requires
        0 <= si, si < n as int,
        pred_int_scanned.len() == n as nat,
        original_pred_int.len() == n as nat,
        spec_pred.len() == n as nat,
        forall|j: int| 0 <= j < n as int ==>
            pred_int_scanned[j] as int == exclusive_scan_int(original_pred_int)[j],
        forall|j: int| 0 <= j < n as int ==>
            original_pred_int[j] == (if spec_pred[j] { 1i64 } else { 0i64 }),
    ensures
        pred_int_scanned[si] as int == compact_indices(spec_pred)[si] as int,
{
    lemma_compact_indices_is_exclusive_scan(spec_pred, si);
    assert forall|j: int| 0 <= j < si implies
        as_int_seq(original_pred_int)[j] == pred_as_int_seq(spec_pred)[j]
    by {
        assert(as_int_seq(original_pred_int)[j] == original_pred_int[j] as int);
    }
    verus_algebra::summation::lemma_sum_congruence::<int>(
        |j: int| as_int_seq(original_pred_int)[j],
        |j: int| pred_as_int_seq(spec_pred)[j],
        0, si,
    );
}

/// Bridge: count_zeros_val matches spec count_zeros.
proof fn lemma_count_zeros_bridge(
    original_pred_int: Seq<i64>,
    spec_pred: Seq<bool>,
    spec_data: Seq<nat>,
    pos: nat,
    n: u64,
    total_ones: i64,
    count_zeros_val: i64,
)
    requires
        original_pred_int.len() == n as nat,
        spec_pred.len() == n as nat,
        spec_data.len() == n as nat,
        n > 0,
        n <= i64::MAX as u64,
        spec_pred == pred_bit(spec_data, pos),
        forall|j: int| 0 <= j < n as int ==>
            original_pred_int[j] == (if spec_pred[j] { 1i64 } else { 0i64 }),
        total_ones as int == exclusive_scan_int(original_pred_int)[(n - 1) as int]
            + original_pred_int[(n - 1) as int] as int,
        count_zeros_val == (n as i64) - total_ones,
        0 <= count_zeros_val,
    ensures
        count_zeros_val as nat == count_zeros(spec_data, pos),
{
    // total_ones = sum of pred_int[0..n] = compact_size(spec_pred)
    verus_algebra::summation::lemma_sum_peel_last::<int>(
        |j: int| as_int_seq(original_pred_int)[j], 0, n as int,
    );
    assert forall|j: int| 0 <= j < n as int implies
        as_int_seq(original_pred_int)[j] == pred_as_int_seq(spec_pred)[j]
    by {
        assert(as_int_seq(original_pred_int)[j] == original_pred_int[j] as int);
    }
    verus_algebra::summation::lemma_sum_congruence::<int>(
        |j: int| as_int_seq(original_pred_int)[j],
        |j: int| pred_as_int_seq(spec_pred)[j],
        0, n as int,
    );
    lemma_compact_size_equals_sum(spec_pred);
    lemma_complement_compact_size(spec_pred);
}

// lemma_compact_size_equals_sum and lemma_compact_indices_le_i moved to proof/scan_lemmas.rs

/// Scatter surjectivity: for every output position, some input maps there.
proof fn lemma_radix_scatter_surjective(data: Seq<nat>, pos: nat, dest: int)
    requires
        0 <= dest, dest < data.len() as int,
    ensures
        exists|j: nat| j < data.len() && radix_scatter_dest(data, pos, j) as int == dest,
{
    let perm = radix_scatter_perm(data, pos);
    // perm maps into [0, n)
    assert forall|i: nat| i < perm.len() implies #[trigger] perm[i as int] < perm.len() by {
        lemma_radix_scatter_in_bounds(data, pos, i);
    };
    // perm is injective
    assert forall|i: nat, j: nat| i < perm.len() && j < perm.len() && i != j
        implies perm[i as int] != perm[j as int]
    by {
        lemma_radix_scatter_injective(data, pos, i, j);
    };
    lemma_finite_pigeonhole(perm, dest as nat);
    let j = choose|j: nat| j < perm.len() && perm[j as int] == dest as nat;
    assert(radix_scatter_dest(data, pos, j) as int == dest);
}

/// Full radix sort: process bits 0 to num_bits-1.
pub fn radix_sort_exec(data: &mut Vec<u64>, num_bits: u64)
    requires
        old(data)@.len() > 0,
        old(data)@.len() <= i64::MAX as nat,
        num_bits <= 64,
        forall|i: int| 0 <= i < old(data)@.len() as int ==>
            (old(data)@[i] as nat) < pow2(num_bits as nat),
    ensures
        data@.len() == old(data)@.len(),
        is_sorted_nat(as_nat_seq(data@)),
{
    let n = data.len() as u64;
    let ghost original = as_nat_seq(old(data)@);

    if num_bits == 0 {
        proof {
            assert(is_sorted_nat(as_nat_seq(data@))) by {
                assert forall|i: int, j: int| 0 <= i < j < as_nat_seq(data@).len() as int
                implies as_nat_seq(data@)[i] <= as_nat_seq(data@)[j]
                by {
                    assert(pow2(0) == 1nat);
                }
            }
        }
        return;
    }

    // Allocate output buffer
    let mut buf: Vec<u64> = Vec::new();
    let mut bi: u64 = 0;
    while bi < n
        invariant bi <= n, buf@.len() == bi as nat,
        decreases n - bi,
    {
        buf.push(0u64);
        bi = bi + 1;
    }

    // Process each bit position
    let mut step: u64 = 0;
    let mut shift: u64 = 1; // pow2(0) = 1
    while step < num_bits
        invariant
            step <= num_bits,
            data@.len() == n as nat,
            buf@.len() == n as nat,
            n > 0,
            n as nat <= i64::MAX as nat,
            num_bits <= 64,
            num_bits > 0,
            original == as_nat_seq(old(data)@),
            original.len() == n as nat,
            step < num_bits ==> shift as nat == pow2(step as nat),
            step < num_bits ==> shift > 0,
            forall|i: int| 0 <= i < n as int ==>
                (data@[i] as nat) == radix_sort_partial(original, step as nat)[i],
            forall|i: int| 0 <= i < n as int ==>
                (old(data)@[i] as nat) < pow2(num_bits as nat),
        decreases num_bits - step,
    {
        // Capture spec data before this step
        let ghost step_input = as_nat_seq(data@);

        proof {
            // step_input == radix_sort_partial(original, step)
            assert forall|i: int| 0 <= i < n as int implies
                step_input[i] == radix_sort_partial(original, step as nat)[i]
            by {}
        }

        radix_step_exec(data, &mut buf, step, shift);

        // buf now has radix_step(step_input, step)
        // = radix_step(radix_sort_partial(original, step), step)
        // = radix_sort_partial(original, step+1)

        // Copy buf -> data
        let mut ci: u64 = 0;
        while ci < n
            invariant
                ci <= n,
                data@.len() == n as nat,
                buf@.len() == n as nat,
                n > 0,
                n as nat <= i64::MAX as nat,
                num_bits <= 64,
                original == as_nat_seq(old(data)@),
                original.len() == n as nat,
                step < num_bits,
                forall|i: int| 0 <= i < n as int ==>
                    (buf@[i] as nat) == radix_step(step_input, step as nat)[i],
                forall|i: int| 0 <= i < ci as int ==>
                    data@[i] == buf@[i],
                forall|i: int| 0 <= i < n as int ==>
                    (old(data)@[i] as nat) < pow2(num_bits as nat),
            decreases n - ci,
        {
            data.set(ci as usize, buf[ci as usize]);
            ci = ci + 1;
        }

        proof {
            // Prove step_input =~= radix_sort_partial(original, step)
            lemma_radix_sort_len(original, step as nat);
            assert(step_input.len() == radix_sort_partial(original, step as nat).len());
            assert(step_input =~= radix_sort_partial(original, step as nat));
            // Now radix_step(step_input, step) == radix_step(radix_sort_partial(original, step), step)
            //   == radix_sort_partial(original, step + 1) by definition
            assert forall|i: int| 0 <= i < n as int implies
                (data@[i] as nat) == radix_sort_partial(original, (step + 1) as nat)[i]
            by {
                assert(data@[i] == buf@[i]);
                assert(buf@[i] as nat == radix_step(step_input, step as nat)[i]);
            }

        }

        step = step + 1;
        if step < num_bits {
            proof {
                assert(pow2(step as nat) == 2 * pow2((step - 1) as nat));
                lemma_pow2_monotone(step as nat, 63);
                assert(pow2(63) <= u64::MAX as nat) by (compute_only);
            }
            shift = shift * 2;
        }
    }

    // Final: result is sorted
    proof {
        lemma_radix_sort_correct(original, num_bits as nat);
        lemma_radix_sort_len(original, num_bits as nat);
        assert(is_sorted_nat(as_nat_seq(data@))) by {
            assert forall|i: int, j: int| 0 <= i < j < as_nat_seq(data@).len() as int
            implies as_nat_seq(data@)[i] <= as_nat_seq(data@)[j]
            by {
                assert(data@[i] as nat == radix_sort(original, num_bits as nat)[i]);
                assert(data@[j] as nat == radix_sort(original, num_bits as nat)[j]);
            }
        }
    }
}

} // verus!
