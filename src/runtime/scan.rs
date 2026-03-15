/// Runtime implementations of scan/reduce primitives.
///
/// Hillis-Steele inclusive scan: O(n log n) work, O(log n) depth.
/// Tree reduce: derived from Hillis-Steele (take last element).
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_tree::tree_reduce_state;
use crate::scan_blelloch::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;

verus! {

/// Hillis-Steele element value: what element i should hold after `level` levels.
/// This is sum(f, max(0, i+1-pow2(level)), i+1).
pub open spec fn hs_value(data: Seq<i64>, i: int, level: nat) -> int {
    let lo = if i + 1 - pow2(level) as int > 0 { i + 1 - pow2(level) as int } else { 0int };
    sum::<int>(|j: int| data[j] as int, lo, i + 1)
}

/// hs_value addition lemma: adding current[i] + current[partner] gives hs_value at next level.
proof fn lemma_hs_addition(data: Seq<i64>, i: int, d: nat, n: nat)
    requires
        n as int == data.len(),
        0 <= i < n as int,
        i >= pow2(d) as int,
    ensures
        hs_value(data, i, d) + hs_value(data, i - pow2(d) as int, d) == hs_value(data, i, (d + 1) as nat),
{
    let stride = pow2(d);
    let partner = i - stride as int;
    let prev_lo = i + 1 - stride as int;  // > 0 since i >= stride
    let partner_lo = if partner + 1 - stride as int > 0 { partner + 1 - stride as int } else { 0int };
    let next_lo = if i + 1 - pow2((d + 1) as nat) as int > 0 { i + 1 - pow2((d + 1) as nat) as int } else { 0int };

    assert(pow2((d + 1) as nat) == 2 * pow2(d));
    assert(partner + 1 == prev_lo);
    assert(partner_lo == next_lo);
    assert(next_lo <= prev_lo);

    lemma_sum_split::<int>(|j: int| data[j] as int, next_lo, prev_lo, i + 1);
}

/// hs_value is unchanged when i < stride (both levels have same lo = 0).
proof fn lemma_hs_no_change(data: Seq<i64>, i: int, d: nat, n: nat)
    requires
        n as int == data.len(),
        0 <= i < n as int,
        i < pow2(d) as int,
    ensures
        hs_value(data, i, d) == hs_value(data, i, (d + 1) as nat),
{
    assert(pow2((d + 1) as nat) == 2 * pow2(d));
    // i < pow2(d) => i+1 <= pow2(d) => i+1-pow2(d) <= 0 => lo_d = 0
    // i+1-2*pow2(d) < i+1-pow2(d) <= 0 => lo_{d+1} = 0
    // So both are sum(f, 0, i+1)
}

/// hs_value at sufficient level equals inclusive_scan_int.
proof fn lemma_hs_equals_inclusive_scan(data: Seq<i64>, i: int, level: nat)
    requires
        0 <= i < data.len() as int,
        pow2(level) >= data.len(),
    ensures
        hs_value(data, i, level) == inclusive_scan_int(data)[i],
{
    // pow2(level) >= n > i+1, so lo = max(0, i+1-pow2(level)) = 0
    // hs_value = sum(|j| data[j] as int, 0, i+1)
    // inclusive_scan_int(data)[i] = sum::<int>(|j| as_int_seq(data)[j], 0, i+1)
    // as_int_seq(data)[j] = data[j] as int, so these are equal
    // But Z3 needs closure congruence:
    assert forall|j: int| 0 <= j < data.len() as int implies
        as_int_seq(data)[j] == data[j] as int by {}
    lemma_sum_congruence::<int>(
        |j: int| data[j] as int,
        |j: int| as_int_seq(data)[j],
        0, i + 1,
    );
    // sum::<int>.eqv() is == for int, so the sums are equal
}

/// Compute ceil(log2(n)) at runtime.
pub fn log2_ceil_exec(n: u64) -> (result: u64)
    requires n > 0,
    ensures result as nat == log2_ceil(n as nat),
    decreases n,
{
    if n <= 1 {
        return 0;
    }
    // ceil(n/2) = n/2 + n%2, avoids overflow unlike (n+1)/2
    let half: u64 = n / 2 + n % 2;
    proof {
        lemma_half_ceil_bounds(n as nat);
        assert(half as nat == ((n as nat + 1) / 2) as nat);
    }
    let r = log2_ceil_exec(half);
    proof {
        if half as nat >= 2 {
            lemma_log2_ceil_lt(half as nat);
        }
        // r < n, so 1 + r doesn't overflow u64
    }
    1 + r
}

/// Hillis-Steele inclusive scan. Creates a new output Vec.
/// O(n log n) work, O(log n) depth.
pub fn hillis_steele_exec(data: &Vec<i64>, n: u64) -> (output: Vec<i64>)
    requires
        data@.len() == n as nat,
        n > 0,
        all_partial_sums_bounded(data@),
        n <= i64::MAX as u64,
    ensures
        output@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            output@[i] as int == inclusive_scan_int(data@)[i],
{
    let levels = log2_ceil_exec(n);

    // Capture data.len() as usize to establish n fits in usize for casts
    let data_len = data.len();

    // Initialize current buffer from data
    let mut current: Vec<i64> = Vec::new();
    let mut idx: u64 = 0;
    while idx < n
        invariant
            idx <= n,
            current@.len() == idx as nat,
            data@.len() == n as nat,
            n as int == data_len as int,
            forall|j: int| 0 <= j < idx as int ==> current@[j] == data@[j],
        decreases n - idx,
    {
        current.push(data[idx as usize]);
        idx = idx + 1;
    }

    proof {
        // Base case: at level 0, current[i] = data[i] = sum(f, i, i+1) = hs_value(i, 0)
        assert forall|i: int| 0 <= i < n as int implies
            #[trigger] current@[i] as int == hs_value(data@, i, 0)
        by {
            lemma_sum_single::<int>(|j: int| data@[j] as int, i);
            assert(current@[i] == data@[i]);
        }
    }

    // Apply Hillis-Steele levels
    let mut d: u64 = 0;
    let mut stride: u64 = 1;
    while d < levels
        invariant
            d <= levels,
            stride as nat == pow2(d as nat),
            current@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 0,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            data@.len() == n as nat,
            all_partial_sums_bounded(data@),
            // Hillis-Steele invariant
            forall|i: int| 0 <= i < n as int ==>
                #[trigger] current@[i] as int == hs_value(data@, i, d as nat),
        decreases levels - d,
    {
        // Prove stride < n for overflow safety of stride * 2
        proof {
            if n as nat > 1 {
                lemma_pow2_lt_for_sub_levels(n as nat, d as nat);
            } else {
                // n == 1 => levels = log2_ceil(1) = 0, d < 0 impossible
                assert(false);
            }
        }

        // Build next level in a new Vec
        let mut next: Vec<i64> = Vec::new();
        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                next@.len() == i as nat,
                current@.len() == n as nat,
                stride as nat == pow2(d as nat),
                stride < n,
                d < levels,
                levels as nat == log2_ceil(n as nat),
                n > 0,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                data@.len() == n as nat,
                all_partial_sums_bounded(data@),
                forall|k: int| 0 <= k < n as int ==>
                    #[trigger] current@[k] as int == hs_value(data@, k, d as nat),
                forall|k: int| 0 <= k < i as int ==>
                    #[trigger] next@[k] as int == hs_value(data@, k, (d + 1) as nat),
            decreases n - i,
        {
            if i >= stride {
                let partner = (i - stride) as usize;

                proof {
                    let ghost ii = i as int;
                    let ghost partner_int = ii - stride as int;

                    // Prove addition doesn't overflow
                    lemma_hs_addition(data@, ii, d as nat, n as nat);
                    // hs_value(ii, d) + hs_value(partner, d) == hs_value(ii, d+1)
                    // current[i] + current[partner] = hs_value(ii, d+1)

                    // hs_value(ii, d+1) = sum(f, next_lo, ii+1) = partial_sum(data@, next_lo, ii+1)
                    let ghost next_lo = if ii + 1 - pow2((d + 1) as nat) as int > 0 { ii + 1 - pow2((d + 1) as nat) as int } else { 0int };
                    assert(0 <= next_lo && ii + 1 <= n as int);
                    assert(partial_sum(data@, next_lo, ii + 1) == hs_value(data@, ii, (d + 1) as nat));
                    // partial_sum is bounded by all_partial_sums_bounded
                }

                let val = current[i as usize] + current[partner];
                next.push(val);
            } else {
                next.push(current[i as usize]);

                proof {
                    let ghost ii = i as int;
                    lemma_hs_no_change(data@, ii, d as nat, n as nat);
                }
            }

            i = i + 1;
        }

        current = next;

        proof {
            assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
            // stride < n <= i64::MAX, so stride * 2 < 2 * i64::MAX < u64::MAX
        }

        stride = stride * 2;
        d = d + 1;
    }

    proof {
        lemma_log2_ceil_pow2(n as nat);
        assert forall|i: int| 0 <= i < n as int implies
            current@[i] as int == inclusive_scan_int(data@)[i]
        by {
            assert(current@[i] as int == hs_value(data@, i, levels as nat));
            lemma_hs_equals_inclusive_scan(data@, i, levels as nat);
        }
    }

    current
}

/// Reduce: sum all elements. Uses Hillis-Steele and returns the last element.
pub fn reduce_exec(data: &Vec<i64>, n: u64) -> (result: i64)
    requires
        data@.len() == n as nat,
        n > 0,
        all_partial_sums_bounded(data@),
        n <= i64::MAX as u64,
    ensures
        result as int == reduce_int(data@, 0, n as int),
{
    let scan = hillis_steele_exec(data, n);
    let data_len = data.len();
    scan[(n - 1) as usize]
}

// ============================================================
// Blelloch exclusive scan
// ============================================================

/// Tree reduce state at level d matches partial sums for positions active at level d.
/// Used for overflow safety: the addition result is a partial sum of original data.
proof fn lemma_upsweep_overflow_bound(
    original_data: Seq<i64>,
    original_int: Seq<int>,
    n: nat,
    total_levels: nat,
    d: nat,
    i: int,
)
    requires
        original_data.len() == n,
        original_int == as_int_seq(original_data),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        d < total_levels,
        0 <= i < n as int,
        (i + 1) % (pow2((d + 1) as nat) as int) == 0,
        all_partial_sums_bounded(original_data),
    ensures ({
        let next_val = tree_reduce_state(original_int, n, (d + 1) as nat)[i];
        i64::MIN as int <= next_val && next_val <= i64::MAX as int
    }),
{
    use crate::proof::scan_blelloch_lemmas::lemma_tree_reduce_invariant_all;

    let p = pow2((d + 1) as nat);
    crate::proof::swizzle_lemmas::lemma_pow2_positive((d + 1) as nat);

    // i+1 >= pow2(d+1) since (i+1) % pow2(d+1) == 0 and i+1 >= 1
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, p as int);
    let k = (i + 1) / (p as int);
    assert(i + 1 == p as int * k);
    assert(k >= 1) by (nonlinear_arith)
        requires i + 1 == p as int * k, p > 0, i >= 0;

    let lo = i + 1 - p as int;
    let hi = i + 1;
    assert(lo >= 0) by (nonlinear_arith)
        requires i + 1 == p as int * k, k >= 1, p > 0, lo == i + 1 - p as int;

    lemma_tree_reduce_invariant_all(original_int, n, total_levels, (d + 1) as nat);
    // tree_reduce_invariant: state[i] == sum(|j| original_int[j], lo, hi)
    let next_val = tree_reduce_state(original_int, n, (d + 1) as nat)[i];
    assert(next_val == sum::<int>(|j: int| original_int[j], lo, hi));

    // Bridge: sum(|j| original_int[j], lo, hi) == partial_sum(original_data, lo, hi)
    assert forall|j: int| lo <= j < hi implies
        original_int[j] == original_data[j] as int by {}
    lemma_sum_congruence::<int>(
        |j: int| original_int[j],
        |j: int| original_data[j] as int,
        lo, hi,
    );
    assert(partial_sum(original_data, lo, hi) == next_val);
}

/// Down-sweep overflow bound: the addition result at each step is a prefix sum.
proof fn lemma_downsweep_overflow_bound(
    original_data: Seq<i64>,
    original_int: Seq<int>,
    n: nat,
    total_levels: nat,
    dk: nat,
    i: int,
    prev_left: int,
    prev_right: int,
)
    requires
        original_data.len() == n,
        original_int == as_int_seq(original_data),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
        dk < total_levels,
        0 <= i < n as int,
        all_partial_sums_bounded(original_data),
        blelloch_downsweep_invariant(original_int, n, total_levels, dk),
        ({
            let stride = pow2((total_levels - dk - 1) as nat);
            let step = 2 * stride;
            (i + 1) % (step as int) == 0 && i >= stride as int
            && prev_left == blelloch_downsweep_state(original_int, n, total_levels, dk)[(i - stride as int) as int]
            && prev_right == blelloch_downsweep_state(original_int, n, total_levels, dk)[i]
        }),
    ensures
        i64::MIN as int <= prev_left + prev_right && prev_left + prev_right <= i64::MAX as int,
{
    let stride = pow2((total_levels - dk - 1) as nat);
    let step = 2 * stride;
    crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);

    // prev_left + prev_right = next_ds[i] by blelloch_downsweep_state definition
    use crate::proof::scan_blelloch_lemmas::*;
    lemma_blelloch_step(original_int, n, total_levels, dk);
    // blelloch_downsweep_invariant holds at dk+1
    let next = blelloch_downsweep_state(original_int, n, total_levels, (dk + 1) as nat);
    let prev = blelloch_downsweep_state(original_int, n, total_levels, dk);
    // By spec definition: next[i] = prev[i] + prev[i-stride] = prev_right + prev_left
    assert(next[i] == prev[i] + prev[(i - stride as int) as int]);
    assert(next[i] == prev_left + prev_right);

    // next[i] == blelloch_expected at dk+1 == sum(original_int, 0, i+1-stride)
    assert((i + 1) % (stride as int) == 0) by {
        crate::proof::swizzle_lemmas::lemma_mod_pow2_weaken(
            (i + 1) as nat,
            (total_levels - dk) as nat,
            (total_levels - dk - 1) as nat,
        );
    };

    // hi = i + 1 - stride >= 0
    let hi = i + 1 - stride as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, step as int);
    let q = (i + 1) / (step as int);
    assert(i + 1 == step as int * q);
    assert(q >= 1) by (nonlinear_arith)
        requires i + 1 == step as int * q, step > 0, i + 1 > 0;
    assert(hi >= 0) by (nonlinear_arith)
        requires i + 1 == step as int * q, q >= 1, step == 2 * stride, hi == i + 1 - stride as int;

    // next[i] = blelloch_expected at dk+1
    // blelloch_expected at dk+1 with stride = pow2(total_levels - dk - 1):
    //   s = pow2(total_levels - (dk+1)) = pow2(total_levels - dk - 1) = stride
    //   (i+1) % s == 0, so expected = sum(data, 0, i+1-stride) = sum(data, 0, hi)
    assert(next[i] == sum::<int>(|j: int| original_int[j], 0, hi));

    // Bridge: sum(|j| original_int[j], 0, hi) == partial_sum(original_data, 0, hi)
    assert forall|j: int| 0 <= j < hi implies
        original_int[j] == original_data[j] as int by {}
    lemma_sum_congruence::<int>(
        |j: int| original_int[j],
        |j: int| original_data[j] as int,
        0, hi,
    );
    assert(partial_sum(original_data, 0, hi) == next[i]);
    assert(partial_sum(original_data, 0, hi) == prev_left + prev_right);
}

/// ds_pair_processed(j, new_ri, ...) == ds_pair_processed(j, old_ri, ...)
/// when j != old_ri and j != old_ri - stride, and new_ri > old_ri with new_ri <= old_ri + step.
/// The only newly processed positions when advancing ri are old_ri (right) and old_ri - stride (left).
proof fn lemma_ds_pair_processed_frame(
    j: int, old_ri: int, new_ri: int, stride: int, step: int, n: int,
)
    requires
        stride > 0,
        step == 2 * stride,
        0 <= j < n,
        (old_ri + 1) % step == 0,
        old_ri >= stride,
        old_ri < new_ri,
        new_ri <= old_ri + step,
        j != old_ri,
        j != old_ri - stride,
    ensures
        ds_pair_processed(j, new_ri, stride, step)
        == ds_pair_processed(j, old_ri, stride, step),
{
    // Right case: (j+1) % step == 0 && j >= stride && j < ri
    // The only difference is j < old_ri+step vs j < old_ri
    // For j in [old_ri, old_ri+step): could j satisfy (j+1)%step==0 && j >= stride?
    // j != old_ri, so j > old_ri. Then j in (old_ri, old_ri+step).
    // (j+1)%step==0 means j+1 = step*k. old_ri+1 = step*q, so j+1 > step*q.
    // Next multiple: step*(q+1) = old_ri+1+step = old_ri+step+1. But j < old_ri+step, so j+1 <= old_ri+step < old_ri+step+1. So no multiple in range.
    if (j + 1) % step == 0 && j >= stride {
        // j < old_ri iff j < old_ri + step (since j != old_ri and there's no other multiple in [old_ri, old_ri+step))
        if j >= old_ri {
            // j > old_ri (since j != old_ri), j < old_ri + step (for the new case)
            // (j+1) % step == 0 and j+1 > old_ri + 1 = step*q
            // Next multiple after step*q is step*(q+1) = old_ri+1+step
            // j+1 <= old_ri+step, so j+1 < step*(q+1). Contradiction with (j+1)%step==0 and j+1 > step*q
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, step);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(old_ri + 1, step);
            let qj = (j + 1) / step;
            let qr = (old_ri + 1) / step;
            assert(j + 1 == step * qj);
            assert(old_ri + 1 == step * qr);
            assert(qj > qr) by (nonlinear_arith)
                requires j + 1 == step * qj, old_ri + 1 == step * qr, j > old_ri, step > 0;
            assert(qj >= qr + 1) by (nonlinear_arith)
                requires qj > qr;
            assert(j + 1 >= step * (qr + 1)) by (nonlinear_arith)
                requires j + 1 == step * qj, qj >= qr + 1, step > 0;
            assert(j >= old_ri + step) by (nonlinear_arith)
                requires j + 1 >= step * (qr + 1), old_ri + 1 == step * qr, step > 0;
            // j >= old_ri + step contradicts j < old_ri + step (from old_ri+step <= n and j < n... wait, j could equal old_ri + step)
            // Actually we need j < old_ri + step for the claim. But j >= old_ri + step means j is NOT in [old_ri, old_ri+step)
            // So ds_pair_processed(j, old_ri+step, ...) requires j < old_ri+step, but j >= old_ri+step: false = false ✓
            // And ds_pair_processed(j, old_ri, ...) requires j < old_ri, but j >= old_ri: false ✓
            // Both false, so equal ✓
        }
    }
    // Left case: (j+1) % step == stride && j + stride < ri
    if (j + 1) % step == stride {
        // j + stride < old_ri iff j + stride < old_ri + step (for j != old_ri - stride)
        if j + stride >= old_ri {
            // j + stride >= old_ri and j != old_ri - stride, so j + stride > old_ri, i.e., j + stride >= old_ri + 1
            // (j+1)%step == stride means j+1 = step*k + stride, so j+stride = step*k + 2*stride - 1 = step*(k+1) - 1
            // old_ri = step*q - 1 (from (old_ri+1)%step==0)
            // j + stride = step*(k+1) - 1 >= old_ri + 1 = step*q, so step*(k+1) >= step*q + 1, k+1 > q, k >= q
            // j + stride = step*(k+1) - 1. For j + stride < old_ri + step = step*(q+1) - 1: step*(k+1) - 1 < step*(q+1) - 1, k < q.
            // But k >= q, contradiction. So j + stride >= old_ri + step.
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, step);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(old_ri + 1, step);
            let kj = (j + 1) / step;
            let qr = (old_ri + 1) / step;
            assert(j + 1 == step * kj + stride);
            assert(old_ri + 1 == step * qr);
            assert(j + stride == step * (kj + 1) - 1) by (nonlinear_arith)
                requires j + 1 == step * kj + stride, step == 2 * stride;
            assert(kj + 1 > qr) by (nonlinear_arith)
                requires j + stride >= old_ri + 1, j + stride == step * (kj + 1) - 1,
                         old_ri + 1 == step * qr, step > 0, j + stride > old_ri;
            assert(kj >= qr) by (nonlinear_arith) requires kj + 1 > qr;
            assert(j + stride >= old_ri + step) by (nonlinear_arith)
                requires j + stride == step * (kj + 1) - 1,
                         old_ri == step * qr - 1, kj >= qr, step > 0;
        }
    }
}

/// No pairs are processed when ri = step - 1 (initial state of inner loop).
proof fn lemma_no_pairs_processed_initially(j: int, stride: int, step: int)
    requires
        stride > 0,
        step == 2 * stride,
        j >= 0,
    ensures !ds_pair_processed(j, step - 1, stride, step),
{
    // Right case: (j+1) % step == 0 && j >= stride && j < step-1
    if (j + 1) % step == 0 {
        if j >= stride {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, step);
            let q = (j + 1) / step;
            assert(j + 1 == step * q);
            assert(q >= 1) by (nonlinear_arith)
                requires j + 1 == step * q, step > 0, j >= 0;
            assert(j >= step - 1) by (nonlinear_arith)
                requires j + 1 == step * q, q >= 1, step > 0;
            // j >= step - 1 means j < step - 1 is false
        }
    }
    // Left case: (j+1) % step == stride && j + stride < step - 1
    if (j + 1) % step == stride {
        if j + stride < step - 1 {
            assert(j + 1 < step) by (nonlinear_arith)
                requires j + stride < step - 1, step == 2 * stride, stride > 0;
            assert(j + 1 >= 1);
            vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, step as nat);
            // (j+1) % step == j+1, but we assumed (j+1) % step == stride
            // j+1 == stride but j + stride < step - 1 = 2*stride - 1 => j < stride - 1 => j+1 < stride
            assert(false);
        }
    }
}

/// Whether position j has been processed in the down-sweep inner loop.
/// A position is processed if it's a right position of a processed pair (j < ri)
/// or the left partner of a processed pair (j + stride < ri).
pub open spec fn ds_pair_processed(j: int, ri: int, stride: int, step: int) -> bool {
    ((j + 1) % step == 0 && j >= stride && j < ri)
    || ((j + 1) % step == stride && j + stride < ri)
}

/// Down-sweep inner loop invariant: processed positions match next_ds, others match prev_ds.
pub open spec fn ds_inner_inv(
    data_view: Seq<i64>, j: int, ri: int, stride: int, step: int,
    prev_ds: Seq<int>, next_ds: Seq<int>,
) -> bool {
    if ds_pair_processed(j, ri, stride, step) {
        data_view[j] as int == next_ds[j]
    } else {
        data_view[j] as int == prev_ds[j]
    }
}

/// Blelloch in-place exclusive scan. O(n) work, O(2 log n) depth.
/// Requires power-of-2 sized input.
pub fn blelloch_exclusive_scan_exec(data: &mut Vec<i64>, n: u64)
    requires
        old(data)@.len() == n as nat,
        n > 0,
        is_power_of_2(n as nat),
        all_partial_sums_bounded(old(data)@),
        n <= i64::MAX as u64,
    ensures
        data@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            data@[i] as int == exclusive_scan_int(old(data)@)[i],
{
    let ghost original_data = old(data)@;
    let ghost original_int = as_int_seq(original_data);
    let levels = log2_ceil_exec(n);
    let data_len = data.len();

    // Handle n = 1: exclusive_scan[0] = sum(data, 0, 0) = 0
    if n == 1 {
        data.set(0, 0i64);
        proof {
            lemma_sum_empty::<int>(|j: int| as_int_seq(original_data)[j], 0, 0);
        }
        return;
    }

    // n >= 2, so levels >= 1
    proof {
        lemma_pow2_log2_ceil_exact(n as nat);
        // pow2(levels) == n
    }

    let ghost total_levels = levels as nat;

    // ============================================================
    // UP-SWEEP (tree reduce, in-place)
    // ============================================================
    let mut d: u64 = 0;
    let mut stride: u64 = 1;
    while d < levels
        invariant
            d <= levels,
            stride as nat == pow2(d as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == tree_reduce_state(original_int, n as nat, d as nat)[j],
        decreases levels - d,
    {
        proof {
            lemma_pow2_lt_for_sub_levels(n as nat, d as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_positive(d as nat);
        }

        let ghost prev_state = tree_reduce_state(original_int, n as nat, d as nat);
        let ghost next_state = tree_reduce_state(original_int, n as nat, (d + 1) as nat);
        let step: u64 = 2 * stride;

        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                data@.len() == n as nat,
                stride as nat == pow2(d as nat),
                stride > 0,
                stride < n,
                step == 2 * stride,
                d < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                prev_state == tree_reduce_state(original_int, n as nat, d as nat),
                next_state == tree_reduce_state(original_int, n as nat, (d + 1) as nat),
                // Processed positions match next level
                forall|j: int| 0 <= j < i as int ==>
                    data@[j] as int == next_state[j],
                // Unprocessed positions match current level
                forall|j: int| i as int <= j < n as int ==>
                    data@[j] as int == prev_state[j],
            decreases n - i,
        {
            if (i + 1) % step == 0 && i >= stride {
                // Active position: data[i] += data[i - stride]
                let partner = (i - stride) as usize;

                proof {
                    // data[partner] was already processed (partner < i).
                    // next_state[partner] == prev_state[partner] because partner is not active.
                    // Show (partner+1) % pow2(d+1) != 0:
                    let pi = partner as int + 1;
                    assert(pi == i as int + 1 - stride as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 1) as int, step as int);
                    let q = ((i + 1) as int) / (step as int);
                    assert(i as int + 1 == step as int * q);
                    assert(q >= 1) by (nonlinear_arith)
                        requires i as int + 1 == step as int * q, step > 0, i as int + 1 > 0;
                    assert(pi == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires pi == i as int + 1 - stride as int,
                                 i as int + 1 == step as int * q, step == 2 * stride;
                    assert(pi == step as int * (q - 1) + stride as int) by (nonlinear_arith)
                        requires pi == stride as int * (2 * q - 1), step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        pi, step as int, q - 1, stride as int
                    );
                    assert(pi % (step as int) != 0) by (nonlinear_arith)
                        requires pi % (step as int) == stride as int, stride > 0;

                    // So next_state[partner] == prev_state[partner]
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                    assert(next_state[partner as int] == prev_state[partner as int]);

                    // Overflow proof
                    lemma_upsweep_overflow_bound(
                        original_data, original_int, n as nat, total_levels,
                        d as nat, i as int,
                    );
                }

                let val = data[i as usize] + data[partner];
                data.set(i as usize, val);
            } else {
                // Non-active: next_state[i] == prev_state[i] (Z3 sees via definition unfolding)
                proof {
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                }
            }

            i = i + 1;
        }

        proof {
            assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
        }
        stride = stride * 2;
        d = d + 1;
    }

    // ============================================================
    // ROOT ZEROING
    // ============================================================
    let ghost upsweep_final = tree_reduce_state(original_int, n as nat, total_levels);
    data.set((n - 1) as usize, 0i64);

    proof {
        use crate::scan_blelloch::*;
        // Prove data now matches blelloch_downsweep_state(original_int, n, levels, 0)
        let ds0 = blelloch_downsweep_state(original_int, n as nat, total_levels, 0);
        assert forall|j: int| 0 <= j < n as int
        implies data@[j] as int == ds0[j]
        by {
            if j == n as int - 1 {
                // data[n-1] = 0, ds0[n-1] = 0 (root set to 0)
            } else {
                // data[j] unchanged, ds0[j] = upsweep_final[j]
            }
        }
    }

    // ============================================================
    // DOWN-SWEEP
    // ============================================================
    let mut dk: u64 = 0;
    let mut ds_stride: u64 = n / 2;  // pow2(levels - 1)
    proof {
        crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - 1) as nat);
        assert(pow2(total_levels) == 2 * pow2((total_levels - 1) as nat));
        assert(ds_stride as nat == pow2((total_levels - 1) as nat)) by (nonlinear_arith)
            requires
                pow2(total_levels) == n as nat,
                pow2(total_levels) == 2 * pow2((total_levels - 1) as nat),
                ds_stride == n / 2,
                n > 1;
    }

    proof {
        use crate::proof::scan_blelloch_lemmas::lemma_blelloch_base;
        lemma_blelloch_base(original_int, n as nat, total_levels);
    }

    while dk < levels
        invariant
            dk <= levels,
            dk < levels ==> ds_stride as nat == pow2((total_levels - dk - 1) as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            total_levels > 0,
            blelloch_downsweep_invariant(original_int, n as nat, total_levels, dk as nat),
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == blelloch_downsweep_state(original_int, n as nat, total_levels, dk as nat)[j],
        decreases levels - dk,
    {
        let ghost prev_ds = blelloch_downsweep_state(original_int, n as nat, total_levels, dk as nat);
        let ghost next_ds = blelloch_downsweep_state(original_int, n as nat, total_levels, (dk + 1) as nat);
        let stride = ds_stride;

        proof {
            crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);
            // 2 * stride = pow2(total_levels - dk) <= pow2(total_levels) = n
            assert(pow2((total_levels - dk) as nat) == 2 * pow2((total_levels - dk - 1) as nat));
            crate::proof::swizzle_lemmas::lemma_pow2_monotone((total_levels - dk) as nat, total_levels);
            assert(2 * stride as nat <= n as nat);
        }

        let step: u64 = 2 * stride;

        // Inner loop: iterate right positions
        let mut ri: u64 = step - 1;  // first right position

        // Establish invariants before the loop
        proof {
            // (ri + 1) % step == 0: ri = step - 1, so ri + 1 = step, step % step = 0
            assert((ri as int + 1) % (step as int) == 0) by {
                assert(ri as int + 1 == step as int);
            };

            // ds_inner_inv: no pairs processed yet (ri = step-1)
            assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
            implies ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds)
            by {
                assert(data@[j] as int == prev_ds[j]);
                lemma_no_pairs_processed_initially(j, stride as int, step as int);
            }
        }

        while ri < n
            invariant
                data@.len() == n as nat,
                stride as nat == pow2((total_levels - dk - 1) as nat),
                step == 2 * stride,
                stride > 0,
                dk < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                total_levels > 0,
                prev_ds == blelloch_downsweep_state(original_int, n as nat, total_levels, dk as nat),
                next_ds == blelloch_downsweep_state(original_int, n as nat, total_levels, (dk + 1) as nat),
                blelloch_downsweep_invariant(original_int, n as nat, total_levels, dk as nat),
                ri >= step - 1,
                ri < n ==> ri >= stride,
                ri < n ==> (ri + 1) % (step as int) == 0,
                // All positions: match next_ds if processed, prev_ds otherwise
                forall|j: int| #![trigger data@[j]] 0 <= j < n as int ==>
                    ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds),
            decreases n - ri,
        {
            let right = ri as usize;
            let left = (ri - stride) as usize;

            // Capture old values
            let temp_right = data[right];
            let temp_left = data[left];

            proof {
                // Verify left and right are unprocessed: ri is the current right,
                // so ri >= ri means it's unprocessed. And left = ri - stride,
                // (left+1) % step == stride, and left + stride == ri >= ri, so unprocessed.
                let li = ri as int - stride as int;
                assert((li + 1) % (step as int) == stride as int) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((ri + 1) as int, step as int);
                    let q = ((ri + 1) as int) / (step as int);
                    assert(ri as int + 1 == step as int * q);
                    assert(li + 1 == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires li == ri as int - stride as int,
                                 ri as int + 1 == step as int * q,
                                 step == 2 * stride;
                    assert(li + 1 == step as int * (q - 1) + stride as int) by (nonlinear_arith)
                        requires li + 1 == stride as int * (2 * q - 1),
                                 step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        li + 1, step as int, q - 1, stride as int
                    );
                };

                // ri is an unprocessed right (ri >= ri), so data[ri] == prev_ds[ri]
                // left is an unprocessed left (left + stride == ri >= ri), so data[left] == prev_ds[left]
                assert(temp_right as int == prev_ds[ri as int]);
                assert(temp_left as int == prev_ds[li]);

                // Overflow: temp_left + temp_right = next_ds[ri] which is a bounded prefix sum
                lemma_downsweep_overflow_bound(
                    original_data, original_int, n as nat, total_levels,
                    dk as nat, ri as int,
                    temp_left as int, temp_right as int,
                );
            }

            // new_left = old_right, new_right = old_left + old_right
            data.set(left, temp_right);
            data.set(right, (temp_left + temp_right));

            proof {
                let li = ri as int - stride as int;

                // Show data@[ri] == next_ds[ri]
                assert(data@[ri as int] as int == temp_left as int + temp_right as int);
                assert(data@[ri as int] as int == next_ds[ri as int]);
                // Show data@[li] == next_ds[li]
                assert(data@[li] as int == temp_right as int);
                assert(data@[li] as int == next_ds[li]);

                // For j != ri && j != li: data unchanged, old ds_inner_inv still applies
                // Since ri and li are the only modified positions, and data.set preserves other indices
            }

            // Advance to next right position
            let ghost old_ri = ri as int;
            if ri + step < n {
                ri = ri + step;
                proof {
                    let li = old_ri - stride as int;
                    // Prove (ri + 1) % step == 0
                    assert(ri as int == old_ri + step as int);
                    assert(ri as int + 1 == old_ri + 1 + step as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((old_ri + 1) as int, step as int);
                    let q = ((old_ri + 1) as int) / (step as int);
                    assert(old_ri + 1 == step as int * q);
                    assert(ri as int + 1 == step as int * (q + 1)) by (nonlinear_arith)
                        requires ri as int + 1 == old_ri + 1 + step as int,
                                 old_ri + 1 == step as int * q;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        ri as int + 1, step as int, q + 1, 0int
                    );

                    // Re-establish ds_inner_inv for new ri = old_ri + step
                    assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                    implies ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds)
                    by {
                        if j == old_ri {
                            // Right position just processed: data == next_ds
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else if j == li {
                            // Left position just processed: data == next_ds
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else {
                            // data@[j] unchanged, ds_pair_processed unchanged
                            lemma_ds_pair_processed_frame(
                                j, old_ri, ri as int, stride as int, step as int, n as int
                            );
                        }
                    }
                }
            } else {
                ri = n; // exit
                proof {
                    let li = old_ri - stride as int;
                    // Re-establish ds_inner_inv for ri = n
                    assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                    implies ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds)
                    by {
                        if j == old_ri {
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else if j == li {
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else {
                            lemma_ds_pair_processed_frame(
                                j, old_ri, n as int, stride as int, step as int, n as int
                            );
                        }
                    }
                }
            }
        }

        // After inner loop: all pairs processed, data matches next_ds
        proof {
            // Show n == step * pow2(dk) for left-partner bound proofs
            let ghost num_pairs = pow2(dk as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_mul((total_levels - dk) as nat, dk as nat);
            assert(n as nat == step as nat * num_pairs) by {
                assert(step as nat == pow2((total_levels - dk) as nat));
                assert((total_levels - dk) as nat + dk as nat == total_levels);
            };

            assert forall|j: int| 0 <= j < n as int
            implies data@[j] as int == next_ds[j]
            by {
                if (j + 1) % (step as int) == 0 && j >= stride as int {
                    // Right position, j < n <= ri, so processed
                    assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                } else if (j + 1) % (step as int) == stride as int {
                    // Left position: show j + stride < n (so its right partner exists)
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((j + 1) as int, step as int);
                    let q = ((j + 1) as int) / (step as int);
                    assert(j + 1 == step as int * q + stride as int);
                    // j + stride + 1 = step*(q+1)
                    let partner = j + stride as int;
                    assert(partner + 1 == step as int * (q + 1)) by (nonlinear_arith)
                        requires j + 1 == step as int * q + stride as int,
                                 partner == j + stride as int, step == 2 * stride;
                    // q+1 <= num_pairs since j+1 <= n = step * num_pairs
                    let np = num_pairs as int;
                    assert(q + 1 <= np) by (nonlinear_arith)
                        requires j + 1 <= n as int,
                                 j + 1 == step as int * q + stride as int,
                                 n as int == step as int * np,
                                 stride > 0;
                    assert(partner < n as int) by (nonlinear_arith)
                        requires partner + 1 == step as int * (q + 1),
                                 q + 1 <= np, n as int == step as int * np, step > 0;
                    assert(partner < ri as int);
                    assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                } else {
                    // Not a pair position: next_ds[j] == prev_ds[j]
                    assert(!ds_pair_processed(j, ri as int, stride as int, step as int));
                    assert(data@[j] as int == prev_ds[j]);
                    assert(prev_ds[j] == next_ds[j]);
                }
            }
        }

        proof {
            use crate::proof::scan_blelloch_lemmas::lemma_blelloch_step;
            lemma_blelloch_step(original_int, n as nat, total_levels, dk as nat);
        }

        dk = dk + 1;
        if dk < levels {
            proof {
                assert(pow2((total_levels - dk - 1) as nat) == ds_stride as nat / 2) by {
                    assert(pow2((total_levels - (dk - 1) - 1) as nat) == ds_stride as nat);
                    assert((total_levels - (dk - 1) - 1) as nat == (total_levels - dk) as nat);
                    assert(pow2((total_levels - dk) as nat) == 2 * pow2((total_levels - dk - 1) as nat));
                    crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);
                };
            }
            ds_stride = ds_stride / 2;
        }
    }

    // ============================================================
    // FINAL: blelloch_result == exclusive_scan_int
    // ============================================================
    proof {
        use crate::proof::scan_blelloch_lemmas::lemma_blelloch_correct;
        lemma_blelloch_correct(original_int, n as nat, total_levels);
        // blelloch_result[j] == exclusive_scan::<int>(original_int)[j]
        // exclusive_scan_int(original_data) = exclusive_scan::<int>(as_int_seq(original_data))
        //                                   = exclusive_scan::<int>(original_int)
        assert forall|j: int| 0 <= j < n as int
        implies data@[j] as int == exclusive_scan_int(original_data)[j]
        by {
            assert(data@[j] as int == blelloch_downsweep_state(original_int, n as nat, total_levels, total_levels)[j]);
            assert(blelloch_result(original_int, n as nat, total_levels)[j] == exclusive_scan::<int>(original_int)[j]);
        }
    }
}

// ============================================================
// Brent-Kung inclusive scan
// ============================================================

/// Whether position j is active at Brent-Kung down-sweep level with given stride.
/// Active = (j+1) is an odd multiple of stride, and j >= stride.
pub open spec fn bk_active(j: int, stride: int, step: int) -> bool {
    (j + 1) % step == stride && j >= stride
}

/// Whether position j has been processed in the Brent-Kung inner loop.
pub open spec fn bk_pair_processed(j: int, ri: int, stride: int, step: int) -> bool {
    bk_active(j, stride, step) && j < ri
}

/// Brent-Kung inner loop invariant: processed positions match next state, others match prev.
pub open spec fn bk_inner_inv(
    data_view: Seq<i64>, j: int, ri: int, stride: int, step: int,
    prev: Seq<int>, next: Seq<int>,
) -> bool {
    if bk_pair_processed(j, ri, stride, step) {
        data_view[j] as int == next[j]
    } else {
        data_view[j] as int == prev[j]
    }
}


/// Brent-Kung inclusive scan. In-place, modifies data.
/// O(n) work, O(2 log n) depth. Requires power-of-2 sized input.
pub fn brent_kung_inclusive_scan_exec(data: &mut Vec<i64>, n: u64)
    requires
        old(data)@.len() == n as nat,
        n > 0,
        is_power_of_2(n as nat),
        all_partial_sums_bounded(old(data)@),
        n <= i64::MAX as u64,
    ensures
        data@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            data@[i] as int == inclusive_scan_int(old(data)@)[i],
{
    let ghost original_data = old(data)@;
    let ghost original_int = as_int_seq(original_data);
    let levels = log2_ceil_exec(n);
    let data_len = data.len();

    // Handle n = 1: inclusive_scan[0] = data[0]
    if n == 1 {
        proof {
            lemma_sum_single::<int>(|j: int| as_int_seq(original_data)[j], 0);
            assert forall|j: int| 0 <= j < 1 implies
                as_int_seq(original_data)[j] == original_data[j] as int by {}
            lemma_sum_congruence::<int>(
                |j: int| as_int_seq(original_data)[j],
                |j: int| original_data[j] as int,
                0, 1,
            );
        }
        return;
    }

    // n >= 2, so levels >= 1
    proof {
        lemma_pow2_log2_ceil_exact(n as nat);
    }

    let ghost total_levels = levels as nat;

    // ============================================================
    // UP-SWEEP (identical to Blelloch up-sweep)
    // ============================================================
    let mut d: u64 = 0;
    let mut stride: u64 = 1;
    while d < levels
        invariant
            d <= levels,
            stride as nat == pow2(d as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == tree_reduce_state(original_int, n as nat, d as nat)[j],
        decreases levels - d,
    {
        proof {
            lemma_pow2_lt_for_sub_levels(n as nat, d as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_positive(d as nat);
        }

        let ghost prev_state = tree_reduce_state(original_int, n as nat, d as nat);
        let ghost next_state = tree_reduce_state(original_int, n as nat, (d + 1) as nat);
        let step: u64 = 2 * stride;

        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                data@.len() == n as nat,
                stride as nat == pow2(d as nat),
                stride > 0,
                stride < n,
                step == 2 * stride,
                d < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                prev_state == tree_reduce_state(original_int, n as nat, d as nat),
                next_state == tree_reduce_state(original_int, n as nat, (d + 1) as nat),
                forall|j: int| 0 <= j < i as int ==>
                    data@[j] as int == next_state[j],
                forall|j: int| i as int <= j < n as int ==>
                    data@[j] as int == prev_state[j],
            decreases n - i,
        {
            if (i + 1) % step == 0 && i >= stride {
                let partner = (i - stride) as usize;

                proof {
                    let pi = partner as int + 1;
                    assert(pi == i as int + 1 - stride as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 1) as int, step as int);
                    let q = ((i + 1) as int) / (step as int);
                    assert(i as int + 1 == step as int * q);
                    assert(q >= 1) by (nonlinear_arith)
                        requires i as int + 1 == step as int * q, step > 0, i as int + 1 > 0;
                    assert(pi == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires pi == i as int + 1 - stride as int,
                                 i as int + 1 == step as int * q, step == 2 * stride;
                    assert(pi == step as int * (q - 1) + stride as int) by (nonlinear_arith)
                        requires pi == stride as int * (2 * q - 1), step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        pi, step as int, q - 1, stride as int
                    );
                    assert(pi % (step as int) != 0) by (nonlinear_arith)
                        requires pi % (step as int) == stride as int, stride > 0;
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                    assert(next_state[partner as int] == prev_state[partner as int]);

                    lemma_upsweep_overflow_bound(
                        original_data, original_int, n as nat, total_levels,
                        d as nat, i as int,
                    );
                }

                let val = data[i as usize] + data[partner];
                data.set(i as usize, val);
            } else {
                proof {
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                }
            }

            i = i + 1;
        }

        proof {
            assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
        }
        stride = stride * 2;
        d = d + 1;
    }

    // ============================================================
    // DOWN-SWEEP (Brent-Kung specific)
    // ============================================================
    // At this point, data matches tree_reduce_state(original_int, n, total_levels)
    // which is bk_downsweep_state(original_int, n, total_levels, 0).

    proof {
        use crate::proof::scan_brent_kung_lemmas::*;
        lemma_bk_downsweep_base(original_int, n as nat, total_levels);
    }

    if levels <= 1 {
        // n == 2, levels == 1, no down-sweep needed (0 iterations of k < levels - 1)
        // bk_result = bk_downsweep_state at k = 0 = tree_reduce_state
        // For n=2: tree_reduce_state[0] = data[0], tree_reduce_state[1] = data[0]+data[1]
        // inclusive_scan[0] = data[0], inclusive_scan[1] = data[0]+data[1] ✓
        proof {
            use crate::proof::scan_brent_kung_lemmas::*;
            lemma_bk_correct(original_int, n as nat, total_levels);
            let result = crate::scan_brent_kung::bk_result(original_int, n as nat, total_levels);
            assert forall|j: int| 0 <= j < n as int
            implies data@[j] as int == inclusive_scan_int(original_data)[j]
            by {
                assert(data@[j] as int == tree_reduce_state(original_int, n as nat, total_levels)[j]);
                assert forall|k: int| 0 <= k < n as int implies
                    as_int_seq(original_data)[k] == original_data[k] as int by {}
                lemma_sum_congruence::<int>(
                    |k: int| as_int_seq(original_data)[k],
                    |k: int| original_data[k] as int,
                    0, j + 1,
                );
            }
        }
        return;
    }

    // levels >= 2, run down-sweep levels 0..levels-2
    let mut dk: u64 = 0;
    let mut ds_stride: u64 = n / 4;  // pow2(total_levels - 2)
    proof {
        crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - 2) as nat);
        assert(pow2(total_levels) == 2 * pow2((total_levels - 1) as nat));
        assert(pow2((total_levels - 1) as nat) == 2 * pow2((total_levels - 2) as nat));
        assert(pow2(total_levels) == 4 * pow2((total_levels - 2) as nat)) by (nonlinear_arith)
            requires pow2(total_levels) == 2 * pow2((total_levels - 1) as nat),
                     pow2((total_levels - 1) as nat) == 2 * pow2((total_levels - 2) as nat);
        assert(ds_stride as nat == pow2((total_levels - 2) as nat)) by (nonlinear_arith)
            requires
                pow2(total_levels) == n as nat,
                pow2(total_levels) == 4 * pow2((total_levels - 2) as nat),
                ds_stride == n / 4,
                n > 1;
    }

    while dk < levels - 1
        invariant
            dk <= levels - 1,
            dk < levels - 1 ==> ds_stride as nat == pow2((total_levels - dk - 2) as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            total_levels > 1,
            crate::scan_brent_kung::bk_downsweep_invariant(original_int, n as nat, total_levels, dk as nat),
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == crate::scan_brent_kung::bk_downsweep_state(
                    original_int, n as nat, total_levels, dk as nat)[j],
        decreases levels - 1 - dk,
    {
        let ghost prev_bk = crate::scan_brent_kung::bk_downsweep_state(
            original_int, n as nat, total_levels, dk as nat);
        let ghost next_bk = crate::scan_brent_kung::bk_downsweep_state(
            original_int, n as nat, total_levels, (dk + 1) as nat);
        let stride = ds_stride;

        proof {
            crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 2) as nat);
            assert(pow2((total_levels - dk - 1) as nat) == 2 * pow2((total_levels - dk - 2) as nat));
            crate::proof::swizzle_lemmas::lemma_pow2_monotone(
                (total_levels - dk - 1) as nat, total_levels);
            assert(2 * stride as nat <= n as nat);
        }

        let step: u64 = 2 * stride;

        let mut i: u64 = 0;

        proof {
            assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
            implies bk_inner_inv(data@, j, 0, stride as int, step as int, prev_bk, next_bk)
            by {
                assert(!bk_pair_processed(j, 0, stride as int, step as int));
                assert(data@[j] as int == prev_bk[j]);
            }
        }

        while i < n
            invariant
                i <= n,
                data@.len() == n as nat,
                stride as nat == pow2((total_levels - dk - 2) as nat),
                stride > 0,
                step == 2 * stride,
                dk < levels - 1,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                total_levels > 1,
                prev_bk == crate::scan_brent_kung::bk_downsweep_state(
                    original_int, n as nat, total_levels, dk as nat),
                next_bk == crate::scan_brent_kung::bk_downsweep_state(
                    original_int, n as nat, total_levels, (dk + 1) as nat),
                crate::scan_brent_kung::bk_downsweep_invariant(
                    original_int, n as nat, total_levels, dk as nat),
                // Processed positions match next state, others match prev
                forall|j: int| #![trigger data@[j]] 0 <= j < n as int ==>
                    bk_inner_inv(data@, j, i as int, stride as int, step as int, prev_bk, next_bk),
            decreases n - i,
        {
            if (i + 1) % step == stride && i >= stride {
                // Active position: data[i] += data[i - stride]
                let partner = (i - stride) as usize;

                proof {
                    // data[i] == prev_bk[i] (not yet processed)
                    assert(!bk_pair_processed(i as int, i as int, stride as int, step as int));
                    assert(data@[i as int] as int == prev_bk[i as int]);
                    // data[partner] == ? We need prev_bk[partner]
                    // partner < i, so it may have been processed.
                    // If processed: data[partner] == next_bk[partner]
                    // If not: data[partner] == prev_bk[partner]
                    // But next_bk[partner] == prev_bk[partner] because partner is not active
                    // at this level (only positions with (j+1)%step == stride are active).
                    // Is partner active?
                    // partner + 1 = i + 1 - stride. i+1 = step*q + stride (from activity condition).
                    // partner + 1 = step*q. (partner+1) % step == 0 != stride. So partner is NOT active.
                    // So next_bk[partner] == prev_bk[partner].
                    // Therefore data[partner] == prev_bk[partner] regardless of processing status.
                    let pi = partner as int;
                    assert(pi + 1 == i as int + 1 - stride as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 1) as int, step as int);
                    let q = ((i + 1) as int) / (step as int);
                    assert(i as int + 1 == step as int * q + stride as int);
                    assert(pi + 1 == step as int * q) by (nonlinear_arith)
                        requires pi + 1 == i as int + 1 - stride as int,
                                 i as int + 1 == step as int * q + stride as int;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        pi + 1, step as int, q, 0
                    );
                    assert((pi + 1) % (step as int) == 0);
                    assert((pi + 1) % (step as int) != stride as int) by (nonlinear_arith)
                        requires (pi + 1) % (step as int) == 0, stride > 0;
                    assert(!bk_active(pi, stride as int, step as int));
                    assert(next_bk[pi] == prev_bk[pi]);

                    // If partner was processed: data == next_bk == prev_bk ✓
                    // If not: data == prev_bk ✓

                    // Overflow: next_bk[i] is a prefix sum of original data (bounded)
                    // next_bk[i] = prev_bk[i] + prev_bk[partner] by BK definition
                    // By BK invariant at dk+1: next_bk[i] = bk_expected(data, n, total_levels, dk+1, i)
                    // bk_expected = sum(original_int, 0, i+1) = partial_sum(original_data, 0, i+1)
                    crate::proof::scan_brent_kung_lemmas::lemma_bk_downsweep_step(
                        original_int, n as nat, total_levels, dk as nat);
                    let next_val = next_bk[i as int];
                    // next_bk[i] = sum(original_int, 0, i+1) since (i+1)%stride==0
                    assert((i as int + 1) % (stride as int) == 0) by {
                        assert(i as int + 1 == step as int * q + stride as int);
                        assert(i as int + 1 == stride as int * (2 * q + 1)) by (nonlinear_arith)
                            requires i as int + 1 == step as int * q + stride as int, step == 2 * stride;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                            i as int + 1, stride as int, 2 * q + 1, 0
                        );
                    };
                    // Bridge to partial_sum for overflow
                    let hi = i as int + 1;
                    assert forall|k: int| 0 <= k < hi implies
                        original_int[k] == original_data[k] as int by {}
                    lemma_sum_congruence::<int>(
                        |k: int| original_int[k],
                        |k: int| original_data[k] as int,
                        0, hi,
                    );
                    assert(partial_sum(original_data, 0, hi) == next_val);
                }

                let val = data[i as usize] + data[partner];
                data.set(i as usize, val);
            }

            proof {
                // Re-establish invariant for all j
                assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                implies bk_inner_inv(data@, j, (i + 1) as int, stride as int, step as int, prev_bk, next_bk)
                by {
                    if j == i as int {
                        if bk_active(j, stride as int, step as int) {
                            // Just processed: data == next_bk
                            assert(bk_pair_processed(j, (i + 1) as int, stride as int, step as int));
                        } else {
                            // Not active, unchanged
                            assert(!bk_pair_processed(j, (i + 1) as int, stride as int, step as int));
                        }
                    } else {
                        // j < i: bk_pair_processed(j, i+1) == bk_pair_processed(j, i)
                        // since only j == i could become newly processed
                        if bk_active(i as int, stride as int, step as int) && j < i as int {
                            // j was either already processed or not
                            // bk_pair_processed(j, i+1) iff bk_active(j) && j < i+1
                            // bk_pair_processed(j, i)   iff bk_active(j) && j < i
                            // j < i < i+1, so both are the same for j < i
                        }
                        // j > i: unchanged, not processed at either i or i+1
                    }
                }
            }

            i = i + 1;
        }

        // After inner loop: all active positions processed, data matches next_bk
        proof {
            assert forall|j: int| 0 <= j < n as int
            implies data@[j] as int == next_bk[j]
            by {
                if bk_active(j, stride as int, step as int) {
                    assert(bk_pair_processed(j, n as int, stride as int, step as int));
                } else {
                    assert(!bk_pair_processed(j, n as int, stride as int, step as int));
                    assert(next_bk[j] == prev_bk[j]);
                }
            }

            crate::proof::scan_brent_kung_lemmas::lemma_bk_downsweep_step(
                original_int, n as nat, total_levels, dk as nat);
        }

        dk = dk + 1;
        if dk < levels - 1 {
            proof {
                assert(pow2((total_levels - dk - 2) as nat) == ds_stride as nat / 2) by {
                    assert(pow2((total_levels - (dk - 1) - 2) as nat) == ds_stride as nat);
                    assert((total_levels - (dk - 1) - 2) as nat == (total_levels - dk - 1) as nat);
                    assert(pow2((total_levels - dk - 1) as nat) == 2 * pow2((total_levels - dk - 2) as nat));
                    crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 2) as nat);
                };
            }
            ds_stride = ds_stride / 2;
        }
    }

    // ============================================================
    // FINAL: bk_result == inclusive_scan_int
    // ============================================================
    proof {
        use crate::proof::scan_brent_kung_lemmas::lemma_bk_correct;
        lemma_bk_correct(original_int, n as nat, total_levels);
        let result = crate::scan_brent_kung::bk_result(original_int, n as nat, total_levels);

        assert forall|j: int| 0 <= j < n as int
        implies data@[j] as int == inclusive_scan_int(original_data)[j]
        by {
            assert(data@[j] as int == crate::scan_brent_kung::bk_downsweep_state(
                original_int, n as nat, total_levels, (total_levels - 1) as nat)[j]);
            assert(result[j] == inclusive_scan::<int>(original_int)[j]);
            // Bridge inclusive_scan(original_int) to inclusive_scan_int(original_data)
            assert forall|k: int| 0 <= k < n as int implies
                as_int_seq(original_data)[k] == original_data[k] as int by {}
            lemma_sum_congruence::<int>(
                |k: int| as_int_seq(original_data)[k],
                |k: int| original_data[k] as int,
                0, j + 1,
            );
        }
    }
}

} // verus!
