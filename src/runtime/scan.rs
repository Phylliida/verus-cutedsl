/// Runtime implementations of scan/reduce primitives.
///
/// Hillis-Steele inclusive scan: O(n log n) work, O(log n) depth.
/// Tree reduce: derived from Hillis-Steele (take last element).
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;

verus! {

/// Partial sum of i64 data interpreted as int.
pub open spec fn partial_sum(data: Seq<i64>, lo: int, hi: int) -> int {
    sum::<int>(|j: int| data[j] as int, lo, hi)
}

/// All partial sums of data fit in i64.
pub open spec fn all_partial_sums_bounded(data: Seq<i64>) -> bool {
    forall|lo: int, hi: int| 0 <= lo <= hi <= data.len() ==>
        i64::MIN as int <= #[trigger] partial_sum(data, lo, hi)
        && partial_sum(data, lo, hi) <= i64::MAX as int
}

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

} // verus!
