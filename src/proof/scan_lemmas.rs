///  Ground-truth lemmas for scan/reduce primitives.
///
///  These establish relationships between the specs in `scan.rs`:
///  inclusive ↔ exclusive conversion, reduce = last of inclusive,
///  scan decomposition for block algorithms, compact index monotonicity,
///  and log2_ceil / pow2 bounds.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::swizzle::pow2;

verus! {

//  ============================================================
//  Inclusive ↔ Exclusive relationships
//  ============================================================

///  inclusive[i] ≡ exclusive[i] + data[i].
pub proof fn lemma_inclusive_exclusive_relation<R: Ring>(data: Seq<R>, i: int)
    requires 0 <= i < data.len(),
    ensures inclusive_scan::<R>(data)[i].eqv(
        exclusive_scan::<R>(data)[i].add(data[i])
    ),
{
    lemma_sum_peel_last::<R>(|j: int| data[j], 0, i + 1);
}

///  exclusive[0] = zero; exclusive[i] = inclusive[i-1] for i > 0.
///  Both equalities are definitional (same sum expression after unfolding).
pub proof fn lemma_exclusive_from_inclusive<R: Ring>(data: Seq<R>, i: int)
    requires 0 <= i < data.len(),
    ensures
        i == 0 ==> exclusive_scan::<R>(data)[0] == R::zero(),
        i > 0 ==> exclusive_scan::<R>(data)[i] == inclusive_scan::<R>(data)[i - 1],
{
}

///  reduce(data, 0, n) = inclusive_scan(data)[n-1] (definitionally equal).
pub proof fn lemma_reduce_equals_last_inclusive<R: Ring>(data: Seq<R>, n: nat)
    requires n > 0, n <= data.len(),
    ensures reduce::<R>(data, 0, n as int) == inclusive_scan::<R>(data)[(n - 1) as int],
{
}

//  ============================================================
//  Scan decomposition (for block-based algorithms)
//  ============================================================

///  inclusive_scan(data)[block_start + j] ≡ reduce(data, 0, block_start) + reduce(data, block_start, block_start + j + 1).
///  Splits a global prefix sum into a block-prefix reduce plus a local reduce.
pub proof fn lemma_scan_decomposition<R: Ring>(data: Seq<R>, block_start: int, j: int)
    requires
        0 <= block_start,
        0 <= j,
        block_start + j + 1 <= data.len(),
    ensures
        inclusive_scan::<R>(data)[(block_start + j) as int].eqv(
            reduce::<R>(data, 0, block_start).add(
                reduce::<R>(data, block_start, block_start + j + 1)
            )
        ),
{
    lemma_sum_split::<R>(|i: int| data[i], 0, block_start, block_start + j + 1);
}

//  ============================================================
//  Compact lemmas
//  ============================================================

///  compact_indices advances by 1 when pred[i] is true, stays when false.
pub proof fn lemma_compact_indices_step(pred: Seq<bool>, i: int)
    requires 0 <= i, i + 1 < pred.len() as int,
    ensures compact_indices(pred)[(i + 1) as int] ==
        compact_indices(pred)[i] + if pred[i] { 1nat } else { 0nat },
{
    assert(pred.take(i + 1).drop_last() =~= pred.take(i));
}

///  When pred[i] is true, compact_indices strictly increases.
pub proof fn lemma_compact_indices_monotone(pred: Seq<bool>, i: int)
    requires
        0 <= i,
        i + 1 < pred.len() as int,
        pred[i],
    ensures compact_indices(pred)[(i + 1) as int] > compact_indices(pred)[i],
{
    lemma_compact_indices_step(pred, i);
}

///  compact_result length equals compact_size.
pub proof fn lemma_compact_result_len<T>(data: Seq<T>, pred: Seq<bool>)
    requires data.len() == pred.len(),
    ensures compact_result(data, pred).len() == compact_size(pred),
    decreases data.len(),
{
    if data.len() > 0 {
        lemma_compact_result_len::<T>(data.drop_last(), pred.drop_last());
    }
}

///  compact_size is bounded by the predicate length.
pub proof fn lemma_compact_size_le_len(pred: Seq<bool>)
    ensures compact_size(pred) <= pred.len(),
    decreases pred.len(),
{
    if pred.len() > 0 {
        lemma_compact_size_le_len(pred.drop_last());
    }
}

///  Step lemma: compact_size(pred.take(i+1)) = compact_size(pred.take(i)) + (1 if pred[i] else 0).
pub proof fn lemma_compact_size_step(pred: Seq<bool>, i: int)
    requires
        0 <= i,
        i < pred.len() as int,
    ensures
        compact_size(pred.take(i + 1))
            == compact_size(pred.take(i))
                + (if pred[i] { 1nat } else { 0nat }),
{
    assert(pred.take(i + 1).drop_last() =~= pred.take(i));
    assert(pred.take(i + 1).last() == pred[i]);
}

///  compact_indices[i] <= i for any predicate.
pub proof fn lemma_compact_indices_le_i(pred: Seq<bool>, i: int)
    requires 0 <= i, i < pred.len() as int,
    ensures compact_indices(pred)[i] <= i as nat,
    decreases i,
{
    if i == 0 {
        assert(pred.take(0).len() == 0);
    } else {
        lemma_compact_indices_le_i(pred, i - 1);
        lemma_compact_indices_step(pred, i - 1);
    }
}

///  compact_size is monotone in take length.
pub proof fn lemma_compact_size_monotone(pred: Seq<bool>, i: int, j: int)
    requires 0 <= i <= j, j <= pred.len() as int,
    ensures compact_size(pred.take(i)) <= compact_size(pred.take(j)),
    decreases j - i,
{
    if i == j {
        assert(pred.take(i) =~= pred.take(j));
    } else {
        lemma_compact_size_monotone(pred, i, j - 1);
        assert(pred.take(j).drop_last() =~= pred.take(j - 1));
    }
}

///  When pred[i] is true, compact_indices(pred)[i] < compact_size(pred).
pub proof fn lemma_compact_size_take_lt(pred: Seq<bool>, i: int)
    requires 0 <= i, i < pred.len() as int, pred[i],
    ensures compact_indices(pred)[i] < compact_size(pred),
{
    assert(pred.take(i + 1).drop_last() =~= pred.take(i));
    assert(pred.take(i + 1).last() == pred[i]);
    lemma_compact_size_monotone(pred, (i + 1) as int, pred.len() as int);
    assert(pred.take(pred.len() as int) =~= pred);
}

///  compact_indices is nondecreasing.
pub proof fn lemma_compact_indices_nondecreasing(pred: Seq<bool>, i: int, j: int)
    requires
        0 <= i <= j,
        j < pred.len() as int,
    ensures
        compact_indices(pred)[i] <= compact_indices(pred)[j],
    decreases j - i,
{
    if i == j {
    } else {
        lemma_compact_indices_nondecreasing(pred, i, j - 1);
        lemma_compact_indices_step(pred, j - 1);
    }
}

///  When pred[i] and pred[j] with i < j, compact_indices[i] < compact_indices[j].
pub proof fn lemma_compact_scatter_disjoint(pred: Seq<bool>, i: int, j: int)
    requires
        0 <= i < j,
        j < pred.len() as int,
        pred[i],
        pred[j],
    ensures
        compact_indices(pred)[i] < compact_indices(pred)[j],
{
    lemma_compact_indices_monotone(pred, i);
    if i + 1 < j {
        lemma_compact_indices_nondecreasing(pred, (i + 1) as int, j);
    }
}

///  compact_result(data, pred)[compact_indices(pred)[i]] == data[i] when pred[i].
pub proof fn lemma_compact_result_at<T>(data: Seq<T>, pred: Seq<bool>, i: int)
    requires
        data.len() == pred.len(),
        0 <= i, i < data.len() as int,
        pred[i],
    ensures
        compact_result(data, pred)[compact_indices(pred)[i] as int] == data[i],
    decreases data.len(),
{
    if i == data.len() - 1 {
        lemma_compact_result_len::<T>(data.drop_last(), pred.drop_last());
        assert(pred.take(i) =~= pred.drop_last());
    } else {
        assert(data.drop_last()[i] == data[i]);
        assert(pred.drop_last()[i] == pred[i]);
        lemma_compact_result_at::<T>(data.drop_last(), pred.drop_last(), i);
        assert(pred.drop_last().take(i) =~= pred.take(i));
        let idx = compact_indices(pred)[i];
        let rest = compact_result(data.drop_last(), pred.drop_last());
        if pred.last() {
            lemma_compact_result_len::<T>(data.drop_last(), pred.drop_last());
            lemma_compact_size_take_lt(pred.drop_last(), i);
            assert(idx < rest.len());
        }
    }
}

///  For each i < compact_size(pred), find the unique j with pred[j] and compact_indices(pred)[j] == i.
pub proof fn lemma_compact_indices_surjective<T>(
    data: Seq<T>, pred: Seq<bool>, i: int,
) -> (j: int)
    requires
        data.len() == pred.len(),
        0 <= i,
        i < compact_size(pred) as int,
    ensures
        0 <= j,
        j < pred.len() as int,
        pred[j],
        compact_indices(pred)[j] as int == i,
    decreases pred.len(),
{
    let n = pred.len() as int;
    assert(pred.drop_last() =~= pred.take(n - 1));
    if pred.last() && i == compact_size(pred) as int - 1 {
        assert(compact_indices(pred)[(n - 1) as int]
            == compact_size(pred.take(n - 1)));
        assert(compact_size(pred) == compact_size(pred.drop_last()) + 1nat);
        (n - 1) as int
    } else {
        let cs_drop = compact_size(pred.drop_last());
        if pred.last() {
            assert(compact_size(pred) == cs_drop + 1nat);
        } else {
            assert(compact_size(pred) == cs_drop);
        }
        assert((i as int) < (cs_drop as int));
        let j = lemma_compact_indices_surjective::<T>(
            data.drop_last(), pred.drop_last(), i,
        );
        assert(pred[j] == pred.drop_last()[j]);
        assert(pred.drop_last().take(j) =~= pred.take(j));
        assert(compact_indices(pred.drop_last())[j] == compact_indices(pred)[j]);
        j
    }
}

///  compact_indices[i] == exclusive_scan(pred_as_int_seq(pred))[i].
pub proof fn lemma_compact_indices_is_exclusive_scan(pred: Seq<bool>, i: int)
    requires
        0 <= i < pred.len() as int,
    ensures
        compact_indices(pred)[i] as int == exclusive_scan::<int>(pred_as_int_seq(pred))[i],
    decreases i,
{
    if i == 0 {
        assert(pred.take(0).len() == 0);
        lemma_sum_empty::<int>(|j: int| pred_as_int_seq(pred)[j], 0, 0);
    } else {
        lemma_compact_indices_is_exclusive_scan(pred, i - 1);
        assert(pred.take(i).drop_last() =~= pred.take(i - 1));
        assert(pred.take(i).last() == pred[i - 1]);
        lemma_sum_peel_last::<int>(|j: int| pred_as_int_seq(pred)[j], 0, i);
    }
}

///  compact_size equals sum of pred_as_int_seq.
pub proof fn lemma_compact_size_equals_sum(pred: Seq<bool>)
    ensures compact_size(pred) as int ==
        sum::<int>(|j: int| pred_as_int_seq(pred)[j], 0, pred.len() as int),
    decreases pred.len(),
{
    if pred.len() == 0 {
        lemma_sum_empty::<int>(
            |j: int| pred_as_int_seq(pred)[j], 0, 0,
        );
    } else {
        let n = pred.len();
        lemma_compact_size_equals_sum(pred.drop_last());
        lemma_sum_peel_last::<int>(
            |j: int| pred_as_int_seq(pred)[j], 0, n as int,
        );
        assert forall|j: int| 0 <= j < (n - 1) as int implies
            pred_as_int_seq(pred)[j] == pred_as_int_seq(pred.drop_last())[j]
        by {
            assert(pred[j] == pred.drop_last()[j]);
        }
        lemma_sum_congruence::<int>(
            |j: int| pred_as_int_seq(pred)[j],
            |j: int| pred_as_int_seq(pred.drop_last())[j],
            0, (n - 1) as int,
        );
    }
}

///  Partial sum of pred_as_int_seq (trigger-friendly wrapper).
pub open spec fn pred_partial_sum(pred: Seq<bool>, lo: int, hi: int) -> int {
    sum::<int>(|j: int| pred_as_int_seq(pred)[j], lo, hi)
}

///  pred_as_int_seq partial sums are bounded by n <= i64::MAX.
pub proof fn lemma_pred_partial_sums_bounded(pred: Seq<bool>)
    requires pred.len() <= i64::MAX as nat,
    ensures
        forall|lo: int, hi: int| 0 <= lo <= hi <= pred.len() ==>
            0 <= #[trigger] pred_partial_sum(pred, lo, hi)
            && pred_partial_sum(pred, lo, hi) <= pred.len() as int,
{
    assert forall|lo: int, hi: int| 0 <= lo <= hi <= pred.len()
    implies 0 <= #[trigger] pred_partial_sum(pred, lo, hi)
        && pred_partial_sum(pred, lo, hi) <= (hi - lo) as int
    by {
        lemma_pred_partial_sum_bounded_helper(pred, lo, hi);
    }
}

proof fn lemma_pred_partial_sum_bounded_helper(pred: Seq<bool>, lo: int, hi: int)
    requires 0 <= lo <= hi, hi <= pred.len(),
    ensures
        0 <= sum::<int>(|j: int| pred_as_int_seq(pred)[j], lo, hi),
        sum::<int>(|j: int| pred_as_int_seq(pred)[j], lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if lo >= hi {
        lemma_sum_empty::<int>(|j: int| pred_as_int_seq(pred)[j], lo, hi);
    } else {
        lemma_pred_partial_sum_bounded_helper(pred, lo, hi - 1);
        lemma_sum_peel_last::<int>(|j: int| pred_as_int_seq(pred)[j], lo, hi);
    }
}

//  ============================================================
//  log2_ceil / pow2 bounds
//  ============================================================

///  Helper: (n + 1) / 2 properties for n > 1.
pub proof fn lemma_half_ceil_bounds(n: nat)
    requires n > 1,
    ensures
        (n + 1) / 2 >= 1,
        (n + 1) / 2 < n,
        2 * ((n + 1) / 2) >= n,
{
}

///  pow2(log2_ceil(n)) >= n for all n > 0.
pub proof fn lemma_log2_ceil_pow2(n: nat)
    requires n > 0,
    ensures pow2(log2_ceil(n)) >= n,
    decreases n,
{
    if n <= 1 {
    } else {
        lemma_half_ceil_bounds(n);
        let m = ((n + 1) / 2) as nat;
        lemma_log2_ceil_pow2(m);
        let k = log2_ceil(m);
        //  log2_ceil(n) == 1 + k by definition unfolding
        assert(log2_ceil(n) == k + 1);
        //  pow2(k + 1) = 2 * pow2(k) by pow2 definition unfolding
        assert(pow2((k + 1) as nat) == 2 * pow2(k));
        //  Chain: pow2(log2_ceil(n)) = 2 * pow2(k) >= 2 * m >= n
    }
}

///  log2_ceil(1) = 0.
pub proof fn lemma_log2_ceil_one()
    ensures log2_ceil(1) == 0,
{
}

///  log2_ceil(n) < n for n >= 2 (used to bound recursion in exec).
pub proof fn lemma_log2_ceil_lt(n: nat)
    requires n >= 2,
    ensures log2_ceil(n) < n,
    decreases n,
{
    let half = ((n + 1) / 2) as nat;
    lemma_half_ceil_bounds(n);
    if half >= 2 {
        lemma_log2_ceil_lt(half);
        assert(log2_ceil(half) < half);
        assert(log2_ceil(n) == 1 + log2_ceil(half));
        assert(half < n);
        //  1 + log2_ceil(half) <= half < n
    } else {
        //  half == 1 (since half >= 1 from lemma_half_ceil_bounds)
        //  log2_ceil(n) = 1 + log2_ceil(1) = 1 + 0 = 1 < n (since n >= 2)
    }
}

///  pow2(d) < n when d < log2_ceil(n) and n > 1.
///  Used to prove stride doesn't overflow in exec loops.
pub proof fn lemma_pow2_lt_for_sub_levels(n: nat, d: nat)
    requires n > 1, d < log2_ceil(n),
    ensures pow2(d) < n,
    decreases n,
{
    let half = ((n + 1) / 2) as nat;
    lemma_half_ceil_bounds(n);
    //  log2_ceil(n) = 1 + log2_ceil(half)
    if d == 0 {
        //  pow2(0) = 1 < n since n > 1
    } else {
        //  d >= 1, d < 1 + log2_ceil(half), so d - 1 < log2_ceil(half)
        if half > 1 {
            lemma_pow2_lt_for_sub_levels(half, (d - 1) as nat);
            //  pow2(d-1) < half, pow2(d) = 2 * pow2(d-1)
            assert(pow2(d) == 2 * pow2((d - 1) as nat));
            //  2 * pow2(d-1) <= 2 * (half - 1) = 2*half - 2 <= n + 1 - 2 = n - 1 < n
        } else {
            //  half == 1, log2_ceil(1) = 0
            //  log2_ceil(n) = 1 + 0 = 1, d < 1 and d >= 1: contradiction
            assert(half == 1);
            lemma_log2_ceil_one();
        }
    }
}

///  If pow2(k) >= n then log2_ceil(n) <= k.
pub proof fn lemma_log2_ceil_upper_bound(n: nat, k: nat)
    requires n > 0, pow2(k) >= n,
    ensures log2_ceil(n) <= k,
    decreases n,
{
    if n <= 1 {
    } else {
        lemma_half_ceil_bounds(n);
        let half = ((n + 1) / 2) as nat;
        //  k >= 1 since pow2(0) = 1 < 2 <= n but pow2(k) >= n
        if k == 0 {
            assert(pow2(0) == 1);
            assert(false); //  contradiction
        }
        //  pow2(k) = 2 * pow2(k-1) >= n, and half = ceil(n/2)
        //  2x >= n iff x >= ceil(n/2), so pow2(k-1) >= half
        assert(pow2(k) == 2 * pow2((k - 1) as nat));
        assert(pow2((k - 1) as nat) >= half) by(nonlinear_arith)
            requires
                2 * pow2((k - 1) as nat) >= n,
                half == ((n + 1) / 2) as nat,
                n >= 2;
        lemma_log2_ceil_upper_bound(half, (k - 1) as nat);
    }
}

///  pow2(log2_ceil(n)) == n when n is a power of 2.
pub proof fn lemma_pow2_log2_ceil_exact(n: nat)
    requires n > 0, is_power_of_2(n),
    ensures pow2(log2_ceil(n)) == n,
{
    let k = choose|k: nat| pow2(k) == n;
    lemma_log2_ceil_upper_bound(n, k);
    lemma_log2_ceil_pow2(n);
    let a = log2_ceil(n);
    if a < k {
        crate::proof::swizzle_lemmas::lemma_pow2_monotone((a + 1) as nat, k);
        crate::proof::swizzle_lemmas::lemma_pow2_positive(a);
        assert(pow2((a + 1) as nat) == 2 * pow2(a));
        assert(false) by (nonlinear_arith)
            requires
                pow2((a + 1) as nat) as int <= pow2(k) as int,
                pow2(a) as int >= n as int,
                pow2((a + 1) as nat) as int == 2 * pow2(a) as int,
                pow2(k) == n,
                n > 0nat;
    }
}

//  ============================================================
//  Bucket offset / multi-split lemmas
//  ============================================================

///  bucket_pred(data, k).drop_last() == bucket_pred(data.drop_last(), k).
pub proof fn lemma_bucket_pred_drop_last(data: Seq<nat>, k: nat)
    requires data.len() > 0,
    ensures bucket_pred(data, k).drop_last() =~= bucket_pred(data.drop_last(), k),
{
    let pred_full = bucket_pred(data, k);
    let pred_short = bucket_pred(data.drop_last(), k);
    assert(pred_full.drop_last().len() == pred_short.len());
    assert forall|i: int| 0 <= i < pred_short.len() as int implies
        pred_full.drop_last()[i] == #[trigger] pred_short[i]
    by {
        assert(pred_full[i] == (data[i] == k));
        assert(pred_short[i] == (data.drop_last()[i] == k));
        assert(data.drop_last()[i] == data[i]);
    }
}

///  bucket_count decomposes on drop_last: adds 1 if last element matches.
pub proof fn lemma_bucket_count_drop_last(data: Seq<nat>, k: nat)
    requires data.len() > 0,
    ensures bucket_count(data, k) ==
        bucket_count(data.drop_last(), k) + if data.last() == k { 1nat } else { 0nat },
{
    lemma_bucket_pred_drop_last(data, k);
    let pred = bucket_pred(data, k);
    //  compact_size(pred) = compact_size(pred.drop_last()) + if pred.last() { 1 } else { 0 }
    //  This is the definition of compact_size when pred.len() > 0.
    assert(pred.last() == (data.last() == k));
}

///  bucket_offset decomposes on drop_last: adds 1 if last element is in [0, b).
pub proof fn lemma_bucket_offset_drop_last(data: Seq<nat>, b: nat)
    requires data.len() > 0,
    ensures bucket_offset(data, b) ==
        bucket_offset(data.drop_last(), b) + if data.last() < b { 1nat } else { 0nat },
    decreases b,
{
    if b == 0 {
        //  Both sides are 0
    } else {
        lemma_bucket_offset_drop_last(data, (b - 1) as nat);
        lemma_bucket_count_drop_last(data, (b - 1) as nat);
        //  bucket_offset(data, b) = bucket_offset(data, b-1) + bucket_count(data, b-1)
        //  = [bucket_offset(dl, b-1) + if last < b-1 { 1 } else { 0 }]
        //    + [bucket_count(dl, b-1) + if last == b-1 { 1 } else { 0 }]
        //  = bucket_offset(dl, b) + (if last < b-1 { 1 } else { 0 }) + (if last == b-1 { 1 } else { 0 })
        //  = bucket_offset(dl, b) + if last < b { 1 } else { 0 }
        //  Because for nats: x < b iff x < b-1 or x == b-1
        let x = data.last();
        assert((if x < (b - 1) as nat { 1nat } else { 0nat })
             + (if x == (b - 1) as nat { 1nat } else { 0nat })
            == (if x < b { 1nat } else { 0nat }));
    }
}

///  bucket_offset(data, b) <= data.len() for all b.
pub proof fn lemma_bucket_offset_bounded(data: Seq<nat>, b: nat)
    ensures bucket_offset(data, b) <= data.len(),
    decreases data.len(),
{
    if data.len() == 0 {
        //  All bucket_preds have length 0, so all compact_sizes are 0
        //  bucket_offset is 0 by induction on b
        lemma_bucket_offset_empty_data(data, b);
    } else {
        lemma_bucket_offset_bounded(data.drop_last(), b);
        lemma_bucket_offset_drop_last(data, b);
        //  bucket_offset(data, b) = bucket_offset(dl, b) + (0 or 1) <= dl.len() + 1 = data.len()
    }
}

///  When data is empty, bucket_offset is 0 for all b.
proof fn lemma_bucket_offset_empty_data(data: Seq<nat>, b: nat)
    requires data.len() == 0,
    ensures bucket_offset(data, b) == 0,
    decreases b,
{
    if b == 0 {
    } else {
        lemma_bucket_offset_empty_data(data, (b - 1) as nat);
        //  bucket_count(data, b-1) = compact_size(bucket_pred(data, b-1))
        //  bucket_pred(data, b-1) has length 0, so compact_size = 0
        let pred = bucket_pred(data, (b - 1) as nat);
        assert(pred.len() == 0);
    }
}

///  bucket_offset is monotone: a <= b implies bucket_offset(data, a) <= bucket_offset(data, b).
pub proof fn lemma_bucket_offset_monotone(data: Seq<nat>, a: nat, b: nat)
    requires a <= b,
    ensures bucket_offset(data, a) <= bucket_offset(data, b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_bucket_offset_monotone(data, a, (b - 1) as nat);
        //  bucket_offset(data, b) = bucket_offset(data, b-1) + bucket_count(data, b-1) >= bucket_offset(data, b-1)
    }
}

///  When all elements have bucket < num_buckets, total offset == data.len().
///  Proof: each element contributes exactly 1 to some bucket_count(b) where b == data[i],
///  so sum of all bucket_counts = data.len().
pub proof fn lemma_bucket_offset_total(data: Seq<nat>, num_buckets: nat)
    requires
        forall|i: int| 0 <= i < data.len() as int ==> (data[i] as nat) < num_buckets,
    ensures
        bucket_offset(data, num_buckets) == data.len(),
    decreases data.len(),
{
    if data.len() == 0 {
        lemma_bucket_offset_empty_data(data, num_buckets);
    } else {
        let dl = data.drop_last();
        let last = data.last();
        //  Induction: dl has all elements < num_buckets
        assert forall|i: int| 0 <= i < dl.len() as int implies (dl[i] as nat) < num_buckets
        by {
            assert(dl[i] == data[i]);
        }
        lemma_bucket_offset_total(dl, num_buckets);
        //  bucket_offset(dl, num_buckets) == dl.len() == data.len() - 1
        lemma_bucket_offset_drop_last(data, num_buckets);
        //  bucket_offset(data, nb) == bucket_offset(dl, nb) + if last < nb { 1 } else { 0 }
        //  last < num_buckets (from precondition, last == data[data.len()-1])
        assert(last < num_buckets);
    }
}

///  bucket_for_index returns a valid bucket b < num_buckets, with
///  bucket_offset(buckets, b) <= i < bucket_offset(buckets, b) + bucket_count(buckets, b).
pub proof fn lemma_bucket_for_index_valid(buckets: Seq<nat>, num_buckets: nat, i: nat)
    requires
        i < bucket_offset(buckets, num_buckets),
    ensures ({
        let b = bucket_for_index(buckets, num_buckets, i);
        &&& b < num_buckets
        &&& bucket_offset(buckets, b) <= i
        &&& i < bucket_offset(buckets, b) + bucket_count(buckets, b)
    }),
    decreases num_buckets,
{
    let b = bucket_for_index(buckets, num_buckets, i);
    if num_buckets == 0 {
        //  bucket_offset(buckets, 0) == 0, so i < 0 — contradicts nat
    } else if bucket_offset(buckets, (num_buckets - 1) as nat) <= i {
        //  b == num_buckets - 1
        //  bucket_offset(buckets, num_buckets) = bucket_offset(nb-1) + bucket_count(nb-1)
        //  i < bucket_offset(nb) = bucket_offset(nb-1) + bucket_count(nb-1)
    } else {
        //  b = bucket_for_index(buckets, num_buckets - 1, i)
        //  Need: i < bucket_offset(buckets, num_buckets - 1)
        lemma_bucket_for_index_valid(buckets, (num_buckets - 1) as nat, i);
    }
}

///  When per-bucket elements match compact_result, the full output equals multi_split_result.
pub proof fn lemma_multi_split_matches<T>(
    data: Seq<T>, buckets: Seq<nat>, num_buckets: nat, output: Seq<T>,
)
    requires
        data.len() == buckets.len(),
        output.len() == data.len(),
        bucket_offset(buckets, num_buckets) == data.len(),
        forall|i: int| 0 <= i < data.len() as int ==> (buckets[i] as nat) < num_buckets,
        forall|b: int, j: int| 0 <= b < num_buckets as int
            && 0 <= j < bucket_count(buckets, b as nat) as int ==>
                output[bucket_offset(buckets, b as nat) as int + j]
                    == #[trigger] compact_result(data, bucket_pred(buckets, b as nat))[j],
    ensures
        output =~= multi_split_result(data, buckets, num_buckets),
{
    let result = multi_split_result(data, buckets, num_buckets);
    assert(output.len() == result.len());
    assert forall|i: int| 0 <= i < output.len() as int implies output[i] == result[i]
    by {
        let b = bucket_for_index(buckets, num_buckets, i as nat);
        lemma_bucket_for_index_valid(buckets, num_buckets, i as nat);
        let j = i - bucket_offset(buckets, b) as int;
        let b_int: int = b as int;
        assert(0 <= j);
        assert(j < bucket_count(buckets, b) as int);
        assert(bucket_offset(buckets, b) as int + j == i);
        assert(0 <= b_int < num_buckets as int);
        assert(0 <= j < bucket_count(buckets, b_int as nat) as int);
        //  Trigger the per-bucket quantifier with b_int and j
        assert(output[bucket_offset(buckets, b_int as nat) as int + j]
            == compact_result(data, bucket_pred(buckets, b_int as nat))[j]);
    }
}

} //  verus!
