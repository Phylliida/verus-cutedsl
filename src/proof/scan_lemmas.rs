/// Ground-truth lemmas for scan/reduce primitives.
///
/// These establish relationships between the specs in `scan.rs`:
/// inclusive ↔ exclusive conversion, reduce = last of inclusive,
/// scan decomposition for block algorithms, compact index monotonicity,
/// and log2_ceil / pow2 bounds.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::swizzle::pow2;

verus! {

// ============================================================
// Inclusive ↔ Exclusive relationships
// ============================================================

/// inclusive[i] ≡ exclusive[i] + data[i].
pub proof fn lemma_inclusive_exclusive_relation<R: Ring>(data: Seq<R>, i: int)
    requires 0 <= i < data.len(),
    ensures inclusive_scan::<R>(data)[i].eqv(
        exclusive_scan::<R>(data)[i].add(data[i])
    ),
{
    lemma_sum_peel_last::<R>(|j: int| data[j], 0, i + 1);
}

/// exclusive[0] = zero; exclusive[i] = inclusive[i-1] for i > 0.
/// Both equalities are definitional (same sum expression after unfolding).
pub proof fn lemma_exclusive_from_inclusive<R: Ring>(data: Seq<R>, i: int)
    requires 0 <= i < data.len(),
    ensures
        i == 0 ==> exclusive_scan::<R>(data)[0] == R::zero(),
        i > 0 ==> exclusive_scan::<R>(data)[i] == inclusive_scan::<R>(data)[i - 1],
{
}

/// reduce(data, 0, n) = inclusive_scan(data)[n-1] (definitionally equal).
pub proof fn lemma_reduce_equals_last_inclusive<R: Ring>(data: Seq<R>, n: nat)
    requires n > 0, n <= data.len(),
    ensures reduce::<R>(data, 0, n as int) == inclusive_scan::<R>(data)[(n - 1) as int],
{
}

// ============================================================
// Scan decomposition (for block-based algorithms)
// ============================================================

/// inclusive_scan(data)[block_start + j] ≡ reduce(data, 0, block_start) + reduce(data, block_start, block_start + j + 1).
/// Splits a global prefix sum into a block-prefix reduce plus a local reduce.
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

// ============================================================
// Compact lemmas
// ============================================================

/// compact_indices advances by 1 when pred[i] is true, stays when false.
pub proof fn lemma_compact_indices_step(pred: Seq<bool>, i: int)
    requires 0 <= i, i + 1 < pred.len() as int,
    ensures compact_indices(pred)[(i + 1) as int] ==
        compact_indices(pred)[i] + if pred[i] { 1nat } else { 0nat },
{
    assert(pred.take(i + 1).drop_last() =~= pred.take(i));
}

/// When pred[i] is true, compact_indices strictly increases.
pub proof fn lemma_compact_indices_monotone(pred: Seq<bool>, i: int)
    requires
        0 <= i,
        i + 1 < pred.len() as int,
        pred[i],
    ensures compact_indices(pred)[(i + 1) as int] > compact_indices(pred)[i],
{
    lemma_compact_indices_step(pred, i);
}

/// compact_result length equals compact_size.
pub proof fn lemma_compact_result_len<T>(data: Seq<T>, pred: Seq<bool>)
    requires data.len() == pred.len(),
    ensures compact_result(data, pred).len() == compact_size(pred),
    decreases data.len(),
{
    if data.len() > 0 {
        lemma_compact_result_len::<T>(data.drop_last(), pred.drop_last());
    }
}

/// compact_size is bounded by the predicate length.
pub proof fn lemma_compact_size_le_len(pred: Seq<bool>)
    ensures compact_size(pred) <= pred.len(),
    decreases pred.len(),
{
    if pred.len() > 0 {
        lemma_compact_size_le_len(pred.drop_last());
    }
}

// ============================================================
// log2_ceil / pow2 bounds
// ============================================================

/// Helper: (n + 1) / 2 properties for n > 1.
pub proof fn lemma_half_ceil_bounds(n: nat)
    requires n > 1,
    ensures
        (n + 1) / 2 >= 1,
        (n + 1) / 2 < n,
        2 * ((n + 1) / 2) >= n,
{
}

/// pow2(log2_ceil(n)) >= n for all n > 0.
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
        // log2_ceil(n) == 1 + k by definition unfolding
        assert(log2_ceil(n) == k + 1);
        // pow2(k + 1) = 2 * pow2(k) by pow2 definition unfolding
        assert(pow2((k + 1) as nat) == 2 * pow2(k));
        // Chain: pow2(log2_ceil(n)) = 2 * pow2(k) >= 2 * m >= n
    }
}

/// log2_ceil(1) = 0.
pub proof fn lemma_log2_ceil_one()
    ensures log2_ceil(1) == 0,
{
}

/// log2_ceil(n) < n for n >= 2 (used to bound recursion in exec).
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
        // 1 + log2_ceil(half) <= half < n
    } else {
        // half == 1 (since half >= 1 from lemma_half_ceil_bounds)
        // log2_ceil(n) = 1 + log2_ceil(1) = 1 + 0 = 1 < n (since n >= 2)
    }
}

/// pow2(d) < n when d < log2_ceil(n) and n > 1.
/// Used to prove stride doesn't overflow in exec loops.
pub proof fn lemma_pow2_lt_for_sub_levels(n: nat, d: nat)
    requires n > 1, d < log2_ceil(n),
    ensures pow2(d) < n,
    decreases n,
{
    let half = ((n + 1) / 2) as nat;
    lemma_half_ceil_bounds(n);
    // log2_ceil(n) = 1 + log2_ceil(half)
    if d == 0 {
        // pow2(0) = 1 < n since n > 1
    } else {
        // d >= 1, d < 1 + log2_ceil(half), so d - 1 < log2_ceil(half)
        if half > 1 {
            lemma_pow2_lt_for_sub_levels(half, (d - 1) as nat);
            // pow2(d-1) < half, pow2(d) = 2 * pow2(d-1)
            assert(pow2(d) == 2 * pow2((d - 1) as nat));
            // 2 * pow2(d-1) <= 2 * (half - 1) = 2*half - 2 <= n + 1 - 2 = n - 1 < n
        } else {
            // half == 1, log2_ceil(1) = 0
            // log2_ceil(n) = 1 + 0 = 1, d < 1 and d >= 1: contradiction
            assert(half == 1);
            lemma_log2_ceil_one();
        }
    }
}

/// If pow2(k) >= n then log2_ceil(n) <= k.
pub proof fn lemma_log2_ceil_upper_bound(n: nat, k: nat)
    requires n > 0, pow2(k) >= n,
    ensures log2_ceil(n) <= k,
    decreases n,
{
    if n <= 1 {
    } else {
        lemma_half_ceil_bounds(n);
        let half = ((n + 1) / 2) as nat;
        // k >= 1 since pow2(0) = 1 < 2 <= n but pow2(k) >= n
        if k == 0 {
            assert(pow2(0) == 1);
            assert(false); // contradiction
        }
        // pow2(k) = 2 * pow2(k-1) >= n, and half = ceil(n/2)
        // 2x >= n iff x >= ceil(n/2), so pow2(k-1) >= half
        assert(pow2(k) == 2 * pow2((k - 1) as nat));
        assert(pow2((k - 1) as nat) >= half) by(nonlinear_arith)
            requires
                2 * pow2((k - 1) as nat) >= n,
                half == ((n + 1) / 2) as nat,
                n >= 2;
        lemma_log2_ceil_upper_bound(half, (k - 1) as nat);
    }
}

} // verus!
