/// Proofs for radix sort: bit arithmetic, complement, scatter, stability, correctness.
use vstd::prelude::*;
use crate::swizzle::pow2;
use crate::scan::{compact_size, compact_indices, compact_result};
use crate::radix_sort::*;
use crate::proof::scan_lemmas::*;
// lemma_compact_scatter_disjoint now in scan_lemmas
use crate::proof::swizzle_lemmas::{lemma_pow2_positive, lemma_pow2_monotone};
use crate::proof::integer_helpers::*;

verus! {

// ============================================================
// Bit arithmetic
// ============================================================

/// bit_at is always 0 or 1.
pub proof fn lemma_bit_at_binary(val: nat, pos: nat)
    ensures bit_at(val, pos) == 0 || bit_at(val, pos) == 1,
{
    lemma_pow2_positive(pos);
    lemma_mod_bound(val / pow2(pos), 2);
}

/// low_bits(val, 0) == 0.
pub proof fn lemma_low_bits_zero(val: nat)
    ensures low_bits(val, 0) == 0,
{
    assert(pow2(0) == 1nat);
}

/// low_bits is bounded by pow2(k).
pub proof fn lemma_low_bits_bound(val: nat, k: nat)
    ensures low_bits(val, k) < pow2(k),
{
    lemma_pow2_positive(k);
    lemma_mod_bound(val, pow2(k));
}

/// When val < pow2(k), low_bits(val, k) == val.
pub proof fn lemma_low_bits_identity(val: nat, k: nat)
    requires val < pow2(k),
    ensures low_bits(val, k) == val,
{
    lemma_pow2_positive(k);
    lemma_mod_small(val, pow2(k));
}

/// low_bits step: low_bits(val, k+1) == low_bits(val, k) + bit_at(val, k) * pow2(k).
pub proof fn lemma_low_bits_step(val: nat, k: nat)
    ensures low_bits(val, k + 1) == low_bits(val, k) + bit_at(val, k) * pow2(k),
{
    lemma_pow2_positive(k);
    let p = pow2(k);
    assert(pow2((k + 1) as nat) == 2 * p);
    // lemma_mod_breakdown(x, y, z): x % (y*z) == y * ((x/y) % z) + x % y
    // Instantiate with x=val, y=p, z=2:
    //   val % (p*2) == p * ((val/p) % 2) + val % p
    //   i.e., low_bits(val,k+1) == pow2(k) * bit_at(val,k) + low_bits(val,k)
    vstd::arithmetic::div_mod::lemma_mod_breakdown(val as int, p as int, 2);
    // mod_breakdown gives: val as int % (p as int * 2) == p as int * ((val as int / p as int) % 2) + val as int % p as int
    // Connect to nat-level specs:
    assert(val as int % (p as int * 2) == (val % (p * 2)) as int) by (nonlinear_arith)
        requires p > 0;
    assert(p as int * 2 == (p * 2) as int) by (nonlinear_arith)
        requires p > 0;
    assert(val as int / p as int == (val / p) as int) by (nonlinear_arith)
        requires p > 0;
    assert((val as int / p as int) % 2 == ((val / p) % 2) as int) by (nonlinear_arith)
        requires p > 0;
    assert(val as int % p as int == (val % p) as int) by (nonlinear_arith)
        requires p > 0;
    // Now: (val % (p * 2)) as int == p as int * ((val / p) % 2) as int + (val % p) as int
    // i.e., val % (2 * p) == p * ((val / p) % 2) + val % p
    assert(p * 2 == 2 * p) by (nonlinear_arith);
    assert(val % (2 * p) == pow2(k) * bit_at(val, k) + low_bits(val, k)) by (nonlinear_arith)
        requires val % (2 * p) == val % (p * 2),
                 (val % (p * 2)) as int == p as int * (((val / p) % 2) as int) + ((val % p) as int),
                 p == pow2(k),
                 bit_at(val, k) == (val / pow2(k)) % 2,
                 low_bits(val, k) == val % pow2(k);
    // bit_at(val, k) * pow2(k) == pow2(k) * bit_at(val, k)
    assert(bit_at(val, k) * pow2(k) == pow2(k) * bit_at(val, k)) by (nonlinear_arith);
}

// ============================================================
// Complement lemmas
// ============================================================

/// compact_size of complement + compact_size of original == length.
pub proof fn lemma_complement_compact_size(pred: Seq<bool>)
    ensures compact_size(pred_complement(pred)) + compact_size(pred) == pred.len(),
    decreases pred.len(),
{
    if pred.len() > 0 {
        let pred_c = pred_complement(pred);
        assert(pred_c.drop_last() =~= pred_complement(pred.drop_last()));
        lemma_complement_compact_size(pred.drop_last());
    }
}

/// compact_indices of complement: not_rank[i] = i - rank[i].
pub proof fn lemma_complement_compact_indices(pred: Seq<bool>, i: int)
    requires 0 <= i, i < pred.len() as int,
    ensures
        compact_indices(pred_complement(pred))[i]
            == (i as nat - compact_indices(pred)[i]),
{
    let pred_c = pred_complement(pred);
    assert(pred_c.take(i) =~= pred_complement(pred.take(i)));
    lemma_complement_compact_size(pred.take(i));
}

// ============================================================
// Radix step length
// ============================================================

/// radix_step preserves length.
pub proof fn lemma_radix_step_len(data: Seq<nat>, pos: nat)
    ensures radix_step(data, pos).len() == data.len(),
{
    let pred = pred_bit(data, pos);
    let not_pred = pred_complement(pred);
    lemma_compact_result_len::<nat>(data, not_pred);
    lemma_compact_result_len::<nat>(data, pred);
    lemma_complement_compact_size(pred);
}

// ============================================================
// Scatter properties
// ============================================================

/// Scatter destinations are in bounds.
pub proof fn lemma_radix_scatter_in_bounds(data: Seq<nat>, pos: nat, i: nat)
    requires i < data.len(),
    ensures radix_scatter_dest(data, pos, i) < data.len(),
{
    let pred = pred_bit(data, pos);
    let not_pred = pred_complement(pred);

    lemma_bit_at_binary(data[i as int], pos);
    if bit_at(data[i as int], pos) == 0 {
        lemma_compact_indices_le_i(pred, i as int);
        lemma_complement_compact_indices(pred, i as int);
        // dest = compact_indices(not_pred)[i] < compact_size(not_pred) <= data.len()
        assert(not_pred[i as int]);
        lemma_compact_size_take_lt(not_pred, i as int);
        lemma_compact_size_le_len(not_pred);
    } else {
        // dest = count_zeros + compact_indices(pred)[i]
        lemma_complement_compact_size(pred);
        assert(pred[i as int]);
        lemma_compact_size_take_lt(pred, i as int);
    }
}

/// Scatter is injective: distinct inputs map to distinct destinations.
pub proof fn lemma_radix_scatter_injective(data: Seq<nat>, pos: nat, i: nat, j: nat)
    requires
        i < data.len(), j < data.len(), i != j,
    ensures
        radix_scatter_dest(data, pos, i) != radix_scatter_dest(data, pos, j),
{
    let pred = pred_bit(data, pos);
    let not_pred = pred_complement(pred);

    lemma_bit_at_binary(data[i as int], pos);
    lemma_bit_at_binary(data[j as int], pos);

    let bi = bit_at(data[i as int], pos);
    let bj = bit_at(data[j as int], pos);

    if bi == 0 && bj == 0 {
        // Both in zero section: dest = compact_indices(not_pred)[i/j]
        lemma_complement_compact_indices(pred, i as int);
        lemma_complement_compact_indices(pred, j as int);
        assert(not_pred[i as int] && not_pred[j as int]);
        if i < j {
            lemma_compact_scatter_disjoint(not_pred, i as int, j as int);
        } else {
            lemma_compact_scatter_disjoint(not_pred, j as int, i as int);
        }
    } else if bi == 1 && bj == 1 {
        // Both in ones section: dest = cz + compact_indices(pred)[i/j]
        assert(pred[i as int] && pred[j as int]);
        if i < j {
            lemma_compact_scatter_disjoint(pred, i as int, j as int);
        } else {
            lemma_compact_scatter_disjoint(pred, j as int, i as int);
        }
    } else {
        // Cross-bit: one in [0, count_zeros), other in [count_zeros, n)
        lemma_complement_compact_size(pred);
        let cz = count_zeros(data, pos);
        if bi == 0 {
            // dest_i < cz, dest_j >= cz
            lemma_compact_indices_le_i(pred, i as int);
            lemma_complement_compact_indices(pred, i as int);
            assert(not_pred[i as int]);
            lemma_compact_size_take_lt(not_pred, i as int);
            // dest_i = compact_indices(not_pred)[i] < compact_size(not_pred) = cz
            // dest_j = cz + compact_indices(pred)[j] >= cz
        } else {
            // dest_i >= cz, dest_j < cz
            lemma_compact_indices_le_i(pred, j as int);
            lemma_complement_compact_indices(pred, j as int);
            assert(not_pred[j as int]);
            lemma_compact_size_take_lt(not_pred, j as int);
        }
    }
}

// ============================================================
// Connecting scatter to radix_step definition
// ============================================================

/// The scatter permutation produces the same result as the spec radix_step.
pub proof fn lemma_radix_scatter_produces_step(data: Seq<nat>, pos: nat, i: nat)
    requires i < data.len(),
    ensures
        radix_step(data, pos)[radix_scatter_dest(data, pos, i) as int] == data[i as int],
{
    let pred = pred_bit(data, pos);
    let not_pred = pred_complement(pred);

    lemma_bit_at_binary(data[i as int], pos);
    lemma_compact_result_len::<nat>(data, not_pred);
    lemma_compact_result_len::<nat>(data, pred);
    lemma_complement_compact_size(pred);

    let cz = compact_size(not_pred);
    let zeros = compact_result(data, not_pred);
    let ones = compact_result(data, pred);

    if bit_at(data[i as int], pos) == 0 {
        // dest = i - rank_ones[i] = rank_zeros[i] (via complement)
        lemma_complement_compact_indices(pred, i as int);
        lemma_compact_indices_le_i(pred, i as int);
        let dest = (i as int - compact_indices(pred)[i as int] as int) as nat;
        assert(dest == compact_indices(not_pred)[i as int]);
        assert(not_pred[i as int]);
        lemma_compact_result_at(data, not_pred, i as int);
        lemma_compact_size_take_lt(not_pred, i as int);
        assert(dest < cz);
        // radix_step = zeros ++ ones, dest < zeros.len()
        assert(zeros[dest as int] == data[i as int]);
        assert((zeros + ones)[dest as int] == zeros[dest as int]);
    } else {
        // dest = cz + rank
        let rank = compact_indices(pred)[i as int];
        assert(pred[i as int]);
        lemma_compact_result_at(data, pred, i as int);
        assert(ones[rank as int] == data[i as int]);
        // Need: radix_step[cz + rank] == ones[rank]
        // radix_step = zeros + ones where zeros.len() == cz
        lemma_compact_size_take_lt(pred, i as int);
        assert(rank < ones.len());
        // Use Seq::add spec directly
        let combined = zeros + ones;
        let idx = (cz + rank) as int;
        assert(idx >= zeros.len() as int);
        // Build the index manually through the Seq::add definition
        assert(combined.len() == zeros.len() + ones.len());
        assert(combined[idx] == ones[idx - zeros.len() as int]) by {
            // This should trigger the Seq::add axiom for idx >= first.len()
            assert(zeros.len() as int <= idx);
        };
    }
}

// ============================================================
// Compact preserves elements (with predicate tracking)
// ============================================================

/// Every element of compact_result comes from an original data position where pred is true.
pub proof fn lemma_compact_result_elements_with_pred(data: Seq<nat>, pred: Seq<bool>, j: int)
    requires
        data.len() == pred.len(),
        0 <= j, j < compact_size(pred) as int,
    ensures
        exists|k: int| 0 <= k < data.len() && compact_result(data, pred)[j] == data[k] && pred[k],
    decreases data.len(),
{
    if data.len() == 0 {
    } else {
        let rest = compact_result(data.drop_last(), pred.drop_last());
        lemma_compact_result_len::<nat>(data.drop_last(), pred.drop_last());
        if pred.last() {
            if j == rest.len() as int {
                assert(compact_result(data, pred)[j] == data.last());
                assert(data.last() == data[data.len() - 1]);
                assert(pred[data.len() - 1]);
            } else {
                lemma_compact_result_elements_with_pred(data.drop_last(), pred.drop_last(), j);
                let k = choose|k: int| 0 <= k < data.drop_last().len()
                    && rest[j] == data.drop_last()[k] && pred.drop_last()[k];
                assert(data.drop_last()[k] == data[k]);
                assert(pred.drop_last()[k] == pred[k]);
            }
        } else {
            lemma_compact_result_elements_with_pred(data.drop_last(), pred.drop_last(), j);
            let k = choose|k: int| 0 <= k < data.drop_last().len()
                && rest[j] == data.drop_last()[k] && pred.drop_last()[k];
            assert(data.drop_last()[k] == data[k]);
            assert(pred.drop_last()[k] == pred[k]);
        }
    }
}

/// Simple version: every element of compact_result comes from the original data.
pub proof fn lemma_compact_result_elements(data: Seq<nat>, pred: Seq<bool>, j: int)
    requires
        data.len() == pred.len(),
        0 <= j, j < compact_size(pred) as int,
    ensures
        exists|k: int| 0 <= k < data.len() && compact_result(data, pred)[j] == data[k],
{
    lemma_compact_result_elements_with_pred(data, pred, j);
}

// ============================================================
// Compact preserves relative order (stability)
// ============================================================

/// compact_result preserves sorted-by-key order.
pub proof fn lemma_compact_preserves_sorted(data: Seq<nat>, pred: Seq<bool>, key: spec_fn(nat) -> nat)
    requires
        data.len() == pred.len(),
        is_sorted_by_key(data, key),
    ensures
        is_sorted_by_key(compact_result(data, pred), key),
    decreases data.len(),
{
    if data.len() == 0 {
    } else {
        let rest_data = data.drop_last();
        let rest_pred = pred.drop_last();
        let rest = compact_result(rest_data, rest_pred);
        lemma_compact_preserves_sorted(rest_data, rest_pred, key);

        if pred.last() {
            lemma_compact_result_len::<nat>(rest_data, rest_pred);
            let result = rest.push(data.last());
            assert forall|i: int, j: int| 0 <= i < j < result.len() as int
            implies key(result[i]) <= key(result[j])
            by {
                if j < rest.len() as int {
                    assert(key(rest[i]) <= key(rest[j]));
                } else {
                    assert(j == rest.len());
                    assert(result[j] == data.last());
                    lemma_compact_result_elements_with_pred(rest_data, rest_pred, i);
                    let k = choose|k: int| 0 <= k < rest_data.len()
                        && rest[i] == rest_data[k] && rest_pred[k];
                    assert(rest_data[k] == data[k]);
                    assert(key(data[k]) <= key(data[data.len() - 1]));
                }
            }
        }
    }
}

// ============================================================
// Radix sort invariant
// ============================================================

/// After k steps, result is sorted by low_bits(_, k).
pub proof fn lemma_radix_sort_invariant(data: Seq<nat>, k: nat)
    ensures is_sorted_by_key(radix_sort_partial(data, k), |v: nat| low_bits(v, k)),
    decreases k,
{
    if k == 0 {
        assert forall|i: int, j: int|
            0 <= i < j < radix_sort_partial(data, 0).len() as int
        implies low_bits(radix_sort_partial(data, 0)[i], 0) <= low_bits(radix_sort_partial(data, 0)[j], 0)
        by {
            lemma_low_bits_zero(radix_sort_partial(data, 0)[i]);
            lemma_low_bits_zero(radix_sort_partial(data, 0)[j]);
        }
    } else {
        let prev = radix_sort_partial(data, (k - 1) as nat);
        let result = radix_step(prev, (k - 1) as nat);
        let pos = (k - 1) as nat;
        let pred = pred_bit(prev, pos);
        let not_pred = pred_complement(pred);
        let zeros = compact_result(prev, not_pred);
        let ones = compact_result(prev, pred);

        lemma_radix_sort_invariant(data, (k - 1) as nat);

        lemma_compact_result_len::<nat>(prev, not_pred);
        lemma_compact_result_len::<nat>(prev, pred);
        lemma_complement_compact_size(pred);
        lemma_radix_step_len(prev, pos);

        let cz = compact_size(not_pred);
        let key_prev = |v: nat| -> nat { low_bits(v, (k - 1) as nat) };

        lemma_compact_preserves_sorted(prev, not_pred, key_prev);
        lemma_compact_preserves_sorted(prev, pred, key_prev);

        let key_k = |v: nat| -> nat { low_bits(v, k) };

        assert forall|i: int, j: int|
            0 <= i < j < result.len() as int
        implies key_k(result[i]) <= key_k(result[j])
        by {
            if i < cz as int && j < cz as int {
                // Both in zeros section
                assert(result[i] == zeros[i]);
                assert(result[j] == zeros[j]);
                // Elements from not_pred compact have bit=0
                lemma_compact_result_elements_with_pred(prev, not_pred, i);
                lemma_compact_result_elements_with_pred(prev, not_pred, j);
                let ki = choose|k: int| 0 <= k < prev.len()
                    && zeros[i] == prev[k] && not_pred[k];
                let kj = choose|k: int| 0 <= k < prev.len()
                    && zeros[j] == prev[k] && not_pred[k];
                // not_pred[ki] means !pred[ki] means bit_at == 0
                lemma_bit_at_binary(prev[ki], pos);
                lemma_bit_at_binary(prev[kj], pos);
                assert(bit_at(zeros[i], pos) == 0);
                assert(bit_at(zeros[j], pos) == 0);
                lemma_low_bits_step(zeros[i], pos);
                lemma_low_bits_step(zeros[j], pos);
                // key_k = key_prev since bit*pow2 = 0
                assert(key_prev(zeros[i]) <= key_prev(zeros[j]));
            } else if i >= cz as int && j >= cz as int {
                // Both in ones section
                let oi = (i - cz as int) as int;
                let oj = (j - cz as int) as int;
                assert(result[i] == ones[oi]);
                assert(result[j] == ones[oj]);
                lemma_compact_result_elements_with_pred(prev, pred, oi);
                lemma_compact_result_elements_with_pred(prev, pred, oj);
                let ki = choose|k: int| 0 <= k < prev.len()
                    && ones[oi] == prev[k] && pred[k];
                let kj = choose|k: int| 0 <= k < prev.len()
                    && ones[oj] == prev[k] && pred[k];
                assert(bit_at(ones[oi], pos) == 1);
                assert(bit_at(ones[oj], pos) == 1);
                lemma_low_bits_step(ones[oi], pos);
                lemma_low_bits_step(ones[oj], pos);
                assert(key_prev(ones[oi]) <= key_prev(ones[oj]));
            } else {
                // i in zeros, j in ones
                assert(i < cz as int && j >= cz as int);
                let oj = (j - cz as int) as int;
                assert(result[i] == zeros[i]);
                assert(result[j] == ones[oj]);
                lemma_compact_result_elements_with_pred(prev, not_pred, i);
                lemma_compact_result_elements_with_pred(prev, pred, oj);
                let ki = choose|k: int| 0 <= k < prev.len()
                    && zeros[i] == prev[k] && not_pred[k];
                let kj = choose|k: int| 0 <= k < prev.len()
                    && ones[oj] == prev[k] && pred[k];
                lemma_bit_at_binary(prev[ki], pos);
                assert(bit_at(zeros[i], pos) == 0);
                assert(bit_at(ones[oj], pos) == 1);
                lemma_low_bits_step(zeros[i], pos);
                lemma_low_bits_step(ones[oj], pos);
                // key_k(zeros[i]) = key_prev(zeros[i]) < pow2(k-1) <= pow2(k-1) + key_prev(ones[oj]) = key_k(ones[oj])
                lemma_low_bits_bound(zeros[i], pos);
            }
        }
    }
}

// ============================================================
// Main theorems
// ============================================================

/// radix_sort preserves length.
pub proof fn lemma_radix_sort_len(data: Seq<nat>, num_bits: nat)
    ensures radix_sort(data, num_bits).len() == data.len(),
    decreases num_bits,
{
    if num_bits > 0 {
        lemma_radix_sort_len(data, (num_bits - 1) as nat);
        lemma_radix_step_len(radix_sort_partial(data, (num_bits - 1) as nat), (num_bits - 1) as nat);
    }
}

/// Every element of radix_sort comes from the original data.
pub proof fn lemma_radix_sort_elements(data: Seq<nat>, num_bits: nat, j: int)
    requires 0 <= j, j < data.len() as int,
    ensures
        exists|k: int| 0 <= k < data.len() && radix_sort(data, num_bits)[j] == data[k],
    decreases num_bits,
{
    if num_bits == 0 {
        assert(radix_sort(data, 0)[j] == data[j]);
    } else {
        let prev = radix_sort_partial(data, (num_bits - 1) as nat);
        lemma_radix_sort_len(data, (num_bits - 1) as nat);
        let pos = (num_bits - 1) as nat;
        let pred = pred_bit(prev, pos);
        let not_pred = pred_complement(pred);

        lemma_compact_result_len::<nat>(prev, not_pred);
        lemma_compact_result_len::<nat>(prev, pred);
        lemma_complement_compact_size(pred);
        let cz = compact_size(not_pred);

        if j < cz as int {
            lemma_compact_result_elements(prev, not_pred, j);
        } else {
            lemma_compact_result_elements(prev, pred, j - cz as int);
        }
        let k_prev = choose|k: int| 0 <= k < prev.len()
            && radix_step(prev, pos)[j] == prev[k];
        lemma_radix_sort_elements(data, (num_bits - 1) as nat, k_prev);
    }
}

/// Correctness: if all values < pow2(num_bits), radix sort produces a sorted sequence.
pub proof fn lemma_radix_sort_correct(data: Seq<nat>, num_bits: nat)
    requires
        forall|i: int| 0 <= i < data.len() as int ==> data[i] < pow2(num_bits),
    ensures
        is_sorted_nat(radix_sort(data, num_bits)),
{
    lemma_radix_sort_invariant(data, num_bits);
    lemma_radix_sort_len(data, num_bits);
    let result = radix_sort(data, num_bits);

    assert forall|i: int, j: int| 0 <= i < j < result.len() as int
    implies result[i] <= result[j]
    by {
        lemma_radix_sort_elements(data, num_bits, i);
        lemma_radix_sort_elements(data, num_bits, j);
        let ki = choose|k: int| 0 <= k < data.len() && result[i] == data[k];
        let kj = choose|k: int| 0 <= k < data.len() && result[j] == data[k];
        lemma_low_bits_identity(result[i], num_bits);
        lemma_low_bits_identity(result[j], num_bits);
    }
}

} // verus!
