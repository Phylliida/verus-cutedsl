/// Brent-Kung inclusive scan correctness proofs.
///
/// Proves that the Brent-Kung down-sweep produces the inclusive prefix sum.
/// Key structure:
/// - Base case (k=0): positions at pow2(total_levels-1) multiples already hold
///   inclusive_scan via tree reduce invariant.
/// - Inductive step: modified positions combine inclusive prefix + local sum via sum_split.
/// - Final (k=total_levels-1): every position active, gives inclusive_scan.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_tree::*;
use crate::scan_brent_kung::*;
use crate::swizzle::pow2;
use crate::proof::scan_blelloch_lemmas::*;
use crate::proof::swizzle_lemmas::*;

verus! {

// ============================================================
// Base case: k = 0
// ============================================================

/// Brent-Kung down-sweep invariant holds at k=0 (base case).
///
/// At k=0, the state is the tree reduce result. Positions where
/// pow2(total_levels - 1) divides (j+1) hold sum(data, 0, j+1) = inclusive_scan[j]
/// from the tree reduce invariant. Other positions hold tree_reduce_state values.
pub proof fn lemma_bk_downsweep_base(data: Seq<int>, n: nat, total_levels: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
    ensures bk_downsweep_invariant(data, n, total_levels, 0),
{
    let state = bk_downsweep_state(data, n, total_levels, 0);
    let threshold = pow2((total_levels - 1) as nat);

    assert(state.len() == n);

    assert forall|j: int| 0 <= j < n as int
    implies #[trigger] state[j] == bk_expected(data, n, total_levels, 0, j)
    by {
        // state[j] = tree_reduce_state(data, n, total_levels)[j]
        // bk_expected: if (j+1) % threshold == 0, should be sum(data, 0, j+1)
        //              else, tree_reduce_state[j]
        if (j + 1) % (threshold as int) == 0 {
            // (j+1) divisible by pow2(total_levels - 1)
            // Tree reduce invariant at level total_levels: state[j] == sum(data, j+1-pow2(total_levels), j+1)
            // But we need sum(data, 0, j+1).
            //
            // Since pow2(total_levels - 1) | (j+1), either pow2(total_levels) | (j+1) or not.
            // pow2(total_levels) = n, and j+1 <= n.
            // If (j+1) == n: pow2(total_levels) | (j+1), tree reduce gives sum(data, 0, n) = sum(data, 0, j+1) ✓
            // If (j+1) < n: (j+1) = threshold * m with m odd (since pow2(total_levels) doesn't divide j+1)
            //   But wait — threshold = n/2, so j+1 = (n/2)*m. Since j+1 <= n, m <= 2.
            //   m == 1: j+1 = n/2. m == 2: j+1 = n (handled above). So j+1 = n/2.
            //   Tree reduce at level total_levels - 1: state[j] == sum(data, j+1-threshold, j+1) = sum(data, 0, n/2) = sum(data, 0, j+1) ✓

            lemma_pow2_positive((total_levels - 1) as nat);
            assert(pow2(total_levels) == 2 * pow2((total_levels - 1) as nat));

            if j + 1 == n as int {
                // j = n-1, tree reduce at total_levels: sum(data, 0, n)
                lemma_tree_reduce_invariant_all(data, n, total_levels, total_levels);
            } else {
                // j+1 = threshold, j+1 < n
                // (j+1) % pow2(total_levels) != 0 since j+1 < n = pow2(total_levels)
                assert(j + 1 < n as int);
                vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, pow2(total_levels));
                assert((j + 1) % (pow2(total_levels) as int) != 0);

                // Exact divisibility level for j is total_levels - 1
                lemma_tree_reduce_value_at_exact_level(data, n, total_levels, (total_levels - 1) as nat, j);
                // tree_reduce_state[j] == sum(data, j+1-threshold, j+1)
                // j+1 = threshold (only valid value), so j+1 - threshold = 0
                // j+1 is a multiple of threshold and j+1 < n = 2*threshold
                // so j+1 must be exactly threshold
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, threshold as int);
                let m = (j + 1) / (threshold as int);
                assert(j + 1 == threshold as int * m);
                assert(m >= 1) by (nonlinear_arith)
                    requires j + 1 == threshold as int * m, j + 1 > 0, threshold > 0;
                assert(m <= 1) by (nonlinear_arith)
                    requires j + 1 == threshold as int * m, j + 1 < 2 * threshold as int;
                assert(m == 1);
                assert(j + 1 == threshold as int) by (nonlinear_arith)
                    requires j + 1 == threshold as int * m, m == 1;
                assert(j + 1 - threshold as int == 0);
            }
        }
        // else: bk_expected is tree_reduce_state[j], which equals state[j] directly
    }
}

// ============================================================
// Inductive step: k → k+1
// ============================================================

/// Brent-Kung down-sweep invariant: inductive step from k to k+1.
pub proof fn lemma_bk_downsweep_step(data: Seq<int>, n: nat, total_levels: nat, k: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 1,
        k + 1 < total_levels,  // k+1 is a valid down-sweep level (up to total_levels - 2)
        bk_downsweep_invariant(data, n, total_levels, k),
    ensures bk_downsweep_invariant(data, n, total_levels, (k + 1) as nat),
{
    let prev = bk_downsweep_state(data, n, total_levels, k);
    let next = bk_downsweep_state(data, n, total_levels, (k + 1) as nat);
    let stride = pow2((total_levels - k - 2) as nat);
    let old_threshold = pow2((total_levels - k - 1) as nat);
    let new_threshold = pow2((total_levels - k - 2) as nat);

    lemma_pow2_positive((total_levels - k - 2) as nat);
    lemma_pow2_positive((total_levels - k - 1) as nat);

    // Key relation: old_threshold = 2 * new_threshold = 2 * stride
    assert(old_threshold == 2 * stride) by {
        assert(pow2((total_levels - k - 1) as nat) == 2 * pow2((total_levels - k - 2) as nat));
    };

    assert(next.len() == n);

    assert forall|j: int| 0 <= j < n as int
    implies #[trigger] next[j] == bk_expected(data, n, total_levels, (k + 1) as nat, j)
    by {
        assert(new_threshold == stride);

        if (j + 1) % (2 * stride as int) == stride as int && j >= stride as int {
            // ========== MODIFIED position ==========
            // next[j] = prev[j] + prev[j - stride]

            // (j+1) % new_threshold == 0 since (j+1) % stride == 0:
            // (j+1) % (2*stride) == stride means (j+1) = 2*stride*q + stride = stride*(2q+1)
            // So (j+1) % stride == 0
            assert((j + 1) % (stride as int) == 0) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, (2 * stride as int));
                let q = (j + 1) / (2 * stride as int);
                assert(j + 1 == (2 * stride as int) * q + stride as int);
                assert(j + 1 == stride as int * (2 * q + 1)) by (nonlinear_arith)
                    requires j + 1 == (2 * stride as int) * q + stride as int;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    j + 1, stride as int, 2 * q + 1, 0
                );
            };

            // bk_expected at k+1: (j+1) % new_threshold == 0, so sum(data, 0, j+1)
            // We need next[j] = sum(data, 0, j+1)

            // prev[j] by IH: (j+1) % (2*stride) == stride != 0, so (j+1) % old_threshold != 0
            // (because old_threshold = 2*stride and (j+1) % (2*stride) = stride ≠ 0)
            assert((j + 1) % (old_threshold as int) != 0) by (nonlinear_arith)
                requires (j + 1) % (2 * stride as int) == stride as int, stride > 0, old_threshold == 2 * stride;
            // So prev[j] = tree_reduce_state[j]
            assert(prev[j] == bk_expected(data, n, total_levels, k, j));
            assert(prev[j] == tree_reduce_state(data, n, total_levels)[j]);

            // (j+1) % stride == 0 but (j+1) % (2*stride) == stride ≠ 0
            // So the exact divisibility level d for j satisfies:
            // pow2(d) | (j+1) but pow2(d+1) ∤ (j+1)
            // Since (j+1) % stride == 0 and (j+1) % (2*stride) != 0,
            // and stride = pow2(total_levels - k - 2):
            // d = total_levels - k - 2
            let d = (total_levels - k - 2) as nat;
            assert(pow2(d) == stride);
            assert(pow2((d + 1) as nat) == old_threshold);
            assert((j + 1) % (pow2(d) as int) == 0);
            assert((j + 1) % (pow2((d + 1) as nat) as int) != 0);

            lemma_tree_reduce_value_at_exact_level(data, n, total_levels, d, j);
            // tree_reduce_state[j] == sum(data, j+1-stride, j+1)
            assert(prev[j] == sum::<int>(|i: int| data[i], j + 1 - stride as int, j + 1));

            // prev[j - stride] by IH:
            let partner = j - stride as int;
            assert(0 <= partner);
            assert(partner < n as int);

            // (partner+1) % old_threshold == 0:
            // partner+1 = j+1-stride = stride*(2q+1) - stride = stride*2q = old_threshold*q
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, (2 * stride as int));
            let q = (j + 1) / (2 * stride as int);
            assert(j + 1 == (2 * stride as int) * q + stride as int);
            assert(partner + 1 == (2 * stride as int) * q) by (nonlinear_arith)
                requires partner == j - stride as int,
                         j + 1 == (2 * stride as int) * q + stride as int;

            // q >= 1: partner+1 = 2*stride*q, and partner >= 0, so partner+1 >= 1
            // If q == 0 then partner+1 == 0 but partner >= 0 means partner+1 >= 1. Contradiction.
            assert(q >= 1) by (nonlinear_arith)
                requires partner + 1 == (2 * stride as int) * q, partner >= 0, stride > 0;

            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                partner + 1, old_threshold as int, q, 0
            );
            assert((partner + 1) % (old_threshold as int) == 0);

            // So prev[partner] = sum(data, 0, partner+1)
            assert(prev[partner] == bk_expected(data, n, total_levels, k, partner));
            assert(prev[partner] == sum::<int>(|i: int| data[i], 0, partner + 1));

            // Combine: next[j] = prev[j] + prev[partner]
            //                   = sum(data, j+1-stride, j+1) + sum(data, 0, partner+1)
            //                   = sum(data, j+1-stride, j+1) + sum(data, 0, j+1-stride)
            assert(partner + 1 == j + 1 - stride as int);

            // sum_split: sum(data, 0, j+1) = sum(data, 0, j+1-stride) + sum(data, j+1-stride, j+1)
            assert(j + 1 - stride as int >= 0) by (nonlinear_arith)
                requires j >= stride as int;
            lemma_sum_split::<int>(|i: int| data[i], 0, j + 1 - stride as int, j + 1);
            // sum(0, j+1) == sum(0, j+1-stride) + sum(j+1-stride, j+1)
            // next[j] = prev[partner] + prev[j] = sum(0, partner+1) + sum(j+1-stride, j+1)
            //         = sum(0, j+1-stride) + sum(j+1-stride, j+1) = sum(0, j+1) ✓

        } else {
            // ========== UNCHANGED position ==========
            // next[j] = prev[j]

            if (j + 1) % (new_threshold as int) == 0 {
                // (j+1) divisible by new_threshold = stride
                // Since position is unchanged (not modified), this must mean
                // (j+1) % old_threshold == 0 (prev already held the right value)
                //
                // (j+1) % stride == 0 but position not modified means:
                // NOT ((j+1) % (2*stride) == stride && j >= stride)
                // Case 1: (j+1) % (2*stride) == 0 (divisible by old_threshold)
                // Case 2: (j+1) % (2*stride) == stride but j < stride
                //   In this case j+1 = stride*(2q+1) for some q, and j < stride means
                //   stride*(2q+1) <= stride, so 2q+1 <= 1, q == 0, j+1 = stride, j = stride-1 < stride ✓
                //   Then j+1 = stride = old_threshold/2, (j+1)%old_threshold = stride ≠ 0

                if (j + 1) % (2 * stride as int) == 0 {
                    // (j+1) % old_threshold == 0
                    assert((j + 1) % (old_threshold as int) == 0);
                    // By IH: prev[j] = sum(data, 0, j+1)
                    assert(prev[j] == bk_expected(data, n, total_levels, k, j));
                } else if (j + 1) % (2 * stride as int) == stride as int {
                    // j < stride (since position wasn't modified)
                    // j+1 <= stride, j+1 = stride*(2q+1), so 2q+1 = 1 (q=0), j+1 = stride
                    // prev[j]: (j+1) % old_threshold == stride ≠ 0, so tree_reduce_state[j]
                    // But we need sum(data, 0, j+1)
                    // j = stride - 1, j+1 = stride = new_threshold
                    assert(j + 1 == stride as int) by (nonlinear_arith)
                        requires
                            (j + 1) % (2 * stride as int) == stride as int,
                            j < stride as int,
                            j >= 0,
                            stride > 0,
                    {
                        vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, (2 * stride) as nat);
                    };
                    // j+1 = stride, so (j+1) % old_threshold = stride ≠ 0
                    // prev[j] = tree_reduce_state[j]
                    assert(prev[j] == bk_expected(data, n, total_levels, k, j));
                    assert((j + 1) % (old_threshold as int) != 0) by (nonlinear_arith)
                        requires j + 1 == stride as int, old_threshold == 2 * stride, stride > 0;
                    assert(prev[j] == tree_reduce_state(data, n, total_levels)[j]);

                    // Need to show tree_reduce_state[j] = sum(data, 0, j+1) = sum(data, 0, stride)
                    // j+1 = stride = pow2(total_levels - k - 2)
                    // Tree reduce at level (total_levels-k-2): state[j] == sum(data, j+1-stride, j+1) = sum(data, 0, stride)
                    // But we need exact divisibility level = total_levels-k-2

                    // (j+1) = stride = pow2(d) where d = total_levels-k-2
                    // pow2(d) | stride ✓. pow2(d+1) | stride? stride = pow2(d), pow2(d+1) = 2*pow2(d) = 2*stride
                    // stride % (2*stride) = stride ≠ 0, so pow2(d+1) ∤ (j+1) ✓
                    let d = (total_levels - k - 2) as nat;
                    assert(pow2(d) == stride);
                    assert(pow2((d + 1) as nat) == old_threshold);
                    assert((j + 1) % (pow2(d) as int) == 0);
                    assert((j + 1) % (pow2((d + 1) as nat) as int) != 0);

                    lemma_tree_reduce_value_at_exact_level(data, n, total_levels, d, j);
                    assert(prev[j] == sum::<int>(|i: int| data[i], j + 1 - stride as int, j + 1));
                    assert(j + 1 - stride as int == 0);
                } else {
                    // (j+1) % (2*stride) is neither 0 nor stride
                    // But (j+1) % stride == 0. Then (j+1) = stride * m for some m.
                    // (j+1) % (2*stride) = stride * m % (2*stride).
                    // If m is even: (j+1) % (2*stride) == 0. If m is odd: (j+1) % (2*stride) == stride.
                    // So we must be in one of the two cases above — contradiction
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, stride as int);
                    let m = (j + 1) / (stride as int);
                    assert(j + 1 == stride as int * m);
                    assert((j + 1) % (stride as int) == 0);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, 2);
                    let q = m / 2;
                    let r = m % 2;
                    assert(m == 2 * q + r);
                    if r == 0 {
                        assert(j + 1 == (2 * stride as int) * q) by (nonlinear_arith)
                            requires j + 1 == stride as int * m, m == 2 * q;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                            j + 1, (2 * stride as int), q, 0
                        );
                        assert(false);
                    } else {
                        assert(j + 1 == (2 * stride as int) * q + stride as int) by (nonlinear_arith)
                            requires j + 1 == stride as int * m, m == 2 * q + r, r == 1;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                            j + 1, (2 * stride as int), q, stride as int
                        );
                        assert(false);
                    }
                }
            } else {
                // (j+1) not divisible by new_threshold
                // bk_expected at k+1: tree_reduce_state[j]

                // prev[j] by IH:
                // If (j+1) % old_threshold == 0: prev[j] = sum(data, 0, j+1)
                //   But (j+1) % new_threshold != 0 and new_threshold | old_threshold... contradiction?
                //   Actually old_threshold = 2*new_threshold. If (j+1) % old_threshold == 0 then
                //   (j+1) % new_threshold == 0. But we assumed (j+1) % new_threshold != 0. Contradiction.
                if (j + 1) % (old_threshold as int) == 0 {
                    lemma_mod_pow2_weaken((j + 1) as nat, (total_levels - k - 1) as nat, (total_levels - k - 2) as nat);
                    assert(false);
                }
                // So (j+1) % old_threshold != 0, prev[j] = tree_reduce_state[j] ✓
                assert(prev[j] == bk_expected(data, n, total_levels, k, j));
            }
        }
    }
}

// ============================================================
// Master invariant + correctness
// ============================================================

/// Brent-Kung down-sweep invariant holds at all levels 0..total_levels-1.
pub proof fn lemma_bk_invariant_all(data: Seq<int>, n: nat, total_levels: nat, k: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
        k < total_levels,
    ensures bk_downsweep_invariant(data, n, total_levels, k),
    decreases k,
{
    if k == 0 {
        lemma_bk_downsweep_base(data, n, total_levels);
    } else {
        lemma_bk_invariant_all(data, n, total_levels, (k - 1) as nat);
        if total_levels > 1 {
            lemma_bk_downsweep_step(data, n, total_levels, (k - 1) as nat);
        }
    }
}

/// Brent-Kung result equals inclusive_scan at all positions.
///
/// After total_levels - 1 down-sweep levels, threshold = pow2(0) = 1 divides all (j+1),
/// so every position holds sum(data, 0, j+1) = inclusive_scan(data)[j].
pub proof fn lemma_bk_correct(data: Seq<int>, n: nat, total_levels: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
    ensures
        bk_result(data, n, total_levels).len() == n,
        forall|j: int| 0 <= j < n as int ==>
            #[trigger] bk_result(data, n, total_levels)[j]
                == inclusive_scan::<int>(data)[j],
{
    lemma_bk_invariant_all(data, n, total_levels, (total_levels - 1) as nat);
    let result = bk_result(data, n, total_levels);

    assert forall|j: int| 0 <= j < n as int
    implies #[trigger] result[j] == inclusive_scan::<int>(data)[j]
    by {
        let threshold = pow2((total_levels - (total_levels - 1) as nat - 1) as nat);
        assert(threshold == pow2(0));
        assert(threshold == 1nat);
        assert((j + 1) % (threshold as int) == 0);
        assert(result[j] == bk_expected(data, n, total_levels, (total_levels - 1) as nat, j));
        assert(bk_expected(data, n, total_levels, (total_levels - 1) as nat, j)
            == sum::<int>(|i: int| data[i], 0, j + 1));
    }
}

} // verus!
