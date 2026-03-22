/// Blelloch exclusive scan correctness proofs.
///
/// Proves that the Blelloch down-sweep produces the exclusive prefix sum.
/// Key structure:
/// - Base case (k=0): root set to 0 = sum(data, 0, 0)
/// - Inductive step: right positions combine prefix + up-sweep partner via sum_split;
///   left positions copy partner's prefix; unchanged positions keep up-sweep values.
/// - Final (k=total_levels): every position active, gives exclusive_scan.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_tree::*;
use crate::scan_blelloch::*;
use crate::swizzle::pow2;
use crate::proof::scan_tree_lemmas::*;
use crate::proof::swizzle_lemmas::*;

verus! {

// ============================================================
// Tree reduce helpers
// ============================================================

/// log2_ceil(pow2(k)) == k for any k.
pub proof fn lemma_log2_ceil_eq_for_pow2(n: nat, total_levels: nat)
    requires
        n > 0,
        pow2(total_levels) == n,
    ensures log2_ceil(n) == total_levels,
{
    // Direction 1: log2_ceil(n) <= total_levels
    crate::proof::scan_lemmas::lemma_log2_ceil_upper_bound(n, total_levels);
    // Direction 2: log2_ceil(n) >= total_levels
    // By contradiction: if log2_ceil(n) < total_levels, then
    // pow2(log2_ceil(n)+1) <= pow2(total_levels) = n (by monotonicity)
    // but pow2(log2_ceil(n)+1) = 2*pow2(log2_ceil(n)) >= 2n > n. Contradiction.
    crate::proof::scan_lemmas::lemma_log2_ceil_pow2(n);
    let k = log2_ceil(n);
    if k < total_levels {
        lemma_pow2_monotone((k + 1) as nat, total_levels);
        lemma_pow2_positive(k);
        assert(pow2((k + 1) as nat) == 2 * pow2(k));
        assert(false) by (nonlinear_arith)
            requires
                pow2((k + 1) as nat) as int <= pow2(total_levels) as int,
                pow2(k) as int >= n as int,
                pow2((k + 1) as nat) as int == 2 * pow2(k) as int,
                pow2(total_levels) == n,
                n > 0nat;
    }
}

/// Tree reduce invariant holds at any level up to total_levels.
pub proof fn lemma_tree_reduce_invariant_all(data: Seq<int>, n: nat, total_levels: nat, level: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        level <= total_levels,
    ensures tree_reduce_invariant(data, n, level),
    decreases level,
{
    lemma_log2_ceil_eq_for_pow2(n, total_levels);
    if level == 0 {
        lemma_tree_reduce_base(data, n);
    } else {
        lemma_tree_reduce_invariant_all(data, n, total_levels, (level - 1) as nat);
        lemma_tree_reduce_step(data, n, (level - 1) as nat);
    }
}

/// Non-active positions are stable across a range of tree_reduce levels.
pub proof fn lemma_tree_reduce_stable_range(data: Seq<int>, n: nat, start: nat, end_level: nat, i: int)
    requires
        n == data.len(),
        start <= end_level,
        0 <= i < n as int,
        forall|L: nat| start < L && L <= end_level ==> (i + 1) % (pow2(L) as int) != 0,
    ensures
        tree_reduce_state(data, n, end_level)[i] == tree_reduce_state(data, n, start)[i],
    decreases end_level - start,
{
    if start == end_level {
    } else {
        lemma_tree_reduce_stable_range(data, n, start, (end_level - 1) as nat, i);
        // At level end_level: (i+1) % pow2(end_level) != 0, so prev[i] passes through
    }
}

/// Value of tree_reduce_state at total_levels for a position whose exact
/// divisibility level is d (i.e., pow2(d) | (i+1) but pow2(d+1) ∤ (i+1)).
pub proof fn lemma_tree_reduce_value_at_exact_level(data: Seq<int>, n: nat, total_levels: nat, d: nat, i: int)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        0 <= i < n as int,
        d <= total_levels,
        (i + 1) % (pow2(d) as int) == 0,
        d < total_levels ==> (i + 1) % (pow2((d + 1) as nat) as int) != 0,
    ensures
        tree_reduce_state(data, n, total_levels)[i] == sum::<int>(|j: int| data[j], i + 1 - pow2(d) as int, i + 1),
{
    // Establish invariant at level d
    lemma_tree_reduce_invariant_all(data, n, total_levels, d);

    if d == total_levels {
        // Only position n-1: invariant says state[n-1] == sum(data, 0, n)
    } else {
        // d < total_levels: show stability from d to total_levels
        // For all L in (d, total_levels], (i+1) % pow2(L) != 0
        // by contrapositive of lemma_mod_pow2_weaken
        assert forall|L: nat| d < L && L <= total_levels
        implies (i + 1) % (pow2(L) as int) != 0
        by {
            if (i + 1) % (pow2(L) as int) == 0 {
                lemma_mod_pow2_weaken((i + 1) as nat, L, (d + 1) as nat);
            }
        };
        lemma_tree_reduce_stable_range(data, n, d, total_levels, i);
    }
}

// ============================================================
// Down-sweep base case
// ============================================================

/// Blelloch down-sweep invariant holds at k=0 (base case).
pub proof fn lemma_blelloch_base(data: Seq<int>, n: nat, total_levels: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
    ensures blelloch_downsweep_invariant(data, n, total_levels, 0),
{
    let state = blelloch_downsweep_state(data, n, total_levels, 0);
    let upsweep = tree_reduce_state(data, n, total_levels);

    assert(state.len() == n);

    assert forall|j: int| 0 <= j < n as int
    implies #[trigger] state[j] == blelloch_expected(data, n, total_levels, 0, j)
    by {
        let s = pow2(total_levels);
        if j == n as int - 1 {
            assert((j + 1) % (s as int) == 0) by {
                assert(j + 1 == n as int);
                assert(n as int == s as int);
            };
            lemma_sum_empty::<int>(|i: int| data[i], 0, 0);
        } else {
            assert((j + 1) % (s as int) != 0) by {
                assert(0 < j + 1 && j + 1 < n as int);
                assert(n as int == s as int);
                vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, s);
            };
        }
    }
}

// ============================================================
// Down-sweep inductive step helper
// ============================================================

/// Helper: in the else branch of blelloch_downsweep_state, (j+1) % stride != 0.
/// Proved by contradiction using the two negated if-conditions.
pub proof fn lemma_else_branch_not_divisible(j: int, stride: nat, s_prev: nat)
    requires
        j >= 0,
        stride > 0,
        s_prev == 2 * stride,
        // Negated right-active condition
        !((j + 1) % (2 * stride as int) == 0 && j >= stride as int),
        // Negated left-active condition
        !((j + 1) % (2 * stride as int) == stride as int),
    ensures (j + 1) % (stride as int) != 0,
{
    if (j + 1) % (stride as int) == 0 {
        // j+1 = stride * m for some m >= 1
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, stride as int);
        let m = (j + 1) / (stride as int);
        assert(j + 1 == stride as int * m);
        assert(m >= 1) by (nonlinear_arith)
            requires j + 1 == stride as int * m, j >= 0, stride > 0;

        // Decompose m into even/odd
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, 2);
        let q = m / 2;
        let r = m % 2;
        assert(m == 2 * q + r);

        if r == 0 {
            // m even: m >= 2 (since m >= 1 and even), so q >= 1
            assert(q >= 1) by (nonlinear_arith)
                requires m >= 1, m == 2 * q + r, r == 0;
            // j+1 = stride*2q = (2*stride)*q, so (j+1) % (2*stride) == 0
            assert(j + 1 == (2 * stride as int) * q) by (nonlinear_arith)
                requires j + 1 == stride as int * m, m == 2 * q, r == 0;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                j + 1, (2 * stride as int), q, 0
            );
            // (j+1) % (2*stride) == 0, so from negated right-active: j < stride
            // But j+1 = 2*stride*q >= 2*stride > stride, so j >= stride. Contradiction.
            assert(j >= stride as int) by (nonlinear_arith)
                requires j + 1 == (2 * stride as int) * q, q >= 1, stride > 0;
        } else {
            // m odd: j+1 = stride*(2q+1) = 2*stride*q + stride
            assert(j + 1 == (2 * stride as int) * q + stride as int) by (nonlinear_arith)
                requires j + 1 == stride as int * m, m == 2 * q + r, r == 1;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                j + 1, (2 * stride as int), q, stride as int
            );
            // (j+1) % (2*stride) == stride, contradicts negated left-active condition
        }
    }
}

// ============================================================
// Down-sweep inductive step
// ============================================================

/// Helper: RIGHT position in Blelloch down-sweep step.
proof fn lemma_blelloch_step_right(
    data: Seq<int>, n: nat, total_levels: nat, k: nat, j: int,
    stride: nat, s_prev: nat,
)
    requires
        n == data.len(), n > 0, is_power_of_2(n),
        pow2(total_levels) == n, total_levels > 0, k < total_levels,
        blelloch_downsweep_invariant(data, n, total_levels, k),
        stride == pow2((total_levels - k - 1) as nat),
        s_prev == pow2((total_levels - k) as nat),
        s_prev == 2 * stride, stride > 0, s_prev > 0,
        0 <= j < n as int,
        (j + 1) % (2 * stride as int) == 0, j >= stride as int,
    ensures
        blelloch_downsweep_state(data, n, total_levels, (k + 1) as nat)[j]
            == blelloch_expected(data, n, total_levels, (k + 1) as nat, j),
{
    let prev = blelloch_downsweep_state(data, n, total_levels, k);
    let f = |j: int| data[j];
    let new_s = pow2((total_levels - (k + 1) as nat) as nat);
    assert(new_s == stride);
    assert((j + 1) % (s_prev as int) == 0);
    assert(prev[j] == blelloch_expected(data, n, total_levels, k, j));
    assert(prev[j] == sum::<int>(f, 0, j + 1 - s_prev as int));
    let partner = j - stride as int;
    assert(0 <= partner && partner < n as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, s_prev as int);
    let q_right = (j + 1) / (s_prev as int);
    assert(j + 1 == s_prev as int * q_right);
    assert(q_right >= 1) by (nonlinear_arith)
        requires j + 1 == s_prev as int * q_right, j + 1 > 0, s_prev > 0;
    assert(partner + 1 == stride as int * (2 * q_right - 1)) by (nonlinear_arith)
        requires partner == j - stride as int, j + 1 == s_prev as int * q_right, s_prev == 2 * stride;
    let odd_factor = 2 * q_right - 1;
    assert(odd_factor >= 1) by (nonlinear_arith) requires q_right >= 1, odd_factor == 2 * q_right - 1;
    assert(partner + 1 == s_prev as int * (q_right - 1) + stride as int) by (nonlinear_arith)
        requires partner + 1 == stride as int * odd_factor, odd_factor == 2 * q_right - 1, s_prev == 2 * stride;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        partner + 1, s_prev as int, q_right - 1, stride as int
    );
    assert((partner + 1) % (s_prev as int) != 0) by (nonlinear_arith)
        requires (partner + 1) % (s_prev as int) == stride as int, stride > 0;
    assert(prev[partner] == blelloch_expected(data, n, total_levels, k, partner));
    assert(prev[partner] == tree_reduce_state(data, n, total_levels)[partner]);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        partner + 1, stride as int, odd_factor, 0
    );
    let d = (total_levels - k - 1) as nat;
    lemma_tree_reduce_value_at_exact_level(data, n, total_levels, d, partner);
    assert(partner + 1 - stride as int == j + 1 - s_prev as int) by (nonlinear_arith)
        requires partner == j - stride as int, s_prev == 2 * stride;
    assert(j + 1 - s_prev as int >= 0) by (nonlinear_arith)
        requires j + 1 == s_prev as int * q_right, q_right >= 1, s_prev > 0;
    lemma_sum_split::<int>(f, 0, j + 1 - s_prev as int, j + 1 - stride as int);
    assert((j + 1) % (new_s as int) == 0) by {
        lemma_mod_pow2_weaken((j + 1) as nat, (total_levels - k) as nat, (total_levels - k - 1) as nat);
    };
}

/// Helper: LEFT position in Blelloch down-sweep step.
proof fn lemma_blelloch_step_left(
    data: Seq<int>, n: nat, total_levels: nat, k: nat, j: int,
    stride: nat, s_prev: nat,
)
    requires
        n == data.len(), n > 0, is_power_of_2(n),
        pow2(total_levels) == n, total_levels > 0, k < total_levels,
        blelloch_downsweep_invariant(data, n, total_levels, k),
        stride == pow2((total_levels - k - 1) as nat),
        s_prev == pow2((total_levels - k) as nat),
        s_prev == 2 * stride, stride > 0, s_prev > 0,
        0 <= j < n as int,
        (j + 1) % (2 * stride as int) == stride as int,
    ensures
        blelloch_downsweep_state(data, n, total_levels, (k + 1) as nat)[j]
            == blelloch_expected(data, n, total_levels, (k + 1) as nat, j),
{
    let prev = blelloch_downsweep_state(data, n, total_levels, k);
    let f = |j: int| data[j];
    let partner_right = j + stride as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, (2 * stride as int));
    let q_left = (j + 1) / (2 * stride as int);
    assert(j + 1 == (2 * stride as int) * q_left + stride as int);
    assert(partner_right + 1 == (2 * stride as int) * (q_left + 1)) by (nonlinear_arith)
        requires partner_right == j + stride as int, j + 1 == (2 * stride as int) * q_left + stride as int;
    lemma_pow2_mul((total_levels - k) as nat, k);
    assert(n == s_prev * pow2(k)) by { assert((total_levels - k) as nat + k == total_levels); };
    assert(partner_right + 1 <= n as int) by (nonlinear_arith)
        requires
            j + 1 == (2 * stride as int) * q_left + stride as int,
            j + 1 <= n as int,
            partner_right + 1 == (2 * stride as int) * (q_left + 1),
            n == s_prev * pow2(k), s_prev == 2 * stride, stride > 0;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        partner_right + 1, s_prev as int, q_left + 1, 0
    );
    assert(prev[partner_right] == blelloch_expected(data, n, total_levels, k, partner_right));
    assert(prev[partner_right] == sum::<int>(f, 0, partner_right + 1 - s_prev as int));
    assert(partner_right + 1 - s_prev as int == j + 1 - stride as int) by (nonlinear_arith)
        requires partner_right == j + stride as int, s_prev == 2 * stride;
    assert((j + 1) % (stride as int) == 0) by {
        assert(j + 1 == stride as int * (2 * q_left + 1)) by (nonlinear_arith)
            requires j + 1 == (2 * stride as int) * q_left + stride as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            j + 1, stride as int, 2 * q_left + 1, 0
        );
    };
}

/// Helper: UNCHANGED position in Blelloch down-sweep step.
proof fn lemma_blelloch_step_unchanged(
    data: Seq<int>, n: nat, total_levels: nat, k: nat, j: int,
    stride: nat, s_prev: nat,
)
    requires
        n == data.len(), n > 0, is_power_of_2(n),
        pow2(total_levels) == n, total_levels > 0, k < total_levels,
        blelloch_downsweep_invariant(data, n, total_levels, k),
        stride == pow2((total_levels - k - 1) as nat),
        s_prev == pow2((total_levels - k) as nat),
        s_prev == 2 * stride, stride > 0, s_prev > 0,
        0 <= j < n as int,
        !((j + 1) % (2 * stride as int) == 0 && j >= stride as int),
        (j + 1) % (2 * stride as int) != stride as int,
    ensures
        blelloch_downsweep_state(data, n, total_levels, (k + 1) as nat)[j]
            == blelloch_expected(data, n, total_levels, (k + 1) as nat, j),
{
    let prev = blelloch_downsweep_state(data, n, total_levels, k);
    lemma_else_branch_not_divisible(j, stride, s_prev);
    assert((j + 1) % (s_prev as int) != 0) by {
        if (j + 1) % (s_prev as int) == 0 {
            lemma_mod_pow2_weaken((j + 1) as nat, (total_levels - k) as nat, (total_levels - k - 1) as nat);
        }
    };
    assert(prev[j] == blelloch_expected(data, n, total_levels, k, j));
    assert(prev[j] == tree_reduce_state(data, n, total_levels)[j]);
}

/// Blelloch down-sweep invariant: inductive step from k to k+1.
pub proof fn lemma_blelloch_step(data: Seq<int>, n: nat, total_levels: nat, k: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
        k < total_levels,
        blelloch_downsweep_invariant(data, n, total_levels, k),
    ensures blelloch_downsweep_invariant(data, n, total_levels, (k + 1) as nat),
{
    let prev = blelloch_downsweep_state(data, n, total_levels, k);
    let next = blelloch_downsweep_state(data, n, total_levels, (k + 1) as nat);
    let stride = pow2((total_levels - k - 1) as nat);
    let s_prev = pow2((total_levels - k) as nat);
    let f = |j: int| data[j];

    // Key relation: s_prev = 2 * stride
    assert(s_prev == 2 * stride) by {
        assert(pow2((total_levels - k) as nat) == 2 * pow2((total_levels - k - 1) as nat));
    };

    lemma_pow2_positive((total_levels - k - 1) as nat);
    lemma_pow2_positive((total_levels - k) as nat);

    assert(prev.len() == n);
    assert(next.len() == n);

    assert forall|j: int| 0 <= j < n as int
    implies #[trigger] next[j] == blelloch_expected(data, n, total_levels, (k + 1) as nat, j)
    by {
        if (j + 1) % (2 * stride as int) == 0 && j >= stride as int {
            lemma_blelloch_step_right(data, n, total_levels, k, j, stride, s_prev);
        } else if (j + 1) % (2 * stride as int) == stride as int {
            lemma_blelloch_step_left(data, n, total_levels, k, j, stride, s_prev);
        } else {
            lemma_blelloch_step_unchanged(data, n, total_levels, k, j, stride, s_prev);
        }
    }
}

// ============================================================
// Master invariant + correctness
// ============================================================

/// Blelloch down-sweep invariant holds at all levels 0..=total_levels.
pub proof fn lemma_blelloch_invariant_all(data: Seq<int>, n: nat, total_levels: nat, k: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
        k <= total_levels,
    ensures blelloch_downsweep_invariant(data, n, total_levels, k),
    decreases k,
{
    if k == 0 {
        lemma_blelloch_base(data, n, total_levels);
    } else {
        lemma_blelloch_invariant_all(data, n, total_levels, (k - 1) as nat);
        lemma_blelloch_step(data, n, total_levels, (k - 1) as nat);
    }
}

/// Blelloch result equals exclusive_scan at all positions.
///
/// After total_levels down-sweep levels, stride = pow2(0) = 1 divides all (j+1),
/// so every position holds sum(data, 0, j) = exclusive_scan(data)[j].
pub proof fn lemma_blelloch_correct(data: Seq<int>, n: nat, total_levels: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
    ensures
        blelloch_result(data, n, total_levels).len() == n,
        forall|j: int| 0 <= j < n as int ==>
            #[trigger] blelloch_result(data, n, total_levels)[j]
                == exclusive_scan::<int>(data)[j],
{
    lemma_blelloch_invariant_all(data, n, total_levels, total_levels);
    let result = blelloch_result(data, n, total_levels);
    let state = blelloch_downsweep_state(data, n, total_levels, total_levels);

    assert forall|j: int| 0 <= j < n as int
    implies #[trigger] result[j] == exclusive_scan::<int>(data)[j]
    by {
        let s = pow2((total_levels - total_levels) as nat);
        assert(s == pow2(0));
        assert(s == 1nat);
        assert((j + 1) % (s as int) == 0);
        assert(state[j] == blelloch_expected(data, n, total_levels, total_levels, j));
        assert(blelloch_expected(data, n, total_levels, total_levels, j) == sum::<int>(|i: int| data[i], 0, j));
    }
}

} // verus!
