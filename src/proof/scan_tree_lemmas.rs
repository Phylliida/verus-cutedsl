/// Correctness proofs for tree reduce and Hillis-Steele scan.
///
/// Tree reduce: induction on levels. At each level, active positions combine
/// two pow2(d-1)-sized sums into one pow2(d)-sized sum via lemma_sum_split.
///
/// Hillis-Steele: induction on levels. Each element adds a contiguous range
/// from the previous level, extending its prefix sum.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_tree::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;

verus! {

// ============================================================
// Tree reduce correctness
// ============================================================

/// Tree reduce invariant holds at level 0 (base case).
pub proof fn lemma_tree_reduce_base(data: Seq<int>, n: nat)
    requires n == data.len(), n > 0,
    ensures tree_reduce_invariant(data, n, 0),
{
    let state = tree_reduce_state(data, n, 0);
    assert(state =~= data);
    assert forall|i: int| 0 <= i < n as int && (i + 1) % (pow2(0) as int) == 0
    implies #[trigger] state[i] == sum::<int>(|j: int| data[j], i + 1 - pow2(0) as int, i + 1)
    by {
        // pow2(0) = 1, so (i+1) % 1 == 0 always, and sum(f, i, i+1) = f(i) = data[i]
        lemma_sum_single::<int>(|j: int| data[j], i);
    }
}

/// Tree reduce invariant: inductive step.
/// If invariant holds at level d, it holds at level d+1.
pub proof fn lemma_tree_reduce_step(data: Seq<int>, n: nat, level: nat)
    requires
        n == data.len(),
        n > 0,
        is_power_of_2(n),
        level < log2_ceil(n),
        tree_reduce_invariant(data, n, level),
    ensures tree_reduce_invariant(data, n, level + 1),
{
    let prev = tree_reduce_state(data, n, level);
    let next = tree_reduce_state(data, n, level + 1);
    let stride = pow2(level);
    let new_stride = pow2(level + 1);
    let f = |j: int| data[j];

    // pow2(level + 1) = 2 * pow2(level)
    assert(pow2((level + 1) as nat) == 2 * pow2(level));

    assert forall|i: int| 0 <= i < n as int && (i + 1) % (new_stride as int) == 0
    implies #[trigger] next[i] == sum::<int>(f, i + 1 - new_stride as int, i + 1)
    by {
        // i is active at level+1: (i+1) % pow2(level+1) == 0
        // This means (i+1) % (2 * stride) == 0, so (i+1) % stride == 0
        // and i - stride >= 0 (since i+1 >= 2*stride, so i >= 2*stride - 1 >= stride)

        // i was active at level d: prev[i] = sum(f, i+1-stride, i+1)
        crate::proof::swizzle_lemmas::lemma_pow2_positive(level);
        assert((i + 1) % (stride as int) == 0) by {
            // (i+1) % (2*stride) == 0 implies 2*stride divides (i+1)
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, new_stride as int);
            let q = (i + 1) / (new_stride as int);
            assert(i + 1 == new_stride as int * q);
            assert(i + 1 == stride as int * (2 * q)) by(nonlinear_arith)
                requires i + 1 == 2 * stride as int * q, new_stride == 2 * stride;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                i + 1, stride as int, 2 * q, 0
            );
        };

        // i + 1 is a positive multiple of new_stride = 2*stride
        crate::proof::swizzle_lemmas::lemma_pow2_positive((level + 1) as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, new_stride as int);
        let q_ns = (i + 1) / (new_stride as int);
        assert(i + 1 == new_stride as int * q_ns);
        assert(q_ns >= 1 && i + 1 >= new_stride as int) by(nonlinear_arith)
            requires i + 1 >= 1, i + 1 == new_stride as int * q_ns, new_stride > 0nat;
        assert(i >= stride as int) by {
            assert(new_stride == 2 * stride);
        };
        assert(((i - stride as int) + 1) % (stride as int) == 0) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, stride as int);
            let q = (i + 1) / (stride as int);
            assert(i + 1 == stride as int * q);
            assert(i + 1 - stride as int == stride as int * (q - 1)) by(nonlinear_arith)
                requires i + 1 == stride as int * q;
            assert(q >= 2) by(nonlinear_arith)
                requires i + 1 == stride as int * q, i >= stride as int, stride > 0nat;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                i + 1 - stride as int, stride as int, q - 1, 0
            );
        };

        // By IH: prev[i] = sum(f, i+1-stride, i+1)
        //         prev[i-stride] = sum(f, i+1-2*stride, i+1-stride)
        let i_lo = i - stride as int;
        assert(0 <= i_lo && i_lo < n as int);
        assert(prev[i] == sum::<int>(f, i + 1 - stride as int, i + 1));
        assert(prev[i_lo] == sum::<int>(f, i_lo + 1 - stride as int, i_lo + 1));
        assert(i_lo + 1 - stride as int == i + 1 - new_stride as int);
        assert(i_lo + 1 == i + 1 - stride as int);

        // next[i] = prev[i] + prev[i - stride]
        //         = sum(f, i+1-stride, i+1) + sum(f, i+1-2*stride, i+1-stride)
        // By sum_split: sum(f, i+1-2*stride, i+1) = sum(f, i+1-2*stride, i+1-stride) + sum(f, i+1-stride, i+1)
        assert(i + 1 - new_stride as int >= 0);
        lemma_sum_split::<int>(f, i + 1 - new_stride as int, i + 1 - stride as int, i + 1);
        // sum(f, i+1-new_stride, i+1).eqv(sum(f, i+1-new_stride, i+1-stride) + sum(f, i+1-stride, i+1))
        // For int, .eqv() is ==, so:
        // sum(f, i+1-new_stride, i+1) == sum(f, i+1-new_stride, i+1-stride) + sum(f, i+1-stride, i+1)
        // = prev[i-stride] + prev[i] = next[i]
    }
}

// ============================================================
// Hillis-Steele correctness
// ============================================================

/// Hillis-Steele invariant holds at level 0 (base case).
pub proof fn lemma_hillis_steele_base(data: Seq<int>, n: nat)
    requires n == data.len(), n > 0,
    ensures hillis_steele_invariant(data, n, 0),
{
    let state = hillis_steele_state(data, n, 0);
    assert(state =~= data);
    assert forall|i: int| 0 <= i < n as int
    implies {
        let lo = if i + 1 - pow2(0) as int > 0 { i + 1 - pow2(0) as int } else { 0int };
        #[trigger] state[i] == sum::<int>(|j: int| data[j], lo, i + 1)
    }
    by {
        // pow2(0) = 1, so lo = max(0, i+1-1) = max(0, i) = i (since i >= 0)
        // sum(f, i, i+1) = f(i) = data[i]
        let lo = if i + 1 - 1 > 0 { i + 1 - 1 } else { 0int };
        assert(lo == i);
        lemma_sum_single::<int>(|j: int| data[j], i);
    }
}

/// Hillis-Steele invariant: inductive step.
pub proof fn lemma_hillis_steele_step(data: Seq<int>, n: nat, level: nat)
    requires
        n == data.len(),
        n > 0,
        hillis_steele_invariant(data, n, level),
    ensures hillis_steele_invariant(data, n, level + 1),
{
    let prev = hillis_steele_state(data, n, level);
    let next = hillis_steele_state(data, n, level + 1);
    let stride = pow2(level);
    let new_stride = pow2(level + 1);
    let f = |j: int| data[j];

    assert(pow2((level + 1) as nat) == 2 * pow2(level));

    assert forall|i: int| 0 <= i < n as int
    implies {
        let lo = if i + 1 - new_stride as int > 0 { i + 1 - new_stride as int } else { 0int };
        #[trigger] next[i] == sum::<int>(f, lo, i + 1)
    }
    by {
        let prev_lo = if i + 1 - stride as int > 0 { i + 1 - stride as int } else { 0int };
        let next_lo = if i + 1 - new_stride as int > 0 { i + 1 - new_stride as int } else { 0int };

        if i >= stride as int {
            // next[i] = prev[i] + prev[i - stride]
            // By IH: prev[i] = sum(f, prev_lo, i+1) where prev_lo = max(0, i+1-stride)
            //         prev[i-stride] = sum(f, partner_lo, i+1-stride)
            //           where partner_lo = max(0, i+1-stride - stride) = max(0, i+1-2*stride)
            let partner = (i - stride as int) as int;
            let partner_lo = if partner + 1 - stride as int > 0 { partner + 1 - stride as int } else { 0int };
            assert(0 <= partner && partner < n as int);

            // prev_lo = i + 1 - stride (since i >= stride, i+1-stride >= 1 > 0)
            assert(prev_lo == i + 1 - stride as int);
            // partner + 1 = i + 1 - stride
            // partner_lo = max(0, i + 1 - 2*stride) = max(0, i + 1 - new_stride) = next_lo
            assert(partner + 1 == i + 1 - stride as int);
            assert(partner_lo == next_lo);

            // By IH:
            assert(prev[i] == sum::<int>(f, prev_lo, i + 1));
            assert(prev[partner] == sum::<int>(f, partner_lo, partner + 1));
            // partner + 1 == prev_lo
            assert(partner + 1 == prev_lo);

            // next[i] = prev[i] + prev[partner]
            //         = sum(f, prev_lo, i+1) + sum(f, next_lo, prev_lo)
            // By sum_split: sum(f, next_lo, i+1) = sum(f, next_lo, prev_lo) + sum(f, prev_lo, i+1)
            assert(next_lo <= prev_lo);
            lemma_sum_split::<int>(f, next_lo, prev_lo, i + 1);
            // sum(f, next_lo, i+1) == sum(f, next_lo, prev_lo) + sum(f, prev_lo, i+1)
            // = prev[partner] + prev[i] = next[i]
        } else {
            // i < stride: next[i] = prev[i] = sum(f, prev_lo, i+1)
            // next_lo = max(0, i+1-2*stride)
            // Since i < stride, i+1 <= stride, so i+1-2*stride <= -stride < 0, so next_lo = 0
            // And prev_lo = max(0, i+1-stride)
            // Since i < stride, i+1 <= stride, so i+1-stride <= 0, so prev_lo = 0
            // So next_lo = prev_lo = 0, and next[i] = prev[i] = sum(f, 0, i+1). Same.
            assert(next_lo == 0);
            assert(prev_lo == 0);
        }
    }
}

/// Hillis-Steele after log2_ceil(n) levels equals inclusive_scan.
pub proof fn lemma_hillis_steele_correct(data: Seq<int>, n: nat, levels: nat)
    requires
        n == data.len(),
        n > 0,
        pow2(levels) >= n,
        hillis_steele_invariant(data, n, levels),
    ensures
        forall|i: int| 0 <= i < n as int
            ==> hillis_steele_state(data, n, levels)[i]
                == sum::<int>(|j: int| data[j], 0, i + 1),
{
    // When pow2(levels) >= n, for all i < n:
    // lo = max(0, i+1-pow2(levels)) = 0 (since i+1 <= n <= pow2(levels))
    let state = hillis_steele_state(data, n, levels);
    assert forall|i: int| 0 <= i < n as int
    implies hillis_steele_state(data, n, levels)[i]
        == sum::<int>(|j: int| data[j], 0, i + 1)
    by {
        let lo = if i + 1 - pow2(levels) as int > 0 { i + 1 - pow2(levels) as int } else { 0int };
        assert(lo == 0);
    }
}

/// Hillis-Steele invariant holds at all levels up to `level` (by induction).
pub proof fn lemma_hillis_steele_invariant_upto(data: Seq<int>, n: nat, level: nat)
    requires n == data.len(), n > 0,
    ensures hillis_steele_invariant(data, n, level),
    decreases level,
{
    if level == 0 {
        lemma_hillis_steele_base(data, n);
    } else {
        lemma_hillis_steele_invariant_upto(data, n, (level - 1) as nat);
        lemma_hillis_steele_step(data, n, (level - 1) as nat);
    }
}

/// Master theorem: Hillis-Steele after log2_ceil(n) levels produces inclusive_scan.
pub proof fn lemma_hillis_steele_full(data: Seq<int>, n: nat)
    requires n == data.len(), n > 0,
    ensures
        forall|i: int| 0 <= i < n as int
            ==> hillis_steele_state(data, n, log2_ceil(n))[i]
                == sum::<int>(|j: int| data[j], 0, i + 1),
{
    let levels = log2_ceil(n);
    lemma_hillis_steele_invariant_upto(data, n, levels);
    lemma_log2_ceil_pow2(n);
    lemma_hillis_steele_correct(data, n, levels);
}

} // verus!
