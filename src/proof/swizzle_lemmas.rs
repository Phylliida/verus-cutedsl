use vstd::prelude::*;
use crate::swizzle::*;

verus! {

// ══════════════════════════════════════════════════════════════
// XOR properties
// ══════════════════════════════════════════════════════════════

/// XOR with 0 is identity: a XOR 0 == a
pub proof fn lemma_bxor_zero(a: nat)
    ensures bxor(a, 0) == a,
    decreases a,
{
    if a > 0 {
        lemma_bxor_zero(a / 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, 2);
    }
}

/// XOR cancel: (a XOR b) XOR b == a.
/// This is the key property for swizzle involution.
pub proof fn lemma_bxor_cancel(a: nat, b: nat)
    ensures bxor(bxor(a, b), b) == a,
    decreases a + b,
{
    if a == 0 && b == 0 {
    } else {
        let ab = bxor(a, b);
        let a0 = a % 2;
        let b0 = b % 2;

        // Establish ab's bit structure for the recursive step
        if a0 == b0 {
            assert(ab == 2 * bxor(a / 2, b / 2));
        } else {
            assert(ab == 1 + 2 * bxor(a / 2, b / 2));
        }

        lemma_bxor_cancel(a / 2, b / 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, 2);
    }
}

/// XOR is commutative: a XOR b == b XOR a
pub proof fn lemma_bxor_commutative(a: nat, b: nat)
    ensures bxor(a, b) == bxor(b, a),
    decreases a + b,
{
    if a == 0 && b == 0 {
    } else {
        lemma_bxor_commutative(a / 2, b / 2);
    }
}

// ══════════════════════════════════════════════════════════════
// pow2 helpers
// ══════════════════════════════════════════════════════════════

/// pow2 is always positive.
pub proof fn lemma_pow2_positive(n: nat)
    ensures pow2(n) > 0,
    decreases n,
{
    if n > 0 {
        lemma_pow2_positive((n - 1) as nat);
    }
}

// ══════════════════════════════════════════════════════════════
// Bit-level helpers for non-overlapping window proof
// ══════════════════════════════════════════════════════════════

/// XOR with a value < 2^n doesn't change bits at or above position n.
/// Formally: if b < 2^n, then shr(bxor(a, b), n) == shr(a, n).
proof fn lemma_bxor_preserves_high_bits(a: nat, b: nat, n: nat)
    requires b < pow2(n),
    ensures shr(bxor(a, b), n) == shr(a, n),
    decreases n,
{
    lemma_pow2_positive(n);
    if n == 0 {
        // b < 1, so b == 0
        assert(b == 0);
        lemma_bxor_zero(a);
    } else {
        // b < 2 * pow2(n-1)
        // b/2 < pow2(n-1)
        let n1 = (n - 1) as nat;
        lemma_pow2_positive(n1);

        let ab = bxor(a, b);
        let a0 = a % 2;
        let b0 = b % 2;

        // ab / 2 == bxor(a/2, b/2) by definition of bxor
        if a0 == b0 {
            assert(ab == 2 * bxor(a / 2, b / 2));
        } else {
            assert(ab == 1 + 2 * bxor(a / 2, b / 2));
        }

        // b/2 < pow2(n-1) because b < 2*pow2(n-1)
        assert(b / 2 < pow2(n1));

        lemma_bxor_preserves_high_bits(a / 2, b / 2, n1);
        // IH: shr(bxor(a/2, b/2), n1) == shr(a/2, n1)

        // shr(ab, n) = ab / pow2(n) = ab / (2 * pow2(n1))
        //            = (ab / 2) / pow2(n1)      (by iterated division)
        //            = bxor(a/2, b/2) / pow2(n1)
        //            = shr(bxor(a/2, b/2), n1)
        //            = shr(a/2, n1)              (by IH)
        //            = (a/2) / pow2(n1)
        //            = a / (2*pow2(n1))
        //            = a / pow2(n)
        //            = shr(a, n)

        // Need: pow2(n) == 2 * pow2(n1) and iterated division identity
        assert(pow2(n) == 2 * pow2(n1));

        // ab / 2 == bxor(a/2, b/2) in both cases
        assert(ab / 2 == bxor(a / 2, b / 2));

        // Iterated division: x / (2 * d) == (x / 2) / d for d > 0
        vstd::arithmetic::div_mod::lemma_div_denominator(ab as int, 2, pow2(n1) as int);
        vstd::arithmetic::div_mod::lemma_div_denominator(a as int, 2, pow2(n1) as int);
    }
}

/// shl(e, m) < pow2(m + b) when e < pow2(b).
/// i.e., e * 2^m < 2^(m+b) when e < 2^b.
pub proof fn lemma_shl_bound(e: nat, m: nat, b: nat)
    requires e < pow2(b),
    ensures shl(e, m) < pow2(m + b),
    decreases m,
{
    lemma_pow2_positive(b);
    lemma_pow2_positive(m);
    if m == 0 {
        assert(shl(e, 0) == e * pow2(0));
        assert(pow2(0) == 1);
        vstd::arithmetic::mul::lemma_mul_basics(e as int);
        assert(pow2(0 + b) == pow2(b));
    } else {
        let m1 = (m - 1) as nat;
        lemma_shl_bound(e, m1, b);
        // IH: e * pow2(m1) < pow2(m1 + b)
        // Need: e * pow2(m) < pow2(m + b)
        // pow2(m) = 2 * pow2(m1), pow2(m+b) = 2 * pow2(m1+b)
        assert(pow2(m) == 2 * pow2(m1));
        assert(pow2(m + b) == 2 * pow2(m1 + b)) by {
            assert((m + b) - 1 == m1 + b);
            assert(pow2((m + b)) == 2 * pow2(((m + b) - 1) as nat));
        };
        // e * (2 * pow2(m1)) = 2 * (e * pow2(m1)) < 2 * pow2(m1 + b) = pow2(m + b)
        vstd::arithmetic::mul::lemma_mul_is_associative(e as int, 2, pow2(m1) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(e as int, 2);
        vstd::arithmetic::mul::lemma_mul_is_associative(2, e as int, pow2(m1) as int);
        // 2 * (e * pow2(m1)) < 2 * pow2(m1 + b)
        vstd::arithmetic::mul::lemma_mul_strict_inequality(
            (e * pow2(m1)) as int,
            pow2(m1 + b) as int,
            2,
        );
    }
}

/// band_mask preserves values: band_mask(x, b) < pow2(b).
pub proof fn lemma_band_mask_bound(x: nat, b: nat)
    ensures band_mask(x, b) < pow2(b),
{
    lemma_pow2_positive(b);
}

/// pow2 is monotone: a <= b implies pow2(a) <= pow2(b).
pub proof fn lemma_pow2_monotone(a: nat, b: nat)
    requires a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_pow2_monotone(a, (b - 1) as nat);
        // IH: pow2(a) <= pow2(b-1)
        // pow2(b) = 2 * pow2(b-1) >= pow2(b-1) >= pow2(a)
        assert(pow2(b) == 2 * pow2((b - 1) as nat));
        lemma_pow2_positive((b - 1) as nat);
    }
}

// ══════════════════════════════════════════════════════════════
// Swizzle involution
// ══════════════════════════════════════════════════════════════

/// Swizzle is its own inverse: swizzle(swizzle(x)) == x.
///
/// Proof sketch: Since S >= B, the source bits [M+S, M+S+B) and
/// destination bits [M, M+B) don't overlap. XOR only modifies
/// destination bits, so the source bits are unchanged in swizzle(x).
/// The second extraction gives the same value c, and
/// bxor(bxor(x, c), c) == x by XOR cancellation.
pub proof fn lemma_swizzle_involution(x: nat, b: nat, m: nat, s: nat)
    requires swizzle_admissible(b, m, s),
    ensures swizzle(swizzle(x, b, m, s), b, m, s) == x,
{
    let extracted = band_mask(shr(x, m + s), b);
    let shifted = shl(extracted, m);
    let sx = bxor(x, shifted);
    assert(sx == swizzle(x, b, m, s));

    // Second application: extract from sx
    let extracted2 = band_mask(shr(sx, m + s), b);
    let shifted2 = shl(extracted2, m);
    let ssx = bxor(sx, shifted2);
    assert(ssx == swizzle(sx, b, m, s));

    // Key: extracted2 == extracted because XOR only modifies bits [M, M+B)
    // and we extract from [M+S, M+S+B) where M+S >= M+B (since S >= B).

    // Step 1: shifted < pow2(m + b) because extracted < pow2(b)
    lemma_band_mask_bound(shr(x, m + s), b);
    assert(extracted < pow2(b));
    lemma_shl_bound(extracted, m, b);
    assert(shifted < pow2(m + b));

    // Step 2: Since s >= b, we have m + s >= m + b.
    // shifted < pow2(m + b) <= pow2(m + s).
    // So shr(bxor(x, shifted), m + s) == shr(x, m + s).
    lemma_pow2_monotone(m + b, m + s);
    assert(shifted < pow2(m + s));
    lemma_bxor_preserves_high_bits(x, shifted, m + s);
    assert(shr(sx, m + s) == shr(x, m + s));

    // Step 3: extracted2 = band_mask(shr(sx, m+s), b) = band_mask(shr(x, m+s), b) = extracted
    assert(extracted2 == extracted);

    // With extracted2 == extracted, shifted2 == shifted
    assert(shifted2 == shifted);

    // bxor(bxor(x, shifted), shifted) == x
    lemma_bxor_cancel(x, shifted);
}

/// Swizzle is a bijection: if swizzle(x) == swizzle(y) then x == y.
/// Follows immediately from involution.
pub proof fn lemma_swizzle_injective(x: nat, y: nat, b: nat, m: nat, s: nat)
    requires
        swizzle_admissible(b, m, s),
        swizzle(x, b, m, s) == swizzle(y, b, m, s),
    ensures x == y,
{
    lemma_swizzle_involution(x, b, m, s);
    lemma_swizzle_involution(y, b, m, s);
}

} // verus!
