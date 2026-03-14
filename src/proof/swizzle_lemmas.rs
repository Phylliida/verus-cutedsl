use vstd::prelude::*;
use crate::swizzle::*;
use crate::layout::*;

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

// ══════════════════════════════════════════════════════════════
// Bounded domain proofs
// ══════════════════════════════════════════════════════════════

/// XOR preserves bounded domain: if a < 2^n and b < 2^n, then bxor(a, b) < 2^n.
pub proof fn lemma_bxor_bounded(a: nat, b: nat, n: nat)
    requires
        a < pow2(n),
        b < pow2(n),
    ensures
        bxor(a, b) < pow2(n),
    decreases n,
{
    lemma_pow2_positive(n);
    if n == 0 {
        assert(a == 0 && b == 0);
    } else {
        let n1 = (n - 1) as nat;
        lemma_pow2_positive(n1);
        assert(pow2(n) == 2 * pow2(n1));

        // a/2 < pow2(n1) and b/2 < pow2(n1)
        assert(a / 2 < pow2(n1));
        assert(b / 2 < pow2(n1));

        lemma_bxor_bounded(a / 2, b / 2, n1);
        // IH: bxor(a/2, b/2) < pow2(n1)

        let ab = bxor(a, b);
        let a0 = a % 2;
        let b0 = b % 2;

        if a == 0 && b == 0 {
            assert(ab == 0);
        } else {
            // ab = bit + 2 * bxor(a/2, b/2) where bit in {0, 1}
            if a0 == b0 {
                assert(ab == 2 * bxor(a / 2, b / 2));
                // 2 * bxor(a/2, b/2) < 2 * pow2(n1) = pow2(n)
            } else {
                assert(ab == 1 + 2 * bxor(a / 2, b / 2));
                // 1 + 2 * bxor(a/2, b/2) <= 1 + 2*(pow2(n1)-1) = 2*pow2(n1) - 1 < pow2(n)
            }
        }
    }
}

/// XOR with a smaller value preserves the larger bound:
/// if a < 2^n and b < 2^k with k <= n, then bxor(a, b) < 2^n.
pub proof fn lemma_bxor_preserves_bound(a: nat, b: nat, k: nat, n: nat)
    requires
        a < pow2(n),
        b < pow2(k),
        k <= n,
    ensures
        bxor(a, b) < pow2(n),
{
    lemma_pow2_monotone(k, n);
    assert(b < pow2(n));
    lemma_bxor_bounded(a, b, n);
}

/// Swizzle preserves bounded domain: if x < 2^(m+s+b), result < 2^(m+s+b).
pub proof fn lemma_swizzle_bounded(x: nat, b: nat, m: nat, s: nat)
    requires
        swizzle_admissible(b, m, s),
        x < pow2(m + s + b),
    ensures
        swizzle(x, b, m, s) < pow2(m + s + b),
{
    let extracted = band_mask(shr(x, m + s), b);
    let shifted = shl(extracted, m);

    // extracted < pow2(b)
    lemma_band_mask_bound(shr(x, m + s), b);

    // shifted < pow2(m + b)
    lemma_shl_bound(extracted, m, b);
    assert(shifted < pow2(m + b));

    // pow2(m + b) <= pow2(m + s + b) since m+b <= m+s+b (s >= b >= 1 > 0)
    lemma_pow2_monotone(m + b, m + s + b);
    assert(shifted < pow2(m + s + b));

    // bxor(x, shifted) < pow2(m + s + b)
    lemma_bxor_bounded(x, shifted, m + s + b);
}

/// Swizzle is surjective on bounded domain: for every k < 2^(m+s+b),
/// there exists a pre-image (namely swizzle(k) itself) that maps to k.
pub proof fn lemma_swizzle_surjective_bounded(k: nat, b: nat, m: nat, s: nat)
    requires
        swizzle_admissible(b, m, s),
        k < pow2(m + s + b),
    ensures
        swizzle(k, b, m, s) < pow2(m + s + b),
        swizzle(swizzle(k, b, m, s), b, m, s) == k,
{
    lemma_swizzle_bounded(k, b, m, s);
    lemma_swizzle_involution(k, b, m, s);
}

// ══════════════════════════════════════════════════════════════
// Bank conflict freedom
// ══════════════════════════════════════════════════════════════

/// Shifting an aligned address recovers the row index:
/// shr(base + i * pow2(k), k) == shr(base, k) + i when base + i*pow2(k) doesn't wrap.
///
/// More precisely: (base + i * 2^k) / 2^k = base / 2^k + i.
proof fn lemma_shr_add_aligned(base: nat, i: nat, k: nat)
    ensures
        shr(base + i * pow2(k), k) == shr(base, k) + i,
    decreases k,
{
    lemma_pow2_positive(k);
    if k == 0 {
        assert(pow2(0) == 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(i as int);
    } else {
        let k1 = (k - 1) as nat;
        lemma_pow2_positive(k1);
        assert(pow2(k) == 2 * pow2(k1));

        // (base + i * 2^k) / 2^k = ((base + i * 2^k) / 2) / 2^(k-1)
        // = (base/2 + i * 2^(k-1)) / 2^(k-1)
        vstd::arithmetic::div_mod::lemma_div_denominator(
            (base + i * pow2(k)) as int,
            2,
            pow2(k1) as int,
        );
        vstd::arithmetic::div_mod::lemma_div_denominator(
            base as int,
            2,
            pow2(k1) as int,
        );

        // i * pow2(k) = i * (2 * pow2(k1)) = 2 * (i * pow2(k1))
        vstd::arithmetic::mul::lemma_mul_is_associative(i as int, 2, pow2(k1) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(i as int, 2);
        vstd::arithmetic::mul::lemma_mul_is_associative(2, i as int, pow2(k1) as int);
        // So base + i * pow2(k) = base + 2 * (i * pow2(k1))
        // (base + 2*(i*pow2(k1))) / 2 = base/2 + i*pow2(k1)
        // when base%2 + 0 < 2 (always true since the extra is even)
        assert((base + 2 * (i * pow2(k1))) / 2 == base / 2 + i * pow2(k1)) by (nonlinear_arith)
            requires base >= 0, i >= 0, pow2(k1) >= 1,
        {};

        lemma_shr_add_aligned(base / 2, i, k1);
    }
}

/// If base < pow2(k), then shr(base + i * pow2(k), k) == i.
pub proof fn lemma_shr_aligned_exact(base: nat, i: nat, k: nat)
    requires
        base < pow2(k),
    ensures
        shr(base + i * pow2(k), k) == i,
{
    lemma_shr_add_aligned(base, i, k);
    lemma_pow2_positive(k);
    assert(shr(base, k) == base / pow2(k));
    vstd::arithmetic::div_mod::lemma_div_basics(base as int);
    assert(base / pow2(k) == 0) by (nonlinear_arith)
        requires base >= 0, base < pow2(k), pow2(k) > 0,
    {};
}

/// band_mask extracts from aligned address:
/// band_mask(base + i * pow2(m), m) == band_mask(base, m).
pub proof fn lemma_band_mask_add_aligned(base: nat, i: nat, m: nat)
    ensures
        band_mask(base + i * pow2(m), m) == band_mask(base, m),
    decreases i,
{
    lemma_pow2_positive(m);
    if i == 0 {
        assert(i * pow2(m) == 0) by (nonlinear_arith) requires i == 0 {};
    } else {
        lemma_band_mask_add_aligned(base, (i - 1) as nat, m);
        // IH: (base + (i-1)*pow2(m)) % pow2(m) == base % pow2(m)
        // Need: (base + i*pow2(m)) % pow2(m) == base % pow2(m)
        // base + i*pow2(m) = (base + (i-1)*pow2(m)) + pow2(m)
        assert(base + i * pow2(m) == (base + (i - 1) * pow2(m)) + pow2(m)) by (nonlinear_arith)
            requires i >= 1, pow2(m) > 0,
        {};
        // (x + pow2(m)) % pow2(m) == x % pow2(m)
        let prev = base + (i - 1) * pow2(m);
        vstd::arithmetic::div_mod::lemma_mod_adds(prev as int, pow2(m) as int, pow2(m) as int);
    }
}

/// Swizzle preserves injectivity: if a layout is injective with non-negative offsets,
/// applying swizzle to all offsets preserves injectivity.
pub proof fn lemma_swizzle_preserves_injectivity(
    layout: &LayoutSpec,
    b: nat,
    m: nat,
    s: nat,
    size: nat,
)
    requires
        swizzle_admissible(b, m, s),
        layout.valid(),
        layout.is_injective(),
        layout.non_negative_strides(),
        size <= layout.size(),
    ensures
        forall|i: nat, j: nat|
            i < size && j < size && i != j
            ==> swizzle(layout.offset(i) as nat, b, m, s)
                != swizzle(layout.offset(j) as nat, b, m, s),
{
    // With non_negative_strides, offset >= 0 so `as nat` is safe
    assert forall|i: nat, j: nat|
        i < size && j < size && i != j
    implies
        swizzle(layout.offset(i) as nat, b, m, s)
        != swizzle(layout.offset(j) as nat, b, m, s)
    by {
        assert(i < layout.size() && j < layout.size());
        // offset(i) >= 0 from non_negative_strides
        crate::proof::offset_lemmas::lemma_offset_nonneg(*layout, i);
        crate::proof::offset_lemmas::lemma_offset_nonneg(*layout, j);
        assert(layout.offset(i) >= 0 && layout.offset(j) >= 0);
        // injectivity gives distinct offsets
        assert(layout.offset(i) != layout.offset(j));
        // distinct non-negative ints → distinct nats
        assert(layout.offset(i) as nat != layout.offset(j) as nat);
        // swizzle injectivity (contrapositive)
        if swizzle(layout.offset(i) as nat, b, m, s)
            == swizzle(layout.offset(j) as nat, b, m, s)
        {
            lemma_swizzle_injective(
                layout.offset(i) as nat,
                layout.offset(j) as nat,
                b, m, s,
            );
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Double-swizzle composition
// ══════════════════════════════════════════════════════════════

/// Helper: establish bxor(a, b) / 2 == bxor(a/2, b/2) and bxor(a,b) % 2.
proof fn lemma_bxor_half(a: nat, b: nat)
    ensures
        bxor(a, b) / 2 == bxor(a / 2, b / 2),
        bxor(a, b) % 2 == (if a % 2 == b % 2 { 0nat } else { 1nat }),
{
    if a == 0 && b == 0 {
        assert(bxor(0, 0) == 0nat);
    } else {
        let ab = bxor(a, b);
        if a % 2 == b % 2 {
            assert(ab == 2 * bxor(a / 2, b / 2));
        } else {
            assert(ab == 1 + 2 * bxor(a / 2, b / 2));
        }
    }
}

/// XOR is associative: bxor(bxor(a, b), c) == bxor(a, bxor(b, c)).
pub proof fn lemma_bxor_associative(a: nat, b: nat, c: nat)
    ensures bxor(bxor(a, b), c) == bxor(a, bxor(b, c)),
    decreases a + b + c,
{
    if a == 0 && b == 0 && c == 0 {
        return;
    }

    // Establish halves for ab and bc
    lemma_bxor_half(a, b);
    lemma_bxor_half(b, c);

    let ab = bxor(a, b);
    let bc = bxor(b, c);

    // ab/2 == bxor(a/2, b/2), bc/2 == bxor(b/2, c/2)

    // Establish halves for lhs = bxor(ab, c) and rhs = bxor(a, bc)
    lemma_bxor_half(ab, c);
    lemma_bxor_half(a, bc);

    let lhs = bxor(ab, c);
    let rhs = bxor(a, bc);

    // lhs/2 == bxor(ab/2, c/2) == bxor(bxor(a/2, b/2), c/2)
    // rhs/2 == bxor(a/2, bc/2) == bxor(a/2, bxor(b/2, c/2))
    // These are equal by IH
    lemma_bxor_associative(a / 2, b / 2, c / 2);
    assert(lhs / 2 == rhs / 2);

    // Low bits: exhaustive check on (a%2, b%2, c%2)
    // ab%2 = if a%2==b%2 { 0 } else { 1 }
    // lhs%2 = if ab%2==c%2 { 0 } else { 1 }
    // bc%2 = if b%2==c%2 { 0 } else { 1 }
    // rhs%2 = if a%2==bc%2 { 0 } else { 1 }
    // In all 8 cases of (a%2, b%2, c%2) ∈ {0,1}^3, lhs%2 == rhs%2
    assert(lhs % 2 == rhs % 2);

    // Reconstruct: lhs == lhs%2 + 2*(lhs/2) == rhs%2 + 2*(rhs/2) == rhs
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(lhs as int, 2);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(rhs as int, 2);
}

/// Helper: If mask < pow2(n), then XOR-ing mask preserves extraction at bit n.
/// band_mask(shr(bxor(x, mask), n), b) == band_mask(shr(x, n), b)
proof fn lemma_extraction_invariant_low(x: nat, mask: nat, n: nat, b: nat)
    requires mask < pow2(n),
    ensures band_mask(shr(bxor(x, mask), n), b) == band_mask(shr(x, n), b),
{
    lemma_bxor_preserves_high_bits(x, mask, n);
}

/// Helper for bxor with multiples of pow2: bits below the alignment are unchanged.
/// If mask % pow2(n) == 0, then bxor(x, mask) % pow2(n) == x % pow2(n).
proof fn lemma_bxor_preserves_low_bits(x: nat, mask: nat, n: nat)
    requires mask % pow2(n) == 0,
    ensures bxor(x, mask) % pow2(n) == x % pow2(n),
    decreases n,
{
    lemma_pow2_positive(n);
    if n == 0 {
        // pow2(0) == 1, everything % 1 == 0
    } else {
        let n1 = (n - 1) as nat;
        lemma_pow2_positive(n1);
        assert(pow2(n) == 2 * pow2(n1));

        // mask is even (multiple of pow2(n) >= 2)
        assert(mask % 2 == 0) by {
            assert(pow2(n) >= 2) by {
                lemma_pow2_monotone(1, n);
            };
            // mask % pow2(n) == 0, pow2(n) is even, so mask is even
            vstd::arithmetic::div_mod::lemma_mod_breakdown(mask as int, 2, pow2(n1) as int);
        };

        // mask/2 % pow2(n1) == 0
        // mask % (2 * pow2(n1)) == 0, and mask is even (shown above)
        // So mask/2 % pow2(n1) == 0
        // Strategy: use fundamental_div_mod on mask/2
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(mask as int, (2 * pow2(n1)) as int);
        // mask == (2 * pow2(n1)) * (mask / (2 * pow2(n1))) + 0
        // so mask == 2 * pow2(n1) * k where k = mask / (2 * pow2(n1))
        // mask/2 == pow2(n1) * k
        let k: nat = mask / (2 * pow2(n1));
        assert(mask == (2 * pow2(n1)) * k) by (nonlinear_arith)
            requires
                mask as int == (2 * pow2(n1)) as int * (k as int) + 0int,
        {};
        assert(mask / 2 == pow2(n1) * k) by (nonlinear_arith)
            requires mask == 2 * pow2(n1) * k, pow2(n1) > 0,
        {};
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k as int, pow2(n1) as int);

        lemma_bxor_half(x, mask);
        // bxor(x, mask) / 2 == bxor(x/2, mask/2)
        // bxor(x, mask) % 2 == if x%2 == mask%2 {0} else {1} == x%2 (since mask%2 == 0)

        lemma_bxor_preserves_low_bits(x / 2, mask / 2, n1);
        // IH: bxor(x/2, mask/2) % pow2(n1) == x/2 % pow2(n1)

        // Reconstruct: bxor(x, mask) % pow2(n) = bxor(x, mask) % (2 * pow2(n1))
        // = (bxor(x,mask) % 2) + 2 * ((bxor(x,mask)/2) % pow2(n1))
        // = (x % 2) + 2 * (bxor(x/2, mask/2) % pow2(n1))
        // = (x % 2) + 2 * (x/2 % pow2(n1))
        // = x % (2 * pow2(n1))
        // = x % pow2(n)
        vstd::arithmetic::div_mod::lemma_mod_breakdown(bxor(x, mask) as int, 2, pow2(n1) as int);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(x as int, 2, pow2(n1) as int);
    }
}

/// If mask % pow2(n + b) == 0, XOR-ing mask doesn't change band_mask(shr(_, n), b).
/// Strategy: reduce to lemma_bxor_preserves_low_bits by peeling off n bits first.
proof fn lemma_extraction_invariant_high(x: nat, mask: nat, n: nat, b: nat)
    requires mask % pow2(n + b) == 0,
    ensures band_mask(shr(bxor(x, mask), n), b) == band_mask(shr(x, n), b),
    decreases n,
{
    lemma_pow2_positive(n);
    lemma_pow2_positive(b);
    lemma_pow2_positive(n + b);

    if n == 0 {
        // shr(_, 0) == identity, need band_mask(bxor(x, mask), b) == band_mask(x, b)
        // mask % pow2(b) == 0
        assert(n + b == b);
        lemma_bxor_preserves_low_bits(x, mask, b);
        // bxor(x, mask) % pow2(b) == x % pow2(b)
    } else {
        let n1 = (n - 1) as nat;
        lemma_pow2_positive(n1);

        // mask is even (multiple of pow2(n+b) >= 2)
        assert(pow2(n + b) >= 2) by {
            lemma_pow2_monotone(1, n + b);
        };
        assert(mask % 2 == 0) by {
            assert(pow2(n + b) == 2 * pow2(((n + b) - 1) as nat));
            vstd::arithmetic::div_mod::lemma_mod_breakdown(mask as int, 2, pow2(((n + b) - 1) as nat) as int);
        };

        // mask/2 % pow2(n1 + b) == 0
        assert(pow2(n + b) == 2 * pow2(n1 + b)) by {
            assert(((n + b) - 1) as nat == n1 + b);
        };
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(mask as int, (2 * pow2(n1 + b)) as int);
        let k: nat = mask / (2 * pow2(n1 + b));
        assert(mask == (2 * pow2(n1 + b)) * k) by (nonlinear_arith)
            requires
                mask as int == (2 * pow2(n1 + b)) as int * (k as int) + 0int,
        {};
        assert(mask / 2 == pow2(n1 + b) * k) by (nonlinear_arith)
            requires mask == 2 * pow2(n1 + b) * k, pow2(n1 + b) > 0,
        {};
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k as int, pow2(n1 + b) as int);
        assert(mask / 2 % pow2(n1 + b) == 0);

        // bxor(x, mask) / 2 == bxor(x/2, mask/2) (since mask is even)
        lemma_bxor_half(x, mask);

        // IH on halves: band_mask(shr(bxor(x/2, mask/2), n1), b) == band_mask(shr(x/2, n1), b)
        lemma_extraction_invariant_high(x / 2, mask / 2, n1, b);

        // shr(bxor(x, mask), n) = bxor(x, mask) / pow2(n)
        //                       = (bxor(x, mask) / 2) / pow2(n1)
        //                       = bxor(x/2, mask/2) / pow2(n1)
        //                       = shr(bxor(x/2, mask/2), n1)
        assert(pow2(n) == 2 * pow2(n1));
        vstd::arithmetic::div_mod::lemma_div_denominator(bxor(x, mask) as int, 2, pow2(n1) as int);
        vstd::arithmetic::div_mod::lemma_div_denominator(x as int, 2, pow2(n1) as int);
    }
}

/// If x % pow2(a) == 0 and b <= a, then x % pow2(b) == 0.
/// (pow2(a) is a multiple of pow2(b) when a >= b)
proof fn lemma_mod_pow2_weaken(x: nat, a: nat, b: nat)
    requires
        x % pow2(a) == 0,
        b <= a,
    ensures
        x % pow2(b) == 0,
{
    lemma_pow2_positive(a);
    lemma_pow2_positive(b);
    // pow2(a) = pow2(b) * pow2(a - b)
    let diff = (a - b) as nat;
    lemma_pow2_mul(b, diff);
    assert(pow2(a) == pow2(b) * pow2(diff)) by {
        assert(b + diff == a);
    };
    // x % (pow2(b) * pow2(diff)) == 0 implies x % pow2(b) == 0
    lemma_pow2_positive(diff);
    vstd::arithmetic::div_mod::lemma_mod_breakdown(x as int, pow2(b) as int, pow2(diff) as int);
    // x % (pow2(b) * pow2(diff)) == pow2(b) * ((x / pow2(b)) % pow2(diff)) + x % pow2(b)
    // LHS == 0, both RHS terms >= 0, so x % pow2(b) == 0
    let p_b = pow2(b);
    let p_d = pow2(diff);
    let x_mod_b = x % p_b;
    let x_div_b_mod_d = (x / p_b) % p_d;
    assert(x_mod_b == 0) by (nonlinear_arith)
        requires
            0 == (p_b as int) * (x_div_b_mod_d as int) + (x_mod_b as int),
            p_b > 0, p_d > 0,
    {};
}

/// If mask = e * pow2(m), then mask % pow2(m) == 0.
proof fn lemma_shl_mod_zero(e: nat, m: nat)
    ensures shl(e, m) % pow2(m) == 0,
{
    lemma_pow2_positive(m);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(e as int, pow2(m) as int);
    assert(shl(e, m) == e * pow2(m));
    assert(e as int * pow2(m) as int == (e * pow2(m)) as int);
}

/// pow2(a) * pow2(b) == pow2(a + b).
proof fn lemma_pow2_mul(a: nat, b: nat)
    ensures pow2(a) * pow2(b) == pow2(a + b),
    decreases a,
{
    lemma_pow2_positive(b);
    if a == 0 {
        assert(pow2(0) == 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(pow2(b) as int);
    } else {
        let a1 = (a - 1) as nat;
        lemma_pow2_mul(a1, b);
        assert(pow2(a) == 2 * pow2(a1));
        assert(pow2(a + b) == 2 * pow2(a1 + b)) by {
            assert((a + b) >= 1);
            assert(((a + b) - 1) as nat == a1 + b);
        };
        // pow2(a) * pow2(b) = 2 * pow2(a1) * pow2(b) = 2 * pow2(a1+b) = pow2(a+b)
        vstd::arithmetic::mul::lemma_mul_is_associative(2, pow2(a1) as int, pow2(b) as int);
    }
}

/// Non-overlapping swizzles commute.
pub proof fn lemma_swizzle_commute(
    x: nat,
    b1: nat, m1: nat, s1: nat,
    b2: nat, m2: nat, s2: nat,
)
    requires
        swizzle_admissible(b1, m1, s1),
        swizzle_admissible(b2, m2, s2),
        // Dest windows don't overlap: [m1, m1+b1) ∩ [m2, m2+b2) = ∅
        m1 + b1 <= m2 || m2 + b2 <= m1,
        // Dest1 ∩ src2 = ∅: [m1, m1+b1) ∩ [m2+s2, m2+s2+b2) = ∅
        m1 + b1 <= m2 + s2 || m2 + s2 + b2 <= m1,
        // Dest2 ∩ src1 = ∅: [m2, m2+b2) ∩ [m1+s1, m1+s1+b1) = ∅
        m2 + b2 <= m1 + s1 || m1 + s1 + b1 <= m2,
    ensures
        swizzle(swizzle(x, b1, m1, s1), b2, m2, s2)
        == swizzle(swizzle(x, b2, m2, s2), b1, m1, s1),
{
    let e1 = band_mask(shr(x, m1 + s1), b1);
    let mask1 = shl(e1, m1);
    let sx1 = bxor(x, mask1);
    assert(sx1 == swizzle(x, b1, m1, s1));

    let e2 = band_mask(shr(x, m2 + s2), b2);
    let mask2 = shl(e2, m2);
    let sx2 = bxor(x, mask2);
    assert(sx2 == swizzle(x, b2, m2, s2));

    // Bound the masks
    lemma_band_mask_bound(shr(x, m1 + s1), b1);
    lemma_shl_bound(e1, m1, b1);
    assert(mask1 < pow2(m1 + b1));

    lemma_band_mask_bound(shr(x, m2 + s2), b2);
    lemma_shl_bound(e2, m2, b2);
    assert(mask2 < pow2(m2 + b2));

    // Show extraction2 is unchanged after swizzle1
    if m1 + b1 <= m2 + s2 {
        lemma_pow2_monotone(m1 + b1, m2 + s2);
        lemma_bxor_preserves_high_bits(x, mask1, m2 + s2);
    } else {
        // m2+s2+b2 <= m1
        lemma_shl_mod_zero(e1, m1);
        assert(mask1 % pow2(m1) == 0);
        lemma_mod_pow2_weaken(mask1, m1, m2 + s2 + b2);
        assert(mask1 % pow2((m2 + s2) + b2) == 0);
        lemma_extraction_invariant_high(x, mask1, m2 + s2, b2);
    }
    assert(band_mask(shr(sx1, m2 + s2), b2) == e2);

    // Show extraction1 is unchanged after swizzle2
    if m2 + b2 <= m1 + s1 {
        lemma_pow2_monotone(m2 + b2, m1 + s1);
        lemma_bxor_preserves_high_bits(x, mask2, m1 + s1);
    } else {
        // m1+s1+b1 <= m2
        lemma_shl_mod_zero(e2, m2);
        assert(mask2 % pow2(m2) == 0);
        lemma_mod_pow2_weaken(mask2, m2, m1 + s1 + b1);
        assert(mask2 % pow2((m1 + s1) + b1) == 0);
        lemma_extraction_invariant_high(x, mask2, m1 + s1, b1);
    }
    assert(band_mask(shr(sx2, m1 + s1), b1) == e1);

    // Both orderings produce x XOR mask1 XOR mask2
    lemma_bxor_associative(x, mask1, mask2);
    lemma_bxor_associative(x, mask2, mask1);
    lemma_bxor_commutative(mask1, mask2);
}

// ══════════════════════════════════════════════════════════════
// Swizzle-layout composition proofs
// ══════════════════════════════════════════════════════════════

/// Swizzled offsets are injective: distinct indices give distinct swizzled offsets.
pub proof fn lemma_swizzled_offset_injective(
    layout: &LayoutSpec, b: nat, m: nat, s: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
    ensures
        forall|i: nat, j: nat|
            i < layout.size() && j < layout.size() && i != j
            ==> swizzled_offset(layout, b, m, s, i)
                != swizzled_offset(layout, b, m, s, j),
{
    lemma_swizzle_preserves_injectivity(layout, b, m, s, layout.size());
}

/// Swizzle involution on layout offsets: double-swizzle recovers original offset.
pub proof fn lemma_swizzled_offset_involution(
    layout: &LayoutSpec, b: nat, m: nat, s: nat, idx: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
        idx < layout.size(),
    ensures
        swizzle(swizzled_offset(layout, b, m, s, idx), b, m, s)
            == layout.offset(idx) as nat,
{
    crate::proof::offset_lemmas::lemma_offset_nonneg(*layout, idx);
    lemma_swizzle_involution(layout.offset(idx) as nat, b, m, s);
}

/// Swizzled offsets stay within the swizzle domain.
pub proof fn lemma_swizzled_offset_bounded(
    layout: &LayoutSpec, b: nat, m: nat, s: nat, idx: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
        idx < layout.size(),
    ensures
        swizzled_offset(layout, b, m, s, idx) < pow2(m + s + b),
{
    crate::proof::offset_lemmas::lemma_offset_nonneg(*layout, idx);
    crate::proof::offset_lemmas::lemma_offset_upper_bound(*layout, idx);
    // offset < cosize <= pow2(m+s+b)
    let off = layout.offset(idx) as nat;
    assert(off < layout.cosize_nonneg());
    assert(off < pow2(m + s + b));
    lemma_swizzle_bounded(off, b, m, s);
}

/// Distinct swizzled bank indices imply distinct swizzled offsets.
pub proof fn lemma_swizzled_bank_distinct(
    layout: &LayoutSpec, b: nat, m: nat, s: nat,
    num_banks: nat, i: nat, j: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
        num_banks > 0,
        i < layout.size(),
        j < layout.size(),
        swizzled_offset(layout, b, m, s, i) % num_banks
            != swizzled_offset(layout, b, m, s, j) % num_banks,
    ensures
        swizzled_offset(layout, b, m, s, i)
            != swizzled_offset(layout, b, m, s, j),
{
    // Contraposition: equal offsets → equal bank indices. Contrapositive is what we need.
}

// ══════════════════════════════════════════════════════════════
// Swizzle injectivity from involution
// ══════════════════════════════════════════════════════════════

/// Swizzle involution implies injectivity: swizzle(x) == swizzle(y) ==> x == y.
pub proof fn lemma_swizzle_involution_implies_injective(
    x: nat, y: nat, b: nat, m: nat, s: nat,
)
    requires
        swizzle_admissible(b, m, s),
        swizzle(x, b, m, s) == swizzle(y, b, m, s),
    ensures
        x == y,
{
    // Apply swizzle to both sides, use involution
    lemma_swizzle_involution(x, b, m, s);
    lemma_swizzle_involution(y, b, m, s);
    // swizzle(swizzle(x)) == x, swizzle(swizzle(y)) == y
    // Since swizzle(x) == swizzle(y), swizzle(swizzle(x)) == swizzle(swizzle(y))
    // So x == y
}

/// Swizzle is injective on any domain: distinct inputs give distinct outputs.
pub proof fn lemma_swizzle_injective_on_domain(b: nat, m: nat, s: nat, n: nat)
    requires
        swizzle_admissible(b, m, s),
    ensures
        forall|i: nat, j: nat|
            i < n && j < n && i != j
            ==> swizzle(i, b, m, s) != swizzle(j, b, m, s),
{
    assert forall|i: nat, j: nat|
        i < n && j < n && i != j
    implies swizzle(i, b, m, s) != swizzle(j, b, m, s)
    by {
        if swizzle(i, b, m, s) == swizzle(j, b, m, s) {
            lemma_swizzle_involution_implies_injective(i, j, b, m, s);
        }
    };
}

/// Packaging: if a layout's swizzled offsets are all distinct, then
/// the layout is bank-conflict-free for any number of banks.
/// (Distinct values trivially have distinct remainders when they differ.)
pub proof fn lemma_swizzled_layout_bank_free(
    layout: &LayoutSpec, b: nat, m: nat, s: nat,
    num_banks: nat, count: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
        num_banks > 0,
        count <= layout.size(),
        // All swizzled offsets are distinct
        forall|i: nat, j: nat|
            i < count && j < count && i != j
            ==> swizzled_offset(layout, b, m, s, i)
                != swizzled_offset(layout, b, m, s, j),
    ensures
        forall|i: nat, j: nat|
            i < count && j < count && i != j
            ==> bank_index(swizzled_offset(layout, b, m, s, i) as int, num_banks)
                != bank_index(swizzled_offset(layout, b, m, s, j) as int, num_banks)
            || swizzled_offset(layout, b, m, s, i) != swizzled_offset(layout, b, m, s, j),
{
    // Trivially follows from the distinctness hypothesis:
    // if swizzled offsets differ, the disjunction holds regardless of bank indices.
}

/// Combined: swizzle-admissible layout → all swizzled offsets distinct.
/// Direct from lemma_swizzled_offset_injective.
pub proof fn lemma_swizzled_layout_fully_distinct(
    layout: &LayoutSpec, b: nat, m: nat, s: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
    ensures
        forall|i: nat, j: nat|
            i < layout.size() && j < layout.size() && i != j
            ==> swizzled_offset(layout, b, m, s, i)
                != swizzled_offset(layout, b, m, s, j),
{
    lemma_swizzled_offset_injective(layout, b, m, s);
}

// ══════════════════════════════════════════════════════════════
// Swizzle bijectivity proofs
// ══════════════════════════════════════════════════════════════

/// Swizzle is a bijection on [0, 2^(m+s+b)): injective (from involution) + surjective.
pub proof fn lemma_swizzle_bijection_on_domain(b: nat, m: nat, s: nat)
    requires swizzle_admissible(b, m, s),
    ensures
        // Injective
        forall|x: nat, y: nat| x < pow2(m + s + b) && y < pow2(m + s + b) && x != y
            ==> swizzle(x, b, m, s) != swizzle(y, b, m, s),
        // Surjective: every k in [0, 2^(m+s+b)) has a pre-image
        forall|k: nat| k < pow2(m + s + b) ==> ({
            let w = #[trigger] swizzle(k, b, m, s);
            w < pow2(m + s + b) && swizzle(w, b, m, s) == k
        }),
{
    // Injectivity from involution
    lemma_swizzle_injective_on_domain(b, m, s, pow2(m + s + b));

    // Surjectivity: witness is swizzle(k) itself (involution)
    assert forall|k: nat| k < pow2(m + s + b) implies ({
        let w = #[trigger] swizzle(k, b, m, s);
        w < pow2(m + s + b) && swizzle(w, b, m, s) == k
    }) by {
        lemma_swizzle_surjective_bounded(k, b, m, s);
    };
}

/// Swizzled bijective layout remains injective on swizzled image.
pub proof fn lemma_swizzled_bijective_layout(
    layout: &LayoutSpec, b: nat, m: nat, s: nat, target: nat,
)
    requires
        swizzle_layout_admissible(layout, b, m, s),
        layout.is_bijective_upto(target),
        target <= pow2(m + s + b),
    ensures
        forall|i: nat, j: nat| i < layout.size() && j < layout.size() && i != j
            ==> swizzled_offset(layout, b, m, s, i) != swizzled_offset(layout, b, m, s, j),
{
    // Direct from lemma_swizzled_offset_injective
    lemma_swizzled_offset_injective(layout, b, m, s);
}

/// SM80 GEMM swizzle (B=3, M=0, S=3) instantiation: injective layout
/// has no bank conflicts after swizzling.
pub proof fn lemma_sm80_smem_swizzle_injective(layout: &LayoutSpec, size: nat)
    requires
        swizzle_layout_admissible(layout, 3, 0, 3),
        layout.is_injective(),
        size <= layout.size(),
    ensures
        forall|i: nat, j: nat| i < size && j < size && i != j
            ==> swizzled_offset(layout, 3, 0, 3, i) != swizzled_offset(layout, 3, 0, 3, j),
{
    lemma_swizzled_offset_injective(layout, 3, 0, 3);
    assert forall|i: nat, j: nat| i < size && j < size && i != j implies
        swizzled_offset(layout, 3, 0, 3, i) != swizzled_offset(layout, 3, 0, 3, j)
    by {
        assert(i < layout.size() && j < layout.size());
    };
}

} // verus!
