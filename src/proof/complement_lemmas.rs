use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::proof::shape_lemmas::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Complement validity
// ══════════════════════════════════════════════════════════════

/// The complement layout has rank k+1 (one more than A).
pub proof fn lemma_complement_rank(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures
        complement(a, m).shape.len() == a.shape.len() + 1,
        complement(a, m).stride.len() == a.shape.len() + 1,
        complement(a, m).shape.len() == complement(a, m).stride.len(),
{
}

// ══════════════════════════════════════════════════════════════
// Helper: if a divides b and a > 0 and b > 0, then b/a > 0
// ══════════════════════════════════════════════════════════════

pub proof fn lemma_div_positive_when_divides(a: int, b: int)
    requires a > 0, b > 0, b % a == 0,
    ensures b / a > 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, a);
    // b == a * (b/a) + b%a == a * (b/a)
    // b > 0 and a > 0, so b/a > 0 (otherwise a * 0 == 0 != b)
    if b / a <= 0 {
        vstd::arithmetic::mul::lemma_mul_nonnegative(a, b / a);
        assert(a * (b / a) <= 0);
        assert(false);
    }
}

// ══════════════════════════════════════════════════════════════
// Complement shape validity
// ══════════════════════════════════════════════════════════════

/// All complement shape entries are positive (the complement layout has a valid shape).
pub proof fn lemma_complement_shape_valid(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures shape_valid(complement_shape(a, m)),
{
    let cs = complement_shape(a, m);
    let k = a.shape.len();

    assert forall|i: int| 0 <= i < cs.len() implies #[trigger] cs[i] > 0 by {
        if i == 0 {
            // cs[0] = a.stride[0] > 0 (from admissibility: a.stride[0] > 0)
            assert(cs[0] == a.stride[0] as nat);
        } else if i < k as int {
            // cs[i] = a.stride[i] / stride_product(a, i-1)
            // tractability: stride_product(a, i-1) divides a.stride[i]
            // and both are positive, so quotient > 0
            let sp = stride_product(a, i - 1);
            assert(sp > 0) by {
                // sp = a.shape[i-1] * a.stride[i-1]
                // a.shape[i-1] > 0 (valid shape), a.stride[i-1] >= 0 (non_negative_strides)
                // For sorted: a.stride[i-1] >= a.stride[0] > 0
                assert(a.stride[i - 1] >= a.stride[0]);
                lemma_mul_pos(a.shape[i - 1], a.stride[i - 1] as nat);
            };
            // From tractability at index i-1:
            // a.stride[(i-1)+1] % ((a.shape[i-1] as int) * a.stride[i-1]) == 0
            // i.e., a.stride[i] % stride_product(a, i-1) == 0
            let ti = i - 1;
            assert(0 <= ti < a.stride.len() as int - 1);
            assert(a.tractable_at(ti));
            let product_ti = (a.shape[ti] as int) * a.stride[ti];
            assert(a.stride[ti + 1] % product_ti == 0);
            assert(sp == product_ti);
            assert(a.stride[i] % sp == 0);
            assert(a.stride[i] >= a.stride[0]);
            assert(a.stride[i] > 0);
            lemma_div_positive_when_divides(sp, a.stride[i]);
            assert(cs[i] == (a.stride[i] / sp) as nat);
        } else {
            // i == k: cs[k] = M / stride_product(a, k-1)
            let sp = stride_product(a, (k - 1) as int);
            assert(sp > 0) by {
                assert(sp == (a.shape.last() as int) * a.stride.last());
                assert(a.stride.last() >= a.stride[0]);
                lemma_mul_pos(a.shape.last(), a.stride.last() as nat);
            };
            assert((m as int) % sp == 0);
            lemma_div_positive_when_divides(sp, m as int);
            assert(cs[i] == ((m as int) / sp) as nat);
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Complement size for 1D layout
// ══════════════════════════════════════════════════════════════

/// For a 1D layout A = (M_0):(d_0), complement size * A size == M.
pub proof fn lemma_complement_size_1d(a: &LayoutSpec, m: nat)
    requires
        complement_admissible(a, m),
        a.shape.len() == 1,
    ensures ({
        let c = complement(a, m);
        // We state it as a product identity rather than division
        // to avoid reasoning about nat division
        shape_size(c.shape) * shape_size(a.shape) == m
    }),
{
    let c = complement(a, m);
    let cs = complement_shape(a, m);
    let m0 = a.shape[0];
    let d0 = a.stride[0];
    let sp0 = (m0 as int) * d0;

    // sp0 > 0
    assert(sp0 > 0) by {
        lemma_mul_pos(m0, d0 as nat);
    };

    // M % sp0 == 0 (from admissibility)
    assert((m as int) % sp0 == 0);

    // M / sp0 > 0
    lemma_div_positive_when_divides(sp0, m as int);

    // cs = complement_shape(a, m) has length 2
    assert(cs.len() == 2);
    let c0 = cs[0]; // = d0
    let c1 = cs[1]; // = M / sp0
    assert(c0 == d0 as nat);
    assert(c1 == ((m as int) / sp0) as nat);
    assert(c1 > 0);

    // shape_size(cs):
    // cs is Seq::new(2, f). We need shape_size of this.
    // shape_size(cs) = cs.first() * shape_size(cs.skip(1))
    //               = c0 * shape_size(cs.skip(1))
    // cs.skip(1) has length 1, first element = c1
    // shape_size(cs.skip(1)) = c1 * shape_size(cs.skip(1).skip(1))
    //                        = c1 * 1 = c1

    // Actually, let me just unfold shape_size for length 2 directly
    assert(cs.first() == c0);
    assert(shape_size(cs) == c0 * shape_size(cs.skip(1)));
    assert(cs.skip(1).len() == 1);
    assert(cs.skip(1).first() == c1);
    assert(shape_size(cs.skip(1)) == c1 * shape_size(cs.skip(1).skip(1)));
    assert(cs.skip(1).skip(1).len() == 0);
    assert(shape_size(cs.skip(1).skip(1)) == 1);

    // shape_size(cs.skip(1)) = c1 * 1 = c1
    vstd::arithmetic::mul::lemma_mul_basics(c1 as int);
    assert(shape_size(cs.skip(1)) == c1);

    // shape_size(cs) = c0 * c1
    assert(shape_size(cs) == c0 * shape_size(cs.skip(1)));
    assert(shape_size(cs) == c0 * c1);

    // shape_size(a.shape) = m0 * 1 = m0
    assert(shape_size(a.shape) == m0 * shape_size(a.shape.skip(1)));
    assert(a.shape.skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(m0 as int);
    assert(shape_size(a.shape) == m0);

    // Now: shape_size(cs) * shape_size(a.shape) = d0 * (M/sp0) * m0
    // sp0 = m0 * d0, so d0 * (M/sp0) * m0 = (M/sp0) * (d0 * m0) = (M/sp0) * sp0 = M

    // (M / sp0) * sp0 == M
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, sp0);
    assert(m as int == sp0 * ((m as int) / sp0));
    vstd::arithmetic::mul::lemma_mul_is_commutative(sp0, (m as int) / sp0);
    assert((m as int) / sp0 * sp0 == m as int);

    // d0 * (M/sp0) * m0 == (M/sp0) * (d0 * m0) == (M/sp0) * sp0 == M
    vstd::arithmetic::mul::lemma_mul_is_commutative(d0 as int, (m as int) / sp0);
    // c0 * c1 = d0 * (M/sp0) = (M/sp0) * d0
    vstd::arithmetic::mul::lemma_mul_is_associative((m as int) / sp0, d0 as int, m0 as int);
    // (M/sp0) * d0 * m0 = (M/sp0) * (d0 * m0) = (M/sp0) * sp0 = M
    vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, d0 as int);
    // d0 * m0 == m0 * d0 == sp0
    assert((c0 * c1) as int * (m0 as int) == m as int);
}

// ══════════════════════════════════════════════════════════════
// Complement strides are ordered
// ══════════════════════════════════════════════════════════════

/// Complement stride[0] == 1.
pub proof fn lemma_complement_stride_first(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).stride[0] == 1,
{
}

/// Complement stride[i+1] = stride_product(a, i) for i >= 0.
pub proof fn lemma_complement_stride_rest(a: &LayoutSpec, m: nat, i: int)
    requires complement_admissible(a, m), 0 <= i < a.shape.len() as int,
    ensures complement(a, m).stride[i + 1] == stride_product(a, i),
{
}

// ══════════════════════════════════════════════════════════════
// Complement validity (full)
// ══════════════════════════════════════════════════════════════

/// The complement layout is valid (shape/stride lengths match, all shapes > 0).
pub proof fn lemma_complement_valid(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).valid(),
{
    lemma_complement_rank(a, m);
    lemma_complement_shape_valid(a, m);
}

// ══════════════════════════════════════════════════════════════
// Complement has all-positive strides
// ══════════════════════════════════════════════════════════════

/// Helper: stride_product(a, i) > 0 for a valid sorted layout with stride[0] > 0.
proof fn lemma_stride_product_positive(a: &LayoutSpec, i: int)
    requires
        a.valid(),
        a.is_sorted(),
        a.stride[0] > 0,
        a.shape.len() > 0,
        0 <= i < a.shape.len() as int,
    ensures stride_product(a, i) > 0,
{
    // stride_product(a, i) = shape[i] * stride[i]
    // shape[i] > 0 (valid), stride[i] >= stride[0] > 0 (sorted, stride[0] > 0)
    assert(a.stride[i] >= a.stride[0]);
    assert(a.stride[i] > 0);
    lemma_mul_pos(a.shape[i], a.stride[i] as nat);
}

/// All complement strides are positive.
pub proof fn lemma_complement_positive_strides(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures
        forall|i: int| 0 <= i < complement(a, m).stride.len()
            ==> #[trigger] complement(a, m).stride[i] > 0,
{
    let c = complement(a, m);
    lemma_complement_rank(a, m);

    assert forall|i: int| 0 <= i < c.stride.len()
    implies #[trigger] c.stride[i] > 0 by {
        if i == 0 {
            lemma_complement_stride_first(a, m);
        } else {
            lemma_complement_stride_rest(a, m, i - 1);
            // c.stride[i] = stride_product(a, i-1) > 0
            lemma_stride_product_positive(a, i - 1);
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Complement is tractable
// ══════════════════════════════════════════════════════════════

/// The complement layout is tractable.
///
/// For complement mode i (0 <= i < k):
///   complement.shape[i] * complement.stride[i] divides complement.stride[i+1]
///
/// At i=0: shape_c[0]*stride_c[0] = d_0*1 = d_0, stride_c[1] = M_0*d_0, so d_0 | M_0*d_0 ✓
/// At i>=1,i<k: shape_c[i]*stride_c[i] = (d_i/sp(i-1))*sp(i-1) = d_i,
///              stride_c[i+1] = sp(i) = M_i*d_i, so d_i | M_i*d_i ✓
pub proof fn lemma_complement_tractable(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).is_tractable(),
{
    let c = complement(a, m);
    let k = a.shape.len();
    lemma_complement_rank(a, m);
    lemma_complement_shape_valid(a, m);
    lemma_complement_positive_strides(a, m);

    assert forall|i: int| 0 <= i < c.stride.len() - 1
    implies #[trigger] c.tractable_at(i) by {
        let cs_i = c.shape[i];
        let cd_i = c.stride[i];
        let cd_next = c.stride[i + 1];
        let product_i = (cs_i as int) * cd_i;

        // product_i > 0
        assert(cs_i > 0) by {
            lemma_complement_shape_valid(a, m);
        };
        assert(cd_i > 0);
        lemma_mul_pos(cs_i, cd_i as nat);

        // Show cd_next % product_i == 0
        if i == 0 {
            // cs[0] = d_0, cd[0] = 1, product_0 = d_0
            lemma_complement_stride_first(a, m);
            assert(cd_i == 1);
            assert(product_i == cs_i as int);
            // cs[0] = a.stride[0]
            assert(cs_i == a.stride[0] as nat);
            assert(product_i == a.stride[0]);
            // cd[1] = stride_product(a, 0) = M_0 * d_0
            lemma_complement_stride_rest(a, m, 0);
            assert(cd_next == stride_product(a, 0));
            assert(cd_next == (a.shape[0] as int) * a.stride[0]);
            // M_0 * d_0 % d_0 == 0
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(a.shape[0] as int, a.stride[0]);
        } else {
            // i >= 1, i < k (since c has k+1 modes, tractability checks i < k)
            // cs[i] = d_i / sp(i-1)
            // cd[i] = sp(i-1)
            // product_i = (d_i / sp(i-1)) * sp(i-1) = d_i
            lemma_complement_stride_rest(a, m, i - 1);
            assert(cd_i == stride_product(a, i - 1));
            let sp_im1 = stride_product(a, i - 1);

            // cs[i] = d_i / sp(i-1)
            // product_i = cs[i] * sp(i-1)
            // We need: product_i == a.stride[i]
            // This follows from cs[i] = (d_i / sp(i-1)) and d_i % sp(i-1) == 0
            // From tractability of a at (i-1): d_i % sp(i-1) == 0
            assert(a.tractable_at(i - 1));
            assert(a.stride[i] % sp_im1 == 0);
            lemma_stride_product_positive(a, i - 1);
            // d_i / sp(i-1) * sp(i-1) == d_i
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a.stride[i], sp_im1);
            assert(a.stride[i] == sp_im1 * (a.stride[i] / sp_im1));
            vstd::arithmetic::mul::lemma_mul_is_commutative(sp_im1, a.stride[i] / sp_im1);
            assert(product_i == a.stride[i]);

            // cd[i+1] = sp(i) = M_i * d_i
            if i < k as int - 1 {
                lemma_complement_stride_rest(a, m, i);
                assert(cd_next == stride_product(a, i));
                // stride_product(a, i) = shape[i] * stride[i] = M_i * d_i
                // So cd_next % product_i == (M_i * d_i) % d_i == 0
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                    a.shape[i] as int, a.stride[i],
                );
            } else {
                // i == k-1 (last tractability check)
                // cd[k] = sp(k-1) = stride_product(a, k-1)
                lemma_complement_stride_rest(a, m, i);
                assert(cd_next == stride_product(a, i));
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                    a.shape[i] as int, a.stride[i],
                );
            }
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Complement injectivity
// ══════════════════════════════════════════════════════════════

/// The complement layout is always injective.
pub proof fn lemma_complement_injective(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).is_injective(),
{
    let c = complement(a, m);
    lemma_complement_valid(a, m);
    lemma_complement_tractable(a, m);
    lemma_complement_positive_strides(a, m);
    lemma_complement_rank(a, m);

    // complement has rank >= 1 (k+1 where k >= 1)
    assert(c.shape.len() > 0);

    crate::proof::injectivity_lemmas::lemma_positive_tractable_injective(c);
}

} // verus!
