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

proof fn lemma_div_positive_when_divides(a: int, b: int)
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

} // verus!
