use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::product::*;
use crate::proof::shape_lemmas::*;
use crate::proof::injectivity_lemmas::lemma_dot_product_scale;

verus! {

// ══════════════════════════════════════════════════════════════
// Logical product: structural properties
// ══════════════════════════════════════════════════════════════

/// Logical product rank = rank(A) + rank(B).
pub proof fn lemma_product_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires product_admissible(a, b),
    ensures
        logical_product(a, b).shape.len() == a.shape.len() + b.shape.len(),
        logical_product(a, b).stride.len() == a.shape.len() + b.shape.len(),
{
}

/// Logical product size = size(A) * size(B).
pub proof fn lemma_product_size(a: &LayoutSpec, b: &LayoutSpec)
    requires product_admissible(a, b),
    ensures
        shape_size(logical_product(a, b).shape)
            == shape_size(a.shape) * shape_size(b.shape),
    decreases a.shape.len() + b.shape.len(),
{
    // shape = a.shape ++ b.shape
    // size(a.shape ++ b.shape) = size(a.shape) * size(b.shape) by lemma_shape_size_append
    lemma_shape_size_append(a.shape, b.shape);
}

/// The product layout's tile modes (first rank(A) modes) match A's modes.
pub proof fn lemma_product_tile_shape(a: &LayoutSpec, b: &LayoutSpec, i: int)
    requires
        product_admissible(a, b),
        0 <= i < a.shape.len() as int,
    ensures
        logical_product(a, b).shape[i] == a.shape[i],
        logical_product(a, b).stride[i] == a.stride[i],
{
}

/// The product layout's rest strides are B's strides scaled by cosize(A).
pub proof fn lemma_product_rest_stride(a: &LayoutSpec, b: &LayoutSpec, i: int)
    requires
        product_admissible(a, b),
        0 <= i < b.shape.len() as int,
    ensures
        logical_product(a, b).shape[(a.shape.len() + i) as int] == b.shape[i],
        logical_product(a, b).stride[(a.shape.len() + i) as int]
            == b.stride[i] * (a.cosize_nonneg() as int),
{
    let p = logical_product(a, b);
    let cs = a.cosize_nonneg();
    let idx = (a.shape.len() + i) as int;

    // p.stride = a.stride ++ scale_strides(b.stride, cs)
    // p.stride[rank_a + i] = scale_strides(b.stride, cs)[i] = b.stride[i] * cs
    assert(scale_strides(b.stride, cs as int)[i] == b.stride[i] * (cs as int));
}

// ══════════════════════════════════════════════════════════════
// Helper: shape_size distributes over concatenation
// ══════════════════════════════════════════════════════════════

/// shape_size(a ++ b) == shape_size(a) * shape_size(b)
pub proof fn lemma_shape_size_append(a: Seq<nat>, b: Seq<nat>)
    ensures shape_size(a.add(b)) == shape_size(a) * shape_size(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a.add(b) =~= b);
        vstd::arithmetic::mul::lemma_mul_basics(shape_size(b) as int);
    } else {
        // shape_size(a ++ b) = (a ++ b)[0] * shape_size((a ++ b).skip(1))
        //                    = a[0] * shape_size(a.skip(1) ++ b)
        assert(a.add(b).first() == a.first());
        assert(a.add(b).skip(1) =~= a.skip(1).add(b));
        lemma_shape_size_append(a.skip(1), b);
        // IH: shape_size(a.skip(1) ++ b) == shape_size(a.skip(1)) * shape_size(b)
        // shape_size(a ++ b) = a[0] * shape_size(a.skip(1)) * shape_size(b)
        //                    = shape_size(a) * shape_size(b)
        vstd::arithmetic::mul::lemma_mul_is_associative(
            a.first() as int,
            shape_size(a.skip(1)) as int,
            shape_size(b) as int,
        );
    }
}

// ══════════════════════════════════════════════════════════════
// Logical product validity
// ══════════════════════════════════════════════════════════════

/// The logical product layout is valid.
pub proof fn lemma_product_valid(a: &LayoutSpec, b: &LayoutSpec)
    requires product_admissible(a, b),
    ensures logical_product(a, b).valid(),
{
    let p = logical_product(a, b);
    lemma_product_rank(a, b);
    assert(p.shape.len() == p.stride.len());

    assert forall|i: int| 0 <= i < p.shape.len() implies #[trigger] p.shape[i] > 0 by {
        if i < a.shape.len() as int {
            lemma_product_tile_shape(a, b, i);
            assert(p.shape[i] == a.shape[i]);
        } else {
            let bi = (i - a.shape.len()) as int;
            lemma_product_rest_stride(a, b, bi);
            assert(p.shape[i] == b.shape[bi]);
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Product offset decomposition
// ══════════════════════════════════════════════════════════════

/// scale_strides (product.rs) == scale_strides_spec (layout.rs) — same definition, bridge for Z3.
proof fn lemma_scale_strides_eq(strides: Seq<int>, factor: int)
    ensures scale_strides(strides, factor) =~= scale_strides_spec(strides, factor),
{
    assert forall|i: int| 0 <= i < strides.len()
    implies scale_strides(strides, factor)[i] == scale_strides_spec(strides, factor)[i] by {
    };
}

/// Product offset decomposition:
/// product(a,b).offset(x) == a.offset(x % size_a) + cosize(a) * b.offset(x / size_a)
pub proof fn lemma_product_offset(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        product_admissible(a, b),
        x < a.size() * b.size(),
    ensures
        logical_product(a, b).offset(x)
            == a.offset(x % a.size()) + (a.cosize_nonneg() as int) * b.offset(x / a.size()),
{
    let p = logical_product(a, b);
    let s_a = a.shape;
    let s_b = b.shape;
    let size_a = shape_size(s_a);
    let size_b = shape_size(s_b);
    let cs = a.cosize_nonneg() as int;

    // Product shape = s_a ++ s_b, size = size_a * size_b
    lemma_product_size(a, b);
    assert(shape_size(p.shape) == size_a * size_b);

    // x < size_a * size_b = shape_size(s_a ++ s_b)
    lemma_shape_size_append(s_a, s_b);
    assert(x < shape_size(s_a.add(s_b)));

    // Step 1: delinearize(x, s_a ++ s_b) =~= delinearize(x % size_a, s_a) ++ delinearize(x / size_a, s_b)
    lemma_delinearize_concat(x, s_a, s_b);
    let d_a = delinearize(x % size_a, s_a);
    let d_b = delinearize(x / size_a, s_b);
    assert(delinearize(x, s_a.add(s_b)) =~= d_a.add(d_b));

    // The product's coords are delinearize(x, p.shape) = delinearize(x, s_a ++ s_b)
    assert(p.shape =~= s_a.add(s_b));

    // Step 2: split dot product over concatenation
    // p.stride = a.stride ++ scale_strides(b.stride, cs)
    let scaled_b = scale_strides(b.stride, cs);
    assert(p.stride =~= a.stride.add(scaled_b));

    // dot(d_a ++ d_b, a.stride ++ scaled_b) = dot(d_a, a.stride) + dot(d_b, scaled_b)
    lemma_delinearize_len(x % size_a, s_a);
    lemma_delinearize_len(x / size_a, s_b);
    assert(d_a.len() == s_a.len());
    assert(d_b.len() == s_b.len());
    assert(d_a.len() == a.stride.len());
    assert(d_b.len() == scaled_b.len());

    lemma_dot_product_append(d_a, d_b, a.stride, scaled_b);
    assert(dot_product_nat_int(d_a.add(d_b), a.stride.add(scaled_b))
        == dot_product_nat_int(d_a, a.stride) + dot_product_nat_int(d_b, scaled_b));

    // Step 3: factor out cs from scaled strides
    // dot(d_b, scale_strides(b.stride, cs)) = cs * dot(d_b, b.stride)
    lemma_scale_strides_eq(b.stride, cs);
    assert(scaled_b =~= scale_strides_spec(b.stride, cs));
    lemma_dot_product_scale(d_b, b.stride, cs);
    assert(dot_product_nat_int(d_b, scaled_b)
        == cs * dot_product_nat_int(d_b, b.stride));

    // Step 4: connect to offset definitions
    // a.offset(x % size_a) = dot(delinearize(x % size_a, s_a), a.stride) = dot(d_a, a.stride)
    // b.offset(x / size_a) = dot(delinearize(x / size_a, s_b), b.stride) = dot(d_b, b.stride)

    // p.offset(x) = dot(delinearize(x, p.shape), p.stride)
    //             = dot(d_a ++ d_b, a.stride ++ scaled_b)
    //             = dot(d_a, a.stride) + cs * dot(d_b, b.stride)
    //             = a.offset(x % size_a) + cs * b.offset(x / size_a)

    // Bridge: delinearize(x, p.shape) =~= d_a ++ d_b, so the dot products match
    assert(p.offset(x) == dot_product_nat_int(delinearize(x, p.shape), p.stride));
    assert(delinearize(x, p.shape) =~= d_a.add(d_b));
    // Need to show dot_product respects extensional equality
    assert(dot_product_nat_int(delinearize(x, p.shape), p.stride)
        == dot_product_nat_int(d_a.add(d_b), a.stride.add(scaled_b)));
}

/// The first tile of a logical product behaves like A:
/// for x < size(A), product(A,B).offset(x) == A.offset(x).
pub proof fn lemma_product_compatible(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        product_admissible(a, b),
        x < a.size(),
    ensures
        logical_product(a, b).offset(x) == a.offset(x),
{
    // product(a,b).offset(x) == a.offset(x % size_a) + cosize(a) * b.offset(x / size_a)
    lemma_shape_size_positive(a.shape);
    lemma_shape_size_positive(b.shape);
    let size_a = shape_size(a.shape);
    assert(x < size_a);
    // x % size_a == x and x / size_a == 0 when x < size_a
    crate::proof::integer_helpers::lemma_mod_small(x, size_a);
    crate::proof::integer_helpers::lemma_div_small(x, size_a);

    // x < size_a * size_b (needed for lemma_product_offset)
    let size_b = shape_size(b.shape);
    assert(size_b >= 1) by {
        lemma_shape_size_positive(b.shape);
    };
    vstd::arithmetic::mul::lemma_mul_basics(size_a as int);
    assert(size_a * 1 == size_a);
    vstd::arithmetic::mul::lemma_mul_inequality(1, size_b as int, size_a as int);
    assert(x < size_a * size_b);
    lemma_product_offset(a, b, x);
    // product(a,b).offset(x) == a.offset(x) + cosize(a) * b.offset(0)

    // b.offset(0) == 0
    crate::proof::offset_lemmas::lemma_offset_zero(
        LayoutSpec { shape: b.shape, stride: b.stride },
    );
    // cosize(a) * 0 == 0
    vstd::arithmetic::mul::lemma_mul_basics(a.cosize_nonneg() as int);
}

// ══════════════════════════════════════════════════════════════
// Raked product: structural properties
// ══════════════════════════════════════════════════════════════

/// Raked product rank = rank(A) + rank(B).
pub proof fn lemma_raked_product_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires raked_product_admissible(a, b),
    ensures
        raked_product(a, b).shape.len() == a.shape.len() + b.shape.len(),
        raked_product(a, b).stride.len() == a.shape.len() + b.shape.len(),
{
}

/// Raked product size = size(A) * size(B).
pub proof fn lemma_raked_product_size(a: &LayoutSpec, b: &LayoutSpec)
    requires raked_product_admissible(a, b),
    ensures
        shape_size(raked_product(a, b).shape)
            == shape_size(a.shape) * shape_size(b.shape),
{
    lemma_shape_size_append(a.shape, b.shape);
}

/// The raked product layout is valid.
pub proof fn lemma_raked_product_valid(a: &LayoutSpec, b: &LayoutSpec)
    requires raked_product_admissible(a, b),
    ensures raked_product(a, b).valid(),
{
    let r = raked_product(a, b);
    lemma_raked_product_rank(a, b);
    assert(r.shape.len() == r.stride.len());

    assert forall|i: int| 0 <= i < r.shape.len() implies #[trigger] r.shape[i] > 0 by {
        if i < a.shape.len() as int {
            assert(r.shape[i] == a.shape[i]);
        } else {
            let bi = (i - a.shape.len()) as int;
            assert(r.shape[i] == b.shape[bi]);
        }
    };
}

/// Raked product is logical_product with swapped operands (up to mode reordering).
/// raked_product(A, B).shape == A.shape ++ B.shape
/// logical_product(B, A).shape == B.shape ++ A.shape
/// They have the same size and hit the same offsets (in different order).
pub proof fn lemma_raked_product_size_eq_product(a: &LayoutSpec, b: &LayoutSpec)
    requires
        raked_product_admissible(a, b),
        product_admissible(b, a),
    ensures
        shape_size(raked_product(a, b).shape) == shape_size(logical_product(b, a).shape),
{
    lemma_raked_product_size(a, b);
    lemma_product_size(b, a);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(a.shape) as int,
        shape_size(b.shape) as int,
    );
}

// ══════════════════════════════════════════════════════════════
// Blocked product: alias for logical_product
// ══════════════════════════════════════════════════════════════

/// Blocked product rank = rank(A) + rank(B).
pub proof fn lemma_blocked_product_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires product_admissible(a, b),
    ensures
        blocked_product(a, b).shape.len() == a.shape.len() + b.shape.len(),
        blocked_product(a, b).stride.len() == a.shape.len() + b.shape.len(),
{
    lemma_product_rank(a, b);
}

/// Blocked product size = size(A) * size(B).
pub proof fn lemma_blocked_product_size(a: &LayoutSpec, b: &LayoutSpec)
    requires product_admissible(a, b),
    ensures
        shape_size(blocked_product(a, b).shape)
            == shape_size(a.shape) * shape_size(b.shape),
{
    lemma_product_size(a, b);
}

/// Blocked product is valid.
pub proof fn lemma_blocked_product_valid(a: &LayoutSpec, b: &LayoutSpec)
    requires product_admissible(a, b),
    ensures blocked_product(a, b).valid(),
{
    lemma_product_valid(a, b);
}

// ══════════════════════════════════════════════════════════════
// Product injectivity
// ══════════════════════════════════════════════════════════════

/// If A and B are both injective, A has non-negative strides, and B has
/// non-negative strides, then logical_product(A, B) is injective.
///
/// Proof: product.offset(x) = A.offset(x % sa) + cosize(A) * B.offset(x / sa).
/// The A-part is in [0, cosize(A)) and the B-part is a multiple of cosize(A),
/// so modular arithmetic separates distinct inputs.
pub proof fn lemma_product_injective(a: &LayoutSpec, b: &LayoutSpec)
    requires
        product_admissible(a, b),
        b.non_negative_strides(),
        a.is_injective(),
        b.is_injective(),
    ensures
        logical_product(a, b).is_injective(),
{
    let p = logical_product(a, b);
    let sa = a.size();
    let sb = b.size();
    let cs = a.cosize_nonneg() as int;

    lemma_product_valid(a, b);
    lemma_product_size(a, b);
    lemma_shape_size_positive(a.shape);
    lemma_shape_size_positive(b.shape);

    assert forall|x1: nat, x2: nat|
        x1 < p.size() && x2 < p.size() && x1 != x2
    implies
        #[trigger] p.offset(x1) != #[trigger] p.offset(x2)
    by {
        // p.size() == sa * sb
        assert(x1 < sa * sb);
        assert(x2 < sa * sb);

        lemma_product_offset(a, b, x1);
        lemma_product_offset(a, b, x2);

        let r1 = x1 % sa;
        let q1 = x1 / sa;
        let r2 = x2 % sa;
        let q2 = x2 / sa;

        // r1, r2 < sa
        crate::proof::integer_helpers::lemma_mod_bound(x1, sa);
        crate::proof::integer_helpers::lemma_mod_bound(x2, sa);

        // q1, q2 < sb
        crate::proof::integer_helpers::lemma_div_upper_bound(x1, sa, sb);
        crate::proof::integer_helpers::lemma_div_upper_bound(x2, sa, sb);

        // A.offset(r) is in [0, cosize(A)) for r < sa
        crate::proof::offset_lemmas::lemma_offset_nonneg(*a, r1);
        crate::proof::offset_lemmas::lemma_offset_nonneg(*a, r2);
        crate::proof::offset_lemmas::lemma_offset_upper_bound(*a, r1);
        crate::proof::offset_lemmas::lemma_offset_upper_bound(*a, r2);
        let oa1 = a.offset(r1);
        let oa2 = a.offset(r2);

        // B.offset(q) >= 0
        crate::proof::offset_lemmas::lemma_offset_nonneg(*b, q1);
        crate::proof::offset_lemmas::lemma_offset_nonneg(*b, q2);
        let ob1 = b.offset(q1);
        let ob2 = b.offset(q2);

        // x1 != x2 means (r1, q1) != (r2, q2)
        crate::proof::integer_helpers::lemma_div_mod_identity(x1, sa);
        crate::proof::integer_helpers::lemma_div_mod_identity(x2, sa);

        // Suppose offsets are equal:
        // oa1 + cs * ob1 == oa2 + cs * ob2
        // oa1 - oa2 == cs * (ob2 - ob1)
        // |oa1 - oa2| < cs, and RHS is a multiple of cs
        // So ob2 - ob1 == 0, then oa1 == oa2

        if p.offset(x1) == p.offset(x2) {
            // oa1 + cs * ob1 == oa2 + cs * ob2
            assert(oa1 + cs * ob1 == oa2 + cs * ob2);

            // Case 1: cs == 0 means cosize == 0, which implies sa == 0 (contradiction since shape_valid)
            // Actually cosize >= 1 always for valid non-neg layouts
            // But cs could be 0 if the layout is empty... no, product_admissible requires a.shape.len() > 0 + valid
            // Let's just handle cases

            if cs == 0 {
                // offset of A is always 0 (all strides 0 and non-neg means all strides == 0)
                // Then oa1 == oa2 == 0, so 0 == 0, which doesn't give contradiction
                // But A injective + cosize == 0 is impossible for non-trivial A
                // Actually cosize = dot(shape_minus_one, stride) + 1 >= 1
                // So cs >= 1
                crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(*a);
                assert(false); // cosize >= 1
            }

            // cs >= 1
            // From equal: oa1 + cs*ob1 == oa2 + cs*ob2
            // So oa1 - oa2 == cs*ob2 - cs*ob1 == cs*(ob2 - ob1)
            let diff = oa1 - oa2;
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub(cs, ob2, ob1);
            assert(cs * ob2 - cs * ob1 == cs * (ob2 - ob1));
            assert(diff == cs * (ob2 - ob1));

            // |diff| < cs since both oa1, oa2 in [0, cs)
            assert(-cs < diff);
            assert(diff < cs);

            // |cs * (ob2 - ob1)| < cs means ob2 - ob1 == 0
            if ob2 - ob1 > 0 {
                vstd::arithmetic::mul::lemma_mul_inequality(1, ob2 - ob1, cs);
                vstd::arithmetic::mul::lemma_mul_basics(cs);
                vstd::arithmetic::mul::lemma_mul_is_commutative(ob2 - ob1, cs);
                assert(cs * (ob2 - ob1) >= cs);
                assert(false);
            } else if ob2 - ob1 < 0 {
                vstd::arithmetic::mul::lemma_mul_inequality(1, ob1 - ob2, cs);
                vstd::arithmetic::mul::lemma_mul_basics(cs);
                assert(cs * (ob1 - ob2) >= cs);
                assert(cs * (ob2 - ob1) == -(cs * (ob1 - ob2))) by (nonlinear_arith)
                    requires cs > 0, ob1 - ob2 > 0;
                assert(diff <= -cs);
                assert(false);
            }
            assert(ob1 == ob2);
            // B injective: ob1 == ob2 and q1, q2 < sb => q1 == q2
            if q1 != q2 {
                assert(b.offset(q1) != b.offset(q2));
                assert(false);
            }
            assert(q1 == q2);

            // oa1 == oa2
            assert(oa1 == oa2);
            // A injective: oa1 == oa2 and r1, r2 < sa => r1 == r2
            if r1 != r2 {
                assert(a.offset(r1) != a.offset(r2));
                assert(false);
            }
            assert(r1 == r2);

            // x1 == sa * q1 + r1 == sa * q2 + r2 == x2
            assert(x1 == x2);
            assert(false);
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Raked product offset decomposition
// ══════════════════════════════════════════════════════════════

/// Raked product offset decomposition:
/// raked_product(a,b).offset(x) == cosize(b) * a.offset(x % size_a) + b.offset(x / size_a)
pub proof fn lemma_raked_product_offset(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        raked_product_admissible(a, b),
        x < a.size() * b.size(),
    ensures
        raked_product(a, b).offset(x)
            == (b.cosize_nonneg() as int) * a.offset(x % a.size()) + b.offset(x / a.size()),
{
    let r = raked_product(a, b);
    let s_a = a.shape;
    let s_b = b.shape;
    let size_a = shape_size(s_a);
    let size_b = shape_size(s_b);
    let cs = b.cosize_nonneg() as int;

    lemma_raked_product_size(a, b);
    lemma_shape_size_append(s_a, s_b);
    assert(x < shape_size(s_a.add(s_b)));

    // Step 1: delinearize distributes over concat
    lemma_delinearize_concat(x, s_a, s_b);
    let d_a = delinearize(x % size_a, s_a);
    let d_b = delinearize(x / size_a, s_b);
    assert(delinearize(x, s_a.add(s_b)) =~= d_a.add(d_b));
    assert(r.shape =~= s_a.add(s_b));

    // Step 2: split dot product
    // r.stride = scale_strides(a.stride, cs) ++ b.stride
    let scaled_a = scale_strides(a.stride, cs);
    assert(r.stride =~= scaled_a.add(b.stride));

    lemma_delinearize_len(x % size_a, s_a);
    lemma_delinearize_len(x / size_a, s_b);
    assert(d_a.len() == s_a.len());
    assert(d_b.len() == s_b.len());
    assert(d_a.len() == scaled_a.len());
    assert(d_b.len() == b.stride.len());

    lemma_dot_product_append(d_a, d_b, scaled_a, b.stride);

    // Step 3: factor out cs from scaled A strides
    lemma_scale_strides_eq(a.stride, cs);
    assert(scaled_a =~= scale_strides_spec(a.stride, cs));
    lemma_dot_product_scale(d_a, a.stride, cs);
    assert(dot_product_nat_int(d_a, scaled_a) == cs * dot_product_nat_int(d_a, a.stride));

    // Step 4: connect to offset definitions
    assert(r.offset(x) == dot_product_nat_int(delinearize(x, r.shape), r.stride));
    assert(delinearize(x, r.shape) =~= d_a.add(d_b));
    assert(dot_product_nat_int(delinearize(x, r.shape), r.stride)
        == dot_product_nat_int(d_a.add(d_b), scaled_a.add(b.stride)));
}

/// First tile of raked product: for x < size(A), offset(x) == cosize(B) * a.offset(x).
pub proof fn lemma_raked_product_compatible(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        raked_product_admissible(a, b),
        x < a.size(),
    ensures
        raked_product(a, b).offset(x) == (b.cosize_nonneg() as int) * a.offset(x),
{
    lemma_shape_size_positive(a.shape);
    lemma_shape_size_positive(b.shape);
    let sa = a.size();
    let sb = b.size();

    crate::proof::integer_helpers::lemma_mod_small(x, sa);
    crate::proof::integer_helpers::lemma_div_small(x, sa);

    // x < sa * sb
    assert(sb >= 1) by { lemma_shape_size_positive(b.shape); };
    vstd::arithmetic::mul::lemma_mul_basics(sa as int);
    vstd::arithmetic::mul::lemma_mul_inequality(1, sb as int, sa as int);
    assert(x < sa * sb);

    lemma_raked_product_offset(a, b, x);
    // offset(x) == cs * a.offset(x % sa) + b.offset(x / sa)
    //           == cs * a.offset(x) + b.offset(0)

    crate::proof::offset_lemmas::lemma_offset_zero(*b);
    vstd::arithmetic::mul::lemma_mul_basics(b.cosize_nonneg() as int);
}

// ══════════════════════════════════════════════════════════════
// Product surjectivity and bijectivity
// ══════════════════════════════════════════════════════════════

/// If A is surjective onto [0, m_a) and B is surjective onto [0, m_b),
/// then logical_product(A, B) is surjective onto [0, m_a * m_b).
pub proof fn lemma_product_surjective(a: &LayoutSpec, b: &LayoutSpec, m_a: nat, m_b: nat)
    requires
        product_admissible(a, b),
        b.non_negative_strides(),
        a.is_surjective_upto(m_a),
        b.is_surjective_upto(m_b),
        m_a == a.cosize_nonneg(),
        m_a > 0,
        m_b > 0,
    ensures
        logical_product(a, b).is_surjective_upto(m_a * m_b),
{
    let p = logical_product(a, b);
    let sa = a.size();
    let sb = b.size();

    lemma_product_size(a, b);
    lemma_product_valid(a, b);
    lemma_shape_size_positive(a.shape);
    lemma_shape_size_positive(b.shape);

    assert forall|k: int| 0 <= k < (m_a * m_b) as int
        implies #[trigger] p.offset_hit(k)
    by {
        let k_a: nat = (k % m_a as int) as nat;
        let k_b: nat = (k / m_a as int) as nat;

        assert(0 <= k_a < m_a);
        crate::proof::integer_helpers::lemma_div_upper_bound(k as nat, m_a, m_b);
        assert(0 <= k_b < m_b);

        assert(a.offset_hit(k_a as int));
        let r: nat = choose|r: nat| r < sa && a.offset(r) == k_a as int;
        assert(r < sa && a.offset(r) == k_a as int);

        assert(b.offset_hit(k_b as int));
        let q: nat = choose|q: nat| q < sb && b.offset(q) == k_b as int;
        assert(q < sb && b.offset(q) == k_b as int);

        let x: nat = r + sa * q;

        // x < sa * sb
        assert(x < sa * sb) by (nonlinear_arith)
            requires r < sa, q < sb, sa > 0, x == r + sa * q;

        crate::proof::integer_helpers::lemma_div_mod_decompose(r, q, sa);

        lemma_product_offset(a, b, x);
        assert(p.offset(x) == a.offset(r) + (m_a as int) * b.offset(q));
        assert(p.offset(x) == k_a as int + (m_a as int) * (k_b as int));

        crate::proof::integer_helpers::lemma_div_mod_identity(k as nat, m_a);
        assert(p.offset(x) == k);
        assert(x < p.size());
    };
}

/// Product bijectivity: injective + surjective → bijective.
pub proof fn lemma_product_bijective(a: &LayoutSpec, b: &LayoutSpec, m_a: nat, m_b: nat)
    requires
        product_admissible(a, b),
        b.non_negative_strides(),
        a.is_injective(),
        b.is_injective(),
        a.is_surjective_upto(m_a),
        b.is_surjective_upto(m_b),
        m_a == a.cosize_nonneg(),
        m_a > 0,
        m_b > 0,
    ensures
        logical_product(a, b).is_bijective_upto(m_a * m_b),
{
    lemma_product_injective(a, b);
    lemma_product_surjective(a, b, m_a, m_b);
}

// ══════════════════════════════════════════════════════════════
// Blocked product: surjectivity and bijectivity aliases
// ══════════════════════════════════════════════════════════════

/// Blocked product offset decomposition (alias for product offset).
pub proof fn lemma_blocked_product_offset(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        product_admissible(a, b),
        x < a.size() * b.size(),
    ensures
        blocked_product(a, b).offset(x)
            == a.offset(x % a.size()) + (a.cosize_nonneg() as int) * b.offset(x / a.size()),
{
    lemma_product_offset(a, b, x);
}

/// Blocked product surjectivity (alias for product surjectivity).
pub proof fn lemma_blocked_product_surjective(a: &LayoutSpec, b: &LayoutSpec, m_a: nat, m_b: nat)
    requires
        product_admissible(a, b),
        b.non_negative_strides(),
        a.is_surjective_upto(m_a),
        b.is_surjective_upto(m_b),
        m_a == a.cosize_nonneg(),
        m_a > 0,
        m_b > 0,
    ensures
        blocked_product(a, b).is_surjective_upto(m_a * m_b),
{
    lemma_product_surjective(a, b, m_a, m_b);
}

/// Blocked product bijectivity (alias for product bijectivity).
pub proof fn lemma_blocked_product_bijective(a: &LayoutSpec, b: &LayoutSpec, m_a: nat, m_b: nat)
    requires
        product_admissible(a, b),
        b.non_negative_strides(),
        a.is_injective(),
        b.is_injective(),
        a.is_surjective_upto(m_a),
        b.is_surjective_upto(m_b),
        m_a == a.cosize_nonneg(),
        m_a > 0,
        m_b > 0,
    ensures
        blocked_product(a, b).is_bijective_upto(m_a * m_b),
{
    lemma_product_bijective(a, b, m_a, m_b);
}

// ══════════════════════════════════════════════════════════════
// Raked product injectivity, surjectivity, bijectivity
// ══════════════════════════════════════════════════════════════

/// Raked product preserves injectivity:
/// if A (non-neg strides) and B are both injective,
/// then raked_product(A, B) is injective.
pub proof fn lemma_raked_product_injective(a: &LayoutSpec, b: &LayoutSpec)
    requires
        raked_product_admissible(a, b),
        a.non_negative_strides(),
        a.is_injective(),
        b.is_injective(),
    ensures
        raked_product(a, b).is_injective(),
{
    let p = raked_product(a, b);
    let sa = a.size();
    let sb = b.size();
    let cs = b.cosize_nonneg() as int;

    lemma_raked_product_valid(a, b);
    lemma_raked_product_size(a, b);
    lemma_shape_size_positive(a.shape);
    lemma_shape_size_positive(b.shape);

    assert forall|x1: nat, x2: nat|
        x1 < p.size() && x2 < p.size() && x1 != x2
    implies
        #[trigger] p.offset(x1) != #[trigger] p.offset(x2)
    by {
        assert(x1 < sa * sb);
        assert(x2 < sa * sb);

        lemma_raked_product_offset(a, b, x1);
        lemma_raked_product_offset(a, b, x2);

        let r1 = x1 % sa;
        let q1 = x1 / sa;
        let r2 = x2 % sa;
        let q2 = x2 / sa;

        crate::proof::integer_helpers::lemma_mod_bound(x1, sa);
        crate::proof::integer_helpers::lemma_mod_bound(x2, sa);
        crate::proof::integer_helpers::lemma_div_upper_bound(x1, sa, sb);
        crate::proof::integer_helpers::lemma_div_upper_bound(x2, sa, sb);

        // A.offset(r) in [0, cosize(A))
        crate::proof::offset_lemmas::lemma_offset_nonneg(*a, r1);
        crate::proof::offset_lemmas::lemma_offset_nonneg(*a, r2);
        crate::proof::offset_lemmas::lemma_offset_upper_bound(*a, r1);
        crate::proof::offset_lemmas::lemma_offset_upper_bound(*a, r2);

        // B.offset(q) >= 0
        crate::proof::offset_lemmas::lemma_offset_nonneg(*b, q1);
        crate::proof::offset_lemmas::lemma_offset_nonneg(*b, q2);
        // B.offset(q) < cosize(B)
        crate::proof::offset_lemmas::lemma_offset_upper_bound(*b, q1);
        crate::proof::offset_lemmas::lemma_offset_upper_bound(*b, q2);

        crate::proof::integer_helpers::lemma_div_mod_identity(x1, sa);
        crate::proof::integer_helpers::lemma_div_mod_identity(x2, sa);

        let oa1 = a.offset(r1);
        let oa2 = a.offset(r2);
        let ob1 = b.offset(q1);
        let ob2 = b.offset(q2);

        // p.offset(x) = cs * a.offset(r) + b.offset(q)
        // If equal: cs * oa1 + ob1 == cs * oa2 + ob2
        // ob1 - ob2 == cs * (oa2 - oa1)
        // |ob1 - ob2| < cs (since both in [0, cs))
        // So oa1 == oa2, then ob1 == ob2

        if p.offset(x1) == p.offset(x2) {
            assert(cs * oa1 + ob1 == cs * oa2 + ob2);

            if cs == 0 {
                crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(*b);
                assert(false); // cosize >= 1
            }

            let diff = ob1 - ob2;
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub(cs, oa2, oa1);
            assert(cs * oa2 - cs * oa1 == cs * (oa2 - oa1));
            assert(diff == cs * (oa2 - oa1));

            assert(-cs < diff);
            assert(diff < cs);

            if oa2 - oa1 > 0 {
                vstd::arithmetic::mul::lemma_mul_inequality(1, oa2 - oa1, cs);
                vstd::arithmetic::mul::lemma_mul_basics(cs);
                vstd::arithmetic::mul::lemma_mul_is_commutative(oa2 - oa1, cs);
                assert(cs * (oa2 - oa1) >= cs);
                assert(false);
            } else if oa2 - oa1 < 0 {
                vstd::arithmetic::mul::lemma_mul_inequality(1, oa1 - oa2, cs);
                vstd::arithmetic::mul::lemma_mul_basics(cs);
                assert(cs * (oa1 - oa2) >= cs);
                assert(cs * (oa2 - oa1) == -(cs * (oa1 - oa2))) by (nonlinear_arith)
                    requires cs > 0, oa1 - oa2 > 0;
                assert(diff <= -cs);
                assert(false);
            }
            assert(oa1 == oa2);

            // A injective: oa1 == oa2, r1 != r2 → contradiction
            if r1 != r2 {
                assert(a.offset(r1) != a.offset(r2));
                assert(false);
            }
            assert(r1 == r2);

            assert(ob1 == ob2);
            if q1 != q2 {
                assert(b.offset(q1) != b.offset(q2));
                assert(false);
            }
            assert(q1 == q2);

            assert(x1 == x2);
            assert(false);
        }
    }
}

/// Raked product surjectivity:
/// If A is surjective onto [0, m_a) and B is surjective onto [0, m_b),
/// then raked_product(A, B) is surjective onto [0, m_a * m_b).
pub proof fn lemma_raked_product_surjective(a: &LayoutSpec, b: &LayoutSpec, m_a: nat, m_b: nat)
    requires
        raked_product_admissible(a, b),
        a.non_negative_strides(),
        a.is_surjective_upto(m_a),
        b.is_surjective_upto(m_b),
        m_b == b.cosize_nonneg(),
        m_a > 0,
        m_b > 0,
    ensures
        raked_product(a, b).is_surjective_upto(m_a * m_b),
{
    let p = raked_product(a, b);
    let sa = a.size();
    let sb = b.size();

    lemma_raked_product_size(a, b);
    lemma_raked_product_valid(a, b);
    lemma_shape_size_positive(a.shape);
    lemma_shape_size_positive(b.shape);

    assert forall|k: int| 0 <= k < (m_a * m_b) as int
        implies #[trigger] p.offset_hit(k)
    by {
        // Decompose k = m_b * k_a + k_b where k_a < m_a, k_b < m_b
        let k_b: nat = (k % m_b as int) as nat;
        let k_a: nat = (k / m_b as int) as nat;

        assert(0 <= k_b < m_b);
        crate::proof::integer_helpers::lemma_div_upper_bound(k as nat, m_b, m_a);
        assert(0 <= k_a < m_a);

        // Find witnesses: r < sa with a.offset(r) == k_a
        assert(a.offset_hit(k_a as int));
        let r: nat = choose|r: nat| r < sa && a.offset(r) == k_a as int;
        assert(r < sa && a.offset(r) == k_a as int);

        // q < sb with b.offset(q) == k_b
        assert(b.offset_hit(k_b as int));
        let q: nat = choose|q: nat| q < sb && b.offset(q) == k_b as int;
        assert(q < sb && b.offset(q) == k_b as int);

        let x: nat = r + sa * q;
        assert(x < sa * sb) by (nonlinear_arith)
            requires r < sa, q < sb, sa > 0, x == r + sa * q;

        crate::proof::integer_helpers::lemma_div_mod_decompose(r, q, sa);

        lemma_raked_product_offset(a, b, x);
        assert(p.offset(x) == (m_b as int) * a.offset(r) + b.offset(q));
        assert(p.offset(x) == (m_b as int) * (k_a as int) + (k_b as int));

        crate::proof::integer_helpers::lemma_div_mod_identity(k as nat, m_b);
        assert(p.offset(x) == k);
        assert(x < p.size());
    };
}

/// Raked product bijectivity.
pub proof fn lemma_raked_product_bijective(a: &LayoutSpec, b: &LayoutSpec, m_a: nat, m_b: nat)
    requires
        raked_product_admissible(a, b),
        a.non_negative_strides(),
        a.is_injective(),
        b.is_injective(),
        a.is_surjective_upto(m_a),
        b.is_surjective_upto(m_b),
        m_b == b.cosize_nonneg(),
        m_a > 0,
        m_b > 0,
    ensures
        raked_product(a, b).is_bijective_upto(m_a * m_b),
{
    lemma_raked_product_injective(a, b);
    lemma_raked_product_surjective(a, b, m_a, m_b);
}

/// Product cosize: for non-negative-stride layouts,
/// cosize(product(A, B)) == cosize(A) * cosize(B).
pub proof fn lemma_product_cosize(a: &LayoutSpec, b: &LayoutSpec)
    requires
        product_admissible(a, b),
        a.non_negative_strides(),
        b.non_negative_strides(),
    ensures
        logical_product(a, b).non_negative_strides(),
        logical_product(a, b).cosize_nonneg() == a.cosize_nonneg() * b.cosize_nonneg(),
{
    let p = logical_product(a, b);
    let ca = a.cosize_nonneg();
    let cb = b.cosize_nonneg();

    lemma_product_valid(a, b);

    // Product has non-negative strides:
    // First part: A strides (unchanged, non-negative by hypothesis)
    // Second part: B strides scaled by cosize(A) (non-neg * non-neg)
    assert(p.non_negative_strides()) by {
        assert forall|i: int| 0 <= i < p.stride.len() implies #[trigger] p.stride[i] >= 0
        by {
            if i < a.stride.len() as int {
                assert(p.stride[i] == a.stride[i]);
            } else {
                let j = i - a.stride.len() as int;
                assert(p.stride[i] == b.stride[j] * (ca as int));
                assert(b.stride[j] >= 0);
                assert(ca as int >= 0);
                assert(b.stride[j] * (ca as int) >= 0) by (nonlinear_arith)
                    requires b.stride[j] >= 0, ca as int >= 0;
            }
        };
    };

    // cosize = max offset + 1
    // max offset of product = max_A + cosize_A * max_B
    // cosize = max_A + cosize_A * max_B + 1
    //        = (cosize_A - 1) + cosize_A * (cosize_B - 1) + 1
    //        = cosize_A * cosize_B
    crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(*a);
    crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(*b);
    crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(p);

    // For the product: dot_product(shape_minus_one(p.shape), p.stride) + 1
    // = dot_product(smo_a ++ smo_b, stride_a ++ scale(stride_b, ca)) + 1
    // = dot(smo_a, stride_a) + dot(smo_b, scale(stride_b, ca)) + 1
    // = (ca - 1) + ca * dot(smo_b, stride_b) + 1
    // = ca * (dot(smo_b, stride_b) + 1)
    // = ca * cb

    let smo_a = shape_minus_one(a.shape);
    let smo_b = shape_minus_one(b.shape);
    let smo_p = shape_minus_one(p.shape);

    // shape_minus_one distributes over concat
    crate::runtime::layout::lemma_shape_minus_one_len(p.shape);
    crate::runtime::layout::lemma_shape_minus_one_len(a.shape);
    crate::runtime::layout::lemma_shape_minus_one_len(b.shape);

    assert(smo_p =~= smo_a.add(smo_b)) by {
        assert(p.shape =~= a.shape.add(b.shape));
        assert forall|i: int| 0 <= i < smo_p.len() implies smo_p[i] == smo_a.add(smo_b)[i]
        by {
            crate::runtime::layout::lemma_shape_minus_one_index(p.shape, i as nat);
            if i < a.shape.len() as int {
                crate::runtime::layout::lemma_shape_minus_one_index(a.shape, i as nat);
                assert(p.shape[i] == a.shape[i]);
            } else {
                let j = i - a.shape.len() as int;
                crate::runtime::layout::lemma_shape_minus_one_index(b.shape, j as nat);
                assert(p.shape[i] == b.shape[j]);
                assert(smo_a.add(smo_b)[i] == smo_b[j]);
            }
        };
    };

    // Split dot product
    let scaled_b = scale_strides(b.stride, ca as int);
    assert(p.stride =~= a.stride.add(scaled_b));
    assert(smo_a.len() == a.stride.len());
    assert(smo_b.len() == scaled_b.len()) by {
        assert(scaled_b.len() == b.stride.len());
    };

    crate::proof::shape_lemmas::lemma_dot_product_append(smo_a, smo_b, a.stride, scaled_b);

    // dot(smo_b, scale(stride_b, ca)) == ca * dot(smo_b, stride_b)
    lemma_scale_strides_eq(b.stride, ca as int);
    crate::proof::injectivity_lemmas::lemma_dot_product_scale(smo_b, b.stride, ca as int);

    // Now: cosize_p = dot(smo_a, stride_a) + ca * dot(smo_b, stride_b) + 1
    //              = (ca - 1) + ca * (cb - 1) + 1
    //              = ca * cb
    assert(p.cosize_nonneg() == ca * cb) by (nonlinear_arith)
        requires
            p.cosize_nonneg() as int
                == dot_product_nat_int(smo_a, a.stride) + (ca as int) * dot_product_nat_int(smo_b, b.stride) + 1,
            ca as int == dot_product_nat_int(smo_a, a.stride) + 1,
            cb as int == dot_product_nat_int(smo_b, b.stride) + 1,
    {};
}

} // verus!
