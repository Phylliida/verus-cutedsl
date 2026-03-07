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
    // x == size_a * (x / size_a) + x % size_a == size_a * (x / size_a) + x
    // => size_a * (x / size_a) == 0 => x / size_a == 0
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, size_a as int);
    assert(x as int == size_a as int * (x as int / size_a as int) + x as int);
    assert(size_a as int * (x as int / size_a as int) == 0int);
    assert(x / size_a == 0nat);

    lemma_product_offset(a, b, x);
    // product(a,b).offset(x) == a.offset(x) + cosize(a) * b.offset(0)

    // b.offset(0) == 0
    crate::proof::offset_lemmas::lemma_offset_zero(
        LayoutSpec { shape: b.shape, stride: b.stride },
    );
    // cosize(a) * 0 == 0
    vstd::arithmetic::mul::lemma_mul_basics(a.cosize_nonneg() as int);
}

} // verus!
