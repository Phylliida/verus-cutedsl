use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::product::*;
use crate::proof::shape_lemmas::*;

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

} // verus!
