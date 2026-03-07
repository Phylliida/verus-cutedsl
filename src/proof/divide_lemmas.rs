use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::composition::*;
use crate::divide::*;
use crate::proof::shape_lemmas::*;
use crate::proof::complement_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Helper: compose preserves rank (number of modes)
// ══════════════════════════════════════════════════════════════

/// compose(A, B) has exactly rank(B) modes.
pub proof fn lemma_compose_rank(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(),
    ensures
        compose(a, b).shape.len() == b.shape.len(),
        compose(a, b).stride.len() == b.shape.len(),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
    } else if b.shape.len() == 1 {
        // compose_single_mode returns 1-mode layout
    } else {
        let first = compose_single_mode(a, b.shape.first(), b.stride.first() as nat);
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        lemma_compose_rank(a, rest_b);
        // first has 1 mode, rest has b.shape.len() - 1 modes
        // total: 1 + (b.shape.len() - 1) = b.shape.len()
    }
}

// ══════════════════════════════════════════════════════════════
// Logical divide: structural properties
// ══════════════════════════════════════════════════════════════

/// The logical divide of A by B has rank = rank(B) + rank(complement(B, size(A))).
pub proof fn lemma_divide_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        let expected_rank = b.shape.len() + c.shape.len();
        &&& logical_divide(a, b).shape.len() == expected_rank
        &&& logical_divide(a, b).stride.len() == expected_rank
    })),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    lemma_complement_rank(b, m);

    // Need zipped.valid() for compose_rank precondition
    lemma_complement_shape_valid(b, m);

    assert(shape_valid(zipped.shape)) by {
        assert forall|i: int| 0 <= i < zipped.shape.len() implies #[trigger] zipped.shape[i] > 0 by {
            if i < b.shape.len() as int {
                assert(zipped.shape[i] == b.shape[i]);
            } else {
                let ci = (i - b.shape.len()) as int;
                assert(zipped.shape[i] == c.shape[ci]);
            }
        };
    };
    assert(zipped.shape.len() == zipped.stride.len());

    lemma_compose_rank(a_val, zipped);
}

/// For a 1D tile B, logical_divide produces rank(B) + rank(B) + 1 = rank(B) + 2 modes.
/// (complement of 1D B has rank 2)
pub proof fn lemma_divide_1d_tile_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        b.shape.len() == 1,
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        &&& logical_divide(a, b).shape.len() == 3
        &&& logical_divide(a, b).stride.len() == 3
    })),
{
    let m = shape_size(a.shape);
    lemma_complement_rank(b, m);
    lemma_divide_rank(a, b);
}

// ══════════════════════════════════════════════════════════════
// Tile count: complement size gives number of tiles
// ══════════════════════════════════════════════════════════════

/// For a 1D tile, complement size * tile size == total size.
pub proof fn lemma_divide_tile_count_1d(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        b.shape.len() == 1,
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        shape_size(c.shape) * shape_size(b.shape) == m
    })),
{
    let m = shape_size(a.shape);
    lemma_complement_size_1d(b, m);
}

// ══════════════════════════════════════════════════════════════
// Divide size preservation
// ══════════════════════════════════════════════════════════════

/// logical_divide(A, B) has the same size as A.
pub proof fn lemma_divide_size(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures
        shape_size(logical_divide(a, b).shape) == shape_size(a.shape),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped is valid
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    assert(shape_valid(zipped.shape)) by {
        assert forall|i: int| 0 <= i < zipped.shape.len()
        implies #[trigger] zipped.shape[i] > 0 by {
            if i < b.shape.len() as int {
                assert(zipped.shape[i] == b.shape[i]);
            } else {
                assert(zipped.shape[i] == c.shape[(i - b.shape.len()) as int]);
            }
        };
    };
    assert(zipped.valid());

    // compose(a, zipped).shape =~= zipped.shape
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, zipped);

    // size(zipped.shape) = size(b.shape ++ c.shape) = size(b.shape) * size(c.shape)
    crate::proof::product_lemmas::lemma_shape_size_append(b.shape, c.shape);

    // size(c.shape) * size(b.shape) = m
    lemma_complement_size(b, m);

    // So size(zipped.shape) = size(b.shape) * size(c.shape) = m = size(a.shape)
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(b.shape) as int,
        shape_size(c.shape) as int,
    );
}

/// Generalized tile count: complement size * tile size == total size.
pub proof fn lemma_divide_tile_count(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures ({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        shape_size(c.shape) * shape_size(b.shape) == m
    }),
{
    let m = shape_size(a.shape);
    lemma_complement_size(b, m);
}

} // verus!
