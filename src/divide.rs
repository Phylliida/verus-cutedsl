use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::composition::*;

verus! {

/// Admissibility condition for logical_divide: B must be complement-admissible w.r.t. size(A),
/// and the composition A ∘ (B, complement(B, size(A))) must be well-formed.
pub open spec fn divide_admissible(a: &LayoutSpec, b: &LayoutSpec) -> bool {
    &&& a.valid()
    &&& b.valid()
    &&& a.shape.len() > 0
    &&& b.shape.len() > 0
    // B must be complement-admissible w.r.t. size(A)
    &&& complement_admissible(b, shape_size(a.shape))
}

/// Logical divide: partition A's index space into tiles of shape B.
///
/// Result has two groups of modes:
/// - "Tile" modes (from B): indices within a single tile
/// - "Rest" modes (from complement(B, size(A))): iterates across tiles
///
/// Formally: logical_divide(A, B) = A ∘ (B, complement(B, size(A)))
pub open spec fn logical_divide(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends divide_admissible(a, b),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    // Build the "zipped" operand: (B, complement(B, M))
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    compose(a_val, zipped)
}

/// The tile part of logical_divide: just A ∘ B.
pub open spec fn divide_tile(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends a.valid(), b.valid(),
{
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let b_val = LayoutSpec { shape: b.shape, stride: b.stride };
    compose(a_val, b_val)
}

/// The rest part of logical_divide: A ∘ complement(B, size(A)).
pub open spec fn divide_rest(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends divide_admissible(a, b),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    compose(a_val, c)
}

/// The number of tiles: size(A) / size(B).
pub open spec fn num_tiles(a: &LayoutSpec, b: &LayoutSpec) -> nat
    recommends divide_admissible(a, b),
{
    shape_size(a.shape) / shape_size(b.shape)
}

} // verus!
