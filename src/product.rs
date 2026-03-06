use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

/// Logical product: tile space by replicating A at offsets determined by B.
///
/// Given A (the intra-tile pattern) and B (the inter-tile iterator):
/// result = (A.shape ++ B.shape, A.stride ++ (B.stride * cosize(A)))
///
/// B's strides are scaled by cosize(A) so that each "copy" of A starts
/// at a fresh block of offsets.
pub open spec fn logical_product(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends a.valid(), b.valid(), a.non_negative_strides(),
{
    let cs = a.cosize_nonneg();
    LayoutSpec {
        shape: a.shape.add(b.shape),
        stride: a.stride.add(scale_strides(b.stride, cs as int)),
    }
}

/// Scale every stride in a sequence by a constant factor.
pub open spec fn scale_strides(strides: Seq<int>, factor: int) -> Seq<int> {
    Seq::new(strides.len(), |i: int| strides[i] * factor)
}

/// Admissibility for logical product: both valid, A has non-negative strides,
/// and cosize(A) * cosize(B_scaled) fits in M (if applicable).
pub open spec fn product_admissible(a: &LayoutSpec, b: &LayoutSpec) -> bool {
    &&& a.valid()
    &&& b.valid()
    &&& a.non_negative_strides()
    &&& a.shape.len() > 0
}

} // verus!
