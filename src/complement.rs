use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

/// Admissibility condition for complement: the layout must be sorted with non-negative strides
/// and satisfy the tractability (divisibility chain) condition, and M must be divisible by the
/// last mode's stride * shape product.
pub open spec fn complement_admissible(a: &LayoutSpec, m: nat) -> bool {
    &&& a.valid()
    &&& a.non_negative_strides()
    &&& a.is_sorted()
    &&& a.is_tractable()
    &&& m > 0
    &&& a.shape.len() > 0
    // d_0 must be positive (first stride)
    &&& a.stride[0] > 0
    // M divisible by (M_k * d_k)
    &&& (m as int) % ((a.shape.last() as int) * a.stride.last()) == 0
}

/// The "stride product" at mode i: M_i * d_i.
/// This is the key building block of the complement formula.
pub open spec fn stride_product(a: &LayoutSpec, i: int) -> int
    recommends a.valid(), 0 <= i < a.shape.len(),
{
    (a.shape[i] as int) * a.stride[i]
}

/// Complement of layout A with respect to target size M.
///
/// Shape: (d_0, d_1/(M_0*d_0), d_2/(M_1*d_1), ..., M/(M_k*d_k))
/// Stride: (1, M_0*d_0, M_1*d_1, ..., M_k*d_k)
///
/// The complement's modes fill in the "gaps" between A's stride products.
pub open spec fn complement(a: &LayoutSpec, m: nat) -> LayoutSpec
    recommends complement_admissible(a, m),
{
    let k = a.shape.len();
    LayoutSpec {
        shape: complement_shape(a, m),
        stride: complement_stride(a),
    }
}

/// Build the complement shape sequence.
/// Entry 0: d_0 (the first stride -- gap before first mode)
/// Entry i (0 < i < k): d_i / (M_{i-1} * d_{i-1}) (gap between mode i-1 and i)
/// Entry k: M / (M_{k-1} * d_{k-1}) (gap after last mode)
pub open spec fn complement_shape(a: &LayoutSpec, m: nat) -> Seq<nat>
    recommends complement_admissible(a, m),
{
    let k = a.shape.len();
    Seq::new(
        k + 1,
        |i: int|
            if i == 0 {
                a.stride[0] as nat
            } else if i < k {
                (a.stride[i] / stride_product(a, i - 1)) as nat
            } else {
                // i == k: M / (M_{k-1} * d_{k-1})
                ((m as int) / stride_product(a, k - 1)) as nat
            }
    )
}

/// Build the complement stride sequence.
/// Entry 0: 1
/// Entry i (0 < i <= k): M_{i-1} * d_{i-1} = stride_product(a, i-1)
pub open spec fn complement_stride(a: &LayoutSpec) -> Seq<int>
    recommends a.valid(), a.shape.len() > 0,
{
    let k = a.shape.len();
    Seq::new(
        k + 1,
        |i: int|
            if i == 0 {
                1int
            } else {
                stride_product(a, i - 1)
            }
    )
}

} // verus!
