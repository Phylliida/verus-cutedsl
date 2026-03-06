use vstd::prelude::*;
use crate::shape::*;

verus! {

/// A layout maps logical indices to memory offsets via (shape, stride) pairs.
///
/// For a layout with shape S = (M_0, ..., M_{k-1}) and stride D = (d_0, ..., d_{k-1}),
/// the offset of linear index x is:
///   offset(x) = sum_i (delinearize(x, S)[i] * D[i])
pub struct LayoutSpec {
    pub shape: Seq<nat>,
    pub stride: Seq<int>,
}

impl LayoutSpec {
    /// A layout is valid if the shape is valid and shape/stride have equal length.
    pub open spec fn valid(&self) -> bool {
        &&& shape_valid(self.shape)
        &&& self.shape.len() == self.stride.len()
    }

    /// Number of elements in the layout's domain.
    pub open spec fn size(&self) -> nat {
        shape_size(self.shape)
    }

    /// Number of dimensions.
    pub open spec fn rank(&self) -> nat {
        self.shape.len()
    }

    /// Compute the memory offset for a given linear index.
    pub open spec fn offset(&self, idx: nat) -> int
        recommends self.valid(), idx < self.size(),
    {
        dot_product_nat_int(delinearize(idx, self.shape), self.stride)
    }

    /// All strides are non-negative.
    pub open spec fn non_negative_strides(&self) -> bool {
        forall|i: int| 0 <= i < self.stride.len() ==> #[trigger] self.stride[i] >= 0
    }

    /// Cosize: minimum codomain size needed (max offset + 1).
    /// Only well-defined for non-negative strides.
    pub open spec fn cosize_nonneg(&self) -> nat
        recommends self.valid(), self.non_negative_strides(),
        decreases self.shape.len(),
    {
        if self.shape.len() == 0 {
            1
        } else {
            let rest = LayoutSpec {
                shape: self.shape.skip(1),
                stride: self.stride.skip(1),
            };
            ((self.shape.first() - 1) * (self.stride.first() as nat) + rest.cosize_nonneg()) as nat
        }
    }

    /// Strides are sorted (non-decreasing). Required for complement.
    pub open spec fn is_sorted(&self) -> bool {
        forall|i: int, j: int| 0 <= i < j < self.stride.len() ==>
            #[trigger] self.stride[i] <= #[trigger] self.stride[j]
    }

    /// Tractability: for adjacent modes, (M_i * d_i) divides d_{i+1}.
    /// Required for complement admissibility.
    pub open spec fn is_tractable(&self) -> bool {
        forall|i: int| 0 <= i < self.stride.len() as int - 1 ==> {
            let product = (self.shape[i] as int) * self.stride[i];
            product > 0 && #[trigger] self.stride[i + 1] % product == 0
        }
    }
}

} // verus!
