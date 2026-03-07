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

    /// Tractability at a single mode: (M_i * d_i) > 0 and divides d_{i+1}.
    pub open spec fn tractable_at(&self, i: int) -> bool {
        let product = (self.shape[i] as int) * self.stride[i];
        product > 0 && self.stride[i + 1] % product == 0
    }

    /// Tractability: for adjacent modes, (M_i * d_i) divides d_{i+1}.
    /// Required for complement admissibility.
    pub open spec fn is_tractable(&self) -> bool {
        forall|i: int| 0 <= i < self.stride.len() as int - 1 ==>
            #[trigger] self.tractable_at(i)
    }

    // ══════════════════════════════════════════════════════════════
    // Injectivity and surjectivity
    // ══════════════════════════════════════════════════════════════

    /// A layout is injective (no aliasing) when distinct indices map to distinct offsets.
    pub open spec fn is_injective(&self) -> bool {
        forall|i: nat, j: nat|
            i < self.size() && j < self.size() && i != j ==>
                #[trigger] self.offset(i) != #[trigger] self.offset(j)
    }

    /// Whether offset k is in the image of this layout.
    pub open spec fn offset_hit(&self, k: int) -> bool {
        exists|i: nat| i < self.size() && #[trigger] self.offset(i) == k
    }

    /// A layout is surjective onto [0, m): every offset in range is hit.
    pub open spec fn is_surjective_upto(&self, m: nat) -> bool {
        forall|k: int| 0 <= k < m as int ==> #[trigger] self.offset_hit(k)
    }

    /// A layout is bijective onto [0, m): injective + surjective.
    pub open spec fn is_bijective_upto(&self, m: nat) -> bool {
        self.is_injective() && self.is_surjective_upto(m)
    }
}

// ══════════════════════════════════════════════════════════════
// Standard layout constructors
// ══════════════════════════════════════════════════════════════

/// Column-major strides: (1, M_0, M_0*M_1, ..., M_0*...*M_{k-2}).
pub open spec fn column_major_strides(shape: Seq<nat>) -> Seq<int>
    decreases shape.len(),
{
    if shape.len() == 0 {
        seq![]
    } else {
        seq![1int].add(
            scale_strides_spec(
                column_major_strides(shape.skip(1)),
                shape.first() as int,
            )
        )
    }
}

/// Scale all strides by a factor.
pub open spec fn scale_strides_spec(strides: Seq<int>, factor: int) -> Seq<int> {
    Seq::new(strides.len(), |i: int| strides[i] * factor)
}

/// Construct a column-major layout from a shape.
pub open spec fn make_column_major(shape: Seq<nat>) -> LayoutSpec {
    LayoutSpec { shape, stride: column_major_strides(shape) }
}

/// Construct an identity layout (M):(1).
pub open spec fn make_identity(m: nat) -> LayoutSpec {
    LayoutSpec { shape: seq![m], stride: seq![1int] }
}

/// Reverse a sequence.
pub open spec fn seq_reverse<A>(s: Seq<A>) -> Seq<A> {
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
}

/// Row-major strides: (..., M_{k-2}*M_{k-1}, M_{k-1}, 1).
/// Defined as the reverse of column-major strides of the reversed shape.
pub open spec fn row_major_strides(shape: Seq<nat>) -> Seq<int> {
    seq_reverse(column_major_strides(seq_reverse(shape)))
}

/// Construct a row-major layout from a shape.
pub open spec fn make_row_major(shape: Seq<nat>) -> LayoutSpec {
    LayoutSpec { shape, stride: row_major_strides(shape) }
}

} // verus!
