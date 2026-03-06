use vstd::prelude::*;

verus! {

/// A shape is valid if all extents are positive.
pub open spec fn shape_valid(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
}

/// The size (total number of elements) of a shape is the product of extents.
/// Empty shape has size 1 (scalar).
pub open spec fn shape_size(s: Seq<nat>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        1
    } else {
        s.first() * shape_size(s.skip(1))
    }
}

/// Decompose a linear index into per-dimension coordinates (mixed-radix decomposition).
/// Returns a sequence of coordinates, one per dimension.
///
/// coords[0] = idx % s[0]
/// coords[1] = (idx / s[0]) % s[1]
/// coords[i] = (idx / (s[0]*...*s[i-1])) % s[i]
pub open spec fn delinearize(idx: nat, shape: Seq<nat>) -> Seq<nat>
    decreases shape.len(),
{
    if shape.len() == 0 {
        seq![]
    } else {
        seq![idx % shape.first()].add(
            delinearize(idx / shape.first(), shape.skip(1))
        )
    }
}

/// Recompose per-dimension coordinates into a linear index.
///
/// idx = coords[0] + s[0] * (coords[1] + s[1] * (coords[2] + ...))
pub open spec fn linearize(coords: Seq<nat>, shape: Seq<nat>) -> nat
    decreases shape.len(),
{
    if shape.len() == 0 || coords.len() == 0 {
        0
    } else {
        coords.first() + shape.first() * linearize(coords.skip(1), shape.skip(1))
    }
}

/// Dot product of a coordinate sequence (nat) with a stride sequence (int).
/// Returns the memory offset.
pub open spec fn dot_product_nat_int(coords: Seq<nat>, strides: Seq<int>) -> int
    decreases coords.len(),
{
    if coords.len() == 0 || strides.len() == 0 {
        0
    } else {
        (coords.first() as int) * strides.first()
            + dot_product_nat_int(coords.skip(1), strides.skip(1))
    }
}

/// Check that coordinates are in-bounds for a given shape.
pub open spec fn coords_in_bounds(coords: Seq<nat>, shape: Seq<nat>) -> bool {
    &&& coords.len() == shape.len()
    &&& forall|i: int| 0 <= i < coords.len() ==> #[trigger] coords[i] < shape[i]
}

/// Elementwise (shape[i] - 1) for each dimension.
/// Used in cosize computation.
pub open spec fn shape_minus_one(s: Seq<nat>) -> Seq<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![(s.first() - 1) as nat].add(shape_minus_one(s.skip(1)))
    }
}

/// A sequence of n zeros.
pub open spec fn zeros(n: nat) -> Seq<nat>
    decreases n,
{
    if n == 0 {
        seq![]
    } else {
        seq![0nat].add(zeros((n - 1) as nat))
    }
}

} // verus!
