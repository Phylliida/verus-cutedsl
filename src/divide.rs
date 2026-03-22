use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::composition::*;

verus! {

/// Admissibility condition for logical_divide_linear: B must be complement-admissible w.r.t. size(A),
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
/// DEPRECATED: Only correct for rank-1 A or column-major A. Uses `compose_linear` which
/// can't handle mode boundary crossings. For general A, use `logical_divide`
/// (CuTe-style recursive composition) or `logical_divide_mode` (first-mode division).
///
/// Formally: logical_divide_linear(A, B) = compose_linear(A, (B, complement(B, size(A))))
pub open spec fn logical_divide_linear(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
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
    compose_linear(a_val, zipped)
}

/// The tile part of logical_divide_linear: just A ∘ B.
pub open spec fn divide_tile(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends a.valid(), b.valid(),
{
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let b_val = LayoutSpec { shape: b.shape, stride: b.stride };
    compose_linear(a_val, b_val)
}

/// The rest part of logical_divide_linear: A ∘ complement(B, size(A)).
pub open spec fn divide_rest(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends divide_admissible(a, b),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    compose_linear(a_val, c)
}

/// The number of tiles: size(A) / size(B).
pub open spec fn num_tiles(a: &LayoutSpec, b: &LayoutSpec) -> nat
    recommends divide_admissible(a, b),
{
    shape_size(a.shape) / shape_size(b.shape)
}

/// DEPRECATED: Use `logical_divide` instead.
///
/// This was an intermediate attempt that uses `compose_extended`, which only
/// handles prefix-product-aligned strides and falls back incorrectly for others.
/// `logical_divide` uses the fully correct `compose`.
pub open spec fn logical_divide_extended(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends divide_admissible(a, b),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    compose_extended(a_val, zipped)
}

/// Convenience: divide A's first mode by N directly (no complement/compose).
///
/// This is a fast-path for the common case of rank-1 B = (N):(1) with N | M_0.
/// It directly constructs the correct result without going through `compose_single`:
///   shape:  (N, M_0/N, M_1, M_2, ...)
///   stride: (d_0, N*d_0, d_1, d_2, ...)
///
/// Use `logical_divide` for the general case (arbitrary B, arbitrary mode crossing).
/// This function is equivalent to `logical_divide` for rank-1 B within the first mode
/// but has a simpler proof (no admissibility predicate needed).
///
/// Offset correctness proved: lemma_divide_mode_offset.
pub open spec fn logical_divide_mode(a: &LayoutSpec, n: nat) -> LayoutSpec
    recommends
        a.valid(),
        a.shape.len() > 0,
        n > 0,
        a.shape.first() % n == 0,
{
    let m0 = a.shape.first();
    let d0 = a.stride.first();
    LayoutSpec {
        shape: seq![n, m0 / n].add(a.shape.skip(1)),
        stride: seq![d0, (n as int) * d0].add(a.stride.skip(1)),
    }
}

/// Admissibility for logical_divide_mode.
pub open spec fn divide_mode_admissible(a: &LayoutSpec, n: nat) -> bool {
    &&& a.valid()
    &&& a.shape.len() > 0
    &&& n > 0
    &&& a.shape.first() % n == 0
}

/// CuTe-style logical divide using recursive composition.
///
/// Unlike `logical_divide_linear` (which uses `compose_linear` — only correct for rank-1/column-major A)
/// and `logical_divide_extended` (which uses `compose_extended` — same limitation),
/// this uses `compose` which correctly handles mode boundary crossings.
///
/// `compose_single` has been formally proved correct:
///   compose_single(A, N, r).offset(x) == A.offset(r * x)
/// for all admissible inputs (see `compose_single_admissible`).
///
/// The divide is: compose(A, (B, complement(B, size(A)))).
pub open spec fn logical_divide(a: &LayoutSpec, b: &LayoutSpec) -> LayoutSpec
    recommends divide_admissible(a, b),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    compose(a_val, zipped)
}

} // verus!
