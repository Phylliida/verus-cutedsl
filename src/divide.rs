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

/// Extended logical divide: uses compose_extended instead of compose.
///
/// WARNING: This is NOT a general fix for multi-rank non-column-major A.
/// When B is rank-1 and the complement's stride doesn't match a prefix product
/// of A, compose_extended falls back to the same incorrect stride as compose.
/// For correct multi-rank divide with rank-1 B, use `logical_divide_mode` instead.
///
/// This function IS correct for:
/// - Rank-1 A (compose_extended == compose, both correct)
/// - Column-major A (all strides are prefix products, fallback is correct)
/// - Multi-rank B whose strides all match prefix products of A
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

/// Mode-aware logical divide: correctly partitions A's first mode by B.
///
/// For rank-1 B = (N):(1) with N dividing A.shape[0], this divides A's first
/// mode into tiles of size N, keeping higher modes unchanged:
///   shape:  (N, M_0/N, M_1, M_2, ...)
///   stride: (d_0, N*d_0, d_1, d_2, ...)
///
/// Unlike `logical_divide` and `logical_divide_extended`, this correctly handles
/// non-column-major multi-rank A because it respects A's mode boundaries.
///
/// Example showing the difference:
///   A = (4, 3):(1, 10), B = (2):(1)
///   logical_divide:          uses complement(B, 12) = (1, 6):(1, 2), gets wrong strides
///   logical_divide_mode:     (2, 2, 3):(1, 2, 10) — correct! offset(x) == A.offset(x)
///
/// The first two modes (N, M_0/N):(d_0, N*d_0) reconstruct A's first mode via
/// mixed-radix decomposition: x%N indexes within a tile, (x/N)%(M_0/N) indexes
/// across tiles, and x%N + N*((x/N)%(M_0/N)) == x%M_0 by the mod-mod identity.
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

} // verus!
