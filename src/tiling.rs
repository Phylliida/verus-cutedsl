use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::divide::*;
use crate::product::*;
use crate::slice::*;
use crate::predication::*;

verus! {

/// A divided layout tracks which modes are tile (intra-tile) vs rest (inter-tile).
/// Modes [0, tile_rank) index within a tile; modes [tile_rank, total_rank) iterate across tiles.
pub struct DividedLayout {
    pub layout: LayoutSpec,
    pub tile_rank: nat,
}

/// Admissibility for a DividedLayout: tile_rank must be within bounds.
pub open spec fn divided_layout_valid(d: &DividedLayout) -> bool {
    &&& d.layout.valid()
    &&& d.tile_rank <= d.layout.shape.len()
}

/// Zipped divide: partition A's index space into tiles of shape B.
/// Returns a DividedLayout where:
///   - tile modes (0..B.rank): index within each tile
///   - rest modes (B.rank..): iterate across tiles
pub open spec fn zipped_divide(a: &LayoutSpec, b: &LayoutSpec) -> DividedLayout
    recommends divide_admissible(a, b),
{
    DividedLayout {
        layout: logical_divide(a, b),
        tile_rank: b.shape.len(),
    }
}

/// Tile shape: the first tile_rank modes of a DividedLayout.
pub open spec fn tile_shape(d: &DividedLayout) -> Seq<nat>
    recommends divided_layout_valid(d),
{
    d.layout.shape.take(d.tile_rank as int)
}

/// Rest shape: the modes after tile_rank in a DividedLayout.
pub open spec fn rest_shape(d: &DividedLayout) -> Seq<nat>
    recommends divided_layout_valid(d),
{
    d.layout.shape.skip(d.tile_rank as int)
}

/// Number of elements per tile.
pub open spec fn tile_size(d: &DividedLayout) -> nat
    recommends divided_layout_valid(d),
{
    shape_size(tile_shape(d))
}

/// Number of tiles.
pub open spec fn num_tiles_divided(d: &DividedLayout) -> nat
    recommends divided_layout_valid(d),
{
    shape_size(rest_shape(d))
}

/// Make a tiled copy plan.
/// Given:
///   - atom: the atomic copy pattern (e.g., a single element or a vector load)
///   - thr_layout: thread distribution pattern
///   - val_layout: per-thread value pattern
///
/// The result is raked_product(atom, logical_product(thr_layout, val_layout)).
/// This distributes work across threads with each thread handling multiple values.
pub open spec fn make_tiled_copy(
    atom: &LayoutSpec,
    thr_layout: &LayoutSpec,
    val_layout: &LayoutSpec,
) -> LayoutSpec
    recommends
        atom.valid(),
        thr_layout.valid(),
        val_layout.valid(),
        thr_layout.non_negative_strides(),
{
    let tv = logical_product(thr_layout, val_layout);
    raked_product(atom, &tv)
}

/// Admissibility for make_tiled_copy.
pub open spec fn tiled_copy_admissible(
    atom: &LayoutSpec,
    thr_layout: &LayoutSpec,
    val_layout: &LayoutSpec,
) -> bool {
    &&& atom.valid()
    &&& thr_layout.valid()
    &&& val_layout.valid()
    &&& thr_layout.non_negative_strides()
    &&& thr_layout.shape.len() > 0
    // TV product must have non-negative strides for raked_product
    &&& logical_product(thr_layout, val_layout).non_negative_strides()
    &&& logical_product(thr_layout, val_layout).shape.len() > 0
}

/// Local partition: extract one thread's portion from a tiled tensor.
/// Given:
///   - tensor: the full divided tensor layout
///   - tv_layout: the thread×value layout (from make_tiled_copy)
///   - thread_id: this thread's ID
///
/// Returns (residual_layout, base_offset):
///   - residual_layout: layout for this thread's elements
///   - base_offset: constant offset to add for this thread
pub open spec fn local_partition(
    tensor: &DividedLayout,
    tv_layout: &LayoutSpec,
    thread_id: nat,
) -> (LayoutSpec, int)
    recommends
        divided_layout_valid(tensor),
        tv_layout.valid(),
        thread_id < tv_layout.shape.first(),
{
    // Slice the first mode of the divided layout at the thread coordinate
    (
        slice_layout(&tensor.layout, 0, thread_id),
        slice_offset(&tensor.layout, 0, thread_id),
    )
}

// ══════════════════════════════════════════════════════════════
// Predicated divide: pad to next multiple, then tile
// ══════════════════════════════════════════════════════════════

/// Predicated divide: pad tensor to next multiple of tile_size, then tile.
/// Returns a DividedLayout where tile modes index within each tile,
/// and rest modes iterate across tiles (including potential padding tiles).
pub open spec fn predicated_divide(original_size: nat, tile_size: nat) -> DividedLayout
    recommends padded_divide_admissible(original_size, tile_size),
{
    let padded = padded_size(original_size, tile_size);
    let a = make_identity(padded);
    let b = make_identity(tile_size);
    zipped_divide(&a, &b)
}

} // verus!
