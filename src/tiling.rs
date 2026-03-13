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

// ══════════════════════════════════════════════════════════════
// Copy atom specs
// ══════════════════════════════════════════════════════════════

/// A copy atom is a rank-1, contiguous, stride-1 layout of `access_width` elements.
/// Models CuTe's Copy_Atom: the smallest unit of a vectorized memory access.
pub open spec fn copy_atom_valid(atom: &LayoutSpec, access_width: nat) -> bool {
    &&& atom.valid()
    &&& atom.rank() == 1
    &&& atom.shape[0] == access_width
    &&& atom.stride[0] == 1
}

/// An offset is aligned to `access_width` if it is a multiple.
pub open spec fn access_aligned(offset: int, access_width: nat) -> bool
    recommends access_width > 0,
{
    offset % (access_width as int) == 0
}

// ══════════════════════════════════════════════════════════════
// Nested partition specs
// ══════════════════════════════════════════════════════════════

/// Two-level partition: slice layout first with id1 (outer), then with id2 (inner).
/// Returns (inner_layout, total_base_offset).
///
/// Models block→warp or warp→thread partitioning.
pub open spec fn nested_local_partition(
    tensor: &LayoutSpec,
    id1: nat,
    id2: nat,
) -> (LayoutSpec, int)
    recommends
        tensor.valid(),
        tensor.rank() >= 2,
        id1 < tensor.shape[0],
        id2 < slice_layout(tensor, 0, id1).shape[0],
{
    let residual1 = slice_layout(tensor, 0, id1);
    let off1 = slice_offset(tensor, 0, id1);
    let inner = slice_layout(&residual1, 0, id2);
    let off2 = slice_offset(&residual1, 0, id2);
    (inner, off1 + off2)
}

// ══════════════════════════════════════════════════════════════
// MMA atom layouts
// ══════════════════════════════════════════════════════════════

/// Thread-value layout for an MMA atom: logical_product(thr, val).
pub open spec fn mma_atom_layout(
    thr_shape: Seq<nat>, thr_stride: Seq<int>,
    val_shape: Seq<nat>, val_stride: Seq<int>,
) -> LayoutSpec {
    let thr = LayoutSpec { shape: thr_shape, stride: thr_stride };
    let val = LayoutSpec { shape: val_shape, stride: val_stride };
    logical_product(&thr, &val)
}

/// Admissibility for MMA atom TV layout.
pub open spec fn mma_atom_admissible(thr: &LayoutSpec, val: &LayoutSpec) -> bool {
    &&& thr.valid()
    &&& val.valid()
    &&& thr.non_negative_strides()
    &&& val.non_negative_strides()
    &&& thr.is_injective()
    &&& val.is_injective()
    &&& thr.shape.len() > 0
}

/// MMA-specific alias for make_tiled_copy.
pub open spec fn mma_tiled_copy(
    atom: &LayoutSpec, thr: &LayoutSpec, val: &LayoutSpec,
) -> LayoutSpec
    recommends tiled_copy_admissible(atom, thr, val),
{
    make_tiled_copy(atom, thr, val)
}

// ══════════════════════════════════════════════════════════════
// GEMM partition specs
// ══════════════════════════════════════════════════════════════

/// CTA-level tiling for GEMM: tile each dimension independently.
pub open spec fn gemm_partition(
    m_size: nat, n_size: nat, k_size: nat,
    bm: nat, bn: nat, bk: nat,
) -> (DividedLayout, DividedLayout, DividedLayout)
    recommends
        padded_divide_admissible(m_size, bm),
        padded_divide_admissible(n_size, bn),
        padded_divide_admissible(k_size, bk),
{
    (predicated_divide(m_size, bm),
     predicated_divide(n_size, bn),
     predicated_divide(k_size, bk))
}

/// Admissibility for GEMM partition.
pub open spec fn gemm_partition_admissible(
    m_size: nat, n_size: nat, k_size: nat,
    bm: nat, bn: nat, bk: nat,
) -> bool {
    &&& padded_divide_admissible(m_size, bm)
    &&& padded_divide_admissible(n_size, bn)
    &&& padded_divide_admissible(k_size, bk)
}

/// Linearize CTA block ID from (cta_m, cta_n) coordinates.
pub open spec fn gemm_cta_index(cta_m: nat, cta_n: nat, num_m_tiles: nat) -> nat {
    cta_m + cta_n * num_m_tiles
}

// ══════════════════════════════════════════════════════════════
// SM80 MMA Atom Instances (m16n8k16)
// ══════════════════════════════════════════════════════════════

/// SM80 m16n8k16 A-fragment thread layout: 32 threads in 4×8 grid.
pub open spec fn sm80_m16n8k16_thr_a() -> LayoutSpec {
    LayoutSpec { shape: seq![4nat, 8nat], stride: seq![2int, 16int] }
}

/// SM80 m16n8k16 A-fragment value layout: 8 values per thread in 2×4 grid.
pub open spec fn sm80_m16n8k16_val_a() -> LayoutSpec {
    LayoutSpec { shape: seq![2nat, 4nat], stride: seq![1int, 4int] }
}

/// SM80 m16n8k16 B-fragment thread layout: 32 threads in 4×8 grid.
pub open spec fn sm80_m16n8k16_thr_b() -> LayoutSpec {
    LayoutSpec { shape: seq![4nat, 8nat], stride: seq![2int, 16int] }
}

/// SM80 m16n8k16 B-fragment value layout: 4 values per thread in 2×2 grid.
pub open spec fn sm80_m16n8k16_val_b() -> LayoutSpec {
    LayoutSpec { shape: seq![2nat, 2nat], stride: seq![1int, 8int] }
}

/// SM80 m16n8k16 D-fragment (accumulator) thread layout: 32 threads in 4×8 grid.
pub open spec fn sm80_m16n8k16_thr_d() -> LayoutSpec {
    LayoutSpec { shape: seq![4nat, 8nat], stride: seq![2int, 16int] }
}

/// SM80 m16n8k16 D-fragment (accumulator) value layout: 4 values per thread in 2×2 grid.
pub open spec fn sm80_m16n8k16_val_d() -> LayoutSpec {
    LayoutSpec { shape: seq![2nat, 2nat], stride: seq![1int, 8int] }
}

// ══════════════════════════════════════════════════════════════
// Deeper GEMM Pipeline: warp/register partitioning
// ══════════════════════════════════════════════════════════════

/// Partition a CTA tile into warp tiles. warp_count warps each handle a sub-tile.
pub open spec fn warp_partition(
    cta_tile: &DividedLayout,
    warp_layout: &LayoutSpec,
) -> DividedLayout
    recommends
        divided_layout_valid(cta_tile),
        warp_layout.valid(),
        warp_layout.shape.len() > 0,
{
    let divided = zipped_divide(&cta_tile.layout, warp_layout);
    DividedLayout {
        layout: divided.layout,
        tile_rank: warp_layout.shape.len(),
    }
}

/// Partition a warp tile into MMA-atom-sized register tiles.
pub open spec fn register_partition(
    warp_tile: &DividedLayout,
    mma_atom: &LayoutSpec,
) -> DividedLayout
    recommends
        divided_layout_valid(warp_tile),
        mma_atom.valid(),
        mma_atom.shape.len() > 0,
{
    let divided = zipped_divide(&warp_tile.layout, mma_atom);
    DividedLayout {
        layout: divided.layout,
        tile_rank: mma_atom.shape.len(),
    }
}

/// Which buffer slot to use at K-iteration k_iter.
pub open spec fn double_buffer_slot(k_iter: nat, num_buffers: nat) -> nat
    recommends num_buffers > 0,
{
    k_iter % num_buffers
}

/// Admissibility for double buffering.
pub open spec fn double_buffer_admissible(num_k_tiles: nat, num_buffers: nat) -> bool {
    &&& num_buffers > 0
    &&& num_k_tiles > 0
}

// ══════════════════════════════════════════════════════════════
// SM80 MMA Atom Cosize specs
// ══════════════════════════════════════════════════════════════

/// SM80 m16n8k16 thr cosize = 119. max(3*2+7*16)+1 = 118+1.
pub open spec fn sm80_m16n8k16_thr_cosize() -> nat { 119 }

/// SM80 m16n8k16 val_a cosize = 14. max(1*1+3*4)+1 = 13+1.
pub open spec fn sm80_m16n8k16_val_a_cosize() -> nat { 14 }

/// SM80 m16n8k16 val_b cosize = 10. max(1*1+1*8)+1 = 9+1.
pub open spec fn sm80_m16n8k16_val_b_cosize() -> nat { 10 }

/// SM80 m16n8k16 val_d cosize = 10. Same layout as B.
pub open spec fn sm80_m16n8k16_val_d_cosize() -> nat { 10 }

/// MMA atom total storage: cosize(thr) * cosize(val).
pub open spec fn sm80_m16n8k16_a_storage() -> nat { 119 * 14 }  // 1666
pub open spec fn sm80_m16n8k16_b_storage() -> nat { 119 * 10 }  // 1190
pub open spec fn sm80_m16n8k16_d_storage() -> nat { 119 * 10 }  // 1190

/// Offset bound: every valid index maps to an offset in [0, cosize).
pub open spec fn mma_offset_bounded(
    thr: &LayoutSpec, val: &LayoutSpec, cosize: nat,
) -> bool {
    forall|x: nat| #![trigger mma_atom_layout(thr.shape, thr.stride, val.shape, val.stride).offset(x)]
        x < thr.size() * val.size() ==> {
        let layout = mma_atom_layout(thr.shape, thr.stride, val.shape, val.stride);
        &&& layout.offset(x) >= 0
        &&& layout.offset(x) < cosize as int
    }
}

// ══════════════════════════════════════════════════════════════
// Software pipelining specs
// ══════════════════════════════════════════════════════════════

/// Pipeline stage: which stage a K-iteration is in.
pub open spec fn pipeline_stage(k_iter: nat, num_stages: nat) -> nat
    recommends num_stages > 0,
{
    k_iter % num_stages
}

/// WAR hazard free: writer at k_w and reader at k_r use different buffer slots
/// when they are different iterations.
pub open spec fn war_hazard_free(
    k_write: nat, k_read: nat, num_buffers: nat,
) -> bool {
    k_write != k_read ==>
        double_buffer_slot(k_write, num_buffers) != double_buffer_slot(k_read, num_buffers)
}

/// RAW hazard free: data written at k_produce is consumed at k_consume
/// from the same slot (same iteration) or from a different slot.
pub open spec fn raw_hazard_free(
    k_produce: nat, k_consume: nat, num_buffers: nat,
) -> bool {
    k_produce == k_consume
    || double_buffer_slot(k_produce, num_buffers)
       != double_buffer_slot(k_consume, num_buffers)
}

/// N-deep pipeline soundness: for any two K-iterations within the pipeline
/// depth, their buffer slots don't collide.
pub open spec fn pipeline_no_collision(
    num_k_tiles: nat, num_buffers: nat,
) -> bool {
    forall|k1: nat, k2: nat|
        k1 < num_k_tiles && k2 < num_k_tiles && k1 != k2
        && ({
            let diff = if k1 >= k2 { k1 - k2 } else { k2 - k1 };
            diff < num_buffers
        })
        ==> double_buffer_slot(k1, num_buffers) != double_buffer_slot(k2, num_buffers)
}

/// Total SMEM storage for double buffering.
pub open spec fn double_buffer_smem_size(
    bm: nat, bk: nat, bn: nat, num_buffers: nat,
) -> nat {
    num_buffers * (bm * bk + bk * bn)
}

/// Partition the output C-tile for epilogue: each thread writes its accumulator.
pub open spec fn epilogue_partition(
    c_tile: &DividedLayout,
    thread_layout: &LayoutSpec,
) -> (LayoutSpec, int)
    recommends
        divided_layout_valid(c_tile),
        thread_layout.valid(),
{
    local_partition(c_tile, thread_layout, 0)
}

} // verus!
