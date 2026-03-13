use vstd::prelude::*;
use crate::layout::*;
use crate::predication::*;
use crate::tiling::*;
use crate::swizzle::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Tensor specification
// ══════════════════════════════════════════════════════════════

/// A tensor is a layout mapping logical indices to abstract data.
pub struct TensorSpec {
    pub layout: LayoutSpec,
    pub data_size: nat,
}

/// A tensor is valid if its layout is valid with non-negative strides
/// and the backing data is large enough.
pub open spec fn tensor_valid(t: &TensorSpec) -> bool {
    &&& t.layout.valid()
    &&& t.layout.non_negative_strides()
    &&& t.layout.cosize_nonneg() <= t.data_size
}

// ══════════════════════════════════════════════════════════════
// GEMM element offset specs
// ══════════════════════════════════════════════════════════════

/// The offset of A[i,k] in a rank-2 layout: row i, column k.
pub open spec fn gemm_a_offset(a_layout: &LayoutSpec, i: nat, k: nat) -> int
    recommends a_layout.rank() == 2,
{
    (i as int) * a_layout.stride[0] + (k as int) * a_layout.stride[1]
}

/// The offset of B[k,j] in a rank-2 layout: row k, column j.
pub open spec fn gemm_b_offset(b_layout: &LayoutSpec, k: nat, j: nat) -> int
    recommends b_layout.rank() == 2,
{
    (k as int) * b_layout.stride[0] + (j as int) * b_layout.stride[1]
}

/// The offset of C[i,j] in a rank-2 layout: row i, column j.
pub open spec fn gemm_c_offset(c_layout: &LayoutSpec, i: nat, j: nat) -> int
    recommends c_layout.rank() == 2,
{
    (i as int) * c_layout.stride[0] + (j as int) * c_layout.stride[1]
}

// ══════════════════════════════════════════════════════════════
// Tiled offset decomposition
// ══════════════════════════════════════════════════════════════

/// Offset of A[i,k] via tiling: tile (ti, tk) at element (ei, ek).
pub open spec fn gemm_a_tiled_offset(
    a_layout: &LayoutSpec, bm: nat, bk: nat,
    ti: nat, tk: nat, ei: nat, ek: nat,
) -> int
    recommends a_layout.rank() == 2, bm > 0, bk > 0,
{
    gemm_a_offset(a_layout, ti * bm + ei, tk * bk + ek)
}

/// The flat and tiled offsets agree when tile coords decompose the global coords.
pub open spec fn gemm_offset_tiling_consistent(
    a_layout: &LayoutSpec, m: nat, k: nat, bm: nat, bk: nat,
) -> bool
    recommends a_layout.rank() == 2, bm > 0, bk > 0,
{
    forall|i: nat, kk: nat| i < m && kk < k ==>
        gemm_a_offset(a_layout, i, kk)
        == gemm_a_tiled_offset(a_layout, bm, bk,
            i / bm, kk / bk, i % bm, kk % bk)
}

// ══════════════════════════════════════════════════════════════
// K-reduction completeness
// ══════════════════════════════════════════════════════════════

/// All K elements in [0, k_size) are covered by some K-tile's valid elements.
pub open spec fn k_reduction_complete(k_size: nat, bk: nat) -> bool
    recommends bk > 0, k_size > 0,
{
    forall|kk: nat| kk < k_size ==>
        tile_element_valid(
            tile_for_index(kk, bk),
            bk,
            elem_in_tile(kk, bk),
            k_size,
        )
}

// ══════════════════════════════════════════════════════════════
// Output coverage
// ══════════════════════════════════════════════════════════════

/// Every output element (i,j) is assigned to exactly one CTA tile.
/// Helper spec for triggering on (i, j) pair in coverage quantifier.
pub open spec fn gemm_cta_for(i: nat, j: nat, bm: nat, bn: nat) -> (nat, nat) {
    (tile_for_index(i, bm), tile_for_index(j, bn))
}

/// Every output element (i,j) is assigned to exactly one CTA tile.
pub open spec fn gemm_output_covered(
    m: nat, n: nat, bm: nat, bn: nat,
) -> bool {
    forall|i: nat, j: nat| i < m && j < n ==> {
        let pair = #[trigger] gemm_cta_for(i, j, bm, bn);
        &&& pair.0 < num_tiles_ceil(m, bm)
        &&& pair.1 < num_tiles_ceil(n, bn)
        &&& pair.0 * bm + elem_in_tile(i, bm) == i
        &&& pair.1 * bn + elem_in_tile(j, bn) == j
    }
}

// ══════════════════════════════════════════════════════════════
// CTA disjointness
// ══════════════════════════════════════════════════════════════

/// Distinct output indices produce distinct C offsets — no two elements
/// of the output matrix share the same physical location.
pub open spec fn gemm_output_injective(
    c_layout: &LayoutSpec, m: nat, n: nat,
) -> bool {
    forall|i1: nat, j1: nat, i2: nat, j2: nat|
        i1 < m && j1 < n && i2 < m && j2 < n
        && (i1 != i2 || j1 != j2)
        ==> #[trigger] gemm_c_offset(c_layout, i1, j1)
            != #[trigger] gemm_c_offset(c_layout, i2, j2)
}

// ══════════════════════════════════════════════════════════════
// GEMM admissibility
// ══════════════════════════════════════════════════════════════

/// Full GEMM configuration admissibility.
pub open spec fn gemm_config_admissible(
    m: nat, n: nat, k: nat,
    bm: nat, bn: nat, bk: nat,
    a_layout: &LayoutSpec, b_layout: &LayoutSpec, c_layout: &LayoutSpec,
) -> bool {
    &&& a_layout.valid() && a_layout.rank() == 2
    &&& b_layout.valid() && b_layout.rank() == 2
    &&& c_layout.valid() && c_layout.rank() == 2
    &&& c_layout.is_injective()
    &&& m > 0 && n > 0 && k > 0
    &&& bm > 0 && bn > 0 && bk > 0
    &&& padded_divide_admissible(m, bm)
    &&& padded_divide_admissible(n, bn)
    &&& padded_divide_admissible(k, bk)
}

// ══════════════════════════════════════════════════════════════
// B-matrix tiled offset decomposition
// ══════════════════════════════════════════════════════════════

/// Offset of B[k,j] via tiling: tile (tk, tj) at element (ek, ej).
pub open spec fn gemm_b_tiled_offset(
    b_layout: &LayoutSpec, bk: nat, bn: nat,
    tk: nat, tj: nat, ek: nat, ej: nat,
) -> int
    recommends b_layout.rank() == 2, bk > 0, bn > 0,
{
    gemm_b_offset(b_layout, tk * bk + ek, tj * bn + ej)
}

/// The flat and tiled B-offsets agree when tile coords decompose the global coords.
pub open spec fn gemm_b_offset_tiling_consistent(
    b_layout: &LayoutSpec, k: nat, n: nat, bk: nat, bn: nat,
) -> bool
    recommends b_layout.rank() == 2, bk > 0, bn > 0,
{
    forall|kk: nat, j: nat| kk < k && j < n ==>
        gemm_b_offset(b_layout, kk, j)
        == gemm_b_tiled_offset(b_layout, bk, bn,
            kk / bk, j / bn, kk % bk, j % bn)
}

// ══════════════════════════════════════════════════════════════
// Shared memory layouts (Feature 1)
// ══════════════════════════════════════════════════════════════

/// Shared memory layout for an A-tile (bm × bk) stored column-major.
pub open spec fn smem_a_layout(bm: nat, bk: nat) -> LayoutSpec {
    make_column_major(seq![bm, bk])
}

/// Shared memory layout for a B-tile (bk × bn) stored column-major.
pub open spec fn smem_b_layout(bk: nat, bn: nat) -> LayoutSpec {
    make_column_major(seq![bk, bn])
}

/// SM80 swizzle parameters: B=3 (8 bytes), M=0, S=3.
pub open spec fn sm80_smem_swizzle_b() -> nat { 3 }
pub open spec fn sm80_smem_swizzle_m() -> nat { 0 }
pub open spec fn sm80_smem_swizzle_s() -> nat { 3 }

/// SMEM layout admissibility: base layout compatible with swizzle parameters.
pub open spec fn smem_layout_swizzle_admissible(
    base: &LayoutSpec, b: nat, m: nat, s: nat,
) -> bool {
    &&& swizzle_layout_admissible(base, b, m, s)
    &&& base.cosize_nonneg() <= pow2(m + s + b)
}

/// Swizzled offsets are all distinct within count elements.
pub open spec fn smem_swizzle_distinct(
    base: &LayoutSpec, b: nat, m: nat, s: nat,
    count: nat,
) -> bool {
    forall|i: nat, j: nat|
        i < count && j < count && i != j
        ==> swizzled_offset(base, b, m, s, i)
            != swizzled_offset(base, b, m, s, j)
}

// ══════════════════════════════════════════════════════════════
// Copy atom specs (Feature 2)
// ══════════════════════════════════════════════════════════════

/// Global-to-shared-memory copy atom: contiguous load of access_width elements.
pub open spec fn g2s_copy_atom(access_width: nat) -> LayoutSpec {
    make_identity(access_width)
}

/// Tiled copy for G2S: distributes copy atom across threads.
pub open spec fn g2s_tiled_copy(
    access_width: nat, thr_layout: &LayoutSpec, val_layout: &LayoutSpec,
) -> LayoutSpec {
    make_tiled_copy(&g2s_copy_atom(access_width), thr_layout, val_layout)
}

/// G2S copy admissibility.
pub open spec fn g2s_copy_admissible(
    access_width: nat, thr_layout: &LayoutSpec, val_layout: &LayoutSpec,
) -> bool {
    &&& access_width > 0
    &&& tiled_copy_admissible(&g2s_copy_atom(access_width), thr_layout, val_layout)
}

/// Shared-memory-to-register copy atom: contiguous load for MMA consumption.
pub open spec fn s2r_copy_atom(access_width: nat) -> LayoutSpec {
    make_identity(access_width)
}

/// Tiled copy for S2R.
pub open spec fn s2r_tiled_copy(
    access_width: nat, thr_layout: &LayoutSpec, val_layout: &LayoutSpec,
) -> LayoutSpec {
    make_tiled_copy(&s2r_copy_atom(access_width), thr_layout, val_layout)
}

/// S2R copy admissibility.
pub open spec fn s2r_copy_admissible(
    access_width: nat, thr_layout: &LayoutSpec, val_layout: &LayoutSpec,
) -> bool {
    &&& access_width > 0
    &&& tiled_copy_admissible(&s2r_copy_atom(access_width), thr_layout, val_layout)
}

/// A tiled copy covers a tile: every element in [0, tile_size) is assigned.
pub open spec fn copy_covers_tile(copy_layout: &LayoutSpec, tile_size: nat) -> bool {
    copy_layout.size() >= tile_size
}

// ══════════════════════════════════════════════════════════════
// Pipeline composition specs (Feature 3)
// ══════════════════════════════════════════════════════════════

/// G2S stage validity: copy tile size matches SMEM tile size.
pub open spec fn g2s_stage_valid(
    g2s_copy: &LayoutSpec, smem_base: &LayoutSpec,
    tile_m: nat, tile_k: nat,
) -> bool {
    &&& g2s_copy.valid()
    &&& smem_base.valid()
    &&& g2s_copy.size() >= tile_m * tile_k
    &&& smem_base.size() == tile_m * tile_k
}

/// S2R stage validity: register copy covers the MMA fragment.
pub open spec fn s2r_stage_valid(
    s2r_copy: &LayoutSpec, mma_thr: &LayoutSpec, mma_val: &LayoutSpec,
) -> bool {
    &&& s2r_copy.valid()
    &&& mma_atom_admissible(mma_thr, mma_val)
    &&& s2r_copy.size() >= mma_thr.size() * mma_val.size()
}

/// Full pipeline admissibility: all stages connect correctly.
pub open spec fn gemm_pipeline_admissible(
    m: nat, n: nat, k: nat,
    bm: nat, bn: nat, bk: nat,
    g2s_a: &LayoutSpec, g2s_b: &LayoutSpec,
    smem_a: &LayoutSpec, smem_b: &LayoutSpec,
    s2r_a: &LayoutSpec, s2r_b: &LayoutSpec,
    mma_thr: &LayoutSpec, mma_val: &LayoutSpec,
    a_layout: &LayoutSpec, b_layout: &LayoutSpec, c_layout: &LayoutSpec,
) -> bool {
    &&& gemm_config_admissible(m, n, k, bm, bn, bk, a_layout, b_layout, c_layout)
    &&& g2s_stage_valid(g2s_a, smem_a, bm, bk)
    &&& g2s_stage_valid(g2s_b, smem_b, bk, bn)
    &&& s2r_stage_valid(s2r_a, mma_thr, mma_val)
    &&& s2r_stage_valid(s2r_b, mma_thr, mma_val)
}

// ══════════════════════════════════════════════════════════════
// MAC (Multiply-Accumulate) offset specs
// ══════════════════════════════════════════════════════════════

/// MAC offset pairs: the sequence of (a_offset, b_offset) pairs
/// for computing C[i,j] += sum_k A[i,k]*B[k,j] over k in [k_start, k_end).
pub open spec fn mac_offset_pairs(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    i: nat, j: nat, k_start: nat, k_end: nat,
) -> Seq<(int, int)>
    recommends a_layout.rank() == 2, b_layout.rank() == 2,
{
    Seq::new((k_end - k_start) as nat, |idx: int|
        (gemm_a_offset(a_layout, i, k_start + idx as nat),
         gemm_b_offset(b_layout, k_start + idx as nat, j)))
}

/// MAC completeness: all K elements contribute to the output.
pub open spec fn mac_complete(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    i: nat, j: nat, k_size: nat,
) -> bool {
    mac_offset_pairs(a_layout, b_layout, i, j, 0, k_size).len() == k_size
}

/// Tiled MAC consistency: the offset pairs for a K-tile match the global offset pairs.
pub open spec fn tiled_mac_consistent(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    i: nat, j: nat, k_tile: nat, bk: nat, k_size: nat,
) -> bool
    recommends bk > 0, k_tile * bk < k_size,
{
    let k_start = k_tile * bk;
    let k_end = if (k_tile + 1) * bk <= k_size { (k_tile + 1) * bk } else { k_size };
    forall|idx: nat| idx < k_end - k_start ==>
        #[trigger] mac_offset_pairs(a_layout, b_layout, i, j, k_start, k_end)[idx as int]
        == mac_offset_pairs(a_layout, b_layout, i, j, 0, k_size)[(k_start + idx) as int]
}

/// C output offset for tiled coordinates: tile (ti, tj) at element (ei, ej).
pub open spec fn gemm_c_tile_offset(
    c_layout: &LayoutSpec,
    ti: nat, tj: nat, ei: nat, ej: nat,
    bm: nat, bn: nat,
) -> int
    recommends c_layout.rank() == 2,
{
    gemm_c_offset(c_layout, ti * bm + ei, tj * bn + ej)
}

// ══════════════════════════════════════════════════════════════
// Epilogue store specs
// ══════════════════════════════════════════════════════════════

/// Epilogue store is in-bounds: the C offset for (i,j) is within data_size.
pub open spec fn epilogue_store_in_bounds(
    c_layout: &LayoutSpec, c_data_size: nat,
    i: nat, j: nat,
) -> bool
    recommends c_layout.rank() == 2,
{
    let off = gemm_c_offset(c_layout, i, j);
    off >= 0 && off < c_data_size as int
}

/// Predicated epilogue: only store if (i,j) is within (m,n).
pub open spec fn epilogue_predicated_store_safe(
    m: nat, n: nat,
    ti: nat, tj: nat, ei: nat, ej: nat,
    bm: nat, bn: nat,
) -> bool {
    let gi = ti * bm + ei;
    let gj = tj * bn + ej;
    gi < m && gj < n
}

/// Full epilogue correctness: for all valid elements in a CTA tile,
/// stores are in-bounds and write distinct locations.
pub open spec fn epilogue_cta_correct(
    c_layout: &LayoutSpec, c_data_size: nat,
    m: nat, n: nat, bm: nat, bn: nat,
    ti: nat, tj: nat,
) -> bool
    recommends c_layout.rank() == 2, bm > 0, bn > 0,
{
    forall|ei: nat, ej: nat| ei < bm && ej < bn
        && epilogue_predicated_store_safe(m, n, ti, tj, ei, ej, bm, bn)
        ==> epilogue_store_in_bounds(c_layout, c_data_size,
                ti * bm + ei, tj * bn + ej)
}

/// Cross-CTA epilogue disjointness: stores from different CTAs don't conflict.
pub open spec fn epilogue_cross_cta_disjoint(
    c_layout: &LayoutSpec, m: nat, n: nat, bm: nat, bn: nat,
) -> bool {
    forall|ti1: nat, tj1: nat, ei1: nat, ej1: nat,
           ti2: nat, tj2: nat, ei2: nat, ej2: nat|
        ei1 < bm && ej1 < bn && ei2 < bm && ej2 < bn
        && (ti1 != ti2 || tj1 != tj2)
        && epilogue_predicated_store_safe(m, n, ti1, tj1, ei1, ej1, bm, bn)
        && epilogue_predicated_store_safe(m, n, ti2, tj2, ei2, ej2, bm, bn)
        ==> #[trigger] gemm_c_tile_offset(c_layout, ti1, tj1, ei1, ej1, bm, bn)
            != #[trigger] gemm_c_tile_offset(c_layout, ti2, tj2, ei2, ej2, bm, bn)
}

} // verus!
