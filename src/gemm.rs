use vstd::prelude::*;
use crate::layout::*;
use crate::predication::*;
use crate::tiling::*;

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

} // verus!
