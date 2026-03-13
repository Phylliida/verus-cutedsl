use vstd::prelude::*;

verus! {

/// Ceiling division: ceil_div(a, b) = ceil(a / b).
pub open spec fn ceil_div(a: nat, b: nat) -> nat
    recommends b > 0,
{
    ((a + b - 1) as nat) / b
}

/// Pad size to next multiple of tile_size: padded_size(m, n) = ceil_div(m, n) * n.
pub open spec fn padded_size(m: nat, n: nat) -> nat
    recommends n > 0,
{
    ceil_div(m, n) * n
}

/// Whether a linear index is in bounds of the original (unpadded) tensor.
pub open spec fn in_bounds(idx: nat, original_size: nat) -> bool {
    idx < original_size
}

/// Number of tiles needed to cover total_size elements with tiles of tile_size.
pub open spec fn num_tiles_ceil(total_size: nat, tile_size: nat) -> nat
    recommends tile_size > 0,
{
    ceil_div(total_size, tile_size)
}

/// Whether element elem_idx within tile tile_idx is a valid (non-padding) element.
pub open spec fn tile_element_valid(
    tile_idx: nat, tile_size: nat, elem_idx: nat, total_size: nat,
) -> bool
    recommends tile_size > 0, elem_idx < tile_size,
{
    tile_idx * tile_size + elem_idx < total_size
}

/// Number of valid (non-padding) elements in a given tile.
pub open spec fn tile_valid_count(tile_idx: nat, tile_size: nat, total_size: nat) -> nat
    recommends tile_size > 0,
{
    if tile_idx * tile_size >= total_size {
        0
    } else if (tile_idx + 1) * tile_size <= total_size {
        tile_size
    } else {
        // Partial tile: total_size - tile_idx * tile_size elements
        (total_size - tile_idx * tile_size) as nat
    }
}

/// Sum of tile_valid_count over tiles [0, n).
pub open spec fn sum_valid_counts(n: nat, tile_size: nat, total_size: nat) -> nat
    recommends tile_size > 0,
    decreases n,
{
    if n == 0 {
        0
    } else {
        sum_valid_counts((n - 1) as nat, tile_size, total_size) +
            tile_valid_count((n - 1) as nat, tile_size, total_size)
    }
}

/// Admissibility for padded divide: tile_size > 0, total_size > 0.
pub open spec fn padded_divide_admissible(total_size: nat, tile_size: nat) -> bool {
    &&& tile_size > 0
    &&& total_size > 0
}

// ══════════════════════════════════════════════════════════════
// Predicated copy helpers
// ══════════════════════════════════════════════════════════════

/// Which tile contains linear index idx.
pub open spec fn tile_for_index(idx: nat, tile_size: nat) -> nat
    recommends tile_size > 0,
{
    idx / tile_size
}

/// Position within tile for linear index idx.
pub open spec fn elem_in_tile(idx: nat, tile_size: nat) -> nat
    recommends tile_size > 0,
{
    idx % tile_size
}

/// Each valid element is covered by exactly one tile-element pair.
pub open spec fn predicated_coverage_unique(original_size: nat, tile_size: nat) -> bool
    recommends padded_divide_admissible(original_size, tile_size),
{
    forall|x: nat| x < original_size ==>
        tile_element_valid(
            tile_for_index(x, tile_size),
            tile_size,
            elem_in_tile(x, tile_size),
            original_size,
        )
}

// ══════════════════════════════════════════════════════════════
// Predication boundary masking
// ══════════════════════════════════════════════════════════════

/// Predicate mask: a sequence of bools, true for valid elements.
pub open spec fn tile_predicate_mask(
    tile_idx: nat, tile_size: nat, total_size: nat,
) -> Seq<bool> {
    Seq::new(tile_size, |i: int|
        tile_element_valid(tile_idx, tile_size, i as nat, total_size))
}

/// Masked value: returns val if mask is true, zero_val if masked out.
pub open spec fn masked_value<T>(mask: bool, val: T, zero_val: T) -> T {
    if mask { val } else { zero_val }
}

/// Count of true values in a bool mask.
pub open spec fn mask_popcount(mask: Seq<bool>) -> nat
    decreases mask.len(),
{
    if mask.len() == 0 { 0 }
    else {
        (if mask.last() { 1nat } else { 0nat })
            + mask_popcount(mask.drop_last())
    }
}

/// The mask popcount equals the tile valid count.
pub open spec fn mask_count_consistent(
    tile_idx: nat, tile_size: nat, total_size: nat,
) -> bool {
    mask_popcount(tile_predicate_mask(tile_idx, tile_size, total_size))
        == tile_valid_count(tile_idx, tile_size, total_size)
}

/// Full tile: all mask bits are true.
pub open spec fn full_tile_mask_all_true(
    tile_idx: nat, tile_size: nat, total_size: nat,
) -> bool {
    forall|i: nat| i < tile_size ==>
        #[trigger] tile_predicate_mask(tile_idx, tile_size, total_size)[i as int] == true
}

/// Boundary tile: mask is contiguous — first valid_count bits true, rest false.
pub open spec fn mask_contiguous(mask: Seq<bool>, valid_count: nat) -> bool {
    &&& valid_count <= mask.len()
    &&& forall|i: nat| i < valid_count ==> #[trigger] mask[i as int] == true
    &&& forall|i: nat| valid_count <= i && i < mask.len() ==> #[trigger] mask[i as int] == false
}

/// Store predication: only write to valid positions.
pub open spec fn store_predication_safe(
    tile_idx: nat, tile_size: nat, total_size: nat,
    write_idx: nat,
) -> bool {
    write_idx < tile_size
    && tile_predicate_mask(tile_idx, tile_size, total_size)[write_idx as int]
}

} // verus!
