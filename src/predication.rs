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

} // verus!
