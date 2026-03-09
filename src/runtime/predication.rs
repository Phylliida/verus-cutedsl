use vstd::prelude::*;
use crate::predication::*;

verus! {

/// Ceiling division at runtime.
pub fn ceil_div_exec(a: u64, b: u64) -> (result: u64)
    requires b > 0, a as nat + b as nat - 1 <= u64::MAX as nat,
    ensures result as nat == ceil_div(a as nat, b as nat),
{
    let wide: u128 = (a as u128) + (b as u128) - 1;
    // wide fits in u64 by precondition
    (wide as u64) / b
}

/// Padded size at runtime: next multiple of tile_size >= total_size.
pub fn padded_size_exec(m: u64, n: u64) -> (result: u64)
    requires
        n > 0,
        m as nat + n as nat - 1 <= u64::MAX as nat,
        padded_size(m as nat, n as nat) <= u64::MAX as nat,
    ensures result as nat == padded_size(m as nat, n as nat),
{
    let q = ceil_div_exec(m, n);
    proof {
        // q * n == padded_size(m, n) which fits in u64 by precondition
    }
    q * n
}

/// Number of tiles needed to cover total_size elements.
pub fn num_tiles_ceil_exec(total_size: u64, tile_size: u64) -> (result: u64)
    requires
        tile_size > 0,
        total_size as nat + tile_size as nat - 1 <= u64::MAX as nat,
    ensures result as nat == num_tiles_ceil(total_size as nat, tile_size as nat),
{
    ceil_div_exec(total_size, tile_size)
}

/// Check if a specific element within a tile is valid.
pub fn tile_element_valid_exec(tile_idx: u64, tile_size: u64, elem_idx: u64, total_size: u64) -> (result: bool)
    requires
        tile_size > 0,
        elem_idx < tile_size,
        tile_idx as nat * tile_size as nat + elem_idx as nat <= u64::MAX as nat,
    ensures result == tile_element_valid(tile_idx as nat, tile_size as nat, elem_idx as nat, total_size as nat),
{
    proof {
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_idx as int, tile_size as int);
    }
    tile_idx * tile_size + elem_idx < total_size
}

/// Count valid elements in a given tile.
pub fn tile_valid_count_exec(tile_idx: u64, tile_size: u64, total_size: u64) -> (result: u64)
    requires
        tile_size > 0,
        tile_idx as nat * tile_size as nat <= u64::MAX as nat,
        (tile_idx as nat + 1) * tile_size as nat <= u64::MAX as nat,
    ensures result as nat == tile_valid_count(tile_idx as nat, tile_size as nat, total_size as nat),
{
    proof {
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_idx as int, tile_size as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative((tile_idx as int + 1), tile_size as int);
    }
    let start: u64 = tile_idx * tile_size;
    let end: u64 = ((tile_idx as u128 + 1) * tile_size as u128) as u64;
    if start >= total_size {
        0
    } else if end <= total_size {
        tile_size
    } else {
        total_size - start
    }
}

} // verus!
