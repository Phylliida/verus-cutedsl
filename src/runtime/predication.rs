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

/// Generate predicate mask for a tile at runtime.
/// Returns Vec<bool> where result[i] == tile_element_valid(tile_idx, tile_size, i, total_size).
pub fn tile_predicate_mask_exec(
    tile_idx: u64, tile_size: u64, total_size: u64,
) -> (result: Vec<bool>)
    requires
        tile_size > 0,
        tile_size <= u64::MAX as nat,
        tile_idx as nat * tile_size as nat + tile_size as nat <= u64::MAX as nat,
    ensures
        result.len() == tile_size as nat,
        forall|i: nat| i < tile_size as nat ==>
            result@[i as int] == tile_predicate_mask(
                tile_idx as nat, tile_size as nat, total_size as nat)[i as int],
{
    let mut mask: Vec<bool> = Vec::new();
    let mut idx: u64 = 0;
    while idx < tile_size
        invariant
            tile_size > 0,
            tile_idx as nat * tile_size as nat + tile_size as nat <= u64::MAX as nat,
            0 <= idx <= tile_size,
            mask.len() == idx as nat,
            forall|i: nat| i < idx as nat ==>
                mask@[i as int] == tile_predicate_mask(
                    tile_idx as nat, tile_size as nat, total_size as nat)[i as int],
        decreases tile_size - idx,
    {
        let valid = tile_element_valid_exec(tile_idx, tile_size, idx, total_size);
        mask.push(valid);
        idx = idx + 1;
    }
    mask
}

/// Count valid elements in a mask at runtime.
pub fn mask_popcount_exec(mask: &Vec<bool>) -> (result: u64)
    requires mask.len() <= u64::MAX as nat,
    ensures result as nat == mask_popcount(mask@),
{
    let mut count: u64 = 0;
    let mut idx: u64 = 0;
    let len = mask.len() as u64;
    proof {
        lemma_mask_popcount_zero_prefix(mask@, 0);
    }
    while idx < len
        invariant
            len == mask.len(),
            0 <= idx <= len,
            mask.len() <= u64::MAX as nat,
            count as nat == mask_popcount(mask@.take(idx as int)),
            count <= idx,
        decreases len - idx,
    {
        proof {
            lemma_mask_popcount_step(mask@, idx as nat);
        }
        if mask[idx as usize] {
            count = count + 1;
        }
        idx = idx + 1;
    }
    proof {
        assert(mask@.take(len as int) =~= mask@);
    }
    count
}

/// Check if a write index is safe under predication.
pub fn store_predication_safe_exec(
    tile_idx: u64, tile_size: u64, total_size: u64, write_idx: u64,
) -> (result: bool)
    requires
        tile_size > 0,
        tile_idx as nat * tile_size as nat + tile_size as nat <= u64::MAX as nat,
    ensures
        result == store_predication_safe(
            tile_idx as nat, tile_size as nat, total_size as nat, write_idx as nat),
{
    if write_idx < tile_size {
        tile_element_valid_exec(tile_idx, tile_size, write_idx, total_size)
    } else {
        false
    }
}

/// Compute the global index for a tile element (for bounds-checked store).
pub fn tile_global_index_exec(
    tile_idx: u64, tile_size: u64, elem_idx: u64,
) -> (result: u64)
    requires
        tile_size > 0,
        elem_idx < tile_size,
        tile_idx as nat * tile_size as nat + elem_idx as nat <= u64::MAX as nat,
    ensures
        result as nat == tile_idx as nat * tile_size as nat + elem_idx as nat,
{
    proof {
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_idx as int, tile_size as int);
    }
    tile_idx * tile_size + elem_idx
}

/// Helper: mask_popcount of an empty prefix is 0.
proof fn lemma_mask_popcount_zero_prefix(s: Seq<bool>, n: nat)
    requires n == 0,
    ensures mask_popcount(s.take(n as int)) == 0,
{
    assert(s.take(0) =~= Seq::<bool>::empty());
    assert(Seq::<bool>::empty().len() == 0);
}

/// Helper: mask_popcount step — extending by one element.
proof fn lemma_mask_popcount_step(s: Seq<bool>, k: nat)
    requires k < s.len(),
    ensures
        mask_popcount(s.take(k as int + 1)) ==
            mask_popcount(s.take(k as int)) + (if s[k as int] { 1nat } else { 0nat }),
    decreases k,
{
    let prefix = s.take(k as int + 1);
    assert(prefix.len() == k + 1);
    assert(prefix.last() == s[k as int]) by {
        assert(prefix[k as int] == s[k as int]);
    };
    assert(prefix.drop_last() =~= s.take(k as int));
}

} // verus!
