use vstd::prelude::*;
use crate::predication::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Arithmetic properties of ceil_div and padded_size
// ══════════════════════════════════════════════════════════════

/// Helper: (m + n - 1) as nat / n = q implies q * n >= m.
proof fn lemma_ceil_div_mul_ge(m: nat, n: nat)
    requires n > 0,
    ensures ceil_div(m, n) * n >= m,
{
    let total = (m + n - 1) as nat;
    let q = total / n;
    // fundamental: total = n * q + r, 0 <= r < n
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(total as int, n as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(total as int, n as int);
    let r: int = (total as int) % (n as int);
    // total = n * q + r
    // m + n - 1 = n * q + r
    // m = n * q + r - n + 1 = n * q - (n - 1 - r)
    // Since 0 <= r < n, n - 1 - r >= 0, so m <= n * q
    assert(total as int == (n as int) * (q as int) + r);
    assert(r >= 0 && r < n as int);
    assert((n as int) * (q as int) == total as int - r);
    assert((n as int) * (q as int) >= m as int);
    // n * q == q * n
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, q as int);
    assert((q as int) * (n as int) >= m as int);
}

/// Helper: padded_size(m, n) - m < n.
proof fn lemma_ceil_div_tight(m: nat, n: nat)
    requires n > 0,
    ensures (ceil_div(m, n) * n) as int - (m as int) < (n as int),
{
    let total = (m + n - 1) as nat;
    let q = total / n;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(total as int, n as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(total as int, n as int);
    let r: int = (total as int) % (n as int);
    assert(total as int == (n as int) * (q as int) + r);
    // q * n = m + n - 1 - r
    // q * n - m = n - 1 - r < n
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, q as int);
    assert((q as int) * (n as int) == total as int - r);
    assert((q as int) * (n as int) - m as int == (n as int) - 1 - r);
}

/// ceil_div(m, n) >= m / n (ceiling >= floor).
pub proof fn lemma_ceil_div_ge_floor(m: nat, n: nat)
    requires n > 0,
    ensures ceil_div(m, n) >= m / n,
{
    assert((m + n - 1) as nat >= m);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(m as int, (m + n - 1) as int, n as int);
}

/// padded_size(m, n) >= m.
pub proof fn lemma_padded_size_ge(m: nat, n: nat)
    requires n > 0,
    ensures padded_size(m, n) >= m,
{
    lemma_ceil_div_mul_ge(m, n);
}

/// padded_size(m, n) is divisible by n.
pub proof fn lemma_padded_size_divisible(m: nat, n: nat)
    requires n > 0,
    ensures padded_size(m, n) % n == 0,
{
    let q = ceil_div(m, n);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int, n as int);
}

/// The padding is at most n - 1: padded_size(m, n) - m < n.
pub proof fn lemma_padded_size_tight(m: nat, n: nat)
    requires n > 0,
    ensures padded_size(m, n) as int - (m as int) < (n as int),
{
    lemma_ceil_div_tight(m, n);
}

/// When m is divisible by n, ceil_div equals floor div.
pub proof fn lemma_ceil_div_exact(m: nat, n: nat)
    requires n > 0, m % n == 0,
    ensures ceil_div(m, n) == m / n,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, n as int);
    // m = n * (m/n) + 0 = n * (m/n)
    let q = m / n;
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, q as int);
    // m = q * n
    // (m + n - 1) = q * n + (n - 1)
    // Since n - 1 < n: (q*n + (n-1)) / n = q
    assert((m + n - 1) as nat == q * n + (n - 1) as nat);
    lemma_div_mod_decompose((n - 1) as nat, q, n);
    // ((n-1) + n * q) / n == q
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, q as int);
    assert(q * n + (n - 1) as nat == (n - 1) as nat + n * q);
}

// ══════════════════════════════════════════════════════════════
// Tile validity properties
// ══════════════════════════════════════════════════════════════

/// Full tiles (not the last) have all elements valid.
pub proof fn lemma_full_tile_all_valid(tile_idx: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        (tile_idx + 1) * tile_size <= total_size,
    ensures
        tile_valid_count(tile_idx, tile_size, total_size) == tile_size,
        forall|e: nat| e < tile_size ==>
            tile_element_valid(tile_idx, tile_size, e, total_size),
{
    // tile_idx * tile_size < (tile_idx + 1) * tile_size <= total_size
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(tile_size as int, tile_idx as int, 1int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, tile_idx as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, (tile_idx + 1) as int);
    assert(tile_idx * tile_size + tile_size == (tile_idx + 1) * tile_size);
    assert(tile_idx * tile_size < total_size);

    assert forall|e: nat| e < tile_size implies tile_element_valid(tile_idx, tile_size, e, total_size)
    by {
        assert(tile_idx * tile_size + e < tile_idx * tile_size + tile_size);
    };
}

/// The last partial tile has total_size - tile_idx * tile_size valid elements.
pub proof fn lemma_partial_tile_count(tile_idx: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        total_size > 0,
        tile_idx * tile_size < total_size,
        (tile_idx + 1) * tile_size > total_size,
    ensures
        tile_valid_count(tile_idx, tile_size, total_size) == total_size - tile_idx * tile_size,
        0 < tile_valid_count(tile_idx, tile_size, total_size),
        tile_valid_count(tile_idx, tile_size, total_size) < tile_size,
{
    let count = (total_size - tile_idx * tile_size) as nat;
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(tile_size as int, tile_idx as int, 1int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, tile_idx as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, (tile_idx + 1) as int);
    assert((tile_idx + 1) * tile_size == tile_idx * tile_size + tile_size);
}

/// Tiles beyond num_tiles_ceil have 0 valid elements.
pub proof fn lemma_out_of_range_tiles_empty(tile_idx: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        tile_idx >= num_tiles_ceil(total_size, tile_size),
    ensures
        tile_valid_count(tile_idx, tile_size, total_size) == 0,
{
    lemma_padded_size_ge(total_size, tile_size);
    let ntiles = num_tiles_ceil(total_size, tile_size);
    // ntiles * tile_size >= total_size (from padded_size_ge)
    // tile_idx >= ntiles, so tile_idx * tile_size >= ntiles * tile_size >= total_size
    vstd::arithmetic::mul::lemma_mul_inequality(ntiles as int, tile_idx as int, tile_size as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(ntiles as int, tile_size as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_idx as int, tile_size as int);
}

/// The sum of tile_valid_counts over all tiles equals total_size.
pub proof fn lemma_total_valid_elements(total_size: nat, tile_size: nat)
    requires tile_size > 0, total_size > 0,
    ensures
        sum_valid_counts(num_tiles_ceil(total_size, tile_size), tile_size, total_size) == total_size,
{
    let n = num_tiles_ceil(total_size, tile_size);
    lemma_total_valid_elements_inductive(n, tile_size, total_size);
    // At k = n: if n * tile_size <= total_size then sum = n * tile_size, else sum = total_size
    // But n = ceil_div(total_size, tile_size), so padded_size = n * tile_size >= total_size
    // We need: sum = total_size
    // Case 1: n * tile_size <= total_size AND n * tile_size >= total_size => n * tile_size == total_size => sum = total_size ✓
    // Case 2: n * tile_size > total_size => sum = total_size ✓
    lemma_padded_size_ge(total_size, tile_size);
}

/// Inductive helper: sum_valid_counts(k) == min(k * tile_size, total_size).
proof fn lemma_total_valid_elements_inductive(k: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        total_size > 0,
        k <= num_tiles_ceil(total_size, tile_size),
    ensures
        sum_valid_counts(k, tile_size, total_size) ==
            (if k * tile_size <= total_size { k * tile_size } else { total_size }),
    decreases k,
{
    if k == 0 {
    } else {
        let prev = (k - 1) as nat;
        // Arithmetic: k * tile_size == prev * tile_size + tile_size
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(tile_size as int, prev as int, 1int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, prev as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, k as int);

        // prev <= k <= num_tiles_ceil, so IH applies
        lemma_total_valid_elements_inductive(prev, tile_size, total_size);

        if prev * tile_size >= total_size {
            // tile_valid_count(prev) = 0 since prev * tile_size >= total_size
            // sum(k) = sum(k-1) + 0 = total_size
        } else if k * tile_size <= total_size {
            // Full tile
            lemma_full_tile_all_valid(prev, tile_size, total_size);
            // sum(k) = prev * tile_size + tile_size = k * tile_size
        } else {
            // Partial tile: prev * tile_size < total_size, k * tile_size > total_size
            lemma_partial_tile_count(prev, tile_size, total_size);
            // sum(k) = prev * tile_size + (total_size - prev * tile_size) = total_size
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Integration with divide
// ══════════════════════════════════════════════════════════════

/// padded_size properties: > 0 and divisible by tile_size.
pub proof fn lemma_padded_size_complement_admissible(total_size: nat, tile_size: nat)
    requires padded_divide_admissible(total_size, tile_size),
    ensures
        padded_size(total_size, tile_size) > 0,
        padded_size(total_size, tile_size) % tile_size == 0,
{
    lemma_padded_size_ge(total_size, tile_size);
    lemma_padded_size_divisible(total_size, tile_size);
}

/// num_tiles_ceil(m, n) * n == padded_size(m, n) — definitional.
pub proof fn lemma_num_tiles_is_padded(total_size: nat, tile_size: nat)
    requires tile_size > 0,
    ensures num_tiles_ceil(total_size, tile_size) * tile_size == padded_size(total_size, tile_size),
{
}

/// When total_size is divisible by tile_size, padded_size == total_size.
pub proof fn lemma_padded_size_exact(total_size: nat, tile_size: nat)
    requires tile_size > 0, total_size % tile_size == 0,
    ensures padded_size(total_size, tile_size) == total_size,
{
    lemma_ceil_div_exact(total_size, tile_size);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(total_size as int, tile_size as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, (total_size / tile_size) as int);
}

} // verus!
