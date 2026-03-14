use vstd::prelude::*;
use crate::predication::*;
use crate::tiling::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Arithmetic properties of ceil_div and padded_size
// ══════════════════════════════════════════════════════════════

/// Helper: (m + n - 1) as nat / n = q implies q * n >= m.
pub proof fn lemma_ceil_div_mul_ge(m: nat, n: nat)
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

// ══════════════════════════════════════════════════════════════
// Predicated copy correctness
// ══════════════════════════════════════════════════════════════

/// tile_for_index(idx) < num_tiles_ceil when idx < original_size.
pub proof fn lemma_tile_for_index_bound(idx: nat, tile_size: nat, original_size: nat)
    requires
        tile_size > 0,
        idx < original_size,
    ensures
        tile_for_index(idx, tile_size) < num_tiles_ceil(original_size, tile_size),
{
    // idx < original_size <= padded_size = ntiles * tile_size
    lemma_padded_size_ge(original_size, tile_size);
    let ntiles = num_tiles_ceil(original_size, tile_size);
    let ps = padded_size(original_size, tile_size);
    assert(ps == ntiles * tile_size);
    assert(idx < ps);
    // idx / tile_size < ntiles because idx < ntiles * tile_size
    // Use: a < b * c ==> a / c < b (when c > 0)
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(idx as int, tile_size as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(idx as int, tile_size as int);
    // idx = tile_size * (idx / tile_size) + (idx % tile_size)
    // idx < ntiles * tile_size
    // tile_size * (idx / tile_size) <= idx < ntiles * tile_size
    // So idx / tile_size < ntiles
    let q = idx / tile_size;
    vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, q as int);
    assert(q * tile_size <= idx) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, q as int);
    };
    assert(q < ntiles) by (nonlinear_arith)
        requires
            q * tile_size <= idx,
            idx < ntiles * tile_size,
            tile_size > 0,
    {};
}

/// elem_in_tile(idx) < tile_size.
pub proof fn lemma_elem_in_tile_bound(idx: nat, tile_size: nat)
    requires
        tile_size > 0,
    ensures
        elem_in_tile(idx, tile_size) < tile_size,
{
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(idx as int, tile_size as int);
}

/// Every valid element is covered: tile * tile_size + elem == x < original_size.
pub proof fn lemma_predicated_coverage_unique(original_size: nat, tile_size: nat)
    requires
        padded_divide_admissible(original_size, tile_size),
    ensures
        predicated_coverage_unique(original_size, tile_size),
{
    assert forall|x: nat| x < original_size
    implies tile_element_valid(
        tile_for_index(x, tile_size),
        tile_size,
        elem_in_tile(x, tile_size),
        original_size,
    ) by {
        // tile_for_index(x) * tile_size + elem_in_tile(x) == x
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, tile_size as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, (x / tile_size) as int);
        // x = tile_size * (x / tile_size) + x % tile_size
        //   = (x / tile_size) * tile_size + x % tile_size
        // So (x / tile_size) * tile_size + (x % tile_size) == x < original_size
    };
}

/// Distinct tile-element pairs map to distinct global indices (no double counting).
pub proof fn lemma_predicated_no_double_count(
    tile_size: nat,
    t1: nat, e1: nat,
    t2: nat, e2: nat,
)
    requires
        tile_size > 0,
        e1 < tile_size,
        e2 < tile_size,
        t1 != t2 || e1 != e2,
    ensures
        t1 * tile_size + e1 != t2 * tile_size + e2,
{
    if t1 == t2 {
        // e1 != e2, same tile, so sums differ
    } else {
        // WLOG t1 != t2. If t1 < t2:
        //   t1 * tile_size + e1 < (t1 + 1) * tile_size <= t2 * tile_size <= t2 * tile_size + e2
        // Symmetric for t2 < t1.
        if t1 < t2 {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(tile_size as int, t1 as int, 1int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, t1 as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, (t1 + 1) as int);
            vstd::arithmetic::mul::lemma_mul_inequality((t1 + 1) as int, t2 as int, tile_size as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative((t1 + 1) as int, tile_size as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(t2 as int, tile_size as int);
        } else {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(tile_size as int, t2 as int, 1int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, t2 as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(tile_size as int, (t2 + 1) as int);
            vstd::arithmetic::mul::lemma_mul_inequality((t2 + 1) as int, t1 as int, tile_size as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative((t2 + 1) as int, tile_size as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(t1 as int, tile_size as int);
        }
    }
}

/// Predicated divide is injective on valid elements: distinct valid indices
/// have distinct offsets.
pub proof fn lemma_predicated_divide_injective_on_valid(
    original_size: nat, tile_size: nat,
)
    requires
        padded_divide_admissible(original_size, tile_size),
    ensures
        forall|x: nat, y: nat|
            x < original_size && y < original_size && x != y ==>
            predicated_divide(original_size, tile_size).layout.offset(x)
                != predicated_divide(original_size, tile_size).layout.offset(y),
{
    lemma_padded_size_ge(original_size, tile_size);
    assert forall|x: nat, y: nat|
        x < original_size && y < original_size && x != y
    implies predicated_divide(original_size, tile_size).layout.offset(x)
        != predicated_divide(original_size, tile_size).layout.offset(y)
    by {
        // offset(x) == x and offset(y) == y by identity
        let ps = padded_size(original_size, tile_size);
        assert(x < ps);
        assert(y < ps);
        crate::proof::tiling_lemmas::lemma_predicated_divide_offset_identity(
            original_size, tile_size, x,
        );
        crate::proof::tiling_lemmas::lemma_predicated_divide_offset_identity(
            original_size, tile_size, y,
        );
        // offset(x) == x, offset(y) == y, x != y
    };
}

// ══════════════════════════════════════════════════════════════
// Predication boundary masking proofs (Feature 2 Round 2)
// ══════════════════════════════════════════════════════════════

/// Full tiles have all-true masks.
pub proof fn lemma_full_tile_mask(tile_idx: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        (tile_idx + 1) * tile_size <= total_size,
    ensures
        full_tile_mask_all_true(tile_idx, tile_size, total_size),
{
    lemma_full_tile_all_valid(tile_idx, tile_size, total_size);
    assert forall|i: nat| i < tile_size implies
        #[trigger] tile_predicate_mask(tile_idx, tile_size, total_size)[i as int] == true
    by {
        assert(tile_element_valid(tile_idx, tile_size, i, total_size));
    };
}

/// Boundary tile mask is contiguous: first valid_count true, rest false.
pub proof fn lemma_boundary_tile_mask_contiguous(
    tile_idx: nat, tile_size: nat, total_size: nat,
)
    requires
        tile_size > 0,
        total_size > 0,
        tile_idx * tile_size < total_size,
        (tile_idx + 1) * tile_size > total_size,
    ensures
        mask_contiguous(
            tile_predicate_mask(tile_idx, tile_size, total_size),
            tile_valid_count(tile_idx, tile_size, total_size)),
{
    lemma_partial_tile_count(tile_idx, tile_size, total_size);
    let vc = tile_valid_count(tile_idx, tile_size, total_size);
    let mask = tile_predicate_mask(tile_idx, tile_size, total_size);

    assert(mask.len() == tile_size);
    assert(vc <= tile_size);

    // For i < vc: tile_idx * tile_size + i < total_size → valid → true
    assert forall|i: nat| i < vc implies #[trigger] mask[i as int] == true
    by {
        // vc == total_size - tile_idx * tile_size
        // i < vc → tile_idx * tile_size + i < total_size
        assert(tile_idx * tile_size + i < total_size);
        assert(tile_element_valid(tile_idx, tile_size, i, total_size));
    };

    // For i >= vc: tile_idx * tile_size + i >= total_size → invalid → false
    assert forall|i: nat| vc <= i && i < mask.len() implies #[trigger] mask[i as int] == false
    by {
        // i >= vc == total_size - tile_idx * tile_size
        // tile_idx * tile_size + i >= total_size
        assert(tile_idx * tile_size + i >= total_size);
        assert(!tile_element_valid(tile_idx, tile_size, i, total_size));
    };
}

/// Store predication implies in-bounds write.
pub proof fn lemma_store_predication_in_bounds(
    tile_idx: nat, tile_size: nat, total_size: nat, write_idx: nat,
)
    requires
        tile_size > 0,
        store_predication_safe(tile_idx, tile_size, total_size, write_idx),
    ensures
        tile_idx * tile_size + write_idx < total_size,
{
    // Unfold: store_predication_safe means mask[write_idx] == true
    // mask[write_idx] == tile_element_valid(tile_idx, tile_size, write_idx, total_size)
    // == tile_idx * tile_size + write_idx < total_size
}

/// Masked load preserves valid data, zeros padding.
pub proof fn lemma_masked_load_correct(
    tile_idx: nat, tile_size: nat, total_size: nat, elem_idx: nat,
)
    requires
        tile_size > 0,
        elem_idx < tile_size,
    ensures
        tile_element_valid(tile_idx, tile_size, elem_idx, total_size) ==>
            tile_predicate_mask(tile_idx, tile_size, total_size)[elem_idx as int] == true,
        !tile_element_valid(tile_idx, tile_size, elem_idx, total_size) ==>
            tile_predicate_mask(tile_idx, tile_size, total_size)[elem_idx as int] == false,
{
    // Direct from tile_predicate_mask definition — mask[i] == tile_element_valid(...)
}

/// Mask popcount for full tiles equals tile_size.
pub proof fn lemma_mask_popcount_full(tile_idx: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        (tile_idx + 1) * tile_size <= total_size,
    ensures
        mask_count_consistent(tile_idx, tile_size, total_size),
{
    lemma_full_tile_all_valid(tile_idx, tile_size, total_size);
    let mask = tile_predicate_mask(tile_idx, tile_size, total_size);
    // All true → popcount == len == tile_size
    lemma_mask_popcount_all_true(mask, tile_size);
    // tile_valid_count == tile_size for full tiles
}

/// Helper: popcount of all-true mask of length n is n.
proof fn lemma_mask_popcount_all_true(mask: Seq<bool>, n: nat)
    requires
        mask.len() == n,
        forall|i: nat| i < n ==> #[trigger] mask[i as int] == true,
    ensures
        mask_popcount(mask) == n,
    decreases n,
{
    if n == 0 {
    } else {
        assert(mask.last() == true) by {
            assert(mask[(n - 1) as int] == true);
        };
        let prev = mask.drop_last();
        assert(prev.len() == (n - 1) as nat);
        assert forall|i: nat| i < (n - 1) as nat implies #[trigger] prev[i as int] == true
        by {
            assert(mask[i as int] == true);
        };
        lemma_mask_popcount_all_true(prev, (n - 1) as nat);
    }
}

/// Mask popcount for boundary tiles.
pub proof fn lemma_mask_popcount_boundary(tile_idx: nat, tile_size: nat, total_size: nat)
    requires
        tile_size > 0,
        total_size > 0,
        tile_idx * tile_size < total_size,
        (tile_idx + 1) * tile_size > total_size,
    ensures
        mask_count_consistent(tile_idx, tile_size, total_size),
{
    lemma_boundary_tile_mask_contiguous(tile_idx, tile_size, total_size);
    lemma_partial_tile_count(tile_idx, tile_size, total_size);
    let vc = tile_valid_count(tile_idx, tile_size, total_size);
    let mask = tile_predicate_mask(tile_idx, tile_size, total_size);
    // mask is contiguous: first vc true, rest false
    lemma_mask_popcount_contiguous(mask, vc);
}

/// Helper: popcount of a contiguous mask with vc true bits is vc.
proof fn lemma_mask_popcount_contiguous(mask: Seq<bool>, vc: nat)
    requires
        mask_contiguous(mask, vc),
    ensures
        mask_popcount(mask) == vc,
    decreases mask.len(),
{
    if mask.len() == 0 {
        assert(vc == 0nat);
    } else {
        let n = mask.len() as nat;
        if vc < n {
            // Last element is false (n-1 >= vc)
            assert(mask[(n - 1) as int] == false);
            assert(mask.last() == false);
            let prev = mask.drop_last();
            // prev is contiguous with same vc
            assert(prev.len() == (n - 1) as nat);
            assert(mask_contiguous(prev, vc)) by {
                assert(vc <= prev.len());
                assert forall|i: nat| i < vc implies #[trigger] prev[i as int] == true
                by {
                    assert(mask[i as int] == true);
                };
                assert forall|i: nat| vc <= i && i < prev.len() implies #[trigger] prev[i as int] == false
                by {
                    assert(mask[i as int] == false);
                };
            };
            lemma_mask_popcount_contiguous(prev, vc);
        } else {
            // vc == n, all true
            assert(mask.last() == true) by {
                assert(mask[(n - 1) as int] == true);
            };
            let prev = mask.drop_last();
            assert(mask_contiguous(prev, (vc - 1) as nat)) by {
                assert((vc - 1) as nat <= prev.len());
                assert forall|i: nat| i < (vc - 1) as nat implies #[trigger] prev[i as int] == true
                by {
                    assert(mask[i as int] == true);
                };
                // No false range since vc-1 == prev.len()
            };
            lemma_mask_popcount_contiguous(prev, (vc - 1) as nat);
        }
    }
}

} // verus!
