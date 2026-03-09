use vstd::prelude::*;
use crate::layout::*;

verus! {

/// XOR-based swizzle parameterized by (B, M, S) following CuTe's Swizzle<B, M, S>:
/// - B (BBits): number of bits in the swizzle mask
/// - M (MBase): base offset for the mask window
/// - S (SShift): shift amount (source bits at [M+S, M+S+B) XOR'd into [M, M+B))
///
/// Formula: swizzle(x) = x XOR ((x >> S) & (bit_mask(B) << M))
///        = x XOR (((x >> (M + S)) & bit_mask(B)) << M)
///
/// Equivalently: extract B bits starting at position (M + S), XOR them into
/// position [M, M+B). Since |S| >= B (non-overlapping constraint), the source
/// and destination bit windows don't overlap, making this an involution.

/// Compute 2^n for spec purposes.
pub open spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 }
    else { 2 * pow2((n - 1) as nat) }
}

/// Bit mask of B ones: (2^B - 1).
pub open spec fn bit_mask(b: nat) -> nat {
    (pow2(b) - 1) as nat
}

/// Bitwise XOR, defined recursively on bits.
pub open spec fn bxor(a: nat, b: nat) -> nat
    decreases a + b,
{
    if a == 0 && b == 0 { 0 }
    else {
        let a_bit = a % 2;
        let b_bit = b % 2;
        let rest = bxor(a / 2, b / 2);
        if a_bit == b_bit { 2 * rest }
        else { 1 + 2 * rest }
    }
}

/// Right shift by n bits.
pub open spec fn shr(x: nat, n: nat) -> nat {
    x / pow2(n)
}

/// Left shift by n bits.
pub open spec fn shl(x: nat, n: nat) -> nat {
    x * pow2(n)
}

/// Bitwise AND with mask of M ones: x % 2^M.
pub open spec fn band_mask(x: nat, m: nat) -> nat {
    x % pow2(m)
}

/// CuTe swizzle: extract B bits at position (M + S), XOR into position M.
///
/// swizzle(x, B, M, S) = x XOR (((x >> (M + S)) % 2^B) << M)
///
/// This is equivalent to: x XOR ((x & (bit_mask(B) << (M+S))) >> S)
pub open spec fn swizzle(x: nat, b: nat, m: nat, s: nat) -> nat {
    let extracted = band_mask(shr(x, m + s), b);
    let shifted = shl(extracted, m);
    bxor(x, shifted)
}

/// Admissibility: S >= B (non-overlapping source and destination windows).
/// Source window: [M+S, M+S+B)
/// Destination window: [M, M+B)
/// Non-overlap requires: M+B <= M+S, i.e., S >= B.
pub open spec fn swizzle_admissible(b: nat, m: nat, s: nat) -> bool {
    &&& b > 0
    &&& s >= b  // non-overlapping windows
}

// ══════════════════════════════════════════════════════════════
// Bank conflict specs
// ══════════════════════════════════════════════════════════════

/// Bank index: which bank an address maps to (modular partitioning).
pub open spec fn bank_index(offset: int, num_banks: nat) -> nat
    recommends num_banks > 0,
{
    (offset % (num_banks as int)) as nat
}

/// A layout is bank-conflict-free if all addresses within count map to distinct banks.
pub open spec fn bank_conflict_free(layout: &LayoutSpec, num_banks: nat, count: nat) -> bool
    recommends num_banks > 0,
{
    forall|i: nat, j: nat|
        i < count && j < count && i != j
        ==> bank_index(layout.offset(i), num_banks) != bank_index(layout.offset(j), num_banks)
}

/// Domain size for a swizzle with parameters (B, M, S).
pub open spec fn swizzle_domain(b: nat, m: nat, s: nat) -> nat {
    pow2(m + s + b)
}

// ══════════════════════════════════════════════════════════════
// Swizzle-layout composition
// ══════════════════════════════════════════════════════════════

/// Apply swizzle to a layout offset at a given index.
/// Requires non-negative strides so offset >= 0.
pub open spec fn swizzled_offset(
    layout: &LayoutSpec, b: nat, m: nat, s: nat, idx: nat,
) -> nat
    recommends
        layout.valid(),
        layout.non_negative_strides(),
        idx < layout.size(),
{
    swizzle(layout.offset(idx) as nat, b, m, s)
}

/// Admissibility for swizzle-layout composition.
pub open spec fn swizzle_layout_admissible(
    layout: &LayoutSpec, b: nat, m: nat, s: nat,
) -> bool {
    &&& layout.valid()
    &&& layout.non_negative_strides()
    &&& layout.is_injective()
    &&& swizzle_admissible(b, m, s)
    &&& layout.cosize_nonneg() <= pow2(m + s + b)
}

} // verus!
