use vstd::prelude::*;
use crate::swizzle::*;

verus! {

/// External body wrapper for Rust's XOR operator.
#[verifier::external_body]
pub fn bxor_exec(a: u64, b: u64) -> (result: u64)
    ensures result as nat == bxor(a as nat, b as nat),
{
    a ^ b
}

/// External body wrapper for Rust's right shift.
#[verifier::external_body]
pub fn shr_exec(x: u64, n: u32) -> (result: u64)
    requires n <= 63,
    ensures result as nat == shr(x as nat, n as nat),
{
    x >> n
}

/// External body wrapper for Rust's left shift.
#[verifier::external_body]
pub fn shl_exec(x: u64, n: u32) -> (result: u64)
    requires n <= 63,
        shl(x as nat, n as nat) <= u64::MAX as nat,
    ensures result as nat == shl(x as nat, n as nat),
{
    x << n
}

/// External body wrapper for Rust's bitwise AND with mask.
/// Computes x & ((1 << m) - 1), i.e., x % 2^m.
#[verifier::external_body]
pub fn band_mask_exec(x: u64, m: u32) -> (result: u64)
    requires m <= 63,
    ensures result as nat == band_mask(x as nat, m as nat),
{
    if m == 0 { 0 } else { x & ((1u64 << m) - 1) }
}

/// CuTe swizzle at runtime.
/// swizzle(x, b, m, s) = x XOR (((x >> (m + s)) & bit_mask(b)) << m)
pub fn swizzle_exec(x: u64, b: u32, m: u32, s: u32) -> (result: u64)
    requires
        swizzle_admissible(b as nat, m as nat, s as nat),
        (m + s + b) <= 63,
    ensures
        result as nat == swizzle(x as nat, b as nat, m as nat, s as nat),
{
    let shifted = shr_exec(x, m + s);
    let extracted = band_mask_exec(shifted, b);

    proof {
        crate::proof::swizzle_lemmas::lemma_band_mask_bound(shifted as nat, b as nat);
        crate::proof::swizzle_lemmas::lemma_shl_bound(extracted as nat, m as nat, b as nat);
        // shl(extracted, m) < pow2(m + b) <= pow2(64) = u64::MAX + 1
        // since m + b <= m + s + b <= 63 < 64
        crate::proof::swizzle_lemmas::lemma_pow2_monotone((m + b) as nat, 64);
        // pow2(64) = 2^64 > u64::MAX, so shl < pow2(m+b) <= pow2(64) and fits in u64
        // Actually we need shl(...) <= u64::MAX. Since shl < pow2(m+b) and m+b <= 63,
        // pow2(63) <= u64::MAX+1, so shl <= pow2(63)-1 <= u64::MAX
        assert(shl(extracted as nat, m as nat) <= u64::MAX as nat) by {
            assert(shl(extracted as nat, m as nat) < pow2((m + b) as nat));
            assert((m + b) as nat <= 63nat);
            crate::proof::swizzle_lemmas::lemma_pow2_monotone((m + b) as nat, 63);
            lemma_pow2_63_bound();
        }
    }

    let mask = shl_exec(extracted, m);
    bxor_exec(x, mask)
}

/// pow2(63) <= u64::MAX + 1, so pow2(63) - 1 <= u64::MAX.
proof fn lemma_pow2_63_bound()
    ensures pow2(63) <= (u64::MAX as nat) + 1,
{
    // pow2(63) = 2^63 = 9223372036854775808
    // u64::MAX = 18446744073709551615
    // pow2(63) <= u64::MAX + 1 = 2^64
    reveal_with_fuel(pow2, 65);
}

} // verus!
