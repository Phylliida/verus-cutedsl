///  Specifications for LSB-first binary radix sort.
///
///  Radix sort processes data bit-by-bit from least significant to most significant.
///  Each step stably partitions data: elements with bit=0 first, then bit=1.
///  The stable partition is expressed as dual compact (compact with NOT pred, then compact with pred).
///
///  Depends on: `crate::swizzle::pow2`, `crate::scan::{compact_size, compact_indices, compact_result}`
use vstd::prelude::*;
use crate::swizzle::pow2;
use crate::scan::{compact_size, compact_indices, compact_result};

verus! {

//  ============================================================
//  Bit extraction
//  ============================================================

///  Extract bit at position `pos` from `val`: (val / pow2(pos)) % 2.
pub open spec fn bit_at(val: nat, pos: nat) -> nat {
    (val / pow2(pos)) % 2
}

///  Low `k` bits of `val`: val % pow2(k).
pub open spec fn low_bits(val: nat, k: nat) -> nat {
    val % pow2(k)
}

//  ============================================================
//  Sortedness
//  ============================================================

///  A sequence of nats is sorted (non-decreasing).
pub open spec fn is_sorted_nat(s: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() as int ==> s[i] <= s[j]
}

///  A sequence is sorted by a key function.
pub open spec fn is_sorted_by_key<T>(s: Seq<T>, key: spec_fn(T) -> nat) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() as int ==> key(s[i]) <= key(s[j])
}

//  ============================================================
//  Predicate complement and bit predicate
//  ============================================================

///  Complement of a boolean predicate sequence.
pub open spec fn pred_complement(pred: Seq<bool>) -> Seq<bool> {
    Seq::new(pred.len(), |i: int| !pred[i])
}

///  Predicate: bit at position `pos` is 1.
pub open spec fn pred_bit(data: Seq<nat>, pos: nat) -> Seq<bool> {
    Seq::new(data.len(), |i: int| bit_at(data[i], pos) == 1)
}

///  Number of zeros at bit position `pos`.
pub open spec fn count_zeros(data: Seq<nat>, pos: nat) -> nat {
    compact_size(pred_complement(pred_bit(data, pos)))
}

//  ============================================================
//  Radix step (dual compact)
//  ============================================================

///  One radix sort step: stable partition by bit at `pos`.
///  Elements with bit=0 come first (via compact with NOT pred), then bit=1 (via compact with pred).
pub open spec fn radix_step(data: Seq<nat>, pos: nat) -> Seq<nat> {
    let pred = pred_bit(data, pos);
    let not_pred = pred_complement(pred);
    compact_result(data, not_pred) + compact_result(data, pred)
}

//  ============================================================
//  Scatter index (bridges spec to exec)
//  ============================================================

///  Destination index for element i in a radix step.
///  bit=0: position among zeros = i - compact_indices(pred)[i]
///  bit=1: count_zeros + rank among ones = count_zeros + compact_indices(pred)[i]
pub open spec fn radix_scatter_dest(data: Seq<nat>, pos: nat, i: nat) -> nat
    recommends i < data.len(),
{
    let pred = pred_bit(data, pos);
    if bit_at(data[i as int], pos) == 0 {
        (i as int - compact_indices(pred)[i as int] as int) as nat
    } else {
        count_zeros(data, pos) + compact_indices(pred)[i as int]
    }
}

///  The scatter permutation for a radix step.
pub open spec fn radix_scatter_perm(data: Seq<nat>, pos: nat) -> Seq<nat> {
    Seq::new(data.len(), |i: int| radix_scatter_dest(data, pos, i as nat))
}

//  ============================================================
//  Full radix sort
//  ============================================================

///  Partial radix sort: process bits 0..k-1.
pub open spec fn radix_sort_partial(data: Seq<nat>, k: nat) -> Seq<nat>
    decreases k,
{
    if k == 0 { data }
    else { radix_step(radix_sort_partial(data, (k - 1) as nat), (k - 1) as nat) }
}

///  Full radix sort: process bits 0..num_bits-1.
pub open spec fn radix_sort(data: Seq<nat>, num_bits: nat) -> Seq<nat> {
    radix_sort_partial(data, num_bits)
}

} //  verus!
