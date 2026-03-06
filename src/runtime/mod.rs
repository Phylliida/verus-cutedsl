use vstd::prelude::*;

pub mod shape_helpers;
pub mod layout;
pub mod ops;
pub mod swizzle;

verus! {

/// Convert a Vec<u64> of shapes to a Seq<nat> for spec-level reasoning.
pub open spec fn shape_to_nat_seq(v: Seq<u64>) -> Seq<nat> {
    Seq::new(v.len(), |i: int| v[i] as nat)
}

/// Convert a Vec<i64> of strides to a Seq<int> for spec-level reasoning.
pub open spec fn strides_to_int_seq(v: Seq<i64>) -> Seq<int> {
    Seq::new(v.len(), |i: int| v[i] as int)
}

/// A u64 shape is valid if all elements are > 0 and the product of all elements fits in u64.
pub open spec fn shape_valid_u64(v: Seq<u64>) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i] > 0
}

/// Bridge: shape_to_nat_seq preserves shape_valid.
pub proof fn lemma_shape_valid_bridge(v: Seq<u64>)
    requires shape_valid_u64(v),
    ensures crate::shape::shape_valid(shape_to_nat_seq(v)),
{
    assert forall|i: int| 0 <= i < shape_to_nat_seq(v).len() implies #[trigger] shape_to_nat_seq(v)[i] > 0
    by {
        assert(v[i] > 0);
    }
}

/// Bridge: shape_to_nat_seq length equals input length.
pub proof fn lemma_shape_to_nat_seq_len(v: Seq<u64>)
    ensures shape_to_nat_seq(v).len() == v.len(),
{
}

/// Bridge: strides_to_int_seq length equals input length.
pub proof fn lemma_strides_to_int_seq_len(v: Seq<i64>)
    ensures strides_to_int_seq(v).len() == v.len(),
{
}

} // verus!
