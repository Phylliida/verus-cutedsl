use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

/// Two layouts have the same total number of elements.
pub open spec fn size_compatible(l1: &LayoutSpec, l2: &LayoutSpec) -> bool {
    l1.size() == l2.size()
}

/// Two layouts produce the same offset for all indices in [0, m).
pub open spec fn offset_compatible(l1: &LayoutSpec, l2: &LayoutSpec, m: nat) -> bool {
    forall|i: nat| i < m ==> l1.offset(i) == l2.offset(i)
}

/// Two layouts are offset-equivalent: same size and same offsets everywhere.
pub open spec fn offset_equivalent(l1: &LayoutSpec, l2: &LayoutSpec) -> bool {
    &&& size_compatible(l1, l2)
    &&& offset_compatible(l1, l2, l1.size())
}

} // verus!
