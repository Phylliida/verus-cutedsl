use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

/// A permutation is valid if it's a bijection on [0, n).
pub open spec fn is_valid_permutation(perm: Seq<nat>, n: nat) -> bool {
    &&& perm.len() == n
    &&& forall|i: nat| i < n ==> #[trigger] perm[i as int] < n
    &&& forall|i: nat, j: nat| i < n && j < n && i != j
        ==> perm[i as int] != perm[j as int]
}

/// Apply a permutation to a sequence of nat.
pub open spec fn apply_perm_nat(s: Seq<nat>, perm: Seq<nat>) -> Seq<nat>
    recommends s.len() == perm.len(),
{
    Seq::new(perm.len(), |i: int| s[perm[i] as int])
}

/// Apply a permutation to a sequence of int.
pub open spec fn apply_perm_int(s: Seq<int>, perm: Seq<nat>) -> Seq<int>
    recommends s.len() == perm.len(),
{
    Seq::new(perm.len(), |i: int| s[perm[i] as int])
}

/// Permute the modes of a layout: reorder both shape and stride by the permutation.
pub open spec fn permute_modes(layout: LayoutSpec, perm: Seq<nat>) -> LayoutSpec
    recommends
        layout.shape.len() == perm.len(),
        layout.stride.len() == perm.len(),
{
    LayoutSpec {
        shape: apply_perm_nat(layout.shape, perm),
        stride: apply_perm_int(layout.stride, perm),
    }
}

/// The identity permutation on [0, n).
pub open spec fn identity_permutation(n: nat) -> Seq<nat> {
    Seq::new(n as nat, |i: int| i as nat)
}

/// Adjacent transposition: swap positions i and i+1, leaving all others fixed.
pub open spec fn swap_permutation(n: nat, i: nat) -> Seq<nat>
    recommends i + 1 < n,
{
    Seq::new(n as nat, |k: int|
        if k == i as int { (i + 1) as nat }
        else if k == (i + 1) as int { i }
        else { k as nat }
    )
}

/// Compose two permutations: (p1 ∘ p2)(i) = p1(p2(i)).
pub open spec fn compose_permutations(p1: Seq<nat>, p2: Seq<nat>) -> Seq<nat>
    recommends p1.len() == p2.len(),
{
    Seq::new(p1.len(), |i: int| p1[p2[i] as int])
}

} // verus!
