use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::permutation::*;
use crate::proof::complement_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Structural properties
// ══════════════════════════════════════════════════════════════

/// permute_modes preserves rank.
pub proof fn lemma_permute_modes_rank(layout: &LayoutSpec, perm: Seq<nat>)
    requires
        layout.shape.len() == perm.len(),
        layout.stride.len() == perm.len(),
    ensures
        permute_modes(*layout, perm).shape.len() == layout.shape.len(),
        permute_modes(*layout, perm).stride.len() == layout.stride.len(),
{
}

/// permute_modes with a valid permutation preserves validity (shape entries > 0).
pub proof fn lemma_permute_modes_valid(layout: &LayoutSpec, perm: Seq<nat>)
    requires
        layout.valid(),
        is_valid_permutation(perm, layout.shape.len()),
    ensures
        permute_modes(*layout, perm).valid(),
{
    let result = permute_modes(*layout, perm);
    assert forall|i: int| 0 <= i < result.shape.len()
        implies #[trigger] result.shape[i] > 0
    by {
        let pi = perm[i] as int;
        assert(layout.shape[pi] > 0);
    };
}

/// Identity permutation is a valid permutation.
pub proof fn lemma_identity_permutation_valid(n: nat)
    ensures is_valid_permutation(identity_permutation(n), n),
{
}

/// swap_permutation is a valid permutation when i+1 < n.
pub proof fn lemma_swap_permutation_valid(n: nat, i: nat)
    requires i + 1 < n,
    ensures is_valid_permutation(swap_permutation(n, i), n),
{
}

/// Permuting by the identity permutation is a no-op.
pub proof fn lemma_permute_identity(layout: &LayoutSpec)
    requires layout.shape.len() == layout.stride.len(),
    ensures permute_modes(*layout, identity_permutation(layout.shape.len())) == *layout,
{
    let n = layout.shape.len();
    let id = identity_permutation(n);
    let result = permute_modes(*layout, id);
    assert(result.shape =~= layout.shape);
    assert(result.stride =~= layout.stride);
}

// ══════════════════════════════════════════════════════════════
// Swap ↔ permute bridge
// ══════════════════════════════════════════════════════════════

/// apply_swap_layout(L, i) == permute_modes(L, swap_permutation(n, i)).
pub proof fn lemma_swap_eq_permute(layout: &LayoutSpec, i: nat)
    requires
        layout.valid(),
        i + 1 < layout.shape.len(),
    ensures
        apply_swap_layout(*layout, i) == permute_modes(*layout, swap_permutation(layout.shape.len(), i)),
{
    let n = layout.shape.len();
    let swap_l = apply_swap_layout(*layout, i);
    let perm_l = permute_modes(*layout, swap_permutation(n, i));
    // Both produce the same shape and stride by extensional equality
    assert(swap_l.shape =~= perm_l.shape);
    assert(swap_l.stride =~= perm_l.stride);
}

// ══════════════════════════════════════════════════════════════
// Size preservation
// ══════════════════════════════════════════════════════════════

/// permute_modes preserves shape_size.
/// Uses the swap bridge: decompose permutation into adjacent swaps (ghost witness).
pub proof fn lemma_permute_modes_size(layout: &LayoutSpec, perm: Seq<nat>, swaps: Seq<nat>)
    requires
        layout.valid(),
        is_valid_permutation(perm, layout.shape.len()),
        // Ghost witness: swaps decompose the permutation
        apply_swaps(*layout, swaps) == permute_modes(*layout, perm),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        shape_size(permute_modes(*layout, perm).shape) == shape_size(layout.shape),
{
    lemma_apply_swaps_size(*layout, swaps);
}

// ══════════════════════════════════════════════════════════════
// Injectivity / surjectivity / bijectivity preservation
// ══════════════════════════════════════════════════════════════

/// permute_modes preserves injectivity (via swap decomposition witness).
pub proof fn lemma_permute_modes_injective(layout: &LayoutSpec, perm: Seq<nat>, swaps: Seq<nat>)
    requires
        layout.valid(),
        layout.is_injective(),
        is_valid_permutation(perm, layout.shape.len()),
        apply_swaps(*layout, swaps) == permute_modes(*layout, perm),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        permute_modes(*layout, perm).is_injective(),
{
    lemma_apply_swaps_preserves_injective(*layout, swaps);
}

/// permute_modes preserves surjectivity (via swap decomposition witness).
pub proof fn lemma_permute_modes_surjective(
    layout: &LayoutSpec, perm: Seq<nat>, swaps: Seq<nat>, m: nat,
)
    requires
        layout.valid(),
        layout.is_surjective_upto(m),
        is_valid_permutation(perm, layout.shape.len()),
        apply_swaps(*layout, swaps) == permute_modes(*layout, perm),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        permute_modes(*layout, perm).is_surjective_upto(m),
{
    lemma_apply_swaps_preserves_surjective(*layout, swaps, m);
}

/// permute_modes preserves bijectivity (chains injective + surjective).
pub proof fn lemma_permute_modes_bijective(
    layout: &LayoutSpec, perm: Seq<nat>, swaps: Seq<nat>, m: nat,
)
    requires
        layout.valid(),
        layout.is_bijective_upto(m),
        is_valid_permutation(perm, layout.shape.len()),
        apply_swaps(*layout, swaps) == permute_modes(*layout, perm),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        permute_modes(*layout, perm).is_bijective_upto(m),
{
    lemma_permute_modes_injective(layout, perm, swaps);
    lemma_permute_modes_surjective(layout, perm, swaps, m);
}

// ══════════════════════════════════════════════════════════════
// Composition of permutations
// ══════════════════════════════════════════════════════════════

/// Composing two permutations: permute(permute(L, p1), p2) == permute(L, compose_permutations(p1, p2)).
/// compose_permutations(p1, p2)(i) = p1(p2(i)), so applying p2 after p1 reads through p2 then p1.
pub proof fn lemma_compose_permutations_correct(
    layout: &LayoutSpec, p1: Seq<nat>, p2: Seq<nat>,
)
    requires
        layout.shape.len() == p1.len(),
        layout.stride.len() == p1.len(),
        p1.len() == p2.len(),
        is_valid_permutation(p1, p1.len()),
        is_valid_permutation(p2, p2.len()),
    ensures
        permute_modes(permute_modes(*layout, p1), p2)
            == permute_modes(*layout, compose_permutations(p1, p2)),
{
    let n = p1.len();
    let inner = permute_modes(*layout, p1);
    let double = permute_modes(inner, p2);
    let cp = compose_permutations(p1, p2);
    let composed = permute_modes(*layout, cp);

    // Extensional equality on shape
    // double.shape[i] = inner.shape[p2[i]] = layout.shape[p1[p2[i]]] = layout.shape[cp[i]]
    assert(double.shape =~= composed.shape) by {
        assert forall|i: int| 0 <= i < n implies double.shape[i] == composed.shape[i]
        by {
            let p2i = p2[i];
            assert(p2i < n);
            assert(double.shape[i] == inner.shape[p2i as int]);
            assert(inner.shape[p2i as int] == layout.shape[p1[p2i as int] as int]);
            assert(cp[i] == p1[p2[i] as int]);
        };
    };

    // Extensional equality on stride
    assert(double.stride =~= composed.stride) by {
        assert forall|i: int| 0 <= i < n implies double.stride[i] == composed.stride[i]
        by {
            let p2i = p2[i];
            assert(p2i < n);
            assert(double.stride[i] == inner.stride[p2i as int]);
            assert(inner.stride[p2i as int] == layout.stride[p1[p2i as int] as int]);
            assert(cp[i] == p1[p2[i] as int]);
        };
    };
}

/// compose_permutations of two valid permutations is valid.
pub proof fn lemma_compose_permutations_valid(p1: Seq<nat>, p2: Seq<nat>, n: nat)
    requires
        is_valid_permutation(p1, n),
        is_valid_permutation(p2, n),
    ensures
        is_valid_permutation(compose_permutations(p1, p2), n),
{
    let cp = compose_permutations(p1, p2);
    // Range: cp[i] = p1[p2[i]] < n since p2[i] < n and p1[p2[i]] < n
    assert forall|i: nat| i < n implies #[trigger] cp[i as int] < n
    by {
        let p2i = p2[i as int];
        assert(p2i < n);
        assert(p1[p2i as int] < n);
    };

    // Injectivity: if cp[i] == cp[j], then p1[p2[i]] == p1[p2[j]].
    // Since p1 is injective, p2[i] == p2[j]. Since p2 is injective, i == j.
    assert forall|i: nat, j: nat| i < n && j < n && i != j
        implies cp[i as int] != cp[j as int]
    by {
        let p2i = p2[i as int];
        let p2j = p2[j as int];
        // p2 injective: i != j → p2[i] != p2[j]
        assert(p2i != p2j);
        // p1 injective: p2[i] != p2[j] → p1[p2[i]] != p1[p2[j]]
        assert(p1[p2i as int] != p1[p2j as int]);
    };
}

// ══════════════════════════════════════════════════════════════
// Finite pigeonhole principle
// ══════════════════════════════════════════════════════════════

/// Injective function [0,n) → [0,n) is surjective.
/// Proof: induction on n. Drop last element, compress codomain, apply IH.
pub proof fn lemma_finite_pigeonhole(perm: Seq<nat>, target: nat)
    requires
        forall|i: nat| i < perm.len() ==> #[trigger] perm[i as int] < perm.len(),
        forall|i: nat, j: nat| i < perm.len() && j < perm.len() && i != j
            ==> perm[i as int] != perm[j as int],
        target < perm.len(),
    ensures
        exists|j: nat| j < perm.len() && perm[j as int] == target,
    decreases perm.len(),
{
    let n = perm.len();
    if n == 0 {
        return;
    }
    let last = perm[(n - 1) as int];
    if last == target {
        let witness: nat = (n - 1) as nat;
        assert(witness < perm.len() && perm[witness as int] == target);
        return;
    }
    // Build compressed permutation g: [0,n-1) → [0,n-1)
    // Removes `last` from the codomain by shifting values above it down by 1.
    let g = Seq::new((n - 1) as nat, |i: int|
        if perm[i] < last { perm[i] } else { (perm[i] - 1) as nat }
    );
    let target_c: nat = if target < last { target } else { (target - 1) as nat };

    // g maps into [0, n-1)
    assert forall|i: nat| i < g.len() implies #[trigger] g[i as int] < g.len() by {
        assert(perm[i as int] < n);
        // perm[i] != last since i != n-1 and perm is injective
        assert(i != (n - 1) as nat);
        assert(perm[i as int] != perm[(n - 1) as int]);
        if perm[i as int] < last {
            // g[i] = perm[i] < last ≤ n-1
        } else {
            // perm[i] > last (since != last), g[i] = perm[i]-1 ≤ n-2 < n-1
            assert(perm[i as int] > 0nat);
        }
    };

    // g is injective
    assert forall|i: nat, j: nat|
        i < g.len() && j < g.len() && i != j
        implies g[i as int] != g[j as int]
    by {
        assert(perm[i as int] != perm[j as int]);
        assert(i != (n - 1) as nat);
        assert(j != (n - 1) as nat);
        assert(perm[i as int] != last);
        assert(perm[j as int] != last);

        if perm[i as int] < last && perm[j as int] < last {
            // g[i] = perm[i] != perm[j] = g[j]
        } else if perm[i as int] > last && perm[j as int] > last {
            // g[i] = perm[i]-1 != perm[j]-1 = g[j]
        } else if perm[i as int] < last && perm[j as int] > last {
            // g[i] = perm[i] ≤ last-1, g[j] = perm[j]-1 ≥ last
            assert(perm[i as int] <= (last - 1) as nat);
            assert(perm[j as int] >= last + 1);
            assert(g[j as int] >= last);
        } else {
            // perm[i] > last, perm[j] < last
            assert(perm[i as int] >= last + 1);
            assert(g[i as int] >= last);
            assert(perm[j as int] <= (last - 1) as nat);
        }
    };

    // target_c < n-1
    if target < last {
    } else {
        assert(target > last);
        assert(target >= 1nat);
    }

    // Apply IH
    lemma_finite_pigeonhole(g, target_c);
    let j = choose|j: nat| j < g.len() && g[j as int] == target_c;

    // Reconstruct: perm[j] == target
    assert(j < (n - 1) as nat);
    if perm[j as int] < last {
        // g[j] = perm[j] = target_c
        if target < last {
            // target_c = target, so perm[j] = target
        } else {
            // target > last, target_c = target-1, perm[j] = target-1
            // But perm[j] < last < target, so perm[j] < target-1... contradiction
            // perm[j] = target-1 >= last (since target > last) but perm[j] < last
            assert(false);
        }
    } else {
        // perm[j] >= last, and != last (since j < n-1), so perm[j] > last
        // g[j] = perm[j]-1 = target_c
        assert(perm[j as int] != last);
        assert(perm[j as int] > last);
        if target > last {
            // target_c = target-1, perm[j]-1 = target-1, so perm[j] = target
        } else {
            // target < last, target_c = target, perm[j]-1 = target
            // perm[j] = target+1 ≤ last (since target < last), but perm[j] > last
            assert(false);
        }
    }
    assert(perm[j as int] == target);
    assert(j < perm.len() && perm[j as int] == target);
}

} // verus!
