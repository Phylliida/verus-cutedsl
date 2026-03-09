use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::coalesce::*;
use crate::compatibility::*;
use crate::composition::*;
use crate::product::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Equivalence relation properties
// ══════════════════════════════════════════════════════════════

/// offset_equivalent is reflexive.
pub proof fn lemma_offset_equivalent_reflexive(l: &LayoutSpec)
    requires l.valid(),
    ensures offset_equivalent(l, l),
{
}

/// offset_equivalent is symmetric.
pub proof fn lemma_offset_equivalent_symmetric(l1: &LayoutSpec, l2: &LayoutSpec)
    requires
        l1.valid(), l2.valid(),
        offset_equivalent(l1, l2),
    ensures offset_equivalent(l2, l1),
{
    assert forall|i: nat| i < l2.size() implies l2.offset(i) == l1.offset(i)
    by {
        assert(l1.offset(i) == l2.offset(i));
    };
}

/// offset_equivalent is transitive.
pub proof fn lemma_offset_equivalent_transitive(l1: &LayoutSpec, l2: &LayoutSpec, l3: &LayoutSpec)
    requires
        l1.valid(), l2.valid(), l3.valid(),
        offset_equivalent(l1, l2),
        offset_equivalent(l2, l3),
    ensures offset_equivalent(l1, l3),
{
    assert forall|i: nat| i < l1.size() implies l1.offset(i) == l3.offset(i)
    by {
        assert(l1.offset(i) == l2.offset(i));
        assert(l2.offset(i) == l3.offset(i));
    };
}

// ══════════════════════════════════════════════════════════════
// Subset/extension
// ══════════════════════════════════════════════════════════════

/// offset_compatible at m implies offset_compatible at any k <= m.
pub proof fn lemma_offset_compatible_monotone(l1: &LayoutSpec, l2: &LayoutSpec, m: nat, k: nat)
    requires
        offset_compatible(l1, l2, m),
        k <= m,
    ensures offset_compatible(l1, l2, k),
{
}

/// offset_equivalent implies offset_compatible at their common size.
pub proof fn lemma_equivalent_implies_compatible(l1: &LayoutSpec, l2: &LayoutSpec)
    requires offset_equivalent(l1, l2),
    ensures offset_compatible(l1, l2, l1.size()),
{
}

// ══════════════════════════════════════════════════════════════
// Operation preservation
// ══════════════════════════════════════════════════════════════

/// Coalesce preserves offset equivalence.
pub proof fn lemma_coalesce_offset_equivalent(layout: &LayoutSpec)
    requires layout.valid(),
    ensures offset_equivalent(layout, &coalesce(*layout)),
{
    crate::proof::shape_lemmas::lemma_shape_size_positive(layout.shape);
    assert forall|i: nat| i < layout.size() implies layout.offset(i) == coalesce(*layout).offset(i)
    by {
        crate::proof::coalesce_lemmas::lemma_coalesce(*layout, i);
    };
    crate::proof::coalesce_lemmas::lemma_coalesce(*layout, 0);
}

/// Flatten preserves offset equivalence.
pub proof fn lemma_flatten_offset_equivalent(layout: &LayoutSpec)
    requires layout.valid(),
    ensures offset_equivalent(layout, &flatten(*layout)),
{
    crate::proof::shape_lemmas::lemma_shape_size_positive(layout.shape);
    assert forall|i: nat| i < layout.size() implies layout.offset(i) == flatten(*layout).offset(i)
    by {
        crate::proof::coalesce_lemmas::lemma_flatten_offset(*layout, i);
    };
    crate::proof::coalesce_lemmas::lemma_flatten_size(*layout);
}

/// group_modes preserves offset equivalence.
pub proof fn lemma_group_modes_offset_equivalent(layout: &LayoutSpec, lo: nat, hi: nat)
    requires group_modes_admissible(layout, lo, hi),
    ensures offset_equivalent(layout, &group_modes(*layout, lo, hi)),
{
    crate::proof::shape_lemmas::lemma_shape_size_positive(layout.shape);
    assert forall|i: nat| i < layout.size() implies
        layout.offset(i) == group_modes(*layout, lo, hi).offset(i)
    by {
        crate::proof::coalesce_lemmas::lemma_group_modes_offset(*layout, lo, hi, i);
    };
    crate::proof::coalesce_lemmas::lemma_group_modes_size(*layout, lo, hi);
}

// ══════════════════════════════════════════════════════════════
// Property transfer
// ══════════════════════════════════════════════════════════════

/// Injectivity transfers across offset-equivalent layouts.
pub proof fn lemma_equivalent_transfers_injectivity(l1: &LayoutSpec, l2: &LayoutSpec)
    requires
        l1.valid(), l2.valid(),
        offset_equivalent(l1, l2),
        l1.is_injective(),
    ensures l2.is_injective(),
{
    assert forall|x: nat, y: nat| x < l2.size() && y < l2.size() && x != y
        implies l2.offset(x) != l2.offset(y)
    by {
        assert(l1.offset(x) == l2.offset(x));
        assert(l1.offset(y) == l2.offset(y));
    };
}

/// Surjectivity transfers across offset-equivalent layouts.
pub proof fn lemma_equivalent_transfers_surjectivity(l1: &LayoutSpec, l2: &LayoutSpec, m: nat)
    requires
        l1.valid(), l2.valid(),
        offset_equivalent(l1, l2),
        l1.is_surjective_upto(m),
    ensures l2.is_surjective_upto(m),
{
    assert forall|k: int| 0 <= k < m as int
        implies #[trigger] l2.offset_hit(k)
    by {
        assert(l1.offset_hit(k));
        let x: nat = choose|x: nat| x < l1.size() && l1.offset(x) == k;
        assert(x < l1.size() && l1.offset(x) == k);
        assert(l2.offset(x) == k);
        assert(x < l2.size());
    };
}

/// Bijectivity transfers across offset-equivalent layouts.
pub proof fn lemma_equivalent_transfers_bijectivity(l1: &LayoutSpec, l2: &LayoutSpec, m: nat)
    requires
        l1.valid(), l2.valid(),
        offset_equivalent(l1, l2),
        l1.is_bijective_upto(m),
    ensures l2.is_bijective_upto(m),
{
    lemma_equivalent_transfers_injectivity(l1, l2);
    lemma_equivalent_transfers_surjectivity(l1, l2, m);
}

// ══════════════════════════════════════════════════════════════
// Congruence: offset-equivalent inputs → offset-equivalent outputs
// ══════════════════════════════════════════════════════════════

/// Compose congruence: varying B while A is fixed.
/// compose(A, B1) ≡ compose(A, B2) when B1 ≡ B2.
pub proof fn lemma_compose_congruence_b(a: &LayoutSpec, b1: &LayoutSpec, b2: &LayoutSpec)
    requires
        a.valid(), b1.valid(), b2.valid(),
        a.shape.len() > 0,
        b1.non_negative_strides(), b2.non_negative_strides(),
        offset_equivalent(b1, b2),
        forall|x: nat| x < b1.size() ==> b1.offset(x) >= 0 && b1.offset(x) < a.shape.first() as int,
        forall|x: nat| x < b2.size() ==> b2.offset(x) >= 0 && b2.offset(x) < a.shape.first() as int,
    ensures
        offset_equivalent(&compose(*a, *b1), &compose(*a, *b2)),
{
    let c1 = compose(*a, *b1);
    let c2 = compose(*a, *b2);

    // compose preserves B's shape, so c1.size() == b1.size() == b2.size() == c2.size()
    crate::proof::composition_lemmas::lemma_compose_shape(*a, *b1);
    crate::proof::composition_lemmas::lemma_compose_shape(*a, *b2);

    assert forall|x: nat| x < c1.size() implies c1.offset(x) == c2.offset(x)
    by {
        crate::proof::composition_lemmas::lemma_compose_correct(*a, *b1, x);
        crate::proof::composition_lemmas::lemma_compose_correct(*a, *b2, x);
        // c1.offset(x) == a.offset(b1.offset(x)), c2.offset(x) == a.offset(b2.offset(x))
        // b1.offset(x) == b2.offset(x) since x < b1.size() and layouts are offset-equivalent
        assert(b1.offset(x) == b2.offset(x));
    };
}

/// Compose congruence: varying A while B is fixed.
/// compose(A1, B) ≡ compose(A2, B) when A1 ≡ A2.
pub proof fn lemma_compose_congruence_a(a1: &LayoutSpec, a2: &LayoutSpec, b: &LayoutSpec)
    requires
        a1.valid(), a2.valid(), b.valid(),
        a1.shape.len() > 0, a2.shape.len() > 0,
        offset_equivalent(a1, a2),
        b.non_negative_strides(),
        forall|x: nat| x < b.size() ==> b.offset(x) >= 0 && b.offset(x) < a1.shape.first() as int,
        forall|x: nat| x < b.size() ==> b.offset(x) >= 0 && b.offset(x) < a2.shape.first() as int,
    ensures
        offset_equivalent(&compose(*a1, *b), &compose(*a2, *b)),
{
    let c1 = compose(*a1, *b);
    let c2 = compose(*a2, *b);

    crate::proof::composition_lemmas::lemma_compose_shape(*a1, *b);
    crate::proof::composition_lemmas::lemma_compose_shape(*a2, *b);

    assert forall|x: nat| x < c1.size() implies c1.offset(x) == c2.offset(x)
    by {
        crate::proof::composition_lemmas::lemma_compose_correct(*a1, *b, x);
        crate::proof::composition_lemmas::lemma_compose_correct(*a2, *b, x);
        let bx = b.offset(x) as nat;
        // bx < a1.shape[0] <= a1.size(), so bx is in range for offset_equivalent
        crate::proof::shape_lemmas::lemma_size_at_least_first(a1.shape);
        assert(a1.offset(bx) == a2.offset(bx));
    };
}

/// Product congruence: varying B in logical_product.
/// product(A, B1) ≡ product(A, B2) when B1 ≡ B2.
pub proof fn lemma_product_congruence_right(a: &LayoutSpec, b1: &LayoutSpec, b2: &LayoutSpec)
    requires
        a.valid(), b1.valid(), b2.valid(),
        product_admissible(a, b1),
        product_admissible(a, b2),
        offset_equivalent(b1, b2),
    ensures
        offset_equivalent(&logical_product(a, b1), &logical_product(a, b2)),
{
    let p1 = logical_product(a, b1);
    let p2 = logical_product(a, b2);
    let sa = a.size();
    let sb = b1.size();

    crate::proof::product_lemmas::lemma_product_size(a, b1);
    crate::proof::product_lemmas::lemma_product_size(a, b2);
    crate::proof::product_lemmas::lemma_product_valid(a, b1);
    crate::proof::product_lemmas::lemma_product_valid(a, b2);

    assert forall|x: nat| x < p1.size() implies p1.offset(x) == p2.offset(x)
    by {
        crate::proof::product_lemmas::lemma_product_offset(a, b1, x);
        crate::proof::product_lemmas::lemma_product_offset(a, b2, x);
        crate::proof::shape_lemmas::lemma_shape_size_positive(a.shape);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, sa, sb);
        assert(b1.offset(x / sa) == b2.offset(x / sa));
    };
}

/// Product congruence: varying A in logical_product.
/// product(A1, B) ≡ product(A2, B) when A1 ≡ A2 and both have equal cosize.
pub proof fn lemma_product_congruence_left(
    a1: &LayoutSpec, a2: &LayoutSpec, b: &LayoutSpec,
    cosize: nat,
)
    requires
        a1.valid(), a2.valid(), b.valid(),
        product_admissible(a1, b),
        product_admissible(a2, b),
        offset_equivalent(a1, a2),
        a1.cosize_nonneg() == cosize,
        a2.cosize_nonneg() == cosize,
    ensures
        offset_equivalent(&logical_product(a1, b), &logical_product(a2, b)),
{
    let p1 = logical_product(a1, b);
    let p2 = logical_product(a2, b);
    let sa = a1.size();

    crate::proof::product_lemmas::lemma_product_size(a1, b);
    crate::proof::product_lemmas::lemma_product_size(a2, b);
    crate::proof::product_lemmas::lemma_product_valid(a1, b);
    crate::proof::product_lemmas::lemma_product_valid(a2, b);

    assert forall|x: nat| x < p1.size() implies p1.offset(x) == p2.offset(x)
    by {
        crate::proof::product_lemmas::lemma_product_offset(a1, b, x);
        crate::proof::product_lemmas::lemma_product_offset(a2, b, x);
        crate::proof::shape_lemmas::lemma_shape_size_positive(a1.shape);
        assert(a1.offset(x % sa) == a2.offset(x % sa));
    };
}

/// Raked product congruence: varying A in raked_product.
/// raked_product(A1, B) ≡ raked_product(A2, B) when A1 ≡ A2.
pub proof fn lemma_raked_product_congruence_left(
    a1: &LayoutSpec, a2: &LayoutSpec, b: &LayoutSpec,
    cosize: nat,
)
    requires
        a1.valid(), a2.valid(), b.valid(),
        raked_product_admissible(a1, b),
        raked_product_admissible(a2, b),
        offset_equivalent(a1, a2),
        b.cosize_nonneg() == cosize,
    ensures
        offset_equivalent(&raked_product(a1, b), &raked_product(a2, b)),
{
    let r1 = raked_product(a1, b);
    let r2 = raked_product(a2, b);
    let sa = a1.size();

    crate::proof::product_lemmas::lemma_raked_product_size(a1, b);
    crate::proof::product_lemmas::lemma_raked_product_size(a2, b);
    crate::proof::product_lemmas::lemma_raked_product_valid(a1, b);
    crate::proof::product_lemmas::lemma_raked_product_valid(a2, b);

    assert forall|x: nat| x < r1.size() implies r1.offset(x) == r2.offset(x)
    by {
        crate::proof::product_lemmas::lemma_raked_product_offset(a1, b, x);
        crate::proof::product_lemmas::lemma_raked_product_offset(a2, b, x);
        // r1.offset(x) == cosize * a1.offset(x % sa) + b.offset(x / sa)
        // r2.offset(x) == cosize * a2.offset(x % sa) + b.offset(x / sa)
        crate::proof::shape_lemmas::lemma_shape_size_positive(a1.shape);
        assert(a1.offset(x % sa) == a2.offset(x % sa));
    };
}

} // verus!
