use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::composition::*;
use crate::proof::shape_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Column-major layout validity helpers
// ══════════════════════════════════════════════════════════════

/// Column-major strides have the same length as the shape.
pub proof fn lemma_column_major_strides_len(shape: Seq<nat>)
    ensures column_major_strides(shape).len() == shape.len(),
    decreases shape.len(),
{
    if shape.len() == 0 {
    } else {
        lemma_column_major_strides_len(shape.skip(1));
    }
}

/// A column-major layout is valid.
pub proof fn lemma_column_major_valid(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_column_major(shape).valid(),
{
    lemma_column_major_strides_len(shape);
}

// ══════════════════════════════════════════════════════════════
// Dot product with scaled strides
// ══════════════════════════════════════════════════════════════

/// Factoring a scalar out of strides: dot(a, scale(b, c)) == c * dot(a, b).
pub proof fn lemma_dot_product_scale(coords: Seq<nat>, strides: Seq<int>, factor: int)
    requires coords.len() == strides.len(),
    ensures dot_product_nat_int(coords, scale_strides_spec(strides, factor))
            == factor * dot_product_nat_int(coords, strides),
    decreases coords.len(),
{
    let scaled = scale_strides_spec(strides, factor);
    if coords.len() == 0 {
        vstd::arithmetic::mul::lemma_mul_basics(factor);
    } else {
        let c0 = coords.first() as int;
        let s0 = strides.first();

        // scaled.skip(1) =~= scale(strides.skip(1), factor)
        let tail_scaled = scaled.skip(1);
        let scaled_tail = scale_strides_spec(strides.skip(1), factor);
        assert forall|j: int| 0 <= j < tail_scaled.len()
        implies #[trigger] tail_scaled[j] == scaled_tail[j] by {
            assert(tail_scaled[j] == scaled[j + 1]);
            assert(scaled[j + 1] == strides[j + 1] * factor);
            assert(scaled_tail[j] == strides.skip(1)[j] * factor);
        }
        assert(tail_scaled =~= scaled_tail);

        // Inductive hypothesis
        lemma_dot_product_scale(coords.skip(1), strides.skip(1), factor);

        // c0 * (s0 * factor) == factor * (c0 * s0)
        vstd::arithmetic::mul::lemma_mul_is_associative(c0, s0, factor);
        vstd::arithmetic::mul::lemma_mul_is_commutative(c0 * s0, factor);

        // factor * (c0 * s0) + factor * dot_tail == factor * (c0 * s0 + dot_tail)
        let dot_tail = dot_product_nat_int(coords.skip(1), strides.skip(1));
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(factor, c0 * s0, dot_tail);
    }
}

// ══════════════════════════════════════════════════════════════
// Column-major dot product equals linearize
// ══════════════════════════════════════════════════════════════

/// For column-major strides, the dot product with coordinates equals linearize.
pub proof fn lemma_column_major_dot_is_linearize(coords: Seq<nat>, shape: Seq<nat>)
    requires
        coords.len() == shape.len(),
        shape_valid(shape),
    ensures
        dot_product_nat_int(coords, column_major_strides(shape)) == linearize(coords, shape),
    decreases shape.len(),
{
    if shape.len() == 0 {
    } else {
        let cm = column_major_strides(shape);
        let cm_tail = column_major_strides(shape.skip(1));
        let scaled_tail = scale_strides_spec(cm_tail, shape.first() as int);

        // cm = [1].add(scaled_tail), so cm.first() == 1
        assert(cm.first() == 1int);
        // cm.skip(1) =~= scaled_tail
        assert(cm.skip(1) =~= scaled_tail);

        // dot_product_scale precondition: coords.skip(1).len() == cm_tail.len()
        lemma_column_major_strides_len(shape.skip(1));

        // dot(coords.skip(1), scaled_tail) == shape[0] * dot(coords.skip(1), cm_tail)
        lemma_dot_product_scale(coords.skip(1), cm_tail, shape.first() as int);

        // dot(coords.skip(1), cm_tail) == linearize(coords.skip(1), shape.skip(1))
        lemma_column_major_dot_is_linearize(coords.skip(1), shape.skip(1));

        // coords[0] * 1 == coords[0]
        vstd::arithmetic::mul::lemma_mul_basics(coords.first() as int);
    }
}

// ══════════════════════════════════════════════════════════════
// Column-major offset is the identity function
// ══════════════════════════════════════════════════════════════

/// For a column-major layout, offset(i) == i.
pub proof fn lemma_column_major_offset_is_identity(shape: Seq<nat>, idx: nat)
    requires
        shape_valid(shape),
        idx < shape_size(shape),
    ensures
        make_column_major(shape).offset(idx) == idx as int,
{
    let coords = delinearize(idx, shape);
    lemma_delinearize_len(idx, shape);
    lemma_column_major_dot_is_linearize(coords, shape);
    lemma_delinearize_roundtrip(idx, shape);
}

// ══════════════════════════════════════════════════════════════
// Column-major layout injectivity and bijectivity
// ══════════════════════════════════════════════════════════════

/// A column-major layout is injective for any valid shape.
pub proof fn lemma_column_major_injective(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_column_major(shape).is_injective(),
{
    let layout = make_column_major(shape);
    assert forall|i: nat, j: nat|
        i < layout.size() && j < layout.size() && i != j
    implies
        #[trigger] layout.offset(i) != #[trigger] layout.offset(j)
    by {
        lemma_column_major_offset_is_identity(shape, i);
        lemma_column_major_offset_is_identity(shape, j);
    }
}

/// A column-major layout is bijective onto [0, size).
pub proof fn lemma_column_major_bijective(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_column_major(shape).is_bijective_upto(shape_size(shape)),
{
    let layout = make_column_major(shape);
    lemma_column_major_injective(shape);

    assert forall|k: int| 0 <= k < shape_size(shape) as int
    implies #[trigger] layout.offset_hit(k) by {
        let idx = k as nat;
        lemma_column_major_offset_is_identity(shape, idx);
    }
}

// ══════════════════════════════════════════════════════════════
// Identity layout: special case of column-major
// ══════════════════════════════════════════════════════════════

/// make_identity(m) and make_column_major(seq![m]) have the same offset function.
proof fn lemma_identity_is_column_major(m: nat)
    requires m > 0,
    ensures
        make_identity(m).shape =~= make_column_major(seq![m as nat]).shape,
        make_identity(m).stride =~= make_column_major(seq![m as nat]).stride,
{
    let s = seq![m as nat];
    // column_major_strides(seq![m]) = [1].add(scale_strides(column_major_strides([]), m))
    //                                = [1].add(scale_strides([], m))
    //                                = [1].add([])
    //                                = [1]
    assert(column_major_strides(s.skip(1)) =~= seq![]);
    assert(scale_strides_spec(seq![], m as int) =~= seq![]);
    assert(column_major_strides(s) =~= seq![1int]);
}

/// The identity layout (M):(1) is injective.
pub proof fn lemma_identity_injective(m: nat)
    requires m > 0,
    ensures make_identity(m).is_injective(),
{
    lemma_identity_is_column_major(m);
    lemma_column_major_injective(seq![m as nat]);
}

/// The identity layout (M):(1) is bijective onto [0, M).
pub proof fn lemma_identity_bijective(m: nat)
    requires m > 0,
    ensures make_identity(m).is_bijective_upto(m),
{
    lemma_identity_is_column_major(m);

    // shape_size(seq![m]) == m
    assert(shape_size(seq![m as nat]) == m * shape_size(seq![m as nat].skip(1)));
    assert(seq![m as nat].skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(m as int);

    lemma_column_major_bijective(seq![m as nat]);
}

// ══════════════════════════════════════════════════════════════
// Injectivity preservation under composition (rank-1 A)
// ══════════════════════════════════════════════════════════════

/// If A (rank-1) and B are both injective, and B's image fits within A's domain,
/// then compose(A, B) is injective.
pub proof fn lemma_compose_preserves_injectivity_1d_a(a: LayoutSpec, b: LayoutSpec)
    requires
        a.valid(), b.valid(),
        a.shape.len() == 1,
        b.non_negative_strides(),
        a.is_injective(),
        b.is_injective(),
        // B's image fits within A's domain for all valid indices
        forall|x: nat| x < b.size() ==> b.offset(x) >= 0 && b.offset(x) < a.shape.first() as int,
    ensures
        compose(a, b).is_injective(),
{
    let c = compose(a, b);

    // c.shape =~= b.shape, so c.size() == b.size()
    crate::proof::composition_lemmas::lemma_compose_shape(a, b);

    // a.size() == a.shape[0] for rank-1 A
    assert(shape_size(a.shape) == a.shape.first() * shape_size(a.shape.skip(1)));
    assert(a.shape.skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(a.shape.first() as int);
    assert(a.size() == a.shape.first());

    assert forall|i: nat, j: nat|
        i < c.size() && j < c.size() && i != j
    implies
        #[trigger] c.offset(i) != #[trigger] c.offset(j)
    by {
        // c.size() == b.size() (since c.shape == b.shape)
        assert(i < b.size());
        assert(j < b.size());

        // c.offset(i) == a.offset(b.offset(i))
        crate::proof::composition_lemmas::lemma_compose_correct_1d_a(a, b, i);
        crate::proof::composition_lemmas::lemma_compose_correct_1d_a(a, b, j);

        // B injective: i != j ==> b.offset(i) != b.offset(j)
        assert(b.offset(i) != b.offset(j));

        // b.offset values are valid indices for A
        let bi = b.offset(i) as nat;
        let bj = b.offset(j) as nat;
        assert(bi < a.size());
        assert(bj < a.size());
        assert(bi != bj);

        // A injective: bi != bj ==> a.offset(bi) != a.offset(bj)
        assert(a.offset(bi) != a.offset(bj));
    }
}

// ══════════════════════════════════════════════════════════════
// Coalesce preserves injectivity (position 0)
// ══════════════════════════════════════════════════════════════

/// If a layout is injective, coalescing at position 0 preserves injectivity.
pub proof fn lemma_coalesce_preserves_injectivity(layout: LayoutSpec)
    requires
        layout.valid(),
        layout.shape.len() >= 2,
        crate::coalesce::modes_coalesceable(&layout, 0),
        layout.is_injective(),
    ensures
        crate::coalesce::coalesce_pair(layout, 0).is_injective(),
{
    let cp = crate::coalesce::coalesce_pair(layout, 0);
    crate::proof::coalesce_lemmas::lemma_coalesce_pair_size(layout);
    // cp.size() == layout.size()

    assert forall|i: nat, j: nat|
        i < cp.size() && j < cp.size() && i != j
    implies
        #[trigger] cp.offset(i) != #[trigger] cp.offset(j)
    by {
        crate::proof::coalesce_lemmas::lemma_coalesce_pair_offset(layout, i);
        crate::proof::coalesce_lemmas::lemma_coalesce_pair_offset(layout, j);
        // cp.offset(i) == layout.offset(i), cp.offset(j) == layout.offset(j)
        // layout injective: layout.offset(i) != layout.offset(j)
    }
}

// ══════════════════════════════════════════════════════════════
// Injectivity from offset-identity
// ══════════════════════════════════════════════════════════════

/// Any layout whose offset function is the identity (offset(i) == i) is injective.
/// Useful as a general principle for various layout transformations.
pub proof fn lemma_identity_offset_implies_injective(layout: LayoutSpec)
    requires
        layout.valid(),
        forall|i: nat| i < layout.size() ==> layout.offset(i) == i as int,
    ensures
        layout.is_injective(),
{
    assert forall|i: nat, j: nat|
        i < layout.size() && j < layout.size() && i != j
    implies
        #[trigger] layout.offset(i) != #[trigger] layout.offset(j)
    by {}
}

/// Any layout whose offset function is the identity is bijective onto [0, size).
pub proof fn lemma_identity_offset_implies_bijective(layout: LayoutSpec)
    requires
        layout.valid(),
        forall|i: nat| i < layout.size() ==> layout.offset(i) == i as int,
    ensures
        layout.is_bijective_upto(layout.size()),
{
    lemma_identity_offset_implies_injective(layout);
    assert forall|k: int| 0 <= k < layout.size() as int
    implies #[trigger] layout.offset_hit(k) by {
        let idx = k as nat;
        assert(idx < layout.size());
        assert(layout.offset(idx) == k);
    }
}

} // verus!
