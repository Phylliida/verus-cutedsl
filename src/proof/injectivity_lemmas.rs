use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::composition::*;
use crate::proof::shape_lemmas::*;
use crate::proof::product_lemmas::lemma_shape_size_append;

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

// ══════════════════════════════════════════════════════════════
// General: sorted tractable layouts are injective
// ══════════════════════════════════════════════════════════════

/// Helper: in a tractable layout, all strides from index 1 onward are multiples
/// of stride_product_0 = shape[0] * stride[0].
proof fn lemma_tractable_higher_strides_multiple(
    shape: Seq<nat>, strides: Seq<int>, j: int,
)
    requires
        shape.len() == strides.len(),
        shape.len() > 0,
        shape_valid(shape),
        forall|i: int| 0 <= i < strides.len() ==> #[trigger] strides[i] > 0,
        // tractable
        forall|i: int| 0 <= i < strides.len() - 1 ==>
            (#[trigger] strides[i + 1]) % ((shape[i] as int) * strides[i]) == 0,
        1 <= j < strides.len(),
    ensures
        strides[j] % ((shape.first() as int) * strides.first()) == 0,
    decreases j,
{
    let d = (shape.first() as int) * strides.first();
    crate::proof::integer_helpers::lemma_mul_pos(shape.first(), strides.first() as nat);
    if j == 1 {
        // Direct from tractability at i=0: strides[1] % (shape[0]*strides[0]) == 0
        assert(strides[0int + 1] == strides[1]); // trigger
    } else {
        // IH: strides[j-1] % d == 0
        lemma_tractable_higher_strides_multiple(shape, strides, j - 1);
        // tractability at j-1: strides[j] % (shape[j-1] * strides[j-1]) == 0
        let product_jm1 = (shape[j - 1] as int) * strides[j - 1];
        assert(strides[(j - 1) + 1] == strides[j]); // trigger tractability at j-1
        assert(strides[j] % product_jm1 == 0);
        // product_jm1 > 0
        crate::proof::integer_helpers::lemma_mul_pos(shape[j - 1], strides[j - 1] as nat);
        // product_jm1 = shape[j-1]*strides[j-1], strides[j-1] % d == 0, so product_jm1 % d == 0
        crate::proof::integer_helpers::lemma_multiple_of_multiple(
            strides[j - 1], shape[j - 1], d,
        );
        assert(product_jm1 % d == 0);
        // Divisibility transitivity: strides[j] % product_jm1 == 0 && product_jm1 % d == 0
        //                          => strides[j] % d == 0
        crate::proof::integer_helpers::lemma_divisibility_transitive(
            strides[j], product_jm1, d,
        );
    }
}

/// Helper: dot product with strides that are all multiples of d gives a multiple of d.
proof fn lemma_dot_with_multiples(
    coords: Seq<nat>, strides: Seq<int>, d: int,
)
    requires
        coords.len() == strides.len(),
        d > 0,
        forall|j: int| 0 <= j < strides.len() ==> #[trigger] strides[j] % d == 0,
        forall|j: int| 0 <= j < strides.len() ==> #[trigger] strides[j] >= 0,
    ensures
        dot_product_nat_int(coords, strides) % d == 0,
    decreases coords.len(),
{
    if coords.len() == 0 {
        // dot = 0, 0 % d == 0
        assert(dot_product_nat_int(coords, strides) == 0);
    } else {
        // dot = coords[0] * strides[0] + dot(tail)
        lemma_dot_with_multiples(coords.skip(1), strides.skip(1), d);
        // coords[0] * strides[0] % d == 0
        crate::proof::integer_helpers::lemma_multiple_of_multiple(
            strides.first(), coords.first(), d,
        );
        // sum of two multiples of d
        crate::proof::integer_helpers::lemma_sum_multiples(
            coords.first() as int * strides.first(),
            dot_product_nat_int(coords.skip(1), strides.skip(1)),
            d,
        );
    }
}

/// If two in-bounds coordinate vectors produce the same dot product with
/// tractable strides (all positive), they must be equal.
///
/// Proof: By induction on rank. The mod-based argument shows c1[0]==c2[0]
/// (since higher stride terms are multiples of shape[0]*stride[0], and the first
/// term is in [0, shape[0]*stride[0])), then the tail dots are equal,
/// and the IH gives tail equality.
proof fn lemma_tractable_dot_determines_coords(
    c1: Seq<nat>, c2: Seq<nat>, shape: Seq<nat>, strides: Seq<int>,
)
    requires
        c1.len() == shape.len(),
        c2.len() == shape.len(),
        shape.len() == strides.len(),
        shape_valid(shape),
        coords_in_bounds(c1, shape),
        coords_in_bounds(c2, shape),
        // all strides positive
        forall|i: int| 0 <= i < strides.len() ==> #[trigger] strides[i] > 0,
        // tractable
        forall|i: int| 0 <= i < strides.len() - 1 ==>
            (#[trigger] strides[i + 1]) % ((shape[i] as int) * strides[i]) == 0,
        dot_product_nat_int(c1, strides) == dot_product_nat_int(c2, strides),
    ensures
        c1 =~= c2,
    decreases shape.len(),
{
    if shape.len() == 0 {
        // Both empty
    } else {
        let d0 = strides.first();
        let s0 = shape.first();
        let product0 = (s0 as int) * d0;

        // product0 > 0
        crate::proof::integer_helpers::lemma_mul_pos(s0, d0 as nat);

        // == Step 1: Show dot(c.skip(1), strides.skip(1)) is a multiple of product0 ==
        assert forall|j: int| 0 <= j < strides.skip(1).len()
        implies #[trigger] strides.skip(1)[j] % product0 == 0 by {
            assert(strides.skip(1)[j] == strides[j + 1]);
            lemma_tractable_higher_strides_multiple(shape, strides, j + 1);
        };

        // Tail strides are also non-negative (actually positive)
        assert forall|j: int| 0 <= j < strides.skip(1).len()
        implies #[trigger] strides.skip(1)[j] >= 0 by {
            assert(strides.skip(1)[j] == strides[j + 1]);
        };

        // So tail dots are multiples of product0
        lemma_dot_with_multiples(c1.skip(1), strides.skip(1), product0);
        lemma_dot_with_multiples(c2.skip(1), strides.skip(1), product0);

        let tail1 = dot_product_nat_int(c1.skip(1), strides.skip(1));
        let tail2 = dot_product_nat_int(c2.skip(1), strides.skip(1));

        // == Step 2: Show c1[0] == c2[0] via mod argument ==
        let term1 = c1.first() as int * d0;
        let term2 = c2.first() as int * d0;

        // 0 <= term1, term2
        crate::proof::integer_helpers::lemma_mul_nonneg(c1.first() as int, d0);
        crate::proof::integer_helpers::lemma_mul_nonneg(c2.first() as int, d0);

        // term1 <= (s0-1)*d0 < s0*d0 = product0
        crate::proof::integer_helpers::lemma_mul_le_right(
            c1.first() as int, (s0 - 1) as int, d0,
        );
        crate::proof::integer_helpers::lemma_mul_le_right(
            c2.first() as int, (s0 - 1) as int, d0,
        );
        // Now: term1 <= (s0-1)*d0 and term2 <= (s0-1)*d0
        // product0 = s0*d0 = ((s0-1)+1)*d0 = (s0-1)*d0 + 1*d0 = (s0-1)*d0 + d0
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(d0, (s0 - 1) as int, 1int);
        // d0 * ((s0-1) + 1) == d0*(s0-1) + d0*1
        vstd::arithmetic::mul::lemma_mul_basics(d0);
        // d0 * 1 == d0
        vstd::arithmetic::mul::lemma_mul_is_commutative(d0, (s0 - 1) as int);
        // d0*(s0-1) == (s0-1)*d0
        vstd::arithmetic::mul::lemma_mul_is_commutative(d0, s0 as int);
        // d0*s0 == s0*d0 == product0
        assert(product0 == (s0 - 1) as int * d0 + d0);
        assert(term1 < product0);
        assert(term2 < product0);

        // From equal dots: term1 + tail1 == term2 + tail2
        // So diff = term1 - term2 = tail2 - tail1 is a multiple of product0
        let diff = term1 - term2;
        assert(diff == tail2 - tail1);
        crate::proof::integer_helpers::lemma_diff_multiples(tail2, tail1, product0);
        assert(diff % product0 == 0);

        // |diff| < product0 and diff % product0 == 0 => diff == 0
        if diff > 0 {
            // 0 < diff < product0 and diff % product0 == 0
            crate::proof::integer_helpers::lemma_small_multiple_is_zero(diff, product0);
        } else if diff < 0 {
            // 0 < -diff < product0
            // (-diff) % product0 == 0
            crate::proof::integer_helpers::lemma_diff_multiples(tail1, tail2, product0);
            assert((-diff) == tail1 - tail2);
            crate::proof::integer_helpers::lemma_small_multiple_is_zero(-diff, product0);
        }
        assert(diff == 0);
        assert(term1 == term2);

        // c1[0] * d0 == c2[0] * d0 with d0 > 0 => c1[0] == c2[0]
        vstd::arithmetic::mul::lemma_mul_is_commutative(c1.first() as int, d0);
        vstd::arithmetic::mul::lemma_mul_is_commutative(c2.first() as int, d0);
        vstd::arithmetic::mul::lemma_mul_equality_converse(
            d0, c1.first() as int, c2.first() as int,
        );
        assert(c1.first() == c2.first());

        // == Step 3: Tail dots are equal, apply IH ==
        assert(tail1 == tail2);

        // Tail strides are positive
        assert forall|i: int| 0 <= i < strides.skip(1).len()
        implies #[trigger] strides.skip(1)[i] > 0 by {
            assert(strides.skip(1)[i] == strides[i + 1]);
        };

        // Tractability of tail
        assert forall|i: int| 0 <= i < strides.skip(1).len() - 1
        implies (#[trigger] strides.skip(1)[i + 1]) % ((shape.skip(1)[i] as int) * strides.skip(1)[i]) == 0
        by {
            assert(strides.skip(1)[i + 1] == strides[i + 2]);
            assert(strides[(i + 1) + 1] == strides[i + 2]); // trigger original tractability
        };

        lemma_tractable_dot_determines_coords(
            c1.skip(1), c2.skip(1), shape.skip(1), strides.skip(1),
        );
        // c1.skip(1) =~= c2.skip(1) and c1[0] == c2[0] => c1 =~= c2
        assert forall|k: int| 0 <= k < c1.len() implies c1[k] == c2[k] by {
            if k == 0 {
                // c1.first() == c2.first() already proved
            } else {
                assert(c1[k] == c1.skip(1)[k - 1]);
                assert(c2[k] == c2.skip(1)[k - 1]);
            }
        };
        assert(c1 =~= c2);
    }
}

/// A tractable layout with all positive strides is injective.
///
/// This generalizes column-major injectivity to all "well-separated" stride patterns.
/// Key application: complement layouts.
pub proof fn lemma_positive_tractable_injective(layout: LayoutSpec)
    requires
        layout.valid(),
        layout.is_tractable(),
        layout.shape.len() > 0,
        forall|i: int| 0 <= i < layout.stride.len() ==> #[trigger] layout.stride[i] > 0,
    ensures
        layout.is_injective(),
{
    assert forall|i: nat, j: nat|
        i < layout.size() && j < layout.size() && i != j
    implies
        #[trigger] layout.offset(i) != #[trigger] layout.offset(j)
    by {
        let ci = delinearize(i, layout.shape);
        let cj = delinearize(j, layout.shape);
        lemma_delinearize_bounds(i, layout.shape);
        lemma_delinearize_bounds(j, layout.shape);
        lemma_delinearize_roundtrip(i, layout.shape);
        lemma_delinearize_roundtrip(j, layout.shape);
        lemma_delinearize_len(i, layout.shape);
        lemma_delinearize_len(j, layout.shape);

        // If coords were equal, linearize would give i == j (contradiction)
        if ci =~= cj {
            assert(linearize(ci, layout.shape) == linearize(cj, layout.shape));
            assert(false);
        }

        // If offsets were equal, coords would be equal (contradiction)
        if layout.offset(i) == layout.offset(j) {
            // Bridge is_tractable() to raw quantifier form
            assert forall|k: int| 0 <= k < layout.stride.len() - 1
            implies (#[trigger] layout.stride[k + 1]) % ((layout.shape[k] as int) * layout.stride[k]) == 0
            by {
                assert(layout.tractable_at(k));
            };
            lemma_tractable_dot_determines_coords(
                ci, cj, layout.shape, layout.stride,
            );
            assert(false);
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Row-major layout injectivity
// ══════════════════════════════════════════════════════════════

/// Sequence reverse is an involution: rev(rev(s)) =~= s.
proof fn lemma_seq_reverse_involution<A>(s: Seq<A>)
    ensures seq_reverse(seq_reverse(s)) =~= s,
{
    assert forall|i: int| 0 <= i < s.len()
    implies seq_reverse(seq_reverse(s))[i] == s[i] by {
        let j = (s.len() - 1 - i) as int;
        assert(seq_reverse(s)[j] == s[s.len() - 1 - j]);
    };
}

/// Reversing preserves shape validity.
proof fn lemma_shape_valid_reverse(s: Seq<nat>)
    requires shape_valid(s),
    ensures shape_valid(seq_reverse(s)),
{
    assert forall|i: int| 0 <= i < seq_reverse(s).len()
    implies #[trigger] seq_reverse(s)[i] > 0 by {};
}

/// Reversing preserves coordinate bounds.
proof fn lemma_coords_in_bounds_reverse(c: Seq<nat>, s: Seq<nat>)
    requires c.len() == s.len(), coords_in_bounds(c, s),
    ensures coords_in_bounds(seq_reverse(c), seq_reverse(s)),
{
    assert forall|i: int| 0 <= i < seq_reverse(c).len()
    implies #[trigger] seq_reverse(c)[i] < seq_reverse(s)[i] by {};
}

/// Dot product commutes with sequence reversal:
/// dot(c, rev(s)) == dot(rev(c), s).
///
/// Proof: split c = c_init ++ [c.last()] and rev(s) = rev(s.skip(1)) ++ [s[0]],
/// apply dot_product_append, use IH, then reassemble as dot(rev(c), s).
proof fn lemma_dot_product_reverse(c: Seq<nat>, s: Seq<int>)
    requires c.len() == s.len(),
    ensures dot_product_nat_int(c, seq_reverse(s)) == dot_product_nat_int(seq_reverse(c), s),
    decreases c.len(),
{
    if c.len() == 0 {
    } else {
        let n = c.len() as int;
        let c_init = c.take(n - 1);
        let c_last = seq![c[n - 1] as nat];
        let revs = seq_reverse(s);
        let revs_init = seq_reverse(s.skip(1));
        let revs_last = seq![s.first()];

        // c =~= c_init ++ c_last
        assert(c =~= c_init.add(c_last));
        // rev(s) =~= rev(s.skip(1)) ++ [s[0]]
        assert(revs =~= revs_init.add(revs_last)) by {
            assert forall|i: int| 0 <= i < revs.len()
            implies revs[i] == revs_init.add(revs_last)[i] by {
                if i < n - 1 {
                    // revs[i] = s[n-1-i], revs_init[i] = s.skip(1)[(n-2)-i] = s[n-1-i]
                } else {
                    // revs[n-1] = s[0] = revs_last[0]
                }
            };
        };

        // dot(c, rev(s)) = dot(c_init, revs_init) + dot(c_last, revs_last)
        lemma_dot_product_append(c_init, c_last, revs_init, revs_last);

        // IH: dot(c_init, rev(s.skip(1))) == dot(rev(c_init), s.skip(1))
        lemma_dot_product_reverse(c_init, s.skip(1));

        // rev(c_init) =~= rev(c).skip(1)
        assert(seq_reverse(c_init) =~= seq_reverse(c).skip(1)) by {
            assert forall|i: int| 0 <= i < seq_reverse(c_init).len()
            implies seq_reverse(c_init)[i] == seq_reverse(c).skip(1)[i] by {};
        };

        // Chain: dot(c_init, revs_init) = dot(rev(c_init), s.skip(1)) [by IH]
        //                                = dot(rev(c).skip(1), s.skip(1)) [by ext eq]
        let dot_tail = dot_product_nat_int(seq_reverse(c).skip(1), s.skip(1));
        assert(dot_product_nat_int(c_init, revs_init) == dot_tail);

        // dot(c_last, revs_last) = c[n-1] * s[0]
        let first_term = (c[n - 1] as int) * s.first();
        assert(c_last.first() == c[n - 1]);
        assert(revs_last.first() == s.first());
        assert(c_last.skip(1) =~= Seq::<nat>::empty());
        assert(revs_last.skip(1) =~= Seq::<int>::empty());
        assert(dot_product_nat_int(Seq::<nat>::empty(), Seq::<int>::empty()) == 0int);
        assert(dot_product_nat_int(c_last, revs_last)
            == (c[n - 1] as int) * s.first() + 0int);
        assert(dot_product_nat_int(c_last, revs_last) == first_term);

        // dot(c, rev(s)) = dot_tail + first_term
        assert(dot_product_nat_int(c, seq_reverse(s)) == dot_tail + first_term);

        // dot(rev(c), s) = rev(c)[0]*s[0] + dot(rev(c).skip(1), s.skip(1))
        //                = c[n-1]*s[0] + dot_tail = first_term + dot_tail
        assert(seq_reverse(c).first() == c[n - 1]);
        assert(dot_product_nat_int(seq_reverse(c), s) == first_term + dot_tail);
    }
}

/// Row-major strides have the same length as the shape.
proof fn lemma_row_major_strides_len(shape: Seq<nat>)
    ensures row_major_strides(shape).len() == shape.len(),
{
    lemma_column_major_strides_len(seq_reverse(shape));
}

/// A row-major layout is valid.
pub proof fn lemma_row_major_valid(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_row_major(shape).valid(),
{
    lemma_row_major_strides_len(shape);
}

/// For a row-major layout, the dot product with coordinates equals
/// linearize of the reversed coordinates in the reversed shape.
proof fn lemma_row_major_dot_is_linearize_rev(coords: Seq<nat>, shape: Seq<nat>)
    requires
        coords.len() == shape.len(),
        shape_valid(shape),
    ensures
        dot_product_nat_int(coords, row_major_strides(shape))
            == linearize(seq_reverse(coords), seq_reverse(shape)),
{
    // row_major_strides(shape) = rev(cm_strides(rev(shape)))
    // dot(coords, rev(cm_strides(rev(shape)))) = dot(rev(coords), cm_strides(rev(shape)))
    lemma_column_major_strides_len(seq_reverse(shape));
    lemma_dot_product_reverse(coords, column_major_strides(seq_reverse(shape)));

    // dot(rev(coords), cm_strides(rev(shape))) = linearize(rev(coords), rev(shape))
    lemma_shape_valid_reverse(shape);
    lemma_column_major_dot_is_linearize(seq_reverse(coords), seq_reverse(shape));
}

/// A row-major layout is injective for any valid shape.
pub proof fn lemma_row_major_injective(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_row_major(shape).is_injective(),
{
    let layout = make_row_major(shape);
    lemma_row_major_valid(shape);

    assert forall|i: nat, j: nat|
        i < layout.size() && j < layout.size() && i != j
    implies
        #[trigger] layout.offset(i) != #[trigger] layout.offset(j)
    by {
        let ci = delinearize(i, shape);
        let cj = delinearize(j, shape);
        lemma_delinearize_len(i, shape);
        lemma_delinearize_len(j, shape);
        lemma_delinearize_bounds(i, shape);
        lemma_delinearize_bounds(j, shape);

        // offset(x) = linearize(rev(delin(x, s)), rev(s))
        lemma_row_major_dot_is_linearize_rev(ci, shape);
        lemma_row_major_dot_is_linearize_rev(cj, shape);

        if layout.offset(i) == layout.offset(j) {
            // linearize(rev(ci), rev(s)) == linearize(rev(cj), rev(s))
            lemma_coords_in_bounds_reverse(ci, shape);
            lemma_coords_in_bounds_reverse(cj, shape);
            lemma_shape_valid_reverse(shape);

            // By roundtrip: delinearize(linearize(rev(c), rev(s)), rev(s)) =~= rev(c)
            lemma_linearize_roundtrip(seq_reverse(ci), seq_reverse(shape));
            lemma_linearize_roundtrip(seq_reverse(cj), seq_reverse(shape));
            // Since linearize values are equal, the delinearize results are equal:
            // rev(ci) =~= rev(cj)

            // By involution: ci =~= cj
            lemma_seq_reverse_involution(ci);
            lemma_seq_reverse_involution(cj);

            // But then i == linearize(ci, s) == linearize(cj, s) == j
            lemma_delinearize_roundtrip(i, shape);
            lemma_delinearize_roundtrip(j, shape);
            assert(false);
        }
    }
}

/// shape_size is preserved under reversal.
pub proof fn lemma_shape_size_reverse(shape: Seq<nat>)
    ensures shape_size(seq_reverse(shape)) == shape_size(shape),
    decreases shape.len(),
{
    if shape.len() > 0 {
        let rev = seq_reverse(shape);
        let n = shape.len();

        // rev.first() == shape[n-1], rev.skip(1) == rev(shape.take(n-1))
        assert(rev.first() == shape[n - 1]);

        // rev.skip(1) =~= rev(shape.take(n-1))
        let init = shape.take(n - 1);
        let rev_init = seq_reverse(init);
        assert(rev.skip(1) =~= rev_init) by {
            assert(rev.skip(1).len() == rev_init.len());
            assert forall|i: int| 0 <= i < rev_init.len()
            implies #[trigger] rev.skip(1)[i] == rev_init[i]
            by {
                assert(rev.skip(1)[i] == rev[i + 1]);
                assert(rev[i + 1] == shape[n - 1 - (i + 1)]);
                assert(rev_init[i] == init[init.len() - 1 - i]);
                assert(init[init.len() - 1 - i] == shape[n - 2 - i]);
            }
        };

        // shape = init ++ [shape[n-1]]
        // shape_size(shape) = shape_size(init) * shape[n-1]
        // We need: shape_size(init ++ [last]) = shape_size(init) * last
        // By induction on shape definition:
        // shape_size(shape) = shape.first() * shape_size(shape.skip(1))
        //                   = shape[0] * shape_size(shape.skip(1))
        // But we want to relate to init. Let's use a different approach:
        // shape_size(rev) = rev.first() * shape_size(rev.skip(1))
        //                 = shape[n-1] * shape_size(rev_init)
        // By IH: shape_size(rev_init) = shape_size(init)
        // So shape_size(rev) = shape[n-1] * shape_size(init)

        lemma_shape_size_reverse(init);
        // shape_size(rev) = shape[n-1] * shape_size(init)
        // shape_size(shape) = shape[0] * shape_size(shape.skip(1))

        // Need: shape[n-1] * shape_size(init) == shape[0] * shape_size(shape.skip(1))
        // shape.skip(1) has elements shape[1], ..., shape[n-1]
        // init has elements shape[0], ..., shape[n-2]
        // These are different sequences. We need commutativity of product.
        // Actually let's just use a simpler induction structure.
        // shape_size(shape) = shape.first() * shape_size(shape.skip(1))
        // shape_size(rev) = rev.first() * shape_size(rev.skip(1))
        //                 = shape[n-1] * shape_size(rev_init)
        // IH gives shape_size(rev_init) == shape_size(init)
        // We need shape[n-1] * shape_size(init) == shape[0] * shape_size(skip(1))
        // This is NOT trivially true unless we use full product commutativity.

        // Better approach: use lemma_shape_size_append.
        // shape = init.push(shape[n-1]) = init ++ seq![shape[n-1]]
        assert(shape =~= init.add(seq![shape[n - 1]]));
        lemma_shape_size_append(init, seq![shape[n - 1]]);

        // shape_size(seq![shape[n-1]]) unfolds to shape[n-1] * shape_size(empty) = shape[n-1]
        let last_seq = seq![shape[n - 1] as nat];
        assert(last_seq.len() == 1);
        assert(last_seq.first() == shape[n - 1]);
        assert(last_seq.skip(1) =~= Seq::<nat>::empty());
        assert(shape_size(last_seq) == last_seq.first() * shape_size(last_seq.skip(1)));
        assert(shape_size(last_seq.skip(1)) == 1nat);
        assert(shape_size(last_seq) == shape[n - 1] * 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(shape[n - 1] as int);

        // shape_size(shape) == shape_size(init) * shape[n-1]
        assert(shape_size(shape) == shape_size(init) * shape[n - 1]);

        // shape_size(rev) = rev.first() * shape_size(rev.skip(1))
        //                 = shape[n-1] * shape_size(rev_init)
        //                 = shape[n-1] * shape_size(init)  [by IH]
        assert(shape_size(seq_reverse(shape)) == shape[n - 1] * shape_size(init));

        vstd::arithmetic::mul::lemma_mul_is_commutative(
            shape[n - 1] as int,
            shape_size(init) as int,
        );
    }
}

/// For a row-major layout, offset acts as "linearize in reversed coordinates".
/// Given k < size, the index linearize(rev(delinearize(k, rev(shape))), shape)
/// maps to offset k.
proof fn lemma_row_major_surjective_witness(shape: Seq<nat>, k: nat)
    requires
        shape_valid(shape),
        k < shape_size(shape),
    ensures ({
        let rev_shape = seq_reverse(shape);
        let rev_coords = delinearize(k, rev_shape);
        let coords = seq_reverse(rev_coords);
        let idx = linearize(coords, shape);
        &&& idx < shape_size(shape)
        &&& make_row_major(shape).offset(idx) == k as int
    }),
{
    let rev_shape = seq_reverse(shape);
    lemma_shape_valid_reverse(shape);
    lemma_shape_size_reverse(shape);
    // k < shape_size(rev_shape)

    let rev_coords = delinearize(k, rev_shape);
    lemma_delinearize_len(k, rev_shape);
    lemma_delinearize_bounds(k, rev_shape);

    let coords = seq_reverse(rev_coords);
    // coords_in_bounds(coords, shape) from coords_in_bounds(rev_coords, rev_shape)
    lemma_coords_in_bounds_reverse_back(rev_coords, shape);

    let idx = linearize(coords, shape);
    lemma_linearize_bound(coords, shape);

    // offset(idx) = linearize(rev(delinearize(idx, shape)), rev(shape))
    lemma_delinearize_len(idx, shape);
    lemma_delinearize_bounds(idx, shape);
    lemma_row_major_dot_is_linearize_rev(delinearize(idx, shape), shape);

    // linearize_roundtrip: delinearize(linearize(coords, shape), shape) =~= coords
    lemma_linearize_roundtrip(coords, shape);
    // So delinearize(idx, shape) =~= coords = rev(rev_coords)

    // offset(idx) = linearize(rev(rev(rev_coords)), rev(shape))
    //             = linearize(rev_coords, rev(shape))  [by involution]
    lemma_seq_reverse_involution(rev_coords);

    // = k  [by delinearize_roundtrip on k and rev_shape]
    lemma_delinearize_roundtrip(k, rev_shape);
}

/// Helper: if coords_in_bounds(coords, rev(shape)), then coords_in_bounds(rev(coords), shape).
proof fn lemma_coords_in_bounds_reverse_back(coords: Seq<nat>, shape: Seq<nat>)
    requires
        coords.len() == shape.len(),
        coords_in_bounds(coords, seq_reverse(shape)),
    ensures
        coords_in_bounds(seq_reverse(coords), shape),
{
    let rev_coords = seq_reverse(coords);
    let n = shape.len();
    assert forall|i: int| 0 <= i < n
    implies #[trigger] rev_coords[i] < shape[i]
    by {
        // rev_coords[i] = coords[n-1-i]
        // shape[i] corresponds to rev(shape)[n-1-i]
        // coords[n-1-i] < rev(shape)[n-1-i] = shape[i]
        let j = (n - 1 - i) as int;
        assert(coords[j] < seq_reverse(shape)[j]);
        assert(seq_reverse(shape)[j] == shape[n - 1 - j]);
        assert((n - 1 - j) as int == i);
    }
}

/// A row-major layout is bijective onto [0, size).
pub proof fn lemma_row_major_bijective(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_row_major(shape).is_bijective_upto(shape_size(shape)),
{
    let layout = make_row_major(shape);
    lemma_row_major_injective(shape);

    assert forall|k: int| 0 <= k < shape_size(shape) as int
    implies #[trigger] layout.offset_hit(k) by {
        lemma_row_major_surjective_witness(shape, k as nat);
        let rev_shape = seq_reverse(shape);
        let rev_coords = delinearize(k as nat, rev_shape);
        let coords = seq_reverse(rev_coords);
        let idx = linearize(coords, shape);
        assert(layout.offset(idx) == k);
    }
}

} // verus!
