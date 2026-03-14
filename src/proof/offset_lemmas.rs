use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::proof::integer_helpers::*;
use crate::proof::shape_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Dot product lemmas
// ══════════════════════════════════════════════════════════════

/// Dot product of zero coordinates with any strides is 0.
pub proof fn lemma_dot_product_empty(strides: Seq<int>)
    ensures dot_product_nat_int(Seq::<nat>::empty(), strides) == 0,
{
}

/// Dot product with non-negative strides and non-negative coords is non-negative.
pub proof fn lemma_dot_product_nonneg(coords: Seq<nat>, strides: Seq<int>)
    requires
        coords.len() == strides.len(),
        forall|i: int| 0 <= i < strides.len() ==> #[trigger] strides[i] >= 0,
    ensures
        dot_product_nat_int(coords, strides) >= 0,
    decreases coords.len(),
{
    if coords.len() > 0 {
        lemma_dot_product_nonneg(coords.skip(1), strides.skip(1));
        lemma_mul_nonneg(coords.first() as int, strides.first());
    }
}

/// Dot product upper bound: if coords[i] < shape[i] for all i, and strides are non-negative,
/// then dot(coords, strides) <= dot(shape - 1, strides) = sum((shape[i]-1) * strides[i]).
pub proof fn lemma_dot_product_upper_bound(
    coords: Seq<nat>, shape: Seq<nat>, strides: Seq<int>
)
    requires
        coords.len() == shape.len(),
        shape.len() == strides.len(),
        forall|i: int| 0 <= i < coords.len() ==> #[trigger] coords[i] < shape[i],
        forall|i: int| 0 <= i < strides.len() ==> #[trigger] strides[i] >= 0,
        forall|i: int| 0 <= i < shape.len() ==> #[trigger] shape[i] > 0,
    ensures
        dot_product_nat_int(coords, strides)
            <= dot_product_nat_int(shape_minus_one(shape), strides),
    decreases coords.len(),
{
    if coords.len() > 0 {
        // coords[0] <= shape[0] - 1, strides[0] >= 0
        // so coords[0] * strides[0] <= (shape[0] - 1) * strides[0]
        assert(coords.first() <= shape.first() - 1);
        lemma_mul_le_right(coords.first() as int, (shape.first() - 1) as int, strides.first());

        // IH on tails
        let rc = coords.skip(1);
        let rs = shape.skip(1);
        let rd = strides.skip(1);
        assert forall|i: int| 0 <= i < rc.len() implies #[trigger] rc[i] < rs[i]
        by { assert(rc[i] == coords[i + 1]); assert(rs[i] == shape[i + 1]); };
        assert forall|i: int| 0 <= i < rd.len() implies #[trigger] rd[i] >= 0
        by { assert(rd[i] == strides[i + 1]); };
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] > 0
        by { assert(rs[i] == shape[i + 1]); };

        lemma_dot_product_upper_bound(rc, rs, rd);

        // shape_minus_one distributes over first/skip
        assert(shape_minus_one(shape).first() == shape.first() - 1);
        assert(shape_minus_one(shape).skip(1) =~= shape_minus_one(rs));
    }
}

/// Dot product of all-zero coordinates is 0.
pub proof fn lemma_dot_product_zeros(n: nat, strides: Seq<int>)
    requires strides.len() == n,
    ensures dot_product_nat_int(zeros(n), strides) == 0,
    decreases n,
{
    if n > 0 {
        assert(zeros(n).first() == 0);
        assert(zeros(n).skip(1) =~= zeros((n - 1) as nat));
        lemma_dot_product_zeros((n - 1) as nat, strides.skip(1));
    }
}

// ══════════════════════════════════════════════════════════════
// Offset lemmas
// ══════════════════════════════════════════════════════════════

/// Offset is non-negative for layouts with non-negative strides.
pub proof fn lemma_offset_nonneg(layout: LayoutSpec, idx: nat)
    requires
        layout.valid(),
        layout.non_negative_strides(),
        idx < layout.size(),
    ensures
        layout.offset(idx) >= 0,
{
    lemma_delinearize_len(idx, layout.shape);
    lemma_dot_product_nonneg(delinearize(idx, layout.shape), layout.stride);
}

/// Offset of index 0 is 0 for non-negative strides.
pub proof fn lemma_offset_zero(layout: LayoutSpec, )
    requires
        layout.valid(),
    ensures
        layout.offset(0) == 0,
{
    // delinearize(0, shape) = (0, 0, ..., 0)
    lemma_delinearize_all_zeros(0, layout.shape);
    lemma_dot_product_zeros(layout.shape.len(), layout.stride);
}

/// Offset is strictly less than cosize for non-negative strides.
pub proof fn lemma_offset_upper_bound(layout: LayoutSpec, idx: nat)
    requires
        layout.valid(),
        layout.non_negative_strides(),
        idx < layout.size(),
    ensures
        layout.offset(idx) < layout.cosize_nonneg() as int,
{
    let coords = delinearize(idx, layout.shape);
    lemma_delinearize_bounds(idx, layout.shape);
    lemma_delinearize_len(idx, layout.shape);

    // offset(idx) = dot(coords, strides) <= dot(shape-1, strides) = cosize - 1
    lemma_dot_product_upper_bound(coords, layout.shape, layout.stride);
    lemma_cosize_equals_dot_plus_one(layout);
}

// ══════════════════════════════════════════════════════════════
// Helper: cosize = dot(shape-1, strides) + 1
// ══════════════════════════════════════════════════════════════

/// cosize_nonneg equals dot_product(shape - 1, strides) + 1.
pub proof fn lemma_cosize_equals_dot_plus_one(layout: LayoutSpec)
    requires
        layout.valid(),
        layout.non_negative_strides(),
    ensures
        layout.cosize_nonneg() as int
            == dot_product_nat_int(shape_minus_one(layout.shape), layout.stride) + 1,
    decreases layout.shape.len(),
{
    if layout.shape.len() == 0 {
        // cosize = 1, dot = 0
    } else {
        let rest = LayoutSpec { shape: layout.shape.skip(1), stride: layout.stride.skip(1) };
        assert forall|i: int| 0 <= i < rest.stride.len() implies #[trigger] rest.stride[i] >= 0
        by { assert(rest.stride[i] == layout.stride[i + 1]); };

        lemma_cosize_equals_dot_plus_one(rest);

        // cosize(layout) = (shape[0]-1)*stride[0] + cosize(rest)
        //                 = (shape[0]-1)*stride[0] + dot(shape_rest - 1, stride_rest) + 1
        // dot(shape-1, strides) = (shape[0]-1)*stride[0] + dot(shape_rest-1, stride_rest)
        // So cosize = dot(shape-1, strides) + 1  ✓

        assert(shape_minus_one(layout.shape).first() == layout.shape.first() - 1);
        assert(shape_minus_one(layout.shape).skip(1) =~= shape_minus_one(layout.shape.skip(1)));
    }
}

// ══════════════════════════════════════════════════════════════
// Helper: delinearize(0, shape) == (0, 0, ..., 0)
// ══════════════════════════════════════════════════════════════

/// Delinearizing 0 gives all-zero coordinates.
proof fn lemma_delinearize_all_zeros(idx: nat, shape: Seq<nat>)
    requires shape_valid(shape), idx == 0,
    ensures delinearize(0, shape) =~= zeros(shape.len()),
    decreases shape.len(),
{
    if shape.len() > 0 {
        assert(0nat % shape.first() == 0);
        assert(0nat / shape.first() == 0);
        lemma_delinearize_all_zeros(0, shape.skip(1));
        assert(zeros(shape.len()).first() == 0);
        assert(zeros(shape.len()).skip(1) =~= zeros(shape.skip(1).len()));
    }
}

// ══════════════════════════════════════════════════════════════
// Rank-2 offset via linearize
// ══════════════════════════════════════════════════════════════

/// For a rank-2 layout, `offset(linearize(seq![i, k], shape))` equals
/// the arithmetic formula `i * stride[0] + k * stride[1]`.
///
/// This is the canonical bridge between the generic `LayoutSpec::offset`
/// definition (which goes through delinearize/dot_product) and the direct
/// arithmetic that runtime code and GEMM specs need.
pub proof fn lemma_rank2_offset_linearize(layout: &LayoutSpec, i: nat, k: nat)
    requires
        layout.valid(),
        layout.shape.len() == 2,
        i < layout.shape[0],
        k < layout.shape[1],
    ensures
        layout.offset(linearize(seq![i, k], layout.shape))
            == (i as int) * layout.stride[0] + (k as int) * layout.stride[1],
{
    let shape = layout.shape;
    let coords = seq![i, k];

    // Show coords_in_bounds(coords, shape)
    assert(coords.len() == shape.len());
    assert forall|j: int| 0 <= j < coords.len() implies #[trigger] coords[j] < shape[j]
    by {
        if j == 0 { assert(coords[0] == i); assert(shape[0] == layout.shape[0]); }
        else { assert(coords[1] == k); assert(shape[1] == layout.shape[1]); }
    };

    // linearize produces in-bounds index
    lemma_linearize_bound(coords, shape);
    let x = linearize(coords, shape);

    // delinearize(linearize(coords, shape), shape) =~= coords
    lemma_linearize_roundtrip(coords, shape);

    // offset(x) = dot(delinearize(x, shape), stride)
    // and delinearize(x, shape) =~= seq![i, k]
    let dcoords = delinearize(x, shape);
    assert(dcoords =~= coords);

    // Unfold dot product for 2 elements
    lemma_delinearize_len(x, shape);
    assert(dcoords.len() == 2);
    let skip1_c = dcoords.skip(1);
    let skip1_s = layout.stride.skip(1);
    assert(skip1_c.len() == 1);
    assert(skip1_c.first() == dcoords[1]);
    assert(skip1_s.first() == layout.stride[1]);
    assert(skip1_c.skip(1) =~= Seq::<nat>::empty());
    assert(skip1_s.skip(1) =~= Seq::<int>::empty());
    assert(dot_product_nat_int(Seq::<nat>::empty(), Seq::<int>::empty()) == 0int);
    assert(dot_product_nat_int(skip1_c, skip1_s) == (dcoords[1] as int) * layout.stride[1]);
    assert(dot_product_nat_int(dcoords, layout.stride) ==
        (dcoords[0] as int) * layout.stride[0] + dot_product_nat_int(skip1_c, skip1_s));

    // Since dcoords =~= seq![i, k]:
    assert(dcoords[0] == i);
    assert(dcoords[1] == k);
}

} // verus!
