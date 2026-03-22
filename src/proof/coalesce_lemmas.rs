use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::coalesce::*;
use crate::runtime::inverse::is_fully_coalesced;
use crate::proof::shape_lemmas::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Helpers
// ══════════════════════════════════════════════════════════════

/// Core algebraic identity: if d1 == M0 * d0, then c0*d0 + c1*d1 == (c0 + M0*c1)*d0.
proof fn lemma_coalesce_dot_contribution(c0: nat, c1: nat, m0: nat, d0: int, d1: int)
    requires d1 == (m0 as int) * d0,
    ensures (c0 as int) * d0 + (c1 as int) * d1 == ((c0 + m0 * c1) as int) * d0,
{
    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(d0, c0 as int, (m0 * c1) as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(c1 as int, m0 as int, d0);
    vstd::arithmetic::mul::lemma_mul_is_commutative(c1 as int, m0 as int);
}

/// Unfold delinearize one step: the second element is (idx / shape[0]) % shape[1].
proof fn lemma_delinearize_second(idx: nat, shape: Seq<nat>)
    requires shape_valid(shape), shape.len() >= 2,
    ensures
        delinearize(idx, shape).len() >= 2,
        delinearize(idx, shape)[1] == (idx / shape[0]) % shape[1],
{
    lemma_delinearize_len(idx, shape);
    // delinearize(idx, shape) = seq![idx % shape[0]] ++ delinearize(idx/shape[0], shape.skip(1))
    // Element [1] = delinearize(idx/shape[0], shape.skip(1))[0]
    //             = (idx/shape[0]) % shape.skip(1).first()
    //             = (idx/shape[0]) % shape[1]
    let rest = delinearize(idx / shape[0], shape.skip(1));
    assert(delinearize(idx, shape)[1] == rest[0]);
    assert(rest[0] == (idx / shape[0]) % shape.skip(1).first());
    assert(shape.skip(1).first() == shape[1]);
}

/// Unfold delinearize: skip(1).skip(1) of a delinearize equals delinearize two levels deep.
proof fn lemma_delinearize_skip2(idx: nat, shape: Seq<nat>)
    requires shape_valid(shape), shape.len() >= 2,
    ensures
        delinearize(idx, shape).skip(1).skip(1)
            =~= delinearize((idx / shape[0]) / shape[1], shape.skip(1).skip(1)),
{
    // delinearize(idx, shape).skip(1) = delinearize(idx/shape[0], shape.skip(1))
    let rest1 = delinearize(idx / shape[0], shape.skip(1));
    assert(delinearize(idx, shape).skip(1) =~= rest1);

    // rest1.skip(1) = delinearize((idx/shape[0])/shape[1], shape.skip(1).skip(1))
    let shape1 = shape.skip(1);
    assert(shape1.first() == shape[1]);
    assert(rest1.skip(1) =~= delinearize((idx / shape[0]) / shape1.first(), shape1.skip(1)));
    assert(shape1.skip(1) =~= shape.skip(1).skip(1));
}

// ══════════════════════════════════════════════════════════════
// Size preservation
// ══════════════════════════════════════════════════════════════

/// Coalescing at position 0 preserves size.
pub proof fn lemma_coalesce_pair_size(layout: LayoutSpec)
    requires
        layout.valid(),
        layout.shape.len() >= 2,
        modes_coalesceable(&layout, 0),
    ensures
        coalesce_pair(layout, 0).size() == layout.size(),
{
    let s = layout.shape;
    let cp = coalesce_pair(layout, 0);
    assert(cp.shape.first() == s[0] * s[1]);
    assert(cp.shape.skip(1) =~= s.skip(2));
    assert(s.skip(1).skip(1) =~= s.skip(2));

    // size(s) = s[0] * s[1] * size(s[2..])
    // size(cp) = (s[0]*s[1]) * size(s[2..])
    assert(shape_size(s) == s[0] * shape_size(s.skip(1)));
    assert(shape_size(s.skip(1)) == s[1] * shape_size(s.skip(2)));
    vstd::arithmetic::mul::lemma_mul_is_associative(s[0] as int, s[1] as int, shape_size(s.skip(2)) as int);
}

// ══════════════════════════════════════════════════════════════
// Offset preservation
// ══════════════════════════════════════════════════════════════

/// Coalescing at position 0 preserves the offset function.
pub proof fn lemma_coalesce_pair_offset(layout: LayoutSpec, idx: nat)
    requires
        layout.valid(),
        layout.shape.len() >= 2,
        modes_coalesceable(&layout, 0),
        idx < layout.size(),
    ensures
        coalesce_pair(layout, 0).valid(),
        coalesce_pair(layout, 0).offset(idx) == layout.offset(idx),
{
    let s = layout.shape;
    let d = layout.stride;
    let m0 = s[0];
    let m1 = s[1];
    let d0 = d[0];
    let d1 = d[1];
    let cp = coalesce_pair(layout, 0);

    // ── Show cp is valid ──
    assert(cp.shape.len() == cp.stride.len());
    lemma_mul_pos(m0, m1);
    assert forall|i: int| 0 <= i < cp.shape.len() implies #[trigger] cp.shape[i] > 0
    by {
        if i == 0 { assert(cp.shape[0] == m0 * m1); }
        else { assert(cp.shape[i] == s[i + 1]); }
    };

    // ── Size equality ──
    lemma_coalesce_pair_size(layout);

    // ── Original coords ──
    let coords = delinearize(idx, s);
    lemma_delinearize_bounds(idx, s);
    let c0 = coords[0];
    let c1 = coords[1];

    // Unfold: c0 = idx % m0
    assert(c0 == idx % m0);

    // Unfold: c1 = (idx / m0) % m1
    lemma_delinearize_second(idx, s);
    assert(c1 == (idx / m0) % m1);

    // ── Coalesced coords ──
    let cp_coords = delinearize(idx, cp.shape);
    lemma_delinearize_bounds(idx, cp.shape);
    assert(cp_coords[0] == idx % (m0 * m1));

    // ── Mixed-radix identity: idx%(m0*m1) == idx%m0 + m0*((idx/m0)%m1) ──
    vstd::arithmetic::div_mod::lemma_breakdown(idx as int, m0 as int, m1 as int);

    // So: c0 + m0*c1 == cp_coords[0]
    assert(c0 + m0 * c1 == cp_coords[0]) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, ((idx / m0) % m1) as int);
    };

    // ── Dot product contribution: c0*d0 + c1*d1 == cp_coords[0]*d0 ──
    lemma_coalesce_dot_contribution(c0, c1, m0, d0, d1);

    // ── Tail equality ──
    // idx/(m0*m1) == (idx/m0)/m1
    vstd::arithmetic::div_mod::lemma_div_denominator(idx as int, m0 as int, m1 as int);

    // delinearize(idx, s).skip(1).skip(1) == delinearize((idx/m0)/m1, s[2..])
    lemma_delinearize_skip2(idx, s);
    assert(s.skip(1).skip(1) =~= s.skip(2));

    // delinearize(idx, cp.shape).skip(1) == delinearize(idx/(m0*m1), s[2..])
    assert(cp.shape.skip(1) =~= s.skip(2));
    assert(cp.stride.skip(1) =~= d.skip(2));

    // The tail delinearizations are the same sequence
    let tail_shape = s.skip(2);
    let tail_idx_orig = (idx / m0) / m1;
    let tail_idx_coal = idx / (m0 * m1);
    assert(tail_idx_orig == tail_idx_coal);

    let tail_coords = delinearize(tail_idx_orig, tail_shape);
    let tail_strides = d.skip(2);

    // ── Chain the dot products ──
    // Original: dot(coords, d)
    //   = c0*d0 + dot(coords.skip(1), d.skip(1))
    //   = c0*d0 + c1*d1 + dot(coords.skip(1).skip(1), d.skip(1).skip(1))
    //   = c0*d0 + c1*d1 + dot(tail_coords, tail_strides)
    assert(d.skip(1).skip(1) =~= tail_strides);
    assert(coords.skip(1).skip(1) =~= tail_coords) by {
        lemma_delinearize_skip2(idx, s);
    };

    // Coalesced: dot(cp_coords, cp.stride)
    //   = cp_coords[0]*d0 + dot(cp_coords.skip(1), d[2..])
    //   = cp_coords[0]*d0 + dot(tail_coords, tail_strides)
    assert(cp_coords.skip(1) =~= delinearize(tail_idx_coal, tail_shape));
    assert(cp_coords.skip(1) =~= tail_coords);

    // ── Explicit arithmetic chain ──
    let tail_dot = dot_product_nat_int(tail_coords, tail_strides);

    // Original offset decomposition
    let coords_skip1 = coords.skip(1);
    let d_skip1 = d.skip(1);
    assert(layout.offset(idx) == dot_product_nat_int(coords, d));
    assert(dot_product_nat_int(coords, d)
        == (c0 as int) * d0 + dot_product_nat_int(coords_skip1, d_skip1));
    assert(dot_product_nat_int(coords_skip1, d_skip1)
        == (c1 as int) * d1 + dot_product_nat_int(coords_skip1.skip(1), d_skip1.skip(1)));
    assert(dot_product_nat_int(coords_skip1.skip(1), d_skip1.skip(1)) == tail_dot);

    // So: layout.offset(idx) == c0*d0 + c1*d1 + tail_dot
    assert(layout.offset(idx) == (c0 as int) * d0 + (c1 as int) * d1 + tail_dot);

    // Coalesced offset decomposition
    assert(cp.offset(idx) == dot_product_nat_int(cp_coords, cp.stride));
    assert(dot_product_nat_int(cp_coords, cp.stride)
        == (cp_coords[0] as int) * d0 + dot_product_nat_int(cp_coords.skip(1), cp.stride.skip(1)));
    assert(dot_product_nat_int(cp_coords.skip(1), cp.stride.skip(1)) == tail_dot);

    // So: cp.offset(idx) == cp_coords[0]*d0 + tail_dot
    assert(cp.offset(idx) == (cp_coords[0] as int) * d0 + tail_dot);

    // And: c0*d0 + c1*d1 == cp_coords[0]*d0 (from lemma_coalesce_dot_contribution)
    // Therefore: layout.offset(idx) == cp.offset(idx)
}

// ══════════════════════════════════════════════════════════════
// Generalized coalesce at arbitrary position
// ══════════════════════════════════════════════════════════════

/// Size is preserved when coalescing at any valid position.
pub proof fn lemma_coalesce_pair_size_general(layout: LayoutSpec, i: nat)
    requires
        layout.valid(),
        (i as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, i as int),
    ensures
        coalesce_pair(layout, i).size() == layout.size(),
{
    let s = layout.shape;
    let cp = coalesce_pair(layout, i);
    let ii = i as int;

    // cp.shape = s.take(i) ++ [s[i]*s[i+1]] ++ s.skip(i+2)
    // shape_size(cp.shape) = shape_size(s.take(i)) * (s[i]*s[i+1]) * shape_size(s.skip(i+2))
    // shape_size(s) = shape_size(s.take(i)) * s[i] * s[i+1] * shape_size(s.skip(i+2))
    // These are equal by associativity of multiplication.

    // Split original at i
    crate::runtime::shape_helpers::lemma_shape_size_split(s, i);
    // size(s) == size(take(i)) * size(skip(i))
    // skip(i) has at least 2 elements, so size(skip(i)) = s[i] * size(skip(i+1))
    // = s[i] * s[i+1] * size(skip(i+2))
    let tail = s.skip(ii);
    assert(tail.first() == s[ii]);
    assert(tail.skip(1).first() == s[ii + 1]);
    assert(tail.skip(1).skip(1) =~= s.skip(ii + 2));

    // Split coalesced at i
    crate::runtime::shape_helpers::lemma_take_shape_valid(s, i);
    assert(cp.shape.take(ii) =~= s.take(ii));

    let cp_tail = cp.shape.skip(ii);
    assert(cp_tail.first() == s[ii] * s[ii + 1]);
    assert(cp_tail.skip(1) =~= s.skip(ii + 2));

    // shape_valid(cp.shape) must be proved BEFORE calling lemma_shape_size_split
    lemma_mul_pos(s[ii], s[ii + 1]);
    assert(shape_valid(cp.shape)) by {
        assert forall|j: int| 0 <= j < cp.shape.len() implies #[trigger] cp.shape[j] > 0
        by {
            if j < ii { assert(cp.shape[j] == s[j]); }
            else if j == ii { assert(cp.shape[j] == s[ii] * s[ii + 1]); }
            else { assert(cp.shape[j] == s[j + 1]); }
        };
    };
    crate::runtime::shape_helpers::lemma_shape_size_split(cp.shape, i);

    // Explicitly unfold shape_size for original tail (two levels)
    assert(tail.len() >= 2);
    assert(shape_size(tail) == tail.first() * shape_size(tail.skip(1)));
    assert(tail.skip(1).len() >= 1);
    assert(shape_size(tail.skip(1)) == tail.skip(1).first() * shape_size(tail.skip(1).skip(1)));

    // Explicitly unfold shape_size for coalesced tail (one level)
    assert(cp_tail.len() >= 1);
    assert(shape_size(cp_tail) == cp_tail.first() * shape_size(cp_tail.skip(1)));

    // s[ii] * (s[ii+1] * X) == (s[ii]*s[ii+1]) * X where X = shape_size(s.skip(ii+2))
    vstd::arithmetic::mul::lemma_mul_is_associative(
        s[ii] as int, s[ii + 1] as int, shape_size(s.skip(ii + 2)) as int,
    );
}

/// Coalescing at any valid position preserves the offset function.
pub proof fn lemma_coalesce_pair_offset_general(layout: LayoutSpec, i: nat, idx: nat)
    requires
        layout.valid(),
        (i as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, i as int),
        idx < layout.size(),
    ensures
        coalesce_pair(layout, i).valid(),
        coalesce_pair(layout, i).offset(idx) == layout.offset(idx),
{
    let s = layout.shape;
    let d = layout.stride;
    let cp = coalesce_pair(layout, i);
    let ii = i as int;

    // ── cp is valid ──
    lemma_mul_pos(s[ii], s[ii + 1]);
    assert(cp.shape.len() == cp.stride.len());
    assert forall|j: int| 0 <= j < cp.shape.len() implies #[trigger] cp.shape[j] > 0
    by {
        if j < ii { assert(cp.shape[j] == s[j]); }
        else if j == ii { assert(cp.shape[j] == s[ii] * s[ii + 1]); }
        else { assert(cp.shape[j] == s[j + 1]); }
    };

    // ── Size equality ──
    lemma_coalesce_pair_size_general(layout, i);

    // ── Split dot products at position i ──
    // Split layout at position i: use delinearize_concat
    // shape = shape.take(i) ++ shape.skip(i)
    let head_shape = s.take(ii);
    let tail_shape = s.skip(ii);
    crate::runtime::shape_helpers::lemma_take_shape_valid(s, i);

    // shape_valid(tail_shape) from shape_valid(s)
    assert(shape_valid(tail_shape)) by {
        assert forall|j: int| 0 <= j < tail_shape.len()
        implies #[trigger] tail_shape[j] > 0 by {};
    };

    // s =~= head_shape ++ tail_shape
    assert(s =~= head_shape.add(tail_shape));

    crate::runtime::shape_helpers::lemma_shape_size_split(s, i);
    let head_size = shape_size(head_shape);
    let tail_size = shape_size(tail_shape);
    lemma_shape_size_positive(head_shape);
    lemma_shape_size_positive(tail_shape);

    // Split delinearize: delinearize(idx, s) =~=
    //   delinearize(idx % head_size, head_shape) ++ delinearize(idx / head_size, tail_shape)
    lemma_delinearize_concat(idx, head_shape, tail_shape);

    let idx_head = idx % head_size;
    let idx_tail = idx / head_size;
    let coords_head = delinearize(idx_head, head_shape);
    let coords_tail = delinearize(idx_tail, tail_shape);
    lemma_delinearize_len(idx_head, head_shape);
    lemma_delinearize_len(idx_tail, tail_shape);

    // Split strides
    let head_stride = d.take(ii);
    let tail_stride = d.skip(ii);
    assert(d =~= head_stride.add(tail_stride));

    // dot(coords, d) = dot(coords_head, head_stride) + dot(coords_tail, tail_stride)
    lemma_dot_product_append(coords_head, coords_tail, head_stride, tail_stride);
    lemma_dot_product_ext(
        delinearize(idx, s), coords_head.add(coords_tail),
        d, head_stride.add(tail_stride),
    );

    // ── Same split for coalesced layout ──
    let cp_head_shape = cp.shape.take(ii);
    let cp_tail_shape = cp.shape.skip(ii);
    assert(cp_head_shape =~= head_shape);

    // cp_tail has the coalesced modes
    assert(cp_tail_shape.first() == s[ii] * s[ii + 1]);
    assert(cp_tail_shape.skip(1) =~= s.skip(ii + 2));
    assert(cp.shape =~= head_shape.add(cp_tail_shape));

    // shape_valid(cp_tail_shape)
    assert(shape_valid(cp_tail_shape)) by {
        assert forall|j: int| 0 <= j < cp_tail_shape.len()
        implies #[trigger] cp_tail_shape[j] > 0 by {
            if j == 0 { assert(cp_tail_shape[0] == s[ii] * s[ii + 1]); }
            else { assert(cp_tail_shape[j] == s[ii + 1 + j]); }
        };
    };

    assert(shape_valid(cp.shape));
    crate::runtime::shape_helpers::lemma_shape_size_split(cp.shape, i);
    let cp_tail_size = shape_size(cp_tail_shape);

    // Explicitly unfold shape_size for both tails
    assert(tail_shape.len() >= 2);
    assert(shape_size(tail_shape) == tail_shape.first() * shape_size(tail_shape.skip(1)));
    assert(tail_shape.first() == s[ii]);
    assert(tail_shape.skip(1).len() >= 1);
    assert(shape_size(tail_shape.skip(1)) == tail_shape.skip(1).first() * shape_size(tail_shape.skip(1).skip(1)));
    assert(tail_shape.skip(1).first() == s[ii + 1]);
    assert(tail_shape.skip(1).skip(1) =~= s.skip(ii + 2));

    assert(cp_tail_shape.len() >= 1);
    assert(shape_size(cp_tail_shape) == cp_tail_shape.first() * shape_size(cp_tail_shape.skip(1)));
    assert(cp_tail_shape.first() == s[ii] * s[ii + 1]);
    assert(cp_tail_shape.skip(1) =~= s.skip(ii + 2));

    vstd::arithmetic::mul::lemma_mul_is_associative(
        s[ii] as int, s[ii + 1] as int, shape_size(s.skip(ii + 2)) as int,
    );
    assert(cp_tail_size == tail_size);

    // head_size is the same, so idx_head and idx_tail are the same for cp
    assert(shape_size(cp_head_shape) == head_size);
    lemma_shape_size_positive(cp_tail_shape);
    lemma_delinearize_concat(idx, head_shape, cp_tail_shape);

    let cp_coords_head = delinearize(idx_head, head_shape);
    let cp_coords_tail = delinearize(idx_tail, cp_tail_shape);
    lemma_delinearize_len(idx_head, head_shape);
    lemma_delinearize_len(idx_tail, cp_tail_shape);

    let cp_head_stride = cp.stride.take(ii);
    let cp_tail_stride = cp.stride.skip(ii);
    assert(cp_head_stride =~= head_stride);
    assert(cp.stride =~= head_stride.add(cp_tail_stride));

    lemma_dot_product_append(cp_coords_head, cp_coords_tail, cp_head_stride, cp_tail_stride);
    lemma_dot_product_ext(
        delinearize(idx, cp.shape), cp_coords_head.add(cp_coords_tail),
        cp.stride, cp_head_stride.add(cp_tail_stride),
    );

    // ── Tail offset equality via position-0 lemma ──
    let tail_layout = LayoutSpec { shape: tail_shape, stride: tail_stride };
    assert(tail_layout.valid());
    assert(tail_layout.shape.len() >= 2);
    assert(modes_coalesceable(&tail_layout, 0)) by {
        assert(tail_layout.stride[1] == d[ii + 1]);
        assert(tail_layout.stride[0] == d[ii]);
        assert(tail_layout.shape[0] == s[ii]);
    };

    lemma_div_upper_bound(idx, head_size, tail_size);
    lemma_coalesce_pair_offset(tail_layout, idx_tail);

    let coalesced_tail = coalesce_pair(tail_layout, 0);
    assert(coalesced_tail.shape =~= cp_tail_shape);
    assert(coalesced_tail.stride =~= cp_tail_stride);

    // Chain: coalesced_tail.offset == tail_layout.offset == dot(coords_tail, tail_stride)
    // And coalesced_tail.offset == dot(cp_coords_tail, cp_tail_stride) via =~=
    lemma_delinearize_len(idx_tail, coalesced_tail.shape);
    lemma_dot_product_ext(
        delinearize(idx_tail, coalesced_tail.shape), cp_coords_tail,
        coalesced_tail.stride, cp_tail_stride,
    );
    let tail_dot = dot_product_nat_int(coords_tail, tail_stride);
    let cp_tail_dot = dot_product_nat_int(cp_coords_tail, cp_tail_stride);
    assert(cp_tail_dot == tail_dot);
}

// ══════════════════════════════════════════════════════════════
// Coalesce chain correctness
// ══════════════════════════════════════════════════════════════

/// coalesce_pass preserves validity, size, and offset.
pub proof fn lemma_coalesce_pass(layout: LayoutSpec, start: nat, idx: nat)
    requires
        layout.valid(),
        idx < layout.size(),
    ensures
        coalesce_pass(layout, start).valid(),
        coalesce_pass(layout, start).size() == layout.size(),
        coalesce_pass(layout, start).offset(idx) == layout.offset(idx),
    decreases layout.shape.len() as int - start as int,
{
    if start as int >= layout.shape.len() as int - 1 {
        // Base case: returns layout unchanged
    } else if modes_coalesceable(&layout, start as int) {
        // Coalesce pair at position start
        let cp = coalesce_pair(layout, start);
        lemma_coalesce_pair_offset_general(layout, start, idx);
        lemma_coalesce_pair_size_general(layout, start);
        // cp.valid(), cp.size() == layout.size(), cp.offset(idx) == layout.offset(idx)
        // Recurse on coalesced layout (length decreased by 1)
        lemma_coalesce_pass(cp, start, idx);
    } else {
        // Skip this position, advance
        lemma_coalesce_pass(layout, start + 1, idx);
    }
}

/// Full coalesce preserves validity, size, and offset.
pub proof fn lemma_coalesce(layout: LayoutSpec, idx: nat)
    requires
        layout.valid(),
        idx < layout.size(),
    ensures
        coalesce(layout).valid(),
        coalesce(layout).size() == layout.size(),
        coalesce(layout).offset(idx) == layout.offset(idx),
{
    lemma_coalesce_pass(layout, 0, idx);
}

// ══════════════════════════════════════════════════════════════
// Remove unit modes
// ══════════════════════════════════════════════════════════════

/// Removing unit modes preserves the offset function.
/// If shape[i] == 1, coords[i] is always 0, so coords[i]*stride[i] == 0.
pub proof fn lemma_remove_unit_mode_offset(layout: LayoutSpec, idx: nat, i: nat)
    requires
        layout.valid(),
        idx < layout.size(),
        (i as int) < layout.shape.len() as int,
        layout.shape[i as int] == 1,
    ensures ({
        // Removing mode i gives a layout with same offset
        let removed = LayoutSpec {
            shape: layout.shape.take(i as int).add(layout.shape.skip(i as int + 1)),
            stride: layout.stride.take(i as int).add(layout.stride.skip(i as int + 1)),
        };
        removed.valid()
        && removed.size() == layout.size()
        && removed.offset(idx) == layout.offset(idx)
    }),
{
    let ii = i as int;
    let s = layout.shape;
    let d = layout.stride;
    let removed = LayoutSpec {
        shape: s.take(ii).add(s.skip(ii + 1)),
        stride: d.take(ii).add(d.skip(ii + 1)),
    };

    // ── removed is valid ──
    assert(removed.shape.len() == removed.stride.len());
    assert forall|j: int| 0 <= j < removed.shape.len() implies #[trigger] removed.shape[j] > 0
    by {
        if j < ii { assert(removed.shape[j] == s[j]); }
        else { assert(removed.shape[j] == s[j + 1]); }
    };

    // ── Size: shape[i]==1 doesn't contribute ──
    crate::runtime::shape_helpers::lemma_shape_size_split(s, i);
    crate::runtime::shape_helpers::lemma_shape_size_split(s, (i + 1) as nat);
    // size(s) = size(take(i)) * size(skip(i))
    // size(skip(i)) = s[i] * size(skip(i+1)) = 1 * size(skip(i+1)) = size(skip(i+1))
    assert(s.skip(ii).first() == 1nat);
    assert(s.skip(ii).skip(1) =~= s.skip(ii + 1));
    vstd::arithmetic::mul::lemma_mul_basics(shape_size(s.skip(ii + 1)) as int);

    // size(removed) = size(take(i)) * size(skip(i+1)) = size(s)
    crate::runtime::shape_helpers::lemma_take_shape_valid(s, i);
    assert(shape_valid(s.skip(ii + 1))) by {
        assert forall|j: int| 0 <= j < s.skip(ii + 1).len()
        implies #[trigger] s.skip(ii + 1)[j] > 0 by {};
    };
    crate::proof::product_lemmas::lemma_shape_size_append(s.take(ii), s.skip(ii + 1));

    // ── Offset: split dot product, mode i contributes 0 ──
    // Split at i: dot(coords, d) = dot(head, head_d) + coords[i]*d[i] + dot(tail, tail_d)
    let coords = delinearize(idx, s);
    lemma_delinearize_bounds(idx, s);
    lemma_delinearize_len(idx, s);

    // coords[i] == 0 (since shape[i] == 1 and 0 <= coords[i] < 1 means coords[i] == 0)
    assert(coords[ii] == 0nat);

    // Split original dot at i
    let coords_head = coords.take(ii);
    let d_head = d.take(ii);
    let coords_tail = coords.skip(ii);
    let d_tail = d.skip(ii);
    lemma_dot_product_append(coords_head, coords_tail, d_head, d_tail);
    lemma_dot_product_ext(coords, coords_head.add(coords_tail), d, d_head.add(d_tail));

    // dot(coords_tail, d_tail) = coords[i]*d[i] + dot(coords.skip(i+1), d.skip(i+1))
    //                          = 0*d[i] + dot(...)
    //                          = dot(coords.skip(i+1), d.skip(i+1))
    assert(coords_tail.first() == 0nat);
    let coords_tail_rest = coords_tail.skip(1);
    let d_tail_rest = d_tail.skip(1);
    assert(coords_tail_rest =~= coords.skip(ii + 1));
    assert(d_tail_rest =~= d.skip(ii + 1));

    // For removed layout: split delinearize using concat
    let rm_head_shape = s.take(ii);
    let rm_tail_shape = s.skip(ii + 1);
    assert(removed.shape =~= rm_head_shape.add(rm_tail_shape));
    assert(removed.stride =~= d.take(ii).add(d.skip(ii + 1)));

    lemma_shape_size_positive(rm_head_shape);
    lemma_shape_size_positive(rm_tail_shape);
    lemma_delinearize_concat(idx, rm_head_shape, rm_tail_shape);

    let rm_idx_head = idx % shape_size(rm_head_shape);
    let rm_idx_tail = idx / shape_size(rm_head_shape);

    // For original: split at i too
    let head_size = shape_size(s.take(ii));
    lemma_shape_size_positive(s.take(ii));
    lemma_shape_size_positive(s.skip(ii));
    lemma_delinearize_concat(idx, s.take(ii), s.skip(ii));

    let orig_idx_head = idx % head_size;
    let orig_idx_tail = idx / head_size;

    // head_size is the same for both
    assert(shape_size(rm_head_shape) == head_size);

    // ── Head coords ──
    // From concat: coords =~= delinearize(orig_idx_head, s.take(ii)) ++ delinearize(orig_idx_tail, s.skip(ii))
    lemma_delinearize_len(orig_idx_head, s.take(ii));
    let orig_hd = delinearize(orig_idx_head, s.take(ii));
    let orig_tl_full = delinearize(orig_idx_tail, s.skip(ii));
    assert(orig_hd.len() == s.take(ii).len());
    // s.take(ii) ++ s.skip(ii) =~= s (basic seq identity)
    assert(s.take(ii).add(s.skip(ii)) =~= s);
    // From concat lemma: delinearize(idx, s.take(ii) ++ s.skip(ii)) =~= orig_hd ++ orig_tl_full
    // And delinearize(idx, s.take(ii) ++ s.skip(ii)) == delinearize(idx, s) == coords
    assert(coords =~= orig_hd.add(orig_tl_full));
    // take(ii) of concat = first part when first part has length ii
    assert(coords_head =~= orig_hd);
    // rm_coords_head = delinearize(rm_idx_head, rm_head_shape) = orig_hd
    assert(rm_idx_head == orig_idx_head);
    let rm_coords_head = delinearize(rm_idx_head, rm_head_shape);
    assert(rm_coords_head =~= coords_head);

    // ── Tail coords ──
    lemma_div_upper_bound(idx, head_size, shape_size(s.skip(ii)));

    // From concat: coords.skip(ii) =~= delinearize(orig_idx_tail, s.skip(ii))
    let orig_tl = delinearize(orig_idx_tail, s.skip(ii));
    lemma_delinearize_len(orig_idx_tail, s.skip(ii));
    assert(coords.skip(ii) =~= orig_tl);

    // Unfold delinearize one level: s.skip(ii).first() == 1
    // orig_tl = seq![orig_idx_tail % 1] ++ delinearize(orig_idx_tail / 1, s.skip(ii+1))
    assert(s.skip(ii).first() == 1nat);
    assert(orig_idx_tail % 1 == 0nat);
    assert(orig_idx_tail / 1 == orig_idx_tail);
    assert(orig_tl.skip(1) =~= delinearize(orig_idx_tail / s.skip(ii).first(), s.skip(ii).skip(1)));
    assert(s.skip(ii).skip(1) =~= s.skip(ii + 1));

    // coords_tail_rest = coords.skip(ii).skip(1) =~= orig_tl.skip(1) =~= delinearize(orig_idx_tail, s.skip(ii+1))
    assert(coords_tail_rest =~= orig_tl.skip(1));

    // rm_coords_tail = delinearize(orig_idx_tail, s.skip(ii+1)) = orig_tl.skip(1)
    lemma_div_upper_bound(idx, head_size, shape_size(rm_tail_shape));
    let rm_coords_tail = delinearize(rm_idx_tail, rm_tail_shape);
    assert(rm_coords_tail =~= coords_tail_rest);

    // Split removed dot product
    lemma_dot_product_append(rm_coords_head, rm_coords_tail, d.take(ii), d.skip(ii + 1));
    lemma_dot_product_ext(
        delinearize(idx, removed.shape),
        rm_coords_head.add(rm_coords_tail),
        removed.stride,
        d.take(ii).add(d.skip(ii + 1)),
    );

    // dot(coords_tail, d_tail) = 0*d[i] + dot(rest) = dot(rest)
    assert(coords_tail.len() > 0);
    assert(d_tail.len() > 0);
    assert((0nat as int) * d_tail.first() == 0int);
    assert(dot_product_nat_int(coords_tail, d_tail)
        == dot_product_nat_int(coords_tail_rest, d_tail_rest));

    // Both sides equal dot(coords_head, d_head) + dot(coords_tail_rest, d_tail_rest)
    assert(removed.offset(idx) == layout.offset(idx));
}

// ══════════════════════════════════════════════════════════════
// Iterative unit mode removal chain
// ══════════════════════════════════════════════════════════════

/// remove_units_iter preserves validity, size, and offset.
pub proof fn lemma_remove_units_iter(layout: LayoutSpec, pos: nat, idx: nat)
    requires
        layout.valid(),
        idx < layout.size(),
        pos <= layout.shape.len(),
    ensures
        remove_units_iter(layout, pos).valid(),
        remove_units_iter(layout, pos).size() == layout.size(),
        remove_units_iter(layout, pos).offset(idx) == layout.offset(idx),
    decreases layout.shape.len() as int - pos as int,
{
    if pos as int >= layout.shape.len() as int {
        // Base: returns layout unchanged
    } else if layout.shape[pos as int] == 1 {
        // Remove unit mode at pos
        lemma_remove_unit_mode_offset(layout, idx, pos);
        let removed = LayoutSpec {
            shape: layout.shape.take(pos as int).add(layout.shape.skip(pos as int + 1)),
            stride: layout.stride.take(pos as int).add(layout.stride.skip(pos as int + 1)),
        };
        // removed.valid(), removed.size() == layout.size(), removed.offset(idx) == layout.offset(idx)
        assert(removed.shape.len() == layout.shape.len() - 1);
        // pos <= removed.shape.len() since pos < layout.shape.len()
        lemma_remove_units_iter(removed, pos, idx);
    } else {
        // Non-unit mode, advance
        lemma_remove_units_iter(layout, pos + 1, idx);
    }
}

/// Full iterative unit removal preserves validity, size, and offset.
pub proof fn lemma_remove_units(layout: LayoutSpec, idx: nat)
    requires
        layout.valid(),
        idx < layout.size(),
    ensures
        remove_units_iter(layout, 0).valid(),
        remove_units_iter(layout, 0).size() == layout.size(),
        remove_units_iter(layout, 0).offset(idx) == layout.offset(idx),
{
    lemma_remove_units_iter(layout, 0, idx);
}

/// Removing a unit mode preserves size fitting in u64.
pub proof fn lemma_remove_unit_mode_size_bound(layout: LayoutSpec, pos: nat)
    requires
        layout.valid(),
        (pos as int) < layout.shape.len() as int,
        layout.shape[pos as int] == 1,
        layout.size() <= u64::MAX as nat,
    ensures ({
        let removed = LayoutSpec {
            shape: layout.shape.take(pos as int).add(layout.shape.skip(pos as int + 1)),
            stride: layout.stride.take(pos as int).add(layout.stride.skip(pos as int + 1)),
        };
        removed.size() <= u64::MAX as nat
    }),
{
    lemma_shape_size_positive(layout.shape);
    lemma_remove_unit_mode_offset(layout, 0, pos);
}

/// Flatten preserves validity.
pub proof fn lemma_flatten_valid(layout: LayoutSpec)
    requires layout.valid(),
    ensures flatten(layout).valid(),
{
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce(layout, 0);
    lemma_remove_units(coalesce(layout), 0);
}

/// Flatten preserves size.
pub proof fn lemma_flatten_size(layout: LayoutSpec)
    requires layout.valid(),
    ensures flatten(layout).size() == layout.size(),
{
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce(layout, 0);
    lemma_remove_units(coalesce(layout), 0);
}

/// Flatten preserves offset for all valid indices.
pub proof fn lemma_flatten_offset(layout: LayoutSpec, idx: nat)
    requires layout.valid(), idx < layout.size(),
    ensures flatten(layout).offset(idx) == layout.offset(idx),
{
    lemma_coalesce(layout, idx);
    lemma_remove_units(coalesce(layout), idx);
}

// ══════════════════════════════════════════════════════════════
// Group modes lemmas
// ══════════════════════════════════════════════════════════════

/// After coalescing at position lo, mode lo is still coalesceable with the new lo+1
/// (the old lo+2). This follows from stride[lo+2] == s[lo+1]*s[lo]*d[lo] == (s[lo]*s[lo+1])*d[lo].
pub proof fn lemma_coalesce_pair_preserves_coalesceable(layout: LayoutSpec, lo: nat)
    requires
        layout.valid(),
        (lo as int) + 2 < layout.shape.len() as int,
        modes_coalesceable(&layout, lo as int),
        modes_coalesceable(&layout, lo as int + 1),
    ensures
        modes_coalesceable(&coalesce_pair(layout, lo), lo as int),
{
    let cp = coalesce_pair(layout, lo);
    let ii = lo as int;
    // cp.shape[lo] = layout.shape[lo] * layout.shape[lo+1]
    // cp.stride[lo] = layout.stride[lo]
    // cp.shape[lo+1] = layout.shape[lo+2] (shifted from skip(lo+2))
    // cp.stride[lo+1] = layout.stride[lo+2]
    assert(cp.shape[ii] == layout.shape[ii] * layout.shape[ii + 1]);
    assert(cp.stride[ii] == layout.stride[ii]);

    // From take(ii).add(seq![...]).add(skip(ii+2)):
    // cp.shape[ii+1] is skip(ii+2)[0] = layout.shape[ii+2]
    assert(cp.shape[ii + 1] == layout.shape[ii + 2]);
    assert(cp.stride[ii + 1] == layout.stride[ii + 2]);

    // Need: cp.stride[lo+1] == cp.shape[lo] * cp.stride[lo]
    // i.e., layout.stride[lo+2] == (layout.shape[lo] * layout.shape[lo+1]) * layout.stride[lo]
    // From coalesceable(lo): layout.stride[lo+1] == layout.shape[lo] * layout.stride[lo]
    // From coalesceable(lo+1): layout.stride[lo+2] == layout.shape[lo+1] * layout.stride[lo+1]
    //   == layout.shape[lo+1] * (layout.shape[lo] * layout.stride[lo])
    //   == (layout.shape[lo+1] * layout.shape[lo]) * layout.stride[lo]
    //   == (layout.shape[lo] * layout.shape[lo+1]) * layout.stride[lo]
    let s0 = layout.shape[ii] as int;
    let s1 = layout.shape[ii + 1] as int;
    let d0 = layout.stride[ii];
    let d1 = layout.stride[ii + 1];
    let d2 = layout.stride[ii + 2];

    assert(d1 == s0 * d0);
    assert(d2 == s1 * d1);
    // d2 == s1 * (s0 * d0) == (s1 * s0) * d0 == (s0 * s1) * d0
    vstd::arithmetic::mul::lemma_mul_is_associative(s1, s0, d0);
    vstd::arithmetic::mul::lemma_mul_is_commutative(s1, s0);
    assert(d2 == (s0 * s1) * d0);
    // (s0 * s1) as int == (layout.shape[lo] * layout.shape[lo+1]) as int
    assert((cp.shape[ii] as int) * cp.stride[ii] == (s0 * s1) * d0);
}

/// After coalescing at lo, higher coalesceable pairs are preserved.
/// Specifically, if modes_coalesceable(layout, j) for j > lo, then
/// modes_coalesceable(coalesce_pair(layout, lo), j-1) (shifted by 1).
proof fn lemma_coalesce_pair_preserves_higher(layout: LayoutSpec, lo: nat, j: int)
    requires
        layout.valid(),
        (lo as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, lo as int),
        j > lo as int + 1,
        j < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, j),
    ensures
        modes_coalesceable(&coalesce_pair(layout, lo), j - 1),
{
    let cp = coalesce_pair(layout, lo);
    let ii = lo as int;
    // For j > lo + 1: cp.shape[j-1] == layout.shape[j], cp.stride[j-1] == layout.stride[j]
    // cp.stride[j] == layout.stride[j+1]
    // modes_coalesceable(cp, j-1): cp.stride[j] == cp.shape[j-1] * cp.stride[j-1]
    assert(cp.shape[j - 1] == layout.shape[j]);
    assert(cp.stride[j - 1] == layout.stride[j]);
    assert(cp.stride[j] == layout.stride[j + 1]);
    // From layout: layout.stride[j+1] == layout.shape[j] * layout.stride[j]
}

/// Coalescing at lo preserves admissibility for [lo, hi-1) in the result.
pub proof fn lemma_group_modes_admissible_step(layout: LayoutSpec, lo: nat, hi: nat)
    requires
        group_modes_admissible(&layout, lo, hi),
        hi > lo + 1,
    ensures ({
        let cp = coalesce_pair(layout, lo);
        &&& cp.valid()
        &&& cp.size() == layout.size()
        &&& group_modes_admissible(&cp, lo, (hi - 1) as nat)
    }),
{
    let cp = coalesce_pair(layout, lo);
    let ii = lo as int;

    // cp.valid() and size preservation from existing lemmas
    lemma_coalesce_pair_size_general(layout, lo);
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce_pair_offset_general(layout, lo, 0);

    // cp.shape.len() == layout.shape.len() - 1
    assert(cp.shape.len() == layout.shape.len() - 1);

    // lo < hi - 1, hi - 1 <= cp.shape.len() == layout.shape.len() - 1
    assert(lo < (hi - 1) as nat);
    assert((hi - 1) as nat <= cp.shape.len());

    // Need: forall i in [lo, hi-2): modes_coalesceable(cp, i)
    assert forall|i: int| lo as int <= i < (hi - 1) as int - 1
        implies #[trigger] modes_coalesceable(&cp, i)
    by {
        if i == lo as int {
            // Need coalesceable(cp, lo): merged mode lo with old lo+2
            // From admissible: coalesceable(layout, lo) and coalesceable(layout, lo+1)
            assert(modes_coalesceable(&layout, lo as int));
            assert(modes_coalesceable(&layout, lo as int + 1));
            // lo + 2 < hi <= layout.shape.len(), so lo + 2 < layout.shape.len()
            lemma_coalesce_pair_preserves_coalesceable(layout, lo);
        } else {
            // i > lo, so cp mode i corresponds to layout mode i+1
            // Need modes_coalesceable(cp, i), which means cp.stride[i+1] == cp.shape[i] * cp.stride[i]
            // cp.shape[i] == layout.shape[i+1], cp.stride[i] == layout.stride[i+1]
            // cp.stride[i+1] == layout.stride[i+2]
            // This is modes_coalesceable(layout, i+1)
            assert(lo as int + 1 <= i + 1);
            assert(i + 1 < hi as int - 1);
            assert(modes_coalesceable(&layout, i + 1));
            lemma_coalesce_pair_preserves_higher(layout, lo, i + 1);
        }
    };
}

/// group_modes preserves validity.
pub proof fn lemma_group_modes_valid(layout: LayoutSpec, lo: nat, hi: nat)
    requires group_modes_admissible(&layout, lo, hi),
    ensures group_modes(layout, lo, hi).valid(),
    decreases hi - lo,
{
    if hi <= lo + 1 {
        // base case: group_modes returns layout unchanged
    } else {
        lemma_group_modes_admissible_step(layout, lo, hi);
        lemma_group_modes_valid(coalesce_pair(layout, lo), lo, (hi - 1) as nat);
    }
}

/// group_modes preserves size.
pub proof fn lemma_group_modes_size(layout: LayoutSpec, lo: nat, hi: nat)
    requires group_modes_admissible(&layout, lo, hi),
    ensures group_modes(layout, lo, hi).size() == layout.size(),
    decreases hi - lo,
{
    if hi <= lo + 1 {
    } else {
        lemma_group_modes_admissible_step(layout, lo, hi);
        let cp = coalesce_pair(layout, lo);
        lemma_group_modes_size(cp, lo, (hi - 1) as nat);
    }
}

/// group_modes preserves offset.
pub proof fn lemma_group_modes_offset(layout: LayoutSpec, lo: nat, hi: nat, idx: nat)
    requires group_modes_admissible(&layout, lo, hi), idx < layout.size(),
    ensures group_modes(layout, lo, hi).offset(idx) == layout.offset(idx),
    decreases hi - lo,
{
    if hi <= lo + 1 {
    } else {
        lemma_group_modes_admissible_step(layout, lo, hi);
        let cp = coalesce_pair(layout, lo);
        lemma_coalesce_pair_offset_general(layout, lo, idx);
        lemma_group_modes_offset(cp, lo, (hi - 1) as nat, idx);
    }
}

/// group_modes decreases rank by (hi - lo - 1).
pub proof fn lemma_group_modes_rank(layout: LayoutSpec, lo: nat, hi: nat)
    requires group_modes_admissible(&layout, lo, hi),
    ensures
        group_modes(layout, lo, hi).shape.len() == layout.shape.len() - (hi - lo - 1),
        group_modes(layout, lo, hi).stride.len() == layout.stride.len() - (hi - lo - 1),
    decreases hi - lo,
{
    if hi <= lo + 1 {
    } else {
        lemma_group_modes_admissible_step(layout, lo, hi);
        let cp = coalesce_pair(layout, lo);
        lemma_group_modes_rank(cp, lo, (hi - 1) as nat);
        assert(cp.shape.len() == layout.shape.len() - 1);
    }
}

// ══════════════════════════════════════════════════════════════
// Coalesce produces fully coalesced output
// ══════════════════════════════════════════════════════════════

/// After coalescing at position lo, non-coalesceability at positions before lo is preserved.
proof fn lemma_coalesce_pair_preserves_lower(layout: LayoutSpec, lo: nat, j: int)
    requires
        layout.valid(),
        (lo as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, lo as int),
        0 <= j < lo as int,
        j < layout.shape.len() as int - 2,
        !modes_coalesceable(&layout, j),
    ensures
        !modes_coalesceable(&coalesce_pair(layout, lo), j),
{
    let cp = coalesce_pair(layout, lo);
    // For j < lo - 1: both modes j and j+1 are in the take(lo) prefix, unchanged.
    // For j == lo - 1: mode j is from prefix, mode j+1 is the merged mode.
    // In both cases: cp.shape[j] == layout.shape[j], cp.stride[j] == layout.stride[j],
    //   cp.stride[j+1] == layout.stride[j+1] (if j+1 < lo) or layout.stride[lo] (if j+1 == lo).
    if j + 1 < lo as int {
        assert(cp.shape[j] == layout.shape[j]);
        assert(cp.stride[j] == layout.stride[j]);
        assert(cp.stride[j + 1] == layout.stride[j + 1]);
    } else {
        // j + 1 == lo, so j == lo - 1
        assert(cp.shape[j] == layout.shape[j]);
        assert(cp.stride[j] == layout.stride[j]);
        assert(cp.stride[j + 1] == layout.stride[lo as int]);
    }
}

/// coalesce_pass(layout, start) produces a fully coalesced layout,
/// provided positions [0, start) are already not coalesceable.
proof fn lemma_coalesce_pass_fully_coalesced(layout: LayoutSpec, start: nat)
    requires
        layout.valid(),
        forall|j: int| 0 <= j < start as int && j < layout.shape.len() as int - 1
            ==> !modes_coalesceable(&layout, j),
    ensures
        is_fully_coalesced(&coalesce_pass(layout, start)),
    decreases layout.shape.len() as int - start as int,
{
    if start as int >= layout.shape.len() as int - 1 {
        // Base: returns layout. All positions checked.
        assert(coalesce_pass(layout, start) == layout);
    } else if modes_coalesceable(&layout, start as int) {
        let cp = coalesce_pair(layout, start);
        // cp has one fewer mode. Positions [0, start) are still not coalesceable in cp.
        lemma_shape_size_positive(layout.shape);
        lemma_coalesce_pair_offset_general(layout, start, 0);
        // gives cp.valid()
        assert forall|j: int| 0 <= j < start as int && j < cp.shape.len() as int - 1
            implies !modes_coalesceable(&cp, j)
        by {
            lemma_coalesce_pair_preserves_lower(layout, start, j);
        };
        lemma_coalesce_pass_fully_coalesced(cp, start);
    } else {
        // Not coalesceable at start. Advance.
        // Positions [0, start+1) are all not coalesceable.
        assert forall|j: int| 0 <= j < start as int + 1 && j < layout.shape.len() as int - 1
            implies !modes_coalesceable(&layout, j)
        by {
            if j < start as int {
            } else {
                assert(j == start as int);
                assert(!modes_coalesceable(&layout, start as int));
            }
        };
        lemma_coalesce_pass_fully_coalesced(layout, start + 1);
    }
}

/// coalesce(L) is always fully coalesced.
pub proof fn lemma_coalesce_fully_coalesced(layout: LayoutSpec)
    requires
        layout.valid(),
    ensures
        is_fully_coalesced(&coalesce(layout)),
{
    lemma_coalesce_pass_fully_coalesced(layout, 0);
}

/// coalesce is idempotent: coalesce(coalesce(L)) == coalesce(L).
pub proof fn lemma_coalesce_idempotent(layout: LayoutSpec)
    requires
        layout.valid(),
    ensures
        coalesce(coalesce(layout)) == coalesce(layout),
{
    lemma_coalesce_fully_coalesced(layout);
    crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&coalesce(layout));
}

// ══════════════════════════════════════════════════════════════
// Layout compatibility and offset equivalence lemmas
// ══════════════════════════════════════════════════════════════

/// layout_compatible is reflexive.
pub proof fn lemma_compatible_reflexive(a: &LayoutSpec)
    requires a.valid(),
    ensures crate::layout::layout_compatible(a, a),
{
}

/// layout_compatible is symmetric.
pub proof fn lemma_compatible_symmetric(a: &LayoutSpec, b: &LayoutSpec)
    requires crate::layout::layout_compatible(a, b),
    ensures crate::layout::layout_compatible(b, a),
{
}

/// layout_offset_equivalent is transitive.
pub proof fn lemma_offset_equivalent_transitive(a: &LayoutSpec, b: &LayoutSpec, c: &LayoutSpec)
    requires
        crate::layout::layout_offset_equivalent(a, b),
        crate::layout::layout_offset_equivalent(b, c),
    ensures
        crate::layout::layout_offset_equivalent(a, c),
{
    assert forall|x: nat| x < a.size() implies a.offset(x) == c.offset(x)
    by {
        assert(a.offset(x) == b.offset(x));
        assert(b.offset(x) == c.offset(x));
    };
}

/// Coalescing a single pair preserves offset equivalence (wrapper around existing lemma).
pub proof fn lemma_coalesce_pair_preserves_offset(layout: LayoutSpec, i: nat, x: nat)
    requires
        layout.valid(),
        (i as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, i as int),
        x < layout.size(),
    ensures
        coalesce_pair(layout, i).offset(x) == layout.offset(x),
{
    lemma_coalesce_pair_offset_general(layout, i, x);
}

/// Full coalesce is offset-equivalent to the original layout.
pub proof fn lemma_coalesce_offset_equivalent(layout: LayoutSpec)
    requires layout.valid(),
    ensures crate::layout::layout_offset_equivalent(&layout, &coalesce(layout)),
{
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce(layout, 0);
    assert forall|x: nat| x < layout.size() implies layout.offset(x) == coalesce(layout).offset(x)
    by {
        lemma_coalesce(layout, x);
    };
}

/// Flatten is offset-equivalent to the original layout.
pub proof fn lemma_flatten_offset_equivalent(layout: LayoutSpec)
    requires layout.valid(),
    ensures crate::layout::layout_offset_equivalent(&layout, &flatten(layout)),
{
    lemma_shape_size_positive(layout.shape);
    lemma_flatten_valid(layout);
    lemma_flatten_size(layout);
    assert forall|x: nat| x < layout.size() implies layout.offset(x) == flatten(layout).offset(x)
    by {
        lemma_flatten_offset(layout, x);
    };
}

/// Group modes is offset-equivalent to the original layout.
pub proof fn lemma_group_modes_offset_equivalent(layout: LayoutSpec, lo: nat, hi: nat)
    requires group_modes_admissible(&layout, lo, hi),
    ensures crate::layout::layout_offset_equivalent(&layout, &group_modes(layout, lo, hi)),
{
    lemma_shape_size_positive(layout.shape);
    lemma_group_modes_valid(layout, lo, hi);
    lemma_group_modes_size(layout, lo, hi);
    assert forall|x: nat| x < layout.size() implies layout.offset(x) == group_modes(layout, lo, hi).offset(x)
    by {
        lemma_group_modes_offset(layout, lo, hi, x);
    };
}

// ══════════════════════════════════════════════════════════════
// full_flatten: the true canonical form
// ══════════════════════════════════════════════════════════════

/// full_flatten preserves validity.
pub proof fn lemma_full_flatten_valid(layout: LayoutSpec)
    requires layout.valid(),
    ensures full_flatten(layout).valid(),
{
    lemma_flatten_valid(layout);
    lemma_flatten_size(layout);
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce(flatten(layout), 0);
}

/// full_flatten preserves size.
pub proof fn lemma_full_flatten_size(layout: LayoutSpec)
    requires layout.valid(),
    ensures full_flatten(layout).size() == layout.size(),
{
    lemma_flatten_valid(layout);
    lemma_flatten_size(layout);
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce(flatten(layout), 0);
}

/// full_flatten preserves offset for all valid indices.
pub proof fn lemma_full_flatten_offset(layout: LayoutSpec, idx: nat)
    requires
        layout.valid(),
        idx < layout.size(),
    ensures
        full_flatten(layout).offset(idx) == layout.offset(idx),
{
    lemma_flatten_valid(layout);
    lemma_flatten_offset(layout, idx);
    lemma_flatten_size(layout);
    lemma_coalesce(flatten(layout), idx);
}

/// full_flatten is fully coalesced.
pub proof fn lemma_full_flatten_fully_coalesced(layout: LayoutSpec)
    requires layout.valid(),
    ensures is_fully_coalesced(&full_flatten(layout)),
{
    lemma_flatten_valid(layout);
    lemma_coalesce_fully_coalesced(flatten(layout));
}

/// full_flatten is offset-equivalent to the original layout.
pub proof fn lemma_full_flatten_offset_equivalent(layout: LayoutSpec)
    requires layout.valid(),
    ensures crate::layout::layout_offset_equivalent(&layout, &full_flatten(layout)),
{
    lemma_shape_size_positive(layout.shape);
    lemma_full_flatten_valid(layout);
    lemma_full_flatten_size(layout);
    assert forall|x: nat| x < layout.size() implies layout.offset(x) == full_flatten(layout).offset(x)
    by {
        lemma_full_flatten_offset(layout, x);
    };
}

// ══════════════════════════════════════════════════════════════
// No unit modes: helpers for full_flatten idempotency
// ══════════════════════════════════════════════════════════════

/// Predicate: all shape entries are > 1 (no unit modes).
/// Delegates to LayoutSpec::has_no_unit_modes (kept for backward compatibility).
pub open spec fn has_no_unit_modes(layout: &LayoutSpec) -> bool {
    layout.has_no_unit_modes()
}

/// remove_units_iter(L, 0) produces a layout with no unit modes.
pub proof fn lemma_remove_units_no_units(layout: LayoutSpec)
    requires layout.valid(),
    ensures has_no_unit_modes(&remove_units_iter(layout, 0)),
{
    lemma_remove_units_iter_no_units(layout, 0);
}

/// remove_units_iter(L, pos) produces a layout with no unit modes from pos onwards.
proof fn lemma_remove_units_iter_no_units(layout: LayoutSpec, pos: nat)
    requires
        layout.valid(),
        pos <= layout.shape.len(),
        // Modes before pos are already non-unit
        forall|i: int| 0 <= i < pos as int ==> #[trigger] layout.shape[i] > 1,
    ensures
        has_no_unit_modes(&remove_units_iter(layout, pos)),
    decreases layout.shape.len() - pos,
{
    if pos as int >= layout.shape.len() as int {
        // Done: all modes checked, result is layout itself
    } else if layout.shape[pos as int] == 1 {
        // Remove this unit mode
        let removed = LayoutSpec {
            shape: layout.shape.take(pos as int).add(layout.shape.skip(pos as int + 1)),
            stride: layout.stride.take(pos as int).add(layout.stride.skip(pos as int + 1)),
        };
        // removed is valid
        lemma_shape_size_positive(layout.shape);
        assert(removed.valid()) by {
            assert forall|i: int| 0 <= i < removed.shape.len()
            implies #[trigger] removed.shape[i] > 0 by {
                if i < pos as int {
                    assert(removed.shape[i] == layout.shape[i]);
                } else {
                    assert(removed.shape[i] == layout.shape[i + 1]);
                }
            };
        };
        assert(pos <= removed.shape.len());
        // Modes before pos in removed are still non-unit
        assert forall|i: int| 0 <= i < pos as int
        implies #[trigger] removed.shape[i] > 1 by {
            assert(removed.shape[i] == layout.shape[i]);
        };
        lemma_remove_units_iter_no_units(removed, pos);
    } else {
        // shape[pos] > 1 (since valid implies > 0, and != 1 means > 1)
        assert(layout.shape[pos as int] > 1);
        assert forall|i: int| 0 <= i < (pos + 1) as int
        implies #[trigger] layout.shape[i] > 1 by {
            if i < pos as int {} else {
                assert(i == pos as int);
            }
        };
        lemma_remove_units_iter_no_units(layout, pos + 1);
    }
}

/// remove_units_iter on a layout with no unit modes is identity.
proof fn lemma_remove_units_noop(layout: LayoutSpec, pos: nat)
    requires
        layout.valid(),
        pos <= layout.shape.len(),
        has_no_unit_modes(&layout),
    ensures
        remove_units_iter(layout, pos) == layout,
    decreases layout.shape.len() - pos,
{
    if pos as int >= layout.shape.len() as int {
    } else {
        // shape[pos] > 1, so != 1
        assert(layout.shape[pos as int] > 1);
        assert(layout.shape[pos as int] != 1);
        lemma_remove_units_noop(layout, pos + 1);
    }
}

/// Coalescing two modes with shape > 1 produces shape > 1.
/// shape[i] * shape[i+1] >= 2 * 2 = 4 > 1 when both > 1.
proof fn lemma_coalesce_pair_preserves_no_units(layout: LayoutSpec, i: nat)
    requires
        layout.valid(),
        (i as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, i as int),
        has_no_unit_modes(&layout),
    ensures
        has_no_unit_modes(&coalesce_pair(layout, i)),
{
    let result = coalesce_pair(layout, i);
    assert forall|j: int| 0 <= j < result.shape.len()
    implies #[trigger] result.shape[j] > 1 by {
        if j < i as int {
            // result.shape[j] == layout.shape[j] > 1
            assert(result.shape[j] == layout.shape[j]);
        } else if j == i as int {
            // result.shape[j] == layout.shape[i] * layout.shape[i+1] >= 2*2 = 4 > 1
            assert(result.shape[j] == layout.shape[i as int] * layout.shape[i as int + 1]);
            assert(layout.shape[i as int] > 1);
            assert(layout.shape[i as int + 1] > 1);
            assert(layout.shape[i as int] * layout.shape[i as int + 1] > 1) by (nonlinear_arith)
                requires layout.shape[i as int] > 1, layout.shape[i as int + 1] > 1;
        } else {
            // result.shape[j] == layout.shape[j+1] > 1
            assert(result.shape[j] == layout.shape[j + 1]);
        }
    };
}

/// coalesce_pass preserves no-unit-modes property.
proof fn lemma_coalesce_pass_preserves_no_units(layout: LayoutSpec, start: nat)
    requires
        layout.valid(),
        has_no_unit_modes(&layout),
    ensures
        has_no_unit_modes(&coalesce_pass(layout, start)),
    decreases layout.shape.len() - start,
{
    if start as int >= layout.shape.len() as int - 1 {
        // No more pairs to check
    } else if modes_coalesceable(&layout, start as int) {
        let merged = coalesce_pair(layout, start);
        // merged is valid (from existing lemma, using idx=0)
        lemma_shape_size_positive(layout.shape);
        lemma_coalesce_pair_offset_general(layout, start, 0);
        // merged has no unit modes
        lemma_coalesce_pair_preserves_no_units(layout, start);
        // Recurse at same position
        lemma_coalesce_pass_preserves_no_units(merged, start);
    } else {
        lemma_coalesce_pass_preserves_no_units(layout, start + 1);
    }
}

/// coalesce preserves no-unit-modes property.
pub proof fn lemma_coalesce_preserves_no_units(layout: LayoutSpec)
    requires
        layout.valid(),
        has_no_unit_modes(&layout),
    ensures
        has_no_unit_modes(&coalesce(layout)),
{
    lemma_coalesce_pass_preserves_no_units(layout, 0);
}

/// full_flatten produces a layout with no unit modes.
pub proof fn lemma_full_flatten_no_units(layout: LayoutSpec)
    requires layout.valid(),
    ensures has_no_unit_modes(&full_flatten(layout)),
{
    // flatten(L) = remove_units(coalesce(L), 0)
    // coalesce(L) is valid
    lemma_shape_size_positive(layout.shape);
    lemma_coalesce(layout, 0);
    // remove_units produces no unit modes
    lemma_remove_units_no_units(coalesce(layout));
    // flatten(L) has no unit modes
    // full_flatten(L) = coalesce(flatten(L))
    // flatten(L) is valid
    lemma_flatten_valid(layout);
    // coalesce preserves no-unit-modes
    lemma_coalesce_preserves_no_units(flatten(layout));
}

/// full_flatten is idempotent: full_flatten(full_flatten(L)) == full_flatten(L).
pub proof fn lemma_full_flatten_idempotent(layout: LayoutSpec)
    requires layout.valid(),
    ensures full_flatten(full_flatten(layout)) == full_flatten(layout),
{
    let ff = full_flatten(layout);
    // ff is valid
    lemma_full_flatten_valid(layout);
    // ff is fully coalesced
    lemma_full_flatten_fully_coalesced(layout);
    // ff has no unit modes
    lemma_full_flatten_no_units(layout);

    // full_flatten(ff) = coalesce(flatten(ff))
    // flatten(ff) = remove_units(coalesce(ff), 0)
    // coalesce(ff) == ff (already fully coalesced)
    crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&ff);
    assert(coalesce(ff) == ff);
    // remove_units(ff, 0) == ff (no unit modes to remove)
    lemma_remove_units_noop(ff, 0);
    assert(remove_units_iter(ff, 0) == ff);
    // flatten(ff) == ff
    assert(flatten(ff) == ff);
    // coalesce(flatten(ff)) == coalesce(ff) == ff
}

// ══════════════════════════════════════════════════════════════
// full_flatten canonicality (partial results)
// ══════════════════════════════════════════════════════════════

/// Column-major layouts with size > 1 full_flatten to make_identity(size).
pub proof fn lemma_full_flatten_column_major(shape: Seq<nat>)
    requires
        shape_valid(shape),
        shape.len() > 0,
        shape_size(shape) > 1,
    ensures
        full_flatten(make_column_major(shape)) == make_identity(shape_size(shape)),
{
    let layout = make_column_major(shape);
    let m = shape_size(shape);

    // coalesce(column_major) == make_identity(M)
    crate::proof::inverse_lemmas::lemma_coalesce_column_major(shape);
    let id = make_identity(m);
    assert(coalesce(layout) == id);

    // id = (M):(1), M > 1 → no unit modes
    assert(has_no_unit_modes(&id));
    assert(id.valid()) by {
        assert(id.shape =~= seq![m]);
        assert(id.stride =~= seq![1int]);
    };
    lemma_remove_units_noop(id, 0);
    // flatten(layout) = remove_units(id, 0) = id
    assert(flatten(layout) == id);

    // coalesce(id) == id (fully coalesced, rank 1)
    crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&id);
    // full_flatten(layout) = coalesce(flatten(layout)) = coalesce(id) = id
}

/// Two rank-1 layouts with the same size and stride are structurally equal.
/// This is the base case for canonicality.
pub proof fn lemma_rank1_offset_equivalent_implies_equal(
    l1: &LayoutSpec, l2: &LayoutSpec,
)
    requires
        l1.valid(),
        l2.valid(),
        l1.shape.len() == 1,
        l2.shape.len() == 1,
        l1.size() == l2.size(),
        l1.size() > 1,
        // Offset equivalent
        forall|x: nat| x < l1.size() ==> l1.offset(x) == l2.offset(x),
    ensures
        *l1 == *l2,
{
    // l1 = (M):(d), l2 = (N):(e), M == N > 1
    let m = l1.shape.first();
    let n = l2.shape.first();
    let d = l1.stride.first();
    let e = l2.stride.first();

    // size == shape[0] for rank-1 layouts
    assert(l1.shape =~= seq![m]);
    assert(l2.shape =~= seq![n]);
    lemma_shape_size_single(m);
    lemma_shape_size_single(n);
    assert(l1.size() == m);
    assert(l2.size() == n);
    assert(m == n);

    // d == e from offset(1) == offset(1)
    // Need 1 < m (which follows from size > 1)
    assert(1nat < m);
    lemma_offset_within_first_mode(l1, 1);
    lemma_offset_within_first_mode(l2, 1);
    assert(l1.offset(1) == d);
    assert(l2.offset(1) == e);
    assert(d == e);

    // Structural equality
    assert(l1.shape =~= l2.shape);
    assert(l1.stride =~= l2.stride);
}

// ══════════════════════════════════════════════════════════════
// full_flatten canonicality for sorted+tractable layouts
// ══════════════════════════════════════════════════════════════

/// For a fully-coalesced layout with shape[0] >= 2 and rank >= 2,
/// offset(shape[0]) != shape[0] * stride[0].
///
/// This follows because delinearize(shape[0]) = (0, 1, 0, ...),
/// so offset(shape[0]) = stride[1], and stride[1] != shape[0] * stride[0]
/// by the fully-coalesced property.
proof fn lemma_offset_at_shape0_breaks(layout: &LayoutSpec)
    requires
        layout.valid(),
        layout.shape.len() >= 2,
        is_fully_coalesced(layout),
        has_no_unit_modes(layout),
        layout.non_negative_strides(),
        layout.is_sorted(),
    ensures
        layout.offset(layout.shape.first())
            != (layout.shape.first() as int) * layout.stride.first(),
{
    let m0 = layout.shape.first();
    let d0 = layout.stride.first();
    let d1 = layout.stride[1];

    // Not coalesceable at 0: d1 != m0 * d0
    assert(!modes_coalesceable(layout, 0));
    assert(d1 != (m0 as int) * d0);

    // offset(m0): delinearize(m0, shape) = (0, 1, 0, ...)
    // since m0 % m0 == 0, m0 / m0 == 1, and 1 < shape[1] (no unit modes)
    assert(m0 > 1); // no unit modes
    assert(layout.shape[1] > 1); // no unit modes

    // offset(m0) = 0 * d0 + 1 * d1 + 0 * ... = d1
    lemma_offset_within_first_mode(layout, 0nat);
    // Actually we need offset(m0) = d1, not offset(0) = 0
    // offset(m0) = dot(delinearize(m0, shape), stride)
    // delinearize(m0, shape)[0] = m0 % m0 = 0
    // delinearize(m0, shape)[1] = (m0 / m0) % shape[1] = 1 % shape[1] = 1

    // Use the prefix-product approach: m0 = prefix_product[1] * 1
    // So by lemma_offset_at_split_mode: offset(m0) = 1 * stride[1] = d1
    crate::runtime::shape_helpers::lemma_shape_size_split(layout.shape, 1);
    assert(layout.shape.take(1) =~= seq![m0]);
    lemma_shape_size_single(m0);
    assert(shape_size(layout.shape.take(1)) == m0);
    // m0 * 1 = m0 < shape_size(layout.shape) (since rank >= 2 and shape[1] >= 2)
    assert(shape_size(layout.shape.take(1)) * 1 < shape_size(layout.shape)) by {
        // shape_size = m0 * shape_size(skip(1)) >= m0 * shape[1] >= m0 * 2 > m0
        lemma_shape_size_positive(layout.shape.skip(1));
        crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(layout.shape.skip(1), 0);
        assert(layout.shape.skip(1).first() == layout.shape[1]);
        assert(shape_size(layout.shape.skip(1)) >= layout.shape[1]);
        assert(shape_size(layout.shape.skip(1)) >= 2nat);
        assert(m0 * shape_size(layout.shape.skip(1)) >= m0 * 2) by (nonlinear_arith)
            requires m0 > 0, shape_size(layout.shape.skip(1)) >= 2;
        assert(m0 * 2 > m0) by (nonlinear_arith) requires m0 > 0;
    };
    crate::proof::composition_lemmas::lemma_offset_at_split_mode(layout, 1, 1);
    assert(layout.offset(m0) == d1);

    // m0 * d0 != d1 (from not coalesceable)
    // So offset(m0) != m0 * d0
}

/// For a layout with rank >= 2 and no unit modes, shape[0] < size.
proof fn lemma_shape0_lt_size(layout: &LayoutSpec)
    requires
        layout.valid(),
        layout.shape.len() >= 2,
        has_no_unit_modes(layout),
    ensures
        layout.shape.first() < layout.size(),
{
    let m0 = layout.shape.first();
    crate::runtime::shape_helpers::lemma_shape_size_split(layout.shape, 1);
    assert(layout.shape.take(1) =~= seq![m0]);
    lemma_shape_size_single(m0);
    lemma_shape_size_positive(layout.shape.skip(1));
    crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(layout.shape.skip(1), 0);
    assert(shape_size(layout.shape.skip(1)) >= 2nat);
    assert(m0 * shape_size(layout.shape.skip(1)) > m0) by (nonlinear_arith)
        requires m0 > 0, shape_size(layout.shape.skip(1)) >= 2;
}

/// skip(1) of a canonical layout preserves all structural properties.
proof fn lemma_skip1_preserves_canonical(layout: &LayoutSpec)
    requires
        layout.valid(),
        layout.shape.len() >= 2,
        has_no_unit_modes(layout),
        is_fully_coalesced(layout),
        layout.non_negative_strides(),
        layout.is_sorted(),
        layout.is_tractable(),
    ensures ({
        let r = LayoutSpec { shape: layout.shape.skip(1), stride: layout.stride.skip(1) };
        &&& r.valid()
        &&& has_no_unit_modes(&r)
        &&& is_fully_coalesced(&r)
        &&& r.non_negative_strides()
        &&& r.is_sorted()
        &&& r.is_tractable()
        &&& r.size() > 1
    }),
{
    let r = LayoutSpec { shape: layout.shape.skip(1), stride: layout.stride.skip(1) };
    assert(r.valid()) by {
        assert forall|i: int| 0 <= i < r.shape.len()
        implies #[trigger] r.shape[i] > 0 by { assert(r.shape[i] == layout.shape[i + 1]); };
    };
    assert(has_no_unit_modes(&r)) by {
        assert forall|i: int| 0 <= i < r.shape.len()
        implies #[trigger] r.shape[i] > 1 by { assert(r.shape[i] == layout.shape[i + 1]); };
    };
    assert(r.non_negative_strides()) by {
        assert forall|i: int| 0 <= i < r.stride.len()
        implies #[trigger] r.stride[i] >= 0 by { assert(r.stride[i] == layout.stride[i + 1]); };
    };
    assert(r.is_sorted()) by {
        assert forall|i: int| 0 <= i < r.stride.len() as int - 1
        implies #[trigger] r.stride[i] <= r.stride[i + 1] by {
            assert(r.stride[i] == layout.stride[i + 1]);
            assert(r.stride[i + 1] == layout.stride[i + 2]);
        };
    };
    assert(r.is_tractable()) by {
        assert forall|i: int| 0 <= i < r.stride.len() as int - 1
        implies #[trigger] r.tractable_at(i) by {
            assert(r.shape[i] == layout.shape[i + 1]);
            assert(r.stride[i] == layout.stride[i + 1]);
            assert(r.stride[i + 1] == layout.stride[i + 2]);
            assert(layout.tractable_at(i + 1));
        };
    };
    assert(is_fully_coalesced(&r)) by {
        assert forall|i: int| 0 <= i < r.shape.len() as int - 1
        implies !modes_coalesceable(&r, i) by {
            assert(r.stride[i + 1] == layout.stride[i + 2]);
            assert(r.shape[i] == layout.shape[i + 1]);
            assert(r.stride[i] == layout.stride[i + 1]);
            assert(!modes_coalesceable(layout, i + 1));
        };
    };
    assert(r.size() > 1) by {
        if r.shape.len() == 0 {
            lemma_shape_size_empty();
            crate::runtime::shape_helpers::lemma_shape_size_split(layout.shape, 1);
            assert(layout.shape.take(1) =~= seq![layout.shape.first()]);
            lemma_shape_size_single(layout.shape.first());
        } else {
            crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(r.shape, 0);
            assert(r.shape[0] == layout.shape[1]);
        }
    };
}

/// Canonicality for sorted, tractable, fully-coalesced, unit-free layouts:
/// offset-equivalent implies structurally equal.
///
/// Proof by induction on rank:
/// - stride[0] is determined by offset(1) = stride[0]
/// - shape[0] is determined as smallest k where offset(k) != k*stride[0]
/// - Remaining modes recurse via offset(shape[0] * y) = rest.offset(y)
pub proof fn lemma_canonical_sorted_tractable(l1: &LayoutSpec, l2: &LayoutSpec)
    requires
        l1.valid(), l2.valid(),
        l1.size() == l2.size(),
        l1.size() > 1,
        has_no_unit_modes(l1), has_no_unit_modes(l2),
        is_fully_coalesced(l1), is_fully_coalesced(l2),
        l1.non_negative_strides(), l2.non_negative_strides(),
        l1.is_sorted(), l2.is_sorted(),
        l1.is_tractable(), l2.is_tractable(),
        // Offset equivalent
        forall|x: nat| x < l1.size() ==> l1.offset(x) == l2.offset(x),
    ensures
        *l1 == *l2,
    decreases l1.shape.len(),
{
    if l1.shape.len() <= 1 && l2.shape.len() <= 1 {
        // Both rank-1 (rank-0 impossible since size > 1 requires at least 1 mode)
        assert(l1.shape.len() == 1 && l2.shape.len() == 1) by {
            if l1.shape.len() == 0 {
                lemma_shape_size_empty();
                assert(l1.size() == 1nat);
                assert(false); // size > 1
            }
            if l2.shape.len() == 0 {
                lemma_shape_size_empty();
                assert(l2.size() == 1nat);
                assert(false);
            }
        };
        lemma_rank1_offset_equivalent_implies_equal(l1, l2);
    } else {
        // At least one has rank >= 2. Show both must have rank >= 2.
        // If one is rank 1 and the other rank >= 2, derive contradiction.
        assert(l1.shape.len() >= 1 && l2.shape.len() >= 1) by {
            if l1.shape.len() == 0 { lemma_shape_size_empty(); assert(false); }
            if l2.shape.len() == 0 { lemma_shape_size_empty(); assert(false); }
        };

        // Step 1: stride[0] agrees (from offset(1) = stride[0])
        assert(l1.shape.first() > 1); // no unit modes
        assert(l2.shape.first() > 1);
        lemma_offset_within_first_mode(l1, 1);
        lemma_offset_within_first_mode(l2, 1);
        assert(l1.stride.first() == l2.stride.first());
        let d0 = l1.stride.first();

        // Step 2: shape[0] agrees.
        // For k < shape[0]: offset(k) = k * d0 (within first mode)
        // At k = shape[0]: offset(shape[0]) != shape[0] * d0 (for rank >= 2)
        // The smallest such k must be the same for both.

        // Handle the case where one is rank 1 and the other rank >= 2
        if l1.shape.len() == 1 {
            // L1 is rank-1: offset(k) = k * d0 for ALL k < size
            // L2 has rank >= 2: at k = l2.shape[0], offset(k) != k * d0
            // But L1.offset(l2.shape[0]) = l2.shape[0] * d0 (since l2.shape[0] < l2.size = l1.size)
            // and L2.offset(l2.shape[0]) != l2.shape[0] * d0 → contradiction
            assert(l2.shape.len() >= 2);
            lemma_offset_at_shape0_breaks(l2);
            let m = l2.shape.first();
            // m < l2.size() (since rank >= 2 and shape entries >= 2)
            lemma_size_at_least_first(l2.shape);
            crate::runtime::shape_helpers::lemma_shape_size_split(l2.shape, 1);
            assert(l2.shape.take(1) =~= seq![m]);
            lemma_shape_size_single(m);
            lemma_shape_size_positive(l2.shape.skip(1));
            assert(m < l2.size()) by {
                assert(l2.size() == m * shape_size(l2.shape.skip(1)));
                assert(shape_size(l2.shape.skip(1)) >= 2nat) by {
                    crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(l2.shape.skip(1), 0);
                };
                assert(m * shape_size(l2.shape.skip(1)) >= m * 2) by (nonlinear_arith)
                    requires m > 0, shape_size(l2.shape.skip(1)) >= 2;
            };
            // For rank-1 L1: l1.shape.first() == l1.size() > m
            assert(l1.shape =~= seq![l1.shape.first()]);
            lemma_shape_size_single(l1.shape.first());
            assert(shape_size(l1.shape) == l1.shape.first());
            assert(m < l1.shape.first());
            lemma_offset_within_first_mode(l1, m);
            // L1.offset(m) = m * d0, L2.offset(m) != m * d0, but they must be equal
            assert(l1.offset(m) == l2.offset(m));
            assert(false);
        }
        if l2.shape.len() == 1 {
            // Symmetric case
            assert(l1.shape.len() >= 2);
            lemma_offset_at_shape0_breaks(l1);
            let m = l1.shape.first();
            crate::runtime::shape_helpers::lemma_shape_size_split(l1.shape, 1);
            assert(l1.shape.take(1) =~= seq![m]);
            lemma_shape_size_single(m);
            lemma_shape_size_positive(l1.shape.skip(1));
            assert(m < l1.size()) by {
                assert(l1.size() == m * shape_size(l1.shape.skip(1)));
                crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(l1.shape.skip(1), 0);
                assert(m * shape_size(l1.shape.skip(1)) >= m * 2) by (nonlinear_arith)
                    requires m > 0, shape_size(l1.shape.skip(1)) >= 2;
            };
            assert(l2.shape =~= seq![l2.shape.first()]);
            lemma_shape_size_single(l2.shape.first());
            assert(shape_size(l2.shape) == l2.shape.first());
            assert(m < l2.shape.first());
            lemma_offset_within_first_mode(l2, m);
            assert(l1.offset(m) == l2.offset(m));
            assert(false);
        }

        // Both have rank >= 2
        assert(l1.shape.len() >= 2 && l2.shape.len() >= 2);

        // Now show shape[0] agrees. WLOG assume l1.shape[0] <= l2.shape[0].
        // At k = l1.shape[0]: L1.offset(k) != k * d0, but if l1.shape[0] < l2.shape[0],
        // then L2.offset(k) = k * d0. Contradiction.
        let m1 = l1.shape.first();
        let m2 = l2.shape.first();

        if m1 < m2 {
            // L2.offset(m1) = m1 * d0 (since m1 < m2 = l2.shape[0])
            lemma_offset_within_first_mode(l2, m1);
            assert(l2.offset(m1) == (m1 as int) * d0);
            // L1.offset(m1) != m1 * d0 (from offset_at_shape0_breaks)
            lemma_offset_at_shape0_breaks(l1);
            assert(l1.offset(m1) != (m1 as int) * d0);
            // But they must be equal (m1 < m2 < l2.size() = l1.size())
            assert(m1 < l1.size()) by {
                crate::runtime::shape_helpers::lemma_shape_size_split(l1.shape, 1);
                assert(l1.shape.take(1) =~= seq![m1]);
                lemma_shape_size_single(m1);
                lemma_shape_size_positive(l1.shape.skip(1));
                crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(l1.shape.skip(1), 0);
                assert(m1 * shape_size(l1.shape.skip(1)) >= m1 * 2) by (nonlinear_arith)
                    requires m1 > 0, shape_size(l1.shape.skip(1)) >= 2;
            };
            assert(l1.offset(m1) == l2.offset(m1));
            assert(false);
        }
        if m2 < m1 {
            lemma_offset_within_first_mode(l1, m2);
            assert(l1.offset(m2) == (m2 as int) * d0);
            lemma_offset_at_shape0_breaks(l2);
            assert(l2.offset(m2) != (m2 as int) * d0);
            assert(m2 < l2.size()) by {
                crate::runtime::shape_helpers::lemma_shape_size_split(l2.shape, 1);
                assert(l2.shape.take(1) =~= seq![m2]);
                lemma_shape_size_single(m2);
                lemma_shape_size_positive(l2.shape.skip(1));
                crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(l2.shape.skip(1), 0);
                assert(m2 * shape_size(l2.shape.skip(1)) >= m2 * 2) by (nonlinear_arith)
                    requires m2 > 0, shape_size(l2.shape.skip(1)) >= 2;
            };
            assert(l1.offset(m2) == l2.offset(m2));
            assert(false);
        }
        assert(m1 == m2);
        let m0 = m1;

        // Step 3: stride[1] agrees (from offset(m0) = stride[1])
        assert(l1.shape.take(1) =~= seq![m0]);
        assert(l2.shape.take(1) =~= seq![m0]);
        lemma_shape_size_single(m0);
        lemma_shape0_lt_size(l1);
        lemma_shape0_lt_size(l2);
        crate::proof::composition_lemmas::lemma_offset_at_split_mode(l1, 1, 1);
        crate::proof::composition_lemmas::lemma_offset_at_split_mode(l2, 1, 1);
        assert(l1.stride[1] == l2.stride[1]);

        // Step 4: Recurse on remaining modes.
        let l1r = LayoutSpec { shape: l1.shape.skip(1), stride: l1.stride.skip(1) };
        let l2r = LayoutSpec { shape: l2.shape.skip(1), stride: l2.stride.skip(1) };

        // Remaining layouts preserve all properties (extracted to helper)
        lemma_skip1_preserves_canonical(l1);
        lemma_skip1_preserves_canonical(l2);

        // Same size
        crate::runtime::shape_helpers::lemma_shape_size_split(l1.shape, 1);
        crate::runtime::shape_helpers::lemma_shape_size_split(l2.shape, 1);
        assert(l1r.size() == l2r.size()) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, l1r.size() as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, l2r.size() as int);
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(l1r.size() as int, m0 as int);
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(l2r.size() as int, m0 as int);
        };

        // Offset equivalence: l1r.offset(y) == l2r.offset(y) for y < l1r.size()
        // Because l1r.offset(y) == l1.offset(m0 * y) == l2.offset(m0 * y) == l2r.offset(y)
        // (by lemma_offset_at_split_mode: offset(pp[1]*y) at mode 1 = y * stride[1])
        // Actually: L.offset(m0 * y) = l_rest.offset(y) + 0*stride[0]
        // because delinearize(m0*y, shape) = (0, delinearize(y, shape.skip(1)))
        assert forall|y: nat| y < l1r.size() implies l1r.offset(y) == l2r.offset(y) by {
            // l1.offset(m0 * y) == l2.offset(m0 * y) (from offset equivalence)
            // m0 * y < l1.size() (since y < l1r.size() and l1.size() = m0 * l1r.size())
            assert(m0 * y < l1.size()) by (nonlinear_arith)
                requires m0 > 0, y < l1r.size(), l1.size() == m0 * l1r.size();
            assert(l1.offset(m0 * y) == l2.offset(m0 * y));

            // l1.offset(m0 * y) == l1r.offset(y): by offset_at_split_mode at mode index 1
            // Actually, we need a helper: for L with shape (M0, rest) and index M0*y:
            // delinearize(M0*y, (M0, rest)) = (0, delinearize(y, rest))
            // offset = 0*stride[0] + rest_offset(y) = l1r.offset(y)
            // This follows from delinearize_concat
            lemma_delinearize_concat(m0 * y, seq![m0], l1r.shape);
            lemma_delinearize_len(0nat, seq![m0]);
            assert(l1.shape =~= seq![m0].add(l1r.shape));
            assert(l1.stride =~= seq![d0].add(l1r.stride));
            // (m0*y) % m0 == 0, (m0*y) / m0 == y
            crate::proof::integer_helpers::lemma_div_mul_cancel(m0, y);
            vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, y as int);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(y as int, m0 as int);
            // dot(delinearize(0, [m0]), [d0]) + dot(delinearize(y, l1r.shape), l1r.stride)
            lemma_delinearize_len(y, l1r.shape);
            lemma_dot_product_append(
                delinearize(0nat, seq![m0]), delinearize(y, l1r.shape),
                seq![d0], l1r.stride,
            );
            crate::proof::offset_lemmas::lemma_offset_zero(
                LayoutSpec { shape: seq![m0], stride: seq![d0] },
            );

            // Same for l2
            lemma_delinearize_concat(m0 * y, seq![m0], l2r.shape);
            lemma_delinearize_len(0nat, seq![m0]);
            assert(l2.shape =~= seq![m0].add(l2r.shape));
            assert(l2.stride =~= seq![d0].add(l2r.stride));
            lemma_delinearize_len(y, l2r.shape);
            lemma_dot_product_append(
                delinearize(0nat, seq![m0]), delinearize(y, l2r.shape),
                seq![d0], l2r.stride,
            );
        };

        // Recurse!
        lemma_canonical_sorted_tractable(&l1r, &l2r);
        assert(l1r == l2r);

        // Conclude: l1 == l2 (same shape[0], stride[0], and same skip(1))
        assert(l1.shape =~= l2.shape) by {
            assert(l1.shape.first() == l2.shape.first());
            assert(l1.shape.skip(1) =~= l2.shape.skip(1));
            assert forall|i: int| 0 <= i < l1.shape.len()
            implies l1.shape[i] == l2.shape[i] by {
                if i == 0 {} else { assert(l1.shape[i] == l1r.shape[i - 1]); }
            };
        };
        assert(l1.stride =~= l2.stride) by {
            assert(l1.stride.first() == l2.stride.first());
            assert(l1.stride.skip(1) =~= l2.stride.skip(1));
            assert forall|i: int| 0 <= i < l1.stride.len()
            implies l1.stride[i] == l2.stride[i] by {
                if i == 0 {} else { assert(l1.stride[i] == l1r.stride[i - 1]); }
            };
        };
    }
}

} // verus!
