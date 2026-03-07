use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::coalesce::*;
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

    // removed.offset(idx) = dot(coords_head, d_head) + dot(coords_tail_rest, d_tail_rest)
    // original.offset(idx) = dot(coords_head, d_head) + 0 + dot(coords_tail_rest, d_tail_rest)
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

} // verus!
