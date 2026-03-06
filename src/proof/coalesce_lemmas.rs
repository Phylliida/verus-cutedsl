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

} // verus!
