use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Size lemmas
// ══════════════════════════════════════════════════════════════

/// A valid shape has positive size.
pub proof fn lemma_shape_size_positive(s: Seq<nat>)
    requires shape_valid(s),
    ensures shape_size(s) > 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s[0] > 0);
        lemma_shape_size_positive(s.skip(1));
        lemma_mul_pos(s.first(), shape_size(s.skip(1)));
    }
}

/// Empty shape has size 1.
pub proof fn lemma_shape_size_empty()
    ensures shape_size(Seq::<nat>::empty()) == 1,
{
}

/// Single-element shape has size equal to its extent.
pub proof fn lemma_shape_size_single(m: nat)
    requires m > 0,
    ensures shape_size(seq![m]) == m,
{
    // shape_size(seq![m]) = m * shape_size(seq![m].skip(1))
    // seq![m].skip(1) =~= seq![]
    // shape_size(seq![]) = 1
    // m * 1 = m
    assert(seq![m].skip(1) =~= Seq::<nat>::empty());
    assert(shape_size(Seq::<nat>::empty()) == 1);
    vstd::arithmetic::mul::lemma_mul_basics(m as int);
}

// ══════════════════════════════════════════════════════════════
// Delinearize lemmas
// ══════════════════════════════════════════════════════════════

/// Delinearize produces a sequence of the same length as the shape.
pub proof fn lemma_delinearize_len(idx: nat, shape: Seq<nat>)
    requires shape_valid(shape),
    ensures delinearize(idx, shape).len() == shape.len(),
    decreases shape.len(),
{
    if shape.len() > 0 {
        assert(shape.first() > 0);
        lemma_delinearize_len(idx / shape.first(), shape.skip(1));
    }
}

/// Helper: establish rest_idx < shape_size(rest_shape) from idx < shape_size(shape).
proof fn lemma_rest_idx_bound(idx: nat, d: nat, rest_shape: Seq<nat>)
    requires
        d > 0,
        shape_valid(rest_shape),
        idx < d * shape_size(rest_shape),
    ensures
        idx / d < shape_size(rest_shape),
{
    lemma_div_upper_bound(idx, d, shape_size(rest_shape));
}

/// Each coordinate from delinearize is in-bounds.
pub proof fn lemma_delinearize_bounds(idx: nat, shape: Seq<nat>)
    requires
        shape_valid(shape),
        idx < shape_size(shape),
    ensures
        delinearize(idx, shape).len() == shape.len(),
        coords_in_bounds(delinearize(idx, shape), shape),
    decreases shape.len(),
{
    lemma_delinearize_len(idx, shape);
    if shape.len() > 0 {
        let d = shape.first();
        let rest_shape = shape.skip(1);
        let rest_idx = idx / d;

        // idx % d < d
        lemma_mod_bound(idx, d);

        // rest_idx < shape_size(rest_shape)
        assert(shape_size(shape) == d * shape_size(rest_shape));
        lemma_rest_idx_bound(idx, d, rest_shape);

        // Recurse
        lemma_delinearize_bounds(rest_idx, rest_shape);

        let coords = delinearize(idx, shape);
        let rest_coords = delinearize(rest_idx, rest_shape);

        assert forall|i: int| 0 <= i < coords.len() implies #[trigger] coords[i] < shape[i]
        by {
            if i == 0 {
                assert(coords[0] == idx % d);
                assert(shape[0] == d);
            } else {
                assert(coords[i] == rest_coords[i - 1]);
                assert(shape[i] == rest_shape[i - 1]);
            }
        };
    }
}

// ══════════════════════════════════════════════════════════════
// Roundtrip: linearize(delinearize(x, S), S) == x
// ══════════════════════════════════════════════════════════════

/// The fundamental roundtrip: delinearize then linearize recovers the original index.
pub proof fn lemma_delinearize_roundtrip(idx: nat, shape: Seq<nat>)
    requires
        shape_valid(shape),
        idx < shape_size(shape),
    ensures
        linearize(delinearize(idx, shape), shape) == idx,
    decreases shape.len(),
{
    if shape.len() > 0 {
        let d = shape.first();
        let rest_shape = shape.skip(1);
        let rest_idx = idx / d;
        let coords = delinearize(idx, shape);

        // rest_idx < shape_size(rest_shape)
        assert(shape_size(shape) == d * shape_size(rest_shape));
        lemma_rest_idx_bound(idx, d, rest_shape);

        // IH: linearize(delinearize(rest_idx, rest_shape), rest_shape) == rest_idx
        lemma_delinearize_roundtrip(rest_idx, rest_shape);

        // coords == seq![idx % d] ++ delinearize(rest_idx, rest_shape)
        assert(coords.first() == idx % d);
        assert(coords.skip(1) =~= delinearize(rest_idx, rest_shape));

        // linearize(coords, shape)
        //   = coords[0] + d * linearize(coords.skip(1), rest_shape)
        //   = (idx % d) + d * rest_idx
        //   = idx
        lemma_delinearize_len(rest_idx, rest_shape);
        assert(linearize(coords.skip(1), rest_shape) == rest_idx);
        lemma_div_mod_identity(idx, d);
    }
}

// ══════════════════════════════════════════════════════════════
// Roundtrip: delinearize(linearize(c, S), S) == c
// ══════════════════════════════════════════════════════════════

/// Linearize produces a value less than the shape size.
pub proof fn lemma_linearize_bound(coords: Seq<nat>, shape: Seq<nat>)
    requires
        shape_valid(shape),
        coords_in_bounds(coords, shape),
    ensures
        linearize(coords, shape) < shape_size(shape),
    decreases shape.len(),
{
    if shape.len() > 0 {
        let d = shape.first();
        let rest_shape = shape.skip(1);
        let rest_coords = coords.skip(1);

        // Propagate bounds to rest
        assert(rest_coords.len() == rest_shape.len());
        assert forall|i: int| 0 <= i < rest_coords.len() implies
            #[trigger] rest_coords[i] < rest_shape[i]
        by {
            assert(rest_coords[i] == coords[i + 1]);
            assert(rest_shape[i] == shape[i + 1]);
        };

        lemma_linearize_bound(rest_coords, rest_shape);

        // coords[0] < d, linearize(rest) < shape_size(rest)
        // => coords[0] + d * linearize(rest) < d * shape_size(rest) = shape_size(shape)
        lemma_mixed_radix_bound(
            coords.first(),
            d,
            linearize(rest_coords, rest_shape),
            shape_size(rest_shape),
        );
    }
}

/// The inverse roundtrip: linearize then delinearize recovers the original coordinates.
pub proof fn lemma_linearize_roundtrip(coords: Seq<nat>, shape: Seq<nat>)
    requires
        shape_valid(shape),
        coords_in_bounds(coords, shape),
    ensures
        delinearize(linearize(coords, shape), shape) =~= coords,
    decreases shape.len(),
{
    if shape.len() > 0 {
        let d = shape.first();
        let rest_shape = shape.skip(1);
        let rest_coords = coords.skip(1);

        // Propagate bounds
        assert(rest_coords.len() == rest_shape.len());
        assert forall|i: int| 0 <= i < rest_coords.len() implies
            #[trigger] rest_coords[i] < rest_shape[i]
        by {
            assert(rest_coords[i] == coords[i + 1]);
            assert(rest_shape[i] == shape[i + 1]);
        };

        lemma_linearize_bound(rest_coords, rest_shape);
        let rest_lin = linearize(rest_coords, rest_shape);

        // idx = coords[0] + d * rest_lin, with coords[0] < d
        let idx = linearize(coords, shape);
        assert(idx == coords.first() + d * rest_lin);
        assert(coords.first() < d);

        // (a + d * b) % d == a and (a + d * b) / d == b
        lemma_div_mod_decompose(coords.first(), rest_lin, d);
        assert(idx % d == coords.first());
        assert(idx / d == rest_lin);

        // IH: delinearize(rest_lin, rest_shape) =~= rest_coords
        lemma_linearize_roundtrip(rest_coords, rest_shape);

        // Chain:
        // delinearize(idx, shape) = seq![idx%d] ++ delinearize(idx/d, rest_shape)
        //                         = seq![coords[0]] ++ delinearize(rest_lin, rest_shape)
        //                         = seq![coords[0]] ++ rest_coords
        //                         = coords
        assert(delinearize(idx, shape) =~= seq![idx % d].add(delinearize(idx / d, rest_shape)));
        assert(delinearize(rest_lin, rest_shape) =~= rest_coords);
        assert(seq![coords.first()].add(rest_coords) =~= coords);
    }
}

// ══════════════════════════════════════════════════════════════
// Concatenation lemmas for product offset decomposition
// ══════════════════════════════════════════════════════════════

/// linearize distributes over shape concatenation:
/// linearize(c_a ++ c_b, s_a ++ s_b) == linearize(c_a, s_a) + size(s_a) * linearize(c_b, s_b)
pub proof fn lemma_linearize_concat(
    c_a: Seq<nat>, c_b: Seq<nat>, s_a: Seq<nat>, s_b: Seq<nat>,
)
    requires
        c_a.len() == s_a.len(),
        c_b.len() == s_b.len(),
    ensures
        linearize(c_a.add(c_b), s_a.add(s_b))
            == linearize(c_a, s_a) + shape_size(s_a) * linearize(c_b, s_b),
    decreases s_a.len(),
{
    if s_a.len() == 0 {
        // c_a ++ c_b =~= c_b, s_a ++ s_b =~= s_b
        assert(c_a.add(c_b) =~= c_b);
        assert(s_a.add(s_b) =~= s_b);
        // linearize([], []) == 0, shape_size([]) == 1
        // 0 + 1 * linearize(c_b, s_b) == linearize(c_b, s_b) ✓
        vstd::arithmetic::mul::lemma_mul_basics(linearize(c_b, s_b) as int);
    } else {
        // (c_a ++ c_b)[0] == c_a[0], (s_a ++ s_b)[0] == s_a[0]
        let ca_cb = c_a.add(c_b);
        let sa_sb = s_a.add(s_b);
        assert(ca_cb.first() == c_a.first());
        assert(sa_sb.first() == s_a.first());
        assert(ca_cb.skip(1) =~= c_a.skip(1).add(c_b));
        assert(sa_sb.skip(1) =~= s_a.skip(1).add(s_b));

        // IH: linearize(c_a.skip(1) ++ c_b, s_a.skip(1) ++ s_b)
        //     == linearize(c_a.skip(1), s_a.skip(1)) + size(s_a.skip(1)) * linearize(c_b, s_b)
        lemma_linearize_concat(c_a.skip(1), c_b, s_a.skip(1), s_b);

        // linearize(ca_cb, sa_sb) = ca_cb[0] + sa_sb[0] * linearize(ca_cb.skip(1), sa_sb.skip(1))
        //                         = c_a[0] + s_a[0] * (linearize(c_a.skip(1), s_a.skip(1))
        //                                              + size(s_a.skip(1)) * linearize(c_b, s_b))
        //                         = c_a[0] + s_a[0] * linearize(c_a.skip(1), s_a.skip(1))
        //                                  + s_a[0] * size(s_a.skip(1)) * linearize(c_b, s_b)
        //                         = linearize(c_a, s_a) + size(s_a) * linearize(c_b, s_b)

        let lin_tail = linearize(c_a.skip(1), s_a.skip(1));
        let lin_b = linearize(c_b, s_b);
        let size_tail = shape_size(s_a.skip(1));

        // Distributivity: s_a[0] * (lin_tail + size_tail * lin_b) = s_a[0]*lin_tail + s_a[0]*size_tail*lin_b
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            s_a.first() as int, lin_tail as int, (size_tail * lin_b) as int,
        );

        // Associativity: s_a[0] * (size_tail * lin_b) == (s_a[0] * size_tail) * lin_b == size(s_a) * lin_b
        vstd::arithmetic::mul::lemma_mul_is_associative(
            s_a.first() as int, size_tail as int, lin_b as int,
        );
    }
}

/// Dot product respects extensional equality on both arguments.
pub proof fn lemma_dot_product_ext(c1: Seq<nat>, c2: Seq<nat>, s1: Seq<int>, s2: Seq<int>)
    requires
        c1.len() == s1.len(),
        c1 =~= c2,
        s1 =~= s2,
    ensures
        dot_product_nat_int(c1, s1) == dot_product_nat_int(c2, s2),
    decreases c1.len(),
{
    if c1.len() == 0 {
    } else {
        assert(c1.first() == c2.first());
        assert(s1.first() == s2.first());
        assert(c1.skip(1) =~= c2.skip(1));
        assert(s1.skip(1) =~= s2.skip(1));
        lemma_dot_product_ext(c1.skip(1), c2.skip(1), s1.skip(1), s2.skip(1));
    }
}

/// dot product distributes over sequence concatenation:
/// dot(c_a ++ c_b, s_a ++ s_b) == dot(c_a, s_a) + dot(c_b, s_b)
pub proof fn lemma_dot_product_append(
    c_a: Seq<nat>, c_b: Seq<nat>, s_a: Seq<int>, s_b: Seq<int>,
)
    requires
        c_a.len() == s_a.len(),
        c_b.len() == s_b.len(),
    ensures
        dot_product_nat_int(c_a.add(c_b), s_a.add(s_b))
            == dot_product_nat_int(c_a, s_a) + dot_product_nat_int(c_b, s_b),
    decreases c_a.len(),
{
    if c_a.len() == 0 {
        assert(c_a.add(c_b) =~= c_b);
        assert(s_a.add(s_b) =~= s_b);
    } else {
        let ca_cb = c_a.add(c_b);
        let sa_sb = s_a.add(s_b);
        assert(ca_cb.first() == c_a.first());
        assert(sa_sb.first() == s_a.first());
        assert(ca_cb.skip(1) =~= c_a.skip(1).add(c_b));
        assert(sa_sb.skip(1) =~= s_a.skip(1).add(s_b));

        lemma_dot_product_append(c_a.skip(1), c_b, s_a.skip(1), s_b);
    }
}

/// coords_in_bounds distributes over concatenation.
pub proof fn lemma_coords_in_bounds_concat(
    c_a: Seq<nat>, c_b: Seq<nat>, s_a: Seq<nat>, s_b: Seq<nat>,
)
    requires
        c_a.len() == s_a.len(),
        c_b.len() == s_b.len(),
        coords_in_bounds(c_a, s_a),
        coords_in_bounds(c_b, s_b),
    ensures
        coords_in_bounds(c_a.add(c_b), s_a.add(s_b)),
{
    assert forall|i: int| 0 <= i < c_a.add(c_b).len()
    implies c_a.add(c_b)[i] < s_a.add(s_b)[i] by {
        if i < c_a.len() as int {
        } else {
            let j = (i - c_a.len()) as int;
            assert(c_a.add(c_b)[i] == c_b[j]);
            assert(s_a.add(s_b)[i] == s_b[j]);
        }
    };
}

/// delinearize distributes over shape concatenation:
/// delinearize(x, s_a ++ s_b) =~= delinearize(x % size(s_a), s_a) ++ delinearize(x / size(s_a), s_b)
pub proof fn lemma_delinearize_concat(
    x: nat, s_a: Seq<nat>, s_b: Seq<nat>,
)
    requires
        shape_valid(s_a),
        shape_valid(s_b),
        x < shape_size(s_a) * shape_size(s_b),
    ensures
        delinearize(x, s_a.add(s_b)) =~=
            delinearize(x % shape_size(s_a), s_a).add(
                delinearize(x / shape_size(s_a), s_b)
            ),
{
    let size_a = shape_size(s_a);
    let size_b = shape_size(s_b);
    lemma_shape_size_positive(s_a);
    lemma_shape_size_positive(s_b);

    let x_a = x % size_a;
    let x_b = x / size_a;

    // x_a < size_a, x_b < size_b
    lemma_mod_bound(x, size_a);
    lemma_div_upper_bound(x, size_a, size_b);

    // c_a, c_b are the coordinate vectors
    let c_a = delinearize(x_a, s_a);
    let c_b = delinearize(x_b, s_b);

    // Lengths match
    lemma_delinearize_len(x_a, s_a);
    lemma_delinearize_len(x_b, s_b);

    // In bounds
    lemma_delinearize_bounds(x_a, s_a);
    lemma_delinearize_bounds(x_b, s_b);

    // linearize(c_a, s_a) == x_a (roundtrip)
    lemma_delinearize_roundtrip(x_a, s_a);
    lemma_delinearize_roundtrip(x_b, s_b);

    // linearize(c_a ++ c_b, s_a ++ s_b) == linearize(c_a, s_a) + size_a * linearize(c_b, s_b)
    //                                    == x_a + size_a * x_b
    //                                    == x  (by div_mod identity)
    lemma_linearize_concat(c_a, c_b, s_a, s_b);
    lemma_div_mod_identity(x, size_a);
    // x == x % size_a + size_a * (x / size_a) == x_a + size_a * x_b

    // c_a ++ c_b is in bounds for s_a ++ s_b
    lemma_coords_in_bounds_concat(c_a, c_b, s_a, s_b);

    // shape_valid(s_a ++ s_b)
    assert forall|i: int| 0 <= i < s_a.add(s_b).len()
    implies #[trigger] s_a.add(s_b)[i] > 0 by {
        if i < s_a.len() as int {} else {}
    };

    // shape_size(s_a ++ s_b) == size_a * size_b (by lemma_shape_size_append)
    crate::proof::product_lemmas::lemma_shape_size_append(s_a, s_b);

    // By linearize_roundtrip: delinearize(linearize(c_a++c_b, s_a++s_b), s_a++s_b) =~= c_a ++ c_b
    lemma_linearize_roundtrip(c_a.add(c_b), s_a.add(s_b));
    // And linearize(c_a++c_b, s_a++s_b) == x
    // So delinearize(x, s_a++s_b) =~= c_a ++ c_b
}

// ══════════════════════════════════════════════════════════════
// Zero-index helpers
// ══════════════════════════════════════════════════════════════

/// delinearize(0, shape) is all zeros for a valid shape.
pub proof fn lemma_delinearize_zero(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures
        delinearize(0, shape).len() == shape.len(),
        forall|i: int| 0 <= i < shape.len() ==> #[trigger] delinearize(0nat, shape)[i] == 0nat,
    decreases shape.len(),
{
    lemma_delinearize_len(0, shape);
    if shape.len() == 0 {
    } else {
        // 0 % shape[0] = 0, 0 / shape[0] = 0
        lemma_mod_small(0, shape.first());
        lemma_div_small(0, shape.first());
        assert(delinearize(0nat, shape).first() == 0nat);

        // Recurse on tail
        lemma_delinearize_zero(shape.skip(1));
        assert forall|i: int| 0 <= i < shape.len()
        implies #[trigger] delinearize(0nat, shape)[i] == 0nat by {
            if i == 0 {
            } else {
                assert(delinearize(0nat, shape).skip(1)[i - 1] == delinearize(0nat, shape.skip(1))[i - 1]);
                assert(delinearize(0nat, shape.skip(1))[i - 1] == 0nat);
            }
        };
    }
}

/// Dot product with all-zero coordinates is 0.
pub proof fn lemma_dot_product_zero_coords(coords: Seq<nat>, strides: Seq<int>)
    requires
        coords.len() == strides.len(),
        forall|i: int| 0 <= i < coords.len() ==> #[trigger] coords[i] == 0nat,
    ensures
        dot_product_nat_int(coords, strides) == 0int,
    decreases coords.len(),
{
    if coords.len() == 0 {
    } else {
        assert(coords.first() == 0nat);
        assert forall|i: int| 0 <= i < coords.skip(1).len()
        implies #[trigger] coords.skip(1)[i] == 0nat by {};
        lemma_dot_product_zero_coords(coords.skip(1), strides.skip(1));
    }
}

/// shape_size(shape) >= shape[0] for valid non-empty shape.
pub proof fn lemma_size_at_least_first(shape: Seq<nat>)
    requires shape_valid(shape), shape.len() > 0,
    ensures shape_size(shape) >= shape.first(),
{
    // shape_size(shape) = shape[0] * shape_size(shape.skip(1))
    // shape_size(shape.skip(1)) >= 1 (product of positives)
    lemma_shape_size_positive(shape.skip(1));
    let s0 = shape.first() as int;
    let rest = shape_size(shape.skip(1)) as int;
    // s0 * rest >= s0 * 1 = s0
    vstd::arithmetic::mul::lemma_mul_inequality(1int, rest, s0);
    vstd::arithmetic::mul::lemma_mul_basics(s0);
    vstd::arithmetic::mul::lemma_mul_is_commutative(s0, rest);
}

/// For a valid layout, if x < shape[0], then offset(x) = x * stride[0].
/// Higher coordinates are all zero when the index fits within the first mode.
pub proof fn lemma_offset_within_first_mode(layout: &LayoutSpec, x: nat)
    requires
        layout.valid(),
        layout.shape.len() > 0,
        x < layout.shape.first(),
    ensures
        layout.offset(x) == (x as int) * layout.stride.first(),
{
    // x < shape[0] <= shape_size(shape)
    lemma_size_at_least_first(layout.shape);

    let coords = delinearize(x, layout.shape);
    lemma_delinearize_len(x, layout.shape);

    // coords[0] = x % shape[0] = x
    lemma_mod_small(x, layout.shape.first());
    assert(coords.first() == x);

    // coords.skip(1) = delinearize(x / shape[0], shape.skip(1)) = delinearize(0, shape.skip(1))
    lemma_div_small(x, layout.shape.first());

    // All higher coords are 0
    lemma_delinearize_zero(layout.shape.skip(1));
    let tail = coords.skip(1);
    let strides_tail = layout.stride.skip(1);

    // tail coords are all zero
    assert forall|i: int| 0 <= i < tail.len()
    implies #[trigger] tail[i] == 0nat by {
        assert(tail[i] == delinearize(0nat, layout.shape.skip(1))[i]);
    };

    // dot(tail, strides_tail) = 0
    lemma_dot_product_zero_coords(tail, strides_tail);
    assert(dot_product_nat_int(tail, strides_tail) == 0int);
}

// ══════════════════════════════════════════════════════════════
// Mode swap lemmas
// ══════════════════════════════════════════════════════════════

/// Dot product is invariant under simultaneous adjacent swap.
pub proof fn lemma_dot_product_swap(c: Seq<nat>, s: Seq<int>, i: nat)
    requires
        c.len() == s.len(),
        (i + 1) < c.len(),
    ensures
        dot_product_nat_int(seq_swap(c, i as int), seq_swap(s, i as int))
            == dot_product_nat_int(c, s),
    decreases i,
{
    let cs = seq_swap(c, i as int);
    let ss = seq_swap(s, i as int);

    if i == 0 {
        // Establish skip(1) structure
        assert(cs.skip(1) =~= Seq::new((c.len() - 1) as nat, |j: int|
            if j == 0 { c[0] } else { c[j + 1] }
        ));
        assert(ss.skip(1) =~= Seq::new((s.len() - 1) as nat, |j: int|
            if j == 0 { s[0] } else { s[j + 1] }
        ));
        assert(cs.skip(1).skip(1) =~= c.skip(2));
        assert(ss.skip(1).skip(1) =~= s.skip(2));
        assert(c.skip(1).skip(1) =~= c.skip(2));
        assert(s.skip(1).skip(1) =~= s.skip(2));

        // Step-by-step two-level unfolding of dot(cs, ss)
        let r = dot_product_nat_int(c.skip(2), s.skip(2));

        // Level 1: dot(cs, ss) = cs[0]*ss[0] + dot(cs.skip(1), ss.skip(1))
        let dot_cs_inner = dot_product_nat_int(cs.skip(1), ss.skip(1));
        assert(dot_product_nat_int(cs, ss) ==
            (cs.first() as int) * ss.first() + dot_cs_inner);
        assert(cs.first() == c[1]);
        assert(ss.first() == s[1]);

        // Level 2: dot(cs.skip(1), ss.skip(1)) = first*first + dot(tail, tail)
        assert(dot_cs_inner ==
            (cs.skip(1).first() as int) * ss.skip(1).first()
            + dot_product_nat_int(cs.skip(1).skip(1), ss.skip(1).skip(1)));
        assert(cs.skip(1).first() == c[0]);
        assert(ss.skip(1).first() == s[0]);

        // Step-by-step two-level unfolding of dot(c, s)
        let dot_c_inner = dot_product_nat_int(c.skip(1), s.skip(1));
        assert(dot_product_nat_int(c, s) ==
            (c.first() as int) * s.first() + dot_c_inner);

        assert(dot_c_inner ==
            (c.skip(1).first() as int) * s.skip(1).first()
            + dot_product_nat_int(c.skip(1).skip(1), s.skip(1).skip(1)));
        assert(c.skip(1).first() == c[1]);
        assert(s.skip(1).first() == s[1]);

        // Both tails are equal: dot(c.skip(2), s.skip(2)) == r
    } else {
        // swap at i > 0 doesn't affect first element
        assert(cs.first() == c.first());
        assert(ss.first() == s.first());

        // cs.skip(1) =~= seq_swap(c.skip(1), (i-1) as int)
        assert(cs.skip(1) =~= seq_swap(c.skip(1), (i - 1) as int));
        assert(ss.skip(1) =~= seq_swap(s.skip(1), (i - 1) as int));

        // By IH:
        lemma_dot_product_swap(c.skip(1), s.skip(1), (i - 1) as nat);
    }
}

/// Shape validity preserved under adjacent swap.
pub proof fn lemma_shape_valid_swap(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        (i + 1) < shape.len(),
    ensures
        shape_valid(seq_swap(shape, i as int)),
{
    let s = seq_swap(shape, i as int);
    assert forall|j: int| 0 <= j < s.len() implies #[trigger] s[j] > 0 by {
        if j == i as int {
            assert(s[j] == shape[(i + 1) as int]);
        } else if j == (i + 1) as int {
            assert(s[j] == shape[i as int]);
        } else {
            assert(s[j] == shape[j]);
        }
    };
}

/// Coordinate bounds preserved under swap.
pub proof fn lemma_coords_in_bounds_swap(coords: Seq<nat>, shape: Seq<nat>, i: nat)
    requires
        coords.len() == shape.len(),
        coords_in_bounds(coords, shape),
        (i + 1) < shape.len(),
    ensures
        coords_in_bounds(seq_swap(coords, i as int), seq_swap(shape, i as int)),
{
    let cs = seq_swap(coords, i as int);
    let ss = seq_swap(shape, i as int);
    assert forall|j: int| 0 <= j < cs.len() implies #[trigger] cs[j] < ss[j] by {
        if j == i as int {
            assert(cs[j] == coords[(i + 1) as int]);
            assert(ss[j] == shape[(i + 1) as int]);
        } else if j == (i + 1) as int {
            assert(cs[j] == coords[i as int]);
            assert(ss[j] == shape[i as int]);
        } else {}
    };
}

/// Shape size preserved under adjacent swap.
pub proof fn lemma_shape_size_swap(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        (i + 1) < shape.len(),
    ensures
        shape_size(seq_swap(shape, i as int)) == shape_size(shape),
    decreases i,
{
    let s = seq_swap(shape, i as int);
    if i == 0 {
        // Establish skip structure
        assert(s.skip(1) =~= Seq::new((shape.len() - 1) as nat, |j: int|
            if j == 0 { shape[0] } else { shape[j + 1] }
        ));
        assert(s.skip(1).skip(1) =~= shape.skip(2));
        assert(shape.skip(1).skip(1) =~= shape.skip(2));

        // Two-level unfolding of shape_size(s)
        let r = shape_size(shape.skip(2));
        assert(shape_size(s) == s.first() * shape_size(s.skip(1)));
        assert(s.first() == shape[1]);
        assert(s.skip(1).first() == shape[0]);
        assert(shape_size(s.skip(1)) == shape[0] * r);
        // So shape_size(s) == shape[1] * (shape[0] * r)

        // Two-level unfolding of shape_size(shape)
        assert(shape_size(shape) == shape.first() * shape_size(shape.skip(1)));
        assert(shape.skip(1).first() == shape[1]);
        assert(shape_size(shape.skip(1)) == shape[1] * r);
        // So shape_size(shape) == shape[0] * (shape[1] * r)

        // b * (a * r) == a * (b * r) by int arithmetic
        let a = shape[0] as int;
        let b = shape[1] as int;
        let ri = r as int;
        vstd::arithmetic::mul::lemma_mul_is_associative(b, a, ri);
        vstd::arithmetic::mul::lemma_mul_is_commutative(b, a);
        vstd::arithmetic::mul::lemma_mul_is_associative(a, b, ri);
    } else {
        // Swap at i > 0 doesn't affect first element
        assert(s.first() == shape.first());
        assert(s.skip(1) =~= seq_swap(shape.skip(1), (i - 1) as int));
        lemma_shape_size_swap(shape.skip(1), (i - 1) as nat);
    }
}

/// For each offset of the swapped layout, there's a matching offset in the original.
pub proof fn lemma_layout_swap_offset_witness(layout: &LayoutSpec, i: nat, y: nat)
    requires
        layout.valid(),
        (i + 1) < layout.shape.len(),
        ({
            let s = LayoutSpec {
                shape: seq_swap(layout.shape, i as int),
                stride: seq_swap(layout.stride, i as int),
            };
            y < shape_size(s.shape)
        }),
    ensures ({
        let s = LayoutSpec {
            shape: seq_swap(layout.shape, i as int),
            stride: seq_swap(layout.stride, i as int),
        };
        s.offset_hit(s.offset(y))
        &&
        exists|x: nat| x < layout.size() && #[trigger] layout.offset(x) == s.offset(y)
    }),
{
    let sl = LayoutSpec {
        shape: seq_swap(layout.shape, i as int),
        stride: seq_swap(layout.stride, i as int),
    };
    lemma_shape_valid_swap(layout.shape, i);
    lemma_shape_size_swap(layout.shape, i);

    let coords_s = delinearize(y, sl.shape);
    lemma_delinearize_len(y, sl.shape);
    lemma_delinearize_bounds(y, sl.shape);

    // Un-swap coordinates: coords_l = swap(coords_s, i)
    let coords_l = seq_swap(coords_s, i as int);

    // coords_l is in bounds for layout.shape
    lemma_coords_in_bounds_swap(coords_s, sl.shape, i);
    // swap(swap(shape, i), i) =~= shape
    assert(seq_swap(sl.shape, i as int) =~= layout.shape);
    assert(seq_swap(sl.stride, i as int) =~= layout.stride);

    let x = linearize(coords_l, layout.shape);
    lemma_linearize_bound(coords_l, layout.shape);

    // layout.offset(x) = dot(delinearize(x, shape), stride)
    // By linearize_roundtrip: delinearize(linearize(coords_l, shape), shape) =~= coords_l
    lemma_linearize_roundtrip(coords_l, layout.shape);

    // Chain: layout.offset(x) = dot(delinearize(x, shape), stride)
    //      = dot(coords_l, stride)  [ext: delinearize(x, shape) =~= coords_l, stride =~= stride]
    lemma_dot_product_ext(
        delinearize(x, layout.shape), coords_l,
        layout.stride, layout.stride,
    );

    // dot(coords_l, stride) = dot(swap(coords_s,i), swap(sl.stride,i))  [ext: stride =~= swap(sl.stride,i)]
    lemma_dot_product_ext(
        coords_l, coords_l,
        layout.stride, seq_swap(sl.stride, i as int),
    );

    // dot(swap(coords_s,i), swap(sl.stride,i)) = dot(coords_s, sl.stride)  [swap lemma]
    lemma_dot_product_swap(coords_s, sl.stride, i);

    // Close the chain explicitly
    assert(layout.offset(x)
        == dot_product_nat_int(delinearize(x, layout.shape), layout.stride));
    assert(dot_product_nat_int(delinearize(x, layout.shape), layout.stride)
        == dot_product_nat_int(coords_l, layout.stride));
    assert(dot_product_nat_int(coords_l, layout.stride)
        == dot_product_nat_int(coords_l, seq_swap(sl.stride, i as int)));
    assert(dot_product_nat_int(seq_swap(coords_s, i as int), seq_swap(sl.stride, i as int))
        == dot_product_nat_int(coords_s, sl.stride));
    assert(sl.offset(y)
        == dot_product_nat_int(delinearize(y, sl.shape), sl.stride));
    assert(layout.offset(x) == sl.offset(y));

    // Witness for offset_hit: y itself
    assert(y < shape_size(sl.shape) && sl.offset(y) == sl.offset(y));
}

/// Helper: construct the offset chain from original layout to swapped layout.
/// Given x < layout.size(), produces y < swapped.size() with swapped.offset(y) == layout.offset(x).
proof fn swap_offset_reverse_witness(layout: &LayoutSpec, i: nat, x: nat)
    requires
        layout.valid(),
        (i + 1) < layout.shape.len(),
        x < layout.size(),
    ensures ({
        let sl = LayoutSpec {
            shape: seq_swap(layout.shape, i as int),
            stride: seq_swap(layout.stride, i as int),
        };
        exists|y: nat| y < shape_size(sl.shape) && #[trigger] sl.offset(y) == layout.offset(x)
    }),
{
    let sl = LayoutSpec {
        shape: seq_swap(layout.shape, i as int),
        stride: seq_swap(layout.stride, i as int),
    };
    lemma_shape_valid_swap(layout.shape, i);
    lemma_shape_size_swap(layout.shape, i);

    let coords_x = delinearize(x, layout.shape);
    lemma_delinearize_len(x, layout.shape);
    lemma_delinearize_bounds(x, layout.shape);

    // Swap to get coords in swapped layout's shape
    let coords_y = seq_swap(coords_x, i as int);
    lemma_coords_in_bounds_swap(coords_x, layout.shape, i);
    // swap(swap(shape, i), i) =~= shape, so coords_y is in bounds for sl.shape

    let y = linearize(coords_y, sl.shape);
    lemma_linearize_bound(coords_y, sl.shape);

    // sl.offset(y) = dot(delinearize(y, sl.shape), sl.stride)
    lemma_linearize_roundtrip(coords_y, sl.shape);
    // delinearize(y, sl.shape) =~= coords_y

    // dot(coords_y, sl.stride) = dot(swap(coords_x, i), swap(layout.stride, i))
    //                           = dot(coords_x, layout.stride) [by swap]
    lemma_dot_product_swap(coords_x, layout.stride, i);

    // Bridge =~= through dot_product
    lemma_dot_product_ext(
        delinearize(y, sl.shape), coords_y,
        sl.stride, sl.stride,
    );
    lemma_dot_product_ext(
        delinearize(x, layout.shape), coords_x,
        layout.stride, layout.stride,
    );

    assert(sl.offset(y) == dot_product_nat_int(coords_y, sl.stride));
    assert(dot_product_nat_int(coords_y, sl.stride)
        == dot_product_nat_int(seq_swap(coords_x, i as int), seq_swap(layout.stride, i as int)));
    assert(dot_product_nat_int(coords_x, layout.stride) == layout.offset(x));
    assert(sl.offset(y) == layout.offset(x));
}

/// Swapping adjacent modes preserves surjectivity.
pub proof fn lemma_swap_preserves_surjective(layout: &LayoutSpec, i: nat, m: nat)
    requires
        layout.valid(),
        (i + 1) < layout.shape.len(),
        layout.is_surjective_upto(m),
    ensures ({
        let s = LayoutSpec {
            shape: seq_swap(layout.shape, i as int),
            stride: seq_swap(layout.stride, i as int),
        };
        s.is_surjective_upto(m)
    }),
{
    let sl = LayoutSpec {
        shape: seq_swap(layout.shape, i as int),
        stride: seq_swap(layout.stride, i as int),
    };
    lemma_shape_valid_swap(layout.shape, i);
    lemma_shape_size_swap(layout.shape, i);

    assert forall|k: int| 0 <= k < m as int implies #[trigger] sl.offset_hit(k) by {
        // layout is surjective, so exists x with layout.offset(x) == k
        assert(layout.offset_hit(k));
        let x: nat = choose|x: nat| x < layout.size() && layout.offset(x) == k;
        swap_offset_reverse_witness(layout, i, x);
    };
}

/// Helper: for y < swapped.size(), shows swapped.offset(y) == layout.offset(x)
/// where x = linearize(swap(delinearize(y, swapped.shape), i), layout.shape).
proof fn swap_offset_chain(layout: &LayoutSpec, i: nat, y: nat) -> (x: nat)
    requires
        layout.valid(),
        (i + 1) < layout.shape.len(),
        shape_valid(seq_swap(layout.shape, i as int)),
        y < shape_size(seq_swap(layout.shape, i as int)),
    ensures ({
        let sl = LayoutSpec {
            shape: seq_swap(layout.shape, i as int),
            stride: seq_swap(layout.stride, i as int),
        };
        &&& x < layout.size()
        &&& sl.offset(y) == layout.offset(x)
        &&& x == linearize(
                seq_swap(delinearize(y, sl.shape), i as int),
                layout.shape,
            )
    }),
{
    let sl = LayoutSpec {
        shape: seq_swap(layout.shape, i as int),
        stride: seq_swap(layout.stride, i as int),
    };
    lemma_shape_size_swap(layout.shape, i);

    let coords_y = delinearize(y, sl.shape);
    lemma_delinearize_len(y, sl.shape);
    lemma_delinearize_bounds(y, sl.shape);

    let coords_x = seq_swap(coords_y, i as int);
    lemma_coords_in_bounds_swap(coords_y, sl.shape, i);

    let x = linearize(coords_x, layout.shape);
    lemma_linearize_bound(coords_x, layout.shape);
    lemma_linearize_roundtrip(coords_x, layout.shape);

    // sl.offset(y) = dot(delinearize(y, sl.shape), sl.stride)
    //              = dot(coords_y, sl.stride)
    lemma_dot_product_ext(delinearize(y, sl.shape), coords_y, sl.stride, sl.stride);

    // dot(coords_y, sl.stride) = dot(swap(coords_y,i), swap(sl.stride,i))
    //                           = dot(coords_x, swap(sl.stride,i))
    lemma_dot_product_swap(coords_y, sl.stride, i);

    // swap(sl.stride, i) = swap(swap(layout.stride, i), i) =~= layout.stride
    assert(seq_swap(sl.stride, i as int) =~= layout.stride);
    lemma_dot_product_ext(
        coords_x, coords_x,
        seq_swap(sl.stride, i as int), layout.stride,
    );

    // layout.offset(x) = dot(delinearize(x, shape), stride) = dot(coords_x, stride)
    lemma_dot_product_ext(delinearize(x, layout.shape), coords_x, layout.stride, layout.stride);

    assert(sl.offset(y) == layout.offset(x));

    x
}

/// Swapping adjacent modes preserves injectivity.
pub proof fn lemma_swap_preserves_injective(layout: &LayoutSpec, i: nat)
    requires
        layout.valid(),
        (i + 1) < layout.shape.len(),
        layout.is_injective(),
    ensures ({
        let s = LayoutSpec {
            shape: seq_swap(layout.shape, i as int),
            stride: seq_swap(layout.stride, i as int),
        };
        s.is_injective()
    }),
{
    let sl = LayoutSpec {
        shape: seq_swap(layout.shape, i as int),
        stride: seq_swap(layout.stride, i as int),
    };
    lemma_shape_valid_swap(layout.shape, i);
    lemma_shape_size_swap(layout.shape, i);

    assert forall|y1: nat, y2: nat|
        y1 < shape_size(sl.shape) && y2 < shape_size(sl.shape) && y1 != y2
    implies
        #[trigger] sl.offset(y1) != #[trigger] sl.offset(y2)
    by {
        let x1 = swap_offset_chain(layout, i, y1);
        let x2 = swap_offset_chain(layout, i, y2);
        // sl.offset(y1) == layout.offset(x1), sl.offset(y2) == layout.offset(x2)

        // Show x1 != x2 from y1 != y2 (contrapositive)
        // We know x1 == linearize(swap(delinearize(y1, sl.shape), i), layout.shape)
        // and     x2 == linearize(swap(delinearize(y2, sl.shape), i), layout.shape)
        if x1 == x2 {
            // x1 == x2 means linearize(swap(delin(y1),i), shape) == linearize(swap(delin(y2),i), shape)
            // By linearize_roundtrip: delinearize(x1, shape) =~= swap(delin(y1), i)
            let cy1 = delinearize(y1, sl.shape);
            let cy2 = delinearize(y2, sl.shape);
            lemma_delinearize_len(y1, sl.shape);
            lemma_delinearize_len(y2, sl.shape);
            lemma_delinearize_bounds(y1, sl.shape);
            lemma_delinearize_bounds(y2, sl.shape);
            lemma_coords_in_bounds_swap(cy1, sl.shape, i);
            lemma_coords_in_bounds_swap(cy2, sl.shape, i);

            lemma_linearize_roundtrip(seq_swap(cy1, i as int), layout.shape);
            lemma_linearize_roundtrip(seq_swap(cy2, i as int), layout.shape);
            // delinearize(x1, shape) =~= swap(cy1, i) and =~= swap(cy2, i) (since x1==x2)
            assert(seq_swap(cy1, i as int) =~= seq_swap(cy2, i as int));
            // Derive cy1 =~= cy2 from swap(cy1,i) =~= swap(cy2,i)
            // Use double-swap involution
            assert(seq_swap(seq_swap(cy1, i as int), i as int) =~= cy1);
            assert(seq_swap(seq_swap(cy2, i as int), i as int) =~= cy2);
            // Since swap(cy1,i) =~= swap(cy2,i), need swap applied to =~= args gives =~= result
            // Z3 can see: if a =~= b then Seq::new(a.len(), f(a)) =~= Seq::new(b.len(), f(b)) pointwise
            // But seq_swap reads from its argument, so we need to bridge explicitly
            let swapped = seq_swap(cy1, i as int); // == seq_swap(cy2, i as int) by =~=
            assert(seq_swap(swapped, i as int) =~= cy1);
            assert(seq_swap(swapped, i as int) =~= cy2);
            // linearize(cy1, sl.shape) == linearize(cy2, sl.shape)
            lemma_delinearize_roundtrip(y1, sl.shape);
            lemma_delinearize_roundtrip(y2, sl.shape);
            // y1 == y2 — contradiction
        }
    };
}

} // verus!
