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

} // verus!
