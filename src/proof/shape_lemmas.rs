use vstd::prelude::*;
use crate::shape::*;
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

} // verus!
