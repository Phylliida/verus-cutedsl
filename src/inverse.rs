use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::coalesce::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Helper functions
// ══════════════════════════════════════════════════════════════

/// Prefix products of a shape: [1, M_0, M_0*M_1, ..., M_0*...*M_{k-1}].
/// Length is shape.len() + 1.
pub open spec fn shape_prefix_products(shape: Seq<nat>) -> Seq<nat>
    decreases shape.len(),
{
    if shape.len() == 0 {
        seq![1nat]
    } else {
        let rest_pp = shape_prefix_products(shape.skip(1));
        // rest_pp = [1, M_1, M_1*M_2, ...]
        // We want [1, M_0, M_0*M_1, M_0*M_1*M_2, ...]
        // = [1] ++ [M_0 * x for x in rest_pp]
        let scaled = Seq::new(rest_pp.len(), |i: int| shape.first() * rest_pp[i]);
        seq![1nat].add(scaled)
    }
}

/// Find the index of the first element equal to target, or -1 if not found.
pub open spec fn find_value(s: Seq<int>, target: int) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        -1
    } else if s.first() == target {
        0
    } else {
        let rest = find_value(s.skip(1), target);
        if rest < 0 { -1int } else { rest + 1 }
    }
}

/// Remove element at position i from a nat sequence.
pub open spec fn remove_at_nat(s: Seq<nat>, i: int) -> Seq<nat> {
    s.take(i).add(s.skip(i + 1))
}

/// Remove element at position i from an int sequence.
pub open spec fn remove_at_int(s: Seq<int>, i: int) -> Seq<int> {
    s.take(i).add(s.skip(i + 1))
}

/// Build coordinates that "undo" right_inverse_build's offset.
///
/// For each step of the build (finding stride == cursor), the coordinate at that
/// position is j % shape[idx], and the remaining coordinates come from the recursive
/// call with j / shape[idx].
pub open spec fn right_inverse_coords(
    shape: Seq<nat>, stride: Seq<int>, cursor: nat, j: nat,
) -> Seq<nat>
    recommends
        shape.len() == stride.len(),
        shape_valid(shape),
        cursor > 0,
    decreases shape.len(),
{
    if shape.len() == 0 {
        seq![]
    } else {
        let idx = find_value(stride, cursor as int);
        if idx < 0 || idx >= shape.len() as int {
            Seq::new(shape.len(), |_i: int| 0nat)
        } else {
            let m = shape[idx];
            let j0 = j % m;
            let j1 = j / m;
            let rest = right_inverse_coords(
                remove_at_nat(shape, idx),
                remove_at_int(stride, idx),
                m * cursor, j1,
            );
            Seq::new(shape.len(), |k: int|
                if k == idx { j0 }
                else if k < idx { rest[k] }
                else { rest[(k - 1) as int] }
            )
        }
    }
}

/// Find the index of the element with smallest positive value, or -1 if none.
pub open spec fn find_min_positive(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        -1int
    } else {
        let rest_idx = find_min_positive(s.skip(1));
        if s.first() > 0 {
            if rest_idx < 0 {
                0
            } else if s.first() <= s[rest_idx + 1] {
                0
            } else {
                rest_idx + 1
            }
        } else {
            if rest_idx < 0 { -1int } else { rest_idx + 1 }
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Right inverse
// ══════════════════════════════════════════════════════════════

/// If find_value returns a non-negative index, it's within bounds.
pub open spec fn find_value_in_bounds(s: Seq<int>, target: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        true
    } else if s.first() == target {
        true
    } else {
        find_value_in_bounds(s.skip(1), target)
    }
}

/// Core right_inverse builder.
///
/// Processes modes by finding stride == cursor (contiguous chain from 1).
/// Each matched mode gets:
/// - shape: the mode's original shape
/// - stride: the prefix product at the mode's original position
///
/// The result has column-major-like strides permuted by the stride sort.
pub open spec fn right_inverse_build(
    shape: Seq<nat>,
    stride: Seq<int>,
    preprod: Seq<nat>,
    cursor: nat,
) -> LayoutSpec
    recommends
        shape.len() == stride.len(),
        shape.len() == preprod.len(),
    decreases shape.len(),
{
    if shape.len() == 0 {
        LayoutSpec { shape: seq![], stride: seq![] }
    } else {
        let idx = find_value(stride, cursor as int);
        if idx < 0 || idx >= shape.len() as int {
            // No mode with matching stride; chain broken
            LayoutSpec { shape: seq![], stride: seq![] }
        } else {
            let m = shape[idx];
            let pp = preprod[idx];
            let next_cursor = m * cursor;
            let rest = right_inverse_build(
                remove_at_nat(shape, idx),
                remove_at_int(stride, idx),
                remove_at_nat(preprod, idx),
                next_cursor,
            );
            LayoutSpec {
                shape: seq![m].add(rest.shape),
                stride: seq![pp as int].add(rest.stride),
            }
        }
    }
}

/// Right inverse of a layout.
///
/// Given layout L, right_inverse(L) = R such that L(R(j)) = j
/// for j in [0, R.size()).
///
/// Algorithm: coalesce L, compute prefix products of shape,
/// then build the inverse by walking modes in stride order.
/// Each mode with stride matching the expected cursor gets
/// column-major strides at its original position.
pub open spec fn right_inverse(layout: &LayoutSpec) -> LayoutSpec {
    let c = coalesce(*layout);
    let pp = shape_prefix_products(c.shape);
    // pp[i] = product(shape[0..i]), has length shape.len() + 1
    // preprod for mode i = pp[i]
    let preprod = pp.take(c.shape.len() as int);
    right_inverse_build(c.shape, c.stride, preprod, 1)
}

// ══════════════════════════════════════════════════════════════
// Left inverse
// ══════════════════════════════════════════════════════════════

/// Core left_inverse builder.
///
/// Processes modes by finding the smallest positive stride.
/// Each mode produces:
/// - A "gap" shape = stride / acc_size (fills codomain gaps)
/// - A stride = prefix product at original position
/// The last mode also appends its shape as the final mode.
///
/// Result stride has an implicit leading 0 (added by left_inverse).
pub open spec fn left_inverse_build(
    shape: Seq<nat>,
    stride: Seq<int>,
    preprod: Seq<nat>,
    acc_size: nat,
) -> LayoutSpec
    recommends
        shape.len() == stride.len(),
        shape.len() == preprod.len(),
    decreases shape.len(),
{
    if shape.len() == 0 {
        LayoutSpec { shape: seq![], stride: seq![] }
    } else {
        let idx = find_min_positive(stride);
        if idx < 0 || idx >= shape.len() as int {
            // No positive-stride modes left
            LayoutSpec { shape: seq![], stride: seq![] }
        } else {
            let d = stride[idx] as nat;
            let m = shape[idx];
            let pp = preprod[idx];
            let gap = d / acc_size;

            let rest_shape = remove_at_nat(shape, idx);
            let rest_stride = remove_at_int(stride, idx);
            let rest_preprod = remove_at_nat(preprod, idx);

            if shape.len() == 1 {
                // Last mode: emit gap and final shape
                LayoutSpec {
                    shape: seq![gap, m],
                    stride: seq![pp as int],
                }
            } else {
                let rest = left_inverse_build(
                    rest_shape, rest_stride, rest_preprod,
                    acc_size * gap,
                );
                LayoutSpec {
                    shape: seq![gap].add(rest.shape),
                    stride: seq![pp as int].add(rest.stride),
                }
            }
        }
    }
}

/// Left inverse of a layout.
///
/// Given layout L, left_inverse(L) = LI such that LI(L(i)) = i
/// for i in [0, L.size()).
///
/// Algorithm: coalesce L, compute prefix products, then build
/// the inverse with gap-filling modes (stride 0) and data modes.
pub open spec fn left_inverse(layout: &LayoutSpec) -> LayoutSpec {
    let c = coalesce(*layout);
    let pp = shape_prefix_products(c.shape);
    let preprod = pp.take(c.shape.len() as int);
    let raw = left_inverse_build(c.shape, c.stride, preprod, 1);
    // Prepend the initial stride-0 gap mode, then coalesce
    let result = LayoutSpec {
        shape: raw.shape,
        stride: seq![0int].add(raw.stride),
    };
    coalesce(result)
}

// ══════════════════════════════════════════════════════════════
// Admissibility predicates
// ══════════════════════════════════════════════════════════════

/// Admissibility for right_inverse: layout must be valid.
/// The result is always well-defined; it just may be partial
/// (only inverts the contiguous-stride portion).
pub open spec fn right_inverse_admissible(layout: &LayoutSpec) -> bool {
    layout.valid()
}

/// Admissibility for left_inverse: layout must be valid and injective.
pub open spec fn left_inverse_admissible(layout: &LayoutSpec) -> bool {
    &&& layout.valid()
    &&& layout.is_injective()
}

} // verus!
