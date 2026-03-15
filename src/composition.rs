use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::inverse::shape_prefix_products;

verus! {

/// Find the split point: mode i where b_stride == prefix_product(a.shape, i).
/// Returns Some(i) if such a mode exists, None otherwise.
pub open spec fn find_split_mode(a: &LayoutSpec, b_stride: nat) -> Option<nat>
    decreases a.shape.len(),
{
    let pp = shape_prefix_products(a.shape);
    // Search through prefix products for a match
    find_pp_index(pp, b_stride, 0)
}

/// Helper: find index i in pp (starting from pos) where pp[i] == target.
pub open spec fn find_pp_index(pp: Seq<nat>, target: nat, pos: nat) -> Option<nat>
    decreases pp.len() - pos,
{
    if pos >= pp.len() {
        None
    } else if pp[pos as int] == target {
        Some(pos)
    } else {
        find_pp_index(pp, target, pos + 1)
    }
}

/// Compose two single-mode layouts: A = (M):(d) and B = (N):(r).
/// Result: (N):(r*d), meaning A(B(x)) = A(r*x) = (r*x mod M)*d = x*(r*d) when r*N <= M.
///
/// Precondition: r * N <= M (B's codomain fits within A's domain).
/// This is the "trivial" case where B maps into a single mode of A without crossing mode boundaries.
pub open spec fn compose_1d(a_shape: nat, a_stride: int, b_shape: nat, b_stride: int) -> LayoutSpec
    recommends a_shape > 0, b_shape > 0, b_stride * (b_shape as int) <= (a_shape as int),
{
    LayoutSpec {
        shape: seq![b_shape],
        stride: seq![b_stride * a_stride],
    }
}

/// Compose a multi-mode A with a single-mode B = (N):(r).
///
/// This is the general single-mode composition. B's stride r determines a "split point"
/// in A's modes -- the mode i where r "lands" after consuming modes 0..i-1.
///
/// For now, we define the simple case where B's stride is 1 (selecting the first N elements
/// of A's linearized domain) and the general stride case.
///
/// When r == 1 and N <= A.shape[0]: result is (N):(A.stride[0]).
/// When r == A.shape[0] and N <= A.shape[1]: result is (N):(A.stride[1]).
/// General: r = product(A.shape[0..i]) * c where c divides A.shape[i].
pub open spec fn compose_single_mode(a: LayoutSpec, b_shape: nat, b_stride: nat) -> LayoutSpec
    recommends a.valid(), b_shape > 0,
{
    // For the stride-1 case: select first b_shape elements from A's fastest mode
    if b_stride == 1 && b_shape <= a.shape.first() && a.shape.len() > 0 {
        LayoutSpec {
            shape: seq![b_shape],
            stride: seq![a.stride.first()],
        }
    } else {
        // Fallback: general composition
        LayoutSpec {
            shape: seq![b_shape],
            stride: seq![(b_stride as int) * a.stride.first()],
        }
    }
}

/// Extended single-mode composition using prefix-product decomposition.
///
/// When B's stride matches a prefix product of A's shape (i.e., b_stride == product(A.shape[0..i])),
/// the result uses A's stride at mode i rather than the naive b_stride * a.stride[0].
/// This is correct for general (non-column-major) layouts and matches CuTe's actual behavior.
///
/// Falls back to compose_single_mode when no split point is found.
pub open spec fn compose_single_mode_extended(a: LayoutSpec, b_shape: nat, b_stride: nat) -> LayoutSpec
    recommends a.valid(), b_shape > 0,
{
    if b_stride == 1 && b_shape <= a.shape.first() && a.shape.len() > 0 {
        LayoutSpec {
            shape: seq![b_shape],
            stride: seq![a.stride.first()],
        }
    } else {
        match find_split_mode(&a, b_stride) {
            Some(idx) => {
                if idx < a.shape.len() && b_shape <= a.shape[idx as int] {
                    LayoutSpec {
                        shape: seq![b_shape],
                        stride: seq![a.stride[idx as int]],
                    }
                } else {
                    LayoutSpec {
                        shape: seq![b_shape],
                        stride: seq![(b_stride as int) * a.stride.first()],
                    }
                }
            }
            None => {
                LayoutSpec {
                    shape: seq![b_shape],
                    stride: seq![(b_stride as int) * a.stride.first()],
                }
            }
        }
    }
}

/// Extended multi-mode composition using prefix-product decomposition.
pub open spec fn compose_extended(a: LayoutSpec, b: LayoutSpec) -> LayoutSpec
    recommends a.valid(), b.valid(),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
        LayoutSpec { shape: seq![], stride: seq![] }
    } else if b.shape.len() == 1 {
        compose_single_mode_extended(a, b.shape.first(), b.stride.first() as nat)
    } else {
        let first = compose_single_mode_extended(a, b.shape.first(), b.stride.first() as nat);
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        let rest = compose_extended(a, rest_b);
        LayoutSpec {
            shape: first.shape.add(rest.shape),
            stride: first.stride.add(rest.stride),
        }
    }
}

/// Multi-mode composition: distributes over B's modes.
/// A compose (B_0, B_1, ..., B_k) = (A compose B_0, A compose B_1, ..., A compose B_k)
///
/// Each B_i is a single-mode layout. The results are concatenated.
pub open spec fn compose(a: LayoutSpec, b: LayoutSpec) -> LayoutSpec
    recommends a.valid(), b.valid(),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
        LayoutSpec { shape: seq![], stride: seq![] }
    } else if b.shape.len() == 1 {
        compose_single_mode(a, b.shape.first(), b.stride.first() as nat)
    } else {
        // Compose A with first mode of B, then recurse
        let first = compose_single_mode(a, b.shape.first(), b.stride.first() as nat);
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        let rest = compose(a, rest_b);
        LayoutSpec {
            shape: first.shape.add(rest.shape),
            stride: first.stride.add(rest.stride),
        }
    }
}

} // verus!
