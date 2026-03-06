use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

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
        // Fallback: general composition (defined operationally for now)
        // Will be extended as we prove more cases
        LayoutSpec {
            shape: seq![b_shape],
            stride: seq![(b_stride as int) * a.stride.first()],
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
