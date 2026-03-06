use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::composition::*;
use crate::proof::shape_lemmas::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Key helper: 1D layout offset is just multiplication
// ══════════════════════════════════════════════════════════════

/// For a 1D layout (M):(d), offset(x) = x * d when x < M.
pub proof fn lemma_1d_offset(m: nat, d: int, x: nat)
    requires m > 0, x < m,
    ensures ({
        let layout = LayoutSpec { shape: seq![m], stride: seq![d] };
        layout.offset(x) == (x as int) * d
    }),
{
    let layout = LayoutSpec { shape: seq![m], stride: seq![d] };
    // delinearize(x, seq![m]) = seq![x % m] ++ delinearize(x / m, seq![])
    //                         = seq![x % m] ++ seq![]
    //                         = seq![x]  (since x < m)
    lemma_mod_small(x, m);
    assert(delinearize(x, seq![m]).first() == x % m);
    assert(x % m == x);
    assert(seq![m].skip(1) =~= Seq::<nat>::empty());
    assert(delinearize(x / m, Seq::<nat>::empty()) =~= Seq::<nat>::empty());

    // Build coords explicitly
    let coords = delinearize(x, layout.shape);
    assert(coords.first() == x);
    assert(coords.skip(1) =~= Seq::<nat>::empty());
    assert(coords.len() == 1) by { lemma_delinearize_len(x, layout.shape); };

    // dot(coords, stride) = x * d + dot(empty, empty) = x * d
    assert(dot_product_nat_int(coords, layout.stride)
        == (coords.first() as int) * layout.stride.first()
           + dot_product_nat_int(coords.skip(1), layout.stride.skip(1)));
    assert(layout.stride.skip(1) =~= Seq::<int>::empty());
    assert(layout.stride.first() == d);
}

// ══════════════════════════════════════════════════════════════
// 1D compose 1D: base case
// ══════════════════════════════════════════════════════════════

/// Composing A=(M):(d) with B=(N):(r): result is (N):(r*d), and
/// result.offset(x) == A.offset(B.offset(x)).
pub proof fn lemma_compose_1d_correct(
    a_shape: nat, a_stride: int, b_shape: nat, b_stride: int, x: nat
)
    requires
        a_shape > 0,
        b_shape > 0,
        b_stride >= 0,
        x < b_shape,
        b_stride * (b_shape as int) <= (a_shape as int),
    ensures ({
        let result = compose_1d(a_shape, a_stride, b_shape, b_stride);
        let a = LayoutSpec { shape: seq![a_shape], stride: seq![a_stride] };
        let b = LayoutSpec { shape: seq![b_shape], stride: seq![b_stride] };
        &&& result.valid()
        &&& result.offset(x) == a.offset(b.offset(x) as nat)
    }),
{
    let result = compose_1d(a_shape, a_stride, b_shape, b_stride);
    let a = LayoutSpec { shape: seq![a_shape], stride: seq![a_stride] };
    let b = LayoutSpec { shape: seq![b_shape], stride: seq![b_stride] };

    assert(result.valid()) by { assert(result.shape[0] > 0); };

    // result.offset(x) = x * (b_stride * a_stride)
    lemma_1d_offset(b_shape, b_stride * a_stride, x);

    // b.offset(x) = x * b_stride
    lemma_1d_offset(b_shape, b_stride, x);
    let bx = (x as int) * b_stride;
    assert(b.offset(x) == bx);

    // bx >= 0 and bx < a_shape
    lemma_mul_nonneg(x as int, b_stride);
    assert(bx >= 0);
    // x * b_stride < b_shape * b_stride <= a_shape
    if b_stride == 0 {
        vstd::arithmetic::mul::lemma_mul_basics(x as int);
        assert(bx == 0);
    } else {
        vstd::arithmetic::mul::lemma_mul_strict_inequality(x as int, b_shape as int, b_stride);
        vstd::arithmetic::mul::lemma_mul_is_commutative(b_shape as int, b_stride);
    }
    assert(bx < a_shape as int);

    // a.offset(bx) = bx * a_stride = (x * b_stride) * a_stride
    lemma_1d_offset(a_shape, a_stride, bx as nat);

    // x * (b_stride * a_stride) == (x * b_stride) * a_stride
    vstd::arithmetic::mul::lemma_mul_is_associative(x as int, b_stride, a_stride);
}

// ══════════════════════════════════════════════════════════════
// Stride-1 composition: multi-mode A compose (N):(1)
// ══════════════════════════════════════════════════════════════

/// Composing multi-mode A with (N):(1) where N <= A.shape[0] gives (N):(A.stride[0]).
/// Selects the first N elements from A's fastest-varying mode.
pub proof fn lemma_compose_stride1_correct(a: LayoutSpec, n: nat, x: nat)
    requires
        a.valid(),
        a.rank() > 0,
        0 < n <= a.shape.first(),
        x < n,
    ensures ({
        let result = compose_single_mode(a, n, 1);
        let b = LayoutSpec { shape: seq![n], stride: seq![1int] };
        &&& result.valid()
        &&& result.offset(x) == a.offset(b.offset(x) as nat)
    }),
{
    let result = compose_single_mode(a, n, 1);
    let b = LayoutSpec { shape: seq![n], stride: seq![1int] };

    // result = (n):(a.stride[0])
    assert(result.valid()) by { assert(result.shape[0] > 0); };

    // result.offset(x) = x * a.stride[0]
    lemma_1d_offset(n, a.stride.first(), x);

    // b.offset(x) = x * 1 = x
    lemma_1d_offset(n, 1int, x);
    assert(b.offset(x) == x as int);

    // a.offset(x): need to show this equals x * a.stride[0]
    // Since x < n <= a.shape[0], delinearize(x, a.shape)[0] = x, rest are 0
    assert(x < a.shape.first());
    lemma_mod_small(x, a.shape.first());
    lemma_div_small(x, a.shape.first());

    // delinearize(x, a.shape) = seq![x] ++ delinearize(0, a.shape.skip(1))
    // dot = x * a.stride[0] + dot(delinearize(0, a.shape.skip(1)), a.stride.skip(1))
    //     = x * a.stride[0] + 0
    lemma_delinearize_zero_dot(a.shape.skip(1), a.stride.skip(1));

    // Expand the dot product
    let coords = delinearize(x, a.shape);
    assert(coords.first() == x);
    assert(coords.skip(1) =~= delinearize(0, a.shape.skip(1)));

    assert(a.offset(x) == dot_product_nat_int(coords, a.stride));
    assert(dot_product_nat_int(coords, a.stride) ==
        (x as int) * a.stride.first()
        + dot_product_nat_int(coords.skip(1), a.stride.skip(1)));
    assert(dot_product_nat_int(coords.skip(1), a.stride.skip(1)) == 0);
}

/// When delinearizing 0, all coordinates are 0 and the dot product is 0.
proof fn lemma_delinearize_zero_dot(shape: Seq<nat>, stride: Seq<int>)
    requires
        shape_valid(shape),
        shape.len() == stride.len(),
    ensures
        dot_product_nat_int(delinearize(0, shape), stride) == 0,
    decreases shape.len(),
{
    if shape.len() > 0 {
        assert(0nat % shape.first() == 0);
        assert(0nat / shape.first() == 0);
        lemma_delinearize_zero_dot(shape.skip(1), stride.skip(1));

        // Unfold: dot(delinearize(0, shape), stride)
        //   = (0 % shape[0]) * stride[0] + dot(delinearize(0, shape.skip(1)), stride.skip(1))
        //   = 0 * stride[0] + 0
        //   = 0
        let coords = delinearize(0, shape);
        assert(coords.first() == 0nat);
        assert((0nat as int) * stride.first() == 0) by {
            vstd::arithmetic::mul::lemma_mul_basics(stride.first());
        };
        assert(coords.skip(1) =~= delinearize(0, shape.skip(1)));
    }
}

} // verus!
