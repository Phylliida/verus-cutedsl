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

// ══════════════════════════════════════════════════════════════
// Element-wise compose access
// ══════════════════════════════════════════════════════════════

/// compose(a, b).shape[i] == b.shape[i] and stride matches compose_single_mode.
pub proof fn lemma_compose_element(a: LayoutSpec, b: LayoutSpec, i: int)
    requires a.valid(), b.valid(), 0 <= i < b.shape.len(), a.shape.len() > 0,
    ensures
        compose(a, b).shape.len() == b.shape.len(),
        compose(a, b).stride.len() == b.shape.len(),
        compose(a, b).shape[i] == b.shape[i],
        compose(a, b).stride[i] == compose_single_mode(a, b.shape[i], b.stride[i] as nat).stride.first(),
    decreases b.shape.len(),
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    if b.shape.len() == 1 {
        assert(b.shape.first() == b.shape[i]);
        assert(b.stride.first() == b.stride[i]);
    } else {
        let first = compose_single_mode(a, b.shape.first(), b.stride.first() as nat);
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        let rest = compose(a, rest_b);
        assert(first.shape.len() == 1);
        assert(first.stride.len() == 1);
        if i == 0 {
            assert(first.shape.add(rest.shape)[0] == first.shape[0]);
            assert(first.stride.add(rest.stride)[0] == first.stride[0]);
            assert(first.shape[0] == b.shape.first());
        } else {
            assert(first.shape.add(rest.shape)[i] == rest.shape[i - 1]);
            assert(first.stride.add(rest.stride)[i] == rest.stride[i - 1]);
            assert(rest_b.valid()) by {
                assert forall|j: int| 0 <= j < rest_b.shape.len() implies #[trigger] rest_b.shape[j] > 0 by {
                    assert(b.shape[j + 1] > 0);
                };
            };
            lemma_compose_element(a, rest_b, i - 1);
            assert(rest_b.shape[i - 1] == b.shape[i]);
            assert(rest_b.stride[i - 1] == b.stride[i]);
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Compose shape and stride as sequences
// ══════════════════════════════════════════════════════════════

/// compose(a, b).shape is extensionally equal to b.shape.
pub proof fn lemma_compose_shape(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(), a.shape.len() > 0,
    ensures compose(a, b).shape =~= b.shape,
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    assert forall|i: int| 0 <= i < b.shape.len()
    implies #[trigger] compose(a, b).shape[i] == b.shape[i] by {
        lemma_compose_element(a, b, i);
    }
}

/// For rank-1 A, compose_single_mode always gives stride b_stride * a.stride[0].
proof fn lemma_compose_single_mode_stride_1d(
    a: LayoutSpec, b_shape: nat, b_stride: nat,
)
    requires
        a.valid(),
        a.shape.len() == 1,
        b_shape > 0,
    ensures
        compose_single_mode(a, b_shape, b_stride).stride.first()
            == (b_stride as int) * a.stride.first(),
{
    if b_stride == 1 && b_shape <= a.shape.first() {
        // Special case: stride = a.stride[0] = 1 * a.stride[0]
        vstd::arithmetic::mul::lemma_mul_basics(a.stride.first());
    } else {
        // General case: stride = b_stride * a.stride[0]
    }
}

/// For rank-1 A, compose(A, B).stride =~= scale_strides_spec(B.stride, A.stride[0]).
proof fn lemma_compose_stride_1d(a: LayoutSpec, b: LayoutSpec)
    requires
        a.valid(), b.valid(),
        a.shape.len() == 1,
        b.non_negative_strides(),
    ensures
        compose(a, b).stride =~= crate::layout::scale_strides_spec(b.stride, a.stride.first()),
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    let scaled = crate::layout::scale_strides_spec(b.stride, a.stride.first());
    assert forall|i: int| 0 <= i < b.shape.len()
    implies #[trigger] compose(a, b).stride[i] == scaled[i] by {
        lemma_compose_element(a, b, i);
        assert(b.stride[i] >= 0);
        lemma_compose_single_mode_stride_1d(a, b.shape[i], b.stride[i] as nat);
        // compose gives ((b.stride[i] as nat) as int) * d
        // Since b.stride[i] >= 0: (b.stride[i] as nat) as int == b.stride[i]
        assert(scaled[i] == b.stride[i] * a.stride.first());
        vstd::arithmetic::mul::lemma_mul_is_commutative(b.stride[i], a.stride.first());
    }
}

// ══════════════════════════════════════════════════════════════
// Compose correctness: rank-1 A with arbitrary B
// ══════════════════════════════════════════════════════════════

/// Helper: for a layout with shape s and stride t, the offset equals the dot product
/// of the delinearized coordinates with the strides.
/// If we substitute shape/stride with =~= equivalents, offset is preserved.
proof fn lemma_offset_eq_layout(s1: Seq<nat>, t1: Seq<int>, s2: Seq<nat>, t2: Seq<int>, x: nat)
    requires
        s1 =~= s2,
        t1 =~= t2,
    ensures ({
        let l1 = LayoutSpec { shape: s1, stride: t1 };
        let l2 = LayoutSpec { shape: s2, stride: t2 };
        l1.offset(x) == l2.offset(x)
    }),
{
    // s1 == s2 and t1 == t2 by extensional equality
    // So LayoutSpec{s1, t1} has the same shape and stride fields
    // and offset uses only those fields, so offsets are equal.
}

/// For rank-1 A = (M):(d) and arbitrary B, compose(A, B).offset(x) == A.offset(B.offset(x)),
/// provided B's image fits within A's domain.
pub proof fn lemma_compose_correct_1d_a(a: LayoutSpec, b: LayoutSpec, x: nat)
    requires
        a.valid(), b.valid(),
        a.shape.len() == 1,
        b.non_negative_strides(),
        x < b.size(),
        // B's image fits within A's domain
        b.offset(x) >= 0,
        b.offset(x) < a.shape.first() as int,
    ensures
        compose(a, b).offset(x) == a.offset(b.offset(x) as nat),
{
    let d = a.stride.first();
    let bx = b.offset(x);
    let c = compose(a, b);

    // compose(a,b).shape =~= b.shape
    lemma_compose_shape(a, b);

    // compose(a,b).stride =~= scale(b.stride, d)
    lemma_compose_stride_1d(a, b);
    let scaled = crate::layout::scale_strides_spec(b.stride, d);

    // Build an equivalent layout with b.shape and scaled strides
    let equiv = LayoutSpec { shape: b.shape, stride: scaled };

    // compose(a,b).offset(x) == equiv.offset(x)
    lemma_offset_eq_layout(c.shape, c.stride, b.shape, scaled, x);

    // equiv.offset(x) = dot(delinearize(x, b.shape), scaled)
    let coords = delinearize(x, b.shape);
    lemma_delinearize_len(x, b.shape);

    // dot(coords, scaled) == d * dot(coords, b.stride) by scale lemma
    crate::proof::injectivity_lemmas::lemma_dot_product_scale(coords, b.stride, d);

    // Explicit chain:
    assert(equiv.offset(x) == dot_product_nat_int(coords, scaled));
    assert(dot_product_nat_int(coords, scaled) == d * dot_product_nat_int(coords, b.stride));
    assert(b.offset(x) == dot_product_nat_int(coords, b.stride));
    assert(c.offset(x) == equiv.offset(x));
    assert(c.offset(x) == d * bx);

    // a.offset(bx) = bx * d (since bx < M, rank-1 A)
    // lemma_1d_offset gives us the result for LayoutSpec{seq![M], seq![d]}
    // We need to bridge this to `a`
    lemma_1d_offset(a.shape.first(), d, bx as nat);
    // Bridge: a.shape =~= seq![a.shape.first()], a.stride =~= seq![d]
    assert(a.shape =~= seq![a.shape.first()]);
    assert(a.stride =~= seq![d]);
    lemma_offset_eq_layout(
        a.shape, a.stride,
        seq![a.shape.first()], seq![d],
        bx as nat,
    );
    assert(a.offset(bx as nat) == bx * d);

    // d * bx == bx * d
    vstd::arithmetic::mul::lemma_mul_is_commutative(d, bx);
    assert(c.offset(x) == a.offset(bx as nat));
}

} // verus!
