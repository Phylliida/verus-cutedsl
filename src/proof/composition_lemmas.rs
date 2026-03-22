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
pub proof fn lemma_offset_eq_layout(s1: Seq<nat>, t1: Seq<int>, s2: Seq<nat>, t2: Seq<int>, x: nat)
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

// ══════════════════════════════════════════════════════════════
// compose_single_mode stride value
// ══════════════════════════════════════════════════════════════

/// compose_single_mode(a, s, r).stride[0] == r * a.stride[0], for any rank A.
proof fn lemma_compose_single_mode_stride_value(a: LayoutSpec, s: nat, r: nat)
    requires a.valid(), a.shape.len() > 0,
    ensures
        compose_single_mode(a, s, r).stride.first() == (r as int) * a.stride.first(),
{
    if r == 1 && s <= a.shape.first() {
        // Branch 1: stride = a.stride[0]
        // r * a.stride[0] = 1 * a.stride[0] = a.stride[0]
        vstd::arithmetic::mul::lemma_mul_basics(a.stride.first());
    } else {
        // Branch 2: stride = r * a.stride[0]
    }
}

/// For arbitrary-rank A, compose(A, B).stride =~= scale(B.stride, A.stride[0]).
pub proof fn lemma_compose_stride_general(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(), a.shape.len() > 0, b.non_negative_strides(),
    ensures compose(a, b).stride =~= scale_strides_spec(b.stride, a.stride.first()),
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    let d = a.stride.first();
    let c = compose(a, b);
    let scaled = scale_strides_spec(b.stride, d);

    assert forall|i: int| 0 <= i < c.stride.len()
    implies c.stride[i] == scaled[i] by {
        lemma_compose_element(a, b, i);
        lemma_compose_single_mode_stride_value(a, b.shape[i], b.stride[i] as nat);
        assert(scaled[i] == b.stride[i] * d);
    };
}

// ══════════════════════════════════════════════════════════════
// General compose correctness (arbitrary-rank A)
// ══════════════════════════════════════════════════════════════

/// compose(A, B).offset(x) == A.offset(B.offset(x)) for arbitrary-rank A,
/// provided B's image fits within A's first mode.
///
/// This generalizes lemma_compose_correct_1d_a to multi-mode A.
/// The key insight: when bx < A.shape[0], A.offset(bx) = bx * A.stride[0]
/// regardless of A's rank (all higher coordinates are zero).
pub proof fn lemma_compose_correct(a: LayoutSpec, b: LayoutSpec, x: nat)
    requires
        a.valid(), b.valid(),
        a.shape.len() > 0,
        b.non_negative_strides(),
        x < b.size(),
        // B's image fits within A's first mode
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
    lemma_compose_stride_general(a, b);
    let scaled = scale_strides_spec(b.stride, d);

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

    // a.offset(bx) = bx * d for ANY rank A, since bx < a.shape[0]
    lemma_offset_within_first_mode(&a, bx as nat);
    assert(a.offset(bx as nat) == bx * d);

    // d * bx == bx * d
    vstd::arithmetic::mul::lemma_mul_is_commutative(d, bx);
    assert(c.offset(x) == a.offset(bx as nat));
}

// ══════════════════════════════════════════════════════════════
// Composition associativity
// ══════════════════════════════════════════════════════════════

/// compose(compose(a,b), c) produces the same layout as compose(a, compose(b,c)).
///
/// Both have shape = c.shape. The strides agree because:
/// - compose(compose(a,b), c).stride[j] = c.stride[j] * (b.stride[0] * a.stride[0])
/// - compose(a, compose(b,c)).stride[j] = (c.stride[j] * b.stride[0]) * a.stride[0]
/// These are equal by associativity of multiplication.
pub proof fn lemma_compose_associative(a: LayoutSpec, b: LayoutSpec, c: LayoutSpec)
    requires
        a.valid(), b.valid(), c.valid(),
        a.shape.len() > 0,
        b.shape.len() > 0,
        b.non_negative_strides(),
        c.non_negative_strides(),
    ensures
        compose(compose(a, b), c).shape =~= compose(a, compose(b, c)).shape,
        compose(compose(a, b), c).stride =~= compose(a, compose(b, c)).stride,
{
    let ab = compose(a, b);
    let bc = compose(b, c);
    let ab_c = compose(ab, c);
    let a_bc = compose(a, bc);

    let da = a.stride.first();
    let db = b.stride.first();

    // Prove ab and bc are valid first
    assert(ab.valid()) by {
        crate::proof::divide_lemmas::lemma_compose_rank(a, b);
        lemma_compose_shape(a, b);
        assert(ab.shape.len() == b.shape.len());
        assert(ab.stride.len() == b.shape.len());
        assert forall|i: int| 0 <= i < ab.shape.len()
        implies #[trigger] ab.shape[i] > 0 by {
            lemma_compose_element(a, b, i);
        };
    };
    assert(bc.valid()) by {
        crate::proof::divide_lemmas::lemma_compose_rank(b, c);
        lemma_compose_shape(b, c);
        assert(bc.shape.len() == c.shape.len());
        assert(bc.stride.len() == c.shape.len());
        assert forall|i: int| 0 <= i < bc.shape.len()
        implies #[trigger] bc.shape[i] > 0 by {
            lemma_compose_element(b, c, i);
        };
    };
    assert(ab.shape.len() > 0);

    // Shape: both equal c.shape
    lemma_compose_shape(b, c);
    assert(bc.shape =~= c.shape);
    lemma_compose_shape(ab, c);
    lemma_compose_shape(a, bc);
    assert(ab_c.shape =~= c.shape);
    assert(a_bc.shape =~= c.shape);

    // Stride: compose(a,b).stride[0] = b.stride[0] * a.stride[0]
    lemma_compose_element(a, b, 0int);
    lemma_compose_single_mode_stride_value(a, b.shape.first(), b.stride.first() as nat);
    let d_ab = db * da;
    assert(ab.stride.first() == d_ab);

    // Now prove stride equality elementwise
    crate::proof::divide_lemmas::lemma_compose_rank(ab, c);
    crate::proof::divide_lemmas::lemma_compose_rank(a, bc);

    assert forall|j: int| 0 <= j < ab_c.stride.len()
    implies ab_c.stride[j] == a_bc.stride[j] by {
        // ab_c.stride[j] = compose_single_mode(ab, c.shape[j], c.stride[j]).stride[0]
        //                 = c.stride[j] * ab.stride[0] = c.stride[j] * (db * da)
        lemma_compose_element(ab, c, j);
        lemma_compose_single_mode_stride_value(ab, c.shape[j], c.stride[j] as nat);
        assert(ab_c.stride[j] == (c.stride[j] as int) * d_ab);

        // a_bc.stride[j] = compose_single_mode(a, bc.shape[j], bc.stride[j]).stride[0]
        //                 = bc.stride[j] * da
        lemma_compose_element(a, bc, j);
        lemma_compose_single_mode_stride_value(a, bc.shape[j], bc.stride[j] as nat);

        // bc.stride[j] = compose_single_mode(b, c.shape[j], c.stride[j]).stride[0]
        //              = c.stride[j] * db
        lemma_compose_element(b, c, j);
        lemma_compose_single_mode_stride_value(b, c.shape[j], c.stride[j] as nat);
        assert(bc.stride[j] == (c.stride[j] as int) * db);

        assert(a_bc.stride[j] == ((c.stride[j] as int) * db) * da);

        // c.stride[j] * (db * da) == (c.stride[j] * db) * da by associativity
        vstd::arithmetic::mul::lemma_mul_is_associative(c.stride[j] as int, db, da);
    };
}

// ══════════════════════════════════════════════════════════════
// Composition identity laws
// ══════════════════════════════════════════════════════════════

/// Composing A with the identity layout on A's first mode yields a rank-1 projection.
/// compose(A, make_identity(A.shape[0])).shape =~= seq![A.shape[0]]
/// compose(A, make_identity(A.shape[0])).stride =~= seq![A.stride[0]]
pub proof fn lemma_compose_identity_right(a: LayoutSpec)
    requires
        a.valid(),
        a.shape.len() > 0,
    ensures
        compose(a, make_identity(a.shape.first())).shape =~= seq![a.shape.first()],
        compose(a, make_identity(a.shape.first())).stride =~= seq![a.stride.first()],
{
    let m = a.shape.first();
    let id = make_identity(m);
    // id = { shape: seq![m], stride: seq![1] }
    // compose(a, id) with id.shape.len() == 1 → compose_single_mode(a, m, 1)
    // Since b_stride == 1 && b_shape (m) <= a.shape.first() (m): result = (m):(a.stride[0])
    assert(id.shape.len() == 1);
    assert(id.shape.first() == m);
    assert(id.stride.first() == 1);
}

/// Composing the identity layout with A preserves offsets.
/// For all x < a.size(), compose(make_identity(M), a).offset(x) == a.offset(x),
/// provided a's image fits within [0, M).
pub proof fn lemma_compose_identity_left(a: LayoutSpec, m: nat)
    requires
        a.valid(),
        a.shape.len() > 0,
        a.non_negative_strides(),
        m > 0,
        // a's image fits within identity's domain
        forall|x: nat| x < a.size() ==> a.offset(x) >= 0 && a.offset(x) < m as int,
    ensures
        forall|x: nat| x < a.size() ==>
            compose(make_identity(m), a).offset(x) == a.offset(x),
{
    let id = make_identity(m);
    assert(id.valid());
    assert(id.shape.len() > 0);

    // shape_size(seq![m]) == m
    crate::proof::shape_lemmas::lemma_shape_size_single(m);

    // compose(id, a) has shape =~= a.shape, so compose(id, a).size() == a.size()
    let c = compose(id, a);
    lemma_compose_shape(id, a);
    crate::proof::divide_lemmas::lemma_compose_rank(id, a);
    // c is valid
    assert(c.valid()) by {
        assert(c.shape.len() == a.shape.len());
        assert(c.stride.len() == a.shape.len());
        assert forall|i: int| 0 <= i < c.shape.len()
        implies #[trigger] c.shape[i] > 0 by {
            lemma_compose_element(id, a, i);
        };
    };
    assert(c.shape =~= a.shape);

    assert forall|x: nat| x < a.size()
    implies c.offset(x) == a.offset(x)
    by {
        // compose(id, a).offset(x) == id.offset(a.offset(x))
        lemma_compose_correct(id, a, x);
        let ax = a.offset(x);
        assert(c.offset(x) == id.offset(ax as nat));
        // id.offset(k) == k for k < m, since make_identity is column-major
        // Need: ax as nat < shape_size(id.shape) == m
        assert((ax as nat) < shape_size(id.shape));
        crate::proof::injectivity_lemmas::lemma_column_major_offset_is_identity(id.shape, ax as nat);
        // make_column_major(seq![m]).stride == seq![1] == id.stride
        // Unfold: column_major_strides(seq![m]) = seq![1].add(scale(cms(empty), m))
        //       = seq![1].add(empty) = seq![1]
        let cm = make_column_major(id.shape);
        assert(cm.shape =~= id.shape);
        assert(id.shape.skip(1) =~= Seq::<nat>::empty());
        assert(column_major_strides(id.shape.skip(1)) =~= Seq::<int>::empty());
        assert(scale_strides_spec(Seq::<int>::empty(), m as int) =~= Seq::<int>::empty());
        assert(cm.stride =~= seq![1int]);
        assert(cm.stride =~= id.stride);
        lemma_offset_eq_layout(cm.shape, cm.stride, id.shape, id.stride, ax as nat);
    };
}

// ══════════════════════════════════════════════════════════════
// Extended composition lemmas
// ══════════════════════════════════════════════════════════════

/// Extended composition agrees with basic composition when find_split_mode returns None
/// or when the split mode index is out of bounds.
pub proof fn lemma_compose_extended_fallback(a: LayoutSpec, b_shape: nat, b_stride: nat)
    requires
        a.valid(), b_shape > 0,
        find_split_mode(&a, b_stride).is_none()
            || find_split_mode(&a, b_stride).unwrap() >= a.shape.len()
            || b_shape > a.shape[find_split_mode(&a, b_stride).unwrap() as int],
    ensures
        compose_single_mode_extended(a, b_shape, b_stride)
            == compose_single_mode(a, b_shape, b_stride),
{
    // Both functions agree in the stride-1 case and the fallback case.
    // The extended function only differs when find_split_mode succeeds with a valid idx
    // and b_shape fits, which the requires excludes.
}

/// The shape output of compose_single_mode_extended always equals seq![b_shape].
pub proof fn lemma_compose_extended_shape(a: LayoutSpec, b_shape: nat, b_stride: nat)
    requires a.valid(), b_shape > 0,
    ensures compose_single_mode_extended(a, b_shape, b_stride).shape =~= seq![b_shape],
{
}

// ══════════════════════════════════════════════════════════════
// Extended composition correctness
// ══════════════════════════════════════════════════════════════

/// Core helper: when index = prefix_product[i] * x with x < shape[i],
/// the offset equals x * stride[i].
///
/// This works because delinearize gives coords = (0, ..., 0, x, 0, ..., 0)
/// with x at position i, so the dot product with strides is just x * stride[i].
pub proof fn lemma_offset_at_split_mode(layout: &LayoutSpec, i: nat, x: nat)
    requires
        layout.valid(),
        layout.shape.len() > 0,
        i < layout.shape.len(),
        x < layout.shape[i as int],
        // Need index in bounds for delinearize_index_formula
        shape_size(layout.shape.take(i as int)) * x < shape_size(layout.shape),
    ensures
        layout.offset(shape_size(layout.shape.take(i as int)) * x)
            == (x as int) * layout.stride[i as int],
{
    let s = layout.shape;
    let d = layout.stride;
    let pp_i = shape_size(s.take(i as int));
    let idx = pp_i * x;

    let coords = delinearize(idx, s);
    lemma_delinearize_len(idx, s);

    // Show each coordinate k:
    // k < i: coords[k] == 0
    // k == i: coords[k] == x
    // k > i: coords[k] == 0

    // We prove each case separately to help z3
    assert forall|k: int| 0 <= k < s.len() as int && k < i as int
    implies #[trigger] coords[k as int] == 0nat
    by {
        crate::runtime::shape_helpers::lemma_delinearize_index_formula(idx, s, k as nat);
        let pp_k = shape_size(s.take(k));
        if k < i as int {
            // pp_i = pp_k * shape_size(s.take(i).skip(k))
            // using: s.take(i) splits as s.take(k) ++ s.take(i).skip(k)
            let sub = s.take(i as int);
            assert(sub.take(k) =~= s.take(k));
            crate::runtime::shape_helpers::lemma_shape_size_split(sub, k as nat);
            let middle = shape_size(sub.skip(k as int));
            assert(pp_i == pp_k * middle);

            // idx = pp_k * (middle * x)
            assert(idx == pp_k * (middle * x)) by {
                vstd::arithmetic::mul::lemma_mul_is_associative(pp_k as int, middle as int, x as int);
            };

            // idx / pp_k == middle * x
            lemma_shape_size_positive(s.take(k));
            crate::proof::integer_helpers::lemma_div_mul_cancel(pp_k, middle * x);

            // middle = s[k] * s[k+1] * ... * s[i-1], so middle % s[k] == 0
            // sub.skip(k) has first element s[k], so middle = s[k] * shape_size(sub.skip(k).skip(1))
            assert(sub.skip(k as int).first() == s[k]) by {
                assert(sub[k] == s[k]);
            };
            // shape_size(sub.skip(k)) = sub.skip(k)[0] * shape_size(sub.skip(k).skip(1))
            //                         = s[k] * (rest)
            // so middle % s[k] == 0
            assert(sub.skip(k as int).len() > 0) by {
                assert(sub.len() == i as int);
            };
            assert(shape_valid(sub.skip(k as int))) by {
                assert forall|j: int| 0 <= j < sub.skip(k as int).len()
                implies #[trigger] sub.skip(k as int)[j] > 0
                by {
                    assert(sub.skip(k as int)[j] == s[k + j]);
                };
            };
            crate::runtime::shape_helpers::lemma_shape_size_split(sub.skip(k as int), 1);
            assert(sub.skip(k as int).take(1) =~= seq![s[k]]);
            lemma_shape_size_single(s[k]);
            // middle = s[k] * shape_size(sub.skip(k).skip(1))
            let rest_size = shape_size(sub.skip(k as int).skip(1));
            assert(middle == s[k] * rest_size);
            // So middle is a multiple of s[k]
            vstd::arithmetic::mul::lemma_mul_is_commutative(s[k] as int, rest_size as int);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(rest_size as int, s[k] as int);
            assert(middle % s[k] == 0nat);
            // (x * middle) % s[k] == 0
            crate::proof::integer_helpers::lemma_multiple_scaled(middle as int, x, s[k] as int);
            // lemma_multiple_scaled gives (x * middle) % s[k] == 0
            // But we need (middle * x) % s[k] == 0
            vstd::arithmetic::mul::lemma_mul_is_commutative(x as int, middle as int);
            // idx / pp_k == middle * x
            assert(idx / pp_k == middle * x);
            assert((middle * x) % s[k] == 0nat);
            assert((idx / pp_k) % s[k] == 0nat);
            vstd::arithmetic::div_mod::lemma_small_mod(0nat, s[k]);
        }
    };

    // Case k == i: coords[i] == x
    assert(coords[i as int] == x) by {
        crate::runtime::shape_helpers::lemma_delinearize_index_formula(idx, s, i);
        lemma_shape_size_positive(s.take(i as int));
        vstd::arithmetic::mul::lemma_mul_is_commutative(pp_i as int, x as int);
        crate::proof::integer_helpers::lemma_div_mul_cancel(pp_i, x);
        crate::proof::integer_helpers::lemma_mod_small(x, s[i as int]);
    };

    // Case k > i: coords[k] == 0
    assert forall|k: int| 0 <= k < s.len() as int && k > i as int
    implies #[trigger] coords[k as int] == 0nat
    by {
        crate::runtime::shape_helpers::lemma_delinearize_index_formula(idx, s, k as nat);
        let pp_k = shape_size(s.take(k));
        let sub = s.take(k);
        assert(sub.take(i as int) =~= s.take(i as int));
        assert(shape_valid(sub)) by {
            assert forall|j: int| 0 <= j < sub.len()
            implies #[trigger] sub[j] > 0
            by { assert(sub[j] == s[j]); };
        };
        crate::runtime::shape_helpers::lemma_shape_size_split(sub, i);
        let middle = shape_size(sub.skip(i as int));
        assert(pp_k == pp_i * middle);

        assert(sub.skip(i as int).first() == s[i as int]) by {
            assert(sub[i as int] == s[i as int]);
        };
        assert(sub.skip(i as int).len() > 0);
        assert(shape_valid(sub.skip(i as int))) by {
            assert forall|j: int| 0 <= j < sub.skip(i as int).len()
            implies #[trigger] sub.skip(i as int)[j] > 0
            by { assert(sub.skip(i as int)[j] == s[(i as int) + j]); };
        };
        crate::proof::inverse_lemmas::lemma_shape_size_geq_entry(sub.skip(i as int), 0);
        assert(middle >= s[i as int]);
        assert(middle > x);
        lemma_shape_size_positive(s.take(i as int));
        assert(pp_i > 0nat);
        assert(pp_i * middle > pp_i * x) by {
            vstd::arithmetic::mul::lemma_mul_inequality(x as int, (middle - 1) as int, pp_i as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(pp_i as int, x as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(pp_i as int, (middle - 1) as int);
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub(pp_i as int, middle as int, 1int);
        };
        assert(idx < pp_k);
        assert(pp_k > 0nat) by {
            vstd::arithmetic::mul::lemma_mul_strictly_positive(pp_i as int, middle as int);
        };
        crate::proof::integer_helpers::lemma_div_small(idx, pp_k);
        assert(idx / pp_k == 0nat);
        vstd::arithmetic::div_mod::lemma_small_mod(0nat, s[k]);
        assert((idx / pp_k) % s[k] == 0nat);
    };

    // Now dot_product(coords, d) == x * d[i]
    // All coords except i are 0, and coords[i] == x
    assert forall|k: int| 0 <= k < coords.len() && k != i as int
    implies coords[k] == 0nat
    by {
        if k < i as int {
            assert(coords[k as int] == 0nat);
        } else {
            assert(k > i as int);
            assert(coords[k as int] == 0nat);
        }
    };
    lemma_dot_product_unit(coords, d, i, x);
}

/// Helper: dot product of a vector with a single nonzero entry at position i
/// equals that entry times the corresponding stride.
proof fn lemma_dot_product_unit(coords: Seq<nat>, strides: Seq<int>, i: nat, x: nat)
    requires
        coords.len() == strides.len(),
        i < coords.len(),
        coords[i as int] == x,
        forall|k: int| 0 <= k < coords.len() && k != i as int ==> coords[k] == 0nat,
    ensures
        dot_product_nat_int(coords, strides) == (x as int) * strides[i as int],
    decreases coords.len(),
{
    if coords.len() == 0 {
        assert(false); // unreachable: i < coords.len()
    } else if coords.len() == 1 {
        assert(i == 0);
        assert(coords.first() == x);
        // dot = x * strides[0] + dot(empty, empty) = x * strides[0]
        assert(coords.skip(1).len() == 0nat);
        assert(dot_product_nat_int(coords.skip(1), strides.skip(1)) == 0int);
    } else {
        if i == 0 {
            assert forall|k: int| 0 <= k < coords.skip(1).len()
            implies #[trigger] coords.skip(1)[k] == 0nat by {
                assert(coords.skip(1)[k] == coords[k + 1]);
            };
            lemma_dot_product_zero_coords(coords.skip(1), strides.skip(1));
        } else {
            assert(coords.first() == 0nat);
            assert(coords.skip(1)[(i - 1) as int] == x) by {
                assert(coords.skip(1)[(i - 1) as int] == coords[i as int]);
            };
            assert forall|k: int| 0 <= k < coords.skip(1).len() && k != (i - 1) as int
            implies #[trigger] coords.skip(1)[k] == 0nat by {
                assert(coords.skip(1)[k] == coords[k + 1]);
            };
            lemma_dot_product_unit(coords.skip(1), strides.skip(1), (i - 1) as nat, x);
            assert(strides.skip(1)[(i - 1) as int] == strides[i as int]);
        }
    }
}

/// Correctness of compose_single_mode_extended: when B's stride matches a prefix
/// product of A and B's shape fits in the corresponding mode of A, the composed
/// offset equals A.offset(b_stride * x).
///
/// This is the key theorem that generalizes compose beyond the "first mode" restriction.
pub proof fn lemma_compose_single_mode_extended_correct(
    a: LayoutSpec, b_shape: nat, b_stride: nat, x: nat,
)
    requires
        a.valid(),
        a.shape.len() > 0,
        b_shape > 0,
        x < b_shape,
        // b_stride matches a prefix product at mode idx, and b_shape fits
        find_split_mode(&a, b_stride).is_some(),
        ({
            let idx = find_split_mode(&a, b_stride).unwrap();
            &&& idx < a.shape.len()
            &&& b_shape <= a.shape[idx as int]
        }),
        // The composed index must be in bounds
        b_stride * x < shape_size(a.shape),
    ensures
        compose_single_mode_extended(a, b_shape, b_stride).offset(x)
            == a.offset(b_stride * x),
{
    let idx = find_split_mode(&a, b_stride).unwrap();
    // compose_single_mode_extended returns (b_shape):(a.stride[idx])
    // Its offset(x) = x * a.stride[idx]

    // We need: a.offset(b_stride * x) == x * a.stride[idx]
    // b_stride == shape_size(a.shape.take(idx)) (from find_split_mode)
    // By lemma_offset_at_split_mode: a.offset(pp[idx] * x) == x * a.stride[idx]
    // where pp[idx] == shape_size(a.shape.take(idx)) == b_stride

    // First establish b_stride == shape_size(a.shape.take(idx))
    crate::proof::inverse_lemmas::lemma_prefix_products_value(a.shape, idx);
    let pp = crate::inverse::shape_prefix_products(a.shape);
    // find_split_mode found pp[idx] == b_stride
    // pp[idx] == shape_size(a.shape.take(idx))
    lemma_find_pp_index_correct(pp, b_stride, 0);
    assert(pp[idx as int] == b_stride);
    assert(shape_size(a.shape.take(idx as int)) == b_stride);

    // x < b_shape <= a.shape[idx]
    assert(x < a.shape[idx as int]);

    // shape_size(a.shape.take(idx)) * x = b_stride * x < shape_size(a.shape)
    lemma_offset_at_split_mode(&a, idx, x);

    // compose_single_mode_extended(a, b_shape, b_stride).offset(x) = x * a.stride[idx]
    // which is a 1D layout (b_shape):(a.stride[idx])
    lemma_1d_offset(b_shape, a.stride[idx as int], x);
}

/// Helper: find_pp_index returns an index where pp[idx] == target.
proof fn lemma_find_pp_index_correct(pp: Seq<nat>, target: nat, pos: nat)
    requires
        find_pp_index(pp, target, pos).is_some(),
        pos <= pp.len(),
    ensures
        ({
            let idx = find_pp_index(pp, target, pos).unwrap();
            idx < pp.len() && pp[idx as int] == target
        }),
    decreases pp.len() - pos,
{
    if pos >= pp.len() {
        // find_pp_index returns None — contradicts is_some()
    } else if pp[pos as int] == target {
        // returns Some(pos)
    } else {
        // recurse
        lemma_find_pp_index_correct(pp, target, pos + 1);
    }
}

} // verus!
