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
// 1D compose_linear 1D: base case
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
// Stride-1 composition: multi-mode A compose_linear (N):(1)
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
// Element-wise compose_linear access
// ══════════════════════════════════════════════════════════════

/// compose_linear(a, b).shape[i] == b.shape[i] and stride matches compose_single_mode.
pub proof fn lemma_compose_element(a: LayoutSpec, b: LayoutSpec, i: int)
    requires a.valid(), b.valid(), 0 <= i < b.shape.len(), a.shape.len() > 0,
    ensures
        compose_linear(a, b).shape.len() == b.shape.len(),
        compose_linear(a, b).stride.len() == b.shape.len(),
        compose_linear(a, b).shape[i] == b.shape[i],
        compose_linear(a, b).stride[i] == compose_single_mode(a, b.shape[i], b.stride[i] as nat).stride.first(),
    decreases b.shape.len(),
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    if b.shape.len() == 1 {
        assert(b.shape.first() == b.shape[i]);
        assert(b.stride.first() == b.stride[i]);
    } else {
        let first = compose_single_mode(a, b.shape.first(), b.stride.first() as nat);
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        let rest = compose_linear(a, rest_b);
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

/// compose_linear(a, b).shape is extensionally equal to b.shape.
pub proof fn lemma_compose_shape(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(), a.shape.len() > 0,
    ensures compose_linear(a, b).shape =~= b.shape,
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    assert forall|i: int| 0 <= i < b.shape.len()
    implies #[trigger] compose_linear(a, b).shape[i] == b.shape[i] by {
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

/// For rank-1 A, compose_linear(A, B).stride =~= scale_strides_spec(B.stride, A.stride[0]).
proof fn lemma_compose_stride_1d(a: LayoutSpec, b: LayoutSpec)
    requires
        a.valid(), b.valid(),
        a.shape.len() == 1,
        b.non_negative_strides(),
    ensures
        compose_linear(a, b).stride =~= crate::layout::scale_strides_spec(b.stride, a.stride.first()),
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    let scaled = crate::layout::scale_strides_spec(b.stride, a.stride.first());
    assert forall|i: int| 0 <= i < b.shape.len()
    implies #[trigger] compose_linear(a, b).stride[i] == scaled[i] by {
        lemma_compose_element(a, b, i);
        assert(b.stride[i] >= 0);
        lemma_compose_single_mode_stride_1d(a, b.shape[i], b.stride[i] as nat);
        // compose_linear gives ((b.stride[i] as nat) as int) * d
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

/// For rank-1 A = (M):(d) and arbitrary B, compose_linear(A, B).offset(x) == A.offset(B.offset(x)),
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
        compose_linear(a, b).offset(x) == a.offset(b.offset(x) as nat),
{
    let d = a.stride.first();
    let bx = b.offset(x);
    let c = compose_linear(a, b);

    // compose_linear(a,b).shape =~= b.shape
    lemma_compose_shape(a, b);

    // compose_linear(a,b).stride =~= scale(b.stride, d)
    lemma_compose_stride_1d(a, b);
    let scaled = crate::layout::scale_strides_spec(b.stride, d);

    // Build an equivalent layout with b.shape and scaled strides
    let equiv = LayoutSpec { shape: b.shape, stride: scaled };

    // compose_linear(a,b).offset(x) == equiv.offset(x)
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

/// For arbitrary-rank A, compose_linear(A, B).stride =~= scale(B.stride, A.stride[0]).
pub proof fn lemma_compose_stride_general(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(), a.shape.len() > 0, b.non_negative_strides(),
    ensures compose_linear(a, b).stride =~= scale_strides_spec(b.stride, a.stride.first()),
{
    crate::proof::divide_lemmas::lemma_compose_rank(a, b);
    let d = a.stride.first();
    let c = compose_linear(a, b);
    let scaled = scale_strides_spec(b.stride, d);

    assert forall|i: int| 0 <= i < c.stride.len()
    implies c.stride[i] == scaled[i] by {
        lemma_compose_element(a, b, i);
        lemma_compose_single_mode_stride_value(a, b.shape[i], b.stride[i] as nat);
        assert(scaled[i] == b.stride[i] * d);
    };
}

// ══════════════════════════════════════════════════════════════
// General compose_linear correctness (arbitrary-rank A)
// ══════════════════════════════════════════════════════════════

/// compose_linear(A, B).offset(x) == A.offset(B.offset(x)) for arbitrary-rank A,
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
        compose_linear(a, b).offset(x) == a.offset(b.offset(x) as nat),
{
    let d = a.stride.first();
    let bx = b.offset(x);
    let c = compose_linear(a, b);

    // compose_linear(a,b).shape =~= b.shape
    lemma_compose_shape(a, b);

    // compose_linear(a,b).stride =~= scale(b.stride, d)
    lemma_compose_stride_general(a, b);
    let scaled = scale_strides_spec(b.stride, d);

    // Build an equivalent layout with b.shape and scaled strides
    let equiv = LayoutSpec { shape: b.shape, stride: scaled };

    // compose_linear(a,b).offset(x) == equiv.offset(x)
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

/// compose_linear(compose_linear(a,b), c) produces the same layout as compose_linear(a, compose_linear(b,c)).
///
/// Both have shape = c.shape. The strides agree because:
/// - compose_linear(compose_linear(a,b), c).stride[j] = c.stride[j] * (b.stride[0] * a.stride[0])
/// - compose_linear(a, compose_linear(b,c)).stride[j] = (c.stride[j] * b.stride[0]) * a.stride[0]
/// These are equal by associativity of multiplication.
pub proof fn lemma_compose_associative(a: LayoutSpec, b: LayoutSpec, c: LayoutSpec)
    requires
        a.valid(), b.valid(), c.valid(),
        a.shape.len() > 0,
        b.shape.len() > 0,
        b.non_negative_strides(),
        c.non_negative_strides(),
    ensures
        compose_linear(compose_linear(a, b), c).shape =~= compose_linear(a, compose_linear(b, c)).shape,
        compose_linear(compose_linear(a, b), c).stride =~= compose_linear(a, compose_linear(b, c)).stride,
{
    let ab = compose_linear(a, b);
    let bc = compose_linear(b, c);
    let ab_c = compose_linear(ab, c);
    let a_bc = compose_linear(a, bc);

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

    // Stride: compose_linear(a,b).stride[0] = b.stride[0] * a.stride[0]
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
/// compose_linear(A, make_identity(A.shape[0])).shape =~= seq![A.shape[0]]
/// compose_linear(A, make_identity(A.shape[0])).stride =~= seq![A.stride[0]]
pub proof fn lemma_compose_identity_right(a: LayoutSpec)
    requires
        a.valid(),
        a.shape.len() > 0,
    ensures
        compose_linear(a, make_identity(a.shape.first())).shape =~= seq![a.shape.first()],
        compose_linear(a, make_identity(a.shape.first())).stride =~= seq![a.stride.first()],
{
    let m = a.shape.first();
    let id = make_identity(m);
    // id = { shape: seq![m], stride: seq![1] }
    // compose_linear(a, id) with id.shape.len() == 1 → compose_single_mode(a, m, 1)
    // Since b_stride == 1 && b_shape (m) <= a.shape.first() (m): result = (m):(a.stride[0])
    assert(id.shape.len() == 1);
    assert(id.shape.first() == m);
    assert(id.stride.first() == 1);
}

/// Composing the identity layout with A preserves offsets.
/// For all x < a.size(), compose_linear(make_identity(M), a).offset(x) == a.offset(x),
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
            compose_linear(make_identity(m), a).offset(x) == a.offset(x),
{
    let id = make_identity(m);
    assert(id.valid());
    assert(id.shape.len() > 0);

    // shape_size(seq![m]) == m
    crate::proof::shape_lemmas::lemma_shape_size_single(m);

    // compose_linear(id, a) has shape =~= a.shape, so compose_linear(id, a).size() == a.size()
    let c = compose_linear(id, a);
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
        // compose_linear(id, a).offset(x) == id.offset(a.offset(x))
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
/// This is the key theorem that generalizes compose_linear beyond the "first mode" restriction.
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

// ══════════════════════════════════════════════════════════════
// compose_extended == compose_linear for rank-1 A
// ══════════════════════════════════════════════════════════════

/// For rank-1 A, compose_single_mode_extended == compose_single_mode.
///
/// prefix_products of rank-1 shape [M] = [1, M]. find_split_mode can only find:
/// - idx=0 (r==1): handled by stride-1 branch OR fallback gives r*d = d (same result)
/// - idx=1 (r==M): idx >= shape.len(), so fallback gives r*d (same as compose_single_mode)
/// - no match: fallback gives r*d (same as compose_single_mode)
pub proof fn lemma_single_mode_extended_eq_rank1(
    a: LayoutSpec, b_shape: nat, b_stride: nat,
)
    requires
        a.valid(),
        a.shape.len() == 1,
        b_shape > 0,
    ensures
        compose_single_mode_extended(a, b_shape, b_stride) == compose_single_mode(a, b_shape, b_stride),
{
    let d = a.stride.first();
    let m = a.shape.first();

    if b_stride == 1 && b_shape <= m && a.shape.len() > 0 {
        // Both take the stride-1 branch: (b_shape):(d)
    } else {
        // compose_single_mode gives (b_shape):(b_stride * d) in the else branch
        // compose_single_mode_extended checks find_split_mode(&a, b_stride)
        let pp = crate::inverse::shape_prefix_products(a.shape);
        // pp = [1, M] for rank-1 A
        crate::proof::inverse_lemmas::lemma_prefix_products_len(a.shape);
        crate::proof::inverse_lemmas::lemma_prefix_products_first(a.shape);
        crate::proof::inverse_lemmas::lemma_prefix_products_value(a.shape, 1);
        assert(pp.len() == 2);
        assert(pp[0] == 1nat);
        // pp[1] == shape_size(a.shape.take(1)) == m
        assert(a.shape.take(1) =~= seq![m]);
        lemma_shape_size_single(m);
        assert(shape_size(a.shape.take(1)) == m);
        assert(pp[1] == m);

        match find_split_mode(&a, b_stride) {
            Some(idx) => {
                lemma_find_pp_index_correct(pp, b_stride, 0);
                assert(pp[idx as int] == b_stride);
                // idx is either 0 or 1
                if idx == 0 {
                    // b_stride == pp[0] == 1
                    // We're in the else branch, so either b_shape > m or shape.len() == 0
                    // shape.len() == 1 > 0, so b_shape > m
                    // idx < shape.len() is 0 < 1 = true
                    // b_shape <= a.shape[0] = m is false
                    // So fallback: (b_shape):(b_stride * d) = (b_shape):(1*d) = (b_shape):(d)
                    // compose_single_mode else: (b_shape):(1*d) = (b_shape):(d)
                    assert(b_stride == 1nat);
                    assert(b_shape > m);
                } else {
                    // idx == 1, idx < shape.len() is 1 < 1 = false
                    // Fallback: (b_shape):(b_stride * d)
                    assert(idx == 1nat);
                    assert(!(idx < a.shape.len()));
                }
            }
            None => {
                // No match, fallback: (b_shape):(b_stride * d)
            }
        }
    }
}

/// For rank-1 A, compose_extended == compose_linear (structural equality).
pub proof fn lemma_compose_extended_eq_rank1(a: LayoutSpec, b: LayoutSpec)
    requires
        a.valid(),
        a.shape.len() == 1,
        b.valid(),
    ensures
        compose_extended(a, b) == compose_linear(a, b),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
        // Both return empty layout
    } else if b.shape.len() == 1 {
        lemma_single_mode_extended_eq_rank1(a, b.shape.first(), b.stride.first() as nat);
    } else {
        let bs = b.shape.first();
        let bd = b.stride.first() as nat;
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        assert(rest_b.valid()) by {
            assert forall|i: int| 0 <= i < rest_b.shape.len()
            implies #[trigger] rest_b.shape[i] > 0 by {
                assert(rest_b.shape[i] == b.shape[i + 1]);
            };
        };

        // Single mode: extended == basic
        lemma_single_mode_extended_eq_rank1(a, bs, bd);

        // Rest: extended == basic by induction
        lemma_compose_extended_eq_rank1(a, rest_b);

        // Both produce first.shape ++ rest.shape, first.stride ++ rest.stride
        // where first and rest are the same for both
    }
}

// ══════════════════════════════════════════════════════════════
// Multi-mode compose_extended correctness
// ══════════════════════════════════════════════════════════════

/// compose_extended produces shape.len() == stride.len().
proof fn lemma_compose_extended_stride_len(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), a.shape.len() > 0, b.valid(),
    ensures compose_extended(a, b).shape.len() == compose_extended(a, b).stride.len(),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
    } else if b.shape.len() == 1 {
    } else {
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        assert(rest_b.valid()) by {
            assert forall|i: int| 0 <= i < rest_b.shape.len()
            implies #[trigger] rest_b.shape[i] > 0 by { assert(rest_b.shape[i] == b.shape[i + 1]); };
        };
        lemma_compose_extended_stride_len(a, rest_b);
    }
}

/// Predicate: compose_extended is correct for A and B at all indices.
/// This is defined recursively to enable inductive proofs.
pub open spec fn compose_extended_correct_at(a: LayoutSpec, b: LayoutSpec) -> bool
    decreases b.shape.len(),
{
    &&& a.valid()
    &&& a.shape.len() > 0
    &&& b.valid()
    &&& b.non_negative_strides()
    &&& (b.shape.len() > 0 ==> {
        let b_rest = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        // 1. Each single-mode extended composition is correct for this mode
        &&& forall|c: nat| c < b.shape.first() ==> (#[trigger] a.offset((b.stride.first() * (c as int)) as nat))
            == compose_single_mode_extended(a, b.shape.first(), b.stride.first() as nat).offset(c)
        // 2. Recursion: compose_extended is correct for remaining modes
        &&& compose_extended_correct_at(a, b_rest)
        // 3. A.offset is additive over first mode and rest
        //    A.offset(stride[0]*c + rest_offset) == A.offset(stride[0]*c) + A.offset(rest_offset)
        &&& forall|c: nat, rest_off: nat|
            c < b.shape.first()
            && rest_off < a.size()
            && (b.stride.first() * (c as int)) as nat + rest_off < a.size()
            ==>
            #[trigger] a.offset((b.stride.first() * (c as int)) as nat + rest_off)
                == a.offset((b.stride.first() * (c as int)) as nat) + a.offset(rest_off)
    })
}

/// Multi-mode compose_extended correctness.
///
/// When `compose_extended_correct_at(A, B)` holds, the composed layout
/// produces the same offset as `A.offset(B.offset(x))` for all x < B.size().
///
/// The predicate `compose_extended_correct_at` requires:
/// 1. Each single-mode composition is correct (offset matches A.offset(stride * coord))
/// 2. A.offset is additive over B's mode decomposition (first mode independent of rest)
///
/// These conditions hold when B's strides address non-overlapping modes of A
/// (e.g., B's strides are prefix products of A's shape).
pub proof fn lemma_compose_extended_correct(a: LayoutSpec, b: LayoutSpec, x: nat)
    requires
        compose_extended_correct_at(a, b),
        x < b.size(),
        b.offset(x) >= 0,
        (b.offset(x) as nat) < a.size(),
    ensures
        compose_extended(a, b).offset(x) == a.offset(b.offset(x) as nat),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
        // compose_extended returns empty, offset = 0
        // B.offset(x) = dot(delinearize(x, []), []) = 0
        // A.offset(0) = 0
        crate::proof::offset_lemmas::lemma_offset_zero(a);
        assert(b.offset(x) == 0int);
    } else {
        let bs = b.shape.first();
        let bd = b.stride.first();
        let c0 = x % bs;
        let x_rest = x / bs;
        let b_rest = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };

        // b_rest validity
        assert(b_rest.valid()) by {
            assert forall|i: int| 0 <= i < b_rest.shape.len()
            implies #[trigger] b_rest.shape[i] > 0 by { assert(b_rest.shape[i] == b.shape[i + 1]); };
        };
        assert(b_rest.non_negative_strides()) by {
            assert forall|i: int| 0 <= i < b_rest.stride.len()
            implies #[trigger] b_rest.stride[i] >= 0 by { assert(b_rest.stride[i] == b.stride[i + 1]); };
        };

        // Bounds: c0 < bs, x_rest < b_rest.size()
        crate::proof::integer_helpers::lemma_mod_bound(x, bs);
        crate::runtime::shape_helpers::lemma_shape_size_split(b.shape, 1);
        assert(b.shape.take(1) =~= seq![bs]);
        lemma_shape_size_single(bs);
        lemma_shape_size_positive(b_rest.shape);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, bs, b_rest.size());

        // ═══ Step 1: B.offset(x) == bd * c0 + b_rest.offset(x_rest) ═══
        let b_first_s: Seq<nat> = seq![bs];
        assert(b.shape =~= b_first_s.add(b_rest.shape));
        lemma_delinearize_len(x, b.shape);
        lemma_delinearize_concat(x, b_first_s, b_rest.shape);
        lemma_delinearize_len(c0, b_first_s);
        lemma_dot_product_append(
            delinearize(c0, b_first_s), delinearize(x_rest, b_rest.shape),
            seq![bd], b_rest.stride,
        );
        // dot([c0%bs], [bd]) = c0 * bd  (since c0 < bs, c0%bs == c0)
        // The first-mode layout (bs):(bd) has offset(c0) == c0 * bd
        let b_first_layout = LayoutSpec { shape: b_first_s, stride: seq![bd] };
        assert(b_first_layout.valid());
        lemma_offset_within_first_mode(&b_first_layout, c0);
        assert(b_first_layout.offset(c0) == (c0 as int) * bd);

        // B.offset(x) decomposes via concat: = b_first.offset(c0) + b_rest.offset(x_rest)
        lemma_delinearize_len(c0, b_first_s);
        lemma_dot_product_append(
            delinearize(c0, b_first_s), delinearize(x_rest, b_rest.shape),
            seq![bd], b_rest.stride,
        );
        // Connect dot_product_append result to b.offset(x)
        assert(b.stride =~= seq![bd].add(b_rest.stride));
        // b.offset(x) = dot(delinearize(x, b.shape), b.stride)
        //             = dot(delinearize(c0, [bs]), [bd]) + dot(delinearize(x_rest, b_rest.shape), b_rest.stride)
        //             = b_first_layout.offset(c0) + b_rest.offset(x_rest)
        //             = c0*bd + b_rest.offset(x_rest)
        assert(b.offset(x) == (c0 as int) * bd + b_rest.offset(x_rest));

        // ═══ Step 2: compose_extended.offset(x) == single.offset(c0) + rest.offset(x_rest) ═══
        let single = compose_single_mode_extended(a, bs, bd as nat);
        let rest_c = compose_extended(a, b_rest);
        let ce = compose_extended(a, b);
        // ce has shape = single.shape ++ rest_c.shape, stride = single.stride ++ rest_c.stride
        // (from compose_extended definition)
        lemma_compose_extended_shape(a, bs, bd as nat);  // single.shape =~= [bs]
        assert(ce.shape =~= single.shape.add(rest_c.shape));
        assert(ce.stride =~= single.stride.add(rest_c.stride));
        assert(shape_size(single.shape) == bs);
        crate::proof::product_lemmas::lemma_shape_size_append(single.shape, rest_c.shape);

        // ce.offset(x) = dot(delinearize(x, ce.shape), ce.stride)
        // Using concat: = dot(delinearize(c0, single.shape), single.stride)
        //              + dot(delinearize(x_rest, rest_c.shape), rest_c.stride)
        //              = single.offset(c0) + rest_c.offset(x_rest)
        lemma_delinearize_len(c0, single.shape);
        // Need x < shape_size(single.shape ++ rest_c.shape) for delinearize_concat
        // ce.shape =~= single.shape ++ rest_c.shape, and x < b.size() == ce.size()
        assert(shape_valid(single.shape));
        assert(shape_valid(rest_c.shape)) by {
            // rest_c = compose_extended(a, b_rest), its shape =~= b_rest.shape (valid)
            crate::proof::divide_lemmas::lemma_compose_extended_multimode_shape(a, b_rest);
            assert(rest_c.shape =~= b_rest.shape);
            assert forall|i: int| 0 <= i < rest_c.shape.len()
            implies #[trigger] rest_c.shape[i] > 0 by {
                assert(rest_c.shape[i] == b_rest.shape[i]);
            };
        };
        // x < b.size() = bs * b_rest.size() = shape_size(single.shape) * shape_size(rest_c.shape)
        crate::proof::divide_lemmas::lemma_compose_extended_multimode_shape(a, b_rest);
        lemma_delinearize_concat(x, single.shape, rest_c.shape);
        // Lengths for dot_product_append
        lemma_delinearize_len(x_rest, rest_c.shape);
        assert(single.shape.len() == single.stride.len());
        assert(rest_c.shape.len() == rest_c.stride.len()) by {
            // compose_extended preserves shape =~= b_rest.shape
            // and stride has same length as shape (from definition)
            lemma_compose_extended_stride_len(a, b_rest);
        };
        lemma_dot_product_append(
            delinearize(c0, single.shape), delinearize(x_rest, rest_c.shape),
            single.stride, rest_c.stride,
        );
        assert(ce.offset(x) == single.offset(c0) + rest_c.offset(x_rest));

        // ═══ Step 3: single.offset(c0) == A.offset(bd * c0) (condition 1) ═══
        let a_val_at_bd_c0 = a.offset((bd * (c0 as int)) as nat);
        assert(single.offset(c0) == a_val_at_bd_c0);

        // ═══ Step 4: rest_c.offset(x_rest) == A.offset(b_rest.offset(x_rest)) (IH) ═══
        // Need b_rest.offset(x_rest) >= 0 and < a.size()
        if b_rest.shape.len() > 0 {
            crate::proof::offset_lemmas::lemma_offset_nonneg(b_rest, x_rest);
            assert(b_rest.offset(x_rest) >= 0);
            // b.offset(x) == bd*c0 + b_rest.offset(x_rest) < a.size()
            // bd >= 0, c0 >= 0 => bd*c0 >= 0
            crate::proof::integer_helpers::lemma_mul_nonneg(bd, c0 as int);
            assert((b_rest.offset(x_rest) as nat) < a.size());
            lemma_compose_extended_correct(a, b_rest, x_rest);
        } else {
            crate::proof::offset_lemmas::lemma_offset_zero(a);
        }
        let rest_off = if b_rest.shape.len() > 0 { b_rest.offset(x_rest) as nat } else { 0nat };

        // ═══ Step 5: A.offset(bd*c0 + rest_off) == A.offset(bd*c0) + A.offset(rest_off) (condition 3) ═══
        // rest_off < a.size() (from step 4)
        // bd*c0 as nat + rest_off == B.offset(x) as nat < a.size() (from requires)
        assert((bd * (c0 as int)) as nat + rest_off < a.size()) by {
            crate::proof::integer_helpers::lemma_mul_nonneg(bd, c0 as int);
            if b_rest.shape.len() > 0 {
                assert(b.offset(x) as nat == (bd * (c0 as int)) as nat + rest_off);
            } else {
                assert(b.offset(x) as nat == (bd * (c0 as int)) as nat);
            }
        };
        assert(a.offset((bd * (c0 as int)) as nat + rest_off)
            == a.offset((bd * (c0 as int)) as nat) + a.offset(rest_off));

        // ═══ Step 6: Chain everything ═══
        // ce.offset(x) = single.offset(c0) + rest_c.offset(x_rest)     [step 2]
        //              = A.offset(bd*c0) + A.offset(rest_off)           [steps 3,4]
        //              = A.offset(bd*c0 + rest_off)                      [step 5]
        //              = A.offset(B.offset(x))                           [step 1]
        assert(b.offset(x) as nat == (bd * (c0 as int)) as nat + rest_off) by {
            crate::proof::integer_helpers::lemma_mul_nonneg(bd, c0 as int);
        };
    }
}

// ══════════════════════════════════════════════════════════════
// CuTe-style recursive composition correctness
// ══════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════
// CuTe-style recursive composition correctness
// ══════════════════════════════════════════════════════════════

/// Recursive admissibility: the compose_single spec is well-formed
/// and the straddle-case divisibility condition holds at every level.
pub open spec fn compose_single_admissible(
    a: LayoutSpec, b_shape: nat, b_stride: nat,
) -> bool
    decreases a.shape.len(),
{
    &&& a.valid()
    &&& a.shape.len() > 0
    &&& b_shape > 0
    &&& b_stride * b_shape <= shape_size(a.shape)
    &&& (a.shape.len() > 0 ==> {
        let m = a.shape.first();
        let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };
        if b_stride * b_shape <= m {
            true
        } else if b_stride > 0 && b_stride < m && m % b_stride == 0 {
            let q = m / b_stride;
            &&& b_shape % q == 0
            &&& (a_rest.shape.len() > 0 ==>
                compose_single_admissible(a_rest, b_shape / q, 1))
        } else if b_stride >= m && b_stride % m == 0 {
            a_rest.shape.len() > 0 ==>
                compose_single_admissible(a_rest, b_shape, b_stride / m)
        } else {
            false
        }
    })
}


/// compose_single always produces shape.len() == stride.len().
/// Uses minimal requires (no recursive admissibility predicate needed).
pub proof fn lemma_crs_len_match(a: LayoutSpec, b_shape: nat, b_stride: nat)
    requires a.valid(), b_shape > 0,
    ensures
        compose_single(a, b_shape, b_stride).shape.len()
            == compose_single(a, b_shape, b_stride).stride.len(),
    decreases a.shape.len(),
{
    if a.shape.len() == 0 {
    } else {
        let m = a.shape.first();
        let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };
        assert(a_rest.valid()) by {
            assert forall|i: int| 0 <= i < a_rest.shape.len()
            implies #[trigger] a_rest.shape[i] > 0 by { assert(a_rest.shape[i] == a.shape[i + 1]); };
        };
        if b_stride * b_shape <= m {
        } else if b_stride < m && m % b_stride == 0 && b_shape > 0 {
            let q = m / b_stride;
            assert(q > 0nat) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
                if q == 0 { vstd::arithmetic::mul::lemma_mul_basics(b_stride as int); }
            };
            assert(b_shape / q > 0nat) by {
                if b_shape / q == 0 {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_shape as int, q as int);
                    vstd::arithmetic::mul::lemma_mul_basics(q as int);
                    // b_shape < q = m/b_stride, so b_stride * b_shape < m, contradicting entry
                    assert(b_shape < q);
                    assert(b_stride * b_shape < b_stride * q) by (nonlinear_arith)
                        requires b_shape < q, b_stride > 0;
                    assert(b_stride * q == m) by {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
                    };
                }
            };
            lemma_crs_len_match(a_rest, b_shape / q, 1);
        } else if b_stride >= m && b_stride % m == 0 {
            lemma_crs_len_match(a_rest, b_shape, b_stride / m);
        }
    }
}

/// compose_single always produces valid shape (all entries > 0).
/// Uses minimal requires (no recursive admissibility predicate needed).
pub proof fn lemma_crs_shape_valid(a: LayoutSpec, b_shape: nat, b_stride: nat)
    requires a.valid(), b_shape > 0,
    ensures shape_valid(compose_single(a, b_shape, b_stride).shape),
    decreases a.shape.len(),
{
    if a.shape.len() == 0 {
        assert(shape_valid(seq![b_shape]));
    } else {
        let m = a.shape.first();
        let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };
        assert(a_rest.valid()) by {
            assert forall|i: int| 0 <= i < a_rest.shape.len()
            implies #[trigger] a_rest.shape[i] > 0 by { assert(a_rest.shape[i] == a.shape[i + 1]); };
        };
        if b_stride * b_shape <= m {
            assert(shape_valid(seq![b_shape]));
        } else if b_stride < m && m % b_stride == 0 && b_shape > 0 {
            let q = m / b_stride;
            assert(q > 0nat) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
                if q == 0 { vstd::arithmetic::mul::lemma_mul_basics(b_stride as int); }
            };
            let bq = b_shape / q;
            assert(bq > 0nat) by {
                if bq == 0 {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_shape as int, q as int);
                    vstd::arithmetic::mul::lemma_mul_basics(q as int);
                    assert(b_shape < q);
                    assert(b_stride * b_shape < b_stride * q) by (nonlinear_arith)
                        requires b_shape < q, b_stride > 0;
                    assert(b_stride * q == m) by {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
                    };
                }
            };
            lemma_crs_shape_valid(a_rest, bq, 1);
        } else if b_stride >= m && b_stride % m == 0 {
            lemma_crs_shape_valid(a_rest, b_shape, b_stride / m);
        } else {
            // Fallback: same as case 1
            assert(shape_valid(seq![b_shape]));
        }
    }
}

/// compose_single preserves total size: shape_size(result.shape) == b_shape.
/// (Requires admissibility to ensure straddle case has exact divisibility.)
pub proof fn lemma_crs_size(a: LayoutSpec, b_shape: nat, b_stride: nat)
    requires compose_single_admissible(a, b_shape, b_stride),
    ensures shape_size(compose_single(a, b_shape, b_stride).shape) == b_shape,
    decreases a.shape.len(),
{
    if a.shape.len() == 0 {
        assert(compose_single(a, b_shape, b_stride).shape =~= seq![b_shape]);
        lemma_shape_size_single(b_shape);
        return;
    }
    {
        let m = a.shape.first();
        let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };
        assert(a_rest.valid()) by {
            assert forall|i: int| 0 <= i < a_rest.shape.len()
            implies #[trigger] a_rest.shape[i] > 0 by { assert(a_rest.shape[i] == a.shape[i + 1]); };
        };
        if b_stride * b_shape <= m {
            assert(compose_single(a, b_shape, b_stride).shape =~= seq![b_shape]);
            lemma_shape_size_single(b_shape);
            return;
        } else if b_stride < m && m % b_stride == 0 && b_shape > 0 {
            // Unfold admissibility for straddle branch
            assert(b_stride > 0nat) by { if b_stride == 0 { assert(b_stride * b_shape == 0nat); } };
            let q = m / b_stride;
            assert(q > 0nat) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
                if q == 0 { vstd::arithmetic::mul::lemma_mul_basics(b_stride as int); }
            };
            // From admissibility: b_shape % q == 0
            assert(b_shape % q == 0nat);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_shape as int, q as int);
            let bq = b_shape / q;
            assert(b_shape == q * bq);
            assert(bq > 0nat) by { if bq == 0 { vstd::arithmetic::mul::lemma_mul_basics(q as int); } };
            // IH
            if a_rest.shape.len() > 0 {
                lemma_crs_size(a_rest, bq, 1);
            } else {
                lemma_shape_size_single(bq);
            }
            let rest = compose_single(a_rest, bq, 1);
            // result.shape =~= [q] ++ rest.shape
            assert(compose_single(a, b_shape, b_stride).shape
                =~= seq![q].add(rest.shape));
            // shape_size([q] ++ rest.shape) = q * shape_size(rest.shape) = q * bq
            crate::proof::product_lemmas::lemma_shape_size_append(seq![q], rest.shape);
            lemma_shape_size_single(q);
            // q * bq == b_shape
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_shape as int, q as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(q as int, bq as int);
            return;
        } else if b_stride >= m && b_stride % m == 0 {
            // Unfold admissibility for skip branch
            assert(!(b_stride * b_shape <= m));
            assert(!(b_stride > 0 && b_stride < m && m % b_stride == 0));
            assert(b_stride >= m && b_stride % m == 0);
            if a_rest.shape.len() > 0 {
                assert(compose_single_admissible(a_rest, b_shape, b_stride / m));
                lemma_crs_size(a_rest, b_shape, b_stride / m);
            } else {
                // 0-mode: result = (b_shape):(0), size = b_shape
                assert(compose_single(a_rest, b_shape, b_stride / m).shape =~= seq![b_shape]);
                lemma_shape_size_single(b_shape);
            }
            // Spec unfolds: compose_single(a,...) == compose_single(a_rest,...)
            let result = compose_single(a, b_shape, b_stride);
            let result_rest = compose_single(a_rest, b_shape, b_stride / m);
            assert(result.shape =~= result_rest.shape);
            return;
        } else {
            assert(compose_single(a, b_shape, b_stride).shape =~= seq![b_shape]);
            lemma_shape_size_single(b_shape);
            return;
        }
    }
}

/// Correctness of recursive single-mode composition:
///   compose_single(A, N, r).offset(x) == A.offset(r * x)
///
/// This is the key theorem that makes compose work for arbitrary A.
/// The proof strategy is induction on A's rank with 3 cases:
/// - Case 1 (within first mode): offset_within_first_mode + 1d_offset
/// - Case 3 (skip first mode): delinearize shows first coord = 0, IH handles rest
/// - Case 2 (straddle): modular scaling splits coordinates, concat-offset decomposes result
///
/// The proof requires `compose_single_admissible` which ensures:
/// - Straddle case has exact divisibility (b_shape % q == 0)
/// - Recursive admissibility holds at each level
///
/// Status: All building blocks proved (modular scaling, offset decomposition,
/// shape validity). The proof body needs z3 to unfold the recursive admissibility
/// predicate at each level, which requires careful assertion ordering.
// TODO: Close this proof by either:
// 1. Inlining the admissibility conditions into requires (avoids recursive predicate unfolding)
// 2. Adding explicit "reveal" hints for the recursive predicate
// 3. Using a non-recursive admissibility check with a fuel-based approach
pub proof fn lemma_compose_recursive_single_correct(
    a: LayoutSpec, b_shape: nat, b_stride: nat, x: nat,
)
    requires
        compose_single_admissible(a, b_shape, b_stride),
        x < b_shape,
    ensures
        compose_single(a, b_shape, b_stride).offset(x)
            == a.offset(b_stride * x),
    decreases a.shape.len(),
{
    let m = a.shape.first();
    let d = a.stride.first();
    let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };

    // ═══════════════════════════════════════════════════
    // Case 1: B fits entirely within A's first mode
    // ═══════════════════════════════════════════════════
    if b_stride * b_shape <= m {
        if b_stride == 0 {
            assert(b_stride * x == 0nat);
        } else {
            assert(b_stride * x < b_stride * b_shape) by (nonlinear_arith)
                requires x < b_shape, b_stride > 0;
        }
        lemma_offset_within_first_mode(&a, b_stride * x);
        lemma_1d_offset(b_shape, (b_stride as int) * d, x);
        assert((x as int) * ((b_stride as int) * d) == ((b_stride * x) as int) * d)
            by (nonlinear_arith);
        return;
    }

    // ═══════════════════════════════════════════════════
    // Case 3: B's stride skips A's first mode entirely
    // ═══════════════════════════════════════════════════
    if b_stride >= m && b_stride % m == 0 {
        let r2 = b_stride / m;
        assert(b_stride > 0nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_stride as int, m as int);
        assert(b_stride == m * r2);

        assert(a_rest.valid()) by {
            assert forall|i: int| 0 <= i < a_rest.shape.len()
            implies #[trigger] a_rest.shape[i] > 0 by { assert(a_rest.shape[i] == a.shape[i + 1]); };
        };

        // Recursive admissibility for a_rest
        // (unfold compose_single_admissible: we're in the skip branch)
        assert(!(b_stride * b_shape <= m));
        assert(!(b_stride > 0 && b_stride < m && m % b_stride == 0));

        // Size bound for recursive call
        crate::runtime::shape_helpers::lemma_shape_size_split(a.shape, 1);
        assert(a.shape.take(1) =~= seq![m]);
        lemma_shape_size_single(m);
        assert(r2 * b_shape <= shape_size(a_rest.shape)) by (nonlinear_arith)
            requires b_stride * b_shape <= m * shape_size(a_rest.shape), b_stride == m * r2, m > 0;

        // A.offset(bx) decomposition (shared between branches)
        let bx = b_stride * x;
        assert(bx < shape_size(a.shape)) by {
            assert(b_stride * x < b_stride * b_shape) by (nonlinear_arith)
                requires x < b_shape, b_stride > 0;
        };
        assert(a.shape =~= seq![m].add(a_rest.shape));
        assert(a.stride =~= seq![d].add(a_rest.stride));
        lemma_delinearize_concat(bx, seq![m], a_rest.shape);
        lemma_delinearize_len(bx % m, seq![m]);
        lemma_delinearize_len(bx / m, a_rest.shape);
        lemma_dot_product_append(
            delinearize(bx % m, seq![m]), delinearize(bx / m, a_rest.shape),
            seq![d], a_rest.stride,
        );
        let r2x = r2 * x;
        assert(bx == m * r2x) by {
            vstd::arithmetic::mul::lemma_mul_is_associative(m as int, r2 as int, x as int);
        };
        vstd::arithmetic::mul::lemma_mul_is_commutative(m as int, r2x as int);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(r2x as int, m as int);
        assert(bx % m == 0nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(bx as int, m as int, r2x as int, 0int);
        assert(bx / m == r2x);
        crate::proof::offset_lemmas::lemma_offset_zero(LayoutSpec { shape: seq![m], stride: seq![d] });
        assert(a.offset(bx) == a_rest.offset(r2x));

        // Spec unfolding
        let result = compose_single(a, b_shape, b_stride);
        let result_rest = compose_single(a_rest, b_shape, r2);
        assert(result.shape =~= result_rest.shape);
        assert(result.stride =~= result_rest.stride);
        lemma_offset_eq_layout(result.shape, result.stride, result_rest.shape, result_rest.stride, x);
        assert(result.offset(x) == result_rest.offset(x));

        // Complete proof per branch
        if a_rest.shape.len() > 0 {
            lemma_compose_recursive_single_correct(a_rest, b_shape, r2, x);
            // IH: result_rest.offset(x) == a_rest.offset(r2*x) == a_rest.offset(r2x)
            // Chain: result.offset(x) == result_rest.offset(x) == a_rest.offset(r2x) == a.offset(bx)
            return;
        } else {
            // 0-mode a_rest: result_rest = (b_shape):(0), offset = 0
            // a_rest.offset(r2x) = 0 (0-mode layout)
            crate::proof::offset_lemmas::lemma_offset_zero(a_rest);
            // result_rest.offset(x) = x * 0 = 0
            lemma_1d_offset(b_shape, 0int, x);
            return;
        }
    }

    // ═══════════════════════════════════════════════════
    // Case 2: B straddles A's first mode boundary
    // ═══════════════════════════════════════════════════
    if b_stride > 0 && b_stride < m && m % b_stride == 0 {
        let q = m / b_stride;
        assert(q > 0nat) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
            if q == 0 { vstd::arithmetic::mul::lemma_mul_basics(b_stride as int); }
        };
        assert(b_stride * q == m) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
        };

        // Unfold admissibility: we're in the straddle branch
        assert(!(b_stride * b_shape <= m));
        // From admissibility straddle branch: b_shape % q == 0
        assert(b_shape % q == 0nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_shape as int, q as int);
        let bq = b_shape / q;
        assert(b_shape == q * bq);
        assert(bq > 0nat) by { if bq == 0 { vstd::arithmetic::mul::lemma_mul_basics(q as int); } };

        let x_inner = x % q;
        let x_outer = x / q;
        let bx = b_stride * x;

        crate::proof::integer_helpers::lemma_mod_bound(x, q);
        assert(x < q * bq);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, q, bq);

        assert(a_rest.valid()) by {
            assert forall|i: int| 0 <= i < a_rest.shape.len()
            implies #[trigger] a_rest.shape[i] > 0 by { assert(a_rest.shape[i] == a.shape[i + 1]); };
        };

        // Size bound for recursive call: bq <= shape_size(a_rest.shape)
        crate::runtime::shape_helpers::lemma_shape_size_split(a.shape, 1);
        assert(a.shape.take(1) =~= seq![m]);
        lemma_shape_size_single(m);
        assert(bq <= shape_size(a_rest.shape)) by {
            assert(b_stride * b_shape == m * bq) by {
                vstd::arithmetic::mul::lemma_mul_is_associative(b_stride as int, q as int, bq as int);
            };
            assert(m * bq <= m * shape_size(a_rest.shape));
            assert(bq <= shape_size(a_rest.shape)) by (nonlinear_arith)
                requires m * bq <= m * shape_size(a_rest.shape), m > 0;
        };

        // IH + complete proof per branch
        let rest_layout = compose_single(a_rest, bq, 1);

        // Shared proof: modular scaling + A.offset decomposition + inner offset
        // (moved into a macro-like block that both branches use)
        // Instead, duplicate into each branch to avoid merge issues:

        if a_rest.shape.len() > 0 {
            // ── Branch A: a_rest has modes ──
            assert(compose_single_admissible(a_rest, bq, 1));
            lemma_compose_recursive_single_correct(a_rest, bq, 1, x_outer);
            // IH: rest_layout.offset(x_outer) == a_rest.offset(1 * x_outer) == a_rest.offset(x_outer)
            assert(1 * x_outer == x_outer) by (nonlinear_arith);

            crate::proof::integer_helpers::lemma_mod_scale(x, b_stride, q);
            crate::proof::integer_helpers::lemma_div_scale(x, b_stride, q);
            assert(b_stride * x_inner == bx % m);
            assert(x_outer == bx / m);
            assert(b_stride * x_inner < m) by (nonlinear_arith)
                requires x_inner < q, b_stride * q == m, b_stride > 0;
            assert(bx < shape_size(a.shape)) by {
                assert(b_stride * x < b_stride * b_shape) by (nonlinear_arith)
                    requires x < b_shape, b_stride > 0;
            };

            assert(a.shape =~= seq![m].add(a_rest.shape));
            assert(a.stride =~= seq![d].add(a_rest.stride));
            lemma_delinearize_concat(bx, seq![m], a_rest.shape);
            lemma_delinearize_len(bx % m, seq![m]);
            lemma_delinearize_len(bx / m, a_rest.shape);
            lemma_dot_product_append(
                delinearize(bx % m, seq![m]), delinearize(bx / m, a_rest.shape),
                seq![d], a_rest.stride,
            );
            crate::proof::integer_helpers::lemma_mod_bound(bx, m);
            lemma_offset_within_first_mode(
                &LayoutSpec { shape: seq![m], stride: seq![d] }, bx % m,
            );
            lemma_1d_offset(q, (b_stride as int) * d, x_inner);
            assert(x_inner as int * ((b_stride as int) * d) == (b_stride * x_inner) as int * d)
                by (nonlinear_arith);

            let result = compose_single(a, b_shape, b_stride);
            let inner_layout = LayoutSpec { shape: seq![q], stride: seq![(b_stride as int) * d] };

            // Prove concat-offset decomposition: result.offset(x) == inner.offset(x_inner) + rest.offset(x_outer)
            assert(result.shape =~= inner_layout.shape.add(rest_layout.shape));
            assert(result.stride =~= inner_layout.stride.add(rest_layout.stride));
            assert(shape_valid(inner_layout.shape));
            // rest_layout shape valid + len match from recursive structure
            assert(shape_valid(rest_layout.shape)) by {
                assert(compose_single_admissible(a_rest, bq, 1));
                lemma_crs_shape_valid(a_rest, bq, 1);
            };
            assert(rest_layout.shape.len() == rest_layout.stride.len()) by {
                assert(compose_single_admissible(a_rest, bq, 1));
                lemma_crs_len_match(a_rest, bq, 1);
            };
            assert(shape_size(inner_layout.shape) == q) by { lemma_shape_size_single(q); };
            crate::proof::product_lemmas::lemma_shape_size_append(inner_layout.shape, rest_layout.shape);
            // x < shape_size(result.shape) from size preservation:
            // shape_size(result.shape) = q * shape_size(rest.shape) = q * bq = b_shape > x
            lemma_crs_size(a_rest, bq, 1);
            // shape_size(rest.shape) == bq, so shape_size(result.shape) == q * bq == b_shape
            lemma_delinearize_concat(x, inner_layout.shape, rest_layout.shape);
            lemma_delinearize_len(x_inner, inner_layout.shape);
            lemma_delinearize_len(x_outer, rest_layout.shape);
            lemma_dot_product_append(
                delinearize(x_inner, inner_layout.shape), delinearize(x_outer, rest_layout.shape),
                inner_layout.stride, rest_layout.stride,
            );

            return;
        } else {
            // ── Branch B: a_rest has 0 modes ──
            crate::proof::offset_lemmas::lemma_offset_zero(a_rest);

            crate::proof::integer_helpers::lemma_mod_scale(x, b_stride, q);
            crate::proof::integer_helpers::lemma_div_scale(x, b_stride, q);
            assert(b_stride * x_inner == bx % m);
            assert(x_outer == bx / m);
            assert(b_stride * x_inner < m) by (nonlinear_arith)
                requires x_inner < q, b_stride * q == m, b_stride > 0;
            assert(bx < shape_size(a.shape)) by {
                assert(b_stride * x < b_stride * b_shape) by (nonlinear_arith)
                    requires x < b_shape, b_stride > 0;
            };

            assert(a.shape =~= seq![m].add(a_rest.shape));
            assert(a.stride =~= seq![d].add(a_rest.stride));
            lemma_delinearize_concat(bx, seq![m], a_rest.shape);
            lemma_delinearize_len(bx % m, seq![m]);
            lemma_delinearize_len(bx / m, a_rest.shape);
            lemma_dot_product_append(
                delinearize(bx % m, seq![m]), delinearize(bx / m, a_rest.shape),
                seq![d], a_rest.stride,
            );
            crate::proof::integer_helpers::lemma_mod_bound(bx, m);
            lemma_offset_within_first_mode(
                &LayoutSpec { shape: seq![m], stride: seq![d] }, bx % m,
            );
            lemma_1d_offset(q, (b_stride as int) * d, x_inner);
            assert(x_inner as int * ((b_stride as int) * d) == (b_stride * x_inner) as int * d)
                by (nonlinear_arith);

            let result = compose_single(a, b_shape, b_stride);
            let inner_layout = LayoutSpec { shape: seq![q], stride: seq![(b_stride as int) * d] };
            // rest_layout for 0-mode a_rest has stride 0
            assert(rest_layout.offset(x_outer) == 0int) by {
                lemma_1d_offset(bq, 0int, x_outer);
            };
            // Concat-offset decomposition (Branch B: 0-mode rest)
            assert(result.shape =~= inner_layout.shape.add(rest_layout.shape));
            assert(result.stride =~= inner_layout.stride.add(rest_layout.stride));
            assert(shape_valid(inner_layout.shape));
            // rest_layout for 0-mode a_rest = (bq):(0), valid shape
            assert(shape_valid(rest_layout.shape));
            assert(rest_layout.shape.len() == rest_layout.stride.len());
            assert(shape_size(inner_layout.shape) == q) by { lemma_shape_size_single(q); };
            crate::proof::product_lemmas::lemma_shape_size_append(inner_layout.shape, rest_layout.shape);
            assert(x < shape_size(result.shape)) by {
                // rest = (bq):(0), size = bq. result size = q * bq = b_shape. x < b_shape.
                lemma_shape_size_single(bq);
            };
            lemma_delinearize_concat(x, inner_layout.shape, rest_layout.shape);
            lemma_delinearize_len(x_inner, inner_layout.shape);
            lemma_delinearize_len(x_outer, rest_layout.shape);
            lemma_dot_product_append(
                delinearize(x_inner, inner_layout.shape), delinearize(x_outer, rest_layout.shape),
                inner_layout.stride, rest_layout.stride,
            );
            return;
        }
    }

    // Case 4: unreachable from admissibility
    assert(false);
}

} // verus!
