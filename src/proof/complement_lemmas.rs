use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::proof::shape_lemmas::*;
use crate::proof::integer_helpers::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Complement validity
// ══════════════════════════════════════════════════════════════

/// The complement layout has rank k+1 (one more than A).
pub proof fn lemma_complement_rank(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures
        complement(a, m).shape.len() == a.shape.len() + 1,
        complement(a, m).stride.len() == a.shape.len() + 1,
        complement(a, m).shape.len() == complement(a, m).stride.len(),
{
}

// ══════════════════════════════════════════════════════════════
// Helper: if a divides b and a > 0 and b > 0, then b/a > 0
// ══════════════════════════════════════════════════════════════

pub proof fn lemma_div_positive_when_divides(a: int, b: int)
    requires a > 0, b > 0, b % a == 0,
    ensures b / a > 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, a);
    // b == a * (b/a) + b%a == a * (b/a)
    // b > 0 and a > 0, so b/a > 0 (otherwise a * 0 == 0 != b)
    if b / a <= 0 {
        vstd::arithmetic::mul::lemma_mul_nonnegative(a, b / a);
        assert(a * (b / a) <= 0);
        assert(false);
    }
}

// ══════════════════════════════════════════════════════════════
// Complement shape validity
// ══════════════════════════════════════════════════════════════

/// All complement shape entries are positive (the complement layout has a valid shape).
pub proof fn lemma_complement_shape_valid(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures shape_valid(complement_shape(a, m)),
{
    let cs = complement_shape(a, m);
    let k = a.shape.len();

    assert forall|i: int| 0 <= i < cs.len() implies #[trigger] cs[i] > 0 by {
        if i == 0 {
            // cs[0] = a.stride[0] > 0 (from admissibility: a.stride[0] > 0)
            assert(cs[0] == a.stride[0] as nat);
        } else if i < k as int {
            // cs[i] = a.stride[i] / stride_product(a, i-1)
            // tractability: stride_product(a, i-1) divides a.stride[i]
            // and both are positive, so quotient > 0
            let sp = stride_product(a, i - 1);
            assert(sp > 0) by {
                // sp = a.shape[i-1] * a.stride[i-1]
                // a.shape[i-1] > 0 (valid shape), a.stride[i-1] >= 0 (non_negative_strides)
                // For sorted: a.stride[i-1] >= a.stride[0] > 0
                assert(a.stride[i - 1] >= a.stride[0]);
                lemma_mul_pos(a.shape[i - 1], a.stride[i - 1] as nat);
            };
            // From tractability at index i-1:
            // a.stride[(i-1)+1] % ((a.shape[i-1] as int) * a.stride[i-1]) == 0
            // i.e., a.stride[i] % stride_product(a, i-1) == 0
            let ti = i - 1;
            assert(0 <= ti < a.stride.len() as int - 1);
            assert(a.tractable_at(ti));
            let product_ti = (a.shape[ti] as int) * a.stride[ti];
            assert(a.stride[ti + 1] % product_ti == 0);
            assert(sp == product_ti);
            assert(a.stride[i] % sp == 0);
            assert(a.stride[i] >= a.stride[0]);
            assert(a.stride[i] > 0);
            lemma_div_positive_when_divides(sp, a.stride[i]);
            assert(cs[i] == (a.stride[i] / sp) as nat);
        } else {
            // i == k: cs[k] = M / stride_product(a, k-1)
            let sp = stride_product(a, (k - 1) as int);
            assert(sp > 0) by {
                assert(sp == (a.shape.last() as int) * a.stride.last());
                assert(a.stride.last() >= a.stride[0]);
                lemma_mul_pos(a.shape.last(), a.stride.last() as nat);
            };
            assert((m as int) % sp == 0);
            lemma_div_positive_when_divides(sp, m as int);
            assert(cs[i] == ((m as int) / sp) as nat);
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Complement size for 1D layout
// ══════════════════════════════════════════════════════════════

/// For a 1D layout A = (M_0):(d_0), complement size * A size == M.
pub proof fn lemma_complement_size_1d(a: &LayoutSpec, m: nat)
    requires
        complement_admissible(a, m),
        a.shape.len() == 1,
    ensures ({
        let c = complement(a, m);
        // We state it as a product identity rather than division
        // to avoid reasoning about nat division
        shape_size(c.shape) * shape_size(a.shape) == m
    }),
{
    let c = complement(a, m);
    let cs = complement_shape(a, m);
    let m0 = a.shape[0];
    let d0 = a.stride[0];
    let sp0 = (m0 as int) * d0;

    // sp0 > 0
    assert(sp0 > 0) by {
        lemma_mul_pos(m0, d0 as nat);
    };

    // M % sp0 == 0 (from admissibility)
    assert((m as int) % sp0 == 0);

    // M / sp0 > 0
    lemma_div_positive_when_divides(sp0, m as int);

    // cs = complement_shape(a, m) has length 2
    assert(cs.len() == 2);
    let c0 = cs[0]; // = d0
    let c1 = cs[1]; // = M / sp0
    assert(c0 == d0 as nat);
    assert(c1 == ((m as int) / sp0) as nat);
    assert(c1 > 0);

    // shape_size(cs):
    // cs is Seq::new(2, f). We need shape_size of this.
    // shape_size(cs) = cs.first() * shape_size(cs.skip(1))
    //               = c0 * shape_size(cs.skip(1))
    // cs.skip(1) has length 1, first element = c1
    // shape_size(cs.skip(1)) = c1 * shape_size(cs.skip(1).skip(1))
    //                        = c1 * 1 = c1

    // Actually, let me just unfold shape_size for length 2 directly
    assert(cs.first() == c0);
    assert(shape_size(cs) == c0 * shape_size(cs.skip(1)));
    assert(cs.skip(1).len() == 1);
    assert(cs.skip(1).first() == c1);
    assert(shape_size(cs.skip(1)) == c1 * shape_size(cs.skip(1).skip(1)));
    assert(cs.skip(1).skip(1).len() == 0);
    assert(shape_size(cs.skip(1).skip(1)) == 1);

    // shape_size(cs.skip(1)) = c1 * 1 = c1
    vstd::arithmetic::mul::lemma_mul_basics(c1 as int);
    assert(shape_size(cs.skip(1)) == c1);

    // shape_size(cs) = c0 * c1
    assert(shape_size(cs) == c0 * shape_size(cs.skip(1)));
    assert(shape_size(cs) == c0 * c1);

    // shape_size(a.shape) = m0 * 1 = m0
    assert(shape_size(a.shape) == m0 * shape_size(a.shape.skip(1)));
    assert(a.shape.skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(m0 as int);
    assert(shape_size(a.shape) == m0);

    // Now: shape_size(cs) * shape_size(a.shape) = d0 * (M/sp0) * m0
    // sp0 = m0 * d0, so d0 * (M/sp0) * m0 = (M/sp0) * (d0 * m0) = (M/sp0) * sp0 = M

    // (M / sp0) * sp0 == M
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, sp0);
    assert(m as int == sp0 * ((m as int) / sp0));
    vstd::arithmetic::mul::lemma_mul_is_commutative(sp0, (m as int) / sp0);
    assert((m as int) / sp0 * sp0 == m as int);

    // d0 * (M/sp0) * m0 == (M/sp0) * (d0 * m0) == (M/sp0) * sp0 == M
    vstd::arithmetic::mul::lemma_mul_is_commutative(d0 as int, (m as int) / sp0);
    // c0 * c1 = d0 * (M/sp0) = (M/sp0) * d0
    vstd::arithmetic::mul::lemma_mul_is_associative((m as int) / sp0, d0 as int, m0 as int);
    // (M/sp0) * d0 * m0 = (M/sp0) * (d0 * m0) = (M/sp0) * sp0 = M
    vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, d0 as int);
    // d0 * m0 == m0 * d0 == sp0
    assert((c0 * c1) as int * (m0 as int) == m as int);
}

// ══════════════════════════════════════════════════════════════
// General complement size
// ══════════════════════════════════════════════════════════════

/// Telescoping invariant: P(j+1) * Q(j) == a.stride[j] for 0 <= j < k.
/// Here P(j) = shape_size(complement_shape.take(j)) and Q(j) = shape_size(a.shape.take(j)).
proof fn lemma_complement_size_step(a: &LayoutSpec, m: nat, j: nat)
    requires
        complement_admissible(a, m),
        j < a.shape.len(),
    ensures
        shape_size(complement_shape(a, m).take((j + 1) as int))
            * shape_size(a.shape.take(j as int))
            == a.stride[j as int] as nat,
    decreases j,
{
    let cs = complement_shape(a, m);
    let k = a.shape.len();
    lemma_complement_shape_valid(a, m);
    lemma_complement_rank(a, m);

    // All strides positive (sorted, stride[0] > 0)
    assert(a.stride[j as int] >= a.stride[0]);
    assert(a.stride[j as int] > 0);

    if j == 0 {
        // P(1) = shape_size(cs.take(1)) = cs[0]
        // Q(0) = shape_size(a.shape.take(0)) = 1

        // shape_size(take(0)) = shape_size(empty) = 1
        assert(a.shape.take(0) =~= Seq::<nat>::empty());
        assert(shape_size(a.shape.take(0)) == 1nat);

        // shape_size(take(1)) = cs[0] (single element)
        assert(cs.take(1).len() == 1);
        assert(cs.take(1).first() == cs[0]);
        assert(cs.take(1).skip(1) =~= Seq::<nat>::empty());
        assert(shape_size(cs.take(1)) == cs[0] * 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(cs[0] as int);

        // cs[0] = a.stride[0] as nat
        assert(cs[0] == a.stride[0] as nat);
    } else {
        // IH: P(j) * Q(j-1) = a.stride[j-1]
        lemma_complement_size_step(a, m, (j - 1) as nat);

        let pj = shape_size(cs.take(j as int));
        let qjm1 = shape_size(a.shape.take((j - 1) as int));
        assert(pj * qjm1 == a.stride[(j - 1) as int] as nat);

        // P(j+1) = P(j) * cs[j]  (via shape_size_take_step)
        crate::runtime::shape_helpers::lemma_shape_size_take_step(cs, j);
        let pj1 = shape_size(cs.take((j + 1) as int));
        assert(pj1 == pj * cs[j as int]);

        // Q(j) = Q(j-1) * a.shape[j-1]  (via shape_size_take_step)
        assert(a.valid());
        crate::runtime::shape_helpers::lemma_shape_size_take_step(a.shape, (j - 1) as nat);
        let qj = shape_size(a.shape.take(j as int));
        assert(qj == qjm1 * a.shape[(j - 1) as int]);

        // P(j+1) * Q(j) = pj * cs[j] * qjm1 * a.shape[j-1]
        //                = (pj * qjm1) * cs[j] * a.shape[j-1]
        //                = a.stride[j-1] * cs[j] * a.shape[j-1]
        let dj_1 = a.stride[(j - 1) as int] as nat;
        let mj_1 = a.shape[(j - 1) as int];
        let csj = cs[j as int];

        // cs[j] = a.stride[j] / stride_product(a, j-1)
        // stride_product(a, j-1) = a.shape[j-1] * a.stride[j-1]
        let sp = stride_product(a, (j - 1) as int);
        assert(sp == (mj_1 as int) * a.stride[(j - 1) as int]);
        assert(sp > 0) by {
            lemma_stride_product_positive(a, (j - 1) as int);
        };

        // From tractability: stride[j] % sp == 0
        assert(a.tractable_at((j - 1) as int));
        assert(a.stride[j as int] % sp == 0);

        // cs[j] = a.stride[j] / sp
        assert(csj == (a.stride[j as int] / sp) as nat);

        // (a.stride[j] / sp) * sp == a.stride[j]
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a.stride[j as int], sp);
        vstd::arithmetic::mul::lemma_mul_is_commutative(sp, a.stride[j as int] / sp);
        assert((a.stride[j as int] / sp) * sp == a.stride[j as int]);

        // Now compute P(j+1) * Q(j):
        // = pj * csj * qjm1 * mj_1
        // = (pj * qjm1) * (csj * mj_1)
        // = dj_1 * (csj * mj_1)
        // = dj_1 * mj_1 * csj    [rearranging]
        // = sp * csj              [since sp = mj_1 * dj_1]
        // = sp * (stride[j] / sp) [since csj = stride[j] / sp]
        // = stride[j]

        // We need to connect the nat multiplications.
        // pj1 * qj = (pj * csj) * (qjm1 * mj_1)
        // Since all are nats, we can use associativity/commutativity.
        vstd::arithmetic::mul::lemma_mul_is_associative(pj as int, csj as int, qjm1 as int);
        // pj * csj * qjm1 = pj * (csj * qjm1)
        vstd::arithmetic::mul::lemma_mul_is_commutative(csj as int, qjm1 as int);
        // csj * qjm1 = qjm1 * csj
        vstd::arithmetic::mul::lemma_mul_is_associative(pj as int, qjm1 as int, csj as int);
        // pj * qjm1 * csj = pj * (qjm1 * csj) = (pj * qjm1) * csj = dj_1 * csj

        // So pj1 * qj = (pj * csj) * (qjm1 * mj_1)
        // We want to show = dj_1 * csj * mj_1 = sp * csj = stride[j]

        // pj1 * qj = pj * csj * qjm1 * mj_1
        // Let's factor as: (pj * qjm1) * (csj * mj_1)
        // = dj_1 * (csj * mj_1)

        // csj * mj_1 as nat = (stride[j] / sp) * mj_1
        // dj_1 * csj * mj_1 = dj_1 * mj_1 * csj = sp_as_nat * csj
        // = (stride[j] / sp) * sp = stride[j]

        assert(pj1 * qj == pj * csj * (qjm1 * mj_1)) by {
            vstd::arithmetic::mul::lemma_mul_is_associative(
                (pj * csj) as int, qjm1 as int, mj_1 as int,
            );
        };
        assert(pj * csj * (qjm1 * mj_1) == (pj * qjm1) * (csj * mj_1)) by {
            // pj * csj * (qjm1 * mj_1)
            // = (pj * csj) * (qjm1 * mj_1)
            // Want: = (pj * qjm1) * (csj * mj_1)
            // Both = pj * qjm1 * csj * mj_1 by associativity/commutativity
            vstd::arithmetic::mul::lemma_mul_is_associative(pj as int, csj as int, (qjm1 * mj_1) as int);
            // pj * csj * (qjm1 * mj_1) = pj * (csj * (qjm1 * mj_1))
            vstd::arithmetic::mul::lemma_mul_is_associative(csj as int, qjm1 as int, mj_1 as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(csj as int, qjm1 as int);
            vstd::arithmetic::mul::lemma_mul_is_associative(qjm1 as int, csj as int, mj_1 as int);
            // csj * qjm1 * mj_1 = qjm1 * csj * mj_1 = qjm1 * (csj * mj_1)
            // So pj * (csj * qjm1 * mj_1) = pj * (qjm1 * (csj * mj_1))
            // = (pj * qjm1) * (csj * mj_1)
            vstd::arithmetic::mul::lemma_mul_is_associative(pj as int, qjm1 as int, (csj * mj_1) as int);
        };
        // (pj * qjm1) * (csj * mj_1) = dj_1 * (csj * mj_1)
        assert((pj * qjm1) * (csj * mj_1) == dj_1 * (csj * mj_1));

        // csj * mj_1 = (stride[j] / sp) * mj_1
        // dj_1 * (stride[j] / sp) * mj_1 = dj_1 * mj_1 * (stride[j] / sp)
        //                                 = sp * (stride[j] / sp)   [since sp = mj_1 * dj_1]
        vstd::arithmetic::mul::lemma_mul_is_commutative(csj as int, mj_1 as int);
        assert(dj_1 * (mj_1 * csj) == dj_1 * mj_1 * csj) by {
            vstd::arithmetic::mul::lemma_mul_is_associative(dj_1 as int, mj_1 as int, csj as int);
        };
        // dj_1 * mj_1 = sp (as nat)
        vstd::arithmetic::mul::lemma_mul_is_commutative(mj_1 as int, dj_1 as int);
        assert((dj_1 * mj_1) as int == sp);
        // sp * csj = sp * (stride[j] / sp) = stride[j]
        assert((dj_1 * mj_1) * csj == a.stride[j as int] as nat) by {
            assert(csj as int == a.stride[j as int] / sp);
            assert(((dj_1 * mj_1) * csj) as int == sp * (a.stride[j as int] / sp));
            assert(sp * (a.stride[j as int] / sp) == a.stride[j as int]);
        };
    }
}

/// The complement size satisfies: size(complement) * size(B) == M.
pub proof fn lemma_complement_size(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures
        shape_size(complement_shape(a, m)) * shape_size(a.shape) == m,
{
    let cs = complement_shape(a, m);
    let k = a.shape.len();
    lemma_complement_shape_valid(a, m);
    lemma_complement_rank(a, m);

    // At j = k-1: P(k) * Q(k-1) = a.stride[k-1]
    lemma_complement_size_step(a, m, (k - 1) as nat);

    let pk = shape_size(cs.take(k as int));
    let qkm1 = shape_size(a.shape.take((k - 1) as int));
    let dk_1 = a.stride[(k - 1) as int] as nat;
    assert(pk * qkm1 == dk_1);

    // P(k+1) = P(k) * cs[k]
    crate::runtime::shape_helpers::lemma_shape_size_take_step(cs, k as nat);
    let pk1 = shape_size(cs.take((k + 1) as int));
    assert(pk1 == pk * cs[k as int]);

    // Q(k) = Q(k-1) * a.shape[k-1]
    crate::runtime::shape_helpers::lemma_shape_size_take_step(a.shape, (k - 1) as nat);
    let qk = shape_size(a.shape.take(k as int));
    assert(qk == qkm1 * a.shape[(k - 1) as int]);

    // cs.take(k+1) =~= cs (full sequence)
    assert(cs.take((k + 1) as int) =~= cs);
    // a.shape.take(k) =~= a.shape (full sequence)
    assert(a.shape.take(k as int) =~= a.shape);

    // cs[k] = m / stride_product(a, k-1)
    let sp_last = stride_product(a, (k - 1) as int);
    assert(sp_last == (a.shape[(k - 1) as int] as int) * a.stride[(k - 1) as int]);
    assert(sp_last > 0) by {
        lemma_stride_product_positive(a, (k - 1) as int);
    };
    assert((m as int) % sp_last == 0);
    assert(cs[k as int] == ((m as int) / sp_last) as nat);

    // P(k+1) * Q(k) = pk * cs[k] * qkm1 * a.shape[k-1]
    //               = (pk * qkm1) * (cs[k] * a.shape[k-1])
    //               = dk_1 * (cs[k] * a.shape[k-1])
    let mk_1 = a.shape[(k - 1) as int];
    let csk = cs[k as int];

    // Same factoring as in step:
    assert(pk1 * qk == pk * csk * (qkm1 * mk_1)) by {
        vstd::arithmetic::mul::lemma_mul_is_associative(
            (pk * csk) as int, qkm1 as int, mk_1 as int,
        );
    };
    assert(pk * csk * (qkm1 * mk_1) == (pk * qkm1) * (csk * mk_1)) by {
        vstd::arithmetic::mul::lemma_mul_is_associative(pk as int, csk as int, (qkm1 * mk_1) as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(csk as int, qkm1 as int, mk_1 as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(csk as int, qkm1 as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(qkm1 as int, csk as int, mk_1 as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(pk as int, qkm1 as int, (csk * mk_1) as int);
    };
    assert((pk * qkm1) * (csk * mk_1) == dk_1 * (csk * mk_1));

    // dk_1 * mk_1 = sp_last
    vstd::arithmetic::mul::lemma_mul_is_commutative(mk_1 as int, dk_1 as int);
    assert((dk_1 * mk_1) as int == sp_last);

    // dk_1 * (csk * mk_1) = dk_1 * mk_1 * csk = sp_last * csk
    vstd::arithmetic::mul::lemma_mul_is_commutative(csk as int, mk_1 as int);
    assert(dk_1 * (mk_1 * csk) == dk_1 * mk_1 * csk) by {
        vstd::arithmetic::mul::lemma_mul_is_associative(dk_1 as int, mk_1 as int, csk as int);
    };

    // sp_last * csk = sp_last * (m / sp_last) = m
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, sp_last);
    vstd::arithmetic::mul::lemma_mul_is_commutative(sp_last, (m as int) / sp_last);
    assert(((m as int) / sp_last) * sp_last == m as int);
    assert(((dk_1 * mk_1) * csk) as int == m as int);
}

// ══════════════════════════════════════════════════════════════
// Complement strides are ordered
// ══════════════════════════════════════════════════════════════

/// Complement stride[0] == 1.
pub proof fn lemma_complement_stride_first(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).stride[0] == 1,
{
}

/// Complement stride[i+1] = stride_product(a, i) for i >= 0.
pub proof fn lemma_complement_stride_rest(a: &LayoutSpec, m: nat, i: int)
    requires complement_admissible(a, m), 0 <= i < a.shape.len() as int,
    ensures complement(a, m).stride[i + 1] == stride_product(a, i),
{
}

// ══════════════════════════════════════════════════════════════
// Complement validity (full)
// ══════════════════════════════════════════════════════════════

/// The complement layout is valid (shape/stride lengths match, all shapes > 0).
pub proof fn lemma_complement_valid(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).valid(),
{
    lemma_complement_rank(a, m);
    lemma_complement_shape_valid(a, m);
}

// ══════════════════════════════════════════════════════════════
// Complement has all-positive strides
// ══════════════════════════════════════════════════════════════

/// Helper: stride_product(a, i) > 0 for a valid sorted layout with stride[0] > 0.
proof fn lemma_stride_product_positive(a: &LayoutSpec, i: int)
    requires
        a.valid(),
        a.is_sorted(),
        a.stride[0] > 0,
        a.shape.len() > 0,
        0 <= i < a.shape.len() as int,
    ensures stride_product(a, i) > 0,
{
    // stride_product(a, i) = shape[i] * stride[i]
    // shape[i] > 0 (valid), stride[i] >= stride[0] > 0 (sorted, stride[0] > 0)
    assert(a.stride[i] >= a.stride[0]);
    assert(a.stride[i] > 0);
    lemma_mul_pos(a.shape[i], a.stride[i] as nat);
}

/// All complement strides are positive.
pub proof fn lemma_complement_positive_strides(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures
        forall|i: int| 0 <= i < complement(a, m).stride.len()
            ==> #[trigger] complement(a, m).stride[i] > 0,
{
    let c = complement(a, m);
    lemma_complement_rank(a, m);

    assert forall|i: int| 0 <= i < c.stride.len()
    implies #[trigger] c.stride[i] > 0 by {
        if i == 0 {
            lemma_complement_stride_first(a, m);
        } else {
            lemma_complement_stride_rest(a, m, i - 1);
            // c.stride[i] = stride_product(a, i-1) > 0
            lemma_stride_product_positive(a, i - 1);
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Complement is tractable
// ══════════════════════════════════════════════════════════════

/// The complement layout is tractable.
///
/// For complement mode i (0 <= i < k):
///   complement.shape[i] * complement.stride[i] divides complement.stride[i+1]
///
/// At i=0: shape_c[0]*stride_c[0] = d_0*1 = d_0, stride_c[1] = M_0*d_0, so d_0 | M_0*d_0 ✓
/// At i>=1,i<k: shape_c[i]*stride_c[i] = (d_i/sp(i-1))*sp(i-1) = d_i,
///              stride_c[i+1] = sp(i) = M_i*d_i, so d_i | M_i*d_i ✓
pub proof fn lemma_complement_tractable(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).is_tractable(),
{
    let c = complement(a, m);
    let k = a.shape.len();
    lemma_complement_rank(a, m);
    lemma_complement_shape_valid(a, m);
    lemma_complement_positive_strides(a, m);

    assert forall|i: int| 0 <= i < c.stride.len() - 1
    implies #[trigger] c.tractable_at(i) by {
        let cs_i = c.shape[i];
        let cd_i = c.stride[i];
        let cd_next = c.stride[i + 1];
        let product_i = (cs_i as int) * cd_i;

        // product_i > 0
        assert(cs_i > 0) by {
            lemma_complement_shape_valid(a, m);
        };
        assert(cd_i > 0);
        lemma_mul_pos(cs_i, cd_i as nat);

        // Show cd_next % product_i == 0
        if i == 0 {
            // cs[0] = d_0, cd[0] = 1, product_0 = d_0
            lemma_complement_stride_first(a, m);
            assert(cd_i == 1);
            assert(product_i == cs_i as int);
            // cs[0] = a.stride[0]
            assert(cs_i == a.stride[0] as nat);
            assert(product_i == a.stride[0]);
            // cd[1] = stride_product(a, 0) = M_0 * d_0
            lemma_complement_stride_rest(a, m, 0);
            assert(cd_next == stride_product(a, 0));
            assert(cd_next == (a.shape[0] as int) * a.stride[0]);
            // M_0 * d_0 % d_0 == 0
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(a.shape[0] as int, a.stride[0]);
        } else {
            // i >= 1, i < k (since c has k+1 modes, tractability checks i < k)
            // cs[i] = d_i / sp(i-1)
            // cd[i] = sp(i-1)
            // product_i = (d_i / sp(i-1)) * sp(i-1) = d_i
            lemma_complement_stride_rest(a, m, i - 1);
            assert(cd_i == stride_product(a, i - 1));
            let sp_im1 = stride_product(a, i - 1);

            // cs[i] = d_i / sp(i-1)
            // product_i = cs[i] * sp(i-1)
            // We need: product_i == a.stride[i]
            // This follows from cs[i] = (d_i / sp(i-1)) and d_i % sp(i-1) == 0
            // From tractability of a at (i-1): d_i % sp(i-1) == 0
            assert(a.tractable_at(i - 1));
            assert(a.stride[i] % sp_im1 == 0);
            lemma_stride_product_positive(a, i - 1);
            // d_i / sp(i-1) * sp(i-1) == d_i
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a.stride[i], sp_im1);
            assert(a.stride[i] == sp_im1 * (a.stride[i] / sp_im1));
            vstd::arithmetic::mul::lemma_mul_is_commutative(sp_im1, a.stride[i] / sp_im1);
            assert(product_i == a.stride[i]);

            // cd[i+1] = sp(i) = M_i * d_i
            if i < k as int - 1 {
                lemma_complement_stride_rest(a, m, i);
                assert(cd_next == stride_product(a, i));
                // stride_product(a, i) = shape[i] * stride[i] = M_i * d_i
                // So cd_next % product_i == (M_i * d_i) % d_i == 0
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                    a.shape[i] as int, a.stride[i],
                );
            } else {
                // i == k-1 (last tractability check)
                // cd[k] = sp(k-1) = stride_product(a, k-1)
                lemma_complement_stride_rest(a, m, i);
                assert(cd_next == stride_product(a, i));
                vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                    a.shape[i] as int, a.stride[i],
                );
            }
        }
    };
}

// ══════════════════════════════════════════════════════════════
// Complement injectivity
// ══════════════════════════════════════════════════════════════

/// The complement layout is always injective.
pub proof fn lemma_complement_injective(a: &LayoutSpec, m: nat)
    requires complement_admissible(a, m),
    ensures complement(a, m).is_injective(),
{
    let c = complement(a, m);
    lemma_complement_valid(a, m);
    lemma_complement_tractable(a, m);
    lemma_complement_positive_strides(a, m);
    lemma_complement_rank(a, m);

    // complement has rank >= 1 (k+1 where k >= 1)
    assert(c.shape.len() > 0);

    crate::proof::injectivity_lemmas::lemma_positive_tractable_injective(c);
}

// ══════════════════════════════════════════════════════════════
// Zipped bijective (1D case)
// ══════════════════════════════════════════════════════════════

/// For a 1D layout B with complement_admissible(B, M), the zipped layout
/// (B.shape ++ complement.shape, B.stride ++ complement.stride)
/// is bijective onto [0, M).
pub proof fn lemma_zipped_bijective_1d(b: &LayoutSpec, m: nat)
    requires
        complement_admissible(b, m),
        b.shape.len() == 1,
    ensures ({
        let c = complement(b, m);
        let zipped = LayoutSpec {
            shape: b.shape.add(c.shape),
            stride: b.stride.add(c.stride),
        };
        zipped.is_bijective_upto(m)
    }),
{
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);

    let m0 = b.shape[0];
    let d0 = b.stride[0];
    let sp = stride_product(b, 0); // M_0 * d_0
    let q = (m as int / sp) as nat;

    // Complement has shape (d0, q) and stride (1, sp)
    assert(c.shape.len() == 2);
    assert(c.shape[0] == d0 as nat);
    assert(c.shape[1] == q);
    assert(c.stride[0] == 1int);
    assert(c.stride[1] == sp);

    // Zipped: shape = (M_0, d_0, q), stride = (d_0, 1, M_0*d_0)
    assert(zipped.shape =~= seq![m0, d0 as nat, q]);
    assert(zipped.stride =~= seq![d0, 1int, sp]);
    assert(zipped.shape.len() == 3);

    // Sorted (swap modes 0,1): shape = (d_0, M_0, q), stride = (1, d_0, M_0*d_0)
    let sorted_shape = seq_swap(zipped.shape, 0);
    let sorted_stride = seq_swap(zipped.stride, 0);
    assert(sorted_shape =~= seq![d0 as nat, m0, q]);
    assert(sorted_stride =~= seq![1int, d0, sp]);

    let sorted = LayoutSpec { shape: sorted_shape, stride: sorted_stride };

    // Show sorted_stride =~= column_major_strides(sorted_shape)
    // column_major_strides((d0, M0, q)):
    //   = [1] ++ scale(column_major_strides((M0, q)), d0)
    //   column_major_strides((M0, q)) = [1] ++ scale(column_major_strides((q,)), M0)
    //     column_major_strides((q,)) = [1] ++ scale(column_major_strides(()), q) = [1] ++ scale([], q) = [1]
    //   column_major_strides((M0, q)) = [1] ++ scale([1], M0) = [1, M0]
    //   scale([1, M0], d0) = [d0, M0*d0]
    // column_major_strides((d0, M0, q)) = [1, d0, M0*d0]

    let shape_q = seq![q];
    let shape_m0q = seq![m0, q];

    // Unfold column_major_strides for single element (q,)
    assert(column_major_strides(shape_q) =~= seq![1int].add(
        scale_strides_spec(column_major_strides(shape_q.skip(1)), shape_q.first() as int)
    ));
    assert(shape_q.skip(1) =~= seq![]);
    assert(column_major_strides(seq![]) =~= seq![]);
    assert(scale_strides_spec(seq![], q as int) =~= seq![]);
    assert(column_major_strides(shape_q) =~= seq![1int]);

    // Unfold for (M0, q)
    assert(column_major_strides(shape_m0q) =~= seq![1int].add(
        scale_strides_spec(column_major_strides(shape_m0q.skip(1)), shape_m0q.first() as int)
    ));
    assert(shape_m0q.skip(1) =~= shape_q);
    assert(scale_strides_spec(seq![1int], m0 as int) =~= seq![m0 as int]);
    assert(column_major_strides(shape_m0q) =~= seq![1int, m0 as int]);

    // Unfold for (d0, M0, q)
    assert(column_major_strides(sorted_shape) =~= seq![1int].add(
        scale_strides_spec(column_major_strides(sorted_shape.skip(1)), sorted_shape.first() as int)
    ));
    assert(sorted_shape.skip(1) =~= shape_m0q);
    vstd::arithmetic::mul::lemma_mul_basics(d0);
    assert(1int * d0 == d0);
    assert(scale_strides_spec(seq![1int, m0 as int], d0) =~= seq![d0, (m0 as int) * d0]);

    // sp = M_0 * d_0 = d_0 * M_0 (commutative)
    vstd::arithmetic::mul::lemma_mul_is_commutative(m0 as int, d0);
    assert(sp == (m0 as int) * d0);
    assert(column_major_strides(sorted_shape) =~= seq![1int, d0, sp]);
    assert(sorted_stride =~= column_major_strides(sorted_shape));

    // sorted == make_column_major(sorted_shape)
    // sorted_shape is valid
    lemma_shape_valid_swap(zipped.shape, 0);
    assert(shape_valid(sorted_shape));

    // sorted_shape product == M
    // d0 * M0 * q = sp * q = M
    lemma_complement_size(b, m);
    crate::proof::product_lemmas::lemma_shape_size_append(b.shape, c.shape);
    lemma_shape_size_swap(zipped.shape, 0);

    // By column_major_bijective: sorted is bijective onto [0, size(sorted_shape))
    crate::proof::injectivity_lemmas::lemma_column_major_bijective(sorted_shape);

    // sorted has same size as zipped
    assert(shape_size(sorted_shape) == shape_size(zipped.shape));

    // Transfer bijectivity via swap (swap(sorted, 0) == zipped)
    // sorted is injective → zipped is injective (swap preserves)
    assert(sorted.shape =~= seq_swap(zipped.shape, 0));
    assert(sorted.stride =~= seq_swap(zipped.stride, 0));
    lemma_swap_preserves_injective(&sorted, 0);
    // swap(sorted, 0) has shape = swap(sorted_shape, 0) = zipped.shape
    assert(seq_swap(sorted.shape, 0) =~= zipped.shape);
    assert(seq_swap(sorted.stride, 0) =~= zipped.stride);

    // sorted is surjective → zipped is surjective (swap preserves)
    lemma_swap_preserves_surjective(&sorted, 0, shape_size(sorted_shape));
}

} // verus!
