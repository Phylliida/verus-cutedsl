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
pub proof fn lemma_stride_product_positive(a: &LayoutSpec, i: int)
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
// Multi-swap utility: apply_swaps preserves injective/surjective
// ══════════════════════════════════════════════════════════════

/// Apply a single adjacent-mode swap to a layout.
pub open spec fn apply_swap_layout(layout: LayoutSpec, i: nat) -> LayoutSpec {
    LayoutSpec {
        shape: seq_swap(layout.shape, i as int),
        stride: seq_swap(layout.stride, i as int),
    }
}

/// Recursively apply a sequence of adjacent swaps.
pub open spec fn apply_swaps(layout: LayoutSpec, swaps: Seq<nat>) -> LayoutSpec
    decreases swaps.len(),
{
    if swaps.len() == 0 { layout }
    else { apply_swaps(apply_swap_layout(layout, swaps.first()), swaps.skip(1)) }
}

/// apply_swaps preserves layout rank.
pub proof fn lemma_apply_swaps_rank(layout: LayoutSpec, swaps: Seq<nat>)
    ensures
        apply_swaps(layout, swaps).shape.len() == layout.shape.len(),
        apply_swaps(layout, swaps).stride.len() == layout.stride.len(),
    decreases swaps.len(),
{
    if swaps.len() > 0 {
        lemma_apply_swaps_rank(apply_swap_layout(layout, swaps.first()), swaps.skip(1));
    }
}

/// apply_swaps preserves validity when all swap indices are in bounds.
pub proof fn lemma_apply_swaps_valid(layout: LayoutSpec, swaps: Seq<nat>)
    requires
        layout.valid(),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        apply_swaps(layout, swaps).valid(),
    decreases swaps.len(),
{
    if swaps.len() > 0 {
        let i = swaps.first();
        lemma_shape_valid_swap(layout.shape, i);
        let next = apply_swap_layout(layout, i);
        assert forall|j: nat| j < swaps.skip(1).len()
            implies #[trigger] swaps.skip(1)[j as int] + 1 < next.shape.len()
        by {};
        lemma_apply_swaps_valid(next, swaps.skip(1));
    }
}

/// apply_swaps preserves shape_size.
pub proof fn lemma_apply_swaps_size(layout: LayoutSpec, swaps: Seq<nat>)
    requires
        shape_valid(layout.shape),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        shape_size(apply_swaps(layout, swaps).shape) == shape_size(layout.shape),
    decreases swaps.len(),
{
    if swaps.len() > 0 {
        let i = swaps.first();
        assert(swaps[0] == i); // trigger the quantifier
        assert(i + 1 < layout.shape.len());
        lemma_shape_size_swap(layout.shape, i);
        let next = apply_swap_layout(layout, i);
        lemma_shape_valid_swap(layout.shape, i);
        assert forall|j: nat| j < swaps.skip(1).len()
            implies #[trigger] swaps.skip(1)[j as int] + 1 < next.shape.len()
        by {};
        lemma_apply_swaps_size(next, swaps.skip(1));
    }
}

/// apply_swaps preserves injectivity.
pub proof fn lemma_apply_swaps_preserves_injective(layout: LayoutSpec, swaps: Seq<nat>)
    requires
        layout.valid(),
        layout.is_injective(),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        apply_swaps(layout, swaps).is_injective(),
    decreases swaps.len(),
{
    if swaps.len() > 0 {
        let i = swaps.first();
        lemma_swap_preserves_injective(&layout, i);
        let next = apply_swap_layout(layout, i);
        lemma_shape_valid_swap(layout.shape, i);
        assert forall|j: nat| j < swaps.skip(1).len()
            implies #[trigger] swaps.skip(1)[j as int] + 1 < next.shape.len()
        by {};
        lemma_apply_swaps_preserves_injective(next, swaps.skip(1));
    }
}

/// apply_swaps preserves surjectivity.
pub proof fn lemma_apply_swaps_preserves_surjective(layout: LayoutSpec, swaps: Seq<nat>, m: nat)
    requires
        layout.valid(),
        layout.is_surjective_upto(m),
        forall|j: nat| j < swaps.len() ==> #[trigger] swaps[j as int] + 1 < layout.shape.len(),
    ensures
        apply_swaps(layout, swaps).is_surjective_upto(m),
    decreases swaps.len(),
{
    if swaps.len() > 0 {
        let i = swaps.first();
        lemma_swap_preserves_surjective(&layout, i, m);
        let next = apply_swap_layout(layout, i);
        lemma_shape_valid_swap(layout.shape, i);
        assert forall|j: nat| j < swaps.skip(1).len()
            implies #[trigger] swaps.skip(1)[j as int] + 1 < next.shape.len()
        by {};
        lemma_apply_swaps_preserves_surjective(next, swaps.skip(1), m);
    }
}

// ══════════════════════════════════════════════════════════════
// Interleaved zipped layout: C[0] B[0] C[1] B[1] ... C[k-1] B[k-1] C[k]
// ══════════════════════════════════════════════════════════════

/// Build the interleaved shape: C[0], B[0], C[1], B[1], ..., C[k-1], B[k-1], C[k].
pub open spec fn interleaved_zipped_shape(b: &LayoutSpec, m: nat) -> Seq<nat>
    recommends complement_admissible(b, m),
{
    let c = complement(b, m);
    let k = b.shape.len();
    Seq::new(
        2 * k + 1,
        |i: int|
            if i % 2 == 0 { c.shape[(i / 2) as int] }
            else { b.shape[((i - 1) / 2) as int] }
    )
}

/// Build the interleaved stride: C.stride[0], B.stride[0], ..., C.stride[k].
pub open spec fn interleaved_zipped_stride(b: &LayoutSpec, m: nat) -> Seq<int>
    recommends complement_admissible(b, m),
{
    let c = complement(b, m);
    let k = b.shape.len();
    Seq::new(
        2 * k + 1,
        |i: int|
            if i % 2 == 0 { c.stride[(i / 2) as int] }
            else { b.stride[((i - 1) / 2) as int] }
    )
}

/// The interleaved shape is valid (all entries > 0).
pub proof fn lemma_interleaved_shape_valid(b: &LayoutSpec, m: nat)
    requires complement_admissible(b, m),
    ensures shape_valid(interleaved_zipped_shape(b, m)),
{
    let iz = interleaved_zipped_shape(b, m);
    let c = complement(b, m);
    lemma_complement_shape_valid(b, m);
    assert forall|i: int| 0 <= i < iz.len() implies #[trigger] iz[i] > 0 by {
        if i % 2 == 0 {
            assert(iz[i] == c.shape[(i / 2) as int]);
        } else {
            assert(iz[i] == b.shape[((i - 1) / 2) as int]);
        }
    };
}

/// The interleaved shape product equals M.
pub proof fn lemma_interleaved_shape_size(b: &LayoutSpec, m: nat)
    requires complement_admissible(b, m),
    ensures shape_size(interleaved_zipped_shape(b, m)) == m,
{
    // interleaved_shape is a permutation of zipped_shape = b.shape ++ c.shape
    // zipped_shape product = sb * sc = M (by complement_size)
    // interleaved_shape is a rearrangement, same product
    // We prove this via the telescoping: each stride = product of all previous shapes
    // So shape_size = product of all shapes = last_stride * last_shape = sp_{k-1} * C.shape[k] = M

    let iz = interleaved_zipped_shape(b, m);
    let c = complement(b, m);
    let k = b.shape.len();
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    lemma_interleaved_shape_valid(b, m);

    // Prove by telescoping: shape_size = product of shapes = M
    // Use complement_size: shape_size(c.shape) * shape_size(b.shape) == m
    lemma_complement_size(b, m);
    crate::proof::product_lemmas::lemma_shape_size_append(b.shape, c.shape);

    // We need: shape_size(interleaved) == shape_size(b.shape.add(c.shape))
    // Both are products of the same multiset of values, just in different order.
    // Prove by induction on k using the telescoping structure.
    lemma_interleaved_size_eq_product(b, m, k);
}

/// Helper: the product of interleaved shapes telescopes to match b ++ c product.
/// Shows shape_size(interleaved) == shape_size(b.shape) * shape_size(c.shape).
proof fn lemma_interleaved_size_eq_product(b: &LayoutSpec, m: nat, k: nat)
    requires
        complement_admissible(b, m),
        k == b.shape.len(),
    ensures
        shape_size(interleaved_zipped_shape(b, m))
            == shape_size(b.shape) * shape_size(complement_shape(b, m)),
    decreases k,
{
    let iz = interleaved_zipped_shape(b, m);
    let c = complement(b, m);
    let cs = complement_shape(b, m);
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    lemma_interleaved_shape_valid(b, m);

    if k == 0 {
        // iz has 1 element: c.shape[0] = M/sp_{-1}... no, k=0 is degenerate
        // complement_admissible requires b.shape.len() > 0, so k >= 1
        // k == b.shape.len() >= 1 from complement_admissible
        assert(false); // complement_admissible requires shape.len() > 0
    } else if k == 1 {
        // iz has 3 elements: c.shape[0], b.shape[0], c.shape[1]
        assert(iz.len() == 3);
        // shape_size = iz[0] * iz[1] * iz[2]
        assert(iz[0] == cs[0]);
        assert(iz[1] == b.shape[0]);
        assert(iz[2] == cs[1]);

        // Unfold shape_size for 3 elements
        assert(shape_size(iz) == iz.first() * shape_size(iz.skip(1)));
        let iz1 = iz.skip(1);
        assert(iz1.first() == iz[1]);
        assert(shape_size(iz1) == iz1.first() * shape_size(iz1.skip(1)));
        let iz2 = iz1.skip(1);
        assert(iz2 =~= iz.skip(2));
        assert(iz2.len() == 1);
        assert(iz2.first() == iz[2]);
        assert(shape_size(iz2) == iz2.first() * shape_size(iz2.skip(1)));
        assert(iz2.skip(1).len() == 0);
        assert(shape_size(iz2.skip(1)) == 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(iz[2] as int);

        // shape_size(b.shape) for 1 element
        assert(shape_size(b.shape) == b.shape.first() * shape_size(b.shape.skip(1)));
        assert(b.shape.skip(1).len() == 0);
        vstd::arithmetic::mul::lemma_mul_basics(b.shape.first() as int);

        // shape_size(cs) for 2 elements
        assert(shape_size(cs) == cs.first() * shape_size(cs.skip(1)));
        assert(cs.skip(1).len() == 1);
        assert(cs.skip(1).first() == cs[1]);
        assert(shape_size(cs.skip(1)) == cs[1] * shape_size(cs.skip(1).skip(1)));
        assert(cs.skip(1).skip(1).len() == 0);
        vstd::arithmetic::mul::lemma_mul_basics(cs[1] as int);

        // iz[0] * iz[1] * iz[2] == cs[0] * b.shape[0] * cs[1]
        //                        == cs[0] * cs[1] * b.shape[0]
        //                        == shape_size(cs) * shape_size(b.shape)
        vstd::arithmetic::mul::lemma_mul_is_associative(cs[0] as int, (b.shape[0]) as int, cs[1] as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative((b.shape[0]) as int, cs[1] as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(cs[0] as int, cs[1] as int, (b.shape[0]) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            shape_size(b.shape) as int,
            shape_size(cs) as int,
        );
    } else {
        // General case: iz = [c.shape[0], b.shape[0], ...rest...]
        // shape_size(iz) = c.shape[0] * b.shape[0] * shape_size(rest)
        // Where rest is the interleaved shape for b' (b with first mode removed)

        // For now, prove via product of b.shape ++ c.shape == product of interleaved
        // using the fact that shape_size is just a product of all elements,
        // which is commutative and associative.

        // We prove: shape_size(iz) == shape_size(b.shape.add(cs))
        // by showing both are the product of the same multiset of nat values.
        // But Verus doesn't have multiset product reasoning.

        // Alternative: use the complement_size telescoping directly.
        // shape_size(iz) unfolds to product of all iz entries.
        // iz entries are: cs[0], b.shape[0], cs[1], b.shape[1], ..., cs[k-1], b.shape[k-1], cs[k]
        // These are exactly cs[0..k+1] and b.shape[0..k], just interleaved.
        // Product of all = product(cs) * product(b.shape)

        // Use a helper that relates iz to two sub-sequences
        lemma_interleaved_product_split(b, m, k);
    }
}

/// Helper: the interleaved product splits into B and C products.
/// shape_size(interleaved) = shape_size(b.shape) * shape_size(c.shape)
/// by induction: peel off the first two elements (c[0], b[0]) and use IH on the rest.
proof fn lemma_interleaved_product_split(b: &LayoutSpec, m: nat, k: nat)
    requires
        complement_admissible(b, m),
        k == b.shape.len(),
        k >= 2,
    ensures
        shape_size(interleaved_zipped_shape(b, m))
            == shape_size(b.shape) * shape_size(complement_shape(b, m)),
    decreases k,
{
    let iz = interleaved_zipped_shape(b, m);
    let cs = complement_shape(b, m);
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    lemma_interleaved_shape_valid(b, m);

    // iz = [cs[0], b.shape[0]] ++ iz_rest
    // where iz_rest is the interleaved shape for the "tail" problem.
    // But defining the tail problem requires a sub-layout, which is complex.

    // Simpler: use that both sides are finite products and argue by regrouping.
    // shape_size(iz) = product of 2k+1 values
    // shape_size(b.shape) * shape_size(cs) = product of k values * product of k+1 values
    // Same 2k+1 factors in both.

    // We prove by strong induction, peeling two elements at a time.
    // shape_size(iz) = iz[0] * iz[1] * shape_size(iz.skip(2))
    // iz[0] = cs[0], iz[1] = b.shape[0]

    assert(iz.first() == cs[0]);
    assert(iz.skip(1).first() == b.shape[0]);

    // shape_size(iz) = cs[0] * b.shape[0] * shape_size(iz.skip(2))
    assert(shape_size(iz) == iz.first() * shape_size(iz.skip(1)));
    assert(shape_size(iz.skip(1)) == b.shape[0] * shape_size(iz.skip(1).skip(1)));
    assert(iz.skip(1).skip(1) =~= iz.skip(2));

    vstd::arithmetic::mul::lemma_mul_is_associative(
        cs[0] as int, (b.shape[0]) as int, shape_size(iz.skip(2)) as int,
    );

    // shape_size(b.shape) = b.shape[0] * shape_size(b.shape.skip(1))
    // shape_size(cs) = cs[0] * shape_size(cs.skip(1))
    // So product = cs[0] * shape_size(cs.skip(1)) * b.shape[0] * shape_size(b.shape.skip(1))
    //            = cs[0] * b.shape[0] * shape_size(cs.skip(1)) * shape_size(b.shape.skip(1))

    // iz.skip(2) is the interleaved shape of the tail:
    // [cs[1], b.shape[1], cs[2], b.shape[2], ..., cs[k-1], b.shape[k-1], cs[k]]
    // which has 2(k-1)+1 elements

    // IH (or direct): shape_size(iz.skip(2)) == shape_size(b.shape.skip(1)) * shape_size(cs.skip(1))

    // For the inductive argument, we need iz.skip(2) to be the interleaved shape
    // of the sub-problem. But the sub-problem is complement of b_tail w.r.t. m_tail,
    // which doesn't have a clean correspondence with complement(b, m).skip(1).

    // Instead, let's just use a general lemma about interleaving products.
    // product(interleave(a, b)) == product(a) * product(b)
    // This is a simple counting argument.
    lemma_interleaved_product_equals(b.shape, cs, k);

    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(b.shape) as int, shape_size(cs) as int);
}

/// General lemma: interleaving two sequences preserves the total product.
/// If iz[2i] = cs[i] and iz[2i+1] = bs[i] (for i < k), iz[2k] = cs[k],
/// then shape_size(iz) == shape_size(bs) * shape_size(cs).
proof fn lemma_interleaved_product_equals(bs: Seq<nat>, cs: Seq<nat>, k: nat)
    requires
        k > 0,
        bs.len() == k,
        cs.len() == k + 1,
        shape_valid(bs),
        shape_valid(cs),
    ensures ({
        let iz = Seq::new(2 * k + 1, |i: int|
            if i % 2 == 0 { cs[(i / 2) as int] }
            else { bs[((i - 1) / 2) as int] }
        );
        shape_size(iz) == shape_size(bs) * shape_size(cs)
    }),
    decreases k,
{
    let iz = Seq::new(2 * k + 1, |i: int|
        if i % 2 == 0 { cs[(i / 2) as int] }
        else { bs[((i - 1) / 2) as int] }
    );

    if k == 1 {
        // iz = [cs[0], bs[0], cs[1]], 3 elements
        assert(iz.len() == 3);
        assert(iz[0] == cs[0]);
        assert(iz[1] == bs[0]);
        assert(iz[2] == cs[1]);

        // shape_size(iz) = cs[0] * bs[0] * cs[1]
        assert(iz.first() == cs[0]);
        let iz1 = iz.skip(1);
        assert(iz1.first() == bs[0]);
        let iz2 = iz1.skip(1);
        assert(iz2 =~= iz.skip(2));
        assert(iz2.len() == 1);
        assert(iz2.first() == cs[1]);
        assert(shape_size(iz2) == iz2.first() * shape_size(iz2.skip(1)));
        assert(iz2.skip(1).len() == 0);
        assert(shape_size(iz2.skip(1)) == 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(cs[1] as int);
        assert(shape_size(iz1) == bs[0] * shape_size(iz2));

        // shape_size(bs) = bs[0]
        assert(bs.skip(1).len() == 0);
        assert(shape_size(bs) == bs[0] * shape_size(bs.skip(1)));
        vstd::arithmetic::mul::lemma_mul_basics(bs[0] as int);

        // shape_size(cs) = cs[0] * cs[1]
        let cs1 = cs.skip(1);
        assert(cs1 =~= cs.skip(1));
        assert(cs1.len() == 1);
        assert(cs1.first() == cs[1]);
        assert(shape_size(cs1) == cs1.first() * shape_size(cs1.skip(1)));
        assert(cs1.skip(1).len() == 0);
        vstd::arithmetic::mul::lemma_mul_basics(cs[1] as int);

        // cs[0] * bs[0] * cs[1] == bs[0] * (cs[0] * cs[1])
        vstd::arithmetic::mul::lemma_mul_is_associative(cs[0] as int, bs[0] as int, cs[1] as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(cs[0] as int, bs[0] as int);
        vstd::arithmetic::mul::lemma_mul_is_associative(bs[0] as int, cs[0] as int, cs[1] as int);
    } else {
        // Peel first two elements: iz = [cs[0], bs[0]] ++ iz_rest
        // iz_rest is the interleaving of bs.skip(1) and cs.skip(1)
        let bs_tail = bs.skip(1);
        let cs_tail = cs.skip(1);
        let km1 = (k - 1) as nat;

        assert(shape_valid(bs_tail)) by {
            assert forall|i: int| 0 <= i < bs_tail.len() implies #[trigger] bs_tail[i] > 0 by {
                assert(bs_tail[i] == bs[i + 1]);
            };
        };
        assert(shape_valid(cs_tail)) by {
            assert forall|i: int| 0 <= i < cs_tail.len() implies #[trigger] cs_tail[i] > 0 by {
                assert(cs_tail[i] == cs[i + 1]);
            };
        };
        assert(bs_tail.len() == km1);
        assert(cs_tail.len() == km1 + 1);

        // IH: interleaving of bs_tail, cs_tail has product = shape_size(bs_tail) * shape_size(cs_tail)
        lemma_interleaved_product_equals(bs_tail, cs_tail, km1);
        let iz_rest = Seq::new(2 * km1 + 1, |i: int|
            if i % 2 == 0 { cs_tail[(i / 2) as int] }
            else { bs_tail[((i - 1) / 2) as int] }
        );

        // iz.skip(2) =~= iz_rest
        assert(iz.skip(2) =~= iz_rest) by {
            assert(iz.skip(2).len() == iz_rest.len());
            assert forall|i: int| 0 <= i < iz_rest.len()
                implies iz.skip(2)[i] == iz_rest[i]
            by {
                assert(iz.skip(2)[i] == iz[i + 2]);
                if (i + 2) % 2 == 0 {
                    assert(iz[i + 2] == cs[((i + 2) / 2) as int]);
                    assert(i % 2 == 0);
                    assert(iz_rest[i] == cs_tail[(i / 2) as int]);
                    assert(cs_tail[(i / 2) as int] == cs[(i / 2 + 1) as int]);
                    assert((i + 2) / 2 == i / 2 + 1);
                } else {
                    assert(iz[i + 2] == bs[((i + 2 - 1) / 2) as int]);
                    assert(i % 2 == 1);
                    assert(iz_rest[i] == bs_tail[((i - 1) / 2) as int]);
                    assert(bs_tail[((i - 1) / 2) as int] == bs[((i - 1) / 2 + 1) as int]);
                    assert((i + 2 - 1) / 2 == (i - 1) / 2 + 1);
                }
            };
        };

        // shape_size(iz) = iz[0] * iz[1] * shape_size(iz.skip(2))
        //                = cs[0] * bs[0] * shape_size(iz_rest)
        //                = cs[0] * bs[0] * shape_size(bs_tail) * shape_size(cs_tail)
        //                = (bs[0] * shape_size(bs_tail)) * (cs[0] * shape_size(cs_tail))
        //                = shape_size(bs) * shape_size(cs)

        // Help Z3 unfold shape_size(iz.skip(1))
        let iz_s1 = iz.skip(1);
        assert(iz_s1.len() > 0);
        assert(iz_s1.first() == iz[1]);
        assert(iz[1] == bs[0]);
        assert(iz_s1.skip(1) =~= iz.skip(2));
        assert(shape_size(iz_s1) == iz_s1.first() * shape_size(iz_s1.skip(1)));
        // Now: shape_size(iz.skip(1)) == bs[0] * shape_size(iz.skip(2))

        vstd::arithmetic::mul::lemma_mul_is_associative(
            cs[0] as int, bs[0] as int, shape_size(iz.skip(2)) as int);
        // cs[0] * bs[0] * S_rest = cs[0] * bs[0] * S_bs_tail * S_cs_tail
        let s_rest = shape_size(iz_rest);
        let s_bt = shape_size(bs_tail);
        let s_ct = shape_size(cs_tail);
        assert(s_rest == s_bt * s_ct);

        // cs[0] * bs[0] * s_bt * s_ct == (bs[0] * s_bt) * (cs[0] * s_ct)
        // = shape_size(bs) * shape_size(cs)
        assert(cs[0] * (bs[0] * (s_bt * s_ct))
            == (bs[0] * s_bt) * (cs[0] * s_ct)) by (nonlinear_arith)
            requires cs[0] >= 0, bs[0] >= 0, s_bt >= 0, s_ct >= 0;

        assert(cs.skip(1) =~= cs_tail);
    }
}

// ══════════════════════════════════════════════════════════════
// Interleaved strides are column-major
// ══════════════════════════════════════════════════════════════

/// The interleaved zipped stride equals column_major_strides of the interleaved shape.
/// This is the key structural property: the complement's stride structure telescopes
/// so that the interleaved layout is exactly column-major.
pub proof fn lemma_interleaved_is_column_major(b: &LayoutSpec, m: nat)
    requires complement_admissible(b, m),
    ensures
        interleaved_zipped_stride(b, m) =~=
            column_major_strides(interleaved_zipped_shape(b, m)),
{
    let iz_shape = interleaved_zipped_shape(b, m);
    let iz_stride = interleaved_zipped_stride(b, m);
    let cm = column_major_strides(iz_shape);
    let c = complement(b, m);
    let k = b.shape.len();
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    lemma_interleaved_shape_valid(b, m);

    crate::proof::injectivity_lemmas::lemma_column_major_strides_len(iz_shape);
    assert(cm.len() == iz_stride.len());

    // Show each stride matches
    assert forall|i: int| 0 <= i < cm.len()
    implies cm[i] == iz_stride[i]
    by {
        lemma_interleaved_stride_matches_cm(b, m, i);
    };
}

/// Helper: each interleaved stride equals the corresponding column-major stride.
/// cm_stride[i] = product of iz_shape[0..i] = interleaved_stride[i].
proof fn lemma_interleaved_stride_matches_cm(b: &LayoutSpec, m: nat, i: int)
    requires
        complement_admissible(b, m),
        0 <= i < (2 * b.shape.len() + 1) as int,
    ensures ({
        let iz_shape = interleaved_zipped_shape(b, m);
        let iz_stride = interleaved_zipped_stride(b, m);
        let cm = column_major_strides(iz_shape);
        cm[i] == iz_stride[i]
    }),
    decreases i,
{
    let iz_shape = interleaved_zipped_shape(b, m);
    let iz_stride = interleaved_zipped_stride(b, m);
    let c = complement(b, m);
    let k = b.shape.len();
    lemma_complement_rank(b, m);

    crate::proof::injectivity_lemmas::lemma_column_major_strides_len(iz_shape);

    if i == 0 {
        // cm[0] = 1, iz_stride[0] = c.stride[0] = 1
        assert(column_major_strides(iz_shape).first() == 1int);
        lemma_complement_stride_first(b, m);
        assert(iz_stride[0] == c.stride[0]);
        assert(c.stride[0] == 1int);
    } else {
        // cm[i] = cm[i-1] * iz_shape[i-1]
        // We use the recursive definition:
        // column_major_strides(s) = [1] ++ scale(column_major_strides(s.skip(1)), s[0])
        // So cm[i] = s[0] * column_major_strides(s.skip(1))[i-1]
        // = iz_shape[0] * cm_tail[i-1]
        // By induction, cm_tail[i-1] is the column-major stride for the tail.

        // Instead, use the simpler property:
        // cm[i] = product of iz_shape[0..i]
        // This is shape_size(iz_shape.take(i))

        // Actually, column_major_strides are defined recursively,
        // and cm[i] = product(iz_shape[0..i]) is the key identity.
        // Let me use complement_size_step which already establishes the telescoping.

        // Even position (i even): iz_stride[i] = c.stride[i/2]
        // Odd position (i odd): iz_stride[i] = b.stride[(i-1)/2]

        if i % 2 == 0 {
            // Even position: iz_stride[i] = c.stride[i/2]
            let ci = (i / 2) as int;
            if ci == 0 {
                assert(false); // i >= 1 and i even means i >= 2
            }

            // IH + recursive step
            lemma_interleaved_stride_matches_cm(b, m, i - 1);
            lemma_cm_recursive_step(iz_shape, i);

            let cm_val = column_major_strides(iz_shape);
            // cm[i] = cm[i-1] * iz_shape[i-1]
            assert(cm_val[i] == cm_val[(i-1) as int] * (iz_shape[(i-1) as int] as int));

            // IH: cm[i-1] = iz_stride[i-1] = b.stride[ci-1] (i-1 is odd)
            assert((i - 1) % 2 == 1);
            assert(iz_stride[(i - 1) as int] == b.stride[(ci - 1) as int]);
            assert(cm_val[(i-1) as int] == b.stride[(ci - 1) as int]);

            // iz_shape[i-1] = b.shape[ci-1] (i-1 is odd)
            assert(iz_shape[(i - 1) as int] == b.shape[(ci - 1) as int]);

            // cm[i] = b.stride[ci-1] * b.shape[ci-1] = stride_product(b, ci-1)
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                b.stride[(ci - 1) as int], b.shape[(ci - 1) as int] as int);

            // iz_stride[i] = c.stride[ci] = stride_product(b, ci-1)
            lemma_complement_stride_rest(b, m, ci - 1);
            assert(iz_stride[i] == c.stride[ci]);
            assert(c.stride[ci] == stride_product(b, ci - 1));
        } else {
            // Odd position: iz_stride[i] = b.stride[(i-1)/2]
            let bi = ((i - 1) / 2) as int;
            assert(iz_stride[i] == b.stride[bi]);

            if i == 1 {
                // cm[1] = cm[0] * iz_shape[0] = 1 * c.shape[0] = b.stride[0]
                assert(iz_shape[0] == c.shape[0]);
                assert(c.shape[0] == b.stride[0] as nat);
                lemma_cm_recursive_step(iz_shape, 1);
                let cm_val = column_major_strides(iz_shape);
                assert(cm_val[0] == 1int);
                vstd::arithmetic::mul::lemma_mul_basics(iz_shape[0] as int);
                assert(cm_val[1] == iz_shape[0] as int);
                assert(iz_shape[0] as int == b.stride[0]);
            } else {
                // i odd, i >= 3
                lemma_interleaved_stride_matches_cm(b, m, i - 1);
                lemma_cm_recursive_step(iz_shape, i);

                let ci = ((i - 1) / 2) as int;
                assert(ci >= 1);
                assert((i - 1) % 2 == 0);

                let cm_val = column_major_strides(iz_shape);
                // cm[i] = cm[i-1] * iz_shape[i-1]
                assert(cm_val[i] == cm_val[(i-1) as int] * (iz_shape[(i-1) as int] as int));

                // IH: cm[i-1] = iz_stride[i-1] = c.stride[ci] (i-1 is even)
                assert(iz_stride[(i - 1) as int] == c.stride[ci]);
                assert(cm_val[(i-1) as int] == c.stride[ci]);

                // iz_shape[i-1] = c.shape[ci] (i-1 is even)
                assert(iz_shape[(i - 1) as int] == c.shape[ci]);

                // c.stride[ci] = stride_product(b, ci-1)
                lemma_complement_stride_rest(b, m, ci - 1);
                let sp_prev = stride_product(b, ci - 1);
                assert(c.stride[ci] == sp_prev);

                // c.shape[ci] = (b.stride[ci] / sp_prev) as nat
                lemma_stride_product_positive(b, ci - 1);
                assert(sp_prev > 0);
                assert(c.shape[ci] == (b.stride[ci] / sp_prev) as nat);

                // b.stride[ci] > 0 (sorted + positive first stride)
                assert(b.stride[ci] > 0);

                // tractability: b.stride[ci] % sp_prev == 0
                assert(b.tractable_at(ci - 1));
                assert(b.stride[ci] % sp_prev == 0);

                // nat-int roundtrip: (b.stride[ci] / sp_prev) is non-negative
                lemma_div_positive_when_divides(sp_prev, b.stride[ci]);
                assert(b.stride[ci] / sp_prev > 0);
                assert((b.stride[ci] / sp_prev) as nat as int == b.stride[ci] / sp_prev);

                // cm[i] = sp_prev * (b.stride[ci] / sp_prev) = b.stride[ci]
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b.stride[ci], sp_prev);
                assert(b.stride[ci] == sp_prev * (b.stride[ci] / sp_prev));

                // Final chain: cm[i] = c.stride[ci] * (c.shape[ci] as int)
                //            = sp_prev * (b.stride[ci] / sp_prev)
                //            = b.stride[ci] = iz_stride[i]
                assert(c.shape[ci] as int == b.stride[ci] / sp_prev);
            }
        }
    }
}

/// Column-major strides satisfy the recursive step: cm[i] = cm[i-1] * shape[i-1] for i >= 1.
pub proof fn lemma_cm_recursive_step(shape: Seq<nat>, i: int)
    requires
        shape.len() > 0,
        1 <= i < shape.len() as int,
    ensures
        column_major_strides(shape)[i]
            == column_major_strides(shape)[(i - 1) as int] * (shape[(i - 1) as int] as int),
    decreases i,
{
    let cm = column_major_strides(shape);
    let tail = shape.skip(1);
    let cm_tail = column_major_strides(tail);
    crate::proof::injectivity_lemmas::lemma_column_major_strides_len(shape);
    crate::proof::injectivity_lemmas::lemma_column_major_strides_len(tail);

    // cm = [1] ++ scale(cm_tail, shape[0])
    let scaled = scale_strides_spec(cm_tail, shape.first() as int);
    assert(cm =~= seq![1int].add(scaled));
    // cm[i] = scaled[i-1] = cm_tail[i-1] * shape[0]

    if i == 1 {
        // cm[1] = scaled[0] = cm_tail[0] * shape[0]
        // cm[0] = 1
        // shape[0] * 1 = shape[0]
        // cm_tail[0] = 1 (column_major_strides starts with 1 if tail non-empty,
        //                  or tail is empty and we have no cm_tail[0])
        if tail.len() == 0 {
            // shape has exactly 1 element, i=1 would require shape.len() > 1
            assert(false);
        }
        assert(cm_tail.first() == 1int);
        vstd::arithmetic::mul::lemma_mul_basics(shape.first() as int);
        assert(scaled[0] == 1int * (shape.first() as int));
    } else {
        // cm[i] = scaled[i-1] = cm_tail[i-1] * shape[0]
        // cm[i-1] = scaled[i-2] = cm_tail[i-2] * shape[0]
        // shape[i-1] = shape.skip(1)[i-2] = tail[i-2]

        // Want: cm_tail[i-1] * s0 == (cm_tail[i-2] * s0) * tail[i-2]
        // i.e., cm_tail[i-1] == cm_tail[i-2] * tail[i-2]
        // This is the recursive step for cm_tail!
        if (i - 1) as int >= tail.len() as int {
            assert(false); // i < shape.len() means i-1 < tail.len()
        }
        lemma_cm_recursive_step(tail, i - 1);
        // cm_tail[i-1] == cm_tail[i-2] * tail[i-2]

        let s0 = shape.first() as int;
        // cm[i] = cm_tail[i-1] * s0
        //       = (cm_tail[i-2] * tail[i-2]) * s0
        //       = (cm_tail[i-2] * s0) * tail[i-2]
        //       = cm[i-1] * shape[i-1]
        vstd::arithmetic::mul::lemma_mul_is_associative(
            cm_tail[(i - 2) as int], tail[(i - 2) as int] as int, s0);
        vstd::arithmetic::mul::lemma_mul_is_commutative(tail[(i - 2) as int] as int, s0);
        vstd::arithmetic::mul::lemma_mul_is_associative(
            cm_tail[(i - 2) as int], s0, tail[(i - 2) as int] as int);
        // cm_tail[i-2] * tail[i-2] * s0 = cm_tail[i-2] * s0 * tail[i-2]
        // which is cm[i-1] * shape[i-1] since tail[i-2] = shape[i-1]
        assert(tail[(i - 2) as int] == shape[(i - 1) as int]);
    }
}

// ══════════════════════════════════════════════════════════════
// Swap sequence from interleaved to zipped
// ══════════════════════════════════════════════════════════════

/// The swap sequence that moves B[j] from position 2j+1 to position j
/// (after B[0]..B[j-1] have already been moved).
/// Swaps at positions 2j, 2j-1, ..., j.
pub open spec fn extraction_swaps_for(j: nat) -> Seq<nat> {
    Seq::new(j + 1, |i: int| (2 * j - i) as nat)
}

/// The full swap sequence to transform interleaved → zipped order.
/// Concatenation of extraction_swaps_for(0), ..., extraction_swaps_for(k-1).
pub open spec fn zipping_swaps(k: nat) -> Seq<nat>
    decreases k,
{
    if k == 0 { seq![] }
    else { zipping_swaps((k - 1) as nat).add(extraction_swaps_for((k - 1) as nat)) }
}

/// All swap indices in zipping_swaps(k) are < 2k (so valid for a layout with 2k+1 modes).
proof fn lemma_zipping_swaps_bounded(k: nat)
    ensures
        forall|j: nat| j < zipping_swaps(k).len() ==>
            #[trigger] zipping_swaps(k)[j as int] + 1 < 2 * k + 1,
    decreases k,
{
    if k == 0 {
    } else {
        lemma_zipping_swaps_bounded((k - 1) as nat);
        let prev = zipping_swaps((k - 1) as nat);
        let ext = extraction_swaps_for((k - 1) as nat);
        let all = prev.add(ext);
        assert(zipping_swaps(k) == all);

        assert forall|j: nat| j < all.len()
        implies #[trigger] all[j as int] + 1 < 2 * k + 1
        by {
            if (j as int) < prev.len() as int {
                assert(all[j as int] == prev[j as int]);
                // By IH: prev[j] + 1 < 2*(k-1) + 1 = 2k - 1 < 2k + 1
            } else {
                let idx = (j as int - prev.len()) as int;
                assert(all[j as int] == ext[idx]);
                // ext[idx] = 2*(k-1) - idx, where 0 <= idx <= k-1
                // max value = 2*(k-1), so 2*(k-1) + 1 = 2k - 1 < 2k + 1
                assert(ext[idx] == (2 * ((k - 1) as nat) - idx) as nat);
                assert(ext[idx] as int <= (2 * (k - 1)) as int);
            }
        };
    }
}

// ══════════════════════════════════════════════════════════════
// Swap sequence infrastructure
// ══════════════════════════════════════════════════════════════

/// apply_swaps distributes over concatenation.
proof fn lemma_apply_swaps_concat(layout: LayoutSpec, a: Seq<nat>, b: Seq<nat>)
    ensures apply_swaps(layout, a.add(b)) == apply_swaps(apply_swaps(layout, a), b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a.add(b) =~= b);
    } else {
        assert(a.add(b).first() == a.first());
        assert(a.add(b).skip(1) =~= a.skip(1).add(b));
        lemma_apply_swaps_concat(
            apply_swap_layout(layout, a.first()), a.skip(1), b);
    }
}

/// Consecutive decreasing swaps [high, high-1, ..., low] bubble element from
/// position high+1 down to position low, shifting [low..high] right by 1.
proof fn lemma_consec_swaps_bubble(layout: LayoutSpec, high: nat, low: nat)
    requires
        low <= high,
        high + 1 < layout.shape.len(),
        layout.shape.len() == layout.stride.len(),
    ensures ({
        let swaps = Seq::new((high - low + 1) as nat, |i: int| (high - i) as nat);
        let r = apply_swaps(layout, swaps);
        &&& r.shape.len() == layout.shape.len()
        &&& r.stride.len() == layout.stride.len()
        &&& r.shape[low as int] == layout.shape[(high + 1) as int]
        &&& r.stride[low as int] == layout.stride[(high + 1) as int]
        &&& (forall|p: nat| low <= p && p <= high ==>
                r.shape[(p+1) as int] == layout.shape[p as int]
                && r.stride[(p+1) as int] == layout.stride[p as int])
        &&& (forall|p: nat| (p < low || p > high + 1) && p < layout.shape.len() ==>
                r.shape[p as int] == layout.shape[p as int]
                && r.stride[p as int] == layout.stride[p as int])
    }),
    decreases high - low,
{
    let swaps = Seq::new((high - low + 1) as nat, |i: int| (high - i) as nat);
    lemma_apply_swaps_rank(layout, swaps);

    if high == low {
        // swaps = seq![low], single swap
        assert(swaps.len() == 1);
        assert(swaps.first() == low);
        let tail = swaps.skip(1);
        assert(tail.len() == 0);
        let after_first = apply_swap_layout(layout, swaps.first());
        // Unfold: apply_swaps(layout, swaps) = apply_swaps(after_first, tail) = after_first
        assert(apply_swaps(after_first, tail) == after_first);
        assert(after_first.shape[low as int] == layout.shape[(low + 1) as int]);
        assert(after_first.stride[low as int] == layout.stride[(low + 1) as int]);
    } else {
        let after = apply_swap_layout(layout, high);
        assert(swaps.first() == high);
        let ih_swaps = Seq::new((high - low) as nat, |i: int| ((high - 1) - i) as nat);
        assert(swaps.skip(1) =~= ih_swaps);

        lemma_consec_swaps_bubble(after, (high - 1) as nat, low);

        // Connect: apply_swaps(layout, swaps) == apply_swaps(after, ih_swaps)
        let result = apply_swaps(after, ih_swaps);
        assert(apply_swaps(layout, swaps) == result);

        // Facts about the first swap
        assert(after.shape[high as int] == layout.shape[(high + 1) as int]);
        assert(after.stride[high as int] == layout.stride[(high + 1) as int]);
        assert(after.shape[(high + 1) as int] == layout.shape[high as int]);
        assert(after.stride[(high + 1) as int] == layout.stride[high as int]);

        // IH gives: result.shape[low] == after.shape[high] (bubbled from high to low)
        assert(result.shape[low as int] == after.shape[high as int]);
        assert(result.stride[low as int] == after.stride[high as int]);
        // Chain: result[low] == after[high] == layout[high+1]
        assert(result.shape[low as int] == layout.shape[(high + 1) as int]);
        assert(result.stride[low as int] == layout.stride[(high + 1) as int]);

        assert forall|p: nat| low <= p && p <= high
            implies result.shape[(p+1) as int] == layout.shape[p as int]
                && result.stride[(p+1) as int] == layout.stride[p as int]
        by {
            if p < high {
                // IH: result[p+1] == after[p], and swap at high doesn't touch p < high
                assert(p as int != high as int && p as int != (high as int + 1));
                assert(after.shape[p as int] == layout.shape[p as int]);
                assert(after.stride[p as int] == layout.stride[p as int]);
            } else {
                // p == high: result[high+1] == after[high+1] (IH: unchanged, high+1 > high)
                assert(p == high);
                assert(result.shape[(high + 1) as int] == after.shape[(high + 1) as int]);
                assert(result.stride[(high + 1) as int] == after.stride[(high + 1) as int]);
            }
        };

        assert forall|p: nat| (p < low || p > high + 1) && p < layout.shape.len()
            implies result.shape[p as int] == layout.shape[p as int]
                && result.stride[p as int] == layout.stride[p as int]
        by {
            assert(p as int != high as int && p as int != (high as int + 1));
            assert(after.shape[p as int] == layout.shape[p as int]);
            assert(after.stride[p as int] == layout.stride[p as int]);
        };
    }
}

// ══════════════════════════════════════════════════════════════
// apply_swaps(interleaved, zipping_swaps) produces the zipped layout
// ══════════════════════════════════════════════════════════════

/// Invariant: after j extraction steps on the interleaved layout, positions are:
/// [0, j) = B modes, [j, 2j) = C modes, [2j, 2k+1) = untouched interleaved tail.
proof fn lemma_zipping_state_invariant(b: &LayoutSpec, m: nat, j: nat)
    requires
        complement_admissible(b, m),
        j <= b.shape.len(),
    ensures ({
        let il = LayoutSpec {
            shape: interleaved_zipped_shape(b, m),
            stride: interleaved_zipped_stride(b, m),
        };
        let st = apply_swaps(il, zipping_swaps(j));
        let c = complement(b, m);
        let k = b.shape.len();
        let iz_s = interleaved_zipped_shape(b, m);
        let iz_d = interleaved_zipped_stride(b, m);
        &&& st.shape.len() == 2 * k + 1
        &&& st.stride.len() == 2 * k + 1
        &&& (forall|p: nat| p < j ==>
                st.shape[p as int] == b.shape[p as int]
                && st.stride[p as int] == b.stride[p as int])
        &&& (forall|p: nat| j <= p && p < 2 * j ==>
                st.shape[p as int] == c.shape[(p - j) as int]
                && st.stride[p as int] == c.stride[(p - j) as int])
        &&& (forall|p: nat| 2 * j <= p && p < 2 * k + 1 ==>
                st.shape[p as int] == iz_s[p as int]
                && st.stride[p as int] == iz_d[p as int])
    }),
    decreases j,
{
    let il = LayoutSpec {
        shape: interleaved_zipped_shape(b, m),
        stride: interleaved_zipped_stride(b, m),
    };
    let c = complement(b, m);
    let k = b.shape.len();
    let iz_s = interleaved_zipped_shape(b, m);
    let iz_d = interleaved_zipped_stride(b, m);

    lemma_complement_rank(b, m);
    lemma_interleaved_shape_valid(b, m);
    lemma_apply_swaps_rank(il, zipping_swaps(j));

    if j == 0 {
        // zipping_swaps(0) = [], state = interleaved, all in tail range
    } else {
        let j1 = (j - 1) as nat;
        lemma_zipping_state_invariant(b, m, j1);

        // zipping_swaps(j) = zipping_swaps(j1) ++ extraction_swaps_for(j1)
        lemma_apply_swaps_concat(il, zipping_swaps(j1), extraction_swaps_for(j1));
        let prev = apply_swaps(il, zipping_swaps(j1));
        let ext = extraction_swaps_for(j1);
        // state = apply_swaps(prev, ext)

        // extraction_swaps_for(j1) = bubble with high=2j1, low=j1
        assert(j1 < k);
        assert(2 * j1 + 1 < 2 * k + 1);
        lemma_apply_swaps_rank(prev, ext);
        assert(prev.shape.len() == 2 * k + 1);
        assert(prev.stride.len() == 2 * k + 1);

        let bub = Seq::new((2 * j1 - j1 + 1) as nat, |i: int| (2 * j1 - i) as nat);
        assert(ext =~= bub);
        lemma_consec_swaps_bubble(prev, 2 * j1, j1);

        let st = apply_swaps(prev, ext);

        // [0, j): B modes
        assert forall|p: nat| p < j
            implies st.shape[p as int] == b.shape[p as int]
                && st.stride[p as int] == b.stride[p as int]
        by {
            if p < j1 {
                // p < low: unchanged by bubble, was B[p] by IH
            } else {
                // p == j1: bubbled from prev[2j1+1] = iz_s[2j1+1] = b.shape[j1]
                assert(p == j1);
                assert(st.shape[j1 as int] == prev.shape[(2 * j1 + 1) as int]);
                assert(prev.shape[(2 * j1 + 1) as int] == iz_s[(2 * j1 + 1) as int]);
                assert((2 * j1 + 1) % 2 == 1);
                assert((2 * j1 + 1 - 1) / 2 == j1 as int);
                assert(iz_s[(2 * j1 + 1) as int] == b.shape[j1 as int]);
                assert(st.stride[j1 as int] == prev.stride[(2 * j1 + 1) as int]);
                assert(prev.stride[(2 * j1 + 1) as int] == iz_d[(2 * j1 + 1) as int]);
                assert(iz_d[(2 * j1 + 1) as int] == b.stride[j1 as int]);
            }
        };

        // [j, 2j): C modes
        assert forall|p: nat| j <= p && p < 2 * j
            implies st.shape[p as int] == c.shape[(p - j) as int]
                && st.stride[p as int] == c.stride[(p - j) as int]
        by {
            // p in [j1+1, 2j1+1]: st[p] = st[(p-1)+1] = prev[p-1] (shifted)
            let p1 = (p - 1) as nat;
            assert(j1 <= p1 && p1 <= 2 * j1);
            assert(st.shape[p as int] == prev.shape[p1 as int]);
            assert(st.stride[p as int] == prev.stride[p1 as int]);

            if p1 < 2 * j1 {
                // p1 in [j1, 2j1): C[p1-j1] by IH
                assert(prev.shape[p1 as int] == c.shape[(p1 - j1) as int]);
                assert(prev.stride[p1 as int] == c.stride[(p1 - j1) as int]);
                assert(p1 - j1 == p - j);
            } else {
                // p1 == 2j1: tail = iz_s[2j1] = c.shape[j1]
                assert(p1 == 2 * j1);
                assert(prev.shape[p1 as int] == iz_s[(2 * j1) as int]);
                assert((2 * j1) % 2 == 0);
                assert(iz_s[(2 * j1) as int] == c.shape[j1 as int]);
                assert(p - j == j1);
                assert(prev.stride[p1 as int] == iz_d[(2 * j1) as int]);
                assert(iz_d[(2 * j1) as int] == c.stride[j1 as int]);
            }
        };

        // [2j, 2k+1): untouched tail
        assert forall|p: nat| 2 * j <= p && p < 2 * k + 1
            implies st.shape[p as int] == iz_s[p as int]
                && st.stride[p as int] == iz_d[p as int]
        by {
            // p >= 2j = 2j1+2 > 2j1+1 = high+1: unchanged by bubble
            assert(p > 2 * j1 + 1);
        };
    }
}

/// After applying zipping_swaps to the interleaved layout, we get the zipped layout.
proof fn lemma_zipping_swaps_produce_zipped(b: &LayoutSpec, m: nat)
    requires complement_admissible(b, m),
    ensures ({
        let c = complement(b, m);
        let interleaved = LayoutSpec {
            shape: interleaved_zipped_shape(b, m),
            stride: interleaved_zipped_stride(b, m),
        };
        let zipped = LayoutSpec {
            shape: b.shape.add(c.shape),
            stride: b.stride.add(c.stride),
        };
        let k = b.shape.len();
        let result = apply_swaps(interleaved, zipping_swaps(k));
        result.shape =~= zipped.shape && result.stride =~= zipped.stride
    }),
{
    let c = complement(b, m);
    let k = b.shape.len();
    let iz_s = interleaved_zipped_shape(b, m);
    let iz_d = interleaved_zipped_stride(b, m);

    lemma_complement_rank(b, m);
    lemma_zipping_state_invariant(b, m, k);

    let interleaved = LayoutSpec { shape: iz_s, stride: iz_d };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    let result = apply_swaps(interleaved, zipping_swaps(k));

    // From invariant at j=k: [0,k)=B, [k,2k)=C, [2k,2k+1)=tail
    assert(result.shape =~= zipped.shape) by {
        assert(result.shape.len() == 2 * k + 1);
        assert(zipped.shape.len() == k + (k + 1));
        assert forall|p: int| 0 <= p < (2 * k + 1) as int
            implies result.shape[p] == zipped.shape[p]
        by {
            let pn = p as nat;
            if pn < k {
                assert(zipped.shape[p] == b.shape[p]);
            } else if pn < 2 * k {
                assert(zipped.shape[p] == c.shape[(pn - k) as int]);
            } else {
                assert(pn == 2 * k);
                assert((2 * k) % 2 == 0);
                assert(iz_s[(2 * k) as int] == c.shape[((2 * k) / 2) as int]);
                assert(zipped.shape[p] == c.shape[k as int]);
            }
        };
    };

    assert(result.stride =~= zipped.stride) by {
        assert(result.stride.len() == 2 * k + 1);
        assert(zipped.stride.len() == k + (k + 1));
        assert forall|p: int| 0 <= p < (2 * k + 1) as int
            implies result.stride[p] == zipped.stride[p]
        by {
            let pn = p as nat;
            if pn < k {
                assert(zipped.stride[p] == b.stride[p]);
            } else if pn < 2 * k {
                assert(zipped.stride[p] == c.stride[(pn - k) as int]);
            } else {
                assert(pn == 2 * k);
                assert((2 * k) % 2 == 0);
                assert(iz_d[(2 * k) as int] == c.stride[((2 * k) / 2) as int]);
                assert(zipped.stride[p] == c.stride[k as int]);
            }
        };
    };
}

// ══════════════════════════════════════════════════════════════
// Zipped bijective (general case)
// ══════════════════════════════════════════════════════════════

/// For any complement-admissible B w.r.t. M, the zipped layout
/// (B.shape ++ complement.shape, B.stride ++ complement.stride)
/// is bijective onto [0, M).
///
/// Proof strategy: The interleaved layout (alternating C and B modes) is column-major,
/// hence bijective. A sequence of adjacent swaps transforms it to the zipped layout,
/// preserving both injectivity and surjectivity.
pub proof fn lemma_zipped_bijective(b: &LayoutSpec, m: nat)
    requires complement_admissible(b, m),
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
    let k = b.shape.len();
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    let interleaved = LayoutSpec {
        shape: interleaved_zipped_shape(b, m),
        stride: interleaved_zipped_stride(b, m),
    };

    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    lemma_interleaved_shape_valid(b, m);
    lemma_interleaved_shape_size(b, m);

    // 1. Interleaved is column-major
    lemma_interleaved_is_column_major(b, m);
    assert(interleaved.stride =~= column_major_strides(interleaved.shape));
    assert(interleaved == make_column_major(interleaved.shape));

    // 2. Column-major → bijective onto [0, M)
    crate::proof::injectivity_lemmas::lemma_column_major_bijective(interleaved.shape);
    assert(interleaved.is_bijective_upto(shape_size(interleaved.shape)));
    assert(shape_size(interleaved.shape) == m);

    // 3. Zipping swaps transform interleaved → zipped
    let swaps = zipping_swaps(k);
    lemma_zipping_swaps_bounded(k);

    // All swap indices are valid for the layout rank
    assert forall|j: nat| j < swaps.len()
        implies #[trigger] swaps[j as int] + 1 < interleaved.shape.len()
    by {
        // interleaved.shape.len() == 2k + 1
        // swaps[j] + 1 < 2k + 1 (from lemma_zipping_swaps_bounded)
    };

    // 4. apply_swaps preserves injective + surjective
    lemma_apply_swaps_preserves_injective(interleaved, swaps);
    lemma_apply_swaps_preserves_surjective(interleaved, swaps, m);
    lemma_apply_swaps_valid(interleaved, swaps);
    lemma_apply_swaps_size(interleaved, swaps);

    let result = apply_swaps(interleaved, swaps);

    // 5. The result has the same shape/stride as zipped
    lemma_zipping_swaps_produce_zipped(b, m);
    assert(result.shape =~= zipped.shape);
    assert(result.stride =~= zipped.stride);

    // 6. Transfer bijectivity via extensional equality of shape/stride
    // Since result and zipped have the same shape/stride, they have the same offset function
    assert(result.is_injective());
    assert(result.is_surjective_upto(m));
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
    vstd::arithmetic::mul::lemma_mul_basics(m0 as int);
    assert(1int * (m0 as int) == m0 as int);
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
