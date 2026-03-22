use vstd::prelude::*;

verus! {

/// If d > 0, then (x % d) < d.
pub proof fn lemma_mod_bound(x: nat, d: nat)
    requires d > 0,
    ensures x % d < d,
{
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, d as int);
}

/// If d > 0, then x == (x % d) + d * (x / d).
pub proof fn lemma_div_mod_identity(x: nat, d: nat)
    requires d > 0,
    ensures x == (x % d) + d * (x / d),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
}

/// If d > 0 and x < d, then x % d == x.
pub proof fn lemma_mod_small(x: nat, d: nat)
    requires d > 0, x < d,
    ensures x % d == x,
{
    vstd::arithmetic::div_mod::lemma_small_mod(x, d);
}

/// If d > 0 and x < d, then x / d == 0.
pub proof fn lemma_div_small(x: nat, d: nat)
    requires d > 0, x < d,
    ensures x / d == 0,
{
    // x = 0 * d + x, so x / d == 0
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x as int, d as int, 0int, x as int);
}

/// Product of positive naturals is positive.
pub proof fn lemma_mul_pos(a: nat, b: nat)
    requires a > 0, b > 0,
    ensures a * b > 0,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(a as int, b as int);
}

/// (d * x) / d == x for d > 0.
pub proof fn lemma_div_mul_cancel(d: nat, x: nat)
    requires d > 0,
    ensures (d * x) / d == x,
{
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(x as int, d as int);
}

/// For a < d and d > 0: (a + d * b) % d == a and (a + d * b) / d == b.
pub proof fn lemma_div_mod_decompose(a: nat, b: nat, d: nat)
    requires d > 0, a < d,
    ensures
        (a + d * b) % d == a,
        (a + d * b) / d == b,
{
    // Use the converse: if x == q * d + r with 0 <= r < d, then x % d == r and x / d == q
    assert(a + d * b == b * (d as int) + (a as int)) by {
        assert(d * b == b * d) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(d as int, b as int);
        };
    };
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (a + d * b) as int, d as int, b as int, a as int
    );
}

/// If a < b and c > 0, then a + c * x < c * y when x < y.
pub proof fn lemma_mixed_radix_bound(coord: nat, extent: nat, rest: nat, rest_size: nat)
    requires
        coord < extent,
        rest < rest_size,
        extent > 0,
    ensures
        coord + extent * rest < extent * rest_size,
{
    // coord + extent * rest < extent + extent * rest = extent * (1 + rest) <= extent * rest_size
    assert(coord + extent * rest < extent + extent * rest);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(extent as int, 1int, rest as int);
    assert(extent + extent * rest == extent * (1 + rest));
    assert(1 + rest <= rest_size);
    vstd::arithmetic::mul::lemma_mul_inequality(1 + rest as int, rest_size as int, extent as int);
    assert(extent * (1 + rest) <= extent * rest_size) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative(extent as int, (1 + rest) as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(extent as int, rest_size as int);
    };
}

/// If d > 0 and x < d * y, then x / d < y.
pub proof fn lemma_div_upper_bound(x: nat, d: nat, y: nat)
    requires d > 0, x < d * y, y > 0,
    ensures x / d < y,
{
    // x / d < y  <==>  x / d <= y - 1  (since both are nat)
    // We show: x/d <= (d*y - 1)/d = y - 1

    // Direct contradiction approach:

    // Step 2: d*(y-1) <= d*y - 1 (since d >= 1, so d*y - d*(y-1) = d >= 1)
    // Step 3: x <= d*y - 1 (since x < d*y)
    // Step 4: d*(y-1) <= x is NOT necessarily true, but we don't need it
    //         We need x/d <= (d*(y-1) + (d-1))/d, but let's just go direct

    // Direct: suppose x/d >= y, then x >= d*y (contradiction)
    if x / d >= y {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
        // x == d * (x/d) + x%d >= d * y
        vstd::arithmetic::mul::lemma_mul_inequality(y as int, (x / d) as int, d as int);
        assert(d * (x / d) >= d * y) by {
            vstd::arithmetic::mul::lemma_mul_is_commutative(d as int, (x / d) as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(d as int, y as int);
        };
        assert(x >= d * (x / d)) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
        };
        assert(false);
    }
}

/// 0 * b == 0 for any b.
pub proof fn lemma_mul_zero(b: int)
    ensures 0int * b == 0,
{
}

/// If 0 <= a and 0 <= b, then 0 <= a * b.
pub proof fn lemma_mul_nonneg(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures a * b >= 0,
{
    vstd::arithmetic::mul::lemma_mul_nonnegative(a, b);
}

/// If 0 <= a <= c and 0 <= b, then a * b <= c * b.
pub proof fn lemma_mul_le_right(a: int, c: int, b: int)
    requires 0 <= a <= c, b >= 0,
    ensures a * b <= c * b,
{
    vstd::arithmetic::mul::lemma_mul_inequality(a, c, b);
}

/// If d > 0 and x % d == 0, then (c * x) % d == 0 for any c >= 0.
pub proof fn lemma_multiple_scaled(x: int, c: nat, d: int)
    requires d > 0, x % d == 0, x >= 0,
    ensures (c as int * x) % d == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d);
    // x == d * (x/d) + 0
    let q = x / d;
    assert(x == d * q);
    // c * x == c * d * q
    vstd::arithmetic::mul::lemma_mul_is_associative(c as int, d, q);
    // c * (d * q) == (c * d) * q, but we want c * x % d == 0
    // c * x == c * (d * q) = (c * q) * d
    vstd::arithmetic::mul::lemma_mul_is_associative(c as int, d, q);
    vstd::arithmetic::mul::lemma_mul_is_commutative(d, q);
    // x == q * d, so c * x == c * q * d
    vstd::arithmetic::mul::lemma_mul_is_associative(c as int, q, d);
    // c * x == (c * q) * d
    assert(c as int * x == (c as int * q) * d);
    // (c * q) * d % d == 0
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(c as int * q, d);
}

/// Sum of two multiples of d is a multiple of d.
pub proof fn lemma_sum_multiples(a: int, b: int, d: int)
    requires d > 0, a % d == 0, b % d == 0,
    ensures (a + b) % d == 0,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a, b, d);
    // (a + b) % d == ((a % d) + (b % d)) % d == (0 + 0) % d == 0 % d == 0
    assert((a % d) + (b % d) == 0int);
    vstd::arithmetic::div_mod::lemma_small_mod(0nat, d as nat);
}

/// A value in [0, d) that equals a multiple of d must be 0.
pub proof fn lemma_small_multiple_is_zero(x: int, d: int)
    requires d > 0, 0 <= x < d, x % d == 0,
    ensures x == 0,
{
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, d as nat);
}

/// If d > 0 and x % d == 0 and y % d == 0, then (x - y) % d == 0.
pub proof fn lemma_diff_multiples(x: int, y: int, d: int)
    requires d > 0, x % d == 0, y % d == 0,
    ensures (x - y) % d == 0,
{
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(x, y, d);
    // (x - y) % d == ((x % d) - (y % d)) % d == (0 - 0) % d == 0
    assert((x % d) - (y % d) == 0int);
    vstd::arithmetic::div_mod::lemma_small_mod(0nat, d as nat);
}

/// Divisibility transitivity: if a % b == 0 and b % c == 0 (and b,c > 0, a >= 0), then a % c == 0.
pub proof fn lemma_divisibility_transitive(a: int, b: int, c: int)
    requires c > 0, b > 0, a >= 0, a % b == 0, b % c == 0,
    ensures a % c == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, b);
    // a == b * (a/b)
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, c);
    // b == c * (b/c)
    let qa = a / b;
    let qb = b / c;
    assert(a == b * qa);
    assert(b == c * qb);
    // a == (c * qb) * qa == c * (qb * qa)
    vstd::arithmetic::mul::lemma_mul_is_associative(c, qb, qa);
    assert(a == c * (qb * qa));
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(qb * qa, c);
}

/// If a % d == 0 and d > 0, then (n * a) % d == 0 for any nat n.
pub proof fn lemma_multiple_of_multiple(a: int, n: nat, d: int)
    requires d > 0, a >= 0, a % d == 0,
    ensures (n as int * a) % d == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, d);
    let q = a / d;
    assert(a == d * q);
    vstd::arithmetic::mul::lemma_mul_is_associative(n as int, d, q);
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, d);
    vstd::arithmetic::mul::lemma_mul_is_associative(d, n as int, q);
    assert(n as int * a == d * (n as int * q));
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(n as int * q, d);
}

// ══════════════════════════════════════════════════════════════
// Div/mod associativity lemmas (for product associativity)
// ══════════════════════════════════════════════════════════════

/// (x / a) / b == x / (a * b) for a, b > 0.
pub proof fn lemma_div_div(x: nat, a: nat, b: nat)
    requires a > 0, b > 0,
    ensures (x / a) / b == x / (a * b),
{
    // Use fundamental_div_mod to decompose x, then show both sides equal.
    // x = a * q1 + r1 where q1 = x/a, r1 = x%a, 0 <= r1 < a
    // q1 = b * q2 + r2 where q2 = q1/b, r2 = q1%b, 0 <= r2 < b
    // LHS = q2
    // x = a * (b * q2 + r2) + r1 = a*b*q2 + a*r2 + r1
    // a*r2 + r1 < a*b (since r2 < b, r1 < a: a*r2 + r1 < a*b)
    // So x / (a*b) = q2 = RHS
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, a as int);
    let q1 = x / a;
    let r1 = x % a;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, a as int);

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q1 as int, b as int);
    let q2 = q1 / b;
    let r2 = q1 % b;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(q1 as int, b as int);

    // x == a * (b * q2 + r2) + r1 == a*b*q2 + a*r2 + r1
    assert(x == a * q1 + r1);
    assert(q1 == b * q2 + r2);
    assert(x == a * (b * q2 + r2) + r1) by {
        assert(a * q1 == a * (b * q2 + r2));
    };
    // a * (b * q2 + r2) == a*b*q2 + a*r2
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a as int, (b * q2) as int, r2 as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(a as int, b as int, q2 as int);
    assert(x == (a * b) * q2 + (a * r2 + r1));

    // remainder < a*b
    assert(a * r2 + r1 < a * b) by {
        // a * r2 <= a * (b-1) = a*b - a
        vstd::arithmetic::mul::lemma_mul_inequality(r2 as int, (b - 1) as int, a as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, r2 as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, (b - 1) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(a as int, b as int, 1int);
    };

    // a*b > 0
    vstd::arithmetic::mul::lemma_mul_strictly_positive(a as int, b as int);

    // By converse of fundamental_div_mod: x = (a*b)*q2 + rem, 0 <= rem < a*b
    // implies x / (a*b) == q2
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        x as int, (a * b) as int, q2 as int, (a * r2 + r1) as int
    );
}

/// (x % (a * b)) % a == x % a for a, b > 0.
pub proof fn lemma_mod_mod(x: nat, a: nat, b: nat)
    requires a > 0, b > 0,
    ensures (x % (a * b)) % a == x % a,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(a as int, b as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, (a * b) as int);
    let q = x / (a * b);
    let r = x % (a * b);
    // x == (a*b)*q + r
    // x % a == ((a*b)*q + r) % a == r % a  (since (a*b)*q is a multiple of a)
    vstd::arithmetic::mul::lemma_mul_is_associative(a as int, b as int, q as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(b as int, q as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(a as int, q as int, b as int);
    // (a*b)*q == a*(b*q), so it's a multiple of a
    assert((a * b) * q == a * (b * q));
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(b as int * q as int, a as int);
    // (a * (b*q)) % a == 0
    vstd::arithmetic::div_mod::lemma_add_mod_noop((a * b) * q as int, r as int, a as int);
    // x % a == ((a*b)*q % a + r % a) % a == (0 + r % a) % a == r % a
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(r as int, a as int);
    vstd::arithmetic::div_mod::lemma_small_mod((r % a) as nat, a);
}

/// (x % (a * b)) / a == (x / a) % b for a, b > 0.
pub proof fn lemma_mod_div_mixed(x: nat, a: nat, b: nat)
    requires a > 0, b > 0,
    ensures (x % (a * b)) / a == (x / a) % b,
{
    vstd::arithmetic::mul::lemma_mul_strictly_positive(a as int, b as int);

    // Decompose: x = a*q1 + r1, q1 = b*q2 + r2
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, a as int);
    let q1 = x / a;
    let r1 = x % a;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, a as int);

    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q1 as int, b as int);
    let q2 = q1 / b;
    let r2 = q1 % b;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(q1 as int, b as int);

    // RHS = r2

    // x = a*(b*q2 + r2) + r1 = a*b*q2 + a*r2 + r1
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a as int, (b * q2) as int, r2 as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(a as int, b as int, q2 as int);
    assert(x == (a * b) * q2 + (a * r2 + r1));

    // remainder = a*r2 + r1 < a*b
    assert(a * r2 + r1 < a * b) by {
        vstd::arithmetic::mul::lemma_mul_inequality(r2 as int, (b - 1) as int, a as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, r2 as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, (b - 1) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(a as int, b as int, 1int);
    };

    // So x % (a*b) == a*r2 + r1
    assert(x == q2 as int * ((a * b) as int) + (a * r2 + r1) as int) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative((a * b) as int, q2 as int);
    };
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        x as int, (a * b) as int, q2 as int, (a * r2 + r1) as int
    );

    // LHS = (a*r2 + r1) / a
    // a*r2 + r1 = r1 + r2*a, where r1 < a
    // So (a*r2 + r1) / a == r2
    assert((a * r2 + r1) as int == r2 as int * (a as int) + r1 as int) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, r2 as int);
    };
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (a * r2 + r1) as int, a as int, r2 as int, r1 as int
    );
    assert((a * r2 + r1) / a == r2);

    // r2 == q1 % b == (x / a) % b
}

// ══════════════════════════════════════════════════════════════
// Modular scaling (for recursive composition straddle case)
// ══════════════════════════════════════════════════════════════

/// Modular scaling: a * (x % b) == (a * x) % (a * b) for a, b > 0.
///
/// Proof: x = b*q + r where r = x%b. Then a*x = a*b*q + a*r.
/// Since 0 <= a*r < a*b, (a*x) % (a*b) == a*r == a*(x%b).
pub proof fn lemma_mod_scale(x: nat, a: nat, b: nat)
    requires a > 0, b > 0,
    ensures a * (x % b) == (a * x) % (a * b),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, b as int);
    let q = x / b;
    let r = x % b;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, b as int);
    // x == b*q + r, 0 <= r < b
    // a*x == a*(b*q + r) == a*b*q + a*r
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a as int, (b * q) as int, r as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(a as int, b as int, q as int);
    assert(a * x == (a * b) * q + a * r);
    // 0 <= a*r < a*b
    assert(a * r < a * b) by {
        vstd::arithmetic::mul::lemma_mul_inequality(r as int, (b - 1) as int, a as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, r as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, (b - 1) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(a as int, b as int, 1int);
    };
    vstd::arithmetic::mul::lemma_mul_strictly_positive(a as int, b as int);
    // By converse: (a*x) % (a*b) == a*r == a*(x%b)
    assert(a * x == q as int * ((a * b) as int) + (a * r) as int) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative((a * b) as int, q as int);
    };
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (a * x) as int, (a * b) as int, q as int, (a * r) as int
    );
}

/// Division scaling: x / b == (a * x) / (a * b) for a, b > 0.
///
/// Proof: same decomposition as lemma_mod_scale — the quotient is q in both cases.
pub proof fn lemma_div_scale(x: nat, a: nat, b: nat)
    requires a > 0, b > 0,
    ensures x / b == (a * x) / (a * b),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, b as int);
    let q = x / b;
    let r = x % b;
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, b as int);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(a as int, (b * q) as int, r as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(a as int, b as int, q as int);
    assert(a * x == (a * b) * q + a * r);
    assert(a * r < a * b) by {
        vstd::arithmetic::mul::lemma_mul_inequality(r as int, (b - 1) as int, a as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, r as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(a as int, (b - 1) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(a as int, b as int, 1int);
    };
    vstd::arithmetic::mul::lemma_mul_strictly_positive(a as int, b as int);
    assert(a * x == q as int * ((a * b) as int) + (a * r) as int) by {
        vstd::arithmetic::mul::lemma_mul_is_commutative((a * b) as int, q as int);
    };
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (a * x) as int, (a * b) as int, q as int, (a * r) as int
    );
}

} // verus!
