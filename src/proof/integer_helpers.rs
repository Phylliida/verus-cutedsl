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

} // verus!
