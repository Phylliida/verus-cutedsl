use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::composition::*;
use crate::divide::*;
use crate::proof::shape_lemmas::*;
use crate::proof::complement_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Helper: compose preserves rank (number of modes)
// ══════════════════════════════════════════════════════════════

/// compose(A, B) has exactly rank(B) modes.
pub proof fn lemma_compose_rank(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(),
    ensures
        compose(a, b).shape.len() == b.shape.len(),
        compose(a, b).stride.len() == b.shape.len(),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
    } else if b.shape.len() == 1 {
        // compose_single_mode returns 1-mode layout
    } else {
        let first = compose_single_mode(a, b.shape.first(), b.stride.first() as nat);
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        lemma_compose_rank(a, rest_b);
        // first has 1 mode, rest has b.shape.len() - 1 modes
        // total: 1 + (b.shape.len() - 1) = b.shape.len()
    }
}

// ══════════════════════════════════════════════════════════════
// Logical divide: structural properties
// ══════════════════════════════════════════════════════════════

/// The logical divide of A by B has rank = rank(B) + rank(complement(B, size(A))).
pub proof fn lemma_divide_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        let expected_rank = b.shape.len() + c.shape.len();
        &&& logical_divide(a, b).shape.len() == expected_rank
        &&& logical_divide(a, b).stride.len() == expected_rank
    })),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    lemma_complement_rank(b, m);

    // Need zipped.valid() for compose_rank precondition
    lemma_complement_shape_valid(b, m);

    assert(shape_valid(zipped.shape)) by {
        assert forall|i: int| 0 <= i < zipped.shape.len() implies #[trigger] zipped.shape[i] > 0 by {
            if i < b.shape.len() as int {
                assert(zipped.shape[i] == b.shape[i]);
            } else {
                let ci = (i - b.shape.len()) as int;
                assert(zipped.shape[i] == c.shape[ci]);
            }
        };
    };
    assert(zipped.shape.len() == zipped.stride.len());

    lemma_compose_rank(a_val, zipped);
}

/// For a 1D tile B, logical_divide produces rank(B) + rank(B) + 1 = rank(B) + 2 modes.
/// (complement of 1D B has rank 2)
pub proof fn lemma_divide_1d_tile_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        b.shape.len() == 1,
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        &&& logical_divide(a, b).shape.len() == 3
        &&& logical_divide(a, b).stride.len() == 3
    })),
{
    let m = shape_size(a.shape);
    lemma_complement_rank(b, m);
    lemma_divide_rank(a, b);
}

// ══════════════════════════════════════════════════════════════
// Tile count: complement size gives number of tiles
// ══════════════════════════════════════════════════════════════

/// For a 1D tile, complement size * tile size == total size.
pub proof fn lemma_divide_tile_count_1d(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        b.shape.len() == 1,
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        shape_size(c.shape) * shape_size(b.shape) == m
    })),
{
    let m = shape_size(a.shape);
    lemma_complement_size_1d(b, m);
}

// ══════════════════════════════════════════════════════════════
// Divide size preservation
// ══════════════════════════════════════════════════════════════

/// logical_divide(A, B) has the same size as A.
pub proof fn lemma_divide_size(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures
        shape_size(logical_divide(a, b).shape) == shape_size(a.shape),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped is valid
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    assert(shape_valid(zipped.shape)) by {
        assert forall|i: int| 0 <= i < zipped.shape.len()
        implies #[trigger] zipped.shape[i] > 0 by {
            if i < b.shape.len() as int {
                assert(zipped.shape[i] == b.shape[i]);
            } else {
                assert(zipped.shape[i] == c.shape[(i - b.shape.len()) as int]);
            }
        };
    };
    assert(zipped.valid());

    // compose(a, zipped).shape =~= zipped.shape
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, zipped);

    // size(zipped.shape) = size(b.shape ++ c.shape) = size(b.shape) * size(c.shape)
    crate::proof::product_lemmas::lemma_shape_size_append(b.shape, c.shape);

    // size(c.shape) * size(b.shape) = m
    lemma_complement_size(b, m);

    // So size(zipped.shape) = size(b.shape) * size(c.shape) = m = size(a.shape)
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(b.shape) as int,
        shape_size(c.shape) as int,
    );
}

/// Generalized tile count: complement size * tile size == total size.
pub proof fn lemma_divide_tile_count(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures ({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        shape_size(c.shape) * shape_size(b.shape) == m
    }),
{
    let m = shape_size(a.shape);
    lemma_complement_size(b, m);
}

// ══════════════════════════════════════════════════════════════
// Zipped identity offset (1D column-major B)
// ══════════════════════════════════════════════════════════════

/// For 1D column-major B = (N):(1), the zipped layout (B, complement(B, M))
/// has identity offset: zipped.offset(x) == x.
///
/// The zipped layout has shape (N, 1, M/N) and stride (1, 1, N).
/// Delinearize gives coords (x%N, 0, x/N), and dot product recovers x.
pub proof fn lemma_zipped_identity_1d(b: &LayoutSpec, m: nat, x: nat)
    requires
        complement_admissible(b, m),
        b.shape.len() == 1,
        b.stride[0] == 1,
        x < m,
    ensures ({
        let c = complement(b, m);
        let zipped = LayoutSpec {
            shape: b.shape.add(c.shape),
            stride: b.stride.add(c.stride),
        };
        zipped.offset(x) == x as int
    }),
{
    let n = b.shape[0];
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    lemma_complement_rank(b, m);

    // Complement shape/stride for 1D B = (N):(1)
    // sp(0) = N * 1 = N
    let sp0 = (n as int) * 1int;
    assert(sp0 == n as int);
    // cs[0] = d_0 = 1, cs[1] = M / sp0 = M / N
    assert(c.shape[0] == 1nat);
    let k = ((m as int) / sp0) as nat;
    assert(c.shape[1] == k);
    assert(c.stride[0] == 1int);
    assert(c.stride[1] == sp0);

    // Zipped = (N, 1, K):(1, 1, N)
    assert(zipped.shape =~= seq![n, 1nat, k]);
    assert(zipped.stride =~= seq![1int, 1int, n as int]);

    // k > 0 (from complement shape validity)
    lemma_complement_shape_valid(b, m);
    assert(k > 0);

    // n * k == m (from complement size)
    lemma_complement_size_1d(b, m);
    // shape_size(c.shape) * shape_size(b.shape) == m
    // shape_size(c.shape) = 1 * k = k, shape_size(b.shape) = n
    lemma_shape_size_positive(b.shape);
    // shape_size(seq![n]) = n * shape_size(empty) = n * 1 = n
    assert(b.shape.len() == 1);
    assert(shape_size(b.shape) == b.shape.first() * shape_size(b.shape.skip(1)));
    assert(b.shape.skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(n as int);
    assert(shape_size(b.shape) == n);

    // shape_size(c.shape) for c.shape = (1, k)
    assert(c.shape.len() == 2);
    assert(shape_size(c.shape) == c.shape.first() * shape_size(c.shape.skip(1)));
    assert(c.shape.first() == 1nat);
    // shape_size(c.shape.skip(1)) for skip = (k,)
    assert(c.shape.skip(1).len() == 1);
    assert(shape_size(c.shape.skip(1))
        == c.shape.skip(1).first() * shape_size(c.shape.skip(1).skip(1)));
    assert(c.shape.skip(1).first() == k);
    assert(c.shape.skip(1).skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(k as int);
    assert(shape_size(c.shape.skip(1)) == k);
    assert(shape_size(c.shape) == 1 * k);
    vstd::arithmetic::mul::lemma_mul_basics(k as int);
    assert(shape_size(c.shape) == k);

    assert(k * n == m);
    vstd::arithmetic::mul::lemma_mul_is_commutative(k as int, n as int);
    assert(n * k == m);

    // x / n < k (since x < m = n * k)
    crate::proof::integer_helpers::lemma_div_upper_bound(x, n, k);
    let xn = x / n;
    assert(xn < k);

    // Now unfold delinearize(x, (N, 1, K)) step by step
    let s = zipped.shape;
    assert(s =~= seq![n, 1nat, k]);

    // Level 0: coord[0] = x % N, remaining index = x / N, remaining shape = (1, K)
    let c0 = x % n;
    let r0 = x / n;
    assert(s.first() == n);
    assert(s.skip(1) =~= seq![1nat, k]);

    // Level 1: coord[1] = r0 % 1 = 0, remaining index = r0 / 1 = r0, remaining shape = (K,)
    assert(s.skip(1).first() == 1nat);
    assert(s.skip(1).skip(1) =~= seq![k]);
    assert(r0 % 1 == 0nat);
    assert(r0 / 1 == r0);

    // Level 2: coord[2] = r0 % K, remaining shape = ()
    assert(s.skip(1).skip(1).first() == k);
    assert(s.skip(1).skip(1).skip(1) =~= Seq::<nat>::empty());
    crate::proof::integer_helpers::lemma_mod_small(xn, k);
    assert(r0 % k == r0);

    // Build delinearize step by step
    // delinearize(x, (N,1,K)) = seq![x%N] ++ delinearize(x/N, (1,K))
    let d0 = delinearize(r0, s.skip(1));
    assert(delinearize(x, s) =~= seq![c0].add(d0));

    // delinearize(r0, (1,K)) = seq![r0%1] ++ delinearize(r0/1, (K,))
    let d1 = delinearize(r0, s.skip(1).skip(1));
    assert(d0 =~= seq![0nat].add(d1));

    // delinearize(r0, (K,)) = seq![r0%K] ++ delinearize(r0/K, ())
    assert(d1 =~= seq![xn].add(delinearize(xn / k, Seq::<nat>::empty())));
    assert(delinearize(xn / k, Seq::<nat>::empty()) =~= Seq::<nat>::empty());
    assert(d1 =~= seq![xn]);
    assert(d0 =~= seq![0nat, xn]);

    let coords = delinearize(x, s);
    assert(coords =~= seq![c0, 0nat, xn]);

    // Now compute dot_product_nat_int((c0, 0, xn), (1, 1, N))
    let strides = zipped.stride;
    assert(strides =~= seq![1int, 1int, n as int]);

    // dot = c0 * 1 + dot((0, xn), (1, N))
    //     = c0 + 0 * 1 + dot((xn,), (N,))
    //     = c0 + xn * N + dot((), ())
    //     = c0 + xn * N + 0
    //     = x%N + (x/N)*N = x (by fundamental div/mod)

    // Unfold dot_product_nat_int directly on coords/strides (3 levels)
    lemma_delinearize_len(x, s);
    assert(coords.len() == 3);
    assert(strides.len() == 3);

    // Level 0: coords.first() * strides.first() + dot(skip(1), skip(1))
    assert(coords.first() == c0);
    assert(strides.first() == 1int);
    let cs1 = coords.skip(1);
    let ss1 = strides.skip(1);
    assert(dot_product_nat_int(coords, strides)
        == (c0 as int) * 1int + dot_product_nat_int(cs1, ss1));
    vstd::arithmetic::mul::lemma_mul_basics(c0 as int);

    // Level 1: cs1 = delinearize(r0, (1,K)), ss1 = (1, N)
    assert(cs1.len() == 2) by { lemma_delinearize_len(r0, s.skip(1)); };
    assert(cs1.first() == 0nat);
    assert(ss1 =~= seq![1int, n as int]);
    assert(ss1.first() == 1int);
    let cs2 = cs1.skip(1);
    let ss2 = ss1.skip(1);
    assert(dot_product_nat_int(cs1, ss1)
        == (0nat as int) * 1int + dot_product_nat_int(cs2, ss2));

    // Level 2: cs2 = delinearize(r0, (K,)), ss2 = (N,)
    assert(cs2.len() == 1) by { lemma_delinearize_len(r0, s.skip(1).skip(1)); };
    assert(cs2.first() == xn);
    assert(ss2 =~= seq![n as int]);
    assert(ss2.first() == n as int);
    let cs3 = cs2.skip(1);
    let ss3 = ss2.skip(1);
    assert(cs3.len() == 0);
    assert(dot_product_nat_int(cs2, ss2)
        == (xn as int) * (n as int) + dot_product_nat_int(cs3, ss3));
    assert(dot_product_nat_int(cs3, ss3) == 0int);

    // Total: c0 + 0 + xn * n = x%n + (x/n)*n = x
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, n as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, xn as int);
    assert(dot_product_nat_int(coords, strides) == x as int);
}

// ══════════════════════════════════════════════════════════════
// Divide offset correctness (1D A, 1D column-major B)
// ══════════════════════════════════════════════════════════════

/// For rank-1 A and column-major B = (N):(1),
/// logical_divide(A, B).offset(x) == A.offset(x).
///
/// This is the key tiling theorem: dividing A into tiles of size N
/// preserves the offset function — each element maps to the same
/// physical location.
pub proof fn lemma_divide_offset_1d_a(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.shape.len() == 1,
        b.stride[0] == 1,
        x < shape_size(a.shape),
    ensures
        logical_divide(a, b).offset(x) == a.offset(x),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped is valid
    lemma_complement_rank(b, m);
    lemma_complement_shape_valid(b, m);
    assert(shape_valid(zipped.shape)) by {
        assert forall|i: int| 0 <= i < zipped.shape.len()
        implies #[trigger] zipped.shape[i] > 0 by {
            if i < b.shape.len() as int {
                assert(zipped.shape[i] == b.shape[i]);
            } else {
                assert(zipped.shape[i] == c.shape[(i - b.shape.len()) as int]);
            }
        };
    };
    assert(zipped.valid());

    // zipped has non-negative strides
    lemma_complement_positive_strides(b, m);
    assert(zipped.non_negative_strides()) by {
        assert forall|i: int| 0 <= i < zipped.stride.len()
        implies #[trigger] zipped.stride[i] >= 0 by {
            if i < b.stride.len() as int {
                assert(zipped.stride[i] == b.stride[i]);
            } else {
                assert(zipped.stride[i] == c.stride[(i - b.stride.len()) as int]);
                assert(c.stride[(i - b.stride.len()) as int] > 0);
            }
        };
    };

    // zipped.size() == m (from lemma_divide_size logic)
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, zipped);
    crate::proof::product_lemmas::lemma_shape_size_append(b.shape, c.shape);
    lemma_complement_size(b, m);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(b.shape) as int,
        shape_size(c.shape) as int,
    );
    assert(shape_size(zipped.shape) == m);
    assert(x < shape_size(zipped.shape));

    // zipped.offset(x) == x
    lemma_zipped_identity_1d(b, m, x);
    assert(zipped.offset(x) == x as int);

    // zipped.offset(x) < a.shape.first() (since x < m = a.shape.first() for 1D A)
    // shape_size(seq![a.shape[0]]) = a.shape[0]
    assert(a.shape.len() == 1);
    assert(shape_size(a.shape) == a.shape.first() * shape_size(a.shape.skip(1)));
    assert(a.shape.skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(a.shape.first() as int);
    assert(m == a.shape.first());
    assert(zipped.offset(x) >= 0);
    assert(zipped.offset(x) < a.shape.first() as int);

    // By compose correctness: compose(A, zipped).offset(x) == A.offset(zipped.offset(x))
    crate::proof::composition_lemmas::lemma_compose_correct(a_val, zipped, x);
    assert(compose(a_val, zipped).offset(x) == a_val.offset(zipped.offset(x) as nat));

    // zipped.offset(x) == x, so A.offset(zipped.offset(x)) == A.offset(x)
    assert(zipped.offset(x) as nat == x);
}

/// For rank-1 A and column-major B, logical_divide preserves injectivity.
pub proof fn lemma_divide_injective_1d_a(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.shape.len() == 1,
        b.stride[0] == 1,
        a.is_injective(),
    ensures
        logical_divide(a, b).is_injective(),
{
    let d = logical_divide(a, b);
    let m = shape_size(a.shape);

    // divide has same size as A
    lemma_divide_size(a, b);
    assert(shape_size(d.shape) == m);

    // For all i != j < size: divide.offset(i) != divide.offset(j)
    assert forall|i: nat, j: nat|
        i < shape_size(d.shape) && j < shape_size(d.shape) && i != j
    implies #[trigger] d.offset(i) != #[trigger] d.offset(j) by {
        // divide.offset(i) == a.offset(i), divide.offset(j) == a.offset(j)
        lemma_divide_offset_1d_a(a, b, i);
        lemma_divide_offset_1d_a(a, b, j);
        // a is injective: i != j => a.offset(i) != a.offset(j)
        assert(a.is_injective());
        assert(i < m && j < m);
    };
}

// ══════════════════════════════════════════════════════════════
// Tiled divide: structural properties
// ══════════════════════════════════════════════════════════════

/// divide_tile has shape =~= b.shape (same rank as the tiling layout).
pub proof fn lemma_divide_tile_shape(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures
        divide_tile(a, b).shape =~= b.shape,
        divide_tile(a, b).shape.len() == b.shape.len(),
{
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let b_val = LayoutSpec { shape: b.shape, stride: b.stride };
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, b_val);
}

/// divide_rest has shape =~= complement(B, M).shape.
pub proof fn lemma_divide_rest_shape(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures ({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        &&& divide_rest(a, b).shape =~= c.shape
        &&& divide_rest(a, b).shape.len() == c.shape.len()
    }),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    lemma_complement_valid(b, m);
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, c);
}

/// The tile count (from rest layout) times tile size equals total size.
pub proof fn lemma_tiled_divide_size_identity(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures ({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        shape_size(b.shape) * shape_size(c.shape) == m
    }),
{
    lemma_divide_tile_count(a, b);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(complement(b, shape_size(a.shape)).shape) as int,
        shape_size(b.shape) as int,
    );
}

} // verus!
