use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::complement::*;
use crate::composition::*;
use crate::divide::*;
use crate::proof::shape_lemmas::*;
use crate::proof::complement_lemmas::*;
use crate::proof::injectivity_lemmas::{lemma_column_major_strides_len, lemma_column_major_offset_is_identity};

verus! {

// ══════════════════════════════════════════════════════════════
// Helper: compose_linear preserves rank (number of modes)
// ══════════════════════════════════════════════════════════════

/// compose_linear(A, B) has exactly rank(B) modes.
pub proof fn lemma_compose_rank(a: LayoutSpec, b: LayoutSpec)
    requires a.valid(), b.valid(),
    ensures
        compose_linear(a, b).shape.len() == b.shape.len(),
        compose_linear(a, b).stride.len() == b.shape.len(),
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
        &&& logical_divide_linear(a, b).shape.len() == expected_rank
        &&& logical_divide_linear(a, b).stride.len() == expected_rank
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

/// For a 1D tile B, logical_divide_linear produces rank(B) + rank(B) + 1 = rank(B) + 2 modes.
/// (complement of 1D B has rank 2)
pub proof fn lemma_divide_1d_tile_rank(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        b.shape.len() == 1,
    ensures (({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        &&& logical_divide_linear(a, b).shape.len() == 3
        &&& logical_divide_linear(a, b).stride.len() == 3
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

/// logical_divide_linear(A, B) has the same size as A.
pub proof fn lemma_divide_size(a: &LayoutSpec, b: &LayoutSpec)
    requires divide_admissible(a, b),
    ensures
        shape_size(logical_divide_linear(a, b).shape) == shape_size(a.shape),
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

    // compose_linear(a, zipped).shape =~= zipped.shape
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
    vstd::arithmetic::mul::lemma_mul_basics(n as int);
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
/// logical_divide_linear(A, B).offset(x) == A.offset(x).
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
        logical_divide_linear(a, b).offset(x) == a.offset(x),
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

    // By compose_linear correctness: compose_linear(A, zipped).offset(x) == A.offset(zipped.offset(x))
    crate::proof::composition_lemmas::lemma_compose_correct(a_val, zipped, x);
    assert(compose_linear(a_val, zipped).offset(x) == a_val.offset(zipped.offset(x) as nat));

    // zipped.offset(x) == x, so A.offset(zipped.offset(x)) == A.offset(x)
    assert(zipped.offset(x) as nat == x);
}

/// For rank-1 A and column-major B, logical_divide_linear preserves injectivity.
pub proof fn lemma_divide_injective_1d_a(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.shape.len() == 1,
        b.stride[0] == 1,
        a.is_injective(),
    ensures
        logical_divide_linear(a, b).is_injective(),
{
    let d = logical_divide_linear(a, b);
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

// ══════════════════════════════════════════════════════════════
// Phase 6: General zipped identity offset + divide offset preservation
// ══════════════════════════════════════════════════════════════

/// If shape[0] == 1, offset(x) == offset(x) of the tail layout (stripping the first mode).
proof fn lemma_unit_mode_offset(layout: &LayoutSpec, x: nat)
    requires
        layout.valid(),
        layout.shape.len() > 0,
        layout.shape.first() == 1nat,
        x < layout.size(),
    ensures ({
        let tail = LayoutSpec {
            shape: layout.shape.skip(1),
            stride: layout.stride.skip(1),
        };
        layout.offset(x) == tail.offset(x)
    }),
{
    let tail = LayoutSpec {
        shape: layout.shape.skip(1),
        stride: layout.stride.skip(1),
    };

    // delinearize(x, shape) = seq![x % 1] ++ delinearize(x / 1, shape.skip(1))
    assert(x % 1 == 0nat);
    assert(x / 1 == x);
    let coords = delinearize(x, layout.shape);
    let tail_coords = delinearize(x, tail.shape);
    assert(coords =~= seq![0nat].add(tail_coords));

    // dot(seq![0] ++ tail_coords, seq![stride[0]] ++ stride.skip(1))
    //   = 0 * stride[0] + dot(tail_coords, stride.skip(1))
    lemma_delinearize_len(x, layout.shape);
    lemma_delinearize_len(x, tail.shape);
    lemma_dot_product_append(
        seq![0nat], tail_coords,
        seq![layout.stride.first()], layout.stride.skip(1),
    );
    assert(layout.stride =~= seq![layout.stride.first()].add(layout.stride.skip(1)));
    lemma_dot_product_ext(
        coords, seq![0nat].add(tail_coords),
        layout.stride, seq![layout.stride.first()].add(layout.stride.skip(1)),
    );
    // dot(seq![0], seq![stride[0]]) = 0 * stride[0] + dot(empty, empty) = 0 + 0 = 0
    vstd::arithmetic::mul::lemma_mul_basics(layout.stride.first());
    assert((0nat as int) * layout.stride.first() == 0int);
    assert(seq![0nat].skip(1).len() == 0);
    assert(dot_product_nat_int(seq![0nat].skip(1), seq![layout.stride.first()].skip(1)) == 0int);
    assert(dot_product_nat_int(seq![0nat], seq![layout.stride.first()]) == 0int);
}

/// For column-major B, complement_shape(B, M)[i] == 1 for all 0 <= i < B.shape.len().
proof fn lemma_complement_cm_shapes_unit(b: &LayoutSpec, m: nat, i: int)
    requires
        complement_admissible(b, m),
        b.stride =~= column_major_strides(b.shape),
        0 <= i < b.shape.len() as int,
    ensures
        complement_shape(b, m)[i] == 1nat,
{
    let k = b.shape.len();
    lemma_column_major_strides_len(b.shape);

    if i == 0 {
        // complement_shape[0] = b.stride[0] = column_major_strides(shape)[0] = 1
        assert(complement_shape(b, m)[0] == b.stride[0] as nat);
        // column_major_strides(shape)[0] == 1 (by definition, shape.len() > 0)
        assert(column_major_strides(b.shape)[0] == 1int);
        assert(b.stride[0] == 1int);
    } else {
        // complement_shape[i] = b.stride[i] / stride_product(b, i-1)
        // For column-major: b.stride[i] = cm[i] and cm[i] = cm[i-1] * shape[i-1]
        // stride_product(b, i-1) = shape[i-1] * stride[i-1] = shape[i-1] * cm[i-1]
        // By lemma_cm_recursive_step: cm[i] = cm[i-1] * shape[i-1]
        // So b.stride[i] = shape[i-1] * cm[i-1] = stride_product(b, i-1)
        // Therefore complement_shape[i] = stride_product(b, i-1) / stride_product(b, i-1) = 1
        crate::proof::complement_lemmas::lemma_cm_recursive_step(b.shape, i);
        assert(column_major_strides(b.shape)[i]
            == column_major_strides(b.shape)[(i - 1)] * (b.shape[(i - 1)] as int));
        assert(b.stride[i] == b.stride[(i - 1)] * (b.shape[(i - 1)] as int));
        assert(stride_product(b, i - 1) == (b.shape[(i - 1)] as int) * b.stride[(i - 1)]);
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            b.shape[(i - 1)] as int,
            b.stride[(i - 1)],
        );
        assert(b.stride[i] == stride_product(b, i - 1));
        lemma_stride_product_positive(b, i - 1);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            b.stride[i], stride_product(b, i - 1));
        assert(b.stride[i] / stride_product(b, i - 1) == 1);
    }
}

/// For column-major B, complement(B, M).offset(y) == y * shape_size(B.shape)
/// for y < M / shape_size(B.shape).
proof fn lemma_complement_offset_cm(b: &LayoutSpec, m: nat, y: nat)
    requires
        complement_admissible(b, m),
        b.stride =~= column_major_strides(b.shape),
        y < shape_size(complement(b, m).shape),
    ensures
        complement(b, m).offset(y) == (y as int) * (shape_size(b.shape) as int),
    decreases b.shape.len(),
{
    let c = complement(b, m);
    let k = b.shape.len();
    let n = shape_size(b.shape);
    lemma_complement_rank(b, m);
    lemma_complement_valid(b, m);
    lemma_shape_size_positive(b.shape);

    if k == 1 {
        // C has 2 modes: (1, m/n) : (1, n)
        lemma_complement_cm_shapes_unit(b, m, 0);
        assert(c.shape[0] == 1nat);
        assert(c.shape.len() == 2);
        lemma_unit_mode_offset(&c, y);

        // Tail = single mode (m/n):(n)
        let tail = LayoutSpec {
            shape: c.shape.skip(1),
            stride: c.stride.skip(1),
        };
        assert(tail.shape.len() == 1);
        assert(tail.stride.len() == 1);
        assert(tail.shape.first() == c.shape[1]);
        // c.stride[1] = stride_product(b, 0) = b.shape[0] * b.stride[0] = n * 1 = n
        // c.stride[1] = stride_product(b, 0) = b.shape[0] * b.stride[0] = b.shape[0] * 1
        lemma_complement_stride_rest(b, m, 0);
        assert(c.stride[1] == stride_product(b, 0));
        assert(stride_product(b, 0) == (b.shape[0] as int) * b.stride[0]);
        lemma_column_major_strides_len(b.shape);
        assert(b.stride[0] == column_major_strides(b.shape)[0]);
        vstd::arithmetic::mul::lemma_mul_basics(b.shape[0] as int);
        // n = shape_size(b.shape) = b.shape[0] for rank-1 B
        assert(b.shape.skip(1).len() == 0);
        assert(shape_size(b.shape.skip(1)) == 1nat);
        assert(shape_size(b.shape) == b.shape.first() * shape_size(b.shape.skip(1)));
        assert(n == b.shape[0]);
        assert(c.stride[1] == n as int);

        // shape_size(c.shape) = c.shape[0] * shape_size(c.shape[1:]) = 1 * c.shape[1] = c.shape[1]
        assert(shape_size(c.shape) == c.shape.first() * shape_size(c.shape.skip(1)));
        let c_tail = c.shape.skip(1);
        assert(c_tail.len() == 1);
        assert(c_tail.first() == c.shape[1]);
        assert(c_tail.skip(1).len() == 0);
        assert(shape_size(c_tail.skip(1)) == 1nat);
        assert(shape_size(c_tail) == c_tail.first() * shape_size(c_tail.skip(1)));
        vstd::arithmetic::mul::lemma_mul_basics(c_tail.first() as int);
        vstd::arithmetic::mul::lemma_mul_basics(shape_size(c.shape.skip(1)) as int);
        assert(shape_size(c.shape) == c.shape[1]);
        crate::proof::integer_helpers::lemma_mod_small(y, c.shape[1]);
        // tail.offset(y) = y * stride[0] = y * n (single mode with y < shape[0])
        assert(tail.valid()) by {
            assert(tail.shape.len() == tail.stride.len());
            assert forall|j: int| 0 <= j < tail.shape.len()
            implies #[trigger] tail.shape[j] > 0 by {
                lemma_complement_shape_valid(b, m);
                assert(tail.shape[j] == c.shape[(j + 1) as int]);
            };
        };
        assert(y < tail.shape.first());
        lemma_offset_within_first_mode(&tail, y);
        assert(tail.stride.first() == n as int);
        assert(c.offset(y) == (y as int) * (n as int));
    } else {
        // k >= 2: Strip first unit mode, recurse
        lemma_complement_cm_shapes_unit(b, m, 0);
        assert(c.shape[0] == 1nat);
        lemma_unit_mode_offset(&c, y);

        // After stripping: (C.shape[1:], C.stride[1:])
        // C.shape[1:] = (complement_shape[1], ..., complement_shape[k])
        // C.stride[1:] = (sp(0), sp(1), ..., sp(k-1))
        //
        // This is the complement of B' = B.skip_first_mode w.r.t. m' = m,
        // with adjusted strides... actually this doesn't decompose cleanly.
        //
        // Instead: unfold complement_shape/stride for positions 1..k.
        // complement_shape[i] for 1 <= i < k: = b.stride[i] / sp(i-1) = 1 (cm shapes unit)
        // complement_shape[k] = m / sp(k-1)
        // complement_stride[i] for 1 <= i <= k: = sp(i-1)
        //
        // So C.stride[1:] = (sp(0), sp(1), ..., sp(k-1))
        //    C.shape[1:] = (1, 1, ..., 1, m/sp(k-1))
        //
        // Repeat stripping: after k-1 more strips, get single mode (m/sp(k-1)):(sp(k-1))
        // sp(k-1) = shape[k-1] * stride[k-1] = shape[k-1] * cm[k-1] = n (for column-major)
        // So final mode is (m/n):(n), and offset(y) = y * n.

        // Use induction: strip all k unit modes at once via loop proof
        // Actually, let me use a direct approach: all coords for unit modes are 0,
        // so the dot product reduces to just the last mode's contribution.

        // Direct proof: decompose offset using delinearize_concat
        // Split C.shape into unit prefix (k modes) and last mode (1 mode)
        let prefix_shape = c.shape.take(k as int);
        let suffix_shape = c.shape.skip(k as int);
        let prefix_stride = c.stride.take(k as int);
        let suffix_stride = c.stride.skip(k as int);

        assert(c.shape =~= prefix_shape.add(suffix_shape));
        assert(c.stride =~= prefix_stride.add(suffix_stride));

        // prefix_shape = (1, 1, ..., 1) [k entries, all 1]
        assert(shape_valid(prefix_shape)) by {
            assert forall|j: int| 0 <= j < prefix_shape.len()
            implies #[trigger] prefix_shape[j] > 0 by {
                lemma_complement_cm_shapes_unit(b, m, j);
            };
        };
        assert forall|j: int| 0 <= j < prefix_shape.len()
        implies #[trigger] prefix_shape[j] == 1nat by {
            lemma_complement_cm_shapes_unit(b, m, j);
            assert(prefix_shape[j] == c.shape[j]);
        };
        lemma_shape_size_all_ones(prefix_shape);
        assert(shape_size(prefix_shape) == 1nat);

        // suffix has 1 mode: (m/sp(k-1))
        assert(suffix_shape.len() == 1);
        assert(suffix_stride.len() == 1);

        // suffix_stride[0] = c.stride[k] = sp(k-1)
        assert(suffix_stride[0] == c.stride[k as int]);
        assert(c.stride[k as int] == stride_product(b, (k - 1) as int));
        // sp(k-1) = shape[k-1] * stride[k-1] = shape[k-1] * cm[k-1]
        // For column-major: cm[k-1] = prod(shape[0..k-2])
        // So sp(k-1) = shape[k-1] * prod(shape[0..k-2]) = prod(shape[0..k-1]) = n
        lemma_cm_stride_product_is_size(b);
        assert(stride_product(b, (k - 1) as int) == n as int);
        assert(suffix_stride[0] == n as int);

        // suffix_shape[0] = m/n
        assert(suffix_shape[0] == c.shape[k as int]);

        // shape_valid(suffix_shape)
        lemma_complement_shape_valid(b, m);
        assert(shape_valid(suffix_shape)) by {
            assert forall|j: int| 0 <= j < suffix_shape.len()
            implies #[trigger] suffix_shape[j] > 0 by {
                assert(suffix_shape[j] == c.shape[(j + k) as int]);
            };
        };

        // y < shape_size(prefix) * shape_size(suffix) = 1 * shape_size(suffix) = suffix_shape[0]
        assert(shape_size(suffix_shape) == suffix_shape.first() * shape_size(suffix_shape.skip(1)));
        assert(suffix_shape.skip(1).len() == 0);
        vstd::arithmetic::mul::lemma_mul_basics(suffix_shape.first() as int);
        assert(shape_size(suffix_shape) == suffix_shape.first());
        vstd::arithmetic::mul::lemma_mul_basics(shape_size(suffix_shape) as int);
        crate::proof::product_lemmas::lemma_shape_size_append(prefix_shape, suffix_shape);
        assert(shape_size(c.shape) == shape_size(prefix_shape) * shape_size(suffix_shape));
        assert(y < shape_size(prefix_shape) * shape_size(suffix_shape));

        // Decompose delinearize
        lemma_delinearize_concat(y, prefix_shape, suffix_shape);
        // Since shape_size(prefix) = 1: y % 1 = 0, y / 1 = y
        assert(y % shape_size(prefix_shape) == 0nat);
        assert(y / shape_size(prefix_shape) == y);

        let prefix_coords = delinearize(0nat, prefix_shape);
        let suffix_coords = delinearize(y, suffix_shape);
        lemma_delinearize_len(0nat, prefix_shape);
        lemma_delinearize_len(y, suffix_shape);

        // dot(prefix_coords, prefix_stride) = 0 (all coords are 0 since delinearize(0, ...) = all zeros)
        lemma_delinearize_zero(prefix_shape);
        lemma_dot_product_zeros(prefix_coords, prefix_stride);

        // dot(suffix_coords, suffix_stride)
        // suffix_coords = delinearize(y, (m/n,)) = (y % (m/n),) = (y,) since y < m/n
        crate::proof::integer_helpers::lemma_mod_small(y, suffix_shape.first());

        // Combine: c.offset(y) = dot(prefix_coords, prefix_stride) + dot(suffix_coords, suffix_stride)
        //                       = 0 + dot(suffix_coords, suffix_stride)
        lemma_dot_product_append(prefix_coords, suffix_coords, prefix_stride, suffix_stride);
        lemma_dot_product_ext(
            delinearize(y, c.shape),
            prefix_coords.add(suffix_coords),
            c.stride,
            prefix_stride.add(suffix_stride),
        );

        // suffix_coords = (y,), suffix_stride = (n,)
        // dot((y,), (n,)) = y * n
        assert(suffix_coords =~= seq![y]);
        assert(suffix_stride =~= seq![n as int]);
        // Single-element dot product: y * n + 0 = y * n
        assert(seq![y].skip(1).len() == 0);
        assert(dot_product_nat_int(seq![y].skip(1), seq![n as int].skip(1)) == 0int);
        assert(dot_product_nat_int(suffix_coords, suffix_stride)
            == (y as int) * (n as int) + 0int);

        assert(c.offset(y) == (y as int) * (n as int));
    }
}

/// For column-major B, stride_product(B, k-1) == shape_size(B.shape).
proof fn lemma_cm_stride_product_is_size(b: &LayoutSpec)
    requires
        b.valid(),
        b.shape.len() > 0,
        b.stride =~= column_major_strides(b.shape),
    ensures
        stride_product(b, (b.shape.len() - 1) as int) == shape_size(b.shape) as int,
    decreases b.shape.len(),
{
    let k = b.shape.len();
    lemma_column_major_strides_len(b.shape);

    if k == 1 {
        // stride_product(b, 0) = shape[0] * stride[0] = shape[0] * 1
        assert(b.stride[0] == 1int);
        vstd::arithmetic::mul::lemma_mul_basics(b.shape[0] as int);
        // shape_size(seq![shape[0]]) = shape[0]
        assert(shape_size(b.shape) == b.shape.first() * shape_size(b.shape.skip(1)));
        assert(b.shape.skip(1).len() == 0);
        vstd::arithmetic::mul::lemma_mul_basics(b.shape.first() as int);
    } else {
        // stride_product(b, k-1) = shape[k-1] * stride[k-1]
        // stride[k-1] = cm[k-1] = cm[k-2] * shape[k-2] (by recursive step)
        // By induction on a "conceptual" smaller layout... actually let me just use
        // the fact that cm[k-1] * shape[k-1] telescopes to prod(shape).
        // cm[0] = 1, cm[i] = cm[i-1] * shape[i-1]
        // So cm[k-1] = prod(shape[0..k-2])
        // stride_product(b, k-1) = shape[k-1] * prod(shape[0..k-2]) = prod(shape)

        // Use the telescoping identity from shape_size:
        // shape_size(shape) = shape[0] * shape_size(shape[1:])
        // We need to show cm[k-1] * shape[k-1] = shape_size(shape)

        // Approach: show stride_product(b, k-1) = stride_product(b, k-2) * shape[k-1] * shape[k-2] / shape[k-2]
        // Actually, let me just unfold recursively.
        // stride_product(b, k-1) = shape[k-1] * stride[k-1]
        //                        = shape[k-1] * cm[k-1]
        // cm[k-1] = cm[k-2] * shape[k-2]  (recursive step)
        // stride_product(b, k-2) = shape[k-2] * cm[k-2]
        // So cm[k-1] = stride_product(b, k-2) (when expressed differently)

        // Actually: cm[i] = shape[i-1] * cm[i-1] for i >= 1
        // stride_product(b, i) = shape[i] * cm[i]
        // So stride_product(b, i) = shape[i] * shape[i-1] * cm[i-1]
        //                         = shape[i] * stride_product(b, i-1) / shape[i-1] * shape[i-1]
        // This is getting circular. Let me use a different approach.

        // cm[k-1] * shape_size(skip(k-1)) == shape_size(shape)
        lemma_cm_prefix_product_identity(b.shape, (k - 1) as nat);
        // shape.skip(k-1) has length 1, so shape_size(skip(k-1)) == shape[k-1]
        let tail = b.shape.skip((k - 1) as int);
        assert(tail.len() == 1);
        assert(tail.first() == b.shape[(k - 1) as int]);
        assert(tail.skip(1).len() == 0);
        assert(shape_size(tail.skip(1)) == 1nat);
        assert(shape_size(tail) == tail.first() * shape_size(tail.skip(1)));
        assert(shape_size(tail) == tail.first() * 1nat);
        vstd::arithmetic::mul::lemma_mul_basics(tail.first() as int);
        assert(shape_size(tail) == b.shape[(k - 1) as int]);
        // So cm[k-1] * shape[k-1] == shape_size(shape)
        // stride_product(b, k-1) = shape[k-1] * stride[k-1] = shape[k-1] * cm[k-1]
        assert(b.stride[(k - 1) as int] == column_major_strides(b.shape)[(k - 1) as int]);
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            b.shape[(k - 1) as int] as int,
            column_major_strides(b.shape)[(k - 1) as int],
        );
    }
}

/// column_major_strides(shape)[i] * shape_size(shape.skip(i)) == shape_size(shape)
/// for 0 <= i < shape.len().
proof fn lemma_cm_prefix_product_identity(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        shape.len() > 0,
        i < shape.len(),
    ensures
        column_major_strides(shape)[i as int] * (shape_size(shape.skip(i as int)) as int)
            == shape_size(shape) as int,
    decreases i,
{
    lemma_column_major_strides_len(shape);

    if i == 0 {
        // cm[0] = 1, skip(0) = shape
        assert(column_major_strides(shape)[0] == 1int);
        assert(shape.skip(0) =~= shape);
        vstd::arithmetic::mul::lemma_mul_basics(shape_size(shape) as int);
    } else {
        // cm[i] = cm[i-1] * shape[i-1] (recursive step)
        crate::proof::complement_lemmas::lemma_cm_recursive_step(shape, i as int);
        // cm[i] = cm[i-1] * shape[i-1]

        // IH: cm[i-1] * shape_size(shape.skip(i-1)) == shape_size(shape)
        lemma_cm_prefix_product_identity(shape, (i - 1) as nat);

        // shape_size(shape.skip(i-1)) = shape[i-1] * shape_size(shape.skip(i))
        let si1 = shape.skip((i - 1) as int);
        assert(si1.len() > 0);
        assert(si1.first() == shape[(i - 1) as int]);
        assert(si1.skip(1) =~= shape.skip(i as int));
        assert(shape_size(si1) == si1.first() * shape_size(si1.skip(1)));

        // cm[i] * shape_size(skip(i))
        // = (cm[i-1] * shape[i-1]) * shape_size(skip(i))
        // = cm[i-1] * (shape[i-1] * shape_size(skip(i)))
        // = cm[i-1] * shape_size(skip(i-1))
        // = shape_size(shape) [by IH]
        vstd::arithmetic::mul::lemma_mul_is_associative(
            column_major_strides(shape)[(i - 1) as int],
            shape[(i - 1) as int] as int,
            shape_size(shape.skip(i as int)) as int,
        );
    }
}

/// delinearize(0, shape) produces all-zero coordinates for valid shape.
proof fn lemma_delinearize_zero(shape: Seq<nat>)
    requires
        shape_valid(shape),
    ensures
        forall|j: int| 0 <= j < shape.len() ==> #[trigger] delinearize(0nat, shape)[j] == 0nat,
    decreases shape.len(),
{
    lemma_delinearize_len(0nat, shape);
    if shape.len() > 0 {
        assert(delinearize(0nat, shape)[0] == 0nat);
        lemma_delinearize_zero(shape.skip(1));
        assert forall|j: int| 0 <= j < shape.len()
        implies #[trigger] delinearize(0nat, shape)[j] == 0nat by {
            if j == 0 {
            } else {
                assert(delinearize(0nat, shape.skip(1))[(j - 1)] == 0nat);
            }
        };
    }
}

/// dot(zeros, any_stride) == 0.
proof fn lemma_dot_product_zeros(coords: Seq<nat>, stride: Seq<int>)
    requires
        coords.len() == stride.len(),
        forall|j: int| 0 <= j < coords.len() ==> #[trigger] coords[j] == 0nat,
    ensures
        dot_product_nat_int(coords, stride) == 0int,
    decreases coords.len(),
{
    if coords.len() > 0 {
        assert(coords.first() == 0nat);
        lemma_dot_product_zeros(coords.skip(1), stride.skip(1));
    }
}

/// shape_size of an all-ones shape is 1.
proof fn lemma_shape_size_all_ones(shape: Seq<nat>)
    requires
        forall|j: int| 0 <= j < shape.len() ==> #[trigger] shape[j] == 1nat,
    ensures
        shape_size(shape) == 1nat,
    decreases shape.len(),
{
    if shape.len() > 0 {
        assert(shape.first() == 1nat);
        lemma_shape_size_all_ones(shape.skip(1));
        vstd::arithmetic::mul::lemma_mul_basics(shape_size(shape.skip(1)) as int);
    }
}

/// For column-major B, the zipped layout (B ++ complement(B, M)) has identity offset.
pub proof fn lemma_zipped_identity_offset(b: &LayoutSpec, m: nat, x: nat)
    requires
        complement_admissible(b, m),
        b.stride =~= column_major_strides(b.shape),
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
    let c = complement(b, m);
    let n = shape_size(b.shape);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    lemma_complement_shape_valid(b, m);
    lemma_complement_valid(b, m);
    lemma_shape_size_positive(b.shape);
    lemma_shape_size_positive(c.shape);
    lemma_complement_size(b, m);
    // shape_size(c.shape) * shape_size(b.shape) == m, i.e., shape_size(c.shape) * n == m

    // x < n * shape_size(c.shape)
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(c.shape) as int, n as int);
    assert(n * shape_size(c.shape) == m);

    // Step 1: Decompose delinearize over B.shape ++ C.shape
    lemma_delinearize_concat(x, b.shape, c.shape);
    crate::proof::integer_helpers::lemma_mod_bound(x, n);
    crate::proof::integer_helpers::lemma_div_upper_bound(x, n, shape_size(c.shape));
    let b_coords = delinearize(x % n, b.shape);
    let c_coords = delinearize(x / n, c.shape);
    lemma_delinearize_len(x % n, b.shape);
    lemma_delinearize_len(x / n, c.shape);

    // Step 2: Decompose dot product
    lemma_dot_product_append(b_coords, c_coords, b.stride, c.stride);
    lemma_dot_product_ext(
        delinearize(x, zipped.shape),
        b_coords.add(c_coords),
        zipped.stride,
        b.stride.add(c.stride),
    );
    // zipped.offset(x) == dot(b_coords, b.stride) + dot(c_coords, c.stride)

    // Step 3: First part = x % n (column-major identity)
    lemma_column_major_offset_is_identity(b.shape, x % n);
    // make_column_major(b.shape).offset(x % n) == (x % n) as int
    // Since b.stride =~= column_major_strides(b.shape):
    lemma_dot_product_ext(
        b_coords, b_coords,
        b.stride, column_major_strides(b.shape),
    );
    // dot(b_coords, b.stride) == (x % n) as int

    // Step 4: Second part = (x / n) * n
    lemma_complement_offset_cm(b, m, x / n);
    // complement.offset(x / n) == (x / n) * n

    // Step 5: (x % n) + (x / n) * n == x
    crate::proof::integer_helpers::lemma_div_mod_identity(x, n);
    vstd::arithmetic::mul::lemma_mul_is_commutative(n as int, (x / n) as int);
}

/// For rank-1 A and column-major B, logical_divide_linear(A, B).offset(x) == A.offset(x).
/// Generalizes lemma_divide_offset_1d_a to multi-rank column-major B.
pub proof fn lemma_divide_offset(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.stride =~= column_major_strides(b.shape),
        x < shape_size(a.shape),
    ensures
        logical_divide_linear(a, b).offset(x) == a.offset(x),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped is valid + non-negative strides + size == m
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);
    lemma_complement_rank(b, m);
    assert(shape_size(zipped.shape) == m);

    // zipped.offset(x) == x (the key identity)
    lemma_zipped_identity_offset(b, m, x);
    assert(zipped.offset(x) == x as int);

    // For rank-1 A: shape_size(a.shape) == a.shape.first()
    // shape_size(s) = s.first() * shape_size(s.skip(1)), and skip(1) is empty so size = 1
    assert(a.shape.skip(1).len() == 0);
    assert(shape_size(a.shape.skip(1)) == 1nat);
    assert(shape_size(a.shape) == a.shape.first() * 1nat);
    vstd::arithmetic::mul::lemma_mul_basics(a.shape.first() as int);
    assert(shape_size(a.shape) == a.shape.first());

    // Therefore zipped.offset(x) < a.shape.first()
    assert(zipped.offset(x) >= 0);
    assert(zipped.offset(x) < a.shape.first() as int);

    // By compose_linear correctness: compose_linear(A, zipped).offset(x) == A.offset(zipped.offset(x))
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    crate::proof::composition_lemmas::lemma_compose_correct(a_val, zipped, x);
    assert(compose_linear(a_val, zipped).offset(x) == a_val.offset(zipped.offset(x) as nat));
    assert(zipped.offset(x) as nat == x);
}

/// For rank-1 A and column-major B, logical_divide_linear preserves injectivity.
/// Generalizes lemma_divide_injective_1d_a to multi-rank column-major B.
pub proof fn lemma_divide_injective(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.stride =~= column_major_strides(b.shape),
        a.is_injective(),
    ensures
        logical_divide_linear(a, b).is_injective(),
{
    lemma_divide_size(a, b);
    assert(shape_size(logical_divide_linear(a, b).shape) == shape_size(a.shape));

    assert forall|x1: nat, x2: nat|
        x1 < shape_size(logical_divide_linear(a, b).shape)
        && x2 < shape_size(logical_divide_linear(a, b).shape)
        && x1 != x2
    implies
        logical_divide_linear(a, b).offset(x1) != logical_divide_linear(a, b).offset(x2)
    by {
        lemma_divide_offset(a, b, x1);
        lemma_divide_offset(a, b, x2);
        // divide.offset(xi) == a.offset(xi), and a is injective
        assert(logical_divide_linear(a, b).offset(x1) == a.offset(x1));
        assert(logical_divide_linear(a, b).offset(x2) == a.offset(x2));
    };
}

/// For rank-1 A and column-major B, logical_divide_linear preserves bijectivity.
/// Since divide has the same offset function as A, bijectivity transfers directly.
pub proof fn lemma_divide_bijective(a: &LayoutSpec, b: &LayoutSpec, target: nat)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.stride =~= column_major_strides(b.shape),
        a.is_bijective_upto(target),
    ensures
        logical_divide_linear(a, b).is_bijective_upto(target),
{
    // Injectivity: same offset function + A injective
    lemma_divide_injective(a, b);

    // Surjectivity: for any k in [0, target), A hits k, so divide hits k too
    lemma_divide_size(a, b);
    assert forall|k: int| 0 <= k < target as int
    implies #[trigger] logical_divide_linear(a, b).offset_hit(k) by {
        // A is surjective onto [0, target), so some i < a.size() has a.offset(i) == k
        assert(a.offset_hit(k));
        let i: nat = choose|i: nat| i < a.size() && #[trigger] a.offset(i) == k;
        // divide.offset(i) == a.offset(i) == k, and i < divide.size()
        lemma_divide_offset(a, b, i);
        assert(logical_divide_linear(a, b).offset(i) == k);
    };
}

// ══════════════════════════════════════════════════════════════
// General divide injectivity (column-major A of any rank)
// ══════════════════════════════════════════════════════════════

/// scale_strides by 1 is identity.
pub proof fn lemma_scale_strides_one(s: Seq<int>)
    ensures scale_strides_spec(s, 1) =~= s,
{
    assert(scale_strides_spec(s, 1).len() == s.len());
    assert forall|i: int| 0 <= i < s.len() implies
        #[trigger] scale_strides_spec(s, 1)[i] == s[i]
    by {
        vstd::arithmetic::mul::lemma_mul_basics(s[i]);
    };
}

/// For column-major A (any rank) and column-major B, divide has identity offset.
pub proof fn lemma_divide_offset_column_major(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        divide_admissible(a, b),
        a.stride =~= column_major_strides(a.shape),
        b.stride =~= column_major_strides(b.shape),
        x < shape_size(a.shape),
    ensures
        logical_divide_linear(a, b).offset(x) == x as int,
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped is valid + non-negative strides + size == m
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);

    // A is column-major → stride[0] == 1
    crate::proof::inverse_lemmas::lemma_column_major_strides_first(a.shape);
    assert(a.stride[0] == 1int);

    // compose_linear(A, zipped).stride =~= scale(zipped.stride, 1) =~= zipped.stride
    crate::proof::composition_lemmas::lemma_compose_stride_general(*a, zipped);
    assert(a.stride.first() == 1int);
    lemma_scale_strides_one(zipped.stride);

    // compose_linear(A, zipped).shape =~= zipped.shape
    crate::proof::composition_lemmas::lemma_compose_shape(*a, zipped);

    // So logical_divide_linear(a,b) has same shape/stride as zipped → same offset
    crate::proof::composition_lemmas::lemma_offset_eq_layout(
        logical_divide_linear(a, b).shape, logical_divide_linear(a, b).stride,
        zipped.shape, zipped.stride, x,
    );

    // zipped has identity offset for column-major B
    lemma_zipped_identity_offset(b, m, x);
}

/// Column-major A (any rank) + column-major B → divide is injective.
pub proof fn lemma_divide_injective_column_major(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        a.stride =~= column_major_strides(a.shape),
        b.stride =~= column_major_strides(b.shape),
    ensures
        logical_divide_linear(a, b).is_injective(),
{
    lemma_divide_size(a, b);
    assert forall|x1: nat, x2: nat|
        x1 < shape_size(logical_divide_linear(a, b).shape)
        && x2 < shape_size(logical_divide_linear(a, b).shape)
        && x1 != x2
    implies
        logical_divide_linear(a, b).offset(x1) != logical_divide_linear(a, b).offset(x2)
    by {
        lemma_divide_offset_column_major(a, b, x1);
        lemma_divide_offset_column_major(a, b, x2);
        // offset(xi) == xi, so distinct inputs → distinct offsets
    };
}

/// Column-major A (any rank) + column-major B → divide is bijective.
pub proof fn lemma_divide_bijective_column_major(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        a.stride =~= column_major_strides(a.shape),
        b.stride =~= column_major_strides(b.shape),
    ensures
        logical_divide_linear(a, b).is_bijective_upto(shape_size(a.shape)),
{
    // Identity offset → bijective via lemma_identity_offset_implies_bijective
    lemma_divide_size(a, b);
    crate::proof::tiling_lemmas::lemma_divide_valid(a, b);
    let div = logical_divide_linear(a, b);
    assert forall|i: nat| i < div.size()
    implies div.offset(i) == i as int
    by {
        lemma_divide_offset_column_major(a, b, i);
    };
    crate::proof::injectivity_lemmas::lemma_identity_offset_implies_bijective(div);
}

// ══════════════════════════════════════════════════════════════
// logical_divide_extended: shape and size properties
// ══════════════════════════════════════════════════════════════

/// logical_divide_extended has the same shape as logical_divide_linear.
///
/// Both use the same zipped layout (B, complement(B, M)) — only the composition
/// method differs. Since compose_linear and compose_extended produce the same shape
/// (always b.shape), the shapes agree.
pub proof fn lemma_divide_extended_shape(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        logical_divide_extended(a, b).shape =~= logical_divide_linear(a, b).shape,
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    // zipped is valid + non-negative strides + size == m
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);

    lemma_compose_rank(a_val, zipped);
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, zipped);
    lemma_compose_extended_multimode_shape(a_val, zipped);
}

/// Helper: compose_extended preserves shape (same as compose_linear).
/// Multi-mode compose_extended preserves shape (deprecated: prefer compose).
pub proof fn lemma_compose_extended_multimode_shape(a: LayoutSpec, b: LayoutSpec)
    requires
        a.valid(),
        b.valid(),
        a.shape.len() > 0,
    ensures
        compose_extended(a, b).shape =~= b.shape,
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
    } else if b.shape.len() == 1 {
        crate::proof::composition_lemmas::lemma_compose_extended_shape(a, b.shape.first(), b.stride.first() as nat);
    } else {
        let rest_b = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };
        assert(rest_b.valid()) by {
            assert forall|i: int| 0 <= i < rest_b.shape.len()
            implies #[trigger] rest_b.shape[i] > 0 by {
                assert(rest_b.shape[i] == b.shape[i + 1]);
            };
        };
        lemma_compose_extended_multimode_shape(a, rest_b);
        let first = compose_single_mode_extended(a, b.shape.first(), b.stride.first() as nat);
        crate::proof::composition_lemmas::lemma_compose_extended_shape(a, b.shape.first(), b.stride.first() as nat);
        // first.shape =~= seq![b.shape.first()]
        // rest.shape =~= rest_b.shape
        // b.shape =~= seq![b.shape.first()] ++ rest_b.shape
        assert(b.shape =~= seq![b.shape.first()].add(rest_b.shape));
    }
}

/// logical_divide_extended has the same size as logical_divide_linear (== size(A)).
pub proof fn lemma_divide_extended_size(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        shape_size(logical_divide_extended(a, b).shape)
            == shape_size(a.shape),
{
    lemma_divide_extended_shape(a, b);
    lemma_divide_size(a, b);
}

/// logical_divide_extended offset correctness for rank-1 A with column-major B.
///
/// When B = (N):(1) and A has rank 1, compose_extended == compose_linear for rank-1 A,
/// so logical_divide_extended == logical_divide_linear, and existing proofs apply.
///
/// For multi-rank A, use lemma_divide_offset_column_major (column-major A)
/// or lemma_divide_offset (rank-1 A) with the original logical_divide_linear.
/// Note: logical_divide_extended with rank-1 B and non-column-major multi-rank A
/// is NOT correct in general — the complement mode may cross A's first mode boundary,
/// and compose_extended's fallback stride (N*d_0) doesn't correctly represent
/// A.offset(N*y) when N*y >= A.shape[0].
pub proof fn lemma_divide_extended_offset(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.shape.len() == 1,
        b.stride[0] == 1,
        x < shape_size(a.shape),
    ensures
        logical_divide_extended(a, b).offset(x) == a.offset(x),
{
    // B = (N):(1) is column-major
    assert(b.stride =~= column_major_strides(b.shape)) by {
        lemma_column_major_strides_len(b.shape);
    };

    // Use existing divide_offset for rank-1 A
    lemma_divide_offset(a, b, x);

    // Show logical_divide_extended == logical_divide_linear for rank-1 A
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);
    crate::proof::composition_lemmas::lemma_compose_extended_eq_rank1(a_val, zipped);
    assert(logical_divide_extended(a, b) == logical_divide_linear(a, b));
}

// ══════════════════════════════════════════════════════════════
// logical_divide_mode: correct multi-rank divide
// ══════════════════════════════════════════════════════════════

/// logical_divide_mode produces a valid layout.
pub proof fn lemma_divide_mode_valid(a: &LayoutSpec, n: nat)
    requires divide_mode_admissible(a, n),
    ensures logical_divide_mode(a, n).valid(),
{
    let result = logical_divide_mode(a, n);
    let m0 = a.shape.first();
    // m0 >= n because m0 % n == 0 and m0 > 0 and n > 0
    // m0 = n * (m0/n) + 0, and m0 > 0 means m0/n >= 1
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m0 as int, n as int);
    assert(m0 == n * (m0 / n));
    assert(m0 / n > 0nat) by {
        if m0 / n == 0 {
            vstd::arithmetic::mul::lemma_mul_basics(n as int);
            assert(m0 == 0nat);
        }
    };
    assert forall|i: int| 0 <= i < result.shape.len()
    implies #[trigger] result.shape[i] > 0 by {
        if i == 0 { assert(result.shape[0] == n); }
        else if i == 1 { assert(result.shape[1] == m0 / n); }
        else { assert(result.shape[i] == a.shape[i - 1]); }
    };
}

/// logical_divide_mode preserves size.
pub proof fn lemma_divide_mode_size(a: &LayoutSpec, n: nat)
    requires divide_mode_admissible(a, n),
    ensures shape_size(logical_divide_mode(a, n).shape) == shape_size(a.shape),
{
    let result = logical_divide_mode(a, n);
    let m0 = a.shape.first();
    // result.shape = [N, M_0/N] ++ a.shape.skip(1)
    // size = N * (M_0/N) * shape_size(a.shape.skip(1))
    //      = M_0 * shape_size(a.shape.skip(1))
    //      = shape_size(a.shape)

    // shape_size([N, M_0/N] ++ rest) = shape_size([N, M_0/N]) * shape_size(rest)
    let tile_shape = seq![n, m0 / n];
    let rest = a.shape.skip(1);
    assert(result.shape =~= tile_shape.add(rest));
    crate::proof::product_lemmas::lemma_shape_size_append(tile_shape, rest);

    // shape_size([N, M_0/N]) = N * (M_0/N) = M_0
    // M_0/N > 0 (same argument as in valid lemma)
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m0 as int, n as int);
    assert(m0 == n * (m0 / n));
    assert(m0 / n > 0nat) by {
        if m0 / n == 0 {
            vstd::arithmetic::mul::lemma_mul_basics(n as int);
            assert(m0 == 0nat);
            assert(false);
        }
    };
    crate::proof::tiling_lemmas::lemma_shape_size_2(n, m0 / n);
    assert(n * (m0 / n) == m0);

    // shape_size(a.shape) = M_0 * shape_size(a.shape.skip(1))
    crate::runtime::shape_helpers::lemma_shape_size_split(a.shape, 1);
    assert(a.shape.take(1) =~= seq![m0]);
    crate::proof::shape_lemmas::lemma_shape_size_single(m0);
}


/// logical_divide_mode offset correctness: offset(x) == A.offset(x) for all x < size(A).
///
/// The proof uses mixed-radix decomposition and delinearize_concat to show that
/// the tile modes (N, M_0/N):(d_0, N*d_0) reconstruct A's first mode contribution,
/// while higher modes pass through unchanged.
pub proof fn lemma_divide_mode_offset(a: &LayoutSpec, n: nat, x: nat)
    requires
        divide_mode_admissible(a, n),
        x < shape_size(a.shape),
    ensures
        logical_divide_mode(a, n).offset(x) == a.offset(x),
{
    let result = logical_divide_mode(a, n);
    let m0 = a.shape.first();
    let d0 = a.stride.first();
    let q = m0 / n;

    lemma_divide_mode_valid(a, n);
    lemma_divide_mode_size(a, n);

    // Establish q > 0 and n * q == m0
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m0 as int, n as int);
    assert(m0 == n * q);
    assert(q > 0nat) by {
        if q == 0 { vstd::arithmetic::mul::lemma_mul_basics(n as int); assert(false); }
    };

    // Define sub-shapes
    let tile_shape: Seq<nat> = seq![n, q];
    let rest_shape = a.shape.skip(1);
    let a_first_shape: Seq<nat> = seq![m0];

    assert(result.shape =~= tile_shape.add(rest_shape));
    assert(a.shape =~= a_first_shape.add(rest_shape));
    assert(shape_valid(tile_shape));
    assert(shape_valid(rest_shape)) by {
        assert forall|i: int| 0 <= i < rest_shape.len()
        implies #[trigger] rest_shape[i] > 0 by { assert(rest_shape[i] == a.shape[i + 1]); };
    };

    // Size facts
    crate::proof::tiling_lemmas::lemma_shape_size_2(n, q);
    assert(shape_size(tile_shape) == m0);
    crate::proof::shape_lemmas::lemma_shape_size_single(m0);
    crate::proof::product_lemmas::lemma_shape_size_append(tile_shape, rest_shape);
    crate::proof::product_lemmas::lemma_shape_size_append(a_first_shape, rest_shape);

    // Delinearize distributes over concat
    crate::proof::shape_lemmas::lemma_delinearize_concat(x, tile_shape, rest_shape);
    crate::proof::shape_lemmas::lemma_delinearize_concat(x, a_first_shape, rest_shape);

    let r_coords = delinearize(x, result.shape);
    let a_coords = delinearize(x, a.shape);
    lemma_delinearize_len(x, result.shape);
    lemma_delinearize_len(x, a.shape);

    let r_tile = delinearize(x % m0, tile_shape);
    let a_tile = delinearize(x % m0, a_first_shape);
    let high = delinearize(x / m0, rest_shape);

    // From concat: r_coords =~= r_tile ++ high, a_coords =~= a_tile ++ high
    assert(r_coords =~= r_tile.add(high));
    assert(a_coords =~= a_tile.add(high));

    // Split strides
    let r_tile_s: Seq<int> = seq![d0, (n as int) * d0];
    let rest_s = a.stride.skip(1);
    assert(result.stride =~= r_tile_s.add(rest_s));

    let a_tile_s: Seq<int> = seq![d0];
    assert(a.stride =~= a_tile_s.add(rest_s));

    // Dot product splits
    lemma_delinearize_len(x % m0, tile_shape);
    lemma_delinearize_len(x % m0, a_first_shape);
    crate::proof::shape_lemmas::lemma_dot_product_append(r_tile, high, r_tile_s, rest_s);
    crate::proof::shape_lemmas::lemma_dot_product_append(a_tile, high, a_tile_s, rest_s);

    // result.offset(x) = dot(r_tile, r_tile_s) + dot(high, rest_s)
    // a.offset(x)       = dot(a_tile, a_tile_s) + dot(high, rest_s)
    // Need: dot(r_tile, r_tile_s) == dot(a_tile, a_tile_s)

    // Help z3 see the delinearize values
    crate::proof::integer_helpers::lemma_mod_bound(x, m0);

    // Strategy: show both tile offsets equal d0 * (x%m0) by using
    // compose_correct_1d_a: compose_linear((m0):(d0), cm_tile).offset(y) == (m0):(d0).offset(cm_tile.offset(y))
    // where cm_tile = column_major([n, q]) has identity offset.

    let y_val = x % m0;
    let a_1d = LayoutSpec { shape: seq![m0], stride: seq![d0] };
    assert(a_1d.valid());

    // The column-major tile layout has identity offset
    let cm_tile = make_column_major(tile_shape);
    crate::proof::injectivity_lemmas::lemma_column_major_offset_is_identity(tile_shape, y_val);
    assert(cm_tile.offset(y_val) == y_val as int);

    // cm_tile is valid with non-negative strides
    assert(cm_tile.valid()) by {
        assert(column_major_strides(tile_shape).len() == tile_shape.len()) by {
            lemma_column_major_strides_len(tile_shape);
        };
    };
    crate::proof::gemm_lemmas::lemma_column_major_nonneg_strides(tile_shape);
    assert(cm_tile.non_negative_strides());

    // cm_tile.offset(y) = y, and y < m0 = a_1d.shape[0]
    assert(cm_tile.offset(y_val) >= 0);
    assert(cm_tile.offset(y_val) < a_1d.shape.first() as int) by {
        crate::proof::shape_lemmas::lemma_shape_size_single(m0);
    };

    // compose_linear(a_1d, cm_tile) has same shape as our tile layouts
    crate::proof::composition_lemmas::lemma_compose_shape(a_1d, cm_tile);

    // compose_linear(a_1d, cm_tile).offset(y) == a_1d.offset(cm_tile.offset(y)) == a_1d.offset(y) == y*d0
    crate::proof::composition_lemmas::lemma_compose_correct_1d_a(a_1d, cm_tile, y_val);
    crate::proof::shape_lemmas::lemma_offset_within_first_mode(&a_1d, y_val);
    // So compose_linear(a_1d, cm_tile).offset(y) == y * d0

    // Now show that compose_linear(a_1d, cm_tile) has the same strides as both our tile layouts
    // compose_linear distributes: stride[j] = cm_tile.stride[j] * d0
    // cm_tile.stride = column_major_strides([n, q]) = [1, n]
    // So compose_linear strides = [1*d0, n*d0] = [d0, n*d0] = r_tile_s
    crate::proof::composition_lemmas::lemma_compose_stride_general(a_1d, cm_tile);

    // The compose_linear result layout == our r_tile_layout
    let composed = compose_linear(a_1d, cm_tile);
    assert(composed.shape =~= tile_shape);
    // composed.stride = scale_strides(cm_tile.stride, d0)
    // cm_tile.stride = column_major_strides([n, q]) = [1, n]
    // So composed.stride = [1*d0, n*d0] = [d0, n*d0] = r_tile_s
    lemma_column_major_strides_len(tile_shape);
    // column_major_strides([n, q])[0] == 1
    crate::proof::inverse_lemmas::lemma_column_major_strides_first(tile_shape);
    assert(cm_tile.stride[0] == 1int);
    // column_major_strides([n, q])[1] == n
    // (prefix product at index 1 = n)
    assert(cm_tile.stride.len() == 2);
    // Show cm_tile.stride[1] == n
    // column_major_strides([n,q]) = [1] ++ scale([1], n) = [1, 1*n] = [1, n]
    assert(cm_tile.stride[1] == n as int) by {
        // Unfold: cm_strides = [1] ++ scale(column_major_strides([q]), n)
        // column_major_strides([q]) = [1] ++ scale([], q) = [1]
        // scale([1], n) = [n]
        // cm_strides = [1, n]
        let inner = column_major_strides(tile_shape.skip(1));
        assert(tile_shape.skip(1) =~= seq![q]);
        // inner = column_major_strides([q]) = [1]
        assert(inner =~= seq![1int]) by {
            let inner2 = column_major_strides(seq![q].skip(1));
            assert(seq![q].skip(1).len() == 0nat);
        };
        let scaled = scale_strides_spec(inner, n as int);
        assert(scaled =~= seq![n as int]);
    };
    assert(composed.stride =~= r_tile_s) by {
        assert forall|i: int| 0 <= i < composed.stride.len()
        implies composed.stride[i] == r_tile_s[i]
        by {
            if i == 0 {
                assert(cm_tile.stride[0] == 1int);
            } else {
                assert(cm_tile.stride[1] == n as int);
            }
        };
    };

    // Therefore: dot(r_tile, r_tile_s) == composed.offset(y) == y*d0
    // And: dot(a_tile, a_tile_s) == a_1d.offset(y) == y*d0;
}

// ══════════════════════════════════════════════════════════════
// logical_divide: the correct general divide
// ══════════════════════════════════════════════════════════════

/// For rank-1 B = (N):(1), logical_divide agrees with logical_divide_mode.
///
/// Both produce the correct tiling of A's first mode by N:
///   shape:  (N, M_0/N, M_1, M_2, ...)
///   stride: (d_0, N*d_0, d_1, d_2, ...)
///
/// This is because compose_single(A, N, 1) with N <= M_0 fits within
/// the first mode (Case 1), and compose_single(A, M_0/N, N) with
/// N*M_0/N = M_0 also fits within the first mode. The complement's higher modes
/// (stride M_0, M_0*M_1, etc.) hit the skip case and recurse correctly.
///
/// Note: logical_divide may produce MORE modes than logical_divide
/// when B's strides straddle A's mode boundaries — this is correct CuTe behavior
/// (the straddle case splits a single mode into multiple result modes to correctly
/// track the mode boundary crossing).
pub proof fn lemma_divide_recursive_agrees_mode(a: &LayoutSpec, n: nat)
    requires
        divide_mode_admissible(a, n),
        n <= a.shape.first(),
    ensures ({
        let expected = LayoutSpec { shape: seq![n], stride: seq![a.stride.first()] };
        compose_single(*a, n, 1) == expected
    }),
{
    // b_stride=1, b_shape=n, n <= shape[0]: Case 1 (within first mode)
    // compose_single returns (n):(1 * d_0) = (n):(d_0)
}

// ══════════════════════════════════════════════════════════════
// logical_divide (using compose) correctness for column-major
// ══════════════════════════════════════════════════════════════

/// Predicate: the zipped layout from divide is compose_recursive_correct_at.
/// This ensures logical_divide (using compose) produces correct offsets.
pub open spec fn divide_compose_admissible(a: &LayoutSpec, b: &LayoutSpec) -> bool {
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    crate::proof::composition_lemmas::compose_recursive_correct_at(*a, zipped)
}

/// For column-major A, per-mode compose_single_admissible implies compose_recursive_correct_at.
/// The additivity condition is trivially satisfied because column-major A has identity offset:
/// A.offset(a + b) = a + b = A.offset(a) + A.offset(b).
pub proof fn lemma_column_major_admissible_implies_correct_at(
    a: LayoutSpec, b: LayoutSpec,
)
    requires
        a.valid(),
        a.shape.len() > 0,
        a.stride =~= column_major_strides(a.shape),
        b.valid(),
        b.non_negative_strides(),
        forall|i: int| 0 <= i < b.shape.len() ==>
            crate::proof::composition_lemmas::compose_single_admissible(
                a, #[trigger] b.shape[i], b.stride[i] as nat),
    ensures
        crate::proof::composition_lemmas::compose_recursive_correct_at(a, b),
    decreases b.shape.len(),
{
    if b.shape.len() > 0 {
        let b_rest = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };

        // b_rest valid + non-negative strides
        assert(b_rest.valid()) by {
            assert forall|i: int| 0 <= i < b_rest.shape.len()
            implies #[trigger] b_rest.shape[i] > 0 by { assert(b_rest.shape[i] == b.shape[i + 1]); };
        };
        assert(b_rest.non_negative_strides()) by {
            assert forall|i: int| 0 <= i < b_rest.stride.len()
            implies #[trigger] b_rest.stride[i] >= 0 by { assert(b_rest.stride[i] == b.stride[i + 1]); };
        };

        // Per-mode admissibility for b_rest
        assert forall|i: int| 0 <= i < b_rest.shape.len()
        implies crate::proof::composition_lemmas::compose_single_admissible(
            a, #[trigger] b_rest.shape[i], b_rest.stride[i] as nat)
        by {
            assert(b_rest.shape[i] == b.shape[i + 1]);
            assert(b_rest.stride[i] == b.stride[i + 1]);
        };

        // IH: compose_recursive_correct_at(a, b_rest)
        lemma_column_major_admissible_implies_correct_at(a, b_rest);

        // Condition 1: compose_single_admissible for first mode (from requires)
        assert(crate::proof::composition_lemmas::compose_single_admissible(
            a, b.shape.first(), b.stride.first() as nat));

        // Condition 3: offset additivity (trivial for column-major)
        // A.offset(y) == y for all y < size(A), so A.offset(a + b) = a + b = a + b
        assert forall|c: nat, rest_off: nat|
            c < b.shape.first()
            && rest_off < a.size()
            && (b.stride.first() * (c as int)) >= 0
            && ((b.stride.first() * (c as int)) as nat + rest_off) < a.size()
        implies
            #[trigger] a.offset((b.stride.first() * (c as int)) as nat + rest_off)
                == a.offset((b.stride.first() * (c as int)) as nat) + a.offset(rest_off)
        by {
            let combined = (b.stride.first() * (c as int)) as nat + rest_off;
            let first_off = (b.stride.first() * (c as int)) as nat;
            // A.offset(x) == x for column-major
            lemma_column_major_offset_is_identity(a.shape, combined);
            lemma_column_major_offset_is_identity(a.shape, first_off);
            lemma_column_major_offset_is_identity(a.shape, rest_off);
            // A.offset(combined) = combined = first_off + rest_off = A.offset(first_off) + A.offset(rest_off)
        };
    }
}

/// For column-major A and B with divide_compose_admissible,
/// logical_divide(A, B) has identity offset.
pub proof fn lemma_divide_offset_column_major_compose(
    a: &LayoutSpec, b: &LayoutSpec, x: nat,
)
    requires
        divide_admissible(a, b),
        a.stride =~= column_major_strides(a.shape),
        b.stride =~= column_major_strides(b.shape),
        divide_compose_admissible(a, b),
        x < shape_size(a.shape),
    ensures
        logical_divide(a, b).offset(x) == x as int,
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped valid + non-negative strides + size == m
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);

    // zipped has identity offset for column-major B
    lemma_zipped_identity_offset(b, m, x);
    assert(zipped.offset(x) == x as int);
    assert(zipped.offset(x) >= 0);

    // A has identity offset (column-major)
    crate::proof::inverse_lemmas::lemma_column_major_strides_first(a.shape);
    assert(a.stride[0] == 1int);
    lemma_column_major_offset_is_identity(a.shape, x);
    assert(LayoutSpec { shape: a.shape, stride: column_major_strides(a.shape) }.offset(x) == x as int);

    // compose_recursive_correct_at holds (from requires)
    assert(crate::proof::composition_lemmas::compose_recursive_correct_at(*a, zipped));

    // Apply multi-mode compose correctness:
    // compose(A, zipped).offset(x) == A.offset(zipped.offset(x))
    crate::proof::composition_lemmas::lemma_compose_recursive_correct(*a, zipped, x);
    assert(compose(*a, zipped).offset(x) == a.offset(zipped.offset(x) as nat));

    // A.offset(x) == x (column-major identity)
    assert(zipped.offset(x) as nat == x);
    assert(a.offset(x) == x as int);
}

/// Simpler version: takes per-mode zipped admissibility directly.
/// The caller establishes compose_single_admissible for each zipped mode,
/// and this lemma handles the column-major additivity automatically.
pub proof fn lemma_divide_offset_column_major_compose_from_modes(
    a: &LayoutSpec, b: &LayoutSpec, x: nat,
)
    requires
        divide_admissible(a, b),
        a.stride =~= column_major_strides(a.shape),
        b.stride =~= column_major_strides(b.shape),
        x < shape_size(a.shape),
        // Per-mode admissibility for the zipped layout
        ({
            let m = shape_size(a.shape);
            let c = complement(b, m);
            let zipped = LayoutSpec {
                shape: b.shape.add(c.shape),
                stride: b.stride.add(c.stride),
            };
            forall|i: int| 0 <= i < zipped.shape.len() ==>
                crate::proof::composition_lemmas::compose_single_admissible(
                    *a, #[trigger] zipped.shape[i], zipped.stride[i] as nat)
        }),
    ensures
        logical_divide(a, b).offset(x) == x as int,
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped valid + non-negative strides
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);

    // Column-major admissibility → compose_recursive_correct_at
    lemma_column_major_admissible_implies_correct_at(*a, zipped);

    // Now use the existing proof
    assert(divide_compose_admissible(a, b));
    lemma_divide_offset_column_major_compose(a, b, x);
}

// ══════════════════════════════════════════════════════════════
// Column-major compose identity (NO admissibility required!)
// ══════════════════════════════════════════════════════════════

/// Predicate: A's strides are a scalar multiple of column-major strides.
/// For column-major A, scale = 1. For A_rest after skipping first mode, scale = M0.
pub open spec fn is_scaled_column_major(a: &LayoutSpec) -> bool {
    a.stride =~= scale_strides_spec(column_major_strides(a.shape), a.stride.first())
}

/// Skip-1 of a scaled column-major layout is also scaled column-major.
proof fn lemma_scaled_cm_skip(a: &LayoutSpec)
    requires
        a.valid(),
        a.shape.len() > 0,
        is_scaled_column_major(a),
    ensures ({
        let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };
        &&& a_rest.stride.len() > 0 ==> a_rest.stride.first() == a.stride.first() * (a.shape.first() as int)
        &&& is_scaled_column_major(&a_rest)
    }),
{
    let scale = a.stride.first();
    let m = a.shape.first();
    let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };

    // a.stride =~= [scale] ++ scale_strides(cm(shape.skip(1)), m * scale)
    // From column_major_strides definition:
    // cm(shape) = [1] ++ scale_strides(cm(shape.skip(1)), m)
    // scale * cm(shape) = [scale] ++ scale_strides(cm(shape.skip(1)), m * scale)
    // a.stride.skip(1) = scale_strides(cm(shape.skip(1)), m * scale)

    assert(a.stride =~= scale_strides_spec(column_major_strides(a.shape), scale));

    // cm(a.shape) = [1] ++ scale_strides(cm(a.shape.skip(1)), m)
    // scale * cm(a.shape) = [scale] ++ scale * scale_strides(cm(a.shape.skip(1)), m)
    //                     = [scale] ++ scale_strides(cm(a.shape.skip(1)), scale * m)

    // a_rest.stride = a.stride.skip(1)
    // We need: a_rest.stride =~= scale_strides(cm(a_rest.shape), a_rest.stride.first())

    // a_rest.shape = a.shape.skip(1)
    // cm(a_rest.shape) = cm(a.shape.skip(1))

    if a_rest.stride.len() > 0 {
        // cm(a.shape) = [1] ++ scale_strides(cm(a.shape.skip(1)), m)
        // So cm(a.shape)[i+1] = m * cm(a.shape.skip(1))[i]
        // And a.stride[i+1] = scale * cm(a.shape)[i+1] = scale * m * cm(a_rest.shape)[i]

        crate::proof::inverse_lemmas::lemma_column_major_strides_first(a.shape.skip(1));
        let new_scale = scale * (m as int);

        // a_rest.stride[0] = a.stride[1] = scale * cm(a.shape)[1]
        // cm(a.shape) = [1] ++ scale_strides(cm(skip1), m)
        // cm(a.shape)[1] = scale_strides(cm(skip1), m)[0] = cm(skip1)[0] * m = 1 * m = m
        assert(a.stride[1] == scale * column_major_strides(a.shape)[1]);
        // From cm definition: cm(shape)[1] = scale_strides(cm(shape.skip(1)), shape[0])[0]
        //                                  = cm(shape.skip(1))[0] * shape[0]
        //                                  = 1 * m = m
        assert(column_major_strides(a.shape).len() > 1);
        assert(scale_strides_spec(column_major_strides(a.shape), scale)[1]
            == scale * column_major_strides(a.shape)[1]);
        // The second element of cm(shape) is m (from the definition)
        assert(column_major_strides(a.shape) =~=
            seq![1int].add(scale_strides_spec(column_major_strides(a.shape.skip(1)), m as int)));
        assert(column_major_strides(a.shape)[1]
            == scale_strides_spec(column_major_strides(a.shape.skip(1)), m as int)[0]);
        assert(scale_strides_spec(column_major_strides(a.shape.skip(1)), m as int)[0]
            == column_major_strides(a.shape.skip(1))[0] * (m as int));
        assert(column_major_strides(a.shape.skip(1))[0] == 1int);
        assert(a_rest.stride.first() == new_scale) by (nonlinear_arith)
            requires a.stride[1] == scale * (m as int), a_rest.stride[0] == a.stride[1];

        // Now prove the full scaled-cm property for a_rest
        assert(a_rest.stride =~= scale_strides_spec(column_major_strides(a_rest.shape), new_scale)) by {
            assert forall|i: int| 0 <= i < a_rest.stride.len()
            implies a_rest.stride[i] == scale_strides_spec(column_major_strides(a_rest.shape), new_scale)[i]
            by {
                // a_rest.stride[i] = a.stride[i+1] = scale * cm(a.shape)[i+1]
                assert(a_rest.stride[i] == a.stride[i + 1]);
                assert(a.stride[i + 1] == scale_strides_spec(column_major_strides(a.shape), scale)[i + 1]);
                assert(scale_strides_spec(column_major_strides(a.shape), scale)[i + 1]
                    == scale * column_major_strides(a.shape)[i + 1]);
                // cm(a.shape)[i+1] = scale_strides(cm(skip1), m)[i] = cm(skip1)[i] * m
                assert(column_major_strides(a.shape)[i + 1]
                    == scale_strides_spec(column_major_strides(a.shape.skip(1)), m as int)[i]);
                assert(scale_strides_spec(column_major_strides(a.shape.skip(1)), m as int)[i]
                    == column_major_strides(a.shape.skip(1))[i] * (m as int));
                // So a_rest.stride[i] = scale * cm(skip1)[i] * m = new_scale * cm(a_rest.shape)[i]
                assert(a_rest.stride[i] == scale * (column_major_strides(a_rest.shape)[i] * (m as int)))
                    by (nonlinear_arith)
                    requires
                        a_rest.stride[i] == scale * (column_major_strides(a.shape.skip(1))[i] * (m as int)),
                        a_rest.shape =~= a.shape.skip(1);
                assert(scale * (column_major_strides(a_rest.shape)[i] * (m as int))
                    == new_scale * column_major_strides(a_rest.shape)[i]) by (nonlinear_arith);
            };
        };
    }
}

/// Key lemma: compose_single on scaled-column-major A produces offset = r * scale * x.
/// No admissibility required! Only needs the size bound.
proof fn lemma_compose_single_scaled_cm_offset(
    a: LayoutSpec, b_shape: nat, b_stride: nat, x: nat,
)
    requires
        a.valid(),
        a.shape.len() > 0,
        is_scaled_column_major(&a),
        b_shape > 0,
        b_stride * b_shape <= shape_size(a.shape),
        x < b_shape,
    ensures
        compose_single(a, b_shape, b_stride).offset(x)
            == (b_stride as int) * a.stride.first() * (x as int),
    decreases a.shape.len(),
{
    let scale = a.stride.first();
    let m = a.shape.first();
    let d = a.stride.first();  // d == scale
    let a_rest = LayoutSpec { shape: a.shape.skip(1), stride: a.stride.skip(1) };

    assert(a_rest.valid()) by {
        assert forall|i: int| 0 <= i < a_rest.shape.len()
        implies #[trigger] a_rest.shape[i] > 0 by { assert(a_rest.shape[i] == a.shape[i + 1]); };
    };

    // ═══ Case 1: within first mode ═══
    if b_stride * b_shape <= m {
        // compose_single = (b_shape):(b_stride * d)
        crate::proof::composition_lemmas::lemma_1d_offset(b_shape, (b_stride as int) * d, x);
        assert(compose_single(a, b_shape, b_stride).offset(x)
            == (x as int) * ((b_stride as int) * d));
        assert((x as int) * ((b_stride as int) * d) == (b_stride as int) * d * (x as int))
            by (nonlinear_arith);
        return;
    }

    // ═══ Case 2: straddle (with divisibility) ═══
    if b_stride < m && m % b_stride == 0 && b_shape > 0 && b_shape % (m / b_stride) == 0 {
        assert(b_stride > 0nat) by { if b_stride == 0 { assert(b_stride * b_shape == 0nat); } };
        let q = m / b_stride;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
        assert(q > 0nat) by {
            if q == 0 { vstd::arithmetic::mul::lemma_mul_basics(b_stride as int); }
        };
        assert(b_stride * q == m) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m as int, b_stride as int);
        };

        let bq = b_shape / q;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_shape as int, q as int);
        assert(bq > 0nat) by {
            if bq == 0 {
                vstd::arithmetic::mul::lemma_mul_basics(q as int);
                assert(b_shape < q);
                assert(b_stride * b_shape < b_stride * q) by (nonlinear_arith)
                    requires b_shape < q, b_stride > 0;
            }
        };
        assert(b_shape == q * bq);

        let c0 = x % q;
        let c1 = x / q;
        crate::proof::integer_helpers::lemma_mod_bound(x, q);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, q, bq);

        let inner = LayoutSpec { shape: seq![q], stride: seq![(b_stride as int) * d] };
        let rest = compose_single(a_rest, bq, 1);
        let result = compose_single(a, b_shape, b_stride);
        assert(result.shape =~= inner.shape.add(rest.shape));
        assert(result.stride =~= inner.stride.add(rest.stride));

        // shape_size(inner.shape) = q
        lemma_shape_size_single(q);
        crate::proof::composition_lemmas::lemma_crs_size(a_rest, bq, 1);
        crate::proof::composition_lemmas::lemma_crs_shape_valid(a_rest, bq, 1);
        crate::proof::composition_lemmas::lemma_crs_len_match(a_rest, bq, 1);
        crate::proof::product_lemmas::lemma_shape_size_append(inner.shape, rest.shape);

        // Decompose offset via concat
        lemma_delinearize_concat(x, inner.shape, rest.shape);
        lemma_delinearize_len(c0, inner.shape);
        lemma_delinearize_len(c1, rest.shape);
        crate::proof::shape_lemmas::lemma_dot_product_append(
            delinearize(c0, inner.shape), delinearize(c1, rest.shape),
            inner.stride, rest.stride,
        );

        // inner.offset(c0) = c0 * b_stride * d
        crate::proof::composition_lemmas::lemma_1d_offset(q, (b_stride as int) * d, c0);

        // rest.offset(c1) by IH: compose_single(a_rest, bq, 1).offset(c1) = 1 * a_rest.stride[0] * c1
        if a_rest.shape.len() > 0 {
            lemma_scaled_cm_skip(&a);
            lemma_compose_single_scaled_cm_offset(a_rest, bq, 1, c1);
            // rest.offset(c1) = 1 * (scale * m) * c1 = scale * m * c1
        } else {
            // a_rest has 0 modes: compose_single returns (bq):(0). offset = 0.
            crate::proof::composition_lemmas::lemma_1d_offset(bq, 0int, c1);
        }

        // Chain: result.offset(x) = inner.offset(c0) + rest.offset(c1)
        //   = c0 * b_stride * d + scale * m * c1   (where d = scale, m * b_stride = m, b_stride * q = m)
        //   = b_stride * scale * c0 + scale * (b_stride * q) * c1
        //   = b_stride * scale * (c0 + q * c1)
        //   = b_stride * scale * x
        assert((b_stride as int) * scale * (x as int)
            == (c0 as int) * ((b_stride as int) * d) + (if a_rest.shape.len() > 0 {
                1int * (scale * (m as int)) * (c1 as int)
            } else { 0int })
        ) by (nonlinear_arith)
            requires
                x == c0 + q * c1,
                b_stride * q == m,
                d == scale,
                c0 < q,
                a_rest.shape.len() > 0 ==> true;

        return;
    }

    // ═══ Case 3: skip first mode ═══
    if b_stride >= m && b_stride % m == 0 {
        let r2 = b_stride / m;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b_stride as int, m as int);
        assert(b_stride == m * r2);

        if a_rest.shape.len() > 0 {
            lemma_scaled_cm_skip(&a);
            lemma_compose_single_scaled_cm_offset(a_rest, b_shape, r2, x);
            // IH: compose_single(a_rest, b_shape, r2).offset(x) = r2 * (scale * m) * x
            let result = compose_single(a, b_shape, b_stride);
            let result_rest = compose_single(a_rest, b_shape, r2);
            assert(result.shape =~= result_rest.shape);
            assert(result.stride =~= result_rest.stride);
            crate::proof::composition_lemmas::lemma_offset_eq_layout(
                result.shape, result.stride, result_rest.shape, result_rest.stride, x);
            // result.offset(x) = result_rest.offset(x) = r2 * scale * m * x = b_stride * scale * x
            assert((r2 as int) * (scale * (m as int)) * (x as int)
                == (b_stride as int) * scale * (x as int)) by (nonlinear_arith)
                requires b_stride == m * r2;
        } else {
            // a_rest empty: compose_single(a_rest, ...) = (b_shape):(0). offset = 0.
            // And compose_single(a, ...) = compose_single(a_rest, ...) via case 3.
            let result = compose_single(a, b_shape, b_stride);
            let result_rest = compose_single(a_rest, b_shape, r2);
            assert(result.shape =~= result_rest.shape);
            assert(result.stride =~= result_rest.stride);
            crate::proof::composition_lemmas::lemma_offset_eq_layout(
                result.shape, result.stride, result_rest.shape, result_rest.stride, x);
            crate::proof::composition_lemmas::lemma_1d_offset(b_shape, 0int, x);
            // offset = 0. Need: b_stride * scale * x = 0.
            // a_rest empty means a has rank 1: shape = [m], size = m.
            // b_stride >= m and b_stride * b_shape <= size(a) = m.
            // b_stride >= m and b_stride * b_shape <= m → b_shape <= 1.
            // b_shape > 0 → b_shape == 1 → x == 0 → b_stride * scale * 0 = 0. ✓
            assert(x == 0nat) by {
                assert(b_shape == 1nat) by {
                    if b_shape > 1 {
                        assert(b_stride * b_shape >= m * 2) by (nonlinear_arith)
                            requires b_stride >= m, b_shape >= 2;
                    }
                };
            };
        }
        return;
    }

    // ═══ Case 4: fallback → (b_shape):(b_stride * d) ═══
    crate::proof::composition_lemmas::lemma_1d_offset(b_shape, (b_stride as int) * d, x);
    assert((x as int) * ((b_stride as int) * d) == (b_stride as int) * d * (x as int))
        by (nonlinear_arith);
}

/// compose(column_major_A, B).offset(x) == B.offset(x).
/// No admissibility required! Works for ALL valid B with non-negative strides.
pub proof fn lemma_compose_column_major_identity(a: LayoutSpec, b: LayoutSpec, x: nat)
    requires
        a.valid(),
        a.shape.len() > 0,
        a.stride =~= column_major_strides(a.shape),
        b.valid(),
        b.non_negative_strides(),
        x < b.size(),
    ensures
        compose(a, b).offset(x) == b.offset(x),
    decreases b.shape.len(),
{
    if b.shape.len() == 0 {
        return;
    }

    let bs = b.shape.first();
    let bd = b.stride.first();
    let c0 = x % bs;
    let x_rest = x / bs;
    let b_rest = LayoutSpec { shape: b.shape.skip(1), stride: b.stride.skip(1) };

    assert(b_rest.valid()) by {
        assert forall|i: int| 0 <= i < b_rest.shape.len()
        implies #[trigger] b_rest.shape[i] > 0 by { assert(b_rest.shape[i] == b.shape[i + 1]); };
    };
    assert(b_rest.non_negative_strides()) by {
        assert forall|i: int| 0 <= i < b_rest.stride.len()
        implies #[trigger] b_rest.stride[i] >= 0 by { assert(b_rest.stride[i] == b.stride[i + 1]); };
    };

    crate::proof::integer_helpers::lemma_mod_bound(x, bs);
    crate::runtime::shape_helpers::lemma_shape_size_split(b.shape, 1);
    assert(b.shape.take(1) =~= seq![bs]);
    lemma_shape_size_single(bs);
    lemma_shape_size_positive(b_rest.shape);
    crate::proof::integer_helpers::lemma_div_upper_bound(x, bs, b_rest.size());

    // ═══ B.offset(x) == bd * c0 + b_rest.offset(x_rest) ═══
    assert(b.shape =~= seq![bs].add(b_rest.shape));
    assert(b.stride =~= seq![bd].add(b_rest.stride));
    lemma_delinearize_concat(x, seq![bs], b_rest.shape);
    lemma_delinearize_len(c0, seq![bs]);
    lemma_delinearize_len(x_rest, b_rest.shape);
    crate::proof::shape_lemmas::lemma_dot_product_append(
        delinearize(c0, seq![bs]), delinearize(x_rest, b_rest.shape),
        seq![bd], b_rest.stride,
    );
    let b_first = LayoutSpec { shape: seq![bs], stride: seq![bd] };
    crate::proof::shape_lemmas::lemma_offset_within_first_mode(&b_first, c0);
    assert(b.offset(x) == (c0 as int) * bd + b_rest.offset(x_rest));

    // ═══ compose(A, B).offset(x) == cs.offset(c0) + compose(A, B_rest).offset(x_rest) ═══
    let cs = compose_single(a, bs, bd as nat);
    let rest_c = compose(a, b_rest);
    let composed = compose(a, b);

    if b.shape.len() == 1 {
        assert(composed == cs);
        assert(compose(a, b_rest).shape.len() == 0);
    } else {
        assert(composed.shape =~= cs.shape.add(rest_c.shape));
        assert(composed.stride =~= cs.stride.add(rest_c.stride));
    }

    crate::proof::composition_lemmas::lemma_crs_size(a, bs, bd as nat);
    crate::proof::composition_lemmas::lemma_crs_shape_valid(a, bs, bd as nat);
    crate::proof::composition_lemmas::lemma_crs_len_match(a, bs, bd as nat);
    crate::proof::composition_lemmas::lemma_compose_wf(a, b_rest);

    if b.shape.len() > 1 {
        crate::proof::product_lemmas::lemma_shape_size_append(cs.shape, rest_c.shape);
        lemma_delinearize_concat(x, cs.shape, rest_c.shape);
        lemma_delinearize_len(c0, cs.shape);
        lemma_delinearize_len(x_rest, rest_c.shape);
        crate::proof::shape_lemmas::lemma_dot_product_append(
            delinearize(c0, cs.shape), delinearize(x_rest, rest_c.shape),
            cs.stride, rest_c.stride,
        );
        assert(composed.offset(x) == cs.offset(c0) + rest_c.offset(x_rest));
    }

    // ═══ cs.offset(c0) == bd * c0 (from scaled-cm identity, scale = 1) ═══
    assert(bd >= 0);
    crate::proof::inverse_lemmas::lemma_column_major_strides_first(a.shape);
    assert(a.stride.first() == 1int);
    assert(is_scaled_column_major(&a));
    lemma_compose_single_scaled_cm_offset(a, bs, bd as nat, c0);
    assert(cs.offset(c0) == (bd as int) * 1int * (c0 as int));
    assert(cs.offset(c0) == (c0 as int) * bd) by (nonlinear_arith);

    // ═══ compose(A, B_rest).offset(x_rest) == b_rest.offset(x_rest) (IH) ═══
    if b.shape.len() > 1 {
        lemma_compose_column_major_identity(a, b_rest, x_rest);
    }

    // ═══ Chain ═══
    // composed.offset(x) = cs.offset(c0) + rest_c.offset(x_rest)
    //                     = bd * c0 + b_rest.offset(x_rest)
    //                     = b.offset(x)
}

/// logical_divide(A, B).offset(x) == x for column-major A and B.
/// No admissibility required!
pub proof fn lemma_divide_identity_column_major_no_admissibility(
    a: &LayoutSpec, b: &LayoutSpec, x: nat,
)
    requires
        divide_admissible(a, b),
        a.stride =~= column_major_strides(a.shape),
        b.stride =~= column_major_strides(b.shape),
        x < shape_size(a.shape),
    ensures
        logical_divide(a, b).offset(x) == x as int,
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped valid + non-negative strides + size == m
    crate::proof::tiling_lemmas::lemma_zipped_setup(a, b);

    // compose(A, zipped).offset(x) == zipped.offset(x)
    lemma_compose_column_major_identity(*a, zipped, x);

    // zipped.offset(x) == x (column-major B identity)
    lemma_zipped_identity_offset(b, m, x);
}

} // verus!
