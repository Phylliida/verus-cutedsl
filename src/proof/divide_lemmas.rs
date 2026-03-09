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

/// For rank-1 A and column-major B, logical_divide(A, B).offset(x) == A.offset(x).
/// Generalizes lemma_divide_offset_1d_a to multi-rank column-major B.
pub proof fn lemma_divide_offset(a: &LayoutSpec, b: &LayoutSpec, x: nat)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.stride =~= column_major_strides(b.shape),
        x < shape_size(a.shape),
    ensures
        logical_divide(a, b).offset(x) == a.offset(x),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };

    // zipped is valid with non-negative strides
    lemma_complement_rank(b, m);
    lemma_complement_valid(b, m);
    lemma_complement_positive_strides(b, m);
    assert(zipped.valid()) by {
        lemma_complement_shape_valid(b, m);
        assert forall|i: int| 0 <= i < zipped.shape.len()
        implies #[trigger] zipped.shape[i] > 0 by {
            if i < b.shape.len() as int {} else {
                assert(zipped.shape[i] == c.shape[(i - b.shape.len()) as int]);
            }
        };
    };
    assert(zipped.non_negative_strides()) by {
        assert forall|i: int| 0 <= i < zipped.stride.len()
        implies #[trigger] zipped.stride[i] >= 0 by {
            if i < b.stride.len() as int {
                assert(zipped.stride[i] == b.stride[i]);
                lemma_column_major_strides_len(b.shape);
            } else {
                assert(zipped.stride[i] == c.stride[(i - b.stride.len()) as int]);
            }
        };
    };

    // zipped.size() == m
    crate::proof::product_lemmas::lemma_shape_size_append(b.shape, c.shape);
    lemma_complement_size(b, m);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(b.shape) as int, shape_size(c.shape) as int);
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

    // By compose correctness: compose(A, zipped).offset(x) == A.offset(zipped.offset(x))
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    crate::proof::composition_lemmas::lemma_compose_correct(a_val, zipped, x);
    assert(compose(a_val, zipped).offset(x) == a_val.offset(zipped.offset(x) as nat));
    assert(zipped.offset(x) as nat == x);
}

/// For rank-1 A and column-major B, logical_divide preserves injectivity.
/// Generalizes lemma_divide_injective_1d_a to multi-rank column-major B.
pub proof fn lemma_divide_injective(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.stride =~= column_major_strides(b.shape),
        a.is_injective(),
    ensures
        logical_divide(a, b).is_injective(),
{
    lemma_divide_size(a, b);
    assert(shape_size(logical_divide(a, b).shape) == shape_size(a.shape));

    assert forall|x1: nat, x2: nat|
        x1 < shape_size(logical_divide(a, b).shape)
        && x2 < shape_size(logical_divide(a, b).shape)
        && x1 != x2
    implies
        logical_divide(a, b).offset(x1) != logical_divide(a, b).offset(x2)
    by {
        lemma_divide_offset(a, b, x1);
        lemma_divide_offset(a, b, x2);
        // divide.offset(xi) == a.offset(xi), and a is injective
        assert(logical_divide(a, b).offset(x1) == a.offset(x1));
        assert(logical_divide(a, b).offset(x2) == a.offset(x2));
    };
}

/// For rank-1 A and column-major B, logical_divide preserves bijectivity.
/// Since divide has the same offset function as A, bijectivity transfers directly.
pub proof fn lemma_divide_bijective(a: &LayoutSpec, b: &LayoutSpec, target: nat)
    requires
        divide_admissible(a, b),
        a.shape.len() == 1,
        b.stride =~= column_major_strides(b.shape),
        a.is_bijective_upto(target),
    ensures
        logical_divide(a, b).is_bijective_upto(target),
{
    // Injectivity: same offset function + A injective
    lemma_divide_injective(a, b);

    // Surjectivity: for any k in [0, target), A hits k, so divide hits k too
    lemma_divide_size(a, b);
    assert forall|k: int| 0 <= k < target as int
    implies #[trigger] logical_divide(a, b).offset_hit(k) by {
        // A is surjective onto [0, target), so some i < a.size() has a.offset(i) == k
        assert(a.offset_hit(k));
        let i: nat = choose|i: nat| i < a.size() && #[trigger] a.offset(i) == k;
        // divide.offset(i) == a.offset(i) == k, and i < divide.size()
        lemma_divide_offset(a, b, i);
        assert(logical_divide(a, b).offset(i) == k);
    };
}

} // verus!
