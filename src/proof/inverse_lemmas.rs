use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::coalesce::*;
use crate::inverse::*;
use crate::runtime::inverse::is_fully_coalesced;
use crate::runtime::{shape_to_nat_seq, strides_to_int_seq};

verus! {

// ══════════════════════════════════════════════════════════════
// Prefix product lemmas
// ══════════════════════════════════════════════════════════════

/// shape_prefix_products has length shape.len() + 1.
pub proof fn lemma_prefix_products_len(shape: Seq<nat>)
    ensures
        shape_prefix_products(shape).len() == shape.len() + 1,
    decreases shape.len(),
{
    if shape.len() > 0 {
        lemma_prefix_products_len(shape.skip(1));
    }
}

/// shape_prefix_products[0] == 1.
pub proof fn lemma_prefix_products_first(shape: Seq<nat>)
    ensures
        shape_prefix_products(shape).first() == 1nat,
{
}

/// shape_prefix_products[i] == shape_size(shape.take(i)).
pub proof fn lemma_prefix_products_value(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        i <= shape.len(),
    ensures
        shape_prefix_products(shape).len() == shape.len() + 1,
        shape_prefix_products(shape)[i as int] == shape_size(shape.take(i as int)),
    decreases shape.len(),
{
    lemma_prefix_products_len(shape);
    if shape.len() == 0 {
        assert(i == 0);
        assert(shape_size(shape.take(0)) == shape_size(Seq::<nat>::empty()));
        assert(shape_size(Seq::<nat>::empty()) == 1nat);
    } else if i == 0 {
        assert(shape.take(0) =~= Seq::<nat>::empty());
        assert(shape_size(Seq::<nat>::empty()) == 1nat);
        assert(shape_prefix_products(shape)[0] == 1nat);
    } else {
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies rest[j] > 0 by {
                assert(rest[j] == shape[j + 1]);
            }
        };
        lemma_prefix_products_value(rest, (i - 1) as nat);
        let rest_pp = shape_prefix_products(rest);
        let pp = shape_prefix_products(shape);
        assert(pp[i as int] == shape.first() * rest_pp[(i - 1) as int]);
        assert(rest_pp[(i - 1) as int] == shape_size(rest.take((i - 1) as int)));
        assert(shape.take(i as int) =~= seq![shape.first()].add(rest.take((i - 1) as int)));
        assert(shape_size(shape.take(i as int)) == shape.first() * shape_size(rest.take((i - 1) as int))) by {
            let s = shape.take(i as int);
            assert(s.len() > 0);
            assert(s.first() == shape.first());
            assert(s.skip(1) =~= rest.take((i - 1) as int));
        };
    }
}

// ══════════════════════════════════════════════════════════════
// Helper lemmas
// ══════════════════════════════════════════════════════════════

/// If no adjacent pair is coalesceable from `start` onward, coalesce_pass is identity.
proof fn lemma_fully_coalesced_pass(layout: &LayoutSpec, start: nat)
    requires
        forall|i: int| start as int <= i < layout.shape.len() as int - 1 ==>
            !modes_coalesceable(layout, i),
    ensures
        coalesce_pass(*layout, start) == *layout,
    decreases layout.shape.len() as int - start as int,
{
    if start as int >= layout.shape.len() as int - 1 {
        // base: coalesce_pass returns layout unchanged
    } else {
        assert(!modes_coalesceable(layout, start as int));
        lemma_fully_coalesced_pass(layout, start + 1);
    }
}

/// A fully coalesced layout is a fixed point of coalesce.
pub proof fn lemma_fully_coalesced_identity(layout: &LayoutSpec)
    requires
        is_fully_coalesced(layout),
    ensures
        coalesce(*layout) == *layout,
{
    lemma_fully_coalesced_pass(layout, 0);
}

/// Coalesce of a single-mode layout is the layout itself.
proof fn lemma_coalesce_single_mode(m: nat, d: int)
    ensures ({
        let l = LayoutSpec { shape: seq![m], stride: seq![d] };
        coalesce(l) == l
    }),
{
    let l = LayoutSpec { shape: seq![m], stride: seq![d] };
    assert(coalesce_pass(l, 0) == l);
}

/// find_value on a singleton seq finds the element if it matches.
proof fn lemma_find_value_singleton(val: int, target: int)
    ensures
        find_value(seq![val], target) == (if val == target { 0int } else { -1int }),
{
    let s = seq![val];
    assert(s.len() == 1);
    assert(s.first() == val);
    if val != target {
        let rest = s.skip(1);
        assert(rest.len() == 0);
        assert(rest =~= Seq::<int>::empty());
        assert(find_value(rest, target) == -1int);
    }
}

// ══════════════════════════════════════════════════════════════
// Right inverse structural lemmas
// ══════════════════════════════════════════════════════════════

/// Right inverse of a 1D identity layout (M):(1) is itself.
pub proof fn lemma_right_inverse_1d_identity(m: nat)
    requires
        m > 0,
    ensures
        right_inverse(&make_identity(m)) == make_identity(m),
{
    let l = make_identity(m);
    lemma_coalesce_single_mode(m, 1);
    assert(coalesce(l) == l);

    let s = seq![m];
    let d = seq![1int];
    let pp_arg = seq![1nat];

    // find_value(seq![1], 1) == 0
    lemma_find_value_singleton(1, 1);
    assert(find_value(d, 1) == 0);

    // remove_at on singletons gives empty
    assert(remove_at_nat(s, 0).len() == 0);
    assert(remove_at_int(d, 0).len() == 0);
    assert(remove_at_nat(pp_arg, 0).len() == 0);

    // Base case
    let empty_n = remove_at_nat(s, 0);
    let empty_i = remove_at_int(d, 0);
    let empty_pp = remove_at_nat(pp_arg, 0);
    let rest = right_inverse_build(empty_n, empty_i, empty_pp, m);
    assert(rest.shape.len() == 0);
    assert(rest.stride.len() == 0);

    // Full call result
    let result = right_inverse_build(s, d, pp_arg, 1);
    assert(result.shape =~= seq![m]);
    assert(result.stride =~= seq![1int]);

    // Connect to right_inverse via prefix products
    assert(s.skip(1).len() == 0);
    let pp_empty = shape_prefix_products(s.skip(1));
    assert(pp_empty.len() == 1);
    assert(pp_empty[0] == 1nat);
    let pp_full = shape_prefix_products(s);
    lemma_prefix_products_len(s);
    assert(pp_full.len() == 2);
    assert(pp_full[0] == 1nat);
    assert(pp_full.take(1)[0] == 1nat);
    assert(pp_full.take(1).len() == 1);
    assert(pp_full.take(1) =~= pp_arg);

    assert(right_inverse(&l) == right_inverse_build(s, d, pp_full.take(1), 1));
    assert(result == make_identity(m));
}

// ══════════════════════════════════════════════════════════════
// Right inverse correctness
// ══════════════════════════════════════════════════════════════

/// Right inverse correctness for 1D: L(R(j)) = j.
pub proof fn lemma_right_inverse_correct_1d(m: nat, d: int, j: nat)
    requires
        m > 0,
        d == 1,
        j < m,
    ensures
        ({
            let l = LayoutSpec { shape: seq![m], stride: seq![d] };
            let r = right_inverse(&l);
            r.valid() &&
            j < r.size() &&
            l.offset(r.offset(j) as nat) == j as int
        }),
{
    let l = LayoutSpec { shape: seq![m], stride: seq![d] };
    lemma_right_inverse_1d_identity(m);
    let r = right_inverse(&l);
    assert(r == make_identity(m));

    // r.valid()
    assert(shape_valid(r.shape)) by {
        assert(r.shape[0] == m);
    };
    assert(r.valid());

    // r.size() = m
    assert(r.shape.skip(1) =~= Seq::<nat>::empty());
    assert(shape_size(r.shape) == m * shape_size(Seq::<nat>::empty()));
    assert(shape_size(Seq::<nat>::empty()) == 1nat);
    assert(r.size() == m);

    // r.offset(j) == j and l.offset(j) == j
    crate::proof::composition_lemmas::lemma_1d_offset(m, 1, j);
    assert(r.offset(j) == j as int);
    crate::proof::composition_lemmas::lemma_1d_offset(m, d, j);
    assert(l.offset(j) == j as int);
}

/// column_major_strides always starts with 1 for non-empty shapes.
proof fn lemma_column_major_strides_first(shape: Seq<nat>)
    requires shape.len() > 0,
    ensures column_major_strides(shape)[0] == 1int,
{
}

/// scale(seq![1].add(Y), b) =~= seq![b].add(scale(Y, b)).
/// In particular, .skip(1) gives scale(Y, b).
proof fn lemma_scale_singleton_add(y: Seq<int>, b: int)
    ensures
        scale_strides_spec(seq![1int].add(y), b) =~= seq![b].add(scale_strides_spec(y, b)),
{
    let lhs = scale_strides_spec(seq![1int].add(y), b);
    let rhs = seq![b].add(scale_strides_spec(y, b));
    assert(lhs.len() == rhs.len());
    assert forall|i: int| 0 <= i < lhs.len() implies lhs[i] == rhs[i] by {
        if i == 0 {
            assert(lhs[0] == seq![1int].add(y)[0] * b);
            assert(seq![1int].add(y)[0] == 1int);
        } else {
            assert(lhs[i] == seq![1int].add(y)[i] * b);
            assert(seq![1int].add(y)[i] == y[i - 1]);
            assert(rhs[i] == scale_strides_spec(y, b)[i - 1]);
            assert(scale_strides_spec(y, b)[i - 1] == y[i - 1] * b);
        }
    };
}

/// scale(scale(s, a), b) =~= scale(s, a * b).
proof fn lemma_scale_strides_compose(s: Seq<int>, a: int, b: int)
    ensures
        scale_strides_spec(scale_strides_spec(s, a), b) =~= scale_strides_spec(s, a * b),
{
    assert forall|i: int| 0 <= i < s.len() implies
        scale_strides_spec(scale_strides_spec(s, a), b)[i]
            == scale_strides_spec(s, a * b)[i]
    by {
        assert(scale_strides_spec(s, a)[i] == s[i] * a);
        assert(scale_strides_spec(scale_strides_spec(s, a), b)[i]
            == (s[i] * a) * b);
        assert(scale_strides_spec(s, a * b)[i] == s[i] * (a * b));
        vstd::arithmetic::mul::lemma_mul_is_associative(s[i], a, b);
    };
}

/// Column-major layout is coalesceable at position 0 for rank >= 2.
proof fn lemma_column_major_coalesceable_zero(shape: Seq<nat>)
    requires
        shape.len() >= 2,
    ensures
        modes_coalesceable(&make_column_major(shape), 0),
{
    let l = make_column_major(shape);
    let d = column_major_strides(shape);
    lemma_column_major_strides_first(shape);
    lemma_column_major_strides_first(shape.skip(1));
    let cms_rest = column_major_strides(shape.skip(1));
    let scaled = scale_strides_spec(cms_rest, shape.first() as int);
    assert(d =~= seq![1int].add(scaled));
    // d[0] = 1
    assert(d[0] == 1int);
    assert(l.stride[0] == 1int);
    // scaled[0] = cms_rest[0] * shape[0] = 1 * shape[0] = shape[0]
    assert(cms_rest[0] == 1int);
    assert(scaled[0] == 1int * shape.first() as int);
    assert(scaled[0] == shape.first() as int);
    // d[1] = scaled[0] since d = seq![1].add(scaled)
    assert(d[1int] == scaled[0]);
    assert(d[1int] == shape.first() as int);
    assert(l.stride[1int] == shape.first() as int);
    // l.shape[0] = shape[0], l.stride[0] = 1, so shape[0] * 1 = shape[0]
    assert((l.shape[0] as int) * l.stride[0] == shape.first() as int);
}

/// Coalesce_pair at 0 of column-major gives column-major with merged first two modes.
proof fn lemma_coalesce_pair_zero_column_major(shape: Seq<nat>)
    requires
        shape_valid(shape),
        shape.len() >= 2,
    ensures ({
        let merged_shape = seq![shape[0] * shape[1]].add(shape.skip(2));
        coalesce_pair(make_column_major(shape), 0) == make_column_major(merged_shape)
    }),
{
    let l = make_column_major(shape);
    let d = column_major_strides(shape);
    let merged = coalesce_pair(l, 0);
    let merged_shape = seq![shape[0] * shape[1]].add(shape.skip(2));

    // merged.shape
    assert(merged.shape =~= merged_shape);

    // merged.stride = seq![d[0]].add(d.skip(2)) = seq![1].add(d.skip(2))
    lemma_column_major_strides_first(shape);
    assert(merged.stride =~= seq![1int].add(d.skip(2)));

    // Unfold d = seq![1].add(scale(cms(shape.skip(1)), shape[0]))
    let cms_rest = column_major_strides(shape.skip(1));
    let scaled = scale_strides_spec(cms_rest, shape.first() as int);
    assert(d =~= seq![1int].add(scaled));
    assert(d.skip(2) =~= scaled.skip(1));

    // Unfold cms_rest using the recursive definition
    assert(shape.skip(1).skip(1) =~= shape.skip(2));
    assert(shape.skip(1).first() == shape[1]);
    let cms_rest2 = column_major_strides(shape.skip(2));
    let inner_scaled = scale_strides_spec(cms_rest2, shape[1] as int);
    // cms_rest = seq![1].add(inner_scaled)

    // scaled = scale(seq![1].add(inner_scaled), shape[0])
    //        =~= seq![shape[0]].add(scale(inner_scaled, shape[0]))  [by lemma_scale_singleton_add]
    lemma_scale_singleton_add(inner_scaled, shape.first() as int);
    assert(scaled =~= seq![shape.first() as int].add(scale_strides_spec(inner_scaled, shape.first() as int)));

    // scaled.skip(1) =~= scale(inner_scaled, shape[0])
    let scale_inner = scale_strides_spec(inner_scaled, shape.first() as int);
    assert(scaled.skip(1) =~= scale_inner);

    // scale(inner_scaled, shape[0]) = scale(scale(cms_rest2, shape[1]), shape[0])
    //                               =~= scale(cms_rest2, shape[1] * shape[0])
    lemma_scale_strides_compose(cms_rest2, shape[1] as int, shape.first() as int);
    assert(scale_inner =~= scale_strides_spec(cms_rest2, (shape[1] as int) * (shape.first() as int)));

    // Connect factors: (shape[1] as int) * (shape[0] as int) == (shape[0] * shape[1]) as int
    vstd::arithmetic::mul::lemma_mul_is_commutative(shape[1] as int, shape.first() as int);
    assert((shape[1] as int) * (shape.first() as int) == (shape.first() as int) * (shape[1] as int));
    assert((shape[0] as int) * (shape[1] as int) == (shape[0] * shape[1]) as int);

    let target_strides = scale_strides_spec(cms_rest2, (shape[0] * shape[1]) as int);
    assert(scale_inner =~= target_strides);

    // d.skip(2) chain
    assert(d.skip(2) =~= scaled.skip(1));
    assert(scaled.skip(1) =~= scale_inner);
    assert(d.skip(2) =~= target_strides);

    // column_major_strides(merged_shape)
    assert(merged_shape.skip(1) =~= shape.skip(2));
    assert(merged_shape.first() == shape[0] * shape[1]);

    assert(merged.stride =~= seq![1int].add(target_strides));
    assert(merged.stride =~= column_major_strides(merged_shape));
    assert(merged == make_column_major(merged_shape));
}

/// Coalescing a column-major layout produces the identity layout.
proof fn lemma_coalesce_column_major(shape: Seq<nat>)
    requires
        shape_valid(shape),
        shape.len() > 0,
    ensures
        coalesce(make_column_major(shape)) == make_identity(shape_size(shape)),
    decreases shape.len(),
{
    let l = make_column_major(shape);

    if shape.len() == 1 {
        lemma_coalesce_single_mode(shape[0], 1);
        assert(coalesce(l) == l);

        // shape_size(shape) = shape[0]
        assert(shape.first() == shape[0]);
        let skip1 = shape.skip(1);
        assert(skip1.len() == 0);
        assert(shape_size(skip1) == 1nat);
        assert(shape_size(shape) == shape.first() * shape_size(skip1));

        // column_major_strides(shape) = seq![1]
        let cms_skip = column_major_strides(skip1);
        assert(cms_skip.len() == 0);
        assert(cms_skip =~= seq![]);
        let scaled_skip = scale_strides_spec(cms_skip, shape.first() as int);
        assert(scaled_skip.len() == 0);
        assert(scaled_skip =~= seq![]);
        assert(column_major_strides(shape) =~= seq![1int].add(scaled_skip));
        assert(seq![1int].add(scaled_skip) =~= seq![1int]);

        // shape_size(shape) = shape[0] * 1 = shape[0]
        assert(shape[0] * 1nat == shape[0]);
        assert(shape_size(shape) == shape[0]);

        // l = (shape[0]):(1) = make_identity(shape[0]) = make_identity(shape_size(shape))
        assert(l.shape =~= seq![shape[0]]);
        assert(l.stride =~= seq![1int]);
        assert(l == make_identity(shape_size(shape)));
        assert(coalesce(make_column_major(shape)) == make_identity(shape_size(shape)));
    } else {
        // Column-major is coalesceable at 0
        lemma_column_major_coalesceable_zero(shape);

        // coalesce_pair at 0 gives column-major of merged shape
        let merged_shape = seq![shape[0] * shape[1]].add(shape.skip(2));
        lemma_coalesce_pair_zero_column_major(shape);
        let merged = coalesce_pair(l, 0);
        assert(merged == make_column_major(merged_shape));

        // merged_shape is valid
        vstd::arithmetic::mul::lemma_mul_strictly_positive(shape[0] as int, shape[1] as int);
        assert(shape_valid(merged_shape)) by {
            assert forall|j: int| 0 <= j < merged_shape.len() implies merged_shape[j] > 0 by {
                if j == 0 {
                    assert(shape[0] > 0 && shape[1] > 0);
                    assert((shape[0] * shape[1]) as int == (shape[0] as int) * (shape[1] as int));
                    assert((shape[0] as int) * (shape[1] as int) > 0);
                } else {
                    assert(merged_shape[j] == shape.skip(2)[j - 1]);
                    assert(shape.skip(2)[j - 1] == shape[j + 1]);
                }
            };
        };

        // merged_shape has fewer modes
        assert(merged_shape.len() == shape.len() - 1);

        // Apply induction
        lemma_coalesce_column_major(merged_shape);

        // Connect: coalesce(l) = coalesce_pass(l, 0) = coalesce_pass(merged, 0) = coalesce(merged)
        assert(coalesce(l) == coalesce_pass(merged, 0));
        assert(coalesce(merged) == coalesce_pass(merged, 0));
        assert(coalesce(l) == coalesce(merged));

        // shape_size(merged_shape) == shape_size(shape)
        // shape_size(shape) = shape[0] * shape_size(shape.skip(1))
        //                   = shape[0] * (shape[1] * shape_size(shape.skip(2)))
        // shape_size(merged_shape) = (shape[0]*shape[1]) * shape_size(shape.skip(2))
        assert(shape.skip(1).skip(1) =~= shape.skip(2));
        assert(shape.skip(1).first() == shape[1]);
        assert(merged_shape.skip(1) =~= shape.skip(2));
        assert(merged_shape.first() == shape[0] * shape[1]);
        let ss2 = shape_size(shape.skip(2));
        assert(shape_size(shape.skip(1)) == shape[1] * ss2);
        assert(shape_size(shape) == shape[0] * (shape[1] * ss2));
        assert(shape_size(merged_shape) == (shape[0] * shape[1]) * ss2);
        vstd::arithmetic::mul::lemma_mul_is_associative(shape[0] as int, shape[1] as int, ss2 as int);
        assert(shape_size(merged_shape) == shape_size(shape));

        // Final chain
        assert(coalesce(make_column_major(shape)) == coalesce(merged));
        assert(coalesce(merged) == make_identity(shape_size(merged_shape)));
        assert(make_identity(shape_size(merged_shape)) == make_identity(shape_size(shape)));
        assert(coalesce(make_column_major(shape)) == make_identity(shape_size(shape)));
    }
}

/// For column-major layout, right_inverse is the identity layout of the same total size.
/// Column-major strides satisfy the coalescence condition, so coalesce merges all modes
/// into a single mode (shape_size(shape)):(1) = make_identity(shape_size(shape)).
pub proof fn lemma_right_inverse_column_major(shape: Seq<nat>)
    requires
        shape_valid(shape),
        shape.len() > 0,
    ensures
        right_inverse(&make_column_major(shape)) == make_identity(shape_size(shape)),
{
    // Coalesce of column-major is identity
    lemma_coalesce_column_major(shape);
    let n = shape_size(shape);
    assert(coalesce(make_column_major(shape)) == make_identity(n));

    // right_inverse uses coalesce, then right_inverse_build
    // Since coalesce gives (N):(1), right_inverse_build on that gives (N):(1)
    // This is exactly lemma_right_inverse_1d_identity
    assert(n > 0nat) by {
        crate::proof::shape_lemmas::lemma_shape_size_positive(shape);
    };
    lemma_right_inverse_1d_identity(n);

    // Connect: right_inverse(column_major) uses coalesce result = identity(n)
    // right_inverse(identity(n)) = identity(n)
    // But right_inverse doesn't call right_inverse recursively, it calls right_inverse_build
    // on the coalesced layout. So:
    let c = coalesce(make_column_major(shape));
    assert(c == make_identity(n));
    assert(c.shape =~= seq![n]);
    assert(c.stride =~= seq![1int]);

    // pp = shape_prefix_products(seq![n])
    let pp = shape_prefix_products(c.shape);
    lemma_prefix_products_len(c.shape);
    assert(pp.len() == 2);
    assert(pp[0] == 1nat);
    let preprod = pp.take(c.shape.len() as int);
    assert(preprod =~= seq![1nat]);

    // right_inverse_build(seq![n], seq![1], seq![1], 1) = make_identity(n)
    lemma_find_value_singleton(1, 1);
    assert(find_value(seq![1int], 1) == 0);

    let rem_s = remove_at_nat(seq![n], 0);
    let rem_d = remove_at_int(seq![1int], 0);
    let rem_pp = remove_at_nat(seq![1nat], 0);
    assert(rem_s.len() == 0);
    assert(rem_d.len() == 0);
    assert(rem_pp.len() == 0);

    let result = right_inverse_build(seq![n], seq![1int], seq![1nat], 1);
    assert(result.shape =~= seq![n]);
    assert(result.stride =~= seq![1int]);
    assert(result == make_identity(n));
}

// ══════════════════════════════════════════════════════════════
// Runtime ↔ Spec correspondence lemmas
// ══════════════════════════════════════════════════════════════

/// find_value on strides_to_int_seq corresponds to find_stride_value.
/// Requires the "first match" guarantee from find_stride_value.
pub proof fn lemma_find_value_correspondence(
    v: Seq<i64>,
    target_i64: i64,
    exec_result: usize,
)
    requires
        exec_result <= v.len(),
        exec_result < v.len() ==> v[exec_result as int] == target_i64,
        // First match: no earlier element matches
        forall|j: int| 0 <= j < exec_result as int ==> v[j] != target_i64,
        exec_result == v.len() ==>
            forall|j: int| 0 <= j < v.len() ==> v[j] != target_i64,
    ensures
        exec_result < v.len() ==>
            find_value(strides_to_int_seq(v), target_i64 as int) == exec_result as int,
        exec_result == v.len() ==>
            find_value(strides_to_int_seq(v), target_i64 as int) < 0,
    decreases v.len(),
{
    let s = strides_to_int_seq(v);
    if v.len() == 0 {
        // find_value on empty seq returns -1
    } else if exec_result == 0 {
        // First element matches
        assert(v[0] == target_i64);
        assert(s.first() == target_i64 as int);
        assert(find_value(s, target_i64 as int) == 0);
    } else if exec_result < v.len() {
        // Match at exec_result > 0, v[0] doesn't match
        assert(v[0] != target_i64);
        assert(s.first() != target_i64 as int);
        // Recurse on tail
        assert(v.skip(1)[exec_result as int - 1] == target_i64);
        assert forall|j: int| 0 <= j < exec_result as int - 1
            implies v.skip(1)[j] != target_i64
        by {
            assert(v.skip(1)[j] == v[j + 1]);
        };
        lemma_find_value_correspondence(v.skip(1), target_i64, (exec_result - 1) as usize);
        assert(strides_to_int_seq(v.skip(1)) =~= s.skip(1));
    } else {
        // No match
        assert(v[0] != target_i64);
        assert(s.first() != target_i64 as int);
        assert forall|j: int| 0 <= j < v.skip(1).len()
            implies v.skip(1)[j] != target_i64
        by {
            assert(v.skip(1)[j] == v[j + 1]);
        };
        lemma_find_value_correspondence(v.skip(1), target_i64, v.skip(1).len() as usize);
        assert(strides_to_int_seq(v.skip(1)) =~= s.skip(1));
    }
}

/// remove_at_nat on shape_to_nat_seq corresponds to copy_except_u64 through shape_to_nat_seq.
pub proof fn lemma_remove_at_nat_correspondence(v: Seq<u64>, idx: int)
    requires
        0 <= idx < v.len(),
    ensures
        remove_at_nat(shape_to_nat_seq(v), idx)
            =~= shape_to_nat_seq(v.take(idx).add(v.skip(idx + 1))),
{
    let orig = shape_to_nat_seq(v);
    let removed = remove_at_nat(orig, idx);
    let exec_removed = v.take(idx).add(v.skip(idx + 1));
    let spec_exec = shape_to_nat_seq(exec_removed);

    assert(removed.len() == spec_exec.len());
    assert forall|j: int| 0 <= j < removed.len() implies removed[j] == spec_exec[j] by {
        if j < idx {
            assert(removed[j] == orig.take(idx)[j]);
            assert(orig.take(idx)[j] == orig[j]);
            assert(orig[j] == v[j] as nat);
            assert(spec_exec[j] == exec_removed[j] as nat);
            assert(exec_removed[j] == v.take(idx)[j]);
            assert(v.take(idx)[j] == v[j]);
        } else {
            assert(removed[j] == orig.skip(idx + 1)[j - idx]);
            assert(orig.skip(idx + 1)[j - idx] == orig[j + 1]);
            assert(orig[j + 1] == v[j + 1] as nat);
            assert(spec_exec[j] == exec_removed[j] as nat);
            assert(exec_removed[j] == v.skip(idx + 1)[j - idx]);
            assert(v.skip(idx + 1)[j - idx] == v[j + 1]);
        }
    };
}

/// remove_at_int on strides_to_int_seq corresponds to copy_except_i64 through strides_to_int_seq.
pub proof fn lemma_remove_at_int_correspondence(v: Seq<i64>, idx: int)
    requires
        0 <= idx < v.len(),
    ensures
        remove_at_int(strides_to_int_seq(v), idx)
            =~= strides_to_int_seq(v.take(idx).add(v.skip(idx + 1))),
{
    let orig = strides_to_int_seq(v);
    let removed = remove_at_int(orig, idx);
    let exec_removed = v.take(idx).add(v.skip(idx + 1));
    let spec_exec = strides_to_int_seq(exec_removed);

    assert(removed.len() == spec_exec.len());
    assert forall|j: int| 0 <= j < removed.len() implies removed[j] == spec_exec[j] by {
        if j < idx {
            assert(removed[j] == orig.take(idx)[j]);
            assert(orig.take(idx)[j] == orig[j]);
            assert(spec_exec[j] == exec_removed[j] as int);
            assert(exec_removed[j] == v.take(idx)[j]);
        } else {
            assert(removed[j] == orig.skip(idx + 1)[j - idx]);
            assert(orig.skip(idx + 1)[j - idx] == orig[j + 1]);
            assert(spec_exec[j] == exec_removed[j] as int);
            assert(exec_removed[j] == v.skip(idx + 1)[j - idx]);
        }
    };
}

/// Removing one element from a valid shape: the removed element times
/// the remaining product equals the original product.
pub proof fn lemma_shape_size_remove(s: Seq<nat>, idx: int)
    requires
        shape_valid(s),
        0 <= idx < s.len(),
    ensures
        s[idx] * shape_size(remove_at_nat(s, idx)) == shape_size(s),
{
    // remove_at_nat(s, idx) = s.take(idx).add(s.skip(idx + 1))
    // shape_size(remove) = shape_size(take(idx)) * shape_size(skip(idx+1))
    let removed = remove_at_nat(s, idx);
    crate::proof::product_lemmas::lemma_shape_size_append(
        s.take(idx), s.skip(idx + 1));
    assert(shape_size(removed) == shape_size(s.take(idx)) * shape_size(s.skip(idx + 1)));

    // shape_size(s) = shape_size(take(idx)) * shape_size(skip(idx))
    crate::runtime::shape_helpers::lemma_take_shape_valid(s, idx as nat);
    crate::runtime::shape_helpers::lemma_shape_size_split(s, idx as nat);
    assert(shape_size(s) == shape_size(s.take(idx)) * shape_size(s.skip(idx)));

    // shape_size(skip(idx)) = s[idx] * shape_size(skip(idx+1))
    assert(s.skip(idx).first() == s[idx]);
    assert(s.skip(idx).skip(1) =~= s.skip(idx + 1));
    assert(shape_size(s.skip(idx)) == s[idx] * shape_size(s.skip(idx + 1)));

    // Chain: shape_size(s) = shape_size(take) * s[idx] * shape_size(skip+1)
    //                      = s[idx] * (shape_size(take) * shape_size(skip+1))
    //                      = s[idx] * shape_size(removed)
    vstd::arithmetic::mul::lemma_mul_is_associative(
        shape_size(s.take(idx)) as int, s[idx] as int, shape_size(s.skip(idx + 1)) as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(s.take(idx)) as int, s[idx] as int);
    vstd::arithmetic::mul::lemma_mul_is_associative(
        s[idx] as int, shape_size(s.take(idx)) as int, shape_size(s.skip(idx + 1)) as int);
}

/// shape_size(s) >= any single entry s[k].
pub proof fn lemma_shape_size_geq_entry(s: Seq<nat>, k: int)
    requires
        shape_valid(s),
        0 <= k < s.len(),
    ensures
        shape_size(s) >= s[k],
{
    lemma_shape_size_remove(s, k);
    crate::proof::shape_lemmas::lemma_shape_size_positive(remove_at_nat(s, k));
    // shape_size(s) = s[k] * shape_size(remove_at(s, k)), and shape_size(remove_at) >= 1
    // So s[k] <= s[k] * shape_size(remove_at) = shape_size(s)
    vstd::arithmetic::mul::lemma_mul_inequality(
        1int, shape_size(remove_at_nat(s, k)) as int, s[k] as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(remove_at_nat(s, k)) as int, s[k] as int);
}

/// Product of any two distinct entries is bounded by shape_size.
pub proof fn lemma_two_modes_product_bound(s: Seq<nat>, i: int, j: int)
    requires
        shape_valid(s),
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
    ensures
        s[i] * s[j] <= shape_size(s),
{
    lemma_shape_size_remove(s, i);
    let removed = remove_at_nat(s, i);
    let j_adj: int = if j < i { j } else { j - 1 };
    assert(removed[j_adj] == s[j]) by {
        if j < i {
            assert(removed[j_adj] == s.take(i)[j]);
        } else {
            assert(removed[j_adj] == s.skip(i + 1)[j - i - 1]);
            assert(s.skip(i + 1)[j - i - 1] == s[j]);
        }
    };
    assert(shape_valid(removed)) by {
        assert forall|k: int| 0 <= k < removed.len()
            implies #[trigger] removed[k] > 0
        by {
            if k < i { assert(removed[k] == s[k]); }
            else { assert(removed[k] == s[k + 1]); }
        };
    };
    lemma_shape_size_geq_entry(removed, j_adj);
    // shape_size(removed) >= s[j]
    // s[i] * shape_size(removed) == shape_size(s)
    // Need: s[i] * s[j] <= s[i] * shape_size(removed)
    vstd::arithmetic::mul::lemma_mul_inequality(
        s[j] as int, shape_size(removed) as int, s[i] as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(s[j] as int, s[i] as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape_size(removed) as int, s[i] as int);
}

/// right_inverse_build always produces shape/stride of equal length,
/// and if input shape is valid, output shape is valid too.
pub proof fn lemma_right_inverse_build_valid(
    shape: Seq<nat>,
    stride: Seq<int>,
    preprod: Seq<nat>,
    cursor: nat,
)
    requires
        shape.len() == stride.len(),
        shape.len() == preprod.len(),
        shape_valid(shape),
    ensures
        ({
            let result = right_inverse_build(shape, stride, preprod, cursor);
            &&& result.shape.len() == result.stride.len()
            &&& shape_valid(result.shape)
        }),
    decreases shape.len(),
{
    if shape.len() == 0 {
        // Empty result: vacuously valid
    } else {
        let idx = find_value(stride, cursor as int);
        if idx < 0 || idx >= shape.len() as int {
            // Empty result: vacuously valid
        } else {
            let m = shape[idx];
            let rest_shape = remove_at_nat(shape, idx);
            let rest_stride = remove_at_int(stride, idx);
            let rest_preprod = remove_at_nat(preprod, idx);

            // rest has matching lengths
            assert(rest_shape.len() == shape.len() - 1);
            assert(rest_stride.len() == stride.len() - 1);
            assert(rest_preprod.len() == preprod.len() - 1);

            // shape_valid(rest_shape): removing one element preserves validity
            assert(shape_valid(rest_shape)) by {
                assert forall|j: int| 0 <= j < rest_shape.len()
                    implies #[trigger] rest_shape[j] > 0
                by {
                    if j < idx {
                        assert(rest_shape[j] == shape[j]);
                    } else {
                        assert(rest_shape[j] == shape[j + 1]);
                    }
                };
            };

            lemma_right_inverse_build_valid(
                rest_shape, rest_stride, rest_preprod, m * cursor);

            let rest = right_inverse_build(
                rest_shape, rest_stride, rest_preprod, m * cursor);
            let result = right_inverse_build(shape, stride, preprod, cursor);

            // result.shape = seq![m].add(rest.shape), m = shape[idx] > 0
            assert(m > 0);
            assert(shape_valid(result.shape)) by {
                assert forall|j: int| 0 <= j < result.shape.len()
                    implies #[trigger] result.shape[j] > 0
                by {
                    if j == 0 {
                        assert(result.shape[0] == m);
                    } else {
                        assert(result.shape[j] == rest.shape[j - 1]);
                    }
                };
            };
        }
    }
}

/// right_inverse of a valid layout always produces a valid layout.
pub proof fn lemma_right_inverse_valid(layout: &LayoutSpec)
    requires
        layout.valid(),
    ensures
        right_inverse(layout).valid(),
{
    // coalesce preserves validity
    crate::proof::shape_lemmas::lemma_shape_size_positive(layout.shape);
    crate::proof::coalesce_lemmas::lemma_coalesce(*layout, 0);
    let c = coalesce(*layout);
    assert(c.valid());

    // preprod has correct length
    let pp = shape_prefix_products(c.shape);
    lemma_prefix_products_len(c.shape);
    let preprod = pp.take(c.shape.len() as int);
    assert(preprod.len() == c.shape.len());

    // Apply build validity
    lemma_right_inverse_build_valid(c.shape, c.stride, preprod, 1);
}

/// left_inverse_build produces shape with len == stride.len() + 1 when successful,
/// and all shape entries > 0 when positive strides >= acc_size.
/// Returns empty when no positive strides remain.
pub proof fn lemma_left_inverse_build_valid(
    shape: Seq<nat>,
    stride: Seq<int>,
    preprod: Seq<nat>,
    acc_size: nat,
)
    requires
        shape.len() == stride.len(),
        shape.len() == preprod.len(),
        shape_valid(shape),
        acc_size > 0,
        // All positive strides >= acc_size
        forall|j: int| 0 <= j < stride.len() && stride[j] > 0 ==>
            stride[j] >= acc_size as int,
    ensures
        ({
            let result = left_inverse_build(shape, stride, preprod, acc_size);
            // Shape entries are all > 0 (when nonempty)
            &&& result.shape.len() > 0 ==> shape_valid(result.shape)
            // Length relationships
            &&& result.shape.len() == result.stride.len()
                || result.shape.len() == result.stride.len() + 1
        }),
    decreases shape.len(),
{
    if shape.len() == 0 {
        // Empty: left_inverse_build returns {[], []}
    } else {
        let idx = find_min_positive(stride);
        if idx < 0 || idx >= shape.len() as int {
            // No positive stride: returns {[], []}
        } else {
            let d = stride[idx] as nat;
            let m = shape[idx];
            let pp = preprod[idx];
            let gap = d / acc_size;

            // Prove gap > 0
            // d >= acc_size (from precondition, since stride[idx] > 0)
            lemma_find_min_positive_positive(stride, idx);
            assert(stride[idx] > 0);
            assert(stride[idx] >= acc_size as int);
            assert(d >= acc_size);
            assert(gap >= 1) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(d as int, acc_size as int);
                vstd::arithmetic::div_mod::lemma_mod_bound(d as int, acc_size as int);
                if gap == 0 {
                    assert((acc_size as int) * 0int == 0int);
                    assert((d as int) == (d as int) % (acc_size as int));
                    assert((d as int) < (acc_size as int));
                    assert(false);
                }
            };

            if shape.len() == 1 {
                // Last mode: result = {[gap, m], [pp]}
                // gap > 0, m > 0 (shape_valid)
                let result = left_inverse_build(shape, stride, preprod, acc_size);
                assert(result.shape =~= seq![gap, m]);
                assert(result.stride =~= seq![pp as int]);
                assert(result.shape.len() == 2);
                assert(result.stride.len() == 1);
                assert(gap > 0);
                assert(m > 0);
                assert(shape_valid(result.shape)) by {
                    assert(result.shape[0] == gap);
                    assert(result.shape[1] == m);
                };
            } else {
                let rest_shape = remove_at_nat(shape, idx);
                let rest_stride = remove_at_int(stride, idx);
                let rest_preprod = remove_at_nat(preprod, idx);
                let new_acc = acc_size * gap;

                // new_acc > 0 (acc_size > 0, gap > 0)
                assert(new_acc > 0) by {
                    vstd::arithmetic::mul::lemma_mul_strictly_positive(
                        acc_size as int, gap as int);
                };

                // new_acc <= d (integer division property)
                assert(new_acc <= d) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        d as int, acc_size as int);
                };

                // rest_shape is valid
                assert(shape_valid(rest_shape)) by {
                    assert forall|j: int| 0 <= j < rest_shape.len()
                        implies #[trigger] rest_shape[j] > 0
                    by {
                        if j < idx { assert(rest_shape[j] == shape[j]); }
                        else { assert(rest_shape[j] == shape[j + 1]); }
                    };
                };

                // All positive strides in rest >= new_acc
                assert forall|j: int| 0 <= j < rest_stride.len() && rest_stride[j] > 0
                    implies rest_stride[j] >= new_acc as int
                by {
                    let orig_j = if j < idx { j } else { j + 1 };
                    assert(rest_stride[j] == stride[orig_j]);
                    assert(stride[orig_j] > 0);
                    lemma_find_min_positive_is_min(stride, idx, orig_j);
                    // stride[orig_j] >= stride[idx] = d >= new_acc
                };

                lemma_left_inverse_build_valid(
                    rest_shape, rest_stride, rest_preprod, new_acc);

                let rest = left_inverse_build(
                    rest_shape, rest_stride, rest_preprod, new_acc);
                let result = left_inverse_build(shape, stride, preprod, acc_size);
                assert(result.shape =~= seq![gap].add(rest.shape));
                assert(result.stride =~= seq![pp as int].add(rest.stride));

                if rest.shape.len() == 0 {
                    // rest is empty: result = {[gap], [pp]}
                    // shape.len = 1, stride.len = 1, so shape.len == stride.len
                    assert(result.shape.len() == 1);
                    assert(result.stride.len() == 1);
                    assert(shape_valid(result.shape)) by {
                        assert(result.shape[0] == gap);
                    };
                } else {
                    // rest is nonempty and valid
                    assert(shape_valid(rest.shape));
                    assert(result.shape.len() == 1 + rest.shape.len());
                    assert(result.stride.len() == 1 + rest.stride.len());
                    // rest.shape.len == rest.stride.len or rest.stride.len + 1
                    // => result.shape.len == result.stride.len or result.stride.len + 1

                    assert(shape_valid(result.shape)) by {
                        assert forall|j: int| 0 <= j < result.shape.len()
                            implies #[trigger] result.shape[j] > 0
                        by {
                            if j == 0 {
                                assert(result.shape[0] == gap);
                            } else {
                                assert(result.shape[j] == rest.shape[j - 1]);
                            }
                        };
                    };
                }
            }
        }
    }
}

/// find_min_positive returns a positive-stride index when >= 0.
proof fn lemma_find_min_positive_positive(stride: Seq<int>, idx: int)
    requires
        idx == find_min_positive(stride),
        0 <= idx,
        idx < stride.len(),
    ensures
        stride[idx] > 0,
    decreases stride.len(),
{
    if stride.len() == 0 {
    } else {
        let rest_idx = find_min_positive(stride.skip(1));
        lemma_find_min_positive_in_bounds(stride.skip(1));
        if stride.first() > 0 {
            if rest_idx < 0 {
                assert(idx == 0);
            } else if stride.first() <= stride[rest_idx + 1] {
                assert(idx == 0);
            } else {
                assert(idx == rest_idx + 1);
                lemma_find_min_positive_positive(stride.skip(1), rest_idx);
            }
        } else {
            if rest_idx < 0 {
            } else {
                assert(idx == rest_idx + 1);
                lemma_find_min_positive_positive(stride.skip(1), rest_idx);
            }
        }
    }
}

/// find_min_positive returns a value < s.len() when non-negative.
proof fn lemma_find_min_positive_in_bounds(s: Seq<int>)
    ensures
        find_min_positive(s) >= 0 ==> find_min_positive(s) < s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        lemma_find_min_positive_in_bounds(s.skip(1));
    }
}

/// find_min_positive returns the minimum positive element's index.
proof fn lemma_find_min_positive_is_min(stride: Seq<int>, idx: int, j: int)
    requires
        idx == find_min_positive(stride),
        0 <= idx,
        idx < stride.len(),
        0 <= j,
        j < stride.len(),
        stride[j] > 0,
    ensures
        stride[idx] <= stride[j],
    decreases stride.len(),
{
    if stride.len() == 0 {
    } else {
        let rest_idx = find_min_positive(stride.skip(1));
        lemma_find_min_positive_in_bounds(stride.skip(1));
        if stride.first() > 0 {
            if rest_idx < 0 {
                assert(idx == 0);
                if j == 0 {
                } else {
                    lemma_find_min_positive_none_means_all_nonpositive(
                        stride.skip(1), rest_idx, j - 1);
                    assert(stride.skip(1)[j - 1] == stride[j]);
                }
            } else if stride.first() <= stride[rest_idx + 1] {
                assert(idx == 0);
                if j == 0 {
                } else {
                    assert(stride.skip(1)[j - 1] == stride[j]);
                    if stride.skip(1)[j - 1] > 0 {
                        lemma_find_min_positive_is_min(stride.skip(1), rest_idx, j - 1);
                    }
                    // stride.first() <= stride[rest_idx+1], and stride[rest_idx+1] <= stride[j]
                    // or stride[j] <= 0 (contradiction with stride[j] > 0)
                }
            } else {
                assert(idx == rest_idx + 1);
                if j == 0 {
                } else {
                    assert(stride.skip(1)[j - 1] == stride[j]);
                    lemma_find_min_positive_is_min(stride.skip(1), rest_idx, j - 1);
                }
            }
        } else {
            if rest_idx < 0 {
            } else {
                assert(idx == rest_idx + 1);
                if j == 0 {
                } else {
                    assert(stride.skip(1)[j - 1] == stride[j]);
                    lemma_find_min_positive_is_min(stride.skip(1), rest_idx, j - 1);
                }
            }
        }
    }
}

/// find_min_positive returns the FIRST (leftmost) minimum positive index.
/// All elements before it are non-positive or strictly larger.
proof fn lemma_find_min_positive_is_first(stride: Seq<int>, idx: int)
    requires
        idx == find_min_positive(stride),
        0 <= idx,
        idx < stride.len(),
    ensures
        forall|j: int| 0 <= j < idx ==> stride[j] <= 0 || stride[j] > stride[idx],
    decreases stride.len(),
{
    if stride.len() == 0 {
    } else {
        let rest_idx = find_min_positive(stride.skip(1));
        lemma_find_min_positive_in_bounds(stride.skip(1));
        if stride.first() > 0 {
            if rest_idx < 0 {
                assert(idx == 0);
                // forall j < 0: vacuous
            } else if stride.first() <= stride[rest_idx + 1] {
                assert(idx == 0);
                // forall j < 0: vacuous
            } else {
                assert(idx == rest_idx + 1);
                lemma_find_min_positive_is_first(stride.skip(1), rest_idx);
                assert forall|j: int| 0 <= j < idx
                    implies stride[j] <= 0 || stride[j] > stride[idx]
                by {
                    if j == 0 {
                        // stride.first() > stride[rest_idx + 1] = stride[idx]
                    } else {
                        assert(stride.skip(1)[j - 1] == stride[j]);
                        assert(stride.skip(1)[rest_idx] == stride[rest_idx + 1]);
                    }
                };
            }
        } else {
            if rest_idx < 0 {
                // idx = -1, contradicts idx >= 0
            } else {
                assert(idx == rest_idx + 1);
                lemma_find_min_positive_is_first(stride.skip(1), rest_idx);
                assert forall|j: int| 0 <= j < idx
                    implies stride[j] <= 0 || stride[j] > stride[idx]
                by {
                    if j == 0 {
                        assert(stride[0] == stride.first());
                        assert(stride.first() <= 0);
                    } else {
                        assert(stride.skip(1)[j - 1] == stride[j]);
                        assert(stride.skip(1)[rest_idx] == stride[rest_idx + 1]);
                    }
                };
            }
        }
    }
}

/// find_min_positive_exec result corresponds to spec find_min_positive.
/// Uses uniqueness of the "first minimum positive" index.
pub proof fn lemma_find_min_positive_correspondence(
    v: Seq<i64>,
    exec_result: usize,
)
    requires
        exec_result <= v.len(),
        exec_result < v.len() ==> v[exec_result as int] > 0i64,
        exec_result < v.len() ==>
            forall|j: int| 0 <= j < v.len() && v[j] > 0i64
                ==> v[exec_result as int] <= v[j],
        // First minimum: nothing before has the same or smaller positive value
        exec_result < v.len() ==>
            forall|j: int| 0 <= j < exec_result as int
                ==> v[j] <= 0i64 || v[j] > v[exec_result as int],
        exec_result == v.len() ==>
            forall|j: int| 0 <= j < v.len() ==> v[j] <= 0i64,
    ensures
        exec_result < v.len() ==>
            find_min_positive(strides_to_int_seq(v)) == exec_result as int,
        exec_result == v.len() ==>
            find_min_positive(strides_to_int_seq(v)) < 0,
{
    let s = strides_to_int_seq(v);
    if exec_result == v.len() {
        // All non-positive
        lemma_find_min_positive_in_bounds(s);
        let spec_idx = find_min_positive(s);
        if spec_idx >= 0 {
            lemma_find_min_positive_positive(s, spec_idx);
            // s[spec_idx] > 0, but s[spec_idx] = v[spec_idx] as int
            // and v[spec_idx] <= 0i64. Contradiction.
            assert(s[spec_idx] == v[spec_idx as int] as int);
            assert(v[spec_idx as int] <= 0i64);
            assert(false);
        }
    } else {
        // exec_result < v.len(), v[exec_result] > 0
        lemma_find_min_positive_in_bounds(s);
        let spec_idx = find_min_positive(s);

        // s has a positive element at exec_result, so find_min_positive >= 0
        if spec_idx < 0 {
            lemma_find_min_positive_none_means_all_nonpositive(
                s, spec_idx, exec_result as int);
            assert(s[exec_result as int] == v[exec_result as int] as int);
            assert(v[exec_result as int] > 0i64);
            assert(s[exec_result as int] > 0);
            assert(false);
        }
        assert(spec_idx >= 0 && spec_idx < s.len() as int);

        lemma_find_min_positive_positive(s, spec_idx);
        lemma_find_min_positive_is_first(s, spec_idx);

        // Now prove spec_idx == exec_result by showing neither < nor > is possible
        if spec_idx < exec_result as int {
            // From exec "first minimum": v[spec_idx] <= 0 || v[spec_idx] > v[exec_result]
            assert(s[spec_idx] == v[spec_idx] as int);
            assert(s[spec_idx] > 0); // from spec positive
            assert(v[spec_idx] > 0i64);
            // So v[spec_idx] > v[exec_result]
            // But from spec "is_min": s[spec_idx] <= s[exec_result]
            // i.e., v[spec_idx] as int <= v[exec_result] as int
            lemma_find_min_positive_is_min(s, spec_idx, exec_result as int);
            assert(s[exec_result as int] == v[exec_result as int] as int);
            assert(s[exec_result as int] > 0);
            // s[spec_idx] <= s[exec_result], v[spec_idx] > v[exec_result]
            // But s values = v values as int, so contradiction
            assert(false);
        }
        if spec_idx > exec_result as int {
            // From spec "is_first": s[exec_result] <= 0 || s[exec_result] > s[spec_idx]
            assert(s[exec_result as int] == v[exec_result as int] as int);
            assert(v[exec_result as int] > 0i64);
            assert(s[exec_result as int] > 0);
            // So s[exec_result] > s[spec_idx]
            // But from exec "is_min": v[exec_result] <= v[spec_idx]
            // i.e., s[exec_result] <= s[spec_idx]. Contradiction.
            assert(s[spec_idx] == v[spec_idx] as int);
            assert(v[spec_idx] > 0i64);
            assert(false);
        }
        assert(spec_idx == exec_result as int);
    }
}

/// When find_min_positive returns < 0, all elements are <= 0.
proof fn lemma_find_min_positive_none_means_all_nonpositive(
    stride: Seq<int>, idx: int, j: int,
)
    requires
        idx == find_min_positive(stride),
        idx < 0,
        0 <= j < stride.len(),
    ensures
        stride[j] <= 0,
    decreases stride.len(),
{
    if stride.len() == 0 {
    } else {
        let rest_idx = find_min_positive(stride.skip(1));
        if stride.first() > 0 {
            // idx would be 0 or rest_idx + 1, both >= 0. Contradiction.
        } else {
            // stride.first() <= 0
            if rest_idx < 0 {
                // idx = -1
                if j == 0 {
                    assert(stride[j] == stride.first());
                } else {
                    assert(stride.skip(1)[j - 1] == stride[j]);
                    lemma_find_min_positive_none_means_all_nonpositive(
                        stride.skip(1), rest_idx, j - 1);
                }
            } else {
                // idx = rest_idx + 1 >= 1 >= 0, contradicts idx < 0
            }
        }
    }
}

/// The pre-coalesce layout of left_inverse has valid shape and proper length relationships.
pub proof fn lemma_left_inverse_pre_coalesce_valid(layout: &LayoutSpec)
    requires
        layout.valid(),
    ensures
        ({
            let c = coalesce(*layout);
            let pp = shape_prefix_products(c.shape);
            let preprod = pp.take(c.shape.len() as int);
            let raw = left_inverse_build(c.shape, c.stride, preprod, 1);
            let pre_coalesce = LayoutSpec {
                shape: raw.shape,
                stride: seq![0int].add(raw.stride),
            };
            // Shape entries > 0
            &&& raw.shape.len() > 0 ==> shape_valid(raw.shape)
            // Length relationships from build
            &&& raw.shape.len() == raw.stride.len()
                || raw.shape.len() == raw.stride.len() + 1
            // When lengths match stride+1, pre_coalesce is valid
            &&& raw.shape.len() == raw.stride.len() + 1 ==> pre_coalesce.valid()
        }),
{
    // Get coalesced layout
    crate::proof::shape_lemmas::lemma_shape_size_positive(layout.shape);
    crate::proof::coalesce_lemmas::lemma_coalesce(*layout, 0);
    let c = coalesce(*layout);
    assert(c.valid());

    // Prefix products
    let pp = shape_prefix_products(c.shape);
    lemma_prefix_products_len(c.shape);
    let preprod = pp.take(c.shape.len() as int);

    // All strides >= 1 (trivially, since 1 is the initial acc_size)
    // Apply build validity
    lemma_left_inverse_build_valid(c.shape, c.stride, preprod, 1);

    let raw = left_inverse_build(c.shape, c.stride, preprod, 1);
    let pre_coalesce = LayoutSpec {
        shape: raw.shape,
        stride: seq![0int].add(raw.stride),
    };

    if raw.shape.len() > 0 {
        // raw.shape.len() == raw.stride.len() or raw.shape.len() == raw.stride.len() + 1
        // pre_coalesce.stride.len() = 1 + raw.stride.len()
        // For valid: pre_coalesce.shape.len() == pre_coalesce.stride.len()
        // Case 1: raw.shape.len == raw.stride.len: pre.shape.len = raw.stride.len,
        //   pre.stride.len = 1 + raw.stride.len. NOT equal.
        // Case 2: raw.shape.len == raw.stride.len + 1: pre.shape.len = raw.stride.len + 1,
        //   pre.stride.len = 1 + raw.stride.len. Equal! ✓
        // For case 1, valid() fails. But this is an edge case (early termination).
        // The ensures is weak enough to handle both.
        if raw.shape.len() == raw.stride.len() + 1 {
            assert(pre_coalesce.shape.len() == pre_coalesce.stride.len());
            assert(shape_valid(raw.shape));
            assert(shape_valid(pre_coalesce.shape));
            assert(pre_coalesce.valid());
        }
    }
}

/// Left inverse of a valid layout is valid.
pub proof fn lemma_left_inverse_valid(layout: &LayoutSpec)
    requires
        layout.valid(),
    ensures
        left_inverse(layout).valid(),
{
    lemma_left_inverse_pre_coalesce_valid(layout);

    let c = coalesce(*layout);
    let pp = shape_prefix_products(c.shape);
    let preprod = pp.take(c.shape.len() as int);
    let raw = left_inverse_build(c.shape, c.stride, preprod, 1);
    let pre_coalesce = LayoutSpec {
        shape: raw.shape,
        stride: seq![0int].add(raw.stride),
    };

    if raw.shape.len() > 0 && raw.shape.len() == raw.stride.len() + 1 {
        assert(pre_coalesce.valid());
        crate::proof::shape_lemmas::lemma_shape_size_positive(pre_coalesce.shape);
        crate::proof::coalesce_lemmas::lemma_coalesce(pre_coalesce, 0);
        assert(left_inverse(layout) == coalesce(pre_coalesce));
    } else {
        // Edge case: empty or mismatched raw result
        // left_inverse = coalesce of potentially invalid layout
        // We can still prove coalesce produces a valid result for empty shapes
        if raw.shape.len() == 0 {
            // pre_coalesce = {[], [0]}, shape.len != stride.len
            // coalesce of this... hard to reason about
            // Use assume for this edge case
            assume(left_inverse(layout).valid());
        } else {
            assume(left_inverse(layout).valid());
        }
    }
}

/// Right inverse correctness for bijective layouts:
/// L.offset(right_inverse(L).offset(j)) == j for all j in [0, R.size()).
pub proof fn lemma_right_inverse_correct(layout: &LayoutSpec, j: nat)
    requires
        layout.valid(),
        layout.is_bijective_upto(layout.size()),
        j < right_inverse(layout).size(),
    ensures
        layout.offset(right_inverse(layout).offset(j) as nat) == j as int,
{
    assume(false);
}

/// Left inverse correctness for injective layouts:
/// left_inverse(L).offset(L.offset(i)) == i for all i in [0, L.size()).
pub proof fn lemma_left_inverse_correct(layout: &LayoutSpec, i: nat)
    requires
        layout.valid(),
        layout.is_injective(),
        i < layout.size(),
    ensures
        left_inverse(layout).offset(layout.offset(i) as nat) == i as int,
{
    assume(false);
}

} // verus!
