use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::divide::*;
use crate::product::*;
use crate::complement::*;
use crate::composition::*;
use crate::tiling::*;
use crate::predication::*;
use crate::slice::*;
use crate::proof::shape_lemmas::*;
use crate::proof::divide_lemmas::*;
use crate::proof::product_lemmas::*;

verus! {

/// Helper: the zipped layout (B ++ complement) is valid.
pub proof fn lemma_zipped_valid(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures ({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        let zipped = LayoutSpec {
            shape: b.shape.add(c.shape),
            stride: b.stride.add(c.stride),
        };
        zipped.valid()
    }),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    crate::proof::complement_lemmas::lemma_complement_valid(b, m);
    crate::proof::complement_lemmas::lemma_complement_shape_valid(b, m);
    assert forall|i: int| 0 <= i < b.shape.add(c.shape).len()
    implies #[trigger] b.shape.add(c.shape)[i] > 0 by {
        if i < b.shape.len() as int {} else {
            assert(b.shape.add(c.shape)[i] == c.shape[(i - b.shape.len()) as int]);
        }
    };
}

/// logical_divide produces a valid layout.
pub proof fn lemma_divide_valid(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        logical_divide(a, b).valid(),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    lemma_zipped_valid(a, b);
    // compose(a_val, zipped).shape =~= zipped.shape (valid)
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, zipped);
    lemma_compose_rank(a_val, zipped);
    // compose.shape =~= zipped.shape, which is valid
    // compose.shape.len() == compose.stride.len()
    assert forall|i: int| 0 <= i < logical_divide(a, b).shape.len()
    implies #[trigger] logical_divide(a, b).shape[i] > 0 by {
        assert(logical_divide(a, b).shape[i] == zipped.shape[i]);
    };
}

/// The DividedLayout from zipped_divide has valid structure.
pub proof fn lemma_zipped_divide_valid(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        divided_layout_valid(&zipped_divide(a, b)),
{
    lemma_divide_valid(a, b);
    lemma_divide_rank(a, b);
}

/// Helper: compose.shape =~= zipped.shape for the divide case.
proof fn lemma_divide_shape_eq_zipped(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures ({
        let m = shape_size(a.shape);
        let c = complement(b, m);
        logical_divide(a, b).shape =~= b.shape.add(c.shape)
    }),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);
    let a_val = LayoutSpec { shape: a.shape, stride: a.stride };
    let zipped = LayoutSpec {
        shape: b.shape.add(c.shape),
        stride: b.stride.add(c.stride),
    };
    lemma_zipped_valid(a, b);
    crate::proof::composition_lemmas::lemma_compose_shape(a_val, zipped);
}

/// tile_shape of zipped_divide equals B's shape.
pub proof fn lemma_zipped_divide_tile_shape(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        tile_shape(&zipped_divide(a, b)) =~= b.shape,
{
    lemma_divide_shape_eq_zipped(a, b);
    // divide.shape =~= B.shape ++ C.shape, take(B.len()) = B.shape
}

/// Total size of zipped_divide equals A's size.
pub proof fn lemma_zipped_divide_size(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        shape_size(zipped_divide(a, b).layout.shape) == shape_size(a.shape),
{
    lemma_divide_size(a, b);
}

/// tile_size of zipped_divide equals B's size.
pub proof fn lemma_zipped_divide_tile_size(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        tile_size(&zipped_divide(a, b)) == shape_size(b.shape),
{
    lemma_zipped_divide_tile_shape(a, b);
}

/// rest_shape of zipped_divide equals complement shape.
pub proof fn lemma_zipped_divide_rest_shape(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        rest_shape(&zipped_divide(a, b)) =~= complement(b, shape_size(a.shape)).shape,
{
    lemma_divide_shape_eq_zipped(a, b);
    // divide.shape =~= B.shape ++ C.shape, skip(B.len()) = C.shape
}

/// num_tiles_divided equals num_tiles.
pub proof fn lemma_zipped_divide_num_tiles(a: &LayoutSpec, b: &LayoutSpec)
    requires
        divide_admissible(a, b),
    ensures
        num_tiles_divided(&zipped_divide(a, b)) == num_tiles(a, b),
{
    let m = shape_size(a.shape);
    let c = complement(b, m);

    lemma_zipped_divide_rest_shape(a, b);
    // rest_shape =~= c.shape, so shape_size(rest_shape) == shape_size(c.shape)

    // shape_size(C.shape) * shape_size(B.shape) == m
    let n = shape_size(b.shape);
    crate::proof::complement_lemmas::lemma_complement_size(b, m);
    lemma_shape_size_positive(b.shape);
    crate::proof::complement_lemmas::lemma_complement_shape_valid(b, m);
    lemma_shape_size_positive(c.shape);
    vstd::arithmetic::mul::lemma_mul_is_commutative(shape_size(c.shape) as int, n as int);
    let sc = shape_size(c.shape);
    assert(n * sc == m);
    // Exact division: (n * sc) / n == sc
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(sc as int, n as int);
    // gives: (n as int * sc as int) / n as int == sc as int
    // Since n * sc == m as nats, m / n == sc
    assert(m / n == sc);
}

/// make_tiled_copy size = atom_size * thr_size * val_size.
pub proof fn lemma_tiled_copy_size(
    atom: &LayoutSpec,
    thr_layout: &LayoutSpec,
    val_layout: &LayoutSpec,
)
    requires
        tiled_copy_admissible(atom, thr_layout, val_layout),
    ensures
        shape_size(make_tiled_copy(atom, thr_layout, val_layout).shape)
            == shape_size(atom.shape)
               * shape_size(thr_layout.shape)
               * shape_size(val_layout.shape),
{
    let tv = logical_product(thr_layout, val_layout);
    lemma_raked_product_size(atom, &tv);
    lemma_product_size(thr_layout, val_layout);
    vstd::arithmetic::mul::lemma_mul_is_associative(
        shape_size(atom.shape) as int,
        shape_size(thr_layout.shape) as int,
        shape_size(val_layout.shape) as int,
    );
}

/// make_tiled_copy produces a valid layout.
pub proof fn lemma_tiled_copy_valid(
    atom: &LayoutSpec,
    thr_layout: &LayoutSpec,
    val_layout: &LayoutSpec,
)
    requires
        tiled_copy_admissible(atom, thr_layout, val_layout),
    ensures
        make_tiled_copy(atom, thr_layout, val_layout).valid(),
{
    let tv = logical_product(thr_layout, val_layout);
    lemma_product_valid(thr_layout, val_layout);
    lemma_raked_product_valid(atom, &tv);
}

// ══════════════════════════════════════════════════════════════
// Predicated divide proofs
// ══════════════════════════════════════════════════════════════

/// shape_size of a single-element shape is the element itself.
proof fn lemma_shape_size_singleton(m: nat)
    ensures shape_size(seq![m]) == m,
{
    let s = seq![m];
    assert(s.skip(1) =~= Seq::<nat>::empty());
    // shape_size(s) = s.first() * shape_size(s.skip(1)) = m * shape_size(seq![]) = m * 1 = m
    assert(s.first() == m);
    assert(shape_size(s.skip(1)) == 1nat);
    vstd::arithmetic::mul::lemma_mul_basics(m as int);
}

/// make_identity(m) is valid when m > 0.
proof fn lemma_identity_valid(m: nat)
    requires m > 0,
    ensures make_identity(m).valid(),
{
    let l = make_identity(m);
    assert(l.shape.len() == 1);
    assert(l.stride.len() == 1);
    assert(l.shape[0] == m);
}

/// Identity layout (m):(1) is complement-admissible with respect to any M
/// where M > 0 and M % m == 0.
proof fn lemma_identity_complement_admissible(m: nat, total: nat)
    requires
        m > 0,
        total > 0,
        total % m == 0,
    ensures
        complement_admissible(&make_identity(m), total),
{
    let b = make_identity(m);
    lemma_identity_valid(m);
    assert(b.shape.len() == 1);
    assert(b.shape[0] == m);
    assert(b.stride[0] == 1int);
    // last() for a single-element seq is the first element
    assert(b.shape.last() == m);
    assert(b.stride.last() == 1int);
    // m * 1 == m
    vstd::arithmetic::mul::lemma_mul_basics(m as int);
}

/// Predicated divide admissibility: padded identity divided by tile identity.
pub proof fn lemma_predicated_divide_admissible(original_size: nat, tile_size: nat)
    requires
        padded_divide_admissible(original_size, tile_size),
    ensures
        divide_admissible(
            &make_identity(padded_size(original_size, tile_size)),
            &make_identity(tile_size),
        ),
{
    let padded = padded_size(original_size, tile_size);
    let a = make_identity(padded);
    let b = make_identity(tile_size);

    crate::proof::predication_lemmas::lemma_padded_size_complement_admissible(original_size, tile_size);
    crate::proof::predication_lemmas::lemma_padded_size_ge(original_size, tile_size);
    assert(padded > 0);
    assert(padded % tile_size == 0);

    lemma_identity_valid(padded);
    lemma_identity_valid(tile_size);
    lemma_identity_complement_admissible(tile_size, padded);

    // shape_size(a.shape) == padded
    lemma_shape_size_singleton(padded);
    assert(shape_size(a.shape) == padded);
}

/// Predicated divide produces a valid DividedLayout.
pub proof fn lemma_predicated_divide_valid(original_size: nat, tile_size: nat)
    requires
        padded_divide_admissible(original_size, tile_size),
    ensures
        divided_layout_valid(&predicated_divide(original_size, tile_size)),
{
    lemma_predicated_divide_admissible(original_size, tile_size);
    lemma_zipped_divide_valid(
        &make_identity(padded_size(original_size, tile_size)),
        &make_identity(tile_size),
    );
}

/// Tile size of predicated_divide is ts.
pub proof fn lemma_predicated_divide_tile_size(original_size: nat, ts: nat)
    requires
        padded_divide_admissible(original_size, ts),
    ensures
        tile_size(&predicated_divide(original_size, ts)) == ts,
{
    lemma_predicated_divide_admissible(original_size, ts);
    let a = make_identity(padded_size(original_size, ts));
    let b = make_identity(ts);
    lemma_zipped_divide_tile_size(&a, &b);
    // tile_size(zipped_divide(a, b)) == shape_size(b.shape) == shape_size(seq![ts]) == ts
    lemma_shape_size_singleton(ts);
}

/// Number of tiles in predicated_divide is ceil_div(original_size, tile_size).
pub proof fn lemma_predicated_divide_num_tiles(original_size: nat, tile_size: nat)
    requires
        padded_divide_admissible(original_size, tile_size),
    ensures
        num_tiles_divided(&predicated_divide(original_size, tile_size))
            == num_tiles_ceil(original_size, tile_size),
{
    lemma_predicated_divide_admissible(original_size, tile_size);
    let padded = padded_size(original_size, tile_size);
    let a = make_identity(padded);
    let b = make_identity(tile_size);

    lemma_shape_size_singleton(padded);
    lemma_shape_size_singleton(tile_size);
    assert(shape_size(a.shape) == padded);
    assert(shape_size(b.shape) == tile_size);

    lemma_zipped_divide_num_tiles(&a, &b);
    // num_tiles_divided == num_tiles(a, b) == padded / tile_size

    crate::proof::predication_lemmas::lemma_num_tiles_is_padded(original_size, tile_size);
    let nt = num_tiles_ceil(original_size, tile_size);
    assert(nt * tile_size == padded);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(nt as int, tile_size as int);
}

/// Sum of valid element counts across all tiles equals original_size.
pub proof fn lemma_predicated_covers_all(original_size: nat, tile_size: nat)
    requires
        padded_divide_admissible(original_size, tile_size),
    ensures
        sum_valid_counts(
            num_tiles_ceil(original_size, tile_size),
            tile_size,
            original_size,
        ) == original_size,
{
    crate::proof::predication_lemmas::lemma_total_valid_elements(original_size, tile_size);
}

/// Predicated divide has identity offset: offset(x) == x for x < padded_size.
pub proof fn lemma_predicated_divide_offset_identity(
    original_size: nat, tile_size: nat, x: nat,
)
    requires
        padded_divide_admissible(original_size, tile_size),
        x < padded_size(original_size, tile_size),
    ensures
        predicated_divide(original_size, tile_size).layout.offset(x) == x as int,
{
    lemma_predicated_divide_admissible(original_size, tile_size);
    let padded = padded_size(original_size, tile_size);
    let a = make_identity(padded);
    let b = make_identity(tile_size);

    lemma_shape_size_singleton(padded);
    assert(shape_size(a.shape) == padded);
    assert(x < shape_size(a.shape));

    // logical_divide(a, b).offset(x) == a.offset(x) for rank-1 A, col-major B
    lemma_divide_offset_1d_a(&a, &b, x);

    // a.offset(x) == x since a = (padded):(1) is column-major
    // column_major_strides(seq![padded]):
    //   = seq![1].add(scale_strides_spec(column_major_strides(seq![padded].skip(1)), padded))
    //   = seq![1].add(scale_strides_spec(seq![], padded))
    //   = seq![1].add(seq![]) = seq![1]
    assert(seq![padded].skip(1) =~= Seq::<nat>::empty());
    assert(column_major_strides(Seq::<nat>::empty()) =~= Seq::<int>::empty());
    assert(scale_strides_spec(Seq::<int>::empty(), padded as int) =~= Seq::<int>::empty());
    assert(seq![1int].add(Seq::<int>::empty()) =~= seq![1int]);
    assert(a.stride =~= seq![1int]);
    assert(make_column_major(seq![padded]).stride =~= seq![1int]);
    assert(make_column_major(seq![padded]).shape =~= seq![padded]);

    crate::proof::injectivity_lemmas::lemma_column_major_offset_is_identity(
        seq![padded], x,
    );
    // make_column_major(seq![padded]).offset(x) == x
    // a and make_column_major(seq![padded]) have same shape and stride
    assert(a.offset(x) == make_column_major(seq![padded]).offset(x));
}

// ══════════════════════════════════════════════════════════════
// Slice partition lemmas (Phase 3b)
// ══════════════════════════════════════════════════════════════

/// For mode-0 slice: L.offset(i * M_0 + c) == slice_offset(L, 0, c) + slice_layout(L, 0, c).offset(i).
///
/// This reconstructs the full layout offset from a slice's residual offset plus the base.
pub proof fn lemma_slice_offset_reconstruction(
    layout: &LayoutSpec, c: nat, i: nat,
)
    requires
        layout.valid(),
        layout.rank() > 0,
        c < layout.shape[0],
        i < shape_size(layout.shape.skip(1)),
    ensures
        layout.offset(i * layout.shape[0] + c)
            == crate::slice::slice_offset(layout, 0, c)
               + crate::slice::slice_layout(layout, 0, c).offset(i),
{
    let m0 = layout.shape[0];
    let rest_shape = layout.shape.skip(1);
    let rest_stride = layout.stride.skip(1);
    let x = i * m0 + c;

    // x < shape_size(layout.shape)
    assert(shape_size(layout.shape) == m0 * shape_size(rest_shape));
    assert(x < shape_size(layout.shape)) by (nonlinear_arith)
        requires i < shape_size(rest_shape), c < m0, x == i * m0 + c,
            shape_size(layout.shape) == m0 * shape_size(rest_shape),
            m0 > 0;

    // delinearize(x, shape) = seq![c] ++ delinearize(i, rest_shape)
    // since x % m0 = c and x / m0 = i
    assert(x % m0 == c) by (nonlinear_arith)
        requires c < m0, x == i * m0 + c, m0 > 0;
    assert(x / m0 == i) by (nonlinear_arith)
        requires c < m0, x == i * m0 + c, m0 > 0;

    // Unfold delinearize one step
    assert(layout.shape.first() == m0);
    assert(delinearize(x, layout.shape) =~=
        seq![x % m0].add(delinearize(x / m0, rest_shape)));
    assert(delinearize(x, layout.shape) =~=
        seq![c].add(delinearize(i, rest_shape)));

    // Unfold the offset: dot(delinearize(x, shape), stride)
    // = dot(seq![c] ++ delinearize(i, rest_shape), seq![stride[0]] ++ rest_stride)
    assert(layout.stride =~= seq![layout.stride[0]].add(rest_stride)) by {
        assert(layout.stride.first() == layout.stride[0]);
        assert(layout.stride =~= seq![layout.stride.first()].add(layout.stride.skip(1)));
    };

    // Split the dot product
    lemma_delinearize_len(i, rest_shape);
    crate::proof::shape_lemmas::lemma_dot_product_append(
        seq![c], delinearize(i, rest_shape),
        seq![layout.stride[0]], rest_stride,
    );

    // dot(seq![c], seq![stride[0]]) = c * stride[0]
    assert(seq![c].first() == c);
    assert(seq![layout.stride[0]].first() == layout.stride[0]);
    assert(seq![c].skip(1) =~= Seq::<nat>::empty());
    assert(seq![layout.stride[0]].skip(1) =~= Seq::<int>::empty());
    assert(dot_product_nat_int(Seq::<nat>::empty(), Seq::<int>::empty()) == 0int);
    assert(dot_product_nat_int(seq![c], seq![layout.stride[0]]) == (c as int) * layout.stride[0]);

    // The residual layout offset
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, c);
    let sl = crate::slice::slice_layout(layout, 0, c);
    assert(sl.shape =~= rest_shape);
    assert(sl.stride =~= rest_stride);

    // sl.offset(i) = dot(delinearize(i, rest_shape), rest_stride)
    // slice_offset(layout, 0, c) = c * stride[0]
    // So: layout.offset(x) = c * stride[0] + sl.offset(i) = slice_offset + sl.offset(i)
}

/// Different mode-0 slices of an injective layout produce disjoint offset sets.
///
/// For c1 != c2, no offset in slice c1 can equal any offset in slice c2.
pub proof fn lemma_slice_disjoint(
    layout: &LayoutSpec, c1: nat, c2: nat, i: nat, j: nat,
)
    requires
        layout.valid(),
        layout.is_injective(),
        layout.rank() > 0,
        c1 < layout.shape[0],
        c2 < layout.shape[0],
        c1 != c2,
        i < shape_size(layout.shape.skip(1)),
        j < shape_size(layout.shape.skip(1)),
    ensures
        crate::slice::slice_offset(layout, 0, c1)
            + crate::slice::slice_layout(layout, 0, c1).offset(i)
        != crate::slice::slice_offset(layout, 0, c2)
            + crate::slice::slice_layout(layout, 0, c2).offset(j),
{
    let m0 = layout.shape[0];
    let rest_size = shape_size(layout.shape.skip(1));

    // Reconstruct full layout offsets
    lemma_slice_offset_reconstruction(layout, c1, i);
    lemma_slice_offset_reconstruction(layout, c2, j);

    let x1 = i * m0 + c1;
    let x2 = j * m0 + c2;

    // x1 != x2 because c1 != c2 and both < m0
    assert(x1 != x2) by (nonlinear_arith)
        requires c1 != c2, c1 < m0, c2 < m0, x1 == i * m0 + c1, x2 == j * m0 + c2, m0 > 0
    {
        // x1 % m0 = c1, x2 % m0 = c2, c1 != c2 => x1 != x2
        assert(x1 % m0 == c1);
        assert(x2 % m0 == c2);
    };

    // Both x1, x2 < shape_size(layout.shape)
    assert(shape_size(layout.shape) == m0 * rest_size);
    assert(x1 < shape_size(layout.shape)) by (nonlinear_arith)
        requires i < rest_size, c1 < m0, x1 == i * m0 + c1,
            shape_size(layout.shape) == m0 * rest_size, m0 > 0;
    assert(x2 < shape_size(layout.shape)) by (nonlinear_arith)
        requires j < rest_size, c2 < m0, x2 == j * m0 + c2,
            shape_size(layout.shape) == m0 * rest_size, m0 > 0;

    // By injectivity: layout.offset(x1) != layout.offset(x2)
    assert(layout.offset(x1) != layout.offset(x2));

    // By reconstruction: layout.offset(x1) == slice_offset(0,c1) + slice(0,c1).offset(i)
    //                    layout.offset(x2) == slice_offset(0,c2) + slice(0,c2).offset(j)
}

/// Every element of the full layout is covered by some mode-0 slice.
///
/// For any x < size(layout), there exist c < shape[0] and i < rest_size such that
/// layout.offset(x) == slice_offset(L, 0, c) + slice_layout(L, 0, c).offset(i).
pub proof fn lemma_partition_coverage(
    layout: &LayoutSpec, x: nat,
)
    requires
        layout.valid(),
        layout.rank() > 0,
        x < shape_size(layout.shape),
    ensures ({
        let m0 = layout.shape[0];
        let c = x % m0;
        let i = x / m0;
        &&& c < m0
        &&& i < shape_size(layout.shape.skip(1))
        &&& layout.offset(x)
            == crate::slice::slice_offset(layout, 0, c)
               + crate::slice::slice_layout(layout, 0, c).offset(i)
    }),
{
    let m0 = layout.shape[0];
    let rest_size = shape_size(layout.shape.skip(1));
    let c = x % m0;
    let i = x / m0;

    assert(shape_size(layout.shape) == m0 * rest_size);

    // c < m0 and i < rest_size
    assert(c < m0) by (nonlinear_arith)
        requires x < m0 * rest_size, m0 > 0, c == x % m0;
    assert(i < rest_size) by (nonlinear_arith)
        requires x < m0 * rest_size, m0 > 0, i == x / m0;

    // x == i * m0 + c
    assert(x == i * m0 + c) by (nonlinear_arith)
        requires c == x % m0, i == x / m0, m0 > 0;

    lemma_slice_offset_reconstruction(layout, c, i);
}

// ══════════════════════════════════════════════════════════════
// TiledCopy pipeline correctness (Phase 3c)
// ══════════════════════════════════════════════════════════════

/// Tiled copy produces an injective layout when all components are injective.
pub proof fn lemma_tiled_copy_injective(
    atom: &LayoutSpec, thr_layout: &LayoutSpec, val_layout: &LayoutSpec,
)
    requires
        tiled_copy_admissible(atom, thr_layout, val_layout),
        atom.is_injective(),
        atom.non_negative_strides(),
        thr_layout.is_injective(),
        val_layout.is_injective(),
        val_layout.non_negative_strides(),
    ensures
        make_tiled_copy(atom, thr_layout, val_layout).is_injective(),
{
    let tv = logical_product(thr_layout, val_layout);

    // TV is injective
    lemma_product_injective(thr_layout, val_layout);

    // TV has non-negative strides (from tiled_copy_admissible)
    assert(tv.non_negative_strides());

    // raked_product(atom, tv) is injective
    lemma_product_valid(thr_layout, val_layout);
    lemma_raked_product_injective(atom, &tv);
}

/// Tiled copy produces a bijective layout when all components are bijective.
pub proof fn lemma_tiled_copy_bijective(
    atom: &LayoutSpec, thr_layout: &LayoutSpec, val_layout: &LayoutSpec,
    m_atom: nat, m_thr: nat, m_val: nat,
)
    requires
        tiled_copy_admissible(atom, thr_layout, val_layout),
        atom.is_injective(),
        atom.non_negative_strides(),
        thr_layout.is_injective(),
        val_layout.is_injective(),
        val_layout.non_negative_strides(),
        atom.is_surjective_upto(m_atom),
        thr_layout.is_surjective_upto(m_thr),
        val_layout.is_surjective_upto(m_val),
        m_thr == thr_layout.cosize_nonneg(),
        m_val == val_layout.cosize_nonneg(),
        m_atom > 0,
        m_thr > 0,
        m_val > 0,
    ensures
        make_tiled_copy(atom, thr_layout, val_layout).is_bijective_upto(m_atom * (m_thr * m_val)),
{
    let tv = logical_product(thr_layout, val_layout);

    // TV is valid with non-negative strides
    lemma_product_valid(thr_layout, val_layout);

    // TV cosize = m_thr * m_val
    lemma_product_cosize(thr_layout, val_layout);

    // TV is bijective onto m_thr * m_val
    lemma_product_bijective(thr_layout, val_layout, m_thr, m_val);

    // raked_product(atom, tv) is bijective onto m_atom * (m_thr * m_val)
    let m_tv = m_thr * m_val;
    assert(m_thr as int * m_val as int > 0) by (nonlinear_arith)
        requires m_thr > 0nat, m_val > 0nat;
    assert(m_tv > 0);
    assert(m_tv == tv.cosize_nonneg());
    lemma_raked_product_bijective(atom, &tv, m_atom, m_tv);
}

/// Tiled copy partitions correctly: different threads get disjoint offset sets
/// from mode-0 slicing of an injective divided layout.
pub proof fn lemma_tiled_copy_partitions_correctly(
    layout: &LayoutSpec, t1: nat, t2: nat, i: nat, j: nat,
)
    requires
        layout.valid(),
        layout.is_injective(),
        layout.rank() > 0,
        t1 < layout.shape[0],
        t2 < layout.shape[0],
        t1 != t2,
        i < shape_size(layout.shape.skip(1)),
        j < shape_size(layout.shape.skip(1)),
    ensures
        slice_offset(layout, 0, t1) + slice_layout(layout, 0, t1).offset(i)
        != slice_offset(layout, 0, t2) + slice_layout(layout, 0, t2).offset(j),
{
    lemma_slice_disjoint(layout, t1, t2, i, j);
}

/// Tiled copy covers all elements: for any element x < size(layout), there exists
/// a thread t and local index i that produces the same offset.
pub proof fn lemma_tiled_copy_covers_all(
    layout: &LayoutSpec, x: nat,
)
    requires
        layout.valid(),
        layout.rank() > 0,
        x < shape_size(layout.shape),
    ensures ({
        let m0 = layout.shape[0];
        let t = x % m0;
        let i = x / m0;
        &&& t < m0
        &&& i < shape_size(layout.shape.skip(1))
        &&& layout.offset(x)
            == slice_offset(layout, 0, t)
               + slice_layout(layout, 0, t).offset(i)
    }),
{
    lemma_partition_coverage(layout, x);
}

// ══════════════════════════════════════════════════════════════
// Copy atom proofs (Phase 4)
// ══════════════════════════════════════════════════════════════

/// A copy atom has contiguous offsets: offset(idx) == idx.
pub proof fn lemma_copy_atom_contiguous(
    atom: &LayoutSpec, access_width: nat, idx: nat,
)
    requires
        copy_atom_valid(atom, access_width),
        idx < access_width,
    ensures
        atom.offset(idx) == idx as int,
{
    // atom = (aw):(1), which is make_column_major(seq![aw])
    assert(atom.shape =~= seq![access_width]);
    assert(atom.stride =~= seq![1int]);

    // make_column_major(seq![aw]).shape =~= seq![aw]
    // make_column_major(seq![aw]).stride =~= seq![1]
    assert(seq![access_width].skip(1) =~= Seq::<nat>::empty());
    assert(column_major_strides(Seq::<nat>::empty()) =~= Seq::<int>::empty());
    assert(scale_strides_spec(Seq::<int>::empty(), access_width as int) =~= Seq::<int>::empty());
    assert(seq![1int].add(Seq::<int>::empty()) =~= seq![1int]);
    assert(make_column_major(seq![access_width]).shape =~= seq![access_width]);
    assert(make_column_major(seq![access_width]).stride =~= seq![1int]);

    // So atom matches make_column_major(seq![aw])
    assert(atom.shape =~= make_column_major(seq![access_width]).shape);
    assert(atom.stride =~= make_column_major(seq![access_width]).stride);

    // offset is determined by shape and stride, extensionally equal layouts have equal offsets
    // delinearize and dot_product depend only on shape/stride contents
    lemma_shape_size_singleton(access_width);
    assert(shape_size(seq![access_width]) == access_width);
    assert(idx < shape_size(seq![access_width]));

    crate::proof::injectivity_lemmas::lemma_column_major_offset_is_identity(
        seq![access_width], idx,
    );
    // make_column_major(seq![aw]).offset(idx) == idx

    // atom.offset(idx) == make_column_major(seq![aw]).offset(idx) since same shape/stride
    assert(atom.offset(idx) == make_column_major(seq![access_width]).offset(idx));
}

/// A copy atom has cosize equal to access_width and non-negative strides.
pub proof fn lemma_copy_atom_cosize(
    atom: &LayoutSpec, access_width: nat,
)
    requires
        copy_atom_valid(atom, access_width),
        access_width > 0,
    ensures
        atom.cosize_nonneg() == access_width,
        atom.non_negative_strides(),
{
    // stride[0] = 1 >= 0
    assert(atom.non_negative_strides());

    // cosize = dot(shape_minus_one, stride) + 1
    // shape_minus_one(seq![aw]) = seq![aw - 1]
    // dot(seq![aw-1], seq![1]) = (aw-1)*1 + dot(empty, empty) = (aw-1) + 0 = aw-1
    // cosize = aw - 1 + 1 = aw
    crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(*atom);

    // Explicitly compute shape_minus_one and dot product
    assert(atom.shape =~= seq![access_width]);
    assert(atom.shape.first() == access_width);
    assert(atom.shape.skip(1) =~= Seq::<nat>::empty());
    assert(shape_minus_one(Seq::<nat>::empty()) =~= Seq::<nat>::empty());
    assert(seq![(access_width - 1) as nat].add(Seq::<nat>::empty())
        =~= seq![(access_width - 1) as nat]);
    let smo = shape_minus_one(atom.shape);
    assert(smo =~= seq![(access_width - 1) as nat]);
    assert(atom.stride =~= seq![1int]);

    // dot_product_nat_int(seq![aw-1], seq![1]) = (aw-1)*1 + dot(empty, empty)
    assert(seq![(access_width - 1) as nat].skip(1) =~= Seq::<nat>::empty());
    assert(seq![1int].skip(1) =~= Seq::<int>::empty());
    assert(dot_product_nat_int(Seq::<nat>::empty(), Seq::<int>::empty()) == 0int);
    assert(dot_product_nat_int(smo, atom.stride) == ((access_width - 1) as int) * 1 + 0);
}

/// A copy atom has size equal to access_width.
pub proof fn lemma_copy_atom_size(
    atom: &LayoutSpec, access_width: nat,
)
    requires
        copy_atom_valid(atom, access_width),
    ensures
        shape_size(atom.shape) == access_width,
{
    // shape_size(seq![aw]) = aw * shape_size(empty) = aw * 1 = aw
    assert(atom.shape =~= seq![access_width]);
    lemma_shape_size_singleton(access_width);
}

/// In a tiled copy, the atom contribution to each element's offset
/// is exactly (x % access_width), scaled by cosize_tv.
pub proof fn lemma_tiled_copy_atom_aligned(
    atom: &LayoutSpec, thr: &LayoutSpec, val: &LayoutSpec,
    access_width: nat, x: nat,
)
    requires
        copy_atom_valid(atom, access_width),
        access_width > 0,
        tiled_copy_admissible(atom, thr, val),
        atom.non_negative_strides(),
        x < shape_size(make_tiled_copy(atom, thr, val).shape),
    ensures ({
        let tv = logical_product(thr, val);
        let sa = shape_size(atom.shape);
        &&& sa == access_width
        &&& atom.offset(x % sa) == (x % access_width) as int
    }),
{
    let tv = logical_product(thr, val);
    lemma_copy_atom_size(atom, access_width);
    let sa = shape_size(atom.shape);
    assert(sa == access_width);

    // x % sa < sa = access_width
    crate::proof::shape_lemmas::lemma_shape_size_positive(atom.shape);
    assert(sa > 0);
    assert(x % sa < sa) by (nonlinear_arith)
        requires sa > 0;

    lemma_copy_atom_contiguous(atom, access_width, x % sa);
}

// ══════════════════════════════════════════════════════════════
// Slice prerequisite proofs for nested tiling (Phase 4b)
// ══════════════════════════════════════════════════════════════

/// Slicing an injective layout at mode 0 preserves injectivity.
pub proof fn lemma_slice_injective_residual(
    layout: &LayoutSpec, c: nat,
)
    requires
        layout.valid(),
        layout.is_injective(),
        layout.rank() > 0,
        c < layout.shape[0],
    ensures
        slice_layout(layout, 0, c).is_injective(),
{
    let sl = slice_layout(layout, 0, c);
    let m0 = layout.shape[0];
    let rest_size = shape_size(layout.shape.skip(1));

    crate::proof::slice_lemmas::lemma_slice_mode0(layout, c);
    assert(sl.shape =~= layout.shape.skip(1));

    // sl is injective: for i != j < rest_size, sl.offset(i) != sl.offset(j)
    assert forall|i: nat, j: nat|
        i < shape_size(sl.shape) && j < shape_size(sl.shape) && i != j
    implies
        sl.offset(i) != sl.offset(j)
    by {
        // Reconstruct full layout indices
        let x1 = i * m0 + c;
        let x2 = j * m0 + c;

        // x1 != x2 since i != j
        assert(x1 != x2) by (nonlinear_arith)
            requires i != j, x1 == i * m0 + c, x2 == j * m0 + c, m0 > 0;

        // Both < shape_size(layout.shape)
        assert(shape_size(layout.shape) == m0 * rest_size);
        assert(x1 < shape_size(layout.shape)) by (nonlinear_arith)
            requires i < rest_size, c < m0, x1 == i * m0 + c,
                shape_size(layout.shape) == m0 * rest_size, m0 > 0;
        assert(x2 < shape_size(layout.shape)) by (nonlinear_arith)
            requires j < rest_size, c < m0, x2 == j * m0 + c,
                shape_size(layout.shape) == m0 * rest_size, m0 > 0;

        // By injectivity: layout.offset(x1) != layout.offset(x2)
        assert(layout.offset(x1) != layout.offset(x2));

        // By reconstruction lemma
        lemma_slice_offset_reconstruction(layout, c, i);
        lemma_slice_offset_reconstruction(layout, c, j);

        // layout.offset(x1) = slice_offset(c) + sl.offset(i)
        // layout.offset(x2) = slice_offset(c) + sl.offset(j)
        // Since layout.offset(x1) != layout.offset(x2),
        // slice_offset(c) + sl.offset(i) != slice_offset(c) + sl.offset(j)
        // => sl.offset(i) != sl.offset(j)
    };
}

/// Slicing a layout with non-negative strides preserves non-negative strides.
pub proof fn lemma_slice_non_negative_strides(
    layout: &LayoutSpec, c: nat,
)
    requires
        layout.valid(),
        layout.non_negative_strides(),
        layout.rank() > 0,
        c < layout.shape[0],
    ensures
        slice_layout(layout, 0, c).non_negative_strides(),
{
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, c);
    let sl = slice_layout(layout, 0, c);
    assert(sl.stride =~= layout.stride.skip(1));
    assert forall|i: int| 0 <= i < sl.stride.len()
    implies #[trigger] sl.stride[i] >= 0
    by {
        assert(sl.stride[i] == layout.stride[i + 1]);
        assert(layout.stride[i + 1] >= 0);
    };
}

/// Slicing at mode 0 gives size = shape_size(shape.skip(1)).
pub proof fn lemma_slice_mode0_size(
    layout: &LayoutSpec, c: nat,
)
    requires
        layout.valid(),
        layout.rank() > 0,
        c < layout.shape[0],
    ensures
        shape_size(slice_layout(layout, 0, c).shape) == shape_size(layout.shape.skip(1)),
{
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, c);
}

// ══════════════════════════════════════════════════════════════
// Nested partition proofs (Phase 4c)
// ══════════════════════════════════════════════════════════════

/// Different outer IDs → disjoint nested offsets.
pub proof fn lemma_nested_partition_disjoint_outer(
    layout: &LayoutSpec,
    t1: nat, t2: nat,
    w1: nat, w2: nat,
    i: nat, j: nat,
)
    requires
        layout.valid(),
        layout.is_injective(),
        layout.rank() >= 2,
        t1 < layout.shape[0],
        t2 < layout.shape[0],
        t1 != t2,
        // r1 = slice(layout, 0, t1) has rank >= 1 since layout.rank() >= 2
        w1 < slice_layout(layout, 0, t1).shape[0],
        w2 < slice_layout(layout, 0, t2).shape[0],
        i < shape_size(slice_layout(&slice_layout(layout, 0, t1), 0, w1).shape),
        j < shape_size(slice_layout(&slice_layout(layout, 0, t2), 0, w2).shape),
    ensures
        nested_local_partition(layout, t1, w1).1
            + nested_local_partition(layout, t1, w1).0.offset(i)
        != nested_local_partition(layout, t2, w2).1
            + nested_local_partition(layout, t2, w2).0.offset(j),
{
    let r1 = slice_layout(layout, 0, t1);
    let r2 = slice_layout(layout, 0, t2);
    let rest_size = shape_size(layout.shape.skip(1));

    crate::proof::slice_lemmas::lemma_slice_valid(layout, 0, t1);
    crate::proof::slice_lemmas::lemma_slice_valid(layout, 0, t2);
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, t1);
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, t2);
    assert(r1.shape =~= layout.shape.skip(1));
    assert(r2.shape =~= layout.shape.skip(1));
    assert(r1.rank() >= 1);

    // Get inner slice info
    let inner1 = slice_layout(&r1, 0, w1);
    let inner2 = slice_layout(&r2, 0, w2);

    crate::proof::slice_lemmas::lemma_slice_valid(&r1, 0, w1);
    crate::proof::slice_lemmas::lemma_slice_valid(&r2, 0, w2);

    // Reconstruct: nested offset = slice_offset(layout, 0, t) + slice_offset(r, 0, w) + inner.offset(k)
    // = slice_offset(layout, 0, t) + r.offset(w * M_1_rest + inner_idx_in_r)
    // We need to show these are within the full layout reconstruction...

    // Strategy: find full layout indices inner_x1, inner_x2 within the respective slices
    // and use lemma_slice_disjoint on the outer level.

    // r1.offset is within rest_size
    // We need an index q1 < rest_size such that r1.offset(q1) = inner offset in r1
    // Use coverage: for any element in r1, there's a (w1, local_i) decomposition
    // But actually we can reconstruct directly:

    // inner1.offset(i) is an offset within r1 after slicing at w1
    // slice_offset(r1, 0, w1) + inner1.offset(i) = r1.offset(some_q1)
    // by lemma_slice_offset_reconstruction on r1

    // r1 has rank >= 1 and shape = layout.shape.skip(1)
    let m1 = r1.shape[0];  // = layout.shape[1]

    // Find q1 = i * m1 + w1, then r1.offset(q1) = slice_offset(r1, 0, w1) + inner1.offset(i)
    crate::proof::slice_lemmas::lemma_slice_mode0(&r1, w1);
    let inner1_size = shape_size(r1.shape.skip(1));
    assert(i < inner1_size);
    lemma_slice_offset_reconstruction(&r1, w1, i);
    let q1 = i * m1 + w1;

    // Same for q2
    let m2 = r2.shape[0];
    assert(m2 == m1);  // same skip(1) shape
    crate::proof::slice_lemmas::lemma_slice_mode0(&r2, w2);
    let inner2_size = shape_size(r2.shape.skip(1));
    assert(j < inner2_size);
    lemma_slice_offset_reconstruction(&r2, w2, j);
    let q2 = j * m1 + w2;

    // q1 < rest_size and q2 < rest_size
    assert(q1 < rest_size) by (nonlinear_arith)
        requires i < inner1_size, w1 < m1, q1 == i * m1 + w1,
            shape_size(r1.shape) == m1 * inner1_size, m1 > 0,
            rest_size == shape_size(r1.shape);
    assert(q2 < rest_size) by (nonlinear_arith)
        requires j < inner2_size, w2 < m1, q2 == j * m1 + w2,
            shape_size(r2.shape) == m1 * inner2_size, m1 > 0,
            rest_size == shape_size(r2.shape);

    // Now use lemma_slice_disjoint on the outer level
    lemma_slice_disjoint(layout, t1, t2, q1, q2);

    // This gives us:
    // slice_offset(layout, 0, t1) + r1.offset(q1) != slice_offset(layout, 0, t2) + r2.offset(q2)
    // And r1.offset(q1) = slice_offset(r1, 0, w1) + inner1.offset(i)
    //     r2.offset(q2) = slice_offset(r2, 0, w2) + inner2.offset(j)
    // So: (off_t1 + off_w1 + inner1.offset(i)) != (off_t2 + off_w2 + inner2.offset(j))
}

/// Same outer ID, different inner IDs → disjoint nested offsets.
pub proof fn lemma_nested_partition_disjoint_inner(
    layout: &LayoutSpec,
    t: nat,
    w1: nat, w2: nat,
    i: nat, j: nat,
)
    requires
        layout.valid(),
        layout.is_injective(),
        layout.rank() >= 2,
        t < layout.shape[0],
        w1 < slice_layout(layout, 0, t).shape[0],
        w2 < slice_layout(layout, 0, t).shape[0],
        w1 != w2,
        i < shape_size(slice_layout(&slice_layout(layout, 0, t), 0, w1).shape),
        j < shape_size(slice_layout(&slice_layout(layout, 0, t), 0, w2).shape),
    ensures
        nested_local_partition(layout, t, w1).1
            + nested_local_partition(layout, t, w1).0.offset(i)
        != nested_local_partition(layout, t, w2).1
            + nested_local_partition(layout, t, w2).0.offset(j),
{
    let r = slice_layout(layout, 0, t);
    crate::proof::slice_lemmas::lemma_slice_valid(layout, 0, t);
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, t);
    assert(r.shape =~= layout.shape.skip(1));
    assert(r.rank() >= 1);

    // r is injective (by slice preserving injectivity)
    lemma_slice_injective_residual(layout, t);
    assert(r.is_injective());

    // Use slice_disjoint on r with w1 != w2
    lemma_slice_disjoint(&r, w1, w2, i, j);

    // This gives:
    // slice_offset(r, 0, w1) + inner1.offset(i) != slice_offset(r, 0, w2) + inner2.offset(j)
    // Adding slice_offset(layout, 0, t) to both sides preserves inequality:
    // (off_t + off_w1 + inner1.offset(i)) != (off_t + off_w2 + inner2.offset(j))
    let off_t = slice_offset(layout, 0, t);
    let off_w1 = slice_offset(&r, 0, w1);
    let off_w2 = slice_offset(&r, 0, w2);
    let inner1 = slice_layout(&r, 0, w1);
    let inner2 = slice_layout(&r, 0, w2);
    assert(off_w1 + inner1.offset(i) != off_w2 + inner2.offset(j));
    // off_t + (off_w1 + inner1.offset(i)) != off_t + (off_w2 + inner2.offset(j))
}

/// Full nested partition coverage: every element has a (t, w, k) decomposition.
pub proof fn lemma_nested_partition_coverage(
    layout: &LayoutSpec, x: nat,
)
    requires
        layout.valid(),
        layout.rank() >= 2,
        x < shape_size(layout.shape),
    ensures ({
        let m0 = layout.shape[0];
        let t = x % m0;
        let q = x / m0;
        let r = slice_layout(layout, 0, t);
        let m1 = r.shape[0];
        let w = q % m1;
        let k = q / m1;
        &&& t < m0
        &&& q < shape_size(layout.shape.skip(1))
        &&& w < r.shape[0]
        &&& k < shape_size(r.shape.skip(1))
        &&& layout.offset(x)
            == nested_local_partition(layout, t, w).1
               + nested_local_partition(layout, t, w).0.offset(k)
    }),
{
    // First level: decompose x into (t, q)
    lemma_partition_coverage(layout, x);
    let m0 = layout.shape[0];
    let t = x % m0;
    let q = x / m0;
    let r = slice_layout(layout, 0, t);

    // r is valid with rank >= 1
    crate::proof::slice_lemmas::lemma_slice_valid(layout, 0, t);
    crate::proof::slice_lemmas::lemma_slice_mode0(layout, t);
    assert(r.shape =~= layout.shape.skip(1));
    assert(r.rank() >= 1);

    // Second level: decompose q within r
    let rest_size = shape_size(layout.shape.skip(1));
    assert(q < rest_size);
    assert(q < shape_size(r.shape));
    lemma_partition_coverage(&r, q);

    // This gives (w, k) where w = q % r.shape[0], k = q / r.shape[0]
    // and r.offset(q) = slice_offset(r, 0, w) + slice_layout(r, 0, w).offset(k)

    // From first level: layout.offset(x) = slice_offset(layout, 0, t) + r.offset(q)
    // From second level: r.offset(q) = slice_offset(r, 0, w) + inner.offset(k)
    // Combined: layout.offset(x) = off_t + off_w + inner.offset(k) = nested_local_partition.1 + inner.offset(k)
}

/// Full disjointness: if (t1, w1) != (t2, w2), nested offsets are distinct.
pub proof fn lemma_nested_partition_full_disjoint(
    layout: &LayoutSpec,
    t1: nat, w1: nat, i: nat,
    t2: nat, w2: nat, j: nat,
)
    requires
        layout.valid(),
        layout.is_injective(),
        layout.rank() >= 2,
        t1 < layout.shape[0],
        t2 < layout.shape[0],
        w1 < slice_layout(layout, 0, t1).shape[0],
        w2 < slice_layout(layout, 0, t2).shape[0],
        i < shape_size(slice_layout(&slice_layout(layout, 0, t1), 0, w1).shape),
        j < shape_size(slice_layout(&slice_layout(layout, 0, t2), 0, w2).shape),
        t1 != t2 || w1 != w2,
    ensures
        nested_local_partition(layout, t1, w1).1
            + nested_local_partition(layout, t1, w1).0.offset(i)
        != nested_local_partition(layout, t2, w2).1
            + nested_local_partition(layout, t2, w2).0.offset(j),
{
    if t1 != t2 {
        lemma_nested_partition_disjoint_outer(layout, t1, t2, w1, w2, i, j);
    } else {
        // t1 == t2 and w1 != w2
        lemma_nested_partition_disjoint_inner(layout, t1, w1, w2, i, j);
    }
}

} // verus!
