use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::divide::*;
use crate::product::*;
use crate::complement::*;
use crate::composition::*;
use crate::tiling::*;
use crate::predication::*;
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

} // verus!
