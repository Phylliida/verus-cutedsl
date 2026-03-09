use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::divide::*;
use crate::product::*;
use crate::complement::*;
use crate::composition::*;
use crate::tiling::*;
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

} // verus!
