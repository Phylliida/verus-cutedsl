use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::divide::*;
use crate::product::*;
use crate::tiling::*;
use super::*;
use super::layout::RuntimeLayout;

verus! {

/// Runtime divided layout: a runtime layout + tile_rank metadata.
pub struct RuntimeDividedLayout {
    pub layout: RuntimeLayout,
    pub tile_rank: usize,
}

impl RuntimeDividedLayout {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.layout.wf_spec()
        &&& self.tile_rank as nat <= self.layout@.shape.len()
    }

    pub open spec fn view_divided(&self) -> DividedLayout {
        DividedLayout {
            layout: self.layout@,
            tile_rank: self.tile_rank as nat,
        }
    }
}

/// Zipped divide at runtime: computes logical_divide(A, B) and tracks tile_rank.
pub fn zipped_divide_exec(
    a: &RuntimeLayout,
    b: &RuntimeLayout,
    complement_result: &RuntimeLayout,
) -> (result: RuntimeDividedLayout)
    requires
        a.wf_spec(),
        b.wf_spec(),
        complement_result.wf_spec(),
        divide_admissible(&a@, &b@),
        complement_result@ == crate::complement::complement(&b@, shape_size(a@.shape)),
        a@.shape.len() > 0,
        ({
            let zipped_stride = b@.stride.add(complement_result@.stride);
            forall|i: int| 0 <= i < zipped_stride.len() ==>
                #[trigger] zipped_stride[i] >= 0 &&
                zipped_stride[i] * a@.stride.first() >= i64::MIN as int &&
                zipped_stride[i] * a@.stride.first() <= i64::MAX as int
        }),
        shape_size(logical_divide(&a@, &b@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result.view_divided() == zipped_divide(&a@, &b@),
        result.tile_rank == b.shape.len(),
{
    let mut zipped_shape: Vec<u64> = Vec::new();
    let mut zipped_stride: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < b.shape.len()
        invariant
            0 <= i <= b.shape.len(),
            zipped_shape@.len() == i as int,
            zipped_stride@.len() == i as int,
            b.wf_spec(),
            forall|j: int| 0 <= j < i as int ==>
                zipped_shape@[j] == b.shape@[j] && zipped_stride@[j] == b.stride@[j],
        decreases b.shape.len() - i,
    {
        zipped_shape.push(b.shape[i]);
        zipped_stride.push(b.stride[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < complement_result.shape.len()
        invariant
            0 <= j <= complement_result.shape.len(),
            zipped_shape@.len() == b.shape@.len() + j as int,
            zipped_stride@.len() == b.stride@.len() + j as int,
            b.wf_spec(),
            complement_result.wf_spec(),
            forall|k: int| 0 <= k < b.shape@.len() as int ==>
                zipped_shape@[k] == b.shape@[k] && zipped_stride@[k] == b.stride@[k],
            forall|k: int| 0 <= k < j as int ==>
                zipped_shape@[b.shape@.len() as int + k] == complement_result.shape@[k] &&
                zipped_stride@[b.stride@.len() as int + k] == complement_result.stride@[k],
        decreases complement_result.shape.len() - j,
    {
        zipped_shape.push(complement_result.shape[j]);
        zipped_stride.push(complement_result.stride[j]);
        j = j + 1;
    }

    proof {
        let b_spec = b@;
        let c_spec = complement_result@;
        let zipped_spec = LayoutSpec {
            shape: b_spec.shape.add(c_spec.shape),
            stride: b_spec.stride.add(c_spec.stride),
        };

        // Runtime→spec bridge
        assert(crate::runtime::shape_to_nat_seq(zipped_shape@) =~= zipped_spec.shape);
        assert(crate::runtime::strides_to_int_seq(zipped_stride@) =~= zipped_spec.stride);

        // shape_valid_u64: all entries > 0
        assert forall|k: int| 0 <= k < zipped_shape@.len()
        implies #[trigger] zipped_shape@[k] > 0u64
        by {
            if k < b.shape@.len() as int {
                assert(zipped_shape@[k] == b.shape@[k]);
                assert(b_spec.shape[k] > 0nat);
            } else {
                let k2 = k - b.shape@.len() as int;
                assert(zipped_shape@[k] == complement_result.shape@[k2]);
                assert(c_spec.shape[k2] > 0nat);
            }
        };

        // Zipped size fits u64: logical_divide.shape =~= zipped_spec.shape
        crate::proof::tiling_lemmas::lemma_zipped_valid(&a@, &b@);
        crate::proof::composition_lemmas::lemma_compose_shape(a@, zipped_spec);
        assert(logical_divide(&a@, &b@).shape =~= zipped_spec.shape);
    }

    let zipped = RuntimeLayout::new(zipped_shape, zipped_stride);

    proof {
        let b_spec = b@;
        let c_spec = complement_result@;
        let zipped_spec = LayoutSpec {
            shape: b_spec.shape.add(c_spec.shape),
            stride: b_spec.stride.add(c_spec.stride),
        };
        assert(zipped@ == zipped_spec);

        // compose_exec: non-negative strides
        assert forall|k: int| 0 <= k < zipped@.stride.len()
        implies #[trigger] zipped@.stride[k] >= 0
        by {
            assert(zipped_spec.stride[k] >= 0);
        };

        // compose_exec: stride products fit i64
        assert forall|k: int| 0 <= k < zipped@.shape.len()
        implies (#[trigger] zipped@.stride[k]) * a@.stride.first() >= i64::MIN as int
            && zipped@.stride[k] * a@.stride.first() <= i64::MAX as int
        by {
            assert(zipped_spec.stride[k] * a@.stride.first() >= i64::MIN as int);
            assert(zipped_spec.stride[k] * a@.stride.first() <= i64::MAX as int);
        };

        // compose_exec: compose size fits u64
        crate::proof::composition_lemmas::lemma_compose_shape(a@, zipped@);
    }

    let result_layout = super::ops::compose_exec(a, &zipped);

    proof {
        let b_spec = b@;
        let c_spec = complement_result@;
        let zipped_spec = LayoutSpec {
            shape: b_spec.shape.add(c_spec.shape),
            stride: b_spec.stride.add(c_spec.stride),
        };
        assert(zipped@ == zipped_spec);

        // tile_rank <= layout shape len
        crate::proof::divide_lemmas::lemma_divide_rank(&a@, &b@);
    }

    RuntimeDividedLayout {
        layout: result_layout,
        tile_rank: b.shape.len(),
    }
}

/// Extract tile_rank from a RuntimeDividedLayout.
pub fn tile_rank(d: &RuntimeDividedLayout) -> (result: usize)
    requires d.wf_spec(),
    ensures result as nat == d.view_divided().tile_rank,
{
    d.tile_rank
}

/// Local partition at runtime: extract one thread's portion via slice.
/// Returns (residual_layout, base_offset).
pub fn local_partition_exec(
    tensor: &RuntimeDividedLayout,
    thread_id: u64,
) -> (result: (RuntimeLayout, i64))
    requires
        tensor.wf_spec(),
        tensor.layout@.rank() > 0,
        (thread_id as nat) < tensor.layout@.shape[0],
        // Offset fits i64
        (thread_id as int) * tensor.layout@.stride[0] >= i64::MIN as int,
        (thread_id as int) * tensor.layout@.stride[0] <= i64::MAX as int,
        // Result size fits u64
        shape_size(crate::slice::slice_layout(&tensor.layout@, 0, thread_id as nat).shape) <= u64::MAX as nat,
    ensures ({
        let (rl, off) = result;
        let (spec_rl, spec_off) = local_partition(&tensor.view_divided(), &tensor.layout@, thread_id as nat);
        &&& rl.wf_spec()
        &&& rl@ == spec_rl
        &&& off as int == spec_off
    }),
{
    super::ops::slice_exec(&tensor.layout, 0, thread_id)
}

/// Make tiled copy at runtime: raked_product(atom, logical_product(thr, val)).
pub fn make_tiled_copy_exec(
    atom: &RuntimeLayout,
    thr_layout: &RuntimeLayout,
    val_layout: &RuntimeLayout,
    cosize_thr: u64,
) -> (result: RuntimeLayout)
    requires
        atom.wf_spec(),
        thr_layout.wf_spec(),
        val_layout.wf_spec(),
        tiled_copy_admissible(&atom@, &thr_layout@, &val_layout@),
        cosize_thr as nat == thr_layout@.cosize_nonneg(),
        // logical_product overflow bounds
        forall|i: int| 0 <= i < val_layout@.stride.len() ==>
            #[trigger] val_layout@.stride[i] * (cosize_thr as int) >= i64::MIN as int &&
            val_layout@.stride[i] * (cosize_thr as int) <= i64::MAX as int,
        shape_size(logical_product(&thr_layout@, &val_layout@).shape) <= u64::MAX as nat,
        // TV cosize bounds for raked_product
        logical_product(&thr_layout@, &val_layout@).cosize_nonneg() <= u64::MAX as nat,
        forall|i: int| 0 <= i < logical_product(&thr_layout@, &val_layout@).shape.len() ==>
            ((#[trigger] logical_product(&thr_layout@, &val_layout@).shape[i] - 1) as int)
            * logical_product(&thr_layout@, &val_layout@).stride[i] <= u64::MAX as int,
        // raked_product overflow bounds
        forall|i: int| 0 <= i < atom@.stride.len() ==>
            #[trigger] atom@.stride[i] * (logical_product(&thr_layout@, &val_layout@).cosize_nonneg() as int) >= i64::MIN as int &&
            atom@.stride[i] * (logical_product(&thr_layout@, &val_layout@).cosize_nonneg() as int) <= i64::MAX as int,
        shape_size(make_tiled_copy(&atom@, &thr_layout@, &val_layout@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == make_tiled_copy(&atom@, &thr_layout@, &val_layout@),
{
    let tv = super::ops::logical_product_exec(thr_layout, val_layout, cosize_thr);

    proof {
        assert(tv@ == logical_product(&thr_layout@, &val_layout@));
        // tv has non-negative strides from tiled_copy_admissible
        assert(tv@.non_negative_strides());
        assert(tv@.shape.len() > 0);
    }

    let cosize_tv = tv.cosize();

    proof {
        assert(cosize_tv as nat == tv@.cosize_nonneg());
        // Bridge stride overflow for raked_product
        assert forall|i: int| 0 <= i < atom@.stride.len()
        implies #[trigger] atom@.stride[i] * (cosize_tv as int) >= i64::MIN as int
            && atom@.stride[i] * (cosize_tv as int) <= i64::MAX as int
        by {
            assert(atom@.stride[i] * (logical_product(&thr_layout@, &val_layout@).cosize_nonneg() as int) >= i64::MIN as int);
            assert(atom@.stride[i] * (logical_product(&thr_layout@, &val_layout@).cosize_nonneg() as int) <= i64::MAX as int);
        };
    }

    super::ops::raked_product_exec(atom, &tv, cosize_tv)
}

/// Extract tile shape from a RuntimeDividedLayout.
pub fn tile_shape_exec(d: &RuntimeDividedLayout) -> (result: Vec<u64>)
    requires
        d.wf_spec(),
    ensures
        shape_to_nat_seq(result@) =~= tile_shape(&d.view_divided()),
        shape_valid_u64(result@),
{
    let mut result: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < d.tile_rank
        invariant
            0 <= i <= d.tile_rank,
            d.wf_spec(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result@[j] == d.layout.shape@[j],
        decreases d.tile_rank - i,
    {
        result.push(d.layout.shape[i]);
        i = i + 1;
    }
    proof {
        assert(shape_to_nat_seq(result@) =~= tile_shape(&d.view_divided())) by {
            assert(result@.len() == d.tile_rank as int);
            assert forall|j: int| 0 <= j < result@.len() implies
                shape_to_nat_seq(result@)[j] == d.view_divided().layout.shape.take(d.tile_rank as int)[j]
            by {
                assert(result@[j] == d.layout.shape@[j]);
            };
        };
        assert forall|j: int| 0 <= j < result@.len() implies #[trigger] result@[j] > 0u64
        by {
            assert(result@[j] == d.layout.shape@[j]);
            assert(d.layout@.shape[j] > 0nat);
        };
    }
    result
}

/// Extract rest shape from a RuntimeDividedLayout.
pub fn rest_shape_exec(d: &RuntimeDividedLayout) -> (result: Vec<u64>)
    requires
        d.wf_spec(),
    ensures
        shape_to_nat_seq(result@) =~= rest_shape(&d.view_divided()),
        shape_valid_u64(result@),
{
    let mut result: Vec<u64> = Vec::new();
    let mut i: usize = d.tile_rank;
    while i < d.layout.shape.len()
        invariant
            d.tile_rank <= i <= d.layout.shape.len(),
            d.wf_spec(),
            result@.len() == (i - d.tile_rank) as int,
            forall|j: int| 0 <= j < (i - d.tile_rank) as int ==>
                #[trigger] result@[j] == d.layout.shape@[(d.tile_rank as int) + j],
        decreases d.layout.shape.len() - i,
    {
        result.push(d.layout.shape[i]);
        i = i + 1;
    }
    proof {
        assert(shape_to_nat_seq(result@) =~= rest_shape(&d.view_divided())) by {
            assert(result@.len() == (d.layout.shape@.len() - d.tile_rank) as int);
            assert forall|j: int| 0 <= j < result@.len() implies
                shape_to_nat_seq(result@)[j] == d.view_divided().layout.shape.skip(d.tile_rank as int)[j]
            by {
                assert(result@[j] == d.layout.shape@[(d.tile_rank as int) + j]);
            };
        };
        assert forall|j: int| 0 <= j < result@.len() implies #[trigger] result@[j] > 0u64
        by {
            assert(result@[j] == d.layout.shape@[(d.tile_rank as int) + j]);
            assert(d.layout@.shape[(d.tile_rank as int) + j] > 0nat);
        };
    }
    result
}

/// Compute tile size (product of tile shape elements).
pub fn tile_size_exec(d: &RuntimeDividedLayout) -> (result: u64)
    requires
        d.wf_spec(),
        tile_size(&d.view_divided()) <= u64::MAX as nat,
    ensures
        result as nat == tile_size(&d.view_divided()),
{
    let ts = tile_shape_exec(d);
    super::shape_helpers::shape_size_exec(&ts)
}

/// Compute number of tiles (product of rest shape elements).
pub fn num_tiles_exec(d: &RuntimeDividedLayout) -> (result: u64)
    requires
        d.wf_spec(),
        num_tiles_divided(&d.view_divided()) <= u64::MAX as nat,
    ensures
        result as nat == num_tiles_divided(&d.view_divided()),
{
    let rs = rest_shape_exec(d);
    super::shape_helpers::shape_size_exec(&rs)
}

} // verus!
