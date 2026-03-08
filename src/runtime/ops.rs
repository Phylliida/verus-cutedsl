use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::composition::*;
use crate::complement::*;
use crate::product::*;
use crate::coalesce::*;
use super::*;
use super::layout::RuntimeLayout;

verus! {

/// Compose A with single-mode B at runtime.
pub fn compose_single_mode_exec(a: &RuntimeLayout, b_shape: u64, b_stride: u64) -> (result: RuntimeLayout)
    requires
        a.wf_spec(),
        b_shape > 0,
        a@.shape.len() > 0,
        (b_stride as int) * a@.stride.first() >= i64::MIN as int,
        (b_stride as int) * a@.stride.first() <= i64::MAX as int,
        shape_size(compose_single_mode(a@, b_shape as nat, b_stride as nat).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == compose_single_mode(a@, b_shape as nat, b_stride as nat),
{
    let new_stride: i64 = if b_stride == 1 && b_shape <= a.shape[0] {
        a.stride[0]
    } else {
        // Use i128 to avoid intermediate overflow when b_stride > i64::MAX
        ((b_stride as i128) * (a.stride[0] as i128)) as i64
    };
    let mut shape_vec: Vec<u64> = Vec::new();
    shape_vec.push(b_shape);
    let mut stride_vec: Vec<i64> = Vec::new();
    stride_vec.push(new_stride);

    proof {
        let spec_result = compose_single_mode(a@, b_shape as nat, b_stride as nat);
        // Bridge exec fields to spec
        assert(a@.shape == shape_to_nat_seq(a.shape@));
        assert(a@.stride == strides_to_int_seq(a.stride@));

        // Shape extensional equality
        assert(shape_to_nat_seq(shape_vec@) =~= spec_result.shape);

        // Stride extensional equality
        assert(strides_to_int_seq(stride_vec@) =~= spec_result.stride);

        // Valid
        assert(spec_result.shape[0] > 0);
    }

    RuntimeLayout {
        shape: shape_vec,
        stride: stride_vec,
        model: Ghost(compose_single_mode(
            *a.model.borrow(),
            b_shape as nat,
            b_stride as nat,
        )),
    }
}

/// Compose A with multi-mode B at runtime.
pub fn compose_exec(a: &RuntimeLayout, b: &RuntimeLayout) -> (result: RuntimeLayout)
    requires
        a.wf_spec(),
        b.wf_spec(),
        a@.shape.len() > 0,
        forall|i: int| 0 <= i < b@.stride.len() ==> #[trigger] b@.stride[i] >= 0,
        forall|i: int| 0 <= i < b@.shape.len() ==>
            (#[trigger] b@.stride[i]) * a@.stride.first() >= i64::MIN as int &&
            b@.stride[i] * a@.stride.first() <= i64::MAX as int,
        shape_size(compose(a@, b@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == compose(a@, b@),
{
    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    proof {
        crate::proof::divide_lemmas::lemma_compose_rank(a@, b@);
    }

    while i < b.shape.len()
        invariant
            0 <= i <= b.shape.len(),
            a.wf_spec(),
            b.wf_spec(),
            a@.shape.len() > 0,
            result_shape@.len() == i,
            result_stride@.len() == i,
            compose(a@, b@).shape.len() == b@.shape.len(),
            compose(a@, b@).stride.len() == b@.shape.len(),
            forall|j: int| 0 <= j < b@.stride.len() ==> #[trigger] b@.stride[j] >= 0,
            forall|j: int| 0 <= j < b@.shape.len() ==>
                (#[trigger] b@.stride[j]) * a@.stride.first() >= i64::MIN as int &&
                b@.stride[j] * a@.stride.first() <= i64::MAX as int,
            shape_size(compose(a@, b@).shape) <= u64::MAX as nat,
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_shape@[j] as nat == compose(a@, b@).shape[j],
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_stride@[j] as int == compose(a@, b@).stride[j],
        decreases b.shape.len() - i,
    {
        proof {
            crate::proof::composition_lemmas::lemma_compose_element(a@, b@, i as int);
        }

        let b_stride_i: u64 = b.stride[i] as u64;

        let new_stride: i64 = if b_stride_i == 1 && b.shape[i] <= a.shape[0] {
            a.stride[0]
        } else {
            ((b_stride_i as i128) * (a.stride[0] as i128)) as i64
        };

        proof {
            // Bridge: compose_single_mode(a@, b@.shape[i], b@.stride[i] as nat)
            // has stride.first() == new_stride as int
            let csm = compose_single_mode(a@, b@.shape[i as int], b@.stride[i as int] as nat);
            assert(a@.shape == shape_to_nat_seq(a.shape@));
            assert(a@.stride == strides_to_int_seq(a.stride@));
            assert(b@.shape == shape_to_nat_seq(b.shape@));
            assert(b@.stride == strides_to_int_seq(b.stride@));
            // b_stride_i as nat == b@.stride[i] as nat == b@.stride[i] (since >= 0)
            assert(new_stride as int == csm.stride.first());
            assert(compose(a@, b@).stride[i as int] == csm.stride.first());
            assert(compose(a@, b@).shape[i as int] == b@.shape[i as int]);
            assert(b.shape@[i as int] as nat == b@.shape[i as int]);
        }

        result_shape.push(b.shape[i]);
        result_stride.push(new_stride);

        i = i + 1;
    }

    proof {
        let spec_result = compose(a@, b@);
        assert(shape_to_nat_seq(result_shape@) =~= spec_result.shape);
        assert(strides_to_int_seq(result_stride@) =~= spec_result.stride);
        // Valid
        assert(spec_result.valid()) by {
            assert forall|j: int| 0 <= j < spec_result.shape.len()
                implies #[trigger] spec_result.shape[j] > 0
            by {
                crate::proof::composition_lemmas::lemma_compose_element(a@, b@, j);
            };
        };
    }

    RuntimeLayout {
        shape: result_shape,
        stride: result_stride,
        model: Ghost(compose(*a.model.borrow(), *b.model.borrow())),
    }
}

/// Complement of layout A with respect to target size M at runtime.
pub fn complement_exec(a: &RuntimeLayout, m: u64) -> (result: RuntimeLayout)
    requires
        a.wf_spec(),
        complement_admissible(&a@, m as nat),
        shape_size(complement(&a@, m as nat).shape) <= u64::MAX as nat,
        forall|i: int| 0 <= i < a@.shape.len() ==>
            (a@.shape[i] as int) * a@.stride[i] > 0 &&
            (a@.shape[i] as int) * a@.stride[i] <= i64::MAX as int,
    ensures
        result.wf_spec(),
        result@ == complement(&a@, m as nat),
{
    let k = a.shape.len();
    let mut comp_shape: Vec<u64> = Vec::new();
    let mut comp_stride: Vec<i64> = Vec::new();

    proof {
        assert(a@.shape == shape_to_nat_seq(a.shape@));
        assert(a@.stride == strides_to_int_seq(a.stride@));
    }

    // Entry 0: shape = d_0, stride = 1
    comp_shape.push(a.stride[0] as u64);
    comp_stride.push(1);

    proof {
        assert(comp_shape@[0] as nat == complement_shape(&a@, m as nat)[0]);
        assert(comp_stride@[0] as int == complement_stride(&a@)[0]);
    }

    // Entries 1..k-1
    let mut i: usize = 1;
    while i < k
        invariant
            1 <= i <= k,
            k == a.shape.len(),
            a.wf_spec(),
            complement_admissible(&a@, m as nat),
            comp_shape@.len() == i,
            comp_stride@.len() == i,
            a@.shape == shape_to_nat_seq(a.shape@),
            a@.stride == strides_to_int_seq(a.stride@),
            forall|j: int| 0 <= j < a@.shape.len() ==>
                (a@.shape[j] as int) * a@.stride[j] > 0 &&
                (a@.shape[j] as int) * a@.stride[j] <= i64::MAX as int,
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] comp_shape@[j] as nat == complement_shape(&a@, m as nat)[j],
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] comp_stride@[j] as int == complement_stride(&a@)[j],
        decreases k - i,
    {
        proof {
            let ii = i as int;
            assert((a@.shape[ii - 1] as int) * a@.stride[ii - 1] > 0);
            assert((a@.shape[ii - 1] as int) * a@.stride[ii - 1] <= i64::MAX as int);
            assert(a@.stride[ii - 1] >= a@.stride[0]);
            assert(a@.stride[0] > 0);
            assert(a@.stride[ii - 1] >= 1int);
            // shape[i-1] fits in i64
            assert(a@.shape[ii - 1] <= i64::MAX as nat) by (nonlinear_arith)
                requires a@.shape[ii - 1] >= 1nat, a@.stride[ii - 1] >= 1int,
                    (a@.shape[ii - 1] as int) * a@.stride[ii - 1] <= i64::MAX as int,
            {};
            assert(a.shape@[ii - 1] as nat == a@.shape[ii - 1]);
        }

        let stride_prod: i64 = (a.shape[i - 1] as i64) * a.stride[i - 1];

        proof {
            let ii = i as int;
            assert(stride_prod as int == (a.shape@[ii - 1] as int) * (a.stride@[ii - 1] as int));
            assert(stride_prod as int == (a@.shape[ii - 1] as int) * a@.stride[ii - 1]);
            assert(stride_prod > 0);
            assert(stride_prod as int == stride_product(&a@, ii - 1));
            assert(a@.stride[ii] >= a@.stride[0]);
            assert(a@.stride[ii] > 0);
        }

        comp_shape.push((a.stride[i] / stride_prod) as u64);
        comp_stride.push(stride_prod);

        proof {
            let ii = i as int;
            assert(comp_shape@[ii] as nat == complement_shape(&a@, m as nat)[ii]) by {
                assert(comp_shape@[ii] == (a.stride@[ii] / stride_prod) as u64);
                assert(a.stride@[ii] as int == a@.stride[ii]);
                assert(stride_prod as int == stride_product(&a@, ii - 1));
            };
            assert(comp_stride@[ii] as int == complement_stride(&a@)[ii]) by {
                assert(comp_stride@[ii] == stride_prod);
                assert(stride_prod as int == stride_product(&a@, ii - 1));
            };
        }

        i = i + 1;
    }

    // Entry k
    proof {
        let ki = (k - 1) as int;
        assert((a@.shape[ki] as int) * a@.stride[ki] > 0);
        assert((a@.shape[ki] as int) * a@.stride[ki] <= i64::MAX as int);
        assert(a@.stride[ki] >= a@.stride[0]);
        assert(a@.stride[0] > 0);
        assert(a@.stride[ki] >= 1int);
        assert(a@.shape[ki] <= i64::MAX as nat) by (nonlinear_arith)
            requires a@.shape[ki] >= 1nat, a@.stride[ki] >= 1int,
                (a@.shape[ki] as int) * a@.stride[ki] <= i64::MAX as int,
        {};
        assert(a.shape@[ki] as nat == a@.shape[ki]);
    }
    let last_stride_prod: i64 = (a.shape[k - 1] as i64) * a.stride[k - 1];
    proof {
        let ki = (k - 1) as int;
        assert(last_stride_prod as int == (a@.shape[ki] as int) * a@.stride[ki]);
        assert(last_stride_prod > 0);
    }
    // Use i128 to avoid overflow when m > i64::MAX
    let last_shape: u64 = ((m as i128) / (last_stride_prod as i128)) as u64;
    comp_shape.push(last_shape);
    comp_stride.push(last_stride_prod);

    proof {
        let ki = k as int;
        assert(last_stride_prod as int == stride_product(&a@, ki - 1));
        assert(comp_shape@[ki] as nat == complement_shape(&a@, m as nat)[ki]) by {
            assert(last_shape as nat == ((m as int) / stride_product(&a@, ki - 1)) as nat);
        };
        assert(comp_stride@[ki] as int == complement_stride(&a@)[ki]);

        // Final: extensional equality
        let spec_comp = complement(&a@, m as nat);
        crate::proof::complement_lemmas::lemma_complement_rank(&a@, m as nat);
        assert(shape_to_nat_seq(comp_shape@) =~= spec_comp.shape) by {
            assert(comp_shape@.len() == spec_comp.shape.len());
        };
        assert(strides_to_int_seq(comp_stride@) =~= spec_comp.stride) by {
            assert(comp_stride@.len() == spec_comp.stride.len());
        };

        // Valid
        crate::proof::complement_lemmas::lemma_complement_shape_valid(&a@, m as nat);
    }

    RuntimeLayout {
        shape: comp_shape,
        stride: comp_stride,
        model: Ghost(complement(&*a.model.borrow(), m as nat)),
    }
}

/// Logical product at runtime: tile A's codomain with B.
pub fn logical_product_exec(a: &RuntimeLayout, b: &RuntimeLayout, cosize_a: u64) -> (result: RuntimeLayout)
    requires
        a.wf_spec(),
        b.wf_spec(),
        a@.non_negative_strides(),
        a@.shape.len() > 0,
        cosize_a as nat == a@.cosize_nonneg(),
        forall|i: int| 0 <= i < b@.stride.len() ==>
            #[trigger] b@.stride[i] * (cosize_a as int) >= i64::MIN as int &&
            b@.stride[i] * (cosize_a as int) <= i64::MAX as int,
        shape_size(logical_product(&a@, &b@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == logical_product(&a@, &b@),
{
    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();

    proof {
        assert(a@.shape == shape_to_nat_seq(a.shape@));
        assert(a@.stride == strides_to_int_seq(a.stride@));
        assert(b@.shape == shape_to_nat_seq(b.shape@));
        assert(b@.stride == strides_to_int_seq(b.stride@));
    }

    // Copy A's modes
    let mut i: usize = 0;
    while i < a.shape.len()
        invariant
            0 <= i <= a.shape.len(),
            a.wf_spec(), b.wf_spec(),
            result_shape@.len() == i,
            result_stride@.len() == i,
            a@.shape == shape_to_nat_seq(a.shape@),
            a@.stride == strides_to_int_seq(a.stride@),
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_shape@[j] as nat == a@.shape[j],
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_stride@[j] as int == a@.stride[j],
        decreases a.shape.len() - i,
    {
        result_shape.push(a.shape[i]);
        result_stride.push(a.stride[i]);
        i = i + 1;
    }

    // Append B's modes with scaled strides
    let mut j: usize = 0;
    while j < b.shape.len()
        invariant
            0 <= j <= b.shape.len(),
            a.wf_spec(), b.wf_spec(),
            result_shape@.len() == a.shape@.len() + j,
            result_stride@.len() == a.stride@.len() + j,
            a@.shape == shape_to_nat_seq(a.shape@),
            a@.stride == strides_to_int_seq(a.stride@),
            b@.shape == shape_to_nat_seq(b.shape@),
            b@.stride == strides_to_int_seq(b.stride@),
            cosize_a as nat == a@.cosize_nonneg(),
            forall|k: int| 0 <= k < b@.stride.len() ==>
                #[trigger] b@.stride[k] * (cosize_a as int) >= i64::MIN as int &&
                b@.stride[k] * (cosize_a as int) <= i64::MAX as int,
            forall|k: int| 0 <= k < a.shape@.len() as int ==>
                #[trigger] result_shape@[k] as nat == a@.shape[k],
            forall|k: int| 0 <= k < a.stride@.len() as int ==>
                #[trigger] result_stride@[k] as int == a@.stride[k],
            forall|k: int| 0 <= k < j as int ==>
                #[trigger] result_shape@[(a.shape@.len() + k) as int] as nat == b@.shape[k],
            forall|k: int| 0 <= k < j as int ==>
                #[trigger] result_stride@[(a.stride@.len() + k) as int] as int ==
                    b@.stride[k] * (cosize_a as int),
        decreases b.shape.len() - j,
    {
        result_shape.push(b.shape[j]);
        proof {
            // Product fits in i64 from requires
            assert(b@.stride[j as int] * (cosize_a as int) >= i64::MIN as int);
            assert(b@.stride[j as int] * (cosize_a as int) <= i64::MAX as int);
        }
        // Use i128 to avoid intermediate overflow
        let scaled_stride: i64 = ((b.stride[j] as i128) * (cosize_a as i128)) as i64;
        result_stride.push(scaled_stride);

        proof {
            let jj = j as int;
            let idx = (a.shape@.len() + jj) as int;
            assert(result_shape@[idx] == b.shape@[jj]);
            assert(result_shape@[idx] as nat == b@.shape[jj]);
            assert(scaled_stride as int == b@.stride[jj] * (cosize_a as int));
            assert(result_stride@[idx] as int == b@.stride[jj] * (cosize_a as int));
        }

        j = j + 1;
    }

    proof {
        let spec_result = logical_product(&a@, &b@);
        let cs = a@.cosize_nonneg();

        // Shape extensional equality
        assert(shape_to_nat_seq(result_shape@) =~= spec_result.shape) by {
            assert(result_shape@.len() == spec_result.shape.len());
            assert forall|k: int| 0 <= k < result_shape@.len() as int implies
                shape_to_nat_seq(result_shape@)[k] == spec_result.shape[k]
            by {
                if k < a@.shape.len() as int {
                    assert(result_shape@[k] as nat == a@.shape[k]);
                } else {
                    let bk = (k - a@.shape.len()) as int;
                    // Trigger loop invariant with (a.shape@.len() + bk)
                    assert(a.shape@.len() == a@.shape.len());
                    assert((a.shape@.len() + bk) as int == k);
                    assert(result_shape@[(a.shape@.len() + bk) as int] as nat == b@.shape[bk]);
                }
            };
        };

        // Stride extensional equality
        assert(strides_to_int_seq(result_stride@) =~= spec_result.stride) by {
            assert(result_stride@.len() == spec_result.stride.len());
            assert forall|k: int| 0 <= k < result_stride@.len() as int implies
                strides_to_int_seq(result_stride@)[k] == spec_result.stride[k]
            by {
                if k < a@.stride.len() as int {
                    assert(result_stride@[k] as int == a@.stride[k]);
                } else {
                    let bk = (k - a@.stride.len()) as int;
                    assert(a.stride@.len() == a@.stride.len());
                    assert((a.stride@.len() + bk) as int == k);
                    assert(result_stride@[(a.stride@.len() + bk) as int] as int
                        == b@.stride[bk] * (cosize_a as int));
                    assert(spec_result.stride[k] == scale_strides(b@.stride, cs as int)[bk]);
                    assert(scale_strides(b@.stride, cs as int)[bk] == b@.stride[bk] * (cs as int));
                }
            };
        };

        // Valid
        assert(spec_result.valid()) by {
            assert forall|k: int| 0 <= k < spec_result.shape.len() implies
                #[trigger] spec_result.shape[k] > 0
            by {
                if k < a@.shape.len() as int {
                    assert(spec_result.shape[k] == a@.shape[k]);
                } else {
                    let bk = (k - a@.shape.len()) as int;
                    assert(spec_result.shape[k] == b@.shape[bk]);
                }
            };
        };
    }

    RuntimeLayout {
        shape: result_shape,
        stride: result_stride,
        model: Ghost(logical_product(&*a.model.borrow(), &*b.model.borrow())),
    }
}

/// Raked product at runtime: interleave A across B's tiles.
/// A's strides are scaled by cosize(B), B's strides are unscaled.
pub fn raked_product_exec(a: &RuntimeLayout, b: &RuntimeLayout, cosize_b: u64) -> (result: RuntimeLayout)
    requires
        a.wf_spec(),
        b.wf_spec(),
        b@.non_negative_strides(),
        b@.shape.len() > 0,
        cosize_b as nat == b@.cosize_nonneg(),
        forall|i: int| 0 <= i < a@.stride.len() ==>
            #[trigger] a@.stride[i] * (cosize_b as int) >= i64::MIN as int &&
            a@.stride[i] * (cosize_b as int) <= i64::MAX as int,
        shape_size(raked_product(&a@, &b@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == raked_product(&a@, &b@),
{
    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();

    proof {
        assert(a@.shape == shape_to_nat_seq(a.shape@));
        assert(a@.stride == strides_to_int_seq(a.stride@));
        assert(b@.shape == shape_to_nat_seq(b.shape@));
        assert(b@.stride == strides_to_int_seq(b.stride@));
    }

    // Copy A's modes with scaled strides
    let mut i: usize = 0;
    while i < a.shape.len()
        invariant
            0 <= i <= a.shape.len(),
            a.wf_spec(), b.wf_spec(),
            result_shape@.len() == i,
            result_stride@.len() == i,
            a@.shape == shape_to_nat_seq(a.shape@),
            a@.stride == strides_to_int_seq(a.stride@),
            cosize_b as nat == b@.cosize_nonneg(),
            forall|k: int| 0 <= k < a@.stride.len() ==>
                #[trigger] a@.stride[k] * (cosize_b as int) >= i64::MIN as int &&
                a@.stride[k] * (cosize_b as int) <= i64::MAX as int,
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_shape@[j] as nat == a@.shape[j],
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_stride@[j] as int ==
                    a@.stride[j] * (cosize_b as int),
        decreases a.shape.len() - i,
    {
        result_shape.push(a.shape[i]);
        proof {
            assert(a@.stride[i as int] * (cosize_b as int) >= i64::MIN as int);
            assert(a@.stride[i as int] * (cosize_b as int) <= i64::MAX as int);
        }
        let scaled_stride: i64 = ((a.stride[i] as i128) * (cosize_b as i128)) as i64;
        result_stride.push(scaled_stride);
        proof {
            assert(scaled_stride as int == a@.stride[i as int] * (cosize_b as int));
        }
        i = i + 1;
    }

    // Append B's modes (unscaled)
    let mut j: usize = 0;
    while j < b.shape.len()
        invariant
            0 <= j <= b.shape.len(),
            a.wf_spec(), b.wf_spec(),
            result_shape@.len() == a.shape@.len() + j,
            result_stride@.len() == a.stride@.len() + j,
            a@.shape == shape_to_nat_seq(a.shape@),
            a@.stride == strides_to_int_seq(a.stride@),
            b@.shape == shape_to_nat_seq(b.shape@),
            b@.stride == strides_to_int_seq(b.stride@),
            cosize_b as nat == b@.cosize_nonneg(),
            forall|k: int| 0 <= k < a@.stride.len() ==>
                #[trigger] a@.stride[k] * (cosize_b as int) >= i64::MIN as int &&
                a@.stride[k] * (cosize_b as int) <= i64::MAX as int,
            forall|k: int| 0 <= k < a.shape@.len() as int ==>
                #[trigger] result_shape@[k] as nat == a@.shape[k],
            forall|k: int| 0 <= k < a.stride@.len() as int ==>
                #[trigger] result_stride@[k] as int ==
                    a@.stride[k] * (cosize_b as int),
            forall|k: int| 0 <= k < j as int ==>
                #[trigger] result_shape@[(a.shape@.len() + k) as int] as nat == b@.shape[k],
            forall|k: int| 0 <= k < j as int ==>
                #[trigger] result_stride@[(a.stride@.len() + k) as int] as int == b@.stride[k],
        decreases b.shape.len() - j,
    {
        result_shape.push(b.shape[j]);
        result_stride.push(b.stride[j]);
        proof {
            let jj = j as int;
            let idx = (a.shape@.len() + jj) as int;
            assert(result_shape@[idx] == b.shape@[jj]);
            assert(result_shape@[idx] as nat == b@.shape[jj]);
            assert(result_stride@[idx] as int == b@.stride[jj]);
        }
        j = j + 1;
    }

    proof {
        let spec_result = raked_product(&a@, &b@);
        let cs = b@.cosize_nonneg();

        // Shape extensional equality
        assert(shape_to_nat_seq(result_shape@) =~= spec_result.shape) by {
            assert(result_shape@.len() == spec_result.shape.len());
            assert forall|k: int| 0 <= k < result_shape@.len() as int implies
                shape_to_nat_seq(result_shape@)[k] == spec_result.shape[k]
            by {
                if k < a@.shape.len() as int {
                    assert(result_shape@[k] as nat == a@.shape[k]);
                } else {
                    let bk = (k - a@.shape.len()) as int;
                    assert(a.shape@.len() == a@.shape.len());
                    assert((a.shape@.len() + bk) as int == k);
                    assert(result_shape@[(a.shape@.len() + bk) as int] as nat == b@.shape[bk]);
                }
            };
        };

        // Stride extensional equality
        assert(strides_to_int_seq(result_stride@) =~= spec_result.stride) by {
            assert(result_stride@.len() == spec_result.stride.len());
            assert forall|k: int| 0 <= k < result_stride@.len() as int implies
                strides_to_int_seq(result_stride@)[k] == spec_result.stride[k]
            by {
                if k < a@.stride.len() as int {
                    assert(result_stride@[k] as int == a@.stride[k] * (cosize_b as int));
                    assert(spec_result.stride[k] == scale_strides(a@.stride, cs as int)[k]);
                    assert(scale_strides(a@.stride, cs as int)[k] == a@.stride[k] * (cs as int));
                } else {
                    let bk = (k - a@.stride.len()) as int;
                    assert(a.stride@.len() == a@.stride.len());
                    assert((a.stride@.len() + bk) as int == k);
                    assert(result_stride@[(a.stride@.len() + bk) as int] as int == b@.stride[bk]);
                }
            };
        };

        // Valid
        assert(spec_result.valid()) by {
            crate::proof::product_lemmas::lemma_raked_product_valid(&a@, &b@);
        };
    }

    RuntimeLayout {
        shape: result_shape,
        stride: result_stride,
        model: Ghost(raked_product(&*a.model.borrow(), &*b.model.borrow())),
    }
}

/// Coalesce a pair of adjacent modes at position i.
pub fn coalesce_pair_exec(layout: &RuntimeLayout, pos: usize) -> (result: RuntimeLayout)
    requires
        layout.wf_spec(),
        (pos as int) < layout@.shape.len() as int - 1,
        modes_coalesceable(&layout@, pos as int),
        (layout@.shape[pos as int] * layout@.shape[pos as int + 1]) <= u64::MAX as nat,
        shape_size(coalesce_pair(layout@, pos as nat).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == coalesce_pair(layout@, pos as nat),
{
    let n = layout.shape.len();

    proof {
        assert(layout@.shape == shape_to_nat_seq(layout.shape@));
        assert(layout@.stride == strides_to_int_seq(layout.stride@));
        assert(n as nat == layout@.shape.len());
        assert(pos + 1 < n);
    }

    let pos1: usize = pos + 1;

    proof {
        assert(layout.shape@[pos as int] as nat == layout@.shape[pos as int]);
        assert(layout.shape@[pos1 as int] as nat == layout@.shape[pos as int + 1]);
    }

    let merged_shape: u64 = layout.shape[pos] * layout.shape[pos1];
    let merged_stride: i64 = layout.stride[pos];

    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();

    // Phase 1: Copy modes [0, pos)
    let mut i: usize = 0;
    while i < pos
        invariant
            0 <= i <= pos,
            layout.wf_spec(),
            (pos as int) < layout@.shape.len() as int - 1,
            layout.shape@.len() == layout@.shape.len(),
            layout.stride@.len() == layout@.stride.len(),
            result_shape@.len() == i,
            result_stride@.len() == i,
            layout@.shape == shape_to_nat_seq(layout.shape@),
            layout@.stride == strides_to_int_seq(layout.stride@),
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_shape@[j] == layout.shape@[j],
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] result_stride@[j] == layout.stride@[j],
        decreases pos - i,
    {
        result_shape.push(layout.shape[i]);
        result_stride.push(layout.stride[i]);
        i = i + 1;
    }

    // Phase 2: Push merged mode
    result_shape.push(merged_shape);
    result_stride.push(merged_stride);

    // Phase 3: Copy modes [pos+2, n)
    let pos2: usize = pos1 + 1;
    let mut k: usize = pos2;
    while k < n
        invariant
            pos2 <= k <= n,
            n == layout.shape.len(),
            pos2 == pos + 2,
            layout.wf_spec(),
            layout@.shape == shape_to_nat_seq(layout.shape@),
            layout@.stride == strides_to_int_seq(layout.stride@),
            result_shape@.len() == (pos + 1 + (k - pos - 2)) as nat,
            result_stride@.len() == (pos + 1 + (k - pos - 2)) as nat,
            forall|j: int| 0 <= j < pos as int ==>
                #[trigger] result_shape@[j] == layout.shape@[j],
            forall|j: int| 0 <= j < pos as int ==>
                #[trigger] result_stride@[j] == layout.stride@[j],
            result_shape@[pos as int] == merged_shape,
            result_stride@[pos as int] == merged_stride,
            forall|j: int| pos2 as int <= j < k as int ==>
                #[trigger] result_shape@[(pos as int + 1 + (j - pos as int - 2))] == layout.shape@[j],
            forall|j: int| pos2 as int <= j < k as int ==>
                #[trigger] result_stride@[(pos as int + 1 + (j - pos as int - 2))] == layout.stride@[j],
        decreases n - k,
    {
        result_shape.push(layout.shape[k]);
        result_stride.push(layout.stride[k]);
        k = k + 1;
    }

    proof {
        let spec_result = coalesce_pair(layout@, pos as nat);
        let p = pos as int;
        let nn = layout@.shape.len() as int;

        // Final length
        assert(result_shape@.len() == (nn - 1) as nat);
        assert(result_stride@.len() == (nn - 1) as nat);
        assert(spec_result.shape.len() == (nn - 1) as nat) by {
            assert(spec_result.shape == layout@.shape.take(p)
                .add(seq![layout@.shape[p] * layout@.shape[p + 1]])
                .add(layout@.shape.skip(p + 2)));
        };

        // Shape extensional equality
        assert(shape_to_nat_seq(result_shape@) =~= spec_result.shape) by {
            assert forall|j: int| 0 <= j < result_shape@.len() as int implies
                shape_to_nat_seq(result_shape@)[j] == spec_result.shape[j]
            by {
                if j < p {
                    // Phase 1: result_shape@[j] == layout.shape@[j]
                    assert(result_shape@[j] == layout.shape@[j]);
                    assert(spec_result.shape[j] == layout@.shape.take(p)[j]);
                    assert(layout@.shape.take(p)[j] == layout@.shape[j]);
                    assert(layout.shape@[j] as nat == layout@.shape[j]);
                } else if j == p {
                    // Phase 2: merged
                    assert(result_shape@[j] == merged_shape);
                    assert(merged_shape as nat == layout@.shape[p] * layout@.shape[p + 1]) by {
                        assert(layout.shape@[p] as nat == layout@.shape[p]);
                        assert(layout.shape@[p + 1] as nat == layout@.shape[p + 1]);
                    };
                } else {
                    // Phase 3: result_shape@[j] == layout.shape@[j+1]
                    let orig = j + 1;
                    assert((pos + 2) as int <= orig);
                    assert(orig < layout.shape@.len() as int);
                    assert(result_shape@[(p + 1 + (orig - p - 2))] == layout.shape@[orig]);
                    assert((p + 1 + (orig - p - 2)) == j);
                    assert(result_shape@[j] as nat == layout.shape@[orig] as nat);
                    assert(spec_result.shape[j] == layout@.shape[orig]);
                    assert(layout.shape@[orig] as nat == layout@.shape[orig]);
                }
            };
        };

        // Stride extensional equality
        assert(strides_to_int_seq(result_stride@) =~= spec_result.stride) by {
            assert(result_stride@.len() == spec_result.stride.len());
            assert forall|j: int| 0 <= j < result_stride@.len() as int implies
                strides_to_int_seq(result_stride@)[j] == spec_result.stride[j]
            by {
                if j < p {
                    assert(result_stride@[j] == layout.stride@[j]);
                    assert(spec_result.stride[j] == layout@.stride.take(p)[j]);
                    assert(layout@.stride.take(p)[j] == layout@.stride[j]);
                    assert(layout.stride@[j] as int == layout@.stride[j]);
                } else if j == p {
                    assert(result_stride@[j] == merged_stride);
                    assert(merged_stride as int == layout@.stride[p]) by {
                        assert(layout.stride@[p] as int == layout@.stride[p]);
                    };
                } else {
                    let orig = j + 1;
                    assert(result_stride@[(p + 1 + (orig - p - 2))] == layout.stride@[orig]);
                    assert((p + 1 + (orig - p - 2)) == j);
                    assert(result_stride@[j] as int == layout.stride@[orig] as int);
                    assert(spec_result.stride[j] == layout@.stride[orig]);
                    assert(layout.stride@[orig] as int == layout@.stride[orig]);
                }
            };
        };

        // Valid
        assert(spec_result.valid()) by {
            assert forall|j: int| 0 <= j < spec_result.shape.len() implies
                #[trigger] spec_result.shape[j] > 0
            by {
                if j < p {
                    assert(spec_result.shape[j] == layout@.shape[j]);
                } else if j == p {
                    assert(spec_result.shape[j] == layout@.shape[p] * layout@.shape[p + 1]);
                    crate::proof::integer_helpers::lemma_mul_pos(layout@.shape[p], layout@.shape[p + 1]);
                } else {
                    assert(spec_result.shape[j] == layout@.shape[j + 1]);
                }
            };
        };
    }

    RuntimeLayout {
        shape: result_shape,
        stride: result_stride,
        model: Ghost(coalesce_pair(*layout.model.borrow(), pos as nat)),
    }
}

/// Check if two adjacent modes are coalesceable at runtime.
fn modes_coalesceable_exec(layout: &RuntimeLayout, pos: usize) -> (result: bool)
    requires
        layout.wf_spec(),
        layout.shape@.len() >= 2,
        pos < layout.shape@.len() - 1,
    ensures
        result == modes_coalesceable(&layout@, pos as int),
{
    let n = layout.shape.len();
    assert(n >= 2);
    let m: u64 = layout.shape[pos];
    let s: i64 = layout.stride[pos];
    let s_next: i64 = layout.stride[pos + 1];

    proof {
        // i128 range is sufficient for u64 * i64
        assert(i128::MIN as int <= (m as int) * (s as int) <= i128::MAX as int)
            by (nonlinear_arith)
            requires
                0 <= m as int <= u64::MAX as int,
                i64::MIN as int <= s as int <= i64::MAX as int,
        ;
    }

    // Compute (shape[pos] as int) * stride[pos] using i128 to avoid overflow
    let product: i128 = (m as i128) * (s as i128);

    proof {
        assert(product as int == (m as int) * (s as int));
        assert(layout@.shape[pos as int] == m as nat);
        assert(layout@.stride[pos as int] == s as int);
        assert(layout@.stride[(pos + 1) as int] == s_next as int);
    }

    product == s_next as i128
}

/// Full coalesce at runtime: merge all adjacent coalesceable pairs.
pub fn coalesce_exec(layout: RuntimeLayout) -> (result: RuntimeLayout)
    requires
        layout.wf_spec(),
    ensures
        result.wf_spec(),
        result@ == coalesce(layout@),
{
    let ghost original = layout@;
    let mut current = layout;
    let mut pos: usize = 0;

    proof {
        assert(coalesce_pass(current@, 0) == coalesce(original));
    }

    while current.shape.len() >= 2 && pos < current.shape.len() - 1
        invariant
            current.wf_spec(),
            pos <= current.shape@.len(),
            coalesce_pass(current@, pos as nat) == coalesce(original),
        decreases current.shape@.len() - pos,
    {
        if modes_coalesceable_exec(&current, pos) {
            proof {
                // shape_size > 0 for valid shapes
                crate::proof::shape_lemmas::lemma_shape_size_positive(current@.shape);

                // Overflow bound: shape[pos] * shape[pos+1] <= shape_size <= u64::MAX
                crate::proof::inverse_lemmas::lemma_two_modes_product_bound(
                    current@.shape, pos as int, (pos + 1) as int);

                // coalesce_pair preserves size => shape_size(coalesced.shape) <= u64::MAX
                crate::proof::coalesce_lemmas::lemma_coalesce_pair_size_general(
                    current@, pos as nat);
            }
            current = coalesce_pair_exec(&current, pos);
        } else {
            pos = pos + 1;
        }
    }

    current
}

/// Slice a layout by fixing a coordinate in one mode.
/// Returns the residual layout (rank - 1) and the constant offset.
pub fn slice_exec(layout: &RuntimeLayout, mode: usize, coord: u64) -> (result: (RuntimeLayout, i64))
    requires
        layout.wf_spec(),
        (mode as nat) < layout@.rank(),
        (coord as nat) < layout@.shape[mode as int],
        // The constant offset fits in i64
        (coord as int) * layout@.stride[mode as int] >= i64::MIN as int,
        (coord as int) * layout@.stride[mode as int] <= i64::MAX as int,
        // Result size fits
        shape_size(crate::slice::slice_layout(&layout@, mode as nat, coord as nat).shape) <= u64::MAX as nat,
    ensures ({
        let (rl, off) = result;
        &&& rl.wf_spec()
        &&& rl@ == crate::slice::slice_layout(&layout@, mode as nat, coord as nat)
        &&& off as int == crate::slice::slice_offset(&layout@, mode as nat, coord as nat)
    }),
{
    let n = layout.shape.len();

    proof {
        assert(layout@.shape == shape_to_nat_seq(layout.shape@));
        assert(layout@.stride == strides_to_int_seq(layout.stride@));
    }

    // Compute constant offset: coord * stride[mode]
    let const_offset: i64 = ((coord as i128) * (layout.stride[mode] as i128)) as i64;

    // Build result shape and stride by copying all modes except `mode`
    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == layout.shape.len(),
            layout.wf_spec(),
            layout@.shape == shape_to_nat_seq(layout.shape@),
            layout@.stride == strides_to_int_seq(layout.stride@),
            (mode as nat) < layout@.rank(),
            // Length tracking: we skip index `mode`, so count is i - (if mode < i then 1 else 0)
            result_shape@.len() == (if mode < i { (i - 1) as nat } else { i as nat }),
            result_stride@.len() == result_shape@.len(),
            // Content: matches remove(mode)
            forall|j: int| 0 <= j < result_shape@.len() as int ==>
                #[trigger] result_shape@[j] == layout.shape@[if j < mode as int { j } else { j + 1 }],
            forall|j: int| 0 <= j < result_stride@.len() as int ==>
                #[trigger] result_stride@[j] == layout.stride@[if j < mode as int { j } else { j + 1 }],
        decreases n - i,
    {
        if i != mode {
            result_shape.push(layout.shape[i]);
            result_stride.push(layout.stride[i]);
        }
        i = i + 1;
    }

    proof {
        let spec_result = crate::slice::slice_layout(&layout@, mode as nat, coord as nat);
        let m = mode as int;

        // Shape extensional equality
        assert(shape_to_nat_seq(result_shape@) =~= spec_result.shape) by {
            assert(result_shape@.len() == spec_result.shape.len());
            assert forall|j: int| 0 <= j < result_shape@.len() as int implies
                shape_to_nat_seq(result_shape@)[j] == spec_result.shape[j]
            by {
                let orig = if j < m { j } else { j + 1 };
                assert(result_shape@[j] == layout.shape@[orig]);
                assert(layout.shape@[orig] as nat == layout@.shape[orig]);
                assert(spec_result.shape[j] == layout@.shape.remove(m)[j]);
                assert(layout@.shape.remove(m)[j] == layout@.shape[orig]);
            };
        };

        // Stride extensional equality
        assert(strides_to_int_seq(result_stride@) =~= spec_result.stride) by {
            assert(result_stride@.len() == spec_result.stride.len());
            assert forall|j: int| 0 <= j < result_stride@.len() as int implies
                strides_to_int_seq(result_stride@)[j] == spec_result.stride[j]
            by {
                let orig = if j < m { j } else { j + 1 };
                assert(result_stride@[j] == layout.stride@[orig]);
                assert(layout.stride@[orig] as int == layout@.stride[orig]);
                assert(spec_result.stride[j] == layout@.stride.remove(m)[j]);
                assert(layout@.stride.remove(m)[j] == layout@.stride[orig]);
            };
        };

        // Valid
        crate::proof::slice_lemmas::lemma_slice_valid(&layout@, mode as nat, coord as nat);
    }

    let rl = RuntimeLayout {
        shape: result_shape,
        stride: result_stride,
        model: Ghost(crate::slice::slice_layout(&*layout.model.borrow(), mode as nat, coord as nat)),
    };
    (rl, const_offset)
}

/// Dice a layout: keep only one mode, producing a rank-1 layout.
pub fn dice_exec(layout: &RuntimeLayout, mode: usize) -> (result: RuntimeLayout)
    requires
        layout.wf_spec(),
        (mode as nat) < layout@.rank(),
        shape_size(crate::slice::dice_layout(&layout@, mode as nat).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == crate::slice::dice_layout(&layout@, mode as nat),
{
    proof {
        assert(layout@.shape == shape_to_nat_seq(layout.shape@));
        assert(layout@.stride == strides_to_int_seq(layout.stride@));
    }

    let mut shape_vec: Vec<u64> = Vec::new();
    shape_vec.push(layout.shape[mode]);
    let mut stride_vec: Vec<i64> = Vec::new();
    stride_vec.push(layout.stride[mode]);

    proof {
        let spec_result = crate::slice::dice_layout(&layout@, mode as nat);

        assert(shape_to_nat_seq(shape_vec@) =~= spec_result.shape) by {
            assert(shape_vec@[0] as nat == layout.shape@[mode as int] as nat);
            assert(layout.shape@[mode as int] as nat == layout@.shape[mode as int]);
        };

        assert(strides_to_int_seq(stride_vec@) =~= spec_result.stride) by {
            assert(stride_vec@[0] as int == layout.stride@[mode as int] as int);
            assert(layout.stride@[mode as int] as int == layout@.stride[mode as int]);
        };

        // Valid: shape[0] = layout.shape[mode] > 0
        crate::proof::slice_lemmas::lemma_dice_valid(&layout@, mode as nat);
    }

    RuntimeLayout {
        shape: shape_vec,
        stride: stride_vec,
        model: Ghost(crate::slice::dice_layout(&*layout.model.borrow(), mode as nat)),
    }
}

} // verus!
