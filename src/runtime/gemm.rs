use vstd::prelude::*;
use crate::layout::*;
use crate::gemm::*;
use super::layout::*;
use super::*;

verus! {

/// Runtime tensor: exec wrapper around TensorSpec.
pub struct RuntimeTensor {
    pub layout: RuntimeLayout,
    pub data_size: u64,
}

impl View for RuntimeTensor {
    type V = TensorSpec;
    open spec fn view(&self) -> TensorSpec {
        TensorSpec {
            layout: self.layout@,
            data_size: self.data_size as nat,
        }
    }
}

impl RuntimeTensor {
    /// Well-formedness: the runtime tensor faithfully represents a spec tensor.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.layout.wf_spec()
        &&& self.data_size as nat >= self.layout@.cosize_nonneg()
    }
}

/// Bridge: spec stride equals concrete stride for rank-2 layout.
proof fn lemma_stride_bridge(layout: &RuntimeLayout)
    requires layout.wf_spec(), layout@.rank() == 2,
    ensures
        layout@.stride[0] == layout.stride@[0] as int,
        layout@.stride[1] == layout.stride@[1] as int,
{
    assert(layout@.stride == strides_to_int_seq(layout.stride@));
    assert(layout@.stride[0] == strides_to_int_seq(layout.stride@)[0]);
    assert(layout@.stride[1] == strides_to_int_seq(layout.stride@)[1]);
}

/// Linearize 2D coordinates (i, j) into a flat offset for a rank-2 layout.
/// offset = i * stride[0] + j * stride[1]
pub fn linearize_2d(layout: &RuntimeLayout, i: u64, j: u64) -> (result: i64)
    requires
        layout.wf_spec(),
        layout@.rank() == 2,
        (i as nat) < layout@.shape[0],
        (j as nat) < layout@.shape[1],
        i <= i64::MAX as u64,
        j <= i64::MAX as u64,
        // Overflow safety: each term and their sum fit in i64
        (i as int) * layout@.stride[0] >= i64::MIN as int,
        (i as int) * layout@.stride[0] <= i64::MAX as int,
        (j as int) * layout@.stride[1] >= i64::MIN as int,
        (j as int) * layout@.stride[1] <= i64::MAX as int,
        (i as int) * layout@.stride[0] + (j as int) * layout@.stride[1] >= i64::MIN as int,
        (i as int) * layout@.stride[0] + (j as int) * layout@.stride[1] <= i64::MAX as int,
    ensures
        result as int == gemm_c_offset(&layout@, i as nat, j as nat),
{
    proof { lemma_stride_bridge(layout); }
    let ii = i as i64;
    let jj = j as i64;
    let s0 = layout.stride[0];
    let s1 = layout.stride[1];
    let term1 = ii * s0;
    let term2 = jj * s1;
    term1 + term2
}

/// Compute A[i,k] offset for GEMM.
pub fn gemm_a_offset_exec(
    a_layout: &RuntimeLayout, i: u64, k: u64,
) -> (result: i64)
    requires
        a_layout.wf_spec(),
        a_layout@.rank() == 2,
        (i as nat) < a_layout@.shape[0],
        (k as nat) < a_layout@.shape[1],
        i <= i64::MAX as u64, k <= i64::MAX as u64,
        (i as int) * a_layout@.stride[0] >= i64::MIN as int,
        (i as int) * a_layout@.stride[0] <= i64::MAX as int,
        (k as int) * a_layout@.stride[1] >= i64::MIN as int,
        (k as int) * a_layout@.stride[1] <= i64::MAX as int,
        (i as int) * a_layout@.stride[0] + (k as int) * a_layout@.stride[1] >= i64::MIN as int,
        (i as int) * a_layout@.stride[0] + (k as int) * a_layout@.stride[1] <= i64::MAX as int,
    ensures
        result as int == gemm_a_offset(&a_layout@, i as nat, k as nat),
{
    linearize_2d(a_layout, i, k)
}

/// Compute B[k,j] offset for GEMM.
pub fn gemm_b_offset_exec(
    b_layout: &RuntimeLayout, k: u64, j: u64,
) -> (result: i64)
    requires
        b_layout.wf_spec(),
        b_layout@.rank() == 2,
        (k as nat) < b_layout@.shape[0],
        (j as nat) < b_layout@.shape[1],
        k <= i64::MAX as u64, j <= i64::MAX as u64,
        (k as int) * b_layout@.stride[0] >= i64::MIN as int,
        (k as int) * b_layout@.stride[0] <= i64::MAX as int,
        (j as int) * b_layout@.stride[1] >= i64::MIN as int,
        (j as int) * b_layout@.stride[1] <= i64::MAX as int,
        (k as int) * b_layout@.stride[0] + (j as int) * b_layout@.stride[1] >= i64::MIN as int,
        (k as int) * b_layout@.stride[0] + (j as int) * b_layout@.stride[1] <= i64::MAX as int,
    ensures
        result as int == gemm_b_offset(&b_layout@, k as nat, j as nat),
{
    linearize_2d(b_layout, k, j)
}

/// Compute C[i,j] offset for GEMM.
pub fn gemm_c_offset_exec(
    c_layout: &RuntimeLayout, i: u64, j: u64,
) -> (result: i64)
    requires
        c_layout.wf_spec(),
        c_layout@.rank() == 2,
        (i as nat) < c_layout@.shape[0],
        (j as nat) < c_layout@.shape[1],
        i <= i64::MAX as u64, j <= i64::MAX as u64,
        (i as int) * c_layout@.stride[0] >= i64::MIN as int,
        (i as int) * c_layout@.stride[0] <= i64::MAX as int,
        (j as int) * c_layout@.stride[1] >= i64::MIN as int,
        (j as int) * c_layout@.stride[1] <= i64::MAX as int,
        (i as int) * c_layout@.stride[0] + (j as int) * c_layout@.stride[1] >= i64::MIN as int,
        (i as int) * c_layout@.stride[0] + (j as int) * c_layout@.stride[1] <= i64::MAX as int,
    ensures
        result as int == gemm_c_offset(&c_layout@, i as nat, j as nat),
{
    linearize_2d(c_layout, i, j)
}

/// Helper: A-offset overflow bounds hold for index kk.
pub open spec fn a_offset_overflow_ok(
    a_layout: &LayoutSpec, i: nat, kk: nat,
) -> bool {
    &&& (kk as int) * a_layout.stride[1] >= i64::MIN as int
    &&& (kk as int) * a_layout.stride[1] <= i64::MAX as int
    &&& (i as int) * a_layout.stride[0] + (kk as int) * a_layout.stride[1] >= i64::MIN as int
    &&& (i as int) * a_layout.stride[0] + (kk as int) * a_layout.stride[1] <= i64::MAX as int
}

/// Helper: B-offset overflow bounds hold for index kk.
pub open spec fn b_offset_overflow_ok(
    b_layout: &LayoutSpec, j: nat, kk: nat,
) -> bool {
    &&& (kk as int) * b_layout.stride[0] >= i64::MIN as int
    &&& (kk as int) * b_layout.stride[0] <= i64::MAX as int
    &&& (kk as int) * b_layout.stride[0] + (j as int) * b_layout.stride[1] >= i64::MIN as int
    &&& (kk as int) * b_layout.stride[0] + (j as int) * b_layout.stride[1] <= i64::MAX as int
}

/// GEMM multiply-accumulate offset computation for one (i,j) output element
/// over k_start..k_end. Returns offset pairs (a_offset, b_offset) for each k.
/// Actual data multiply is external — this is data-type-agnostic.
pub fn gemm_mac_offsets(
    a_layout: &RuntimeLayout, b_layout: &RuntimeLayout,
    i: u64, j: u64, k_start: u64, k_end: u64,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        a_layout.wf_spec(), b_layout.wf_spec(),
        a_layout@.rank() == 2, b_layout@.rank() == 2,
        k_start <= k_end,
        (i as nat) < a_layout@.shape[0],
        (k_end as nat) <= a_layout@.shape[1],
        (k_end as nat) <= b_layout@.shape[0],
        (j as nat) < b_layout@.shape[1],
        i <= i64::MAX as u64, j <= i64::MAX as u64,
        k_end <= i64::MAX as u64,
        (i as int) * a_layout@.stride[0] >= i64::MIN as int,
        (i as int) * a_layout@.stride[0] <= i64::MAX as int,
        (j as int) * b_layout@.stride[1] >= i64::MIN as int,
        (j as int) * b_layout@.stride[1] <= i64::MAX as int,
        forall|kk: nat| kk < (k_end as nat) ==>
            #[trigger] a_offset_overflow_ok(&a_layout@, i as nat, kk),
        forall|kk: nat| kk < (k_end as nat) ==>
            #[trigger] b_offset_overflow_ok(&b_layout@, j as nat, kk),
    ensures
        result.0.len() == (k_end - k_start) as nat,
        result.1.len() == (k_end - k_start) as nat,
        forall|idx: nat| idx < (k_end - k_start) as nat ==>
            result.0@[idx as int] as int
            == gemm_a_offset(&a_layout@, i as nat, (k_start as nat + idx)),
        forall|idx: nat| idx < (k_end - k_start) as nat ==>
            result.1@[idx as int] as int
            == gemm_b_offset(&b_layout@, (k_start as nat + idx), j as nat),
{
    let mut a_offs: Vec<i64> = Vec::new();
    let mut b_offs: Vec<i64> = Vec::new();
    let mut kk = k_start;

    while kk < k_end
        invariant
            k_start <= kk <= k_end,
            a_layout.wf_spec(), b_layout.wf_spec(),
            a_layout@.rank() == 2, b_layout@.rank() == 2,
            (i as nat) < a_layout@.shape[0],
            (k_end as nat) <= a_layout@.shape[1],
            (k_end as nat) <= b_layout@.shape[0],
            (j as nat) < b_layout@.shape[1],
            a_offs.len() == (kk - k_start) as nat,
            b_offs.len() == (kk - k_start) as nat,
            forall|idx: nat| idx < (kk - k_start) as nat ==>
                a_offs@[idx as int] as int
                == gemm_a_offset(&a_layout@, i as nat, (k_start as nat + idx)),
            forall|idx: nat| idx < (kk - k_start) as nat ==>
                b_offs@[idx as int] as int
                == gemm_b_offset(&b_layout@, (k_start as nat + idx), j as nat),
            i <= i64::MAX as u64, j <= i64::MAX as u64,
            k_end <= i64::MAX as u64,
            (i as int) * a_layout@.stride[0] >= i64::MIN as int,
            (i as int) * a_layout@.stride[0] <= i64::MAX as int,
            (j as int) * b_layout@.stride[1] >= i64::MIN as int,
            (j as int) * b_layout@.stride[1] <= i64::MAX as int,
            forall|kk2: nat| kk2 < (k_end as nat) ==>
                #[trigger] a_offset_overflow_ok(&a_layout@, i as nat, kk2),
            forall|kk2: nat| kk2 < (k_end as nat) ==>
                #[trigger] b_offset_overflow_ok(&b_layout@, j as nat, kk2),
        decreases k_end - kk,
    {
        proof {
            assert(a_offset_overflow_ok(&a_layout@, i as nat, kk as nat));
            assert(b_offset_overflow_ok(&b_layout@, j as nat, kk as nat));
        }
        let a_off = gemm_a_offset_exec(a_layout, i, kk);
        let b_off = gemm_b_offset_exec(b_layout, kk, j);
        a_offs.push(a_off);
        b_offs.push(b_off);

        proof {
            let idx = (kk - k_start) as nat;
            assert(a_offs@[idx as int] as int == gemm_a_offset(&a_layout@, i as nat, kk as nat));
            assert(k_start as nat + idx == kk as nat);
        }

        kk = kk + 1;
    }

    (a_offs, b_offs)
}

/// Compute MAC offset pairs for one (i,j) output element over k_start..k_end.
/// Returns Vec of (a_offset, b_offset) pairs.
pub fn mac_offset_pairs_exec(
    a_layout: &RuntimeLayout, b_layout: &RuntimeLayout,
    i: u64, j: u64, k_start: u64, k_end: u64,
) -> (result: Vec<(i64, i64)>)
    requires
        a_layout.wf_spec(), b_layout.wf_spec(),
        a_layout@.rank() == 2, b_layout@.rank() == 2,
        k_start <= k_end,
        (i as nat) < a_layout@.shape[0],
        (k_end as nat) <= a_layout@.shape[1],
        (k_end as nat) <= b_layout@.shape[0],
        (j as nat) < b_layout@.shape[1],
        i <= i64::MAX as u64, j <= i64::MAX as u64,
        k_end <= i64::MAX as u64,
        (i as int) * a_layout@.stride[0] >= i64::MIN as int,
        (i as int) * a_layout@.stride[0] <= i64::MAX as int,
        (j as int) * b_layout@.stride[1] >= i64::MIN as int,
        (j as int) * b_layout@.stride[1] <= i64::MAX as int,
        forall|kk: nat| kk < (k_end as nat) ==>
            #[trigger] a_offset_overflow_ok(&a_layout@, i as nat, kk),
        forall|kk: nat| kk < (k_end as nat) ==>
            #[trigger] b_offset_overflow_ok(&b_layout@, j as nat, kk),
    ensures
        result.len() == (k_end - k_start) as nat,
        forall|idx: nat| idx < (k_end - k_start) as nat ==>
            (#[trigger] result@[idx as int]).0 as int
            == gemm_a_offset(&a_layout@, i as nat, (k_start as nat + idx)),
        forall|idx: nat| idx < (k_end - k_start) as nat ==>
            (#[trigger] result@[idx as int]).1 as int
            == gemm_b_offset(&b_layout@, (k_start as nat + idx), j as nat),
{
    let mut out: Vec<(i64, i64)> = Vec::new();
    let mut kk = k_start;

    while kk < k_end
        invariant
            k_start <= kk <= k_end,
            a_layout.wf_spec(), b_layout.wf_spec(),
            a_layout@.rank() == 2, b_layout@.rank() == 2,
            (i as nat) < a_layout@.shape[0],
            (k_end as nat) <= a_layout@.shape[1],
            (k_end as nat) <= b_layout@.shape[0],
            (j as nat) < b_layout@.shape[1],
            out.len() == (kk - k_start) as nat,
            forall|idx: nat| idx < (kk - k_start) as nat ==>
                (#[trigger] out@[idx as int]).0 as int
                == gemm_a_offset(&a_layout@, i as nat, (k_start as nat + idx)),
            forall|idx: nat| idx < (kk - k_start) as nat ==>
                (#[trigger] out@[idx as int]).1 as int
                == gemm_b_offset(&b_layout@, (k_start as nat + idx), j as nat),
            i <= i64::MAX as u64, j <= i64::MAX as u64,
            k_end <= i64::MAX as u64,
            (i as int) * a_layout@.stride[0] >= i64::MIN as int,
            (i as int) * a_layout@.stride[0] <= i64::MAX as int,
            (j as int) * b_layout@.stride[1] >= i64::MIN as int,
            (j as int) * b_layout@.stride[1] <= i64::MAX as int,
            forall|kk2: nat| kk2 < (k_end as nat) ==>
                #[trigger] a_offset_overflow_ok(&a_layout@, i as nat, kk2),
            forall|kk2: nat| kk2 < (k_end as nat) ==>
                #[trigger] b_offset_overflow_ok(&b_layout@, j as nat, kk2),
        decreases k_end - kk,
    {
        proof {
            assert(a_offset_overflow_ok(&a_layout@, i as nat, kk as nat));
            assert(b_offset_overflow_ok(&b_layout@, j as nat, kk as nat));
        }
        let a_off = gemm_a_offset_exec(a_layout, i, kk);
        let b_off = gemm_b_offset_exec(b_layout, kk, j);
        out.push((a_off, b_off));

        proof {
            let idx = (kk - k_start) as nat;
            assert(out@[idx as int] == (a_off, b_off));
            assert(k_start as nat + idx == kk as nat);
        }

        kk = kk + 1;
    }

    out
}

/// Compute C output offset for tile (ti, tj) at element (ei, ej).
pub fn gemm_c_tile_offset_exec(
    c_layout: &RuntimeLayout,
    ti: u64, tj: u64, ei: u64, ej: u64,
    bm: u64, bn: u64,
) -> (result: i64)
    requires
        c_layout.wf_spec(), c_layout@.rank() == 2,
        bm > 0, bn > 0,
        (ti as nat) * (bm as nat) + (ei as nat) < c_layout@.shape[0],
        (tj as nat) * (bn as nat) + (ej as nat) < c_layout@.shape[1],
        (ti as nat) * (bm as nat) + (ei as nat) <= u64::MAX as nat,
        (tj as nat) * (bn as nat) + (ej as nat) <= u64::MAX as nat,
        (ti as nat) * (bm as nat) + (ei as nat) <= i64::MAX as nat,
        (tj as nat) * (bn as nat) + (ej as nat) <= i64::MAX as nat,
        (((ti as nat) * (bm as nat) + (ei as nat)) as int) * c_layout@.stride[0] >= i64::MIN as int,
        (((ti as nat) * (bm as nat) + (ei as nat)) as int) * c_layout@.stride[0] <= i64::MAX as int,
        (((tj as nat) * (bn as nat) + (ej as nat)) as int) * c_layout@.stride[1] >= i64::MIN as int,
        (((tj as nat) * (bn as nat) + (ej as nat)) as int) * c_layout@.stride[1] <= i64::MAX as int,
        (((ti as nat) * (bm as nat) + (ei as nat)) as int) * c_layout@.stride[0]
            + (((tj as nat) * (bn as nat) + (ej as nat)) as int) * c_layout@.stride[1] >= i64::MIN as int,
        (((ti as nat) * (bm as nat) + (ei as nat)) as int) * c_layout@.stride[0]
            + (((tj as nat) * (bn as nat) + (ej as nat)) as int) * c_layout@.stride[1] <= i64::MAX as int,
    ensures
        result as int == gemm_c_tile_offset(&c_layout@,
            ti as nat, tj as nat, ei as nat, ej as nat,
            bm as nat, bn as nat),
{
    let gi = ti * bm + ei;
    let gj = tj * bn + ej;
    linearize_2d(c_layout, gi, gj)
}

} // verus!
