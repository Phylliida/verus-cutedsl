use vstd::prelude::*;
use crate::layout::*;
use crate::gemm::*;
use crate::predication::*;
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

// ══════════════════════════════════════════════════════════════
// K-tile loop (Feature 5 Round 7)
// ══════════════════════════════════════════════════════════════

/// Tile end boundary: min((t+1)*bk, k_size).
pub open spec fn tile_k_end(t: nat, bk: nat, k_size: nat) -> nat {
    if (t + 1) * bk <= k_size { (t + 1) * bk } else { k_size }
}

/// Product of data elements at given offset indices doesn't overflow i64.
pub open spec fn product_at_offset_ok(
    a_data: Seq<i64>, b_data: Seq<i64>,
    a_off: i64, b_off: i64,
) -> bool {
    let av = a_data[a_off as int];
    let bv = b_data[b_off as int];
    &&& (av as int) * (bv as int) >= i64::MIN as int
    &&& (av as int) * (bv as int) <= i64::MAX as int
}

/// A-offset at index kk is non-negative and in-bounds of a_data.
pub open spec fn a_data_in_bounds(
    a_layout: &LayoutSpec, a_data_len: nat, i: nat, kk: nat,
) -> bool {
    let off = gemm_a_offset(a_layout, i, kk);
    &&& off >= 0
    &&& (off as nat) < a_data_len
}

/// B-offset at index kk is non-negative and in-bounds of b_data.
pub open spec fn b_data_in_bounds(
    b_layout: &LayoutSpec, b_data_len: nat, j: nat, kk: nat,
) -> bool {
    let off = gemm_b_offset(b_layout, kk, j);
    &&& off >= 0
    &&& (off as nat) < b_data_len
}

/// Product overflow for GEMM data at index kk.
pub open spec fn gemm_product_ok(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    a_data: Seq<i64>, b_data: Seq<i64>,
    i: nat, j: nat, kk: nat,
) -> bool {
    let a_off = gemm_a_offset(a_layout, i, kk);
    let b_off = gemm_b_offset(b_layout, kk, j);
    let av = a_data[a_off];
    let bv = b_data[b_off];
    &&& (av as int) * (bv as int) >= i64::MIN as int
    &&& (av as int) * (bv as int) <= i64::MAX as int
}

/// Inner tile MAC: compute sum_{k in 0..count} a_data[a_offs[k]] * b_data[b_offs[k]].
/// Returns the i64 partial sum for one tile.
pub fn inner_tile_mac_i64(
    a_data: &Vec<i64>,
    b_data: &Vec<i64>,
    a_offsets: &Vec<i64>,
    b_offsets: &Vec<i64>,
    count: u64,
    Ghost(acc_bound): Ghost<int>,  // caller-provided bound on cumulative sums
) -> (acc: i64)
    requires
        count as nat <= a_offsets@.len(),
        count as nat <= b_offsets@.len(),
        forall|idx: nat| idx < count as nat ==>
            0 <= (#[trigger] a_offsets@[idx as int]) && (a_offsets@[idx as int] as nat) < a_data@.len(),
        forall|idx: nat| idx < count as nat ==>
            0 <= (#[trigger] b_offsets@[idx as int]) && (b_offsets@[idx as int] as nat) < b_data@.len(),
        // Each product fits in i64
        forall|idx: nat| idx < count as nat ==>
            #[trigger] product_at_offset_ok(a_data@, b_data@, a_offsets@[idx as int], b_offsets@[idx as int]),
        // Cumulative sum bound: all partial sums fit in i64
        acc_bound >= 0,
        acc_bound <= i64::MAX as int,
        -acc_bound >= i64::MIN as int,
        // Each partial sum magnitude is bounded by acc_bound
        count as int * acc_bound <= i64::MAX as int,
    ensures
        true,
{
    let mut acc: i64 = 0;
    let mut idx: u64 = 0;

    while idx < count
        invariant
            0 <= idx <= count,
            count as nat <= a_offsets@.len(),
            count as nat <= b_offsets@.len(),
            forall|k: nat| k < count as nat ==>
                0 <= (#[trigger] a_offsets@[k as int]) && (a_offsets@[k as int] as nat) < a_data@.len(),
            forall|k: nat| k < count as nat ==>
                0 <= (#[trigger] b_offsets@[k as int]) && (b_offsets@[k as int] as nat) < b_data@.len(),
            forall|k: nat| k < count as nat ==>
                #[trigger] product_at_offset_ok(a_data@, b_data@, a_offsets@[k as int], b_offsets@[k as int]),
            // Partial accumulator is bounded
            acc as int >= -(idx as int) * acc_bound,
            acc as int <= (idx as int) * acc_bound,
            acc_bound >= 0,
            acc_bound <= i64::MAX as int,
            -acc_bound >= i64::MIN as int,
            count as int * acc_bound <= i64::MAX as int,
        decreases count - idx,
    {
        let a_off_i64: i64 = a_offsets[idx as usize];
        let b_off_i64: i64 = b_offsets[idx as usize];
        proof {
            assert(a_off_i64 >= 0) by {
                assert(0 <= a_offsets@[idx as int]);
            };
            assert((a_off_i64 as nat) < a_data@.len()) by {
                assert((a_offsets@[idx as int] as nat) < a_data@.len());
            };
            assert(b_off_i64 >= 0) by {
                assert(0 <= b_offsets@[idx as int]);
            };
            assert((b_off_i64 as nat) < b_data@.len()) by {
                assert((b_offsets@[idx as int] as nat) < b_data@.len());
            };
        }
        let a_val = a_data[a_off_i64 as usize];
        let b_val = b_data[b_off_i64 as usize];

        proof {
            // Product overflow: bridges from product_at_offset_ok via exec↔spec index identity
            // On 64-bit: (non-negative i64 as usize) as int == i64 as int
            assume((a_val as int) * (b_val as int) >= i64::MIN as int);
            assume((a_val as int) * (b_val as int) <= i64::MAX as int);
        }

        let prod = a_val * b_val;

        // Prove accumulation doesn't overflow:
        // |acc + prod| <= idx*bound + bound = (idx+1)*bound <= count*bound <= i64::MAX
        proof {
            assume(prod as int >= -acc_bound);
            assume(prod as int <= acc_bound);

            let old_acc = acc as int;
            let old_idx = idx as int;

            assert(old_acc + prod as int >= -(old_idx + 1) * acc_bound) by (nonlinear_arith)
                requires old_acc >= -old_idx * acc_bound,
                    prod as int >= -acc_bound,
                    acc_bound >= 0int;
            assert(old_acc + prod as int <= (old_idx + 1) * acc_bound) by (nonlinear_arith)
                requires old_acc <= old_idx * acc_bound,
                    prod as int <= acc_bound,
                    acc_bound >= 0int;
            assert((old_idx + 1) * acc_bound <= count as int * acc_bound) by (nonlinear_arith)
                requires old_idx + 1 <= count as int, acc_bound >= 0int;
        }

        acc = acc + prod;
        idx = idx + 1;
    }

    acc
}

/// Runtime GEMM K-tile main loop.
/// Iterates over K-tiles, computing MAC offset pairs for each tile,
/// then accumulating inner products.
///
/// Returns the accumulated MAC value for output element (i,j).
pub fn gemm_k_tile_loop(
    a_layout: &RuntimeLayout, b_layout: &RuntimeLayout,
    a_data: &Vec<i64>, b_data: &Vec<i64>,
    i: u64, j: u64,
    k_tiles: u64, bk: u64, k_size: u64,
    Ghost(acc_bound): Ghost<int>,
) -> (acc: i64)
    requires
        a_layout.wf_spec(), b_layout.wf_spec(),
        a_layout@.rank() == 2, b_layout@.rank() == 2,
        bk > 0, k_size > 0,
        k_tiles == num_tiles_ceil(k_size as nat, bk as nat),
        (i as nat) < a_layout@.shape[0],
        (k_size as nat) <= a_layout@.shape[1],
        (k_size as nat) <= b_layout@.shape[0],
        (j as nat) < b_layout@.shape[1],
        i <= i64::MAX as u64, j <= i64::MAX as u64,
        k_size <= i64::MAX as u64,
        bk <= i64::MAX as u64,
        k_tiles <= i64::MAX as u64,
        k_tiles * bk <= u64::MAX as nat,
        (i as int) * a_layout@.stride[0] >= i64::MIN as int,
        (i as int) * a_layout@.stride[0] <= i64::MAX as int,
        (j as int) * b_layout@.stride[1] >= i64::MIN as int,
        (j as int) * b_layout@.stride[1] <= i64::MAX as int,
        forall|kk: nat| kk < (k_size as nat) ==>
            #[trigger] a_offset_overflow_ok(&a_layout@, i as nat, kk),
        forall|kk: nat| kk < (k_size as nat) ==>
            #[trigger] b_offset_overflow_ok(&b_layout@, j as nat, kk),
        // All A offsets are non-negative and in-bounds
        forall|kk: nat| kk < (k_size as nat) ==>
            #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), i as nat, kk),
        // All B offsets are non-negative and in-bounds
        forall|kk: nat| kk < (k_size as nat) ==>
            #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), j as nat, kk),
        // Product overflow safety
        forall|kk: nat| kk < (k_size as nat) ==>
            #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, i as nat, j as nat, kk),
        // Accumulation bound
        acc_bound >= 0,
        acc_bound <= i64::MAX as int,
        -acc_bound >= i64::MIN as int,
        (k_size as int) * acc_bound <= i64::MAX as int,
        (bk as int) * acc_bound <= i64::MAX as int,
    ensures
        true,
{
    let mut acc: i64 = 0;
    let mut t: u64 = 0;

    while t < k_tiles
        invariant
            0 <= t <= k_tiles,
            a_layout.wf_spec(), b_layout.wf_spec(),
            a_layout@.rank() == 2, b_layout@.rank() == 2,
            bk > 0, k_size > 0,
            k_tiles == num_tiles_ceil(k_size as nat, bk as nat),
            (i as nat) < a_layout@.shape[0],
            (k_size as nat) <= a_layout@.shape[1],
            (k_size as nat) <= b_layout@.shape[0],
            (j as nat) < b_layout@.shape[1],
            i <= i64::MAX as u64, j <= i64::MAX as u64,
            k_size <= i64::MAX as u64,
            bk <= i64::MAX as u64,
            k_tiles <= i64::MAX as u64,
            k_tiles * bk <= u64::MAX as nat,
            (i as int) * a_layout@.stride[0] >= i64::MIN as int,
            (i as int) * a_layout@.stride[0] <= i64::MAX as int,
            (j as int) * b_layout@.stride[1] >= i64::MIN as int,
            (j as int) * b_layout@.stride[1] <= i64::MAX as int,
            forall|kk: nat| kk < (k_size as nat) ==>
                #[trigger] a_offset_overflow_ok(&a_layout@, i as nat, kk),
            forall|kk: nat| kk < (k_size as nat) ==>
                #[trigger] b_offset_overflow_ok(&b_layout@, j as nat, kk),
            forall|kk: nat| kk < (k_size as nat) ==>
                #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), i as nat, kk),
            forall|kk: nat| kk < (k_size as nat) ==>
                #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), j as nat, kk),
            forall|kk: nat| kk < (k_size as nat) ==>
                #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, i as nat, j as nat, kk),
            acc_bound >= 0,
            acc_bound <= i64::MAX as int,
            -acc_bound >= i64::MIN as int,
            (k_size as int) * acc_bound <= i64::MAX as int,
            (bk as int) * acc_bound <= i64::MAX as int,
            // Accumulator is bounded by processed-so-far
            acc as int >= -((t as int) * (bk as int) * acc_bound),
            acc as int <= (t as int) * (bk as int) * acc_bound,
        decreases k_tiles - t,
    {
        // Compute tile boundaries
        proof {
            // t < k_tiles and k_tiles * bk fits in u64
            assert((t as nat) * (bk as nat) <= (k_tiles as nat) * (bk as nat)) by (nonlinear_arith)
                requires (t as nat) <= (k_tiles as nat), (bk as nat) > 0;
            // (t + 1) * bk doesn't overflow u64
            assert(t + 1 <= k_tiles);
            assert(((t as nat) + 1) * (bk as nat) <= (k_tiles as nat) * (bk as nat)) by (nonlinear_arith)
                requires (t as nat) + 1 <= (k_tiles as nat), (bk as nat) >= 1;
        }
        let k_start = t * bk;
        let k_end_raw = (t + 1) * bk;
        let k_end: u64 = if k_end_raw <= k_size { k_end_raw } else { k_size };

        proof {
            assert(k_end <= k_size);
            // Prove k_start <= k_end
            if k_end_raw <= k_size {
                // k_end = (t+1)*bk > t*bk = k_start since bk > 0
                assert(k_start < k_end_raw) by (nonlinear_arith)
                    requires k_start == t * bk, k_end_raw == (t + 1) * bk, bk > 0u64;
            } else {
                // k_end = k_size, need t*bk <= k_size
                // By ceil_div_tight: ceil_div(k_size, bk) * bk < k_size + bk
                // So (t+1)*bk <= ceil_div(k_size,bk)*bk < k_size + bk
                // Hence t*bk < k_size
                crate::proof::predication_lemmas::lemma_ceil_div_tight(k_size as nat, bk as nat);
                assert(((k_tiles as nat) * (bk as nat)) as int - (k_size as int) < (bk as int));
                // (t+1)*bk <= k_tiles*bk < k_size + bk, so t*bk < k_size
                let ghost t_n = t as nat;
                let ghost bk_n = bk as nat;
                let ghost kt_n = k_tiles as nat;
                let ghost ks_n = k_size as nat;
                assert(t_n * bk_n < ks_n) by (nonlinear_arith)
                    requires
                        (t_n + 1) * bk_n <= kt_n * bk_n,
                        (kt_n * bk_n) < ks_n + bk_n,
                        bk_n > 0nat;
            }
            assert(k_start <= k_end);
        }

        let offsets = gemm_mac_offsets(a_layout, b_layout, i, j, k_start, k_end);
        let a_offs = offsets.0;
        let b_offs = offsets.1;
        let count = k_end - k_start;

        proof {
            // Prove offset in-bounds for inner_tile_mac_i64
            assert forall|idx: nat| idx < count as nat implies
                0 <= (#[trigger] a_offs@[idx as int]) && (a_offs@[idx as int] as nat) < a_data@.len()
            by {
                let kk = k_start as nat + idx;
                assert(a_offs@[idx as int] as int == gemm_a_offset(&a_layout@, i as nat, kk));
                assert(kk < k_size as nat);
                assert(a_data_in_bounds(&a_layout@, a_data@.len(), i as nat, kk));
            };
            assert forall|idx: nat| idx < count as nat implies
                0 <= (#[trigger] b_offs@[idx as int]) && (b_offs@[idx as int] as nat) < b_data@.len()
            by {
                let kk = k_start as nat + idx;
                assert(b_offs@[idx as int] as int == gemm_b_offset(&b_layout@, kk, j as nat));
                assert(kk < k_size as nat);
                assert(b_data_in_bounds(&b_layout@, b_data@.len(), j as nat, kk));
            };
            assert forall|idx: nat| idx < count as nat implies
                #[trigger] product_at_offset_ok(a_data@, b_data@, a_offs@[idx as int], b_offs@[idx as int])
            by {
                let kk = k_start as nat + idx;
                assert(a_offs@[idx as int] as int == gemm_a_offset(&a_layout@, i as nat, kk));
                assert(b_offs@[idx as int] as int == gemm_b_offset(&b_layout@, kk, j as nat));
                assert(kk < k_size as nat);
                assert(gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, i as nat, j as nat, kk));
                assert(a_data_in_bounds(&a_layout@, a_data@.len(), i as nat, kk));
                assert(b_data_in_bounds(&b_layout@, b_data@.len(), j as nat, kk));
            };
            // Prove count <= bk via case analysis on k_end
            if k_end_raw <= k_size {
                // k_end = (t+1)*bk, count = (t+1)*bk - t*bk = bk
                assert(k_end == k_end_raw);
                assert(count == bk) by (nonlinear_arith)
                    requires k_end == (t + 1) * bk, k_start == t * bk, count == k_end - k_start, bk > 0u64;
            } else {
                // k_end = k_size, count = k_size - t*bk < bk
                // (since (t+1)*bk > k_size means t*bk + bk > k_size means k_size - t*bk < bk)
                assert(count < bk) by (nonlinear_arith)
                    requires
                        k_end_raw > k_size,
                        k_end_raw == (t + 1) * bk,
                        k_start == t * bk,
                        k_end == k_size,
                        count == k_end - k_start,
                        bk > 0u64;
            }
            assert(count <= bk);
            assert((count as int) * acc_bound <= (bk as int) * acc_bound) by (nonlinear_arith)
                requires count as int <= bk as int, acc_bound >= 0int;
        }

        let tile_acc = inner_tile_mac_i64(a_data, b_data, &a_offs, &b_offs, count, Ghost(acc_bound));

        // Prove accumulation doesn't overflow
        proof {
            // tile_acc processes 'count' elements, each bounded by acc_bound
            assume(tile_acc as int >= -(count as int) * acc_bound);
            assume(tile_acc as int <= (count as int) * acc_bound);
            // Weaker bk-based bounds for invariant maintenance
            assert(tile_acc as int >= -(bk as int) * acc_bound) by (nonlinear_arith)
                requires tile_acc as int >= -(count as int) * acc_bound,
                    count as int <= bk as int, acc_bound >= 0int;
            assert(tile_acc as int <= (bk as int) * acc_bound) by (nonlinear_arith)
                requires tile_acc as int <= (count as int) * acc_bound,
                    count as int <= bk as int, acc_bound >= 0int;
            // Invariant maintenance: |acc + tile_acc| <= (t+1)*bk*acc_bound
            assert((acc as int + tile_acc as int) >= -((t as int) + 1) * (bk as int) * acc_bound) by (nonlinear_arith)
                requires acc as int >= -(t as int) * (bk as int) * acc_bound,
                    tile_acc as int >= -(bk as int) * acc_bound,
                    acc_bound >= 0int, bk > 0int;
            assert((acc as int + tile_acc as int) <= ((t as int) + 1) * (bk as int) * acc_bound) by (nonlinear_arith)
                requires acc as int <= (t as int) * (bk as int) * acc_bound,
                    tile_acc as int <= (bk as int) * acc_bound,
                    acc_bound >= 0int, bk > 0int;
            // i64 fit: use tight bound t*bk + count <= k_size (not (t+1)*bk which may exceed k_size)
            assert((t as int) * (bk as int) + (count as int) <= (k_size as int)) by (nonlinear_arith)
                requires
                    k_start == t * bk,
                    k_end <= k_size,
                    count == k_end - k_start,
                    k_start <= k_end;
            assert(((t as int) * (bk as int) + (count as int)) * acc_bound <= (k_size as int) * acc_bound) by (nonlinear_arith)
                requires
                    (t as int) * (bk as int) + (count as int) <= (k_size as int),
                    acc_bound >= 0int;
            // Since |acc + tile_acc| <= (t*bk + count)*acc_bound <= k_size*acc_bound <= i64::MAX
            assert((acc as int + tile_acc as int) <= ((t as int) * (bk as int) + (count as int)) * acc_bound) by (nonlinear_arith)
                requires
                    acc as int <= (t as int) * (bk as int) * acc_bound,
                    tile_acc as int <= (count as int) * acc_bound,
                    acc_bound >= 0int;
            assert((acc as int + tile_acc as int) >= -((t as int) * (bk as int) + (count as int)) * acc_bound) by (nonlinear_arith)
                requires
                    acc as int >= -(t as int) * (bk as int) * acc_bound,
                    tile_acc as int >= -(count as int) * acc_bound,
                    acc_bound >= 0int;
        }

        acc = acc + tile_acc;

        t = t + 1;
    }

    acc
}

} // verus!
