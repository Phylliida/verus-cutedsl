use vstd::prelude::*;
use crate::layout::*;
use crate::gemm::*;
use crate::predication::*;
use super::layout::*;
use super::*;
use super::predication::num_tiles_ceil_exec;

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

/// A-stride row overflow ok: i * stride[0] fits in i64.
pub open spec fn a_row_stride_ok(
    a_layout: &LayoutSpec, i: nat,
) -> bool {
    &&& (i as int) * a_layout.stride[0] >= i64::MIN as int
    &&& (i as int) * a_layout.stride[0] <= i64::MAX as int
}

/// B-stride column overflow ok: j * stride[1] fits in i64.
pub open spec fn b_col_stride_ok(
    b_layout: &LayoutSpec, j: nat,
) -> bool {
    &&& (j as int) * b_layout.stride[1] >= i64::MIN as int
    &&& (j as int) * b_layout.stride[1] <= i64::MAX as int
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

/// Product magnitude bounded by given bound.
pub open spec fn product_bounded_at_offset(
    a_data: Seq<i64>, b_data: Seq<i64>,
    a_off: i64, b_off: i64,
    bound: int,
) -> bool {
    let av = a_data[a_off as int];
    let bv = b_data[b_off as int];
    &&& (av as int) * (bv as int) >= -bound
    &&& (av as int) * (bv as int) <= bound
}

/// Product magnitude bounded by given bound for GEMM data at index kk.
pub open spec fn gemm_product_bounded(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    a_data: Seq<i64>, b_data: Seq<i64>,
    i: nat, j: nat, kk: nat,
    bound: int,
) -> bool {
    let a_off = gemm_a_offset(a_layout, i, kk);
    let b_off = gemm_b_offset(b_layout, kk, j);
    let av = a_data[a_off];
    let bv = b_data[b_off];
    &&& (av as int) * (bv as int) >= -bound
    &&& (av as int) * (bv as int) <= bound
}

/// Sum of i64 products accessed through offset sequences.
pub open spec fn sum_int_products(
    a_data: Seq<i64>, b_data: Seq<i64>,
    a_offs: Seq<i64>, b_offs: Seq<i64>,
    count: nat,
) -> int
    decreases count,
{
    if count == 0 { 0 }
    else {
        sum_int_products(a_data, b_data, a_offs, b_offs, (count - 1) as nat)
        + (a_data[a_offs[(count - 1) as int] as int] as int)
          * (b_data[b_offs[(count - 1) as int] as int] as int)
    }
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
        // Each product magnitude bounded by acc_bound
        forall|idx: nat| idx < count as nat ==>
            #[trigger] product_bounded_at_offset(a_data@, b_data@, a_offsets@[idx as int], b_offsets@[idx as int], acc_bound),
        // Cumulative sum bound: all partial sums fit in i64
        acc_bound >= 0,
        acc_bound <= i64::MAX as int,
        -acc_bound >= i64::MIN as int,
        // Each partial sum magnitude is bounded by acc_bound
        count as int * acc_bound <= i64::MAX as int,
    ensures
        acc as int >= -(count as int) * acc_bound,
        acc as int <= (count as int) * acc_bound,
        acc as int == sum_int_products(a_data@, b_data@, a_offsets@, b_offsets@, count as nat),
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
            forall|k: nat| k < count as nat ==>
                #[trigger] product_bounded_at_offset(a_data@, b_data@, a_offsets@[k as int], b_offsets@[k as int], acc_bound),
            // Partial accumulator is bounded
            acc as int >= -(idx as int) * acc_bound,
            acc as int <= (idx as int) * acc_bound,
            // Functional correctness
            acc as int == sum_int_products(a_data@, b_data@, a_offsets@, b_offsets@, idx as nat),
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
        // Capture Vec lengths (usize) for cast identity proofs
        let a_len = a_data.len();
        let b_len = b_data.len();
        let a_off_len = a_offsets.len();
        let b_off_len = b_offsets.len();

        proof {
            // Bridge u64→usize: idx < count <= a_offsets@.len() = a_off_len (usize)
            assert((idx as int) < (a_off_len as int));
            assert((idx as usize) as int == idx as int);
            // Bridge i64→usize: a_off_i64 >= 0, a_off_i64 < a_len (usize)
            assert(a_off_i64 as int >= 0);
            assert((a_off_i64 as nat) < a_data@.len());
            assert((a_off_i64 as int) < (a_len as int));
            assert((a_off_i64 as usize) as int == a_off_i64 as int);
            assert(a_val == a_data@[a_off_i64 as int]);
            assert(b_off_i64 as int >= 0);
            assert((b_off_i64 as nat) < b_data@.len());
            assert((b_off_i64 as int) < (b_len as int));
            assert((b_off_i64 as usize) as int == b_off_i64 as int);
            assert(b_val == b_data@[b_off_i64 as int]);
            // Connect to spec-level offsets (now (idx as usize) as int == idx as int is known)
            assert(a_off_i64 as int == a_offsets@[idx as int] as int);
            assert(b_off_i64 as int == b_offsets@[idx as int] as int);
            // Product overflow from product_at_offset_ok
            assert(product_at_offset_ok(a_data@, b_data@, a_offsets@[idx as int], b_offsets@[idx as int]));
            // Product bound from product_bounded_at_offset
            assert(product_bounded_at_offset(a_data@, b_data@, a_offsets@[idx as int], b_offsets@[idx as int], acc_bound));
        }

        let prod = a_val * b_val;

        // Prove accumulation doesn't overflow:
        // |acc + prod| <= idx*bound + bound = (idx+1)*bound <= count*bound <= i64::MAX
        proof {

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
            // Prove acc + prod fits in i64
            assert(old_acc + prod as int <= i64::MAX as int) by (nonlinear_arith)
                requires
                    old_acc + prod as int <= (old_idx + 1) * acc_bound,
                    (old_idx + 1) * acc_bound <= count as int * acc_bound,
                    count as int * acc_bound <= i64::MAX as int;
            assert(old_acc + prod as int >= i64::MIN as int) by (nonlinear_arith)
                requires
                    old_acc + prod as int >= -(old_idx + 1) * acc_bound,
                    (old_idx + 1) * acc_bound <= count as int * acc_bound,
                    count as int * acc_bound <= i64::MAX as int,
                    acc_bound >= 0int;
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
        // Product bounded by acc_bound
        forall|kk: nat| kk < (k_size as nat) ==>
            #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, i as nat, j as nat, kk, acc_bound),
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
            forall|kk: nat| kk < (k_size as nat) ==>
                #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, i as nat, j as nat, kk, acc_bound),
            acc_bound >= 0,
            acc_bound <= i64::MAX as int,
            -acc_bound >= i64::MIN as int,
            (k_size as int) * acc_bound <= i64::MAX as int,
            (bk as int) * acc_bound <= i64::MAX as int,
            // Accumulator is bounded by processed-so-far
            acc as int >= -(t as int) * (bk as int) * acc_bound,
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
            assert forall|idx: nat| idx < count as nat implies
                #[trigger] product_bounded_at_offset(a_data@, b_data@, a_offs@[idx as int], b_offs@[idx as int], acc_bound)
            by {
                let kk = k_start as nat + idx;
                assert(a_offs@[idx as int] as int == gemm_a_offset(&a_layout@, i as nat, kk));
                assert(b_offs@[idx as int] as int == gemm_b_offset(&b_layout@, kk, j as nat));
                assert(kk < k_size as nat);
                assert(gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, i as nat, j as nat, kk, acc_bound));
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
            // tile_acc bounded by inner_tile_mac_i64's ensures
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
            // Prove acc + tile_acc fits in i64
            assert((acc as int + tile_acc as int) <= i64::MAX as int) by (nonlinear_arith)
                requires
                    (acc as int + tile_acc as int) <= ((t as int) * (bk as int) + (count as int)) * acc_bound,
                    ((t as int) * (bk as int) + (count as int)) * acc_bound <= (k_size as int) * acc_bound,
                    (k_size as int) * acc_bound <= i64::MAX as int;
            assert((acc as int + tile_acc as int) >= i64::MIN as int) by (nonlinear_arith)
                requires
                    (acc as int + tile_acc as int) >= -((t as int) * (bk as int) + (count as int)) * acc_bound,
                    ((t as int) * (bk as int) + (count as int)) * acc_bound <= (k_size as int) * acc_bound,
                    (k_size as int) * acc_bound <= i64::MAX as int,
                    acc_bound >= 0int;
        }

        acc = acc + tile_acc;

        t = t + 1;
    }

    acc
}

// ══════════════════════════════════════════════════════════════
// Epilogue: predicated store (Feature 3 Round 8)
// ══════════════════════════════════════════════════════════════

/// C offset overflow safety for tile element (ti, tj, ei, ej).
pub open spec fn c_tile_offset_overflow_ok(
    c_layout: &LayoutSpec,
    ti: nat, tj: nat, ei: nat, ej: nat,
    bm: nat, bn: nat,
) -> bool {
    let gi = ti * bm + ei;
    let gj = tj * bn + ej;
    &&& gi <= u64::MAX as nat
    &&& gj <= u64::MAX as nat
    &&& gi <= i64::MAX as nat
    &&& gj <= i64::MAX as nat
    &&& (gi as int) * c_layout.stride[0] >= i64::MIN as int
    &&& (gi as int) * c_layout.stride[0] <= i64::MAX as int
    &&& (gj as int) * c_layout.stride[1] >= i64::MIN as int
    &&& (gj as int) * c_layout.stride[1] <= i64::MAX as int
    &&& (gi as int) * c_layout.stride[0] + (gj as int) * c_layout.stride[1] >= i64::MIN as int
    &&& (gi as int) * c_layout.stride[0] + (gj as int) * c_layout.stride[1] <= i64::MAX as int
}

/// Write one accumulator value to C if (gi, gj) is within (m, n).
pub fn epilogue_predicated_store_exec(
    c_data: &mut Vec<i64>,
    c_layout: &RuntimeLayout,
    ti: u64, tj: u64, ei: u64, ej: u64,
    bm: u64, bn: u64,
    m: u64, n: u64,
    value: i64,
) -> (written: bool)
    requires
        c_layout.wf_spec(), c_layout@.rank() == 2,
        c_layout@.valid(), c_layout@.is_injective(),
        bm > 0, bn > 0,
        (ti as nat) * (bm as nat) + (ei as nat) <= u64::MAX as nat,
        (tj as nat) * (bn as nat) + (ej as nat) <= u64::MAX as nat,
        m as nat <= c_layout@.shape[0],
        n as nat <= c_layout@.shape[1],
        // If in-bounds, we need overflow safety and data bounds
        epilogue_predicated_store_safe(m as nat, n as nat,
            ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat)
            ==> c_tile_offset_overflow_ok(&c_layout@,
                    ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat),
        epilogue_predicated_store_safe(m as nat, n as nat,
            ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat)
            ==> epilogue_store_in_bounds(&c_layout@, old(c_data)@.len(),
                    ti as nat * bm as nat + ei as nat, tj as nat * bn as nat + ej as nat),
    ensures
        written == epilogue_predicated_store_safe(m as nat, n as nat,
            ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat),
        written ==> c_data@.len() == old(c_data)@.len(),
        written ==> c_data@[gemm_c_tile_offset(&c_layout@,
            ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat) as int]
            == value as int,
        // Frame: non-target indices unchanged
        written ==> forall|idx: int| 0 <= idx < c_data@.len()
            && idx != gemm_c_tile_offset(&c_layout@,
                ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat)
            ==> c_data@[idx] == old(c_data)@[idx],
        !written ==> c_data@ =~= old(c_data)@,
{
    let gi = ti * bm + ei;
    let gj = tj * bn + ej;

    if gi < m && gj < n {
        // Compute offset
        let off = gemm_c_tile_offset_exec(c_layout, ti, tj, ei, ej, bm, bn);

        proof {
            // off is in-bounds of c_data
            assert(epilogue_predicated_store_safe(m as nat, n as nat,
                ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat));
            assert(epilogue_store_in_bounds(&c_layout@, old(c_data)@.len(),
                gi as nat, gj as nat));
            assert(off as int == gemm_c_offset(&c_layout@, gi as nat, gj as nat));
            assert(off >= 0);
            assert((off as nat) < c_data@.len());
        }

        // Cast to usize for indexing
        let c_len = c_data.len();
        proof {
            assert((off as int) < (c_len as int));
            assert((off as usize) as int == off as int);
        }
        c_data.set(off as usize, value);

        true
    } else {
        false
    }
}

// ══════════════════════════════════════════════════════════════
// Epilogue: tile write loop (Feature 4 Round 8)
// ══════════════════════════════════════════════════════════════

/// C-offset overflow safety for all valid elements in a CTA tile.
pub open spec fn cta_tile_overflow_ok(
    c_layout: &LayoutSpec, m: nat, n: nat,
    bm: nat, bn: nat, ti: nat, tj: nat,
) -> bool {
    forall|ei: nat, ej: nat| ei < bm && ej < bn
        && epilogue_predicated_store_safe(m, n, ti, tj, ei, ej, bm, bn)
        ==> #[trigger] c_tile_offset_overflow_ok(c_layout, ti, tj, ei, ej, bm, bn)
}

/// Write all accumulated values for one CTA tile to C.
pub fn epilogue_tile_write(
    c_data: &mut Vec<i64>,
    c_layout: &RuntimeLayout,
    accumulators: &Vec<i64>,
    ti: u64, tj: u64,
    bm: u64, bn: u64,
    m: u64, n: u64,
)
    requires
        c_layout.wf_spec(), c_layout@.rank() == 2,
        c_layout@.valid(), c_layout@.is_injective(),
        c_layout@.non_negative_strides(),
        bm > 0, bn > 0,
        (bm as nat) * (bn as nat) <= usize::MAX as nat,
        accumulators@.len() == (bm as nat) * (bn as nat),
        m as nat <= c_layout@.shape[0],
        n as nat <= c_layout@.shape[1],
        // All valid stores are in-bounds
        epilogue_cta_correct(&c_layout@, old(c_data)@.len(),
            m as nat, n as nat, bm as nat, bn as nat, ti as nat, tj as nat),
        // Overflow safety for all valid elements
        cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
            bm as nat, bn as nat, ti as nat, tj as nat),
        // Tile index overflow
        (ti as nat) * (bm as nat) + (bm as nat) <= u64::MAX as nat,
        (tj as nat) * (bn as nat) + (bn as nat) <= u64::MAX as nat,
    ensures
        c_data@.len() == old(c_data)@.len(),
        // All valid elements written correctly
        forall|ei: nat, ej: nat| ei < bm as nat && ej < bn as nat
            && epilogue_predicated_store_safe(m as nat, n as nat,
                ti as nat, tj as nat, ei, ej, bm as nat, bn as nat)
            ==> #[trigger] c_data@[gemm_c_tile_offset(&c_layout@,
                    ti as nat, tj as nat, ei, ej, bm as nat, bn as nat) as int]
                == accumulators@[(ei * bn as nat + ej) as int],
{
    let mut ei: u64 = 0;

    while ei < bm
        invariant
            0 <= ei <= bm,
            c_data@.len() == old(c_data)@.len(),
            c_layout.wf_spec(), c_layout@.rank() == 2,
            c_layout@.valid(), c_layout@.is_injective(),
            c_layout@.non_negative_strides(),
            bm > 0, bn > 0,
            (bm as nat) * (bn as nat) <= usize::MAX as nat,
            accumulators@.len() == (bm as nat) * (bn as nat),
            m as nat <= c_layout@.shape[0],
            n as nat <= c_layout@.shape[1],
            epilogue_cta_correct(&c_layout@, c_data@.len(),
                m as nat, n as nat, bm as nat, bn as nat, ti as nat, tj as nat),
            cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
                bm as nat, bn as nat, ti as nat, tj as nat),
            (ti as nat) * (bm as nat) + (bm as nat) <= u64::MAX as nat,
            (tj as nat) * (bn as nat) + (bn as nat) <= u64::MAX as nat,
            // Previously written elements preserved
            forall|pi: nat, pj: nat| pi < ei as nat && pj < bn as nat
                && epilogue_predicated_store_safe(m as nat, n as nat,
                    ti as nat, tj as nat, pi, pj, bm as nat, bn as nat)
                ==> #[trigger] c_data@[gemm_c_tile_offset(&c_layout@,
                        ti as nat, tj as nat, pi, pj, bm as nat, bn as nat) as int]
                    == accumulators@[(pi * bn as nat + pj) as int],
        decreases bm - ei,
    {
        let mut ej: u64 = 0;

        while ej < bn
            invariant
                0 <= ej <= bn,
                0 <= ei < bm,
                c_data@.len() == old(c_data)@.len(),
                c_layout.wf_spec(), c_layout@.rank() == 2,
                c_layout@.valid(), c_layout@.is_injective(),
                c_layout@.non_negative_strides(),
                bm > 0, bn > 0,
                (bm as nat) * (bn as nat) <= usize::MAX as nat,
                accumulators@.len() == (bm as nat) * (bn as nat),
                m as nat <= c_layout@.shape[0],
                n as nat <= c_layout@.shape[1],
                epilogue_cta_correct(&c_layout@, c_data@.len(),
                    m as nat, n as nat, bm as nat, bn as nat, ti as nat, tj as nat),
                cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
                    bm as nat, bn as nat, ti as nat, tj as nat),
                (ti as nat) * (bm as nat) + (bm as nat) <= u64::MAX as nat,
                (tj as nat) * (bn as nat) + (bn as nat) <= u64::MAX as nat,
                // Previous rows preserved
                forall|pi: nat, pj: nat| pi < ei as nat && pj < bn as nat
                    && epilogue_predicated_store_safe(m as nat, n as nat,
                        ti as nat, tj as nat, pi, pj, bm as nat, bn as nat)
                    ==> #[trigger] c_data@[gemm_c_tile_offset(&c_layout@,
                            ti as nat, tj as nat, pi, pj, bm as nat, bn as nat) as int]
                        == accumulators@[(pi * bn as nat + pj) as int],
                // Current row, already-written columns preserved
                forall|pj: nat| pj < ej as nat
                    && epilogue_predicated_store_safe(m as nat, n as nat,
                        ti as nat, tj as nat, ei as nat, pj, bm as nat, bn as nat)
                    ==> c_data@[gemm_c_tile_offset(&c_layout@,
                            ti as nat, tj as nat, ei as nat, pj, bm as nat, bn as nat) as int]
                        == accumulators@[(ei as nat * bn as nat + pj) as int],
            decreases bn - ej,
        {
            // Accumulator index — prove overflow safety first
            proof {
                let ei_n = ei as nat;
                let ej_n = ej as nat;
                let bm_n = bm as nat;
                let bn_n = bn as nat;
                assert(ei_n * bn_n + ej_n < bm_n * bn_n) by (nonlinear_arith)
                    requires ei_n < bm_n, ej_n < bn_n, bm_n > 0, bn_n > 0;
                // bm * bn <= usize::MAX <= u64::MAX, so ei*bn+ej < bm*bn fits
            }
            let acc_idx = ei * bn + ej;
            let acc_len = accumulators.len();
            proof {
                assert((acc_idx as int) < (acc_len as int));
                assert((acc_idx as usize) as int == acc_idx as int);
            }
            let value = accumulators[acc_idx as usize];

            proof {
                // Set up preconditions for predicated store
                let ti_n = ti as nat;
                let tj_n = tj as nat;
                let ei_n = ei as nat;
                let ej_n = ej as nat;
                let bm_n = bm as nat;
                let bn_n = bn as nat;
                assert(ti_n * bm_n + ei_n <= u64::MAX as nat) by (nonlinear_arith)
                    requires ti_n * bm_n + bm_n <= u64::MAX as nat, ei_n < bm_n;
                assert(tj_n * bn_n + ej_n <= u64::MAX as nat) by (nonlinear_arith)
                    requires tj_n * bn_n + bn_n <= u64::MAX as nat, ej_n < bn_n;
                // Trigger overflow check
                assert(epilogue_predicated_store_safe(m as nat, n as nat,
                    ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat)
                    ==> c_tile_offset_overflow_ok(&c_layout@,
                        ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat));
            }

            // Snapshot c_data before write for frame reasoning
            let ghost c_before = c_data@;

            let written = epilogue_predicated_store_exec(
                c_data, c_layout, ti, tj, ei, ej, bm, bn, m, n, value,
            );

            proof {
                // Prove previously written values are preserved
                if written {
                    let off_new = gemm_c_tile_offset(&c_layout@,
                        ti as nat, tj as nat, ei as nat, ej as nat, bm as nat, bn as nat);

                    // Previous rows: their offsets differ from off_new
                    assert forall|pi: nat, pj: nat| pi < ei as nat && pj < bn as nat
                        && epilogue_predicated_store_safe(m as nat, n as nat,
                            ti as nat, tj as nat, pi, pj, bm as nat, bn as nat)
                    implies #[trigger] c_data@[gemm_c_tile_offset(&c_layout@,
                            ti as nat, tj as nat, pi, pj, bm as nat, bn as nat) as int]
                        == accumulators@[(pi * bn as nat + pj) as int]
                    by {
                        let off_old = gemm_c_tile_offset(&c_layout@,
                            ti as nat, tj as nat, pi, pj, bm as nat, bn as nat);
                        // pi != ei, so different offsets
                        crate::proof::gemm_lemmas::lemma_epilogue_intra_cta_disjoint(
                            &c_layout@, m as nat, n as nat, bm as nat, bn as nat,
                            ti as nat, tj as nat,
                            pi, pj, ei as nat, ej as nat,
                        );
                        assert(off_old != off_new);
                        assert(c_data@[off_old as int] == c_before[off_old as int]);
                    };

                    // Current row, already-written columns: pj < ej, so different offsets
                    assert forall|pj: nat| pj < ej as nat
                        && epilogue_predicated_store_safe(m as nat, n as nat,
                            ti as nat, tj as nat, ei as nat, pj, bm as nat, bn as nat)
                    implies c_data@[gemm_c_tile_offset(&c_layout@,
                            ti as nat, tj as nat, ei as nat, pj, bm as nat, bn as nat) as int]
                        == accumulators@[(ei as nat * bn as nat + pj) as int]
                    by {
                        let off_old = gemm_c_tile_offset(&c_layout@,
                            ti as nat, tj as nat, ei as nat, pj, bm as nat, bn as nat);
                        // pj != ej, so different offsets
                        crate::proof::gemm_lemmas::lemma_epilogue_intra_cta_disjoint(
                            &c_layout@, m as nat, n as nat, bm as nat, bn as nat,
                            ti as nat, tj as nat,
                            ei as nat, pj, ei as nat, ej as nat,
                        );
                        assert(off_old != off_new);
                        assert(c_data@[off_old as int] == c_before[off_old as int]);
                    };

                    // epilogue_cta_correct preserved (c_data.len() unchanged)
                } else {
                    // c_data unchanged, nothing to prove
                }
            }

            ej = ej + 1;
        }

        ei = ei + 1;
    }
}

// ══════════════════════════════════════════════════════════════
// GEMM CTA kernel (Feature 5 Round 8)
// ══════════════════════════════════════════════════════════════

/// Compute and store one CTA tile's output: K-reduction + epilogue.
pub fn gemm_cta_kernel(
    a_layout: &RuntimeLayout, b_layout: &RuntimeLayout, c_layout: &RuntimeLayout,
    a_data: &Vec<i64>, b_data: &Vec<i64>, c_data: &mut Vec<i64>,
    ti: u64, tj: u64,
    m: u64, n: u64, k_size: u64,
    bm: u64, bn: u64, bk: u64,
    k_tiles: u64,
    Ghost(acc_bound): Ghost<int>,
)
    requires
        // Layout well-formedness
        a_layout.wf_spec(), b_layout.wf_spec(), c_layout.wf_spec(),
        a_layout@.rank() == 2, b_layout@.rank() == 2, c_layout@.rank() == 2,
        c_layout@.valid(), c_layout@.is_injective(), c_layout@.non_negative_strides(),
        // Tile sizes
        bm > 0, bn > 0, bk > 0, k_size > 0,
        k_tiles == num_tiles_ceil(k_size as nat, bk as nat),
        // Shape bounds
        m as nat <= a_layout@.shape[0],
        k_size as nat <= a_layout@.shape[1],
        k_size as nat <= b_layout@.shape[0],
        n as nat <= b_layout@.shape[1],
        m as nat <= c_layout@.shape[0],
        n as nat <= c_layout@.shape[1],
        // Overflow bounds
        (bm as nat) * (bn as nat) <= usize::MAX as nat,
        (bm as nat) * (bn as nat) <= u64::MAX as nat,
        (ti as nat) * (bm as nat) + (bm as nat) <= u64::MAX as nat,
        (tj as nat) * (bn as nat) + (bn as nat) <= u64::MAX as nat,
        // Global index fits in i64 (for gemm_k_tile_loop)
        (ti as nat) * (bm as nat) + (bm as nat) <= i64::MAX as nat,
        (tj as nat) * (bn as nat) + (bn as nat) <= i64::MAX as nat,
        k_tiles <= i64::MAX as u64,
        k_tiles * bk <= u64::MAX as nat,
        k_size <= i64::MAX as u64,
        bk <= i64::MAX as u64,
        // A/B offset overflow for all k in this CTA's range
        forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
            #[trigger] a_offset_overflow_ok(&a_layout@, gi, kk),
        forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
            #[trigger] b_offset_overflow_ok(&b_layout@, gj, kk),
        // A/B data in bounds
        forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
            #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi, kk),
        forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
            #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj, kk),
        // Product overflow & boundedness
        forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
            #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk),
        forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
            #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk, acc_bound),
        // Accumulation bound
        acc_bound >= 0,
        acc_bound <= i64::MAX as int,
        -acc_bound >= i64::MIN as int,
        (k_size as int) * acc_bound <= i64::MAX as int,
        (bk as int) * acc_bound <= i64::MAX as int,
        // A/B stride overflow for individual indices
        forall|gi: nat| gi < m as nat ==>
            #[trigger] a_row_stride_ok(&a_layout@, gi),
        forall|gj: nat| gj < n as nat ==>
            #[trigger] b_col_stride_ok(&b_layout@, gj),
        // Epilogue safety
        epilogue_cta_correct(&c_layout@, old(c_data)@.len(),
            m as nat, n as nat, bm as nat, bn as nat, ti as nat, tj as nat),
        // C offset overflow safety
        cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
            bm as nat, bn as nat, ti as nat, tj as nat),
    ensures
        c_data@.len() == old(c_data)@.len(),
{
    // Step 1: Allocate accumulators
    let acc_size: u64 = bm * bn;
    let mut accumulators: Vec<i64> = Vec::new();
    let mut init_idx: u64 = 0;
    while init_idx < acc_size
        invariant
            0 <= init_idx <= acc_size,
            acc_size == bm * bn,
            accumulators@.len() == init_idx as nat,
            forall|k: nat| k < init_idx as nat ==> accumulators@[k as int] == 0i64,
        decreases acc_size - init_idx,
    {
        accumulators.push(0i64);
        init_idx = init_idx + 1;
    }

    // Step 2: Compute MAC for each (ei, ej) and store in accumulators
    let mut ei: u64 = 0;
    while ei < bm
        invariant
            0 <= ei <= bm,
            bm > 0, bn > 0, bk > 0, k_size > 0,
            acc_size == bm * bn,
            accumulators@.len() == (bm as nat) * (bn as nat),
            a_layout.wf_spec(), b_layout.wf_spec(),
            a_layout@.rank() == 2, b_layout@.rank() == 2,
            k_tiles == num_tiles_ceil(k_size as nat, bk as nat),
            m as nat <= a_layout@.shape[0],
            k_size as nat <= a_layout@.shape[1],
            k_size as nat <= b_layout@.shape[0],
            n as nat <= b_layout@.shape[1],
            (bm as nat) * (bn as nat) <= usize::MAX as nat,
            (ti as nat) * (bm as nat) + (bm as nat) <= u64::MAX as nat,
            (tj as nat) * (bn as nat) + (bn as nat) <= u64::MAX as nat,
            (ti as nat) * (bm as nat) + (bm as nat) <= i64::MAX as nat,
            (tj as nat) * (bn as nat) + (bn as nat) <= i64::MAX as nat,
            k_tiles <= i64::MAX as u64,
            k_tiles * bk <= u64::MAX as nat,
            k_size <= i64::MAX as u64,
            bk <= i64::MAX as u64,
            forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                #[trigger] a_offset_overflow_ok(&a_layout@, gi, kk),
            forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                #[trigger] b_offset_overflow_ok(&b_layout@, gj, kk),
            forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi, kk),
            forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj, kk),
            forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk),
            forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk, acc_bound),
            acc_bound >= 0,
            acc_bound <= i64::MAX as int,
            -acc_bound >= i64::MIN as int,
            (k_size as int) * acc_bound <= i64::MAX as int,
            (bk as int) * acc_bound <= i64::MAX as int,
            forall|gi: nat| gi < m as nat ==>
                #[trigger] a_row_stride_ok(&a_layout@, gi),
            forall|gj: nat| gj < n as nat ==>
                #[trigger] b_col_stride_ok(&b_layout@, gj),
        decreases bm - ei,
    {
        let mut ej: u64 = 0;
        while ej < bn
            invariant
                0 <= ej <= bn,
                0 <= ei < bm,
                bm > 0, bn > 0, bk > 0, k_size > 0,
                acc_size == bm * bn,
                accumulators@.len() == (bm as nat) * (bn as nat),
                a_layout.wf_spec(), b_layout.wf_spec(),
                a_layout@.rank() == 2, b_layout@.rank() == 2,
                k_tiles == num_tiles_ceil(k_size as nat, bk as nat),
                m as nat <= a_layout@.shape[0],
                k_size as nat <= a_layout@.shape[1],
                k_size as nat <= b_layout@.shape[0],
                n as nat <= b_layout@.shape[1],
                (bm as nat) * (bn as nat) <= usize::MAX as nat,
                (ti as nat) * (bm as nat) + (bm as nat) <= u64::MAX as nat,
                (tj as nat) * (bn as nat) + (bn as nat) <= u64::MAX as nat,
                (ti as nat) * (bm as nat) + (bm as nat) <= i64::MAX as nat,
                (tj as nat) * (bn as nat) + (bn as nat) <= i64::MAX as nat,
                k_tiles <= i64::MAX as u64,
                k_tiles * bk <= u64::MAX as nat,
                k_size <= i64::MAX as u64,
                bk <= i64::MAX as u64,
                forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                    #[trigger] a_offset_overflow_ok(&a_layout@, gi, kk),
                forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                    #[trigger] b_offset_overflow_ok(&b_layout@, gj, kk),
                forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                    #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi, kk),
                forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                    #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj, kk),
                forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                    #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk),
                forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                    #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk, acc_bound),
                acc_bound >= 0,
                acc_bound <= i64::MAX as int,
                -acc_bound >= i64::MIN as int,
                (k_size as int) * acc_bound <= i64::MAX as int,
                (bk as int) * acc_bound <= i64::MAX as int,
                forall|gi: nat| gi < m as nat ==>
                    #[trigger] a_row_stride_ok(&a_layout@, gi),
                forall|gj: nat| gj < n as nat ==>
                    #[trigger] b_col_stride_ok(&b_layout@, gj),
            decreases bn - ej,
        {
            let gi = ti * bm + ei;
            let gj = tj * bn + ej;

            proof {
                let ti_n = ti as nat;
                let tj_n = tj as nat;
                let ei_n = ei as nat;
                let ej_n = ej as nat;
                let bm_n = bm as nat;
                let bn_n = bn as nat;
                assert(ti_n * bm_n + ei_n <= u64::MAX as nat) by (nonlinear_arith)
                    requires ti_n * bm_n + bm_n <= u64::MAX as nat, ei_n < bm_n;
                assert(tj_n * bn_n + ej_n <= u64::MAX as nat) by (nonlinear_arith)
                    requires tj_n * bn_n + bn_n <= u64::MAX as nat, ej_n < bn_n;
            }

            if gi < m && gj < n {
                proof {
                    let gi_n = gi as nat;
                    let gj_n = gj as nat;
                    assert(gi_n < m as nat);
                    assert(gj_n < n as nat);

                    // Bridge stride overflow
                    assert(a_row_stride_ok(&a_layout@, gi_n));
                    assert(b_col_stride_ok(&b_layout@, gj_n));

                    // gi <= i64::MAX and gj <= i64::MAX
                    assert(gi_n < (ti as nat) * (bm as nat) + (bm as nat)) by (nonlinear_arith)
                        requires gi_n == (ti as nat) * (bm as nat) + (ei as nat), (ei as nat) < (bm as nat);
                    assert(gj_n < (tj as nat) * (bn as nat) + (bn as nat)) by (nonlinear_arith)
                        requires gj_n == (tj as nat) * (bn as nat) + (ej as nat), (ej as nat) < (bn as nat);

                    // gi < a_layout@.shape[0] (since gi < m <= shape[0])
                    assert(gi_n < a_layout@.shape[0]);
                    // gj < b_layout@.shape[1] (since gj < n <= shape[1])
                    assert(gj_n < b_layout@.shape[1]);

                    // Instantiate per-kk quantifiers for this specific gi, gj
                    assert forall|kk: nat| kk < k_size as nat implies
                        #[trigger] a_offset_overflow_ok(&a_layout@, gi_n, kk)
                    by {
                        assert(a_offset_overflow_ok(&a_layout@, gi_n, kk));
                    };
                    assert forall|kk: nat| kk < k_size as nat implies
                        #[trigger] b_offset_overflow_ok(&b_layout@, gj_n, kk)
                    by {
                        assert(b_offset_overflow_ok(&b_layout@, gj_n, kk));
                    };
                    assert forall|kk: nat| kk < k_size as nat implies
                        #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi_n, kk)
                    by {
                        assert(a_data_in_bounds(&a_layout@, a_data@.len(), gi_n, kk));
                    };
                    assert forall|kk: nat| kk < k_size as nat implies
                        #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj_n, kk)
                    by {
                        assert(b_data_in_bounds(&b_layout@, b_data@.len(), gj_n, kk));
                    };
                    assert forall|kk: nat| kk < k_size as nat implies
                        #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi_n, gj_n, kk)
                    by {
                        assert(gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi_n, gj_n, kk));
                    };
                    assert forall|kk: nat| kk < k_size as nat implies
                        #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi_n, gj_n, kk, acc_bound)
                    by {
                        assert(gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi_n, gj_n, kk, acc_bound));
                    };
                }
                let mac_val = gemm_k_tile_loop(
                    a_layout, b_layout, a_data, b_data,
                    gi, gj, k_tiles, bk, k_size, Ghost(acc_bound),
                );

                // Prove overflow safety for accumulator index
                proof {
                    let ei_n = ei as nat;
                    let ej_n = ej as nat;
                    let bm_n = bm as nat;
                    let bn_n = bn as nat;
                    assert(ei_n * bn_n + ej_n < bm_n * bn_n) by (nonlinear_arith)
                        requires ei_n < bm_n, ej_n < bn_n, bm_n > 0, bn_n > 0;
                }
                let acc_idx = ei * bn + ej;
                let acc_len = accumulators.len();
                proof {
                    assert((acc_idx as int) < (acc_len as int));
                    assert((acc_idx as usize) as int == acc_idx as int);
                }
                accumulators.set(acc_idx as usize, mac_val);
            }

            ej = ej + 1;
        }

        ei = ei + 1;
    }

    // Step 3: Write accumulators to C
    epilogue_tile_write(c_data, c_layout, &accumulators, ti, tj, bm, bn, m, n);
}

// ══════════════════════════════════════════════════════════════
// Multi-CTA Dispatch (Feature 2 Round 9)
// ══════════════════════════════════════════════════════════════

/// Multi-CTA GEMM dispatch: loop over all (ti, tj) tiles, calling gemm_cta_kernel for each.
pub fn gemm_dispatch(
    a_layout: &RuntimeLayout, b_layout: &RuntimeLayout, c_layout: &RuntimeLayout,
    a_data: &Vec<i64>, b_data: &Vec<i64>, c_data: &mut Vec<i64>,
    m: u64, n: u64, k_size: u64,
    bm: u64, bn: u64, bk: u64,
    Ghost(acc_bound): Ghost<int>,
)
    requires
        // Layout well-formedness
        a_layout.wf_spec(), b_layout.wf_spec(), c_layout.wf_spec(),
        a_layout@.rank() == 2, b_layout@.rank() == 2, c_layout@.rank() == 2,
        c_layout@.valid(), c_layout@.is_injective(), c_layout@.non_negative_strides(),
        // Tile sizes
        bm > 0, bn > 0, bk > 0, k_size > 0,
        // Shape bounds
        m as nat <= a_layout@.shape[0], k_size as nat <= a_layout@.shape[1],
        k_size as nat <= b_layout@.shape[0], n as nat <= b_layout@.shape[1],
        m as nat <= c_layout@.shape[0], n as nat <= c_layout@.shape[1],
        // Tile/overflow bounds
        (bm as nat) * (bn as nat) <= usize::MAX as nat,
        (bm as nat) * (bn as nat) <= u64::MAX as nat,
        m as nat + bm as nat <= u64::MAX as nat,
        n as nat + bn as nat <= u64::MAX as nat,
        m as nat + bm as nat <= i64::MAX as nat,
        n as nat + bn as nat <= i64::MAX as nat,
        k_size as nat + bk as nat - 1 <= u64::MAX as nat,
        k_size <= i64::MAX as u64,
        bk <= i64::MAX as u64,
        // A/B offset overflow for all valid indices
        forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
            #[trigger] a_offset_overflow_ok(&a_layout@, gi, kk),
        forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
            #[trigger] b_offset_overflow_ok(&b_layout@, gj, kk),
        // A/B data in bounds
        forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
            #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi, kk),
        forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
            #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj, kk),
        // Product overflow & boundedness
        forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
            #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk),
        forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
            #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk, acc_bound),
        // Accumulation bound
        acc_bound >= 0, acc_bound <= i64::MAX as int, -acc_bound >= i64::MIN as int,
        (k_size as int) * acc_bound <= i64::MAX as int,
        (bk as int) * acc_bound <= i64::MAX as int,
        // Stride overflow
        forall|gi: nat| gi < m as nat ==> #[trigger] a_row_stride_ok(&a_layout@, gi),
        forall|gj: nat| gj < n as nat ==> #[trigger] b_col_stride_ok(&b_layout@, gj),
        // C tensor validity
        tensor_valid(&TensorSpec { layout: c_layout@, data_size: old(c_data)@.len() }),
        // C offset overflow for ALL tiles
        forall|ti: nat, tj: nat| ti < num_tiles_ceil(m as nat, bm as nat)
            && tj < num_tiles_ceil(n as nat, bn as nat) ==>
            #[trigger] cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
                bm as nat, bn as nat, ti, tj),
        // k_tiles overflow
        num_tiles_ceil(k_size as nat, bk as nat) <= i64::MAX as nat,
        num_tiles_ceil(k_size as nat, bk as nat) * (bk as nat) <= u64::MAX as nat,
    ensures
        c_data@.len() == old(c_data)@.len(),
{
    let k_tiles = num_tiles_ceil_exec(k_size, bk);
    let m_tiles = num_tiles_ceil_exec(m, bm);
    let n_tiles = num_tiles_ceil_exec(n, bn);

    proof {
        // Prove m_tiles and n_tiles fit in u64 (they already do from num_tiles_ceil_exec)
        // Prove k_tiles matches spec
        assert(k_tiles as nat == num_tiles_ceil(k_size as nat, bk as nat));
    }

    let mut ti: u64 = 0;
    while ti < m_tiles
        invariant
            0 <= ti <= m_tiles,
            m_tiles as nat == num_tiles_ceil(m as nat, bm as nat),
            n_tiles as nat == num_tiles_ceil(n as nat, bn as nat),
            k_tiles as nat == num_tiles_ceil(k_size as nat, bk as nat),
            c_data@.len() == old(c_data)@.len(),
            // Re-state all requires for gemm_cta_kernel
            a_layout.wf_spec(), b_layout.wf_spec(), c_layout.wf_spec(),
            a_layout@.rank() == 2, b_layout@.rank() == 2, c_layout@.rank() == 2,
            c_layout@.valid(), c_layout@.is_injective(), c_layout@.non_negative_strides(),
            bm > 0, bn > 0, bk > 0, k_size > 0,
            m as nat <= a_layout@.shape[0], k_size as nat <= a_layout@.shape[1],
            k_size as nat <= b_layout@.shape[0], n as nat <= b_layout@.shape[1],
            m as nat <= c_layout@.shape[0], n as nat <= c_layout@.shape[1],
            (bm as nat) * (bn as nat) <= usize::MAX as nat,
            (bm as nat) * (bn as nat) <= u64::MAX as nat,
            m as nat + bm as nat <= u64::MAX as nat,
            n as nat + bn as nat <= u64::MAX as nat,
            m as nat + bm as nat <= i64::MAX as nat,
            n as nat + bn as nat <= i64::MAX as nat,
            forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                #[trigger] a_offset_overflow_ok(&a_layout@, gi, kk),
            forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                #[trigger] b_offset_overflow_ok(&b_layout@, gj, kk),
            forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi, kk),
            forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj, kk),
            forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk),
            forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk, acc_bound),
            acc_bound >= 0, acc_bound <= i64::MAX as int, -acc_bound >= i64::MIN as int,
            (k_size as int) * acc_bound <= i64::MAX as int,
            (bk as int) * acc_bound <= i64::MAX as int,
            forall|gi: nat| gi < m as nat ==> #[trigger] a_row_stride_ok(&a_layout@, gi),
            forall|gj: nat| gj < n as nat ==> #[trigger] b_col_stride_ok(&b_layout@, gj),
            tensor_valid(&TensorSpec { layout: c_layout@, data_size: c_data@.len() }),
            forall|ti2: nat, tj2: nat| ti2 < num_tiles_ceil(m as nat, bm as nat)
                && tj2 < num_tiles_ceil(n as nat, bn as nat) ==>
                #[trigger] cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
                    bm as nat, bn as nat, ti2, tj2),
            k_tiles as nat <= i64::MAX as nat,
            k_tiles as nat * (bk as nat) <= u64::MAX as nat,
            k_size <= i64::MAX as u64,
            bk <= i64::MAX as u64,
        decreases m_tiles - ti,
    {
        let mut tj: u64 = 0;
        while tj < n_tiles
            invariant
                0 <= tj <= n_tiles,
                0 <= ti < m_tiles,
                m_tiles as nat == num_tiles_ceil(m as nat, bm as nat),
                n_tiles as nat == num_tiles_ceil(n as nat, bn as nat),
                k_tiles as nat == num_tiles_ceil(k_size as nat, bk as nat),
                c_data@.len() == old(c_data)@.len(),
                a_layout.wf_spec(), b_layout.wf_spec(), c_layout.wf_spec(),
                a_layout@.rank() == 2, b_layout@.rank() == 2, c_layout@.rank() == 2,
                c_layout@.valid(), c_layout@.is_injective(), c_layout@.non_negative_strides(),
                bm > 0, bn > 0, bk > 0, k_size > 0,
                m as nat <= a_layout@.shape[0], k_size as nat <= a_layout@.shape[1],
                k_size as nat <= b_layout@.shape[0], n as nat <= b_layout@.shape[1],
                m as nat <= c_layout@.shape[0], n as nat <= c_layout@.shape[1],
                (bm as nat) * (bn as nat) <= usize::MAX as nat,
                (bm as nat) * (bn as nat) <= u64::MAX as nat,
                m as nat + bm as nat <= u64::MAX as nat,
                n as nat + bn as nat <= u64::MAX as nat,
                m as nat + bm as nat <= i64::MAX as nat,
                n as nat + bn as nat <= i64::MAX as nat,
                forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                    #[trigger] a_offset_overflow_ok(&a_layout@, gi, kk),
                forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                    #[trigger] b_offset_overflow_ok(&b_layout@, gj, kk),
                forall|gi: nat, kk: nat| gi < m as nat && kk < k_size as nat ==>
                    #[trigger] a_data_in_bounds(&a_layout@, a_data@.len(), gi, kk),
                forall|gj: nat, kk: nat| gj < n as nat && kk < k_size as nat ==>
                    #[trigger] b_data_in_bounds(&b_layout@, b_data@.len(), gj, kk),
                forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                    #[trigger] gemm_product_ok(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk),
                forall|gi: nat, gj: nat, kk: nat| gi < m as nat && gj < n as nat && kk < k_size as nat ==>
                    #[trigger] gemm_product_bounded(&a_layout@, &b_layout@, a_data@, b_data@, gi, gj, kk, acc_bound),
                acc_bound >= 0, acc_bound <= i64::MAX as int, -acc_bound >= i64::MIN as int,
                (k_size as int) * acc_bound <= i64::MAX as int,
                (bk as int) * acc_bound <= i64::MAX as int,
                forall|gi: nat| gi < m as nat ==> #[trigger] a_row_stride_ok(&a_layout@, gi),
                forall|gj: nat| gj < n as nat ==> #[trigger] b_col_stride_ok(&b_layout@, gj),
                tensor_valid(&TensorSpec { layout: c_layout@, data_size: c_data@.len() }),
                forall|ti2: nat, tj2: nat| ti2 < num_tiles_ceil(m as nat, bm as nat)
                    && tj2 < num_tiles_ceil(n as nat, bn as nat) ==>
                    #[trigger] cta_tile_overflow_ok(&c_layout@, m as nat, n as nat,
                        bm as nat, bn as nat, ti2, tj2),
                k_tiles as nat <= i64::MAX as nat,
                k_tiles as nat * (bk as nat) <= u64::MAX as nat,
                k_size <= i64::MAX as u64,
                bk <= i64::MAX as u64,
            decreases n_tiles - tj,
        {
            proof {
                // Prove tile index overflow bounds
                // ti < ceil(m/bm), so ti*bm < m + bm (by ceil_div_tight)
                crate::proof::predication_lemmas::lemma_ceil_div_tight(m as nat, bm as nat);
                // ceil(m/bm) * bm < m + bm, so ti * bm <= ceil(m/bm)*bm - bm < m
                // Actually: ti * bm + bm <= ceil(m/bm) * bm < m + bm
                let ti_n = ti as nat;
                let tj_n = tj as nat;
                let bm_n = bm as nat;
                let bn_n = bn as nat;
                let m_n = m as nat;
                let n_n = n as nat;
                let mt_n = m_tiles as nat;
                let nt_n = n_tiles as nat;

                // ti < m_tiles = ceil(m/bm), so (ti+1) <= ceil(m/bm)
                // (ti+1)*bm <= ceil(m/bm)*bm < m + bm
                assert((ti_n + 1) * bm_n <= mt_n * bm_n) by (nonlinear_arith)
                    requires ti_n + 1 <= mt_n, bm_n >= 1;
                assert(mt_n * bm_n < m_n + bm_n) by {
                    crate::proof::predication_lemmas::lemma_ceil_div_tight(m_n, bm_n);
                };
                assert(ti_n * bm_n + bm_n <= u64::MAX as nat) by (nonlinear_arith)
                    requires (ti_n + 1) * bm_n <= mt_n * bm_n,
                        mt_n * bm_n < m_n + bm_n,
                        m_n + bm_n <= u64::MAX as nat;
                assert(ti_n * bm_n + bm_n <= i64::MAX as nat) by (nonlinear_arith)
                    requires (ti_n + 1) * bm_n <= mt_n * bm_n,
                        mt_n * bm_n < m_n + bm_n,
                        m_n + bm_n <= i64::MAX as nat;

                crate::proof::predication_lemmas::lemma_ceil_div_tight(n_n, bn_n);
                assert((tj_n + 1) * bn_n <= nt_n * bn_n) by (nonlinear_arith)
                    requires tj_n + 1 <= nt_n, bn_n >= 1;
                assert(nt_n * bn_n < n_n + bn_n) by {
                    crate::proof::predication_lemmas::lemma_ceil_div_tight(n_n, bn_n);
                };
                assert(tj_n * bn_n + bn_n <= u64::MAX as nat) by (nonlinear_arith)
                    requires (tj_n + 1) * bn_n <= nt_n * bn_n,
                        nt_n * bn_n < n_n + bn_n,
                        n_n + bn_n <= u64::MAX as nat;
                assert(tj_n * bn_n + bn_n <= i64::MAX as nat) by (nonlinear_arith)
                    requires (tj_n + 1) * bn_n <= nt_n * bn_n,
                        nt_n * bn_n < n_n + bn_n,
                        n_n + bn_n <= i64::MAX as nat;

                // Prove epilogue_cta_correct for this tile
                crate::proof::gemm_lemmas::lemma_epilogue_cta_correct(
                    &c_layout@, c_data@.len(),
                    m_n, n_n, bm_n, bn_n, ti_n, tj_n,
                );

                // Trigger cta_tile_overflow_ok
                assert(cta_tile_overflow_ok(&c_layout@, m_n, n_n, bm_n, bn_n, ti_n, tj_n));
            }

            gemm_cta_kernel(
                a_layout, b_layout, c_layout,
                a_data, b_data, c_data,
                ti, tj, m, n, k_size,
                bm, bn, bk, k_tiles,
                Ghost(acc_bound),
            );

            tj = tj + 1;
        }

        ti = ti + 1;
    }
}

// ══════════════════════════════════════════════════════════════
// Copy Pipeline Runtime (Feature 3 Round 9)
// ══════════════════════════════════════════════════════════════

/// G2S copy precondition helper: all offset/data overflow conditions for in-range elements.
pub open spec fn g2s_element_ok(
    src_layout: &LayoutSpec, src_data_len: nat,
    gi: nat, gj: nat,
) -> bool {
    &&& gi <= i64::MAX as nat
    &&& gj <= i64::MAX as nat
    &&& a_offset_overflow_ok(src_layout, gi, gj)
    &&& a_data_in_bounds(src_layout, src_data_len, gi, gj)
}

/// Copy a tile from global memory into a flat shared-memory buffer.
/// Elements outside global bounds are zero-filled (boundary tile predication).
pub fn g2s_copy_tile_exec(
    src_data: &Vec<i64>,
    src_layout: &RuntimeLayout,
    dst_buf: &mut Vec<i64>,
    tile_row_start: u64, tile_col_start: u64,
    tile_rows: u64, tile_cols: u64,
    global_rows: u64, global_cols: u64,
)
    requires
        src_layout.wf_spec(), src_layout@.rank() == 2,
        old(dst_buf)@.len() == (tile_rows as nat) * (tile_cols as nat),
        global_rows as nat <= src_layout@.shape[0],
        global_cols as nat <= src_layout@.shape[1],
        tile_rows > 0, tile_cols > 0,
        tile_rows as nat * tile_cols as nat <= usize::MAX as nat,
        tile_row_start as nat + tile_rows as nat <= u64::MAX as nat,
        tile_col_start as nat + tile_cols as nat <= u64::MAX as nat,
        forall|r: nat, c: nat| r < tile_rows as nat && c < tile_cols as nat
            && tile_row_start as nat + r < global_rows as nat
            && tile_col_start as nat + c < global_cols as nat
            ==> #[trigger] g2s_element_ok(&src_layout@, src_data@.len(),
                    tile_row_start as nat + r, tile_col_start as nat + c),
        forall|r: nat| r < tile_rows as nat
            && tile_row_start as nat + r < global_rows as nat
            ==> #[trigger] a_row_stride_ok(&src_layout@, tile_row_start as nat + r),
    ensures
        dst_buf@.len() == old(dst_buf)@.len(),
        forall|r: nat, c: nat| r < tile_rows as nat && c < tile_cols as nat
            && tile_row_start as nat + r < global_rows as nat
            && tile_col_start as nat + c < global_cols as nat
            ==> #[trigger] dst_buf@[(r * tile_cols as nat + c) as int]
                == src_data@[gemm_a_offset(&src_layout@,
                    tile_row_start as nat + r, tile_col_start as nat + c) as int],
        forall|r: nat, c: nat| r < tile_rows as nat && c < tile_cols as nat
            && (tile_row_start as nat + r >= global_rows as nat
                || tile_col_start as nat + c >= global_cols as nat)
            ==> #[trigger] dst_buf@[(r * tile_cols as nat + c) as int] == 0i64,
{
    let mut ri: u64 = 0;
    while ri < tile_rows
        invariant
            0 <= ri <= tile_rows,
            dst_buf@.len() == (tile_rows as nat) * (tile_cols as nat),
            src_layout.wf_spec(), src_layout@.rank() == 2,
            tile_rows > 0, tile_cols > 0,
            tile_rows as nat * tile_cols as nat <= usize::MAX as nat,
            tile_row_start as nat + tile_rows as nat <= u64::MAX as nat,
            tile_col_start as nat + tile_cols as nat <= u64::MAX as nat,
            global_rows as nat <= src_layout@.shape[0],
            global_cols as nat <= src_layout@.shape[1],
            forall|r2: nat, c2: nat| r2 < tile_rows as nat && c2 < tile_cols as nat
                && tile_row_start as nat + r2 < global_rows as nat
                && tile_col_start as nat + c2 < global_cols as nat
                ==> #[trigger] g2s_element_ok(&src_layout@, src_data@.len(),
                        tile_row_start as nat + r2, tile_col_start as nat + c2),
            forall|r2: nat| r2 < tile_rows as nat
                && tile_row_start as nat + r2 < global_rows as nat
                ==> #[trigger] a_row_stride_ok(&src_layout@, tile_row_start as nat + r2),
            // Previously written rows: in-bounds
            forall|pr: nat, pc: nat| pr < ri as nat && pc < tile_cols as nat
                && tile_row_start as nat + pr < global_rows as nat
                && tile_col_start as nat + pc < global_cols as nat
                ==> #[trigger] dst_buf@[(pr * tile_cols as nat + pc) as int]
                    == src_data@[gemm_a_offset(&src_layout@,
                        tile_row_start as nat + pr, tile_col_start as nat + pc) as int],
            // Previously written rows: out-of-bounds
            forall|pr: nat, pc: nat| pr < ri as nat && pc < tile_cols as nat
                && (tile_row_start as nat + pr >= global_rows as nat
                    || tile_col_start as nat + pc >= global_cols as nat)
                ==> #[trigger] dst_buf@[(pr * tile_cols as nat + pc) as int] == 0i64,
        decreases tile_rows - ri,
    {
        let mut ci: u64 = 0;
        while ci < tile_cols
            invariant
                0 <= ci <= tile_cols,
                0 <= ri < tile_rows,
                dst_buf@.len() == (tile_rows as nat) * (tile_cols as nat),
                src_layout.wf_spec(), src_layout@.rank() == 2,
                tile_rows > 0, tile_cols > 0,
                tile_rows as nat * tile_cols as nat <= usize::MAX as nat,
                tile_row_start as nat + tile_rows as nat <= u64::MAX as nat,
                tile_col_start as nat + tile_cols as nat <= u64::MAX as nat,
                global_rows as nat <= src_layout@.shape[0],
                global_cols as nat <= src_layout@.shape[1],
                forall|r2: nat, c2: nat| r2 < tile_rows as nat && c2 < tile_cols as nat
                    && tile_row_start as nat + r2 < global_rows as nat
                    && tile_col_start as nat + c2 < global_cols as nat
                    ==> #[trigger] g2s_element_ok(&src_layout@, src_data@.len(),
                            tile_row_start as nat + r2, tile_col_start as nat + c2),
                forall|r2: nat| r2 < tile_rows as nat
                    && tile_row_start as nat + r2 < global_rows as nat
                    ==> #[trigger] a_row_stride_ok(&src_layout@, tile_row_start as nat + r2),
                // Previous rows preserved
                forall|pr: nat, pc: nat| pr < ri as nat && pc < tile_cols as nat
                    && tile_row_start as nat + pr < global_rows as nat
                    && tile_col_start as nat + pc < global_cols as nat
                    ==> #[trigger] dst_buf@[(pr * tile_cols as nat + pc) as int]
                        == src_data@[gemm_a_offset(&src_layout@,
                            tile_row_start as nat + pr, tile_col_start as nat + pc) as int],
                forall|pr: nat, pc: nat| pr < ri as nat && pc < tile_cols as nat
                    && (tile_row_start as nat + pr >= global_rows as nat
                        || tile_col_start as nat + pc >= global_cols as nat)
                    ==> #[trigger] dst_buf@[(pr * tile_cols as nat + pc) as int] == 0i64,
                // Current row, already-written columns: in-bounds
                forall|pc: nat| pc < ci as nat
                    && (tile_row_start as nat + ri as nat) < global_rows as nat
                    && (tile_col_start as nat + pc) < global_cols as nat
                    ==> #[trigger] dst_buf@[(ri as nat * tile_cols as nat + pc) as int]
                        == src_data@[gemm_a_offset(&src_layout@,
                            tile_row_start as nat + ri as nat, tile_col_start as nat + pc) as int],
                // Current row, already-written columns: out-of-bounds
                forall|pc: nat| pc < ci as nat
                    && ((tile_row_start as nat + ri as nat) >= global_rows as nat
                        || (tile_col_start as nat + pc) >= global_cols as nat)
                    ==> #[trigger] dst_buf@[(ri as nat * tile_cols as nat + pc) as int] == 0i64,
            decreases tile_cols - ci,
        {
            let gi = tile_row_start + ri;
            let gj = tile_col_start + ci;

            // Compute dst index
            proof {
                let ri_n = ri as nat;
                let ci_n = ci as nat;
                let tr_n = tile_rows as nat;
                let tc_n = tile_cols as nat;
                assert(ri_n * tc_n + ci_n < tr_n * tc_n) by (nonlinear_arith)
                    requires ri_n < tr_n, ci_n < tc_n, tc_n > 0, tr_n > 0;
            }
            let dst_idx = ri * tile_cols + ci;
            let dst_len = dst_buf.len();
            proof {
                assert((dst_idx as int) < (dst_len as int));
                assert((dst_idx as usize) as int == dst_idx as int);
            }

            let ghost dst_before = dst_buf@;

            if gi < global_rows && gj < global_cols {
                proof {
                    let ri_n = ri as nat;
                    let ci_n = ci as nat;
                    let gi_n = tile_row_start as nat + ri_n;
                    let gj_n = tile_col_start as nat + ci_n;
                    // Trigger quantifier with original form
                    assert(g2s_element_ok(&src_layout@, src_data@.len(),
                        tile_row_start as nat + ri_n, tile_col_start as nat + ci_n));
                    assert(a_offset_overflow_ok(&src_layout@, gi_n, gj_n));
                    assert(a_data_in_bounds(&src_layout@, src_data@.len(), gi_n, gj_n));
                    assert(a_row_stride_ok(&src_layout@, tile_row_start as nat + ri_n));
                }
                let off = gemm_a_offset_exec(src_layout, gi, gj);
                proof {
                    assert(off >= 0);
                    assert((off as nat) < src_data@.len());
                }
                let src_len = src_data.len();
                proof {
                    assert((off as int) < (src_len as int));
                    assert((off as usize) as int == off as int);
                }
                let val = src_data[off as usize];
                dst_buf.set(dst_idx as usize, val);
            } else {
                dst_buf.set(dst_idx as usize, 0i64);
            }

            proof {
                let tc = tile_cols as nat;
                let ri_n = ri as nat;
                let ci_n = ci as nat;
                let di = dst_idx as int;
                // Frame: previous rows' indices are strictly less than dst_idx
                assert forall|pr: nat, pc: nat| pr < ri_n && pc < tc
                implies #[trigger] dst_buf@[(pr * tc + pc) as int]
                    == dst_before[(pr * tc + pc) as int]
                by {
                    assert((pr * tc + pc) < (ri_n * tc)) by (nonlinear_arith)
                        requires pr < ri_n, pc < tc, tc > 0;
                    assert((ri_n * tc) <= di) by (nonlinear_arith)
                        requires di == (ri_n * tc + ci_n) as int, ci_n >= 0nat;
                    assert((pr * tc + pc) as int != di);
                };
                // Frame: current row, earlier columns are strictly less
                assert forall|pc: nat| pc < ci_n
                implies #[trigger] dst_buf@[(ri_n * tc + pc) as int]
                    == dst_before[(ri_n * tc + pc) as int]
                by {
                    assert((ri_n * tc + pc) < (ri_n * tc + ci_n)) by (nonlinear_arith)
                        requires pc < ci_n;
                    assert((ri_n * tc + pc) as int != di);
                };
            }

            ci = ci + 1;
        }

        ri = ri + 1;
    }
}

/// Copy elements from shared memory buffer to register buffer (flat contiguous copy).
pub fn s2r_copy_fragment_exec(
    smem_buf: &Vec<i64>,
    reg_buf: &mut Vec<i64>,
    fragment_size: u64,
)
    requires
        fragment_size as nat <= smem_buf@.len(),
        old(reg_buf)@.len() == fragment_size as nat,
        fragment_size as nat <= usize::MAX as nat,
    ensures
        reg_buf@.len() == old(reg_buf)@.len(),
        forall|i: nat| i < fragment_size as nat
            ==> #[trigger] reg_buf@[i as int] == smem_buf@[i as int],
{
    let mut i: u64 = 0;
    while i < fragment_size
        invariant
            0 <= i <= fragment_size,
            reg_buf@.len() == fragment_size as nat,
            fragment_size as nat <= smem_buf@.len(),
            fragment_size as nat <= usize::MAX as nat,
            forall|j: nat| j < i as nat
                ==> #[trigger] reg_buf@[j as int] == smem_buf@[j as int],
        decreases fragment_size - i,
    {
        let smem_len = smem_buf.len();
        let reg_len = reg_buf.len();
        proof {
            assert((i as int) < (smem_len as int));
            assert((i as usize) as int == i as int);
            assert((i as int) < (reg_len as int));
        }
        let val = smem_buf[i as usize];
        reg_buf.set(i as usize, val);
        i = i + 1;
    }
}

} // verus!
