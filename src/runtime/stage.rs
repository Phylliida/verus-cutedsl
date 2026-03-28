/// Runtime (exec) shared state for CPU-side Stage evaluation.
///
/// Flat buffer layout (single Vec<i64> with offsets) matching how GPU
/// shared memory actually works. O(1) reads and writes.

use vstd::prelude::*;
use crate::stage::*;
use crate::scan::{inclusive_scan, exclusive_scan, reduce, all_partial_sums_bounded,
    inclusive_scan_int, exclusive_scan_int, reduce_int, as_int_seq};
use crate::runtime::scan_multiblock::{inclusive_scan_i64_exec, exclusive_scan_i64_exec};

verus! {

// ══════════════════════════════════════════════════════════════
// RuntimeSharedState — flat buffer layout
// ══════════════════════════════════════════════════════════════

pub struct RuntimeSharedState {
    pub data: Vec<i64>,
    pub offsets: Vec<usize>,
    pub lengths: Vec<usize>,
    pub workgroup_size: u32,
    pub model: Ghost<SharedState>,
}

impl View for RuntimeSharedState {
    type V = SharedState;
    open spec fn view(&self) -> SharedState { self.model@ }
}

impl RuntimeSharedState {
    /// Well-formedness: flat layout matches ghost model.
    pub open spec fn wf_spec(&self) -> bool {
        let n = self@.buffers.len();
        &&& self.offsets@.len() == n
        &&& self.lengths@.len() == n
        &&& self.workgroup_size as nat == self@.workgroup_size
        // Per-buffer: length matches, region fits, values match
        &&& forall|b: int| #![trigger self.offsets@[b], self.lengths@[b]]
            0 <= b < n ==> {
            &&& self.lengths@[b] as nat == self@.buffers[b].len()
            &&& self.offsets@[b] as nat + self.lengths@[b] as nat <= self.data@.len()
            &&& forall|j: int| 0 <= j < self.lengths@[b] as int ==>
                self.data@[self.offsets@[b] as int + j] as int == self@.buffers[b][j]
        }
        // Ordered non-overlapping: each buffer region ends before the next starts
        &&& forall|b1: int, b2: int|
            0 <= b1 < b2 < n ==>
            self.offsets@[b1] as nat + (#[trigger] self.lengths@[b1]) as nat
                <= (#[trigger] self.offsets@[b2]) as nat
    }

    pub fn num_buffers(&self) -> (result: usize)
        requires self.wf_spec(),
        ensures result as nat == self@.num_buffers(),
    {
        self.offsets.len()
    }

    pub fn buffer_len(&self, buf: usize) -> (result: usize)
        requires self.wf_spec(), buf < self@.num_buffers(),
        ensures result as nat == self@.buffer_len(buf as nat),
    {
        // Trigger wf_spec's per-buffer clause for buf
        proof { assert(self.offsets@[buf as int] >= 0); }
        self.lengths[buf]
    }

    pub fn read(&self, buf: usize, idx: usize) -> (result: i64)
        requires
            self.wf_spec(),
            buf < self@.num_buffers(),
            idx < self@.buffer_len(buf as nat),
        ensures
            result as int == self@.read(buf as nat, idx as nat),
    {
        let off = self.offsets[buf];
        let len = self.lengths[buf];
        proof {
            assert(off as nat + len as nat <= self.data@.len());
            assert(idx < len);
        }
        assert(off + idx < self.data.len());
        self.data[off + idx]
    }

    pub fn write(&mut self, buf: usize, idx: usize, val: i64)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            idx < old(self)@.buffer_len(buf as nat),
        ensures
            self.wf_spec(),
            self@ == old(self)@.write(buf as nat, idx as nat, val as int),
    {
        proof { self.lemma_buffer_bounds(buf as nat); }
        let off = self.offsets[buf];
        let len = self.lengths[buf];
        assert(off + idx < self.data.len());
        let ghost old_snap = *self;
        self.data.set(off + idx, val);
        self.model = Ghost(old(self)@.write(buf as nat, idx as nat, val as int));
        proof {
            // The new spec buffer is the old one with position idx updated
            let new_buf_spec = old_snap@.buffers[buf as int].update(idx as int, val as int);
            assert(self.model@ == (SharedState {
                buffers: old_snap@.buffers.update(buf as int, new_buf_spec),
                workgroup_size: old_snap@.workgroup_size,
            }));
            // Target region: only position idx changed
            assert forall|j: int| 0 <= j < new_buf_spec.len() implies
                self.data@[old_snap.offsets@[buf as int] as int + j] as int == new_buf_spec[j]
            by {
                if j == idx as int {
                } else {
                    assert(old_snap.offsets@[buf as int] as int + j
                        != old_snap.offsets@[buf as int] as int + idx as int);
                }
            }
            // Non-target data: only one position changed
            assert forall|p: int| (0 <= p < self.data@.len() as int
                && !(old_snap.offsets@[buf as int] as int <= p
                     < old_snap.offsets@[buf as int] as int
                       + old_snap.lengths@[buf as int] as int)) implies
                self.data@[p] == old_snap.data@[p]
            by {
                assert(p != off as int + idx as int);
            }
            self.lemma_wf_after_region_write(&old_snap, buf as nat, new_buf_spec);
        }
    }

    pub fn new_zeroed(buffer_sizes: &Vec<usize>, workgroup_size: u32) -> (result: RuntimeSharedState)
        requires
            buffer_sizes@.len() > 0,
            spec_total_size(buffer_sizes@) <= usize::MAX as nat,
        ensures
            result.wf_spec(),
            result@.workgroup_size == workgroup_size as nat,
            result@.buffers.len() == buffer_sizes@.len(),
            forall|i: int| 0 <= i < buffer_sizes@.len() ==>
                result@.buffers[i].len() == #[trigger] buffer_sizes@[i] as nat,
            forall|i: int, j: int| 0 <= i < buffer_sizes@.len()
                && 0 <= j < buffer_sizes@[i] as int
                ==> result@.buffers[i][j] == 0,
    {
        let n = buffer_sizes.len();
        let ghost sizes = buffer_sizes@;
        let ghost total_bound = spec_total_size(sizes);

        // Compute offsets (consecutive)
        let mut total: usize = 0;
        let mut offsets: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == sizes.len(),
                sizes == buffer_sizes@,
                total_bound == spec_total_size(sizes),
                total_bound <= usize::MAX as nat,
                offsets@.len() == i,
                total as nat == spec_partial_sum(sizes, i as nat),
                forall|k: int| 0 <= k < i as int ==>
                    offsets@[k] as nat == spec_partial_sum(sizes, k as nat),
            decreases n - i,
        {
            offsets.push(total);
            proof {
                lemma_partial_sum_step(sizes, i as nat);
                lemma_partial_sum_monotone(sizes, (i + 1) as nat);
                assert(spec_partial_sum(sizes, (i + 1) as nat) <= total_bound);
            }
            total = total + buffer_sizes[i];
            i = i + 1;
        }

        let data = vec_i64_zeroed(total);

        let mut lengths: Vec<usize> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n, n == buffer_sizes@.len(),
                lengths@.len() == j,
                forall|k: int| 0 <= k < j as int ==> lengths@[k] == buffer_sizes@[k],
            decreases n - j,
        {
            lengths.push(buffer_sizes[j]);
            j = j + 1;
        }

        let ghost spec_buffers = Seq::new(n as nat, |i: int|
            Seq::new(buffer_sizes@[i] as nat, |_j: int| 0int));

        let result = RuntimeSharedState {
            data, offsets, lengths, workgroup_size,
            model: Ghost(SharedState {
                buffers: spec_buffers,
                workgroup_size: workgroup_size as nat,
            }),
        };

        proof {
            // Prove wf_spec
            let rn = spec_buffers.len() as int;

            // Per-buffer properties
            assert forall|b: int| #![trigger result.offsets@[b], result.lengths@[b]]
                0 <= b < rn implies {
                &&& result.lengths@[b] as nat == result@.buffers[b].len()
                &&& result.offsets@[b] as nat + result.lengths@[b] as nat <= result.data@.len()
                &&& forall|j: int| 0 <= j < result.lengths@[b] as int ==>
                    result.data@[result.offsets@[b] as int + j] as int == result@.buffers[b][j]
            } by {
                // offset[b] = partial_sum(b), length[b] = sizes[b]
                // offset[b] + length[b] = partial_sum(b+1) <= total = data.len()
                lemma_partial_sum_step(buffer_sizes@, b as nat);
                lemma_partial_sum_monotone(buffer_sizes@, (b + 1) as nat);
                // Values: data is all 0, spec buffers are all 0
                assert forall|j: int| 0 <= j < result.lengths@[b] as int implies
                    result.data@[result.offsets@[b] as int + j] as int == result@.buffers[b][j]
                by {
                    // data[off + j] == 0i64, spec_buffers[b][j] == 0int
                    assert(result.data@[result.offsets@[b] as int + j] == 0i64);
                }
            }

            // Ordered non-overlapping
            assert forall|b1: int, b2: int|
                0 <= b1 < b2 < rn implies
                result.offsets@[b1] as nat + (#[trigger] result.lengths@[b1]) as nat
                    <= (#[trigger] result.offsets@[b2]) as nat
            by {
                // offset[b1] + length[b1] = partial_sum(b1+1) <= partial_sum(b2) = offset[b2]
                lemma_partial_sum_step(buffer_sizes@, b1 as nat);
                lemma_partial_sum_le(buffer_sizes@, (b1 + 1) as nat, b2 as nat);
            }
        }

        result
    }
}

// ══════════════════════════════════════════════════════════════
// Partial sum helpers
// ══════════════════════════════════════════════════════════════

pub open spec fn spec_partial_sum(sizes: Seq<usize>, k: nat) -> nat
    decreases k,
{
    if k == 0 { 0 }
    else { spec_partial_sum(sizes, (k - 1) as nat) + sizes[(k - 1) as int] as nat }
}

pub open spec fn spec_total_size(sizes: Seq<usize>) -> nat {
    spec_partial_sum(sizes, sizes.len())
}

/// partial_sum(k+1) = partial_sum(k) + sizes[k].
proof fn lemma_partial_sum_step(sizes: Seq<usize>, k: nat)
    requires k < sizes.len(),
    ensures spec_partial_sum(sizes, k + 1)
        == spec_partial_sum(sizes, k) + sizes[k as int] as nat,
{}

/// partial_sum is monotone: k1 <= k2 ==> partial_sum(k1) <= partial_sum(k2).
proof fn lemma_partial_sum_le(sizes: Seq<usize>, k1: nat, k2: nat)
    requires k1 <= k2, k2 <= sizes.len(),
    ensures spec_partial_sum(sizes, k1) <= spec_partial_sum(sizes, k2),
    decreases k2 - k1,
{
    if k1 == k2 {
    } else {
        lemma_partial_sum_le(sizes, k1, (k2 - 1) as nat);
    }
}

/// partial_sum(k) <= total for all k <= n.
proof fn lemma_partial_sum_monotone(sizes: Seq<usize>, k: nat)
    requires k <= sizes.len(),
    ensures spec_partial_sum(sizes, k) <= spec_total_size(sizes),
{
    lemma_partial_sum_le(sizes, k, sizes.len());
}

fn vec_i64_zeroed(n: usize) -> (result: Vec<i64>)
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < n as int ==> result@[i] == 0i64,
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n, v@.len() == i,
            forall|j: int| 0 <= j < i as int ==> v@[j] == 0i64,
        decreases n - i,
    {
        v.push(0i64);
        i = i + 1;
    }
    v
}

// ══════════════════════════════════════════════════════════════
// Buffer bounds infrastructure
//
// Extracts the key facts from wf_spec that every operation needs.
// Call once, then use the ensures throughout the function.
// ══════════════════════════════════════════════════════════════

impl RuntimeSharedState {
    /// Extract buffer bounds from wf_spec. Call this at the start of any
    /// function that operates on a buffer — it gives you everything you need
    /// for offset arithmetic without manually triggering wf_spec quantifiers.
    pub proof fn lemma_buffer_bounds(&self, buf: nat)
        requires self.wf_spec(), buf < self@.num_buffers(),
        ensures
            (buf as int) < self.offsets@.len(),
            (buf as int) < self.lengths@.len(),
            self.offsets@[buf as int] as nat + self.lengths@[buf as int] as nat
                <= self.data@.len(),
            self.lengths@[buf as int] as nat == self@.buffer_len(buf),
            forall|j: int| 0 <= j < self.lengths@[buf as int] as int ==>
                self.data@[self.offsets@[buf as int] as int + j] as int
                    == self@.buffers[buf as int][j],
    {
        // Trigger the per-buffer clause in wf_spec
        assert(self.offsets@[buf as int] >= 0);
        assert(self.lengths@[buf as int] >= 0);
    }

    /// After modifying the flat data for one buffer region and updating the
    /// ghost model, re-establish wf_spec. This is the key lemma that avoids
    /// re-proving wf_spec from scratch after every write_buffer.
    pub proof fn lemma_wf_after_region_write(
        &self,
        old_state: &RuntimeSharedState,
        buf: nat,
        new_buf_spec: Seq<int>,
    )
        requires
            old_state.wf_spec(),
            buf < old_state@.num_buffers(),
            // Structure unchanged
            self.offsets@ == old_state.offsets@,
            self.lengths@ == old_state.lengths@,
            self.workgroup_size == old_state.workgroup_size,
            self.data@.len() == old_state.data@.len(),
            // Ghost model updated for target buffer only
            self.model@ == (SharedState {
                buffers: old_state@.buffers.update(buf as int, new_buf_spec),
                workgroup_size: old_state@.workgroup_size,
            }),
            // New buffer spec has correct length
            new_buf_spec.len() == old_state@.buffer_len(buf),
            // Target region has new values
            forall|j: int| 0 <= j < new_buf_spec.len() ==>
                self.data@[old_state.offsets@[buf as int] as int + j] as int
                    == new_buf_spec[j],
            // Non-target data unchanged
            forall|p: int| (0 <= p < self.data@.len() as int
                && !(old_state.offsets@[buf as int] as int <= p
                     < old_state.offsets@[buf as int] as int
                       + old_state.lengths@[buf as int] as int)) ==>
                self.data@[p] == old_state.data@[p],
        ensures
            self.wf_spec(),
    {
        // Per-buffer: target buffer has new values, others unchanged
        assert forall|b: int| #![trigger self.offsets@[b], self.lengths@[b]]
            0 <= b < self@.buffers.len() implies {
            &&& self.lengths@[b] as nat == self@.buffers[b].len()
            &&& self.offsets@[b] as nat + self.lengths@[b] as nat <= self.data@.len()
            &&& forall|j: int| 0 <= j < self.lengths@[b] as int ==>
                self.data@[self.offsets@[b] as int + j] as int == self@.buffers[b][j]
        } by {
            // Trigger old wf_spec for buffer b
            assert(old_state.offsets@[b] >= 0);
            if b == buf as int {
                // Target buffer: new values from new_buf_spec
            } else {
                // Other buffer: data unchanged in its region
                // (by non-overlap, its region doesn't intersect the target region)
                assert forall|j: int| 0 <= j < self.lengths@[b] as int implies
                    self.data@[self.offsets@[b] as int + j] as int == self@.buffers[b][j]
                by {
                    let p = self.offsets@[b] as int + j;
                    // p is in buffer b's region, not in target buffer's region
                    // by non-overlap from old wf_spec
                    if b < buf as int {
                        assert(old_state.offsets@[b] as nat + old_state.lengths@[b] as nat
                            <= old_state.offsets@[buf as int] as nat);
                    } else {
                        assert(old_state.offsets@[buf as int] as nat
                            + old_state.lengths@[buf as int] as nat
                            <= old_state.offsets@[b] as nat);
                    }
                    // So p is outside target region → data unchanged
                    assert(self.data@[p] == old_state.data@[p]);
                    // old data matches old spec
                    assert(old_state.data@[p] as int == old_state@.buffers[b][j]);
                }
            }
        }

        // Non-overlap preserved (offsets/lengths unchanged)
        assert forall|b1: int, b2: int|
            0 <= b1 < b2 < self@.buffers.len() as int implies
            self.offsets@[b1] as nat + (#[trigger] self.lengths@[b1]) as nat
                <= (#[trigger] self.offsets@[b2]) as nat
        by {
            assert(old_state.offsets@[b1] >= 0);
            assert(old_state.offsets@[b2] >= 0);
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Exec scan: run_scan
// ══════════════════════════════════════════════════════════════

impl RuntimeSharedState {
    /// Extract a logical buffer as a Vec<i64> (copy out from flat layout).
    pub fn extract_buffer(&self, buf: usize) -> (result: Vec<i64>)
        requires
            self.wf_spec(),
            buf < self@.num_buffers(),
            self@.buffer_len(buf as nat) > 0,
        ensures
            result@.len() == self@.buffer_len(buf as nat),
            forall|i: int| 0 <= i < result@.len() ==>
                result@[i] as int == self@.buffers[buf as int][i],
    {
        let off = self.offsets[buf];
        let len = self.lengths[buf];
        let mut result: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                len as nat == self@.buffer_len(buf as nat),
                result@.len() == i,
                self.wf_spec(),
                buf < self@.num_buffers(),
                forall|j: int| 0 <= j < i as int ==>
                    result@[j] as int == self@.buffers[buf as int][j],
            decreases len - i,
        {
            let val = self.read(buf, i);
            result.push(val);
            i = i + 1;
        }
        result
    }

    /// Write a Vec<i64> back into a logical buffer.
    pub fn write_buffer(&mut self, buf: usize, new_data: &Vec<i64>)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            new_data@.len() == old(self)@.buffer_len(buf as nat),
        ensures
            self.wf_spec(),
            self@.workgroup_size == old(self)@.workgroup_size,
            self@.buffers.len() == old(self)@.buffers.len(),
            self@.buffer_len(buf as nat) == new_data@.len(),
            forall|i: int| 0 <= i < new_data@.len() ==>
                self@.buffers[buf as int][i] == new_data@[i] as int,
            forall|b: int| 0 <= b < old(self)@.buffers.len() && b != buf as int ==>
                self@.buffers[b] == old(self)@.buffers[b],
    {
        proof { self.lemma_buffer_bounds(buf as nat); }
        let off = self.offsets[buf];
        let len = self.lengths[buf];

        let ghost old_snap = *self;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                len == new_data@.len(),
                self.offsets@ == old_snap.offsets@,
                self.lengths@ == old_snap.lengths@,
                self.workgroup_size == old_snap.workgroup_size,
                self.model == old_snap.model,
                self.data@.len() == old_snap.data@.len(),
                off as nat + len as nat <= self.data@.len(),
                forall|j: int| 0 <= j < i as int ==>
                    self.data@[off as int + j] == new_data@[j],
                forall|p: int| (0 <= p < self.data@.len() as int
                    && !(off as int <= p < off as int + i as int)) ==>
                    self.data@[p] == old_snap.data@[p],
            decreases len - i,
        {
            assert(off + i < self.data.len());
            self.data.set(off + i, new_data[i]);
            i = i + 1;
        }

        let ghost new_buf_spec = Seq::new(new_data@.len(), |i: int| new_data@[i] as int);
        self.model = Ghost(SharedState {
            buffers: old(self)@.buffers.update(buf as int, new_buf_spec),
            workgroup_size: old(self)@.workgroup_size,
        });

        proof {
            self.lemma_wf_after_region_write(&old_snap, buf as nat, new_buf_spec);
        }
    }

    /// Execute a scan operation on a logical buffer.
    /// Ensures result matches eval_scan spec.
    /// Execute an inclusive scan on a buffer.
    pub fn run_inclusive_scan(&mut self, buf: usize)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            old(self)@.buffer_len(buf as nat) > 0,
            old(self)@.buffer_len(buf as nat) <= i64::MAX as nat,
            all_partial_sums_bounded(old(self).extract_buffer_spec(buf as nat)),
        ensures
            self.wf_spec(),
            self@.workgroup_size == old(self)@.workgroup_size,
            self@.buffers.len() == old(self)@.buffers.len(),
            self@.buffer_len(buf as nat) == old(self)@.buffer_len(buf as nat),
            forall|b: int| 0 <= b < old(self)@.buffers.len() && b != buf as int ==>
                self@.buffers[b] == old(self)@.buffers[b],
            // Result values match inclusive_scan_int
            forall|i: int| 0 <= i < old(self)@.buffer_len(buf as nat) as int ==>
                self@.buffers[buf as int][i]
                    == inclusive_scan_int(old(self).extract_buffer_spec(buf as nat))[i],
    {
        let ghost old_spec = self.extract_buffer_spec(buf as nat);
        let data = self.extract_buffer(buf);
        proof { assert(data@ =~= old_spec); }
        let scanned = inclusive_scan_i64_exec(&data);
        // scanned[i] as int == inclusive_scan_int(data@)[i] == inclusive_scan_int(old_spec)[i]
        proof {
            assert(data@ =~= old_spec);
            assert forall|i: int| 0 <= i < scanned@.len() implies
                scanned@[i] as int == inclusive_scan_int(old_spec)[i]
            by {
                assert(scanned@[i] as int == inclusive_scan_int(data@)[i]);
            }
        }
        self.write_buffer(buf, &scanned);
        // self@.buffers[buf][i] == scanned[i] as int == inclusive_scan_int(old_spec)[i]
    }
}

/// Spec helper: the i64 data for a logical buffer (for preconditions).
impl RuntimeSharedState {
    pub open spec fn extract_buffer_spec(&self, buf: nat) -> Seq<i64> {
        Seq::new(self.lengths@[buf as int] as nat, |i: int|
            self.data@[self.offsets@[buf as int] as int + i])
    }
}

// ══════════════════════════════════════════════════════════════
// #1: Full scan exec↔spec bridge
// ══════════════════════════════════════════════════════════════

/// Bridge: as_int_seq of extract_buffer_spec equals the spec-level buffer.
pub proof fn lemma_as_int_seq_extract_equals_spec(state: &RuntimeSharedState, buf: nat)
    requires state.wf_spec(), buf < state@.num_buffers(),
    ensures as_int_seq(state.extract_buffer_spec(buf)) =~= state@.buffers[buf as int],
{
    state.lemma_buffer_bounds(buf);
}

/// Full bridge: if run_inclusive_scan's ensures hold, the result equals eval_scan.
pub proof fn lemma_run_inclusive_scan_matches_eval_scan(
    old_state: &RuntimeSharedState,
    new_state: &RuntimeSharedState,
    buf: nat,
)
    requires
        old_state.wf_spec(),
        buf < old_state@.num_buffers(),
        new_state.wf_spec(),
        new_state@.workgroup_size == old_state@.workgroup_size,
        new_state@.buffers.len() == old_state@.buffers.len(),
        new_state@.buffer_len(buf) == old_state@.buffer_len(buf),
        forall|b: int| 0 <= b < old_state@.buffers.len() && b != buf as int ==>
            new_state@.buffers[b] == old_state@.buffers[b],
        forall|i: int| 0 <= i < old_state@.buffer_len(buf) as int ==>
            new_state@.buffers[buf as int][i]
                == inclusive_scan_int(old_state.extract_buffer_spec(buf))[i],
    ensures
        new_state@ == eval_scan(buf, ScanOp::InclusiveSum, old_state@),
{
    let scan_result = inclusive_scan::<int>(old_state@.buffers[buf as int]);
    lemma_as_int_seq_extract_equals_spec(old_state, buf);
    // inclusive_scan_int(extract) = inclusive_scan::<int>(as_int_seq(extract))
    // as_int_seq(extract) =~= spec_buf  (from bridge lemma)
    // So scan_result =~= inclusive_scan_int(extract)
    let extract = old_state.extract_buffer_spec(buf);
    assert(as_int_seq(extract) =~= old_state@.buffers[buf as int]);
    // inclusive_scan_int(extract) == inclusive_scan::<int>(as_int_seq(extract))
    //                             =~= inclusive_scan::<int>(spec_buf) = scan_result
    // inclusive_scan_int(extract) = inclusive_scan::<int>(as_int_seq(extract)) by definition
    // as_int_seq(extract) =~= spec_buf, so their inclusive_scans agree pointwise
    assert(inclusive_scan::<int>(as_int_seq(extract))
        =~= inclusive_scan::<int>(old_state@.buffers[buf as int]));
    assert forall|i: int| 0 <= i < scan_result.len() implies
        new_state@.buffers[buf as int][i] == scan_result[i]
    by {
        assert(new_state@.buffers[buf as int][i] == inclusive_scan_int(extract)[i]);
        assert(inclusive_scan_int(extract)[i]
            == inclusive_scan::<int>(as_int_seq(extract))[i]);
    }
    assert(new_state@.buffers[buf as int] =~= scan_result);
    assert(new_state@.buffers =~= old_state@.set_buffer(buf, scan_result).buffers);
}

// ══════════════════════════════════════════════════════════════
// #2: run_exclusive_scan
// ══════════════════════════════════════════════════════════════

impl RuntimeSharedState {
    pub fn run_exclusive_scan(&mut self, buf: usize)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            old(self)@.buffer_len(buf as nat) > 0,
            old(self)@.buffer_len(buf as nat) <= i64::MAX as nat,
            all_partial_sums_bounded(old(self).extract_buffer_spec(buf as nat)),
        ensures
            self.wf_spec(),
            self@.workgroup_size == old(self)@.workgroup_size,
            self@.buffers.len() == old(self)@.buffers.len(),
            self@.buffer_len(buf as nat) == old(self)@.buffer_len(buf as nat),
            forall|b: int| 0 <= b < old(self)@.buffers.len() && b != buf as int ==>
                self@.buffers[b] == old(self)@.buffers[b],
            forall|i: int| 0 <= i < old(self)@.buffer_len(buf as nat) as int ==>
                self@.buffers[buf as int][i]
                    == exclusive_scan_int(old(self).extract_buffer_spec(buf as nat))[i],
    {
        let ghost old_spec = self.extract_buffer_spec(buf as nat);
        let data = self.extract_buffer(buf);
        proof { assert(data@ =~= old_spec); }
        let scanned = exclusive_scan_i64_exec(&data);
        proof {
            assert forall|i: int| 0 <= i < scanned@.len() implies
                scanned@[i] as int == exclusive_scan_int(old_spec)[i]
            by {
                assert(scanned@[i] as int == exclusive_scan_int(data@)[i]);
            }
        }
        self.write_buffer(buf, &scanned);
    }
}

// ══════════════════════════════════════════════════════════════
// #3: 2D thread env injectivity
// ══════════════════════════════════════════════════════════════

/// For 2D dispatch, distinct linear thread IDs produce distinct environments.
/// env(t) = [t % width, t / width] — the mixed-radix decomposition is injective.
pub proof fn lemma_dim2d_env_injective(t1: nat, t2: nat, width: nat, height: nat)
    requires
        width > 0,
        t1 < width * height,
        t2 < width * height,
        t1 != t2,
    ensures
        thread_env_for_dim(&ThreadDim::Dim2D { width, height }, t1)
            != thread_env_for_dim(&ThreadDim::Dim2D { width, height }, t2),
{
    // If envs were equal: t1 % w == t2 % w AND t1 / w == t2 / w
    // Then t1 == (t1/w)*w + t1%w == (t2/w)*w + t2%w == t2. Contradiction.
    if t1 % width == t2 % width && t1 / width == t2 / width {
        // t == (t / w) * w + t % w is the Euclidean division identity
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t1 as int, width as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t2 as int, width as int);
    }
}

// NOTE on 2D scatter: Var(0) scatter is NOT injective for 2D dispatch
// because env[0] = t % width (gid_x), and threads in different rows share
// the same gid_x. For 2D kernels, scatter must linearize:
//   scatter = Add(Var(0), Mul(Var(1), Const(width)))
// The lemma_identity_scatter_injective in stage_lemmas.rs works for 1D only.

} // verus!
