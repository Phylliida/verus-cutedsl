/// Runtime (exec) shared state for CPU-side Stage evaluation.
///
/// Uses a FLAT buffer layout (single Vec<i64> with offsets) matching how
/// GPU shared memory actually works. Each logical buffer is a contiguous
/// region at a known offset.

use vstd::prelude::*;
use crate::stage::*;

verus! {

// ══════════════════════════════════════════════════════════════
// RuntimeSharedState — flat buffer layout
// ══════════════════════════════════════════════════════════════

/// Exec-level shared state: flat i64 buffer + metadata + ghost spec model.
///
/// Logical buffer `b` occupies `data[offsets[b] .. offsets[b] + lengths[b]]`.
/// This matches GPU shared memory (one contiguous block with manual offsets).
pub struct RuntimeSharedState {
    pub data: Vec<i64>,
    pub offsets: Vec<usize>,    // start offset of each logical buffer
    pub lengths: Vec<usize>,    // length of each logical buffer
    pub workgroup_size: u32,
    pub model: Ghost<SharedState>,
}

impl View for RuntimeSharedState {
    type V = SharedState;
    open spec fn view(&self) -> SharedState {
        self.model@
    }
}

impl RuntimeSharedState {
    /// Well-formedness: flat layout matches ghost model.
    pub open spec fn wf_spec(&self) -> bool {
        // Buffer counts match
        &&& self.offsets@.len() == self@.buffers.len()
        &&& self.lengths@.len() == self@.buffers.len()
        // Workgroup size matches
        &&& self.workgroup_size as nat == self@.workgroup_size
        // Each buffer: length matches, values match
        &&& forall|b: int| 0 <= b < self@.buffers.len() ==> {
            let off = #[trigger] self.offsets@[b] as nat;
            let len = self.lengths@[b] as nat;
            // Length matches spec
            &&& len == self@.buffers[b].len()
            // Region fits in data
            &&& off + len <= self.data@.len()
            // Values match spec
            &&& forall|j: int| 0 <= j < len as int ==>
                self.data@[(off + j) as int] as int == self@.buffers[b][j]
        }
        // Non-overlapping buffers (each region is disjoint)
        &&& forall|b1: int, b2: int|
            0 <= b1 < self@.buffers.len() && 0 <= b2 < self@.buffers.len() && b1 != b2
            ==>
                (#[trigger] self.offsets@[b1]) as nat + self.lengths@[b1] as nat
                    <= (#[trigger] self.offsets@[b2]) as nat
                || self.offsets@[b2] as nat + self.lengths@[b2] as nat
                    <= self.offsets@[b1] as nat
    }

    /// Number of logical buffers.
    pub fn num_buffers(&self) -> (result: usize)
        requires self.wf_spec(),
        ensures result as nat == self@.num_buffers(),
    {
        self.offsets.len()
    }

    /// Length of a specific logical buffer.
    pub fn buffer_len(&self, buf: usize) -> (result: usize)
        requires self.wf_spec(), buf < self@.num_buffers(),
        ensures result as nat == self@.buffer_len(buf as nat),
    {
        self.lengths[buf]
    }

    /// Read a value from a logical buffer. O(1).
    pub fn read(&self, buf: usize, idx: usize) -> (result: i64)
        requires
            self.wf_spec(),
            buf < self@.num_buffers(),
            idx < self@.buffer_len(buf as nat),
        ensures
            result as int == self@.read(buf as nat, idx as nat),
    {
        let off = self.offsets[buf];
        self.data[off + idx]
    }

    /// Write a value to a logical buffer. O(1).
    pub fn write(&mut self, buf: usize, idx: usize, val: i64)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            idx < old(self)@.buffer_len(buf as nat),
        ensures
            self.wf_spec(),
            self@ == old(self)@.write(buf as nat, idx as nat, val as int),
    {
        let off = self.offsets[buf];
        self.data.set(off + idx, val);
        self.model = Ghost(old(self)@.write(buf as nat, idx as nat, val as int));
    }

    /// Create a RuntimeSharedState with given buffer sizes, all zeroed.
    pub fn new_zeroed(buffer_sizes: &Vec<usize>, workgroup_size: u32) -> (result: RuntimeSharedState)
        requires
            buffer_sizes@.len() > 0,
            // Total size fits in usize
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

        // Compute total size and offsets
        let mut total: usize = 0;
        let mut offsets: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == buffer_sizes@.len(),
                offsets@.len() == i,
                total == spec_partial_sum(buffer_sizes@, i as nat),
                total <= usize::MAX as nat,
                forall|k: int| 0 <= k < i as int ==>
                    offsets@[k] as nat == spec_offset(buffer_sizes@, k as nat),
            decreases n - i,
        {
            offsets.push(total);
            total = total + buffer_sizes[i];
            i = i + 1;
        }

        // Allocate flat zeroed data
        let data = vec_i64_zeroed(total);

        // Copy lengths
        let mut lengths: Vec<usize> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == buffer_sizes@.len(),
                lengths@.len() == j,
                forall|k: int| 0 <= k < j as int ==>
                    lengths@[k] == buffer_sizes@[k],
            decreases n - j,
        {
            lengths.push(buffer_sizes[j]);
            j = j + 1;
        }

        // Build ghost model
        let ghost spec_buffers = Seq::new(n as nat, |i: int|
            Seq::new(buffer_sizes@[i] as nat, |_j: int| 0int));
        let ghost model = SharedState {
            buffers: spec_buffers,
            workgroup_size: workgroup_size as nat,
        };

        RuntimeSharedState {
            data,
            offsets,
            lengths,
            workgroup_size,
            model: Ghost(model),
        }
    }
}

// ══════════════════════════════════════════════════════════════
// Spec helpers for flat layout
// ══════════════════════════════════════════════════════════════

/// Sum of buffer_sizes[0..k).
pub open spec fn spec_partial_sum(sizes: Seq<usize>, k: nat) -> nat
    decreases k,
{
    if k == 0 { 0 }
    else { spec_partial_sum(sizes, (k - 1) as nat) + sizes[(k - 1) as int] as nat }
}

/// Total size = sum of all buffer sizes.
pub open spec fn spec_total_size(sizes: Seq<usize>) -> nat {
    spec_partial_sum(sizes, sizes.len())
}

/// Offset of buffer b = sum of sizes[0..b).
pub open spec fn spec_offset(sizes: Seq<usize>, b: nat) -> nat {
    spec_partial_sum(sizes, b)
}

/// Create a zero-filled Vec<i64>.
fn vec_i64_zeroed(n: usize) -> (result: Vec<i64>)
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < n as int ==> result@[i] == 0i64,
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@.len() == i,
            forall|j: int| 0 <= j < i as int ==> v@[j] == 0i64,
        decreases n - i,
    {
        v.push(0i64);
        i = i + 1;
    }
    v
}

} // verus!
