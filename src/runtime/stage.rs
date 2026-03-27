/// Runtime (exec) shared state for CPU-side Stage evaluation.
///
/// Follows the RuntimeLayout pattern: concrete Vec<Vec<i64>> buffers
/// with a Ghost<SharedState> model. The `wf_spec()` predicate bridges
/// concrete i64 values to spec-level int values.
///
/// Used for:
/// 1. CPU cross-validation against GPU output
/// 2. Exec-level proofs that connect runtime to staged_eval spec

use vstd::prelude::*;
use crate::stage::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Spec helpers for bridging i64 ↔ int buffers
// ══════════════════════════════════════════════════════════════

/// Convert a Vec<i64> to Seq<int> for spec reasoning.
pub open spec fn i64_vec_to_int_seq(v: Seq<i64>) -> Seq<int> {
    Seq::new(v.len(), |i: int| v[i] as int)
}

/// Convert Vec<Vec<i64>> to Seq<Seq<int>> for spec reasoning.
pub open spec fn buffers_to_spec(bufs: Seq<Seq<i64>>) -> Seq<Seq<int>> {
    Seq::new(bufs.len(), |i: int| i64_vec_to_int_seq(bufs[i]))
}

// ══════════════════════════════════════════════════════════════
// RuntimeSharedState
// ══════════════════════════════════════════════════════════════

/// Exec-level shared state: concrete i64 buffers + ghost spec model.
pub struct RuntimeSharedState {
    pub buffers: Vec<Vec<i64>>,
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
    /// Well-formedness: concrete matches ghost, all values representable.
    pub open spec fn wf_spec(&self) -> bool {
        // Buffer counts match
        &&& self.buffers@.len() == self@.buffers.len()
        // Workgroup size matches
        &&& self.workgroup_size as nat == self@.workgroup_size
        // Each buffer: length matches, values match
        &&& forall|i: int| 0 <= i < self.buffers@.len() ==> {
            &&& (#[trigger] self.buffers@[i]).len() == self@.buffers[i].len()
            &&& forall|j: int| 0 <= j < self.buffers@[i].len() ==>
                self.buffers@[i][j] as int == (#[trigger] self@.buffers[i])[j]
        }
    }

    /// Number of buffers.
    pub fn num_buffers(&self) -> (result: usize)
        requires self.wf_spec(),
        ensures result as nat == self@.num_buffers(),
    {
        self.buffers.len()
    }

    /// Length of a specific buffer.
    pub fn buffer_len(&self, buf: usize) -> (result: usize)
        requires self.wf_spec(), buf < self@.num_buffers(),
        ensures result as nat == self@.buffer_len(buf as nat),
    {
        self.buffers[buf].len()
    }

    /// Read a value from a buffer.
    pub fn read(&self, buf: usize, idx: usize) -> (result: i64)
        requires
            self.wf_spec(),
            buf < self@.num_buffers(),
            idx < self@.buffer_len(buf as nat),
        ensures
            result as int == self@.read(buf as nat, idx as nat),
    {
        self.buffers[buf][idx]
    }

    /// Write a value to a buffer.
    pub fn write(&mut self, buf: usize, idx: usize, val: i64)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            idx < old(self)@.buffer_len(buf as nat),
        ensures
            self.wf_spec(),
            self@ == old(self)@.write(buf as nat, idx as nat, val as int),
    {
        self.buffers[buf].set(idx, val);
        proof {
            self.model = Ghost(old(self)@.write(buf as nat, idx as nat, val as int));
        }
    }

    /// Create a RuntimeSharedState with given buffer sizes, initialized to zero.
    pub fn new_zeroed(buffer_sizes: &Vec<usize>, workgroup_size: u32) -> (result: RuntimeSharedState)
        requires buffer_sizes@.len() > 0,
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
        let mut buffers: Vec<Vec<i64>> = Vec::new();
        let n = buffer_sizes.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == buffer_sizes@.len(),
                buffers@.len() == i,
                forall|k: int| 0 <= k < i as int ==> {
                    &&& (#[trigger] buffers@[k]).len() == buffer_sizes@[k] as nat
                    &&& forall|j: int| 0 <= j < buffers@[k].len() ==> buffers@[k][j] == 0i64
                },
            decreases n - i,
        {
            let size = buffer_sizes[i];
            let buf: Vec<i64> = vec_i64_zeroed(size);
            buffers.push(buf);
            i = i + 1;
        }

        let ghost spec_buffers = Seq::new(n as nat, |i: int|
            Seq::new(buffer_sizes@[i] as nat, |j: int| 0int));
        let ghost model = SharedState {
            buffers: spec_buffers,
            workgroup_size: workgroup_size as nat,
        };

        RuntimeSharedState {
            buffers,
            workgroup_size,
            model: Ghost(model),
        }
    }
}

/// Create a zero-filled Vec<i64> of a given size.
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
