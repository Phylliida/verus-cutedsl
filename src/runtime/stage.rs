/// Runtime (exec) shared state for CPU-side Stage evaluation.
///
/// Follows the RuntimeLayout pattern: concrete Vec<Vec<i64>> buffers
/// with a Ghost<SharedState> model. The `wf_spec()` predicate bridges
/// concrete i64 values to spec-level int values.
///
/// TODO: Migrate to flat Vec<i64> with offsets for O(1) writes and
/// better GPU memory model match. Currently uses Vec<Vec<i64>> because
/// Verus's nested &mut limitation requires rebuilding inner Vecs on write.

use vstd::prelude::*;
use crate::stage::*;

verus! {

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
        &&& self.buffers@.len() == self@.buffers.len()
        &&& self.workgroup_size as nat == self@.workgroup_size
        &&& forall|i: int| 0 <= i < self.buffers@.len() ==> {
            &&& (#[trigger] self.buffers@[i]).len() == self@.buffers[i].len()
            &&& forall|j: int| 0 <= j < self.buffers@[i].len() ==>
                self.buffers@[i][j] as int == (#[trigger] self@.buffers[i])[j]
        }
    }

    pub fn num_buffers(&self) -> (result: usize)
        requires self.wf_spec(),
        ensures result as nat == self@.num_buffers(),
    {
        self.buffers.len()
    }

    pub fn buffer_len(&self, buf: usize) -> (result: usize)
        requires self.wf_spec(), buf < self@.num_buffers(),
        ensures result as nat == self@.buffer_len(buf as nat),
    {
        self.buffers[buf].len()
    }

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
    /// Rebuilds the inner Vec (Verus doesn't support nested &mut indexing).
    pub fn write(&mut self, buf: usize, idx: usize, val: i64)
        requires
            old(self).wf_spec(),
            buf < old(self)@.num_buffers(),
            idx < old(self)@.buffer_len(buf as nat),
        ensures
            self.wf_spec(),
            self@ == old(self)@.write(buf as nat, idx as nat, val as int),
    {
        let len = self.buffers[buf].len();
        let mut new_inner: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                0 <= k <= len,
                len == old(self).buffers@[buf as int].len(),
                new_inner@.len() == k,
                self.buffers@ == old(self).buffers@,
                self.workgroup_size == old(self).workgroup_size,
                self.model == old(self).model,
                buf < self.buffers@.len(),
                forall|i: int| 0 <= i < k as int ==>
                    new_inner@[i] == if i == idx as int { val }
                        else { self.buffers@[buf as int][i] },
            decreases len - k,
        {
            if k == idx {
                new_inner.push(val);
            } else {
                new_inner.push(self.buffers[buf][k]);
            }
            k = k + 1;
        }
        self.buffers.set(buf, new_inner);
        self.model = Ghost(old(self)@.write(buf as nat, idx as nat, val as int));
    }

    /// Create with given buffer sizes, all zeroed.
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
            let buf = vec_i64_zeroed(buffer_sizes[i]);
            buffers.push(buf);
            i = i + 1;
        }

        let ghost spec_buffers = Seq::new(n as nat, |i: int|
            Seq::new(buffer_sizes@[i] as nat, |_j: int| 0int));

        RuntimeSharedState {
            buffers,
            workgroup_size,
            model: Ghost(SharedState {
                buffers: spec_buffers,
                workgroup_size: workgroup_size as nat,
            }),
        }
    }
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
