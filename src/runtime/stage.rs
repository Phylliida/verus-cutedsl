/// Runtime (exec) shared state for CPU-side Stage evaluation.
///
/// Flat buffer layout (single Vec<i64> with offsets) matching how GPU
/// shared memory actually works. O(1) reads and writes.

use vstd::prelude::*;
use crate::stage::*;

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
        let off = self.offsets[buf];
        let len = self.lengths[buf];
        proof {
            assert(off as nat + len as nat <= old(self).data@.len());
            assert(idx < len);
        }
        assert(off + idx < self.data.len());
        self.data.set(off + idx, val);
        self.model = Ghost(old(self)@.write(buf as nat, idx as nat, val as int));
        proof {
            // Prove wf_spec is maintained
            let n = old(self)@.buffers.len();
            let pos = off as int + idx as int;

            // For each buffer b, show values still match
            assert forall|b: int| #![trigger self.offsets@[b], self.lengths@[b]]
                0 <= b < n implies {
                &&& self.lengths@[b] as nat == self@.buffers[b].len()
                &&& self.offsets@[b] as nat + self.lengths@[b] as nat <= self.data@.len()
                &&& forall|j: int| 0 <= j < self.lengths@[b] as int ==>
                    self.data@[self.offsets@[b] as int + j] as int == self@.buffers[b][j]
            } by {
                // offsets and lengths unchanged
                assert(self.offsets@[b] == old(self).offsets@[b]);
                assert(self.lengths@[b] == old(self).lengths@[b]);
                let ob = self.offsets@[b] as int;
                let lb = self.lengths@[b] as int;

                if b == buf as int {
                    // Target buffer: position idx has new value, others unchanged
                    assert forall|j: int| 0 <= j < lb implies
                        self.data@[ob + j] as int == self@.buffers[b][j]
                    by {
                        if j == idx as int {
                            // Written position: data[pos] = val, spec says val as int
                        } else {
                            // Other positions: data unchanged at ob + j != pos
                            assert(ob + j != pos);
                        }
                    }
                } else {
                    // Other buffer: region doesn't contain pos
                    assert forall|j: int| 0 <= j < lb implies
                        self.data@[ob + j] as int == self@.buffers[b][j]
                    by {
                        // ob + j != pos because regions don't overlap
                        if b < buf as int {
                            assert(ob + lb <= old(self).offsets@[buf as int] as int);
                            assert(ob + j < ob + lb);
                            assert(ob + j < pos);
                        } else {
                            assert(old(self).offsets@[buf as int] as nat
                                + old(self).lengths@[buf as int] as nat
                                <= ob as nat);
                            assert(pos < old(self).offsets@[buf as int] as int
                                + old(self).lengths@[buf as int] as int);
                            assert(pos < ob);
                            assert(ob + j >= ob);
                        }
                        assert(ob + j != pos);
                    }
                }
            }
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

        // Compute offsets (consecutive)
        let mut total: usize = 0;
        let mut offsets: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == buffer_sizes@.len(),
                offsets@.len() == i,
                total as nat == spec_partial_sum(buffer_sizes@, i as nat),
                total as nat <= usize::MAX as nat,
                forall|k: int| 0 <= k < i as int ==>
                    offsets@[k] as nat == spec_partial_sum(buffer_sizes@, k as nat),
            decreases n - i,
        {
            offsets.push(total);
            proof {
                lemma_partial_sum_step(buffer_sizes@, i as nat);
                lemma_partial_sum_monotone(buffer_sizes@, (i + 1) as nat);
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

} // verus!
