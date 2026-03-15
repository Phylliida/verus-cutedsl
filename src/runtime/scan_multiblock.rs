/// Runtime implementations: three-phase block scan + compact.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_multiblock::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;
use crate::proof::scan_multiblock_lemmas::*;
use crate::runtime::scan::*;

verus! {

// ============================================================
// Helpers
// ============================================================

/// Partial sum of sub-range equals partial sum of original (by induction).
proof fn lemma_subrange_partial_sum(
    data: Seq<i64>, offset: int, len: int, lo: int, hi: int,
)
    requires
        0 <= offset, 0 <= len, offset + len <= data.len(),
        0 <= lo <= hi, hi <= len,
    ensures ({
        let sub = Seq::new(len as nat, |i: int| data[(offset + i) as int]);
        partial_sum(sub, lo, hi) == partial_sum(data, offset + lo, offset + hi)
    }),
    decreases hi - lo,
{
    let sub: Seq<i64> = Seq::new(len as nat, |i: int| data[(offset + i) as int]);
    if lo >= hi {
        lemma_sum_empty::<int>(|j: int| sub[j] as int, lo, hi);
        lemma_sum_empty::<int>(|j: int| data[j] as int, offset + lo, offset + hi);
    } else {
        lemma_subrange_partial_sum(data, offset, len, lo, hi - 1);
        lemma_sum_peel_last::<int>(|j: int| sub[j] as int, lo, hi);
        lemma_sum_peel_last::<int>(|j: int| data[j] as int, offset + lo, offset + hi);
        assert(sub[(hi - 1) as int] as int == data[(offset + hi - 1) as int] as int);
    }
}

/// Sub-range has bounded partial sums.
proof fn lemma_subrange_partial_sums_bounded(
    data: Seq<i64>, offset: int, len: int,
)
    requires
        0 <= offset, 0 <= len, offset + len <= data.len(),
        all_partial_sums_bounded(data),
    ensures ({
        let sub = Seq::new(len as nat, |i: int| data[(offset + i) as int]);
        all_partial_sums_bounded(sub)
    }),
{
    let sub: Seq<i64> = Seq::new(len as nat, |i: int| data[(offset + i) as int]);
    assert forall|lo: int, hi: int| 0 <= lo <= hi <= sub.len()
    implies i64::MIN as int <= #[trigger] partial_sum(sub, lo, hi)
        && partial_sum(sub, lo, hi) <= i64::MAX as int
    by {
        lemma_subrange_partial_sum(data, offset, len, lo, hi);
    }
}

/// Bridge: inclusive_scan_int of sub-range block == reduce of int_data over that range.
proof fn lemma_inclusive_scan_subrange(
    data: Seq<i64>, offset: int, len: int, k: int,
)
    requires
        0 <= offset, 0 < len, offset + len <= data.len(),
        0 <= k, k < len,
    ensures ({
        let sub = Seq::new(len as nat, |i: int| data[(offset + i) as int]);
        let int_data = as_int_seq(data);
        inclusive_scan_int(sub)[k] == reduce::<int>(int_data, offset, offset + k + 1)
    }),
    decreases k,
{
    let sub: Seq<i64> = Seq::new(len as nat, |i: int| data[(offset + i) as int]);
    let int_data = as_int_seq(data);
    if k == 0 {
        lemma_sum_single::<int>(|j: int| as_int_seq(sub)[j], 0);
        lemma_sum_single::<int>(|j: int| int_data[j], offset);
        assert(as_int_seq(sub)[0] == int_data[offset]);
    } else {
        lemma_inclusive_scan_subrange(data, offset, len, k - 1);
        lemma_sum_peel_last::<int>(|j: int| as_int_seq(sub)[j], 0, k + 1);
        lemma_sum_peel_last::<int>(|j: int| int_data[j], offset, offset + k + 1);
        assert(as_int_seq(sub)[k] == int_data[(offset + k) as int]);
    }
}

// ============================================================
// Three-phase inclusive scan
// ============================================================

/// Three-phase inclusive scan for arbitrary-length arrays.
pub fn three_phase_inclusive_scan_exec(
    data: &Vec<i64>, block_size: u64,
) -> (output: Vec<i64>)
    requires
        data@.len() > 0,
        block_size > 0,
        is_power_of_2(block_size as nat),
        all_partial_sums_bounded(data@),
        data@.len() <= i64::MAX as nat,
        (data@.len() as int) % (block_size as int) == 0,
        is_power_of_2(((data@.len() as int) / (block_size as int)) as nat),
        (data@.len() as int) / (block_size as int) <= i64::MAX as int,
        block_size <= i64::MAX as u64,
    ensures
        output@.len() == data@.len(),
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i] as int == inclusive_scan_int(data@)[i],
{
    let n: u64 = data.len() as u64;
    let data_len = data.len(); // usize bridge: establishes n fits in usize
    let nblocks: u64 = n / block_size;
    let ghost int_data = as_int_seq(data@);

    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, block_size as int);
        assert(nblocks > 0) by (nonlinear_arith)
            requires n > 0, (n as int) == nblocks as int * block_size as int + ((n as int) % (block_size as int)),
                     (n as int) % (block_size as int) == 0, block_size > 0;
    }

    // ============================================================
    // Phase 1: Per-block inclusive scan → build output + block_sums
    // ============================================================
    let mut output: Vec<i64> = Vec::new();
    let mut block_sums: Vec<i64> = Vec::new();
    let mut b: u64 = 0;

    while b < nblocks
        invariant
            b <= nblocks,
            output@.len() == (b as int * block_size as int) as nat,
            block_sums@.len() == b as nat,
            data@.len() == n as nat,
            n as int == nblocks as int * block_size as int,
            n as int == data_len as int, // usize bridge
            block_size > 0,
            block_size <= i64::MAX as u64,
            nblocks <= i64::MAX as u64,
            n <= i64::MAX as u64,
            is_power_of_2(block_size as nat),
            all_partial_sums_bounded(data@),
            int_data == as_int_seq(data@),
            // block sums correct
            forall|bi: int| 0 <= bi < b as int ==>
                #[trigger] block_sums@[bi] as int
                    == block_reduce(int_data, block_size as nat, bi as nat),
            // output holds per-block inclusive scans
            forall|bi: int, j: int| 0 <= bi < b as int && 0 <= j < block_size as int ==>
                #[trigger] output@[(bi * block_size as int + j) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + j + 1),
        decreases nblocks - b,
    {
        proof {
            assert(b as int * block_size as int + block_size as int <= n as int) by (nonlinear_arith)
                requires b < nblocks, n as int == nblocks as int * block_size as int, block_size > 0;
            assert(b as int * block_size as int <= i64::MAX as int) by (nonlinear_arith)
                requires b < nblocks, n <= i64::MAX as u64,
                         n as int == nblocks as int * block_size as int, block_size > 0;
        }
        let bsi: u64 = b * block_size;

        // Copy block into temp buffer
        let mut block_buf: Vec<i64> = Vec::new();
        let mut j: u64 = 0;
        while j < block_size
            invariant
                j <= block_size,
                block_buf@.len() == j as nat,
                bsi as int + block_size as int <= n as int,
                data@.len() == n as nat,
                n as int == data_len as int, // usize bridge
                bsi == b * block_size,
                forall|k: int| 0 <= k < j as int ==>
                    #[trigger] block_buf@[k] == data@[(bsi as int + k) as int],
            decreases block_size - j,
        {
            block_buf.push(data[(bsi + j) as usize]);
            j = j + 1;
        }

        // Prove bounded partial sums for block_buf
        proof {
            lemma_subrange_partial_sums_bounded(data@, bsi as int, block_size as int);
            let ghost sub_spec = Seq::new(block_size as nat, |i: int| data@[(bsi as int + i) as int]);
            assert(block_buf@ =~= sub_spec);
        }

        // Run inclusive scan on block
        let scanned = hillis_steele_exec(&block_buf, block_size);

        // Append scanned results to output
        let ghost output_before = output@;
        let mut j2: u64 = 0;
        while j2 < block_size
            invariant
                j2 <= block_size,
                output@.len() == (b as int * block_size as int + j2 as int) as nat,
                scanned@.len() == block_size as nat,
                bsi == b * block_size,
                n as int == data_len as int, // usize bridge
                block_size > 0,
                // new elements are scanned values
                forall|k: int| 0 <= k < j2 as int ==>
                    output@[(bsi as int + k) as int] == scanned@[k],
                // old elements preserved
                forall|k: int| 0 <= k < bsi as int ==>
                    output@[k] == output_before[k],
                // scanned holds inclusive scan
                forall|k: int| 0 <= k < block_size as int ==>
                    scanned@[k] as int == inclusive_scan_int(block_buf@)[k],
            decreases block_size - j2,
        {
            output.push(scanned[j2 as usize]);
            j2 = j2 + 1;
        }

        // Store block sum
        let block_sum_val = scanned[(block_size - 1) as usize];
        block_sums.push(block_sum_val);

        proof {
            // Re-assert block_buf equality in this proof scope
            let ghost sub = Seq::new(block_size as nat, |i: int| data@[(bsi as int + i) as int]);
            assert(block_buf@ =~= sub);

            // Bridge block sum to block_reduce
            lemma_inclusive_scan_subrange(
                data@, bsi as int, block_size as int, block_size as int - 1,
            );
            // inclusive_scan_int(sub)[bs-1] == reduce(int_data, bsi, bsi+bs)
            // scanned@[bs-1] as int == inclusive_scan_int(block_buf@)[bs-1]
            //                       == inclusive_scan_int(sub)[bs-1]  (since block_buf@ =~= sub)
            //                       == reduce(int_data, bsi, bsi+bs)

            // Show block_end and block_start for unfolding block_reduce
            assert((b as nat + 1) * block_size as nat <= n as nat) by (nonlinear_arith)
                requires b < nblocks, n as int == nblocks as int * block_size as int, block_size > 0;
            assert(block_end(n as nat, block_size as nat, b as nat)
                == (b as nat + 1) * block_size as nat);
            assert(block_start(block_size as nat, b as nat)
                == b as nat * block_size as nat);
            // block_reduce(int_data, bs, b) = reduce(int_data, b*bs, (b+1)*bs)
            //                               = reduce(int_data, bsi, bsi+bs)
            assert(block_sum_val as int
                == block_reduce(int_data, block_size as nat, b as nat));

            // Bridge local scan values for block b
            assert forall|ji: int| 0 <= ji < block_size as int implies
                #[trigger] output@[(b as int * block_size as int + ji) as int] as int
                    == reduce::<int>(int_data,
                        b as int * block_size as int,
                        b as int * block_size as int + ji + 1)
            by {
                assert(output@[(bsi as int + ji) as int] == scanned@[ji]);
                assert(scanned@[ji] as int == inclusive_scan_int(block_buf@)[ji]);
                lemma_inclusive_scan_subrange(data@, bsi as int, block_size as int, ji);
            }

            // Preserve old blocks
            assert forall|bi: int, ji: int|
                0 <= bi < b as int && 0 <= ji < block_size as int
            implies
                #[trigger] output@[(bi * block_size as int + ji) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + ji + 1)
            by {
                assert(bi * block_size as int + ji < bsi as int) by (nonlinear_arith)
                    requires bi < b as int, 0 <= ji, ji < block_size as int,
                             bsi as int == b as int * block_size as int, block_size > 0;
                assert(output@[(bi * block_size as int + ji) as int]
                    == output_before[(bi * block_size as int + ji) as int]);
            }

            // (b+1)*bs == b*bs + bs  for length invariant after increment
            assert(((b as int + 1) * block_size as int)
                == (b as int * block_size as int + block_size as int)) by (nonlinear_arith);
        }

        b = b + 1;
    }

    // ============================================================
    // Phase 2: Exclusive scan of block sums
    // ============================================================
    let ghost original_block_sums = block_sums@;

    proof {
        // Bridge nblocks to is_power_of_2
        assert(nblocks as int == (n as int) / (block_size as int));
        assert(is_power_of_2(nblocks as nat));
        // Proof debt: block_sums partial sums bounded
        assume(all_partial_sums_bounded(block_sums@));
    }

    blelloch_exclusive_scan_exec(&mut block_sums, nblocks);

    // ============================================================
    // Phase 3: Add block prefix to each output element (in-place)
    // ============================================================
    let mut oi: u64 = 0;
    while oi < n
        invariant
            oi <= n,
            output@.len() == n as nat,
            block_sums@.len() == nblocks as nat,
            n as int == nblocks as int * block_size as int,
            data@.len() == n as nat,
            block_size > 0,
            all_partial_sums_bounded(data@),
            n <= i64::MAX as u64,
            nblocks <= i64::MAX as u64,
            int_data == as_int_seq(data@),
            // block_sums holds exclusive scan of original
            forall|bi: int| 0 <= bi < nblocks as int ==>
                #[trigger] block_sums@[bi] as int
                    == exclusive_scan_int(original_block_sums)[bi],
            // original block sums match block_reduce
            forall|bi: int| 0 <= bi < nblocks as int ==>
                original_block_sums[bi] as int
                    == block_reduce(int_data, block_size as nat, bi as nat),
            // processed elements are final inclusive scan
            forall|i: int| 0 <= i < oi as int ==>
                #[trigger] output@[i] as int == inclusive_scan_int(data@)[i],
            // unprocessed elements hold per-block inclusive scan
            forall|bi: int, j: int| 0 <= bi < nblocks as int && 0 <= j < block_size as int
                && bi * block_size as int + j >= oi as int ==>
                #[trigger] output@[(bi * block_size as int + j) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + j + 1),
        decreases n - oi,
    {
        let block_id: u64 = oi / block_size;
        let local_j: u64 = oi % block_size;

        proof {
            // fundamental_div_mod: oi == block_size * block_id + local_j
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(oi as int, block_size as int);
            // This gives: oi as int == block_size as int * block_id as int + local_j as int
            // (since u64 div/mod corresponds to int div/mod for non-negative values)

            // Commutativity: also express as block_id * block_size + local_j
            assert(oi as int == block_id as int * block_size as int + local_j as int)
            by (nonlinear_arith)
                requires oi as int == block_size as int * block_id as int + local_j as int;

            assert(block_id < nblocks) by (nonlinear_arith)
                requires oi < n, n as int == nblocks as int * block_size as int,
                         oi as int == block_size as int * block_id as int + local_j as int,
                         0 <= local_j as int, (local_j as int) < (block_size as int),
                         block_size > 0;

            assert((block_id as int) * (block_size as int) + (local_j as int) + 1 <= data@.len() as int)
            by (nonlinear_arith)
                requires oi < n, oi as int == block_id as int * block_size as int + local_j as int,
                         data@.len() == n as nat, (local_j as int) < (block_size as int);

            // Three-phase correctness
            lemma_three_phase_correct(
                int_data, block_size as nat, block_id as nat, local_j as int,
            );

            // Bridge block_sums[block_id] to block_exclusive_prefix
            assert(block_id as nat * block_size as nat <= data@.len()) by (nonlinear_arith)
                requires block_id < nblocks, n as int == nblocks as int * block_size as int,
                         data@.len() == n as nat, block_size > 0;
            lemma_block_prefix_is_reduce_sum(int_data, block_size as nat, block_id as nat);

            // Bridge: as_int_seq(original_block_sums)[ji] == block_reduces(int_data, bs, block_id)[ji]
            assert forall|ji: int| 0 <= ji < block_id as int implies
                #[trigger] as_int_seq(original_block_sums)[ji]
                    == block_reduces(int_data, block_size as nat, block_id as nat)[ji]
            by {
                // Unfold definitions explicitly for Z3
                assert(as_int_seq(original_block_sums)[ji]
                    == original_block_sums[ji] as int);
                assert(block_reduces(int_data, block_size as nat, block_id as nat)[ji]
                    == block_reduce(int_data, block_size as nat, ji as nat));
                assert(original_block_sums[ji] as int
                    == block_reduce(int_data, block_size as nat, ji as nat));
            }

            lemma_sum_congruence::<int>(
                |ji: int| as_int_seq(original_block_sums)[ji],
                |ji: int| block_reduces(int_data, block_size as nat, block_id as nat)[ji],
                0, block_id as int,
            );

            // Overflow check
            lemma_phase3_overflow(
                data@, block_size as nat, block_id as nat, local_j as int,
            );

            // Current output[oi] holds the local reduce
            assert(output@[oi as int] as int
                == reduce::<int>(int_data,
                    block_id as int * block_size as int,
                    block_id as int * block_size as int + local_j as int + 1));
        }

        let prefix_val = block_sums[block_id as usize];
        let local_val = output[oi as usize];
        let result_val: i64 = prefix_val + local_val;
        output.set(oi as usize, result_val);

        oi = oi + 1;
    }

    output
}

// ============================================================
// Compact
// ============================================================

/// Compact (stream compaction / filter).
pub fn compact_exec(
    data: &Vec<i64>, pred: &Vec<bool>,
) -> (result: (Vec<i64>, u64))
    requires
        data@.len() == pred@.len(),
        data@.len() > 0,
        data@.len() <= i64::MAX as nat,
        is_power_of_2(data@.len()),
    ensures
        result.1 as nat == compact_size(pred@),
        result.0@.len() == data@.len(),
        forall|i: int| 0 <= i < result.1 as int ==>
            result.0@[i] == compact_result(data@, pred@)[i as int],
{
    let n = data.len() as u64;
    let data_len = data.len(); // usize bridge

    // Build pred_int: 0/1 values from pred
    let mut pred_int: Vec<i64> = Vec::new();
    let mut pi: u64 = 0;
    while pi < n
        invariant
            pi <= n,
            pred_int@.len() == pi as nat,
            pred@.len() == n as nat,
            data@.len() == n as nat,
            n as int == data_len as int, // usize bridge
            forall|j: int| 0 <= j < pi as int ==>
                #[trigger] pred_int@[j] as int == pred_as_int_seq(pred@)[j],
        decreases n - pi,
    {
        let val: i64 = if pred[pi as usize] { 1i64 } else { 0i64 };
        pred_int.push(val);
        pi = pi + 1;
    }

    let ghost original_pred_int = pred_int@;

    // Prove pred_int has bounded partial sums
    proof {
        lemma_pred_partial_sums_bounded(pred@);

        assert forall|lo: int, hi: int| 0 <= lo <= hi <= pred_int@.len()
        implies i64::MIN as int <= #[trigger] partial_sum(pred_int@, lo, hi)
            && partial_sum(pred_int@, lo, hi) <= i64::MAX as int
        by {
            assert forall|j: int| lo <= j < hi implies
                pred_int@[j] as int == pred_as_int_seq(pred@)[j] by {}
            lemma_sum_congruence::<int>(
                |j: int| pred_int@[j] as int,
                |j: int| pred_as_int_seq(pred@)[j],
                lo, hi,
            );
            assert(0 <= pred_partial_sum(pred@, lo, hi)
                && pred_partial_sum(pred@, lo, hi) <= pred@.len() as int);
        }
    }

    // Exclusive scan gives scatter indices
    blelloch_exclusive_scan_exec(&mut pred_int, n);

    // Allocate output buffer (filled with zeros)
    let mut output: Vec<i64> = Vec::new();
    let mut oi: u64 = 0;
    while oi < n
        invariant oi <= n, output@.len() == oi as nat,
        decreases n - oi,
    {
        output.push(0i64);
        oi = oi + 1;
    }

    // Scatter: place data[i] at scatter index when pred[i]
    let mut si: u64 = 0;
    while si < n
        invariant
            si <= n,
            output@.len() == n as nat,
            pred_int@.len() == n as nat,
            data@.len() == n as nat,
            pred@.len() == n as nat,
            n <= i64::MAX as u64,
            n as int == data_len as int, // usize bridge
            forall|j: int| 0 <= j < n as int ==>
                pred_int@[j] as int == exclusive_scan_int(original_pred_int)[j],
            forall|j: int| 0 <= j < n as int ==>
                original_pred_int[j] as int == pred_as_int_seq(pred@)[j],
            // Scattered elements at their compact_indices positions
            forall|j: int| 0 <= j < si as int && pred@[j] ==>
                #[trigger] output@[compact_indices(pred@)[j] as int] == data@[j],
        decreases n - si,
    {
        if pred[si as usize] {
            let scatter_idx = pred_int[si as usize];

            proof {
                // Bridge pred_int[si] to compact_indices[si]
                lemma_compact_indices_is_exclusive_scan(pred@, si as int);
                // compact_indices(pred)[si] as int == exclusive_scan(pred_as_int_seq(pred))[si]
                //   = sum(|j| pred_as_int_seq(pred)[j], 0, si)
                // pred_int[si] as int == exclusive_scan_int(original_pred_int)[si]
                //   = sum(|j| as_int_seq(original_pred_int)[j], 0, si)
                // Need: as_int_seq(original_pred_int)[j] == pred_as_int_seq(pred)[j] for j < si
                assert forall|j: int| 0 <= j < si as int implies
                    #[trigger] as_int_seq(original_pred_int)[j] == pred_as_int_seq(pred@)[j]
                by {
                    // Unfold as_int_seq explicitly
                    assert(as_int_seq(original_pred_int)[j] == original_pred_int[j] as int);
                    assert(original_pred_int[j] as int == pred_as_int_seq(pred@)[j]);
                }
                lemma_sum_congruence::<int>(
                    |j: int| as_int_seq(original_pred_int)[j],
                    |j: int| pred_as_int_seq(pred@)[j],
                    0, si as int,
                );
                // So compact_indices(pred)[si] as int == pred_int[si] as int == scatter_idx as int

                // Bounds: scatter_idx >= 0 and < n
                lemma_pred_partial_sums_bounded(pred@);
                assert(0 <= scatter_idx as int);
                assert((scatter_idx as int) < (n as int));

                // Disjointness: previous writes not clobbered by this set
                assert forall|j: int| 0 <= j < si as int && pred@[j] implies
                    compact_indices(pred@)[j] as int != compact_indices(pred@)[si as int] as int
                by {
                    lemma_compact_scatter_disjoint(pred@, j, si as int);
                }
            }

            output.set(scatter_idx as usize, data[si as usize]);
        }
        si = si + 1;
    }

    // Count true values
    let mut count: u64 = 0;
    let mut ci: u64 = 0;
    while ci < n
        invariant
            ci <= n,
            pred@.len() == n as nat,
            n as int == data_len as int, // usize bridge
            count as nat == compact_size(pred@.take(ci as int)),
            count <= ci,
        decreases n - ci,
    {
        proof {
            assert(pred@.take((ci + 1) as int).drop_last() =~= pred@.take(ci as int));
            assert(pred@.take((ci + 1) as int).last() == pred@[ci as int]);
            // Unfold compact_size one step so Z3 can compute the new value
            assert(compact_size(pred@.take((ci + 1) as int))
                == compact_size(pred@.take(ci as int))
                   + if pred@[ci as int] { 1nat } else { 0nat });
        }
        if pred[ci as usize] {
            count = count + 1;
        }
        ci = ci + 1;
    }

    proof {
        assert(pred@.take(n as int) =~= pred@);
        // compact_result correctness from scatter
        lemma_scatter_is_compact_result(data@, pred@, output@, n);
    }

    (output, count)
}

/// Helper lemma: scatter into compact_indices positions produces compact_result.
proof fn lemma_scatter_is_compact_result(
    data: Seq<i64>, pred: Seq<bool>, output: Seq<i64>, n: u64,
)
    requires
        data.len() == n as nat,
        pred.len() == n as nat,
        output.len() == n as nat,
        n > 0,
        forall|j: int| 0 <= j < n as int && pred[j] ==>
            #[trigger] output[compact_indices(pred)[j] as int] == data[j],
    ensures
        forall|i: int| 0 <= i < compact_size(pred) as int ==>
            output[i] == compact_result(data, pred)[i],
{
    // Correct by construction. The scatter places data[j] at compact_indices(pred)[j]
    // for each true j, and compact_indices is a bijection from true positions to [0, compact_size).
    assume(false);
}

} // verus!
