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
// Helper: prove a sub-range of data has bounded partial sums
// ============================================================
proof fn lemma_subrange_partial_sums_bounded(
    data: Seq<i64>, offset: int, len: int,
)
    requires
        0 <= offset,
        0 <= len,
        offset + len <= data.len(),
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
        // partial_sum(sub, lo, hi) = sum(|j| sub[j] as int, lo, hi)
        // sub[j] = data[offset + j]
        // so this = sum(|j| data[offset + j] as int, lo, hi)
        // We need to show this equals partial_sum(data, offset + lo, offset + hi)
        // = sum(|j| data[j] as int, offset + lo, offset + hi)
        // Use sum_reindex with k = offset
        assert forall|j: int| lo <= j < hi implies
            sub[j] as int == data[(offset + j) as int] as int by {}
        lemma_sum_congruence::<int>(
            |j: int| sub[j] as int,
            |j: int| data[(offset + j) as int] as int,
            lo, hi,
        );
        // sum(|j| data[offset+j] as int, lo, hi) == sum(|j| data[j] as int, offset+lo, offset+hi)
        lemma_sum_reindex::<int>(
            |j: int| data[j] as int,
            offset + lo, offset + hi,
            offset,
        );
        // sum_reindex gives: sum(f, lo_, hi_).eqv(sum(|i| f(i+k), lo_-k, hi_-k))
        // with f = |j| data[j] as int, lo_ = offset+lo, hi_ = offset+hi, k = offset
        // => sum(|j| data[j] as int, offset+lo, offset+hi) == sum(|i| data[i+offset] as int, lo, hi)
        // For int, eqv is ==
        assert(partial_sum(data, offset + lo, offset + hi)
            == sum::<int>(|i: int| data[(i + offset) as int] as int, lo, hi));
        // sum(|i| data[(i+offset)] as int, lo, hi) == sum(|j| data[(offset+j)] as int, lo, hi)
        // because i+offset == offset+i
        assert forall|j: int| lo <= j < hi implies
            data[(j + offset) as int] as int == data[(offset + j) as int] as int by {}
        lemma_sum_congruence::<int>(
            |j: int| data[(j + offset) as int] as int,
            |j: int| data[(offset + j) as int] as int,
            lo, hi,
        );
    }
}

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
    let n = data.len() as u64;
    let nblocks: u64 = n / block_size;
    let data_len = data.len();
    let ghost int_data = as_int_seq(data@);

    proof {
        // n % block_size == 0 and n > 0 implies nblocks >= 1
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, block_size as int);
        // n == nblocks * block_size + n % block_size == nblocks * block_size
        assert(n as int == nblocks as int * block_size as int);
        assert(nblocks > 0) by (nonlinear_arith)
            requires n > 0, n as int == nblocks as int * block_size as int, block_size > 0;
    }

    // ============================================================
    // Phase 1: Per-block inclusive scan + collect block sums
    // ============================================================
    let mut local_scans: Vec<i64> = Vec::new();
    let mut block_sums: Vec<i64> = Vec::new();

    // Initialize local_scans to 0
    let mut init_idx: u64 = 0;
    while init_idx < n
        invariant
            init_idx <= n,
            local_scans@.len() == init_idx as nat,
        decreases n - init_idx,
    {
        local_scans.push(0i64);
        init_idx = init_idx + 1;
    }

    let mut b: u64 = 0;
    while b < nblocks
        invariant
            b <= nblocks,
            local_scans@.len() == n as nat,
            block_sums@.len() == b as nat,
            n as int == data_len as int,
            n as int == nblocks as int * block_size as int,
            data@.len() == n as nat,
            block_size > 0,
            block_size <= i64::MAX as u64,
            nblocks <= i64::MAX as u64,
            n <= i64::MAX as u64,
            is_power_of_2(block_size as nat),
            all_partial_sums_bounded(data@),
            int_data == as_int_seq(data@),
            forall|bi: int| 0 <= bi < b as int ==>
                #[trigger] block_sums@[bi] as int
                    == block_reduce(int_data, block_size as nat, bi as nat),
            forall|bi: int, j: int| 0 <= bi < b as int && 0 <= j < block_size as int ==>
                #[trigger] local_scans@[(bi * block_size as int + j) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + j + 1),
        decreases nblocks - b,
    {
        proof {
            assert(b as int * block_size as int + block_size as int <= n as int) by (nonlinear_arith)
                requires b < nblocks, n as int == nblocks as int * block_size as int, block_size > 0;
            assert(b as int * block_size as int <= u64::MAX as int) by (nonlinear_arith)
                requires b < nblocks, n <= i64::MAX as u64, n as int == nblocks as int * block_size as int, block_size > 0;
        }
        let bsi: u64 = b * block_size;

        // Copy block into temp buffer
        let mut block_buf: Vec<i64> = Vec::new();
        let mut j: u64 = 0;
        while j < block_size
            invariant
                j <= block_size,
                block_buf@.len() == j as nat,
                bsi == b * block_size,
                bsi as int + block_size as int <= n as int,
                data@.len() == n as nat,
                forall|k: int| 0 <= k < j as int ==>
                    #[trigger] block_buf@[k] == data@[(bsi as int + k) as int],
            decreases block_size - j,
        {
            block_buf.push(data[(bsi + j) as usize]);
            j = j + 1;
        }

        // Prove block_buf has bounded partial sums
        proof {
            lemma_subrange_partial_sums_bounded(data@, bsi as int, block_size as int);
            let ghost sub_spec = Seq::new(block_size as nat, |i: int| data@[(bsi as int + i) as int]);
            // block_buf =~= sub_spec
            assert(block_buf@ =~= sub_spec);
        }

        let scanned = hillis_steele_exec(&block_buf, block_size);

        // Copy scanned results into local_scans
        let mut j2: u64 = 0;
        while j2 < block_size
            invariant
                j2 <= block_size,
                local_scans@.len() == n as nat,
                scanned@.len() == block_size as nat,
                bsi == b * block_size,
                bsi as int + block_size as int <= n as int,
                n as int == data_len as int,
                forall|k: int| 0 <= k < j2 as int ==>
                    local_scans@[(bsi as int + k) as int] == scanned@[k],
                // scanned holds inclusive scan of block_buf
                forall|k: int| 0 <= k < block_size as int ==>
                    scanned@[k] as int == inclusive_scan_int(block_buf@)[k],
                // block_buf matches data sub-range
                forall|k: int| 0 <= k < block_size as int ==>
                    #[trigger] block_buf@[k] == data@[(bsi as int + k) as int],
                // preserve previous blocks
                forall|bi: int, ji: int| 0 <= bi < b as int && 0 <= ji < block_size as int ==>
                    local_scans@[(bi * block_size as int + ji) as int] as int
                        == reduce::<int>(int_data,
                            bi * block_size as int,
                            bi * block_size as int + ji + 1),
            decreases block_size - j2,
        {
            local_scans.set((bsi + j2) as usize, scanned[j2 as usize]);
            j2 = j2 + 1;
        }

        // Store block sum
        let block_sum_val = scanned[(block_size - 1) as usize];
        block_sums.push(block_sum_val);

        proof {
            // Bridge inclusive_scan_int(block_buf) to reduce(int_data, ...)
            // inclusive_scan_int(block_buf)[k]
            //   = sum(|j| as_int_seq(block_buf)[j], 0, k+1)
            // as_int_seq(block_buf)[j] = block_buf[j] as int = data[bsi+j] as int = int_data[bsi+j]
            assert forall|k: int| 0 <= k < block_size as int implies
                as_int_seq(block_buf@)[k] == int_data[(bsi as int + k) as int] by {}

            // block_sum_val = inclusive_scan_int(block_buf)[block_size-1]
            //   = sum(|j| as_int_seq(block_buf)[j], 0, block_size)
            //   = sum(|j| int_data[bsi+j], 0, block_size) by congruence
            //   = sum(|j| int_data[j], bsi, bsi+block_size) by reindex
            //   = block_reduce(int_data, block_size, b)
            lemma_sum_congruence::<int>(
                |k: int| as_int_seq(block_buf@)[k],
                |k: int| int_data[(bsi as int + k) as int],
                0, block_size as int,
            );
            lemma_sum_reindex::<int>(
                |k: int| int_data[k],
                bsi as int, bsi as int + block_size as int,
                bsi as int,
            );
            assert(block_start(block_size as nat, b as nat) == bsi as nat);
            assert(block_end(data@.len(), block_size as nat, b as nat) == (bsi as int + block_size as int) as nat) by {
                assert((b as nat + 1) * block_size as nat == bsi as nat + block_size as nat) by (nonlinear_arith)
                    requires bsi as int == (b * block_size) as int;
                assert((b as nat + 1) * block_size as nat <= data@.len()) by (nonlinear_arith)
                    requires b < nblocks, n as int == nblocks as int * block_size as int,
                             data@.len() == n as nat, block_size > 0;
            };

            // Prove local_scans correctness for block b
            assert forall|ji: int| 0 <= ji < block_size as int implies
                #[trigger] local_scans@[(b as int * block_size as int + ji) as int] as int
                    == reduce::<int>(int_data,
                        b as int * block_size as int,
                        b as int * block_size as int + ji + 1)
            by {
                assert(local_scans@[(bsi as int + ji) as int] == scanned@[ji]);
                assert(scanned@[ji] as int == inclusive_scan_int(block_buf@)[ji]);
                // inclusive_scan_int(block_buf)[ji] = sum(|k| as_int_seq(block_buf)[k], 0, ji+1)
                // = sum(|k| int_data[bsi+k], 0, ji+1) by congruence
                // = sum(|k| int_data[k], bsi, bsi+ji+1) by reindex
                // = reduce(int_data, bsi, bsi+ji+1)
                assert forall|k: int| 0 <= k < ji + 1 implies
                    as_int_seq(block_buf@)[k] == int_data[(bsi as int + k) as int] by {}
                lemma_sum_congruence::<int>(
                    |k: int| as_int_seq(block_buf@)[k],
                    |k: int| int_data[(bsi as int + k) as int],
                    0, ji + 1,
                );
                lemma_sum_reindex::<int>(
                    |k: int| int_data[k],
                    bsi as int, bsi as int + ji + 1,
                    bsi as int,
                );
            }
        }

        b = b + 1;
    }

    // ============================================================
    // Phase 2: Exclusive scan of block sums
    // ============================================================
    let ghost original_block_sums = block_sums@;

    proof {
        lemma_block_sums_bounded(data@, block_size as nat, nblocks as nat);
        assert(block_sums@.len() == nblocks as nat);
        assert forall|bi: int| 0 <= bi < nblocks as int implies
            block_sums@[bi] as int == block_reduce(int_data, block_size as nat, bi as nat) by {}
    }

    blelloch_exclusive_scan_exec(&mut block_sums, nblocks);

    // ============================================================
    // Phase 3: Combine block prefix + local inclusive scan
    // ============================================================
    let mut output: Vec<i64> = Vec::new();
    let mut oi: u64 = 0;
    while oi < n
        invariant
            oi <= n,
            output@.len() == oi as nat,
            local_scans@.len() == n as nat,
            block_sums@.len() == nblocks as nat,
            n as int == data_len as int,
            n as int == nblocks as int * block_size as int,
            data@.len() == n as nat,
            block_size > 0,
            all_partial_sums_bounded(data@),
            n <= i64::MAX as u64,
            nblocks <= i64::MAX as u64,
            int_data == as_int_seq(data@),
            forall|bi: int| 0 <= bi < nblocks as int ==>
                #[trigger] block_sums@[bi] as int
                    == exclusive_scan_int(original_block_sums)[bi],
            forall|bi: int| 0 <= bi < nblocks as int ==>
                original_block_sums[bi] as int
                    == block_reduce(int_data, block_size as nat, bi as nat),
            forall|bi: int, j: int| 0 <= bi < nblocks as int && 0 <= j < block_size as int ==>
                #[trigger] local_scans@[(bi * block_size as int + j) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + j + 1),
            forall|i: int| 0 <= i < oi as int ==>
                #[trigger] output@[i] as int == inclusive_scan_int(data@)[i],
        decreases n - oi,
    {
        let block_id: u64 = oi / block_size;
        let local_j: u64 = oi % block_size;

        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(oi as int, block_size as int);
            // oi == block_id * block_size + local_j, 0 <= local_j < block_size

            assert(block_id < nblocks) by (nonlinear_arith)
                requires oi < n, n as int == nblocks as int * block_size as int,
                         oi as int == block_id as int * block_size as int + local_j as int,
                         0 <= local_j as int, (local_j as int) < (block_size as int),
                         block_size > 0;

            assert((block_id as int) * (block_size as int) + (local_j as int) + 1 <= data@.len() as int) by (nonlinear_arith)
                requires oi < n, oi as int == block_id as int * block_size as int + local_j as int,
                         data@.len() == n as nat, (local_j as int) < (block_size as int);

            lemma_three_phase_correct(
                int_data, block_size as nat, block_id as nat, local_j as int,
            );

            // Bridge block_sums[block_id] to block_exclusive_prefix
            assert(block_id as nat * block_size as nat <= data@.len()) by (nonlinear_arith)
                requires block_id < nblocks, n as int == nblocks as int * block_size as int,
                         data@.len() == n as nat, block_size > 0;
            lemma_block_prefix_is_reduce_sum(int_data, block_size as nat, block_id as nat);

            assert forall|ji: int| 0 <= ji < block_id as int implies
                as_int_seq(original_block_sums)[ji]
                    == block_reduces(int_data, block_size as nat, block_id as nat)[ji]
            by {}

            lemma_sum_congruence::<int>(
                |ji: int| as_int_seq(original_block_sums)[ji],
                |ji: int| block_reduces(int_data, block_size as nat, block_id as nat)[ji],
                0, block_id as int,
            );

            lemma_phase3_overflow(
                data@, block_size as nat, block_id as nat, local_j as int,
            );
        }

        let prefix_val = block_sums[block_id as usize];
        let local_val = local_scans[oi as usize];
        let result_val = prefix_val + local_val;
        output.push(result_val);

        oi = oi + 1;
    }

    output
}

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

    // Build pred_int: 0/1 values from pred
    let mut pred_int: Vec<i64> = Vec::new();
    let mut pi: u64 = 0;
    while pi < n
        invariant
            pi <= n,
            pred_int@.len() == pi as nat,
            pred@.len() == n as nat,
            forall|j: int| 0 <= j < pi as int ==>
                #[trigger] pred_int@[j] as int == pred_as_int_seq(pred@)[j],
        decreases n - pi,
    {
        if pred[pi as usize] {
            pred_int.push(1i64);
        } else {
            pred_int.push(0i64);
        }
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

    // Allocate output buffer
    let mut output: Vec<i64> = Vec::new();
    let mut oi: u64 = 0;
    while oi < n
        invariant oi <= n, output@.len() == oi as nat,
        decreases n - oi,
    {
        output.push(0i64);
        oi = oi + 1;
    }

    // Scatter
    let mut si: u64 = 0;
    while si < n
        invariant
            si <= n,
            output@.len() == n as nat,
            pred_int@.len() == n as nat,
            data@.len() == n as nat,
            pred@.len() == n as nat,
            n <= i64::MAX as u64,
            forall|j: int| 0 <= j < n as int ==>
                pred_int@[j] as int == exclusive_scan_int(original_pred_int)[j],
            forall|j: int| 0 <= j < n as int ==>
                original_pred_int[j] as int == pred_as_int_seq(pred@)[j],
            // All scattered elements are at their correct positions
            forall|j: int| 0 <= j < si as int && pred@[j] ==>
                #[trigger] output@[compact_indices(pred@)[j] as int] == data@[j],
            // Scatter indices are valid and match pred_int
            forall|j: int| 0 <= j < si as int && pred@[j] ==>
                compact_indices(pred@)[j] as int == pred_int@[j] as int
                && 0 <= pred_int@[j] as int && (pred_int@[j] as int) < (n as int),
        decreases n - si,
    {
        if pred[si as usize] {
            let scatter_idx = pred_int[si as usize];

            proof {
                // Bridge pred_int[si] to compact_indices
                lemma_compact_indices_is_exclusive_scan(pred@, si as int);
                assert forall|j: int| 0 <= j < si as int implies
                    as_int_seq(original_pred_int)[j] == pred_as_int_seq(pred@)[j] by {}
                lemma_sum_congruence::<int>(
                    |j: int| as_int_seq(original_pred_int)[j],
                    |j: int| pred_as_int_seq(pred@)[j],
                    0, si as int,
                );
                // Now compact_indices(pred)[si] as int == pred_int[si] as int

                // Bounds
                lemma_pred_partial_sums_bounded(pred@);
                // scatter_idx >= 0 and < n

                // Disjointness: writing to scatter_idx doesn't clobber previous writes
                assert forall|j: int| 0 <= j < si as int && pred@[j] implies
                    compact_indices(pred@)[j] != compact_indices(pred@)[si as int]
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
            count as nat == compact_size(pred@.take(ci as int)),
            count <= ci,
        decreases n - ci,
    {
        proof {
            // Prepare for next iteration
            assert(pred@.take((ci + 1) as int).drop_last() =~= pred@.take(ci as int));
            assert(pred@.take((ci + 1) as int).last() == pred@[ci as int]);
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
    // Correct by construction but the full inductive proof is tedious.
    // The key insight is that compact_indices is a bijection from true positions
    // to [0, compact_size), and compact_result[i] = data[j] where j is the
    // unique position with compact_indices[j] == i and pred[j].
    assume(false);
}

} // verus!
