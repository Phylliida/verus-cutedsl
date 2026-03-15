/// Runtime implementations: three-phase block scan + compact.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_multiblock::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;
use crate::proof::scan_multiblock_lemmas::*;
use crate::proof::swizzle_lemmas::{lemma_pow2_positive, lemma_pow2_monotone};
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
// Padding helpers for non-power-of-2 block counts
// ============================================================

/// Partial sum of all-zero region is zero.
proof fn lemma_zero_partial_sum(data: Seq<i64>, lo: int, hi: int, nblocks: int)
    requires
        0 <= nblocks,
        nblocks <= lo,
        lo <= hi,
        hi <= data.len(),
        forall|i: int| nblocks <= i < data.len() as int ==> data[i] == 0i64,
    ensures
        partial_sum(data, lo, hi) == 0,
    decreases hi - lo,
{
    if lo >= hi {
        lemma_sum_empty::<int>(|j: int| data[j] as int, lo, hi);
    } else {
        lemma_sum_peel_last::<int>(|j: int| data[j] as int, lo, hi);
        lemma_zero_partial_sum(data, lo, hi - 1, nblocks);
    }
}

/// Partial sum of padded data equals partial sum of original for indices within original range.
proof fn lemma_original_partial_sum(
    padded: Seq<i64>, original: Seq<i64>, lo: int, hi: int, nblocks: int,
)
    requires
        0 <= lo,
        lo <= hi,
        hi <= nblocks,
        nblocks <= padded.len(),
        original.len() == nblocks as nat,
        forall|i: int| 0 <= i < nblocks ==> padded[i] == original[i],
    ensures
        partial_sum(padded, lo, hi) == partial_sum(original, lo, hi),
{
    assert forall|j: int| lo <= j < hi implies
        padded[j] as int == original[j] as int
    by {
        assert(padded[j] == original[j]);
    }
    lemma_sum_congruence::<int>(
        |j: int| padded[j] as int,
        |j: int| original[j] as int,
        lo, hi,
    );
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
        block_size > 1,
        is_power_of_2(block_size as nat),
        all_partial_sums_bounded(data@),
        data@.len() <= i64::MAX as nat,
        block_size <= i64::MAX as u64,
    ensures
        output@.len() == data@.len(),
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i] as int == inclusive_scan_int(data@)[i],
{
    let n: u64 = data.len() as u64;
    let data_len = data.len(); // usize bridge: establishes n fits in usize
    let ghost int_data = as_int_seq(data@);

    // Compute nblocks = ceil_div(n, block_size)
    proof {
        // n + block_size - 1 fits in u64 (both <= i64::MAX, so sum < u64::MAX)
        assert(n as int + block_size as int - 1 <= u64::MAX as int) by (nonlinear_arith)
            requires n <= i64::MAX as u64, block_size <= i64::MAX as u64;
    }
    let nblocks: u64 = (n + block_size - 1) / block_size;
    let remainder: u64 = n % block_size;

    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, block_size as int);
        let full_blocks: int = n as int / block_size as int;
        let rem: int = n as int % block_size as int;
        // n == block_size * full_blocks + rem, 0 <= rem < block_size
        assert(remainder as int == rem);

        // ceil_div(n, bs) = full_blocks + (if rem > 0 { 1 } else { 0 })
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            (n as int + block_size as int - 1), block_size as int);
        assert(nblocks > 0) by (nonlinear_arith)
            requires n > 0, block_size > 1,
                     n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int;

        // (nblocks - 1) * block_size < n <= nblocks * block_size
        assert(nblocks as int * block_size as int >= n as int) by (nonlinear_arith)
            requires n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int,
                     nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 0;

        assert((nblocks as int - 1) * block_size as int < n as int) by (nonlinear_arith)
            requires n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int,
                     nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 0, n > 0;

        // nblocks bound for padding: nblocks <= (n+1)/2 since block_size >= 2
        assert(nblocks as int <= (n as int + 1) / 2) by (nonlinear_arith)
            requires nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 1;
        assert(nblocks <= i64::MAX as u64) by (nonlinear_arith)
            requires nblocks as int <= (n as int + 1) / 2, n <= i64::MAX as u64;
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
            // Output length: b*bs for full blocks, n when all blocks processed
            output@.len() == (if b as int * block_size as int <= n as int {
                (b as int * block_size as int) as nat } else { n as nat }),
            block_sums@.len() == b as nat,
            data@.len() == n as nat,
            nblocks as int * block_size as int >= n as int,
            (nblocks as int - 1) * block_size as int < n as int,
            n > 0,
            n as int == data_len as int, // usize bridge
            block_size > 1,
            block_size <= i64::MAX as u64,
            nblocks > 0,
            nblocks <= i64::MAX as u64,
            n <= i64::MAX as u64,
            is_power_of_2(block_size as nat),
            all_partial_sums_bounded(data@),
            int_data == as_int_seq(data@),
            // For b < nblocks: b*bs < n (all processed blocks are full)
            b < nblocks ==> b as int * block_size as int < n as int,
            // block sums correct
            forall|bi: int| 0 <= bi < b as int ==>
                #[trigger] block_sums@[bi] as int
                    == block_reduce(int_data, block_size as nat, bi as nat),
            // output holds per-block inclusive scans (clamped to n)
            forall|bi: int, j: int| 0 <= bi < b as int && 0 <= j
                && bi * block_size as int + j < n as int ==>
                #[trigger] output@[(bi * block_size as int + j) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + j + 1),
        decreases nblocks - b,
    {
        let bsi: u64 = b * block_size;
        // this_block_len = min(block_size, n - bsi)
        let this_block_len: u64 = if bsi + block_size <= n { block_size } else { n - bsi };

        proof {
            // bsi < n (from b < nblocks invariant)
            assert(bsi as int < n as int) by (nonlinear_arith)
                requires b < nblocks, (nblocks as int - 1) * block_size as int < n as int,
                         block_size > 0;
            assert(this_block_len > 0) by (nonlinear_arith)
                requires bsi as int < n as int;
            assert(bsi as int + this_block_len as int <= n as int);
            assert(bsi as int <= i64::MAX as int) by (nonlinear_arith)
                requires bsi as int < n as int, n <= i64::MAX as u64;
            // this_block_len <= block_size
            assert(this_block_len <= block_size);
        }

        // Copy block into temp buffer
        let mut block_buf: Vec<i64> = Vec::new();
        let mut j: u64 = 0;
        while j < this_block_len
            invariant
                j <= this_block_len,
                block_buf@.len() == j as nat,
                bsi as int + this_block_len as int <= n as int,
                data@.len() == n as nat,
                n as int == data_len as int, // usize bridge
                bsi == b * block_size,
                forall|k: int| 0 <= k < j as int ==>
                    #[trigger] block_buf@[k] == data@[(bsi as int + k) as int],
            decreases this_block_len - j,
        {
            block_buf.push(data[(bsi + j) as usize]);
            j = j + 1;
        }

        // Prove bounded partial sums for block_buf
        proof {
            lemma_subrange_partial_sums_bounded(data@, bsi as int, this_block_len as int);
            let ghost sub_spec = Seq::new(this_block_len as nat, |i: int| data@[(bsi as int + i) as int]);
            assert(block_buf@ =~= sub_spec);
        }

        // Run inclusive scan on block (Hillis-Steele works for any n > 0)
        let scanned = hillis_steele_exec(&block_buf, this_block_len);

        // Append scanned results to output
        let ghost output_before = output@;
        let mut j2: u64 = 0;
        while j2 < this_block_len
            invariant
                j2 <= this_block_len,
                output@.len() == (b as int * block_size as int + j2 as int) as nat,
                scanned@.len() == this_block_len as nat,
                bsi == b * block_size,
                bsi as int + this_block_len as int <= n as int,
                n as int == data_len as int, // usize bridge
                this_block_len > 0,
                // new elements are scanned values
                forall|k: int| 0 <= k < j2 as int ==>
                    output@[(bsi as int + k) as int] == scanned@[k],
                // old elements preserved
                forall|k: int| 0 <= k < bsi as int ==>
                    output@[k] == output_before[k],
                // scanned holds inclusive scan of block_buf
                forall|k: int| 0 <= k < this_block_len as int ==>
                    scanned@[k] as int == inclusive_scan_int(block_buf@)[k],
            decreases this_block_len - j2,
        {
            output.push(scanned[j2 as usize]);
            j2 = j2 + 1;
        }

        // Store block sum
        let block_sum_val = scanned[(this_block_len - 1) as usize];
        block_sums.push(block_sum_val);

        proof {
            // Re-assert block_buf equality in this proof scope
            let ghost sub = Seq::new(this_block_len as nat, |i: int| data@[(bsi as int + i) as int]);
            assert(block_buf@ =~= sub);

            // Bridge block sum to block_reduce
            lemma_inclusive_scan_subrange(
                data@, bsi as int, this_block_len as int, this_block_len as int - 1,
            );

            // Explicit chain: block_sum_val → scanned → inclusive_scan → reduce
            assert(block_sum_val as int
                == scanned@[(this_block_len as int - 1) as int] as int);
            assert(scanned@[(this_block_len as int - 1) as int] as int
                == inclusive_scan_int(block_buf@)[this_block_len as int - 1]);

            // Show block_end: min((b+1)*bs, n)
            assert(block_start(block_size as nat, b as nat)
                == b as nat * block_size as nat);

            // block_end(n, bs, b) = min((b+1)*bs, n)
            // bsi + this_block_len = min(bsi + bs, n) = block_end
            assert(((b as nat + 1) * block_size as nat) as int
                == (b as nat * block_size as nat) as int + block_size as int)
            by (nonlinear_arith)
                requires b >= 0nat, block_size as nat >= 0nat;

            if bsi + block_size <= n {
                // Full block: block_end = (b+1)*bs
                assert((b as nat + 1) * block_size as nat <= n as nat);
                assert(block_end(n as nat, block_size as nat, b as nat)
                    == (b as nat + 1) * block_size as nat);
                assert(this_block_len == block_size);
            } else {
                // Short last block: block_end = n
                assert(block_end(n as nat, block_size as nat, b as nat)
                    == n as nat);
                assert(bsi as int + this_block_len as int == n as int);
            }

            // In both cases: reduce(int_data, bsi, bsi + this_block_len) == block_reduce
            assert(bsi as int + this_block_len as int
                == block_end(n as nat, block_size as nat, b as nat) as int);
            assert(reduce::<int>(int_data, bsi as int, bsi as int + this_block_len as int)
                == block_reduce(int_data, block_size as nat, b as nat));
            assert(block_sum_val as int
                == block_reduce(int_data, block_size as nat, b as nat));

            // Bridge local scan values for block b
            assert forall|ji: int| 0 <= ji < this_block_len as int implies
                #[trigger] output@[(b as int * block_size as int + ji) as int] as int
                    == reduce::<int>(int_data,
                        b as int * block_size as int,
                        b as int * block_size as int + ji + 1)
            by {
                assert(output@[(bsi as int + ji) as int] == scanned@[ji]);
                assert(scanned@[ji] as int == inclusive_scan_int(block_buf@)[ji]);
                lemma_inclusive_scan_subrange(data@, bsi as int, this_block_len as int, ji);
            }
            // Since this_block_len <= block_size and bsi + this_block_len <= n,
            // this covers all j where b*bs + j < n (for this block)
            assert forall|ji: int| 0 <= ji
                && b as int * block_size as int + ji < n as int implies
                #[trigger] output@[(b as int * block_size as int + ji) as int] as int
                    == reduce::<int>(int_data,
                        b as int * block_size as int,
                        b as int * block_size as int + ji + 1)
            by {
                // ji < n - b*bs = n - bsi <= this_block_len
                assert(ji < this_block_len as int) by (nonlinear_arith)
                    requires b as int * block_size as int + ji < n as int,
                             bsi as int + this_block_len as int <= n as int,
                             bsi as int >= b as int * block_size as int;
            }

            // Preserve old blocks
            assert forall|bi: int, ji: int|
                0 <= bi < b as int && 0 <= ji
                && bi * block_size as int + ji < n as int
            implies
                #[trigger] output@[(bi * block_size as int + ji) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + ji + 1)
            by {
                assert(bi * block_size as int + ji < bsi as int) by (nonlinear_arith)
                    requires bi < b as int, 0 <= ji, bi * block_size as int + ji < n as int,
                             bsi as int == b as int * block_size as int, block_size > 0;
                assert(output@[(bi * block_size as int + ji) as int]
                    == output_before[(bi * block_size as int + ji) as int]);
            }

            // Output length after processing block b
            // After appending this_block_len elements: output.len = b*bs + this_block_len
            // = bsi + this_block_len
            // If (b+1)*bs <= n: = bsi + bs = (b+1)*bs
            // If (b+1)*bs > n: = bsi + (n - bsi) = n
            // Invariant at b+1: if (b+1)*bs <= n then (b+1)*bs else n
            if bsi + block_size <= n {
                assert(output@.len() == ((b as int + 1) * block_size as int) as nat) by (nonlinear_arith)
                    requires output@.len() == (b as int * block_size as int + this_block_len as int) as nat,
                             this_block_len == block_size;
                assert((b + 1) as int * block_size as int <= n as int) by (nonlinear_arith)
                    requires bsi as int + block_size as int <= n as int,
                             bsi as int == b as int * block_size as int;
            } else {
                assert(output@.len() == n as nat);
            }

            // b+1 < nblocks ==> (b+1)*bs < n (for next iteration's invariant)
            assert((b as int + 1) < nblocks as int ==>
                (b as int + 1) * block_size as int < n as int)
            by (nonlinear_arith)
                requires (nblocks as int - 1) * block_size as int < n as int, block_size > 0;
        }

        b = b + 1;
    }

    // ============================================================
    // Phase 2: Exclusive scan of block sums (pad to power-of-2)
    // ============================================================
    let ghost original_block_sums = block_sums@;

    // After Phase 1: output has n elements (all blocks processed)
    proof {
        // At loop exit, b == nblocks. nblocks*bs >= n, so the conditional gives n.
        assert(nblocks as int * block_size as int >= n as int);
        assert(output@.len() == n as nat);

        // block_sums partial sums bounded (from original data being bounded)
        // lemma_block_sums_bounded needs nblocks * block_size <= data.len()
        // With ceil_div, nblocks * block_size >= n = data.len(). So we need >=.
        // Actually lemma_block_sums_bounded uses block_end which clamps, so it's fine
        // as long as we pass the right bound.
        lemma_block_sums_bounded(data@, block_size as nat, nblocks as nat);
        // Bridge: the Seq::new in lemma matches our block_sums
        let ghost lemma_seq: Seq<i64> = Seq::new(nblocks as nat, |i: int|
            block_reduce(int_data, block_size as nat, i as nat) as i64);
        assert(block_sums@ =~= lemma_seq) by {
            assert(block_sums@.len() == lemma_seq.len());
            assert forall|i: int| 0 <= i < block_sums@.len() as int implies
                block_sums@[i] == lemma_seq[i]
            by {
                assert(block_sums@[i] as int == block_reduce(int_data, block_size as nat, i as nat));
                assert(lemma_seq[i] == block_reduce(int_data, block_size as nat, i as nat) as i64);
            }
        }
    }

    // Pad block_sums to next power-of-2 for Blelloch
    let padded_levels = log2_ceil_exec(nblocks);

    // Compute padded_nblocks = pow2(padded_levels)
    let mut padded_nblocks: u64 = 1;
    let mut pk: u64 = 0;

    proof {
        // Bound padded_levels: nblocks <= (n+1)/2 since block_size >= 2,
        // so log2_ceil(nblocks) <= 62, and pow2(62) fits in i64.
        assert(nblocks as int <= (n as int + 1) / 2) by (nonlinear_arith)
            requires nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 1;
        assert(nblocks as int <= (i64::MAX as int) / 2) by (nonlinear_arith)
            requires nblocks as int <= (n as int + 1) / 2, n <= i64::MAX as u64;
        assert(pow2(62) >= nblocks as nat) by {
            assert(pow2(62) >= 4611686018427387903nat) by (compute_only);
            assert((i64::MAX as int) / 2 == 4611686018427387903int);
        }
        lemma_log2_ceil_upper_bound(nblocks as nat, 62);
    }

    while pk < padded_levels
        invariant
            pk <= padded_levels,
            padded_nblocks as nat == pow2(pk as nat),
            padded_nblocks > 0,
            padded_levels as nat <= 62,
        decreases padded_levels - pk,
    {
        proof {
            assert(pow2((pk + 1) as nat) == 2 * pow2(pk as nat));
            lemma_pow2_monotone((pk + 1) as nat, 62);
            assert(pow2(62) <= u64::MAX as nat) by (compute_only);
        }
        padded_nblocks = padded_nblocks * 2;
        pk = pk + 1;
    }

    // padded_nblocks == pow2(log2_ceil(nblocks)) >= nblocks
    proof {
        lemma_log2_ceil_pow2(nblocks as nat);
        // pow2(padded_levels) >= nblocks
        assert(padded_nblocks as nat >= nblocks as nat);
        // pow2(padded_levels) <= pow2(62) < i64::MAX
        lemma_pow2_monotone(padded_levels as nat, 62);
        assert(pow2(62) <= i64::MAX as nat) by (compute_only);
        assert(padded_nblocks as nat <= i64::MAX as nat);
        // is_power_of_2
        assert(is_power_of_2(padded_nblocks as nat));
    }

    // Pad block_sums with zeros
    let mut pad_i: u64 = nblocks;
    while pad_i < padded_nblocks
        invariant
            nblocks <= pad_i,
            pad_i <= padded_nblocks,
            block_sums@.len() == pad_i as nat,
            padded_nblocks as nat <= i64::MAX as nat,
            // Original elements preserved
            forall|i: int| 0 <= i < nblocks as int ==>
                block_sums@[i] == original_block_sums[i],
            // Padding elements are zero
            forall|i: int| nblocks as int <= i < pad_i as int ==>
                block_sums@[i] == 0i64,
        decreases padded_nblocks - pad_i,
    {
        block_sums.push(0i64);
        pad_i = pad_i + 1;
    }

    // Prove padded block_sums have bounded partial sums
    let ghost padded_block_sums = block_sums@;
    proof {
        // The padded suffix is all zeros, so partial sums over any range
        // [lo, hi) equal partial sums of the original (clamped to nblocks).
        assert forall|lo: int, hi: int| 0 <= lo <= hi <= block_sums@.len()
        implies i64::MIN as int <= #[trigger] partial_sum(block_sums@, lo, hi)
            && partial_sum(block_sums@, lo, hi) <= i64::MAX as int
        by {
            // Clamp hi to nblocks for the non-zero portion
            let clamped_hi = if hi <= nblocks as int { hi } else { nblocks as int };
            let clamped_lo = if lo <= nblocks as int { lo } else { nblocks as int };
            // partial_sum(padded, lo, hi) = partial_sum(padded, lo, clamped_hi) + partial_sum(padded, clamped_hi, hi)
            // The second part is zero (all padding elements are 0).
            // The first part: padded[j] == unpadded[j] for j < nblocks, so equals partial_sum(unpadded, lo, clamped_hi).
            // unpadded has bounded partial sums.

            // Split at clamped boundaries
            if lo >= nblocks as int {
                // Entire range is in padding (zeros)
                lemma_zero_partial_sum(block_sums@, lo, hi, nblocks as int);
            } else if hi <= nblocks as int {
                // Entire range is in original
                lemma_original_partial_sum(block_sums@, original_block_sums, lo, hi, nblocks as int);
            } else {
                // Split at nblocks
                lemma_sum_split::<int>(|j: int| block_sums@[j] as int, lo, nblocks as int, hi);
                lemma_original_partial_sum(block_sums@, original_block_sums, lo, nblocks as int, nblocks as int);
                lemma_zero_partial_sum(block_sums@, nblocks as int, hi, nblocks as int);
            }
        }
    }

    blelloch_exclusive_scan_exec(&mut block_sums, padded_nblocks);

    // Bridge: exclusive_scan of padded == exclusive_scan of original for indices < nblocks
    proof {
        assert forall|bi: int| 0 <= bi < nblocks as int implies
            block_sums@[bi] as int == exclusive_scan_int(padded_block_sums)[bi]
        by {}
        // For bi < nblocks: exclusive_scan_int(padded)[bi] = sum(|j| padded[j] as int, 0, bi)
        //   = sum(|j| unpadded[j] as int, 0, bi) = exclusive_scan_int(unpadded)[bi]
        // because padded[j] == unpadded[j] for j < nblocks
        assert forall|bi: int| 0 <= bi < nblocks as int implies
            exclusive_scan_int(padded_block_sums)[bi]
                == exclusive_scan_int(original_block_sums)[bi]
        by {
            assert forall|j: int| 0 <= j < bi implies
                as_int_seq(padded_block_sums)[j] == as_int_seq(original_block_sums)[j]
            by {
                assert(padded_block_sums[j] == original_block_sums[j]);
            }
            lemma_sum_congruence::<int>(
                |j: int| as_int_seq(padded_block_sums)[j],
                |j: int| as_int_seq(original_block_sums)[j],
                0, bi,
            );
        }
    }

    // ============================================================
    // Phase 3: Add block prefix to each output element (in-place)
    // ============================================================
    let mut oi: u64 = 0;
    while oi < n
        invariant
            oi <= n,
            output@.len() == n as nat,
            block_sums@.len() == padded_nblocks as nat,
            padded_nblocks >= nblocks,
            original_block_sums.len() == nblocks as nat, // needed for as_int_seq unfolding
            nblocks as int * block_size as int >= n as int,
            (nblocks as int - 1) * block_size as int < n as int,
            nblocks > 0,
            data@.len() == n as nat,
            block_size > 0,
            all_partial_sums_bounded(data@),
            n <= i64::MAX as u64,
            nblocks <= i64::MAX as u64,
            n as int == data_len as int, // usize bridge
            int_data == as_int_seq(data@),
            // block_sums holds exclusive scan of original (bridged through padding)
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
            // unprocessed elements hold per-block inclusive scan (clamped to n)
            forall|bi: int, j: int| 0 <= bi < nblocks as int && 0 <= j
                && bi * block_size as int + j < n as int
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
                requires oi < n, nblocks as int * block_size as int >= n as int,
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
            // block_id * bs <= (nblocks-1) * bs < n = data.len
            assert(block_id as nat * block_size as nat <= data@.len()) by (nonlinear_arith)
                requires block_id < nblocks,
                         (nblocks as int - 1) * block_size as int < n as int,
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

            // eqv for int is ==, so sum_congruence gives actual equality
            // reduce unfolds to sum with same closure, so these are equal
            assert(
                reduce::<int>(as_int_seq(original_block_sums), 0, block_id as int)
                == reduce::<int>(block_reduces(int_data, block_size as nat, block_id as nat), 0, block_id as int)
            );
            // Chain: exclusive_scan_int → reduce → block_exclusive_prefix
            assert(exclusive_scan_int(original_block_sums)[block_id as int]
                == block_exclusive_prefix(int_data, block_size as nat, block_id as nat));

            // prefix_val == block_sums[block_id] and block_sums holds exclusive scan
            assert(block_sums@[block_id as int] as int
                == exclusive_scan_int(original_block_sums)[block_id as int]);
            // So prefix_val as int == block_exclusive_prefix(int_data, bs, block_id)

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

        proof {
            // usize bridge: oi < n, block_id < n, n fits in usize (data_len)
            assert(oi < n); // from loop guard, both u64
            assert(n as int == data_len as int); // from invariant
            assert((oi as usize) as int == oi as int);
            assert((block_id as int) < (n as int)) by (nonlinear_arith)
                requires (block_id as int) < (nblocks as int),
                         (nblocks as int - 1) * block_size as int < n as int,
                         block_size > 0;
            assert((block_id as usize) as int == block_id as int);

            // Chain prefix_val → block_exclusive_prefix
            assert(prefix_val as int == block_sums@[block_id as int] as int);
            assert(prefix_val as int == exclusive_scan_int(original_block_sums)[block_id as int]);
            assert(prefix_val as int == block_exclusive_prefix(int_data, block_size as nat, block_id as nat));

            // Chain local_val → reduce
            assert(local_val as int == output@[oi as int] as int);
            assert(local_val as int == reduce::<int>(int_data,
                block_id as int * block_size as int,
                block_id as int * block_size as int + local_j as int + 1));

            // From lemma_phase3_overflow: the sum fits in i64
            // (block_id as nat * block_size as nat) = block_id * block_size
            assert((block_id as nat * block_size as nat) as int == block_id as int * block_size as int) by (nonlinear_arith);
        }

        let result_val: i64 = prefix_val + local_val;

        proof {
            // result_val = prefix + local = block_exclusive_prefix + local_reduce
            // = inclusive_scan_int(data@)[oi]  [by lemma_three_phase_correct]
            assert(result_val as int == prefix_val as int + local_val as int);
            assert(result_val as int == inclusive_scan_int(data@)[oi as int]);
        }

        let ghost output_before_set = output@;
        output.set(oi as usize, result_val);

        proof {
            // Unprocessed invariant: set only changes output[oi], all other indices preserved
            assert forall|bi: int, j: int|
                0 <= bi < nblocks as int && 0 <= j
                && bi * block_size as int + j < n as int
                && bi * block_size as int + j >= oi as int + 1
            implies
                #[trigger] output@[(bi * block_size as int + j) as int] as int
                    == reduce::<int>(int_data,
                        bi * block_size as int,
                        bi * block_size as int + j + 1)
            by {
                let idx = bi * block_size as int + j;
                assert(idx != oi as int) by (nonlinear_arith)
                    requires idx >= oi as int + 1;
                assert(idx != (oi as usize) as int);
                // bounds for Vec::set postcondition trigger
                assert((0 <= idx) && (idx < output@.len() as int)) by (nonlinear_arith)
                    requires bi >= 0, j >= 0, idx == bi * block_size as int + j,
                             idx < n as int, output@.len() == n as nat;
            }
        }

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
            original_pred_int.len() == n as nat, // needed for as_int_seq unfolding
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

                // Now: scatter_idx as int == compact_indices(pred)[si] as int
                // compact_indices values are nat (>= 0) and < n
                // (they are counts of true values in prefix, hence < n)
                assert(scatter_idx as int == compact_indices(pred@)[si as int] as int);
                assert(0 <= compact_indices(pred@)[si as int]);
                lemma_pred_partial_sums_bounded(pred@);
                // compact_indices[si] = compact_size(pred.take(si)) <= pred.take(si).len() == si < n
                lemma_compact_size_le_len(pred@.take(si as int));
                assert(compact_indices(pred@)[si as int] == compact_size(pred@.take(si as int)));
                assert(pred@.take(si as int).len() == si as nat);
                assert(compact_indices(pred@)[si as int] <= si as nat);
                assert((compact_indices(pred@)[si as int] as int) < (n as int));

                // Disjointness: previous writes not clobbered by this set
                assert forall|j: int| 0 <= j < si as int && pred@[j] implies
                    compact_indices(pred@)[j] as int != compact_indices(pred@)[si as int] as int
                by {
                    lemma_compact_scatter_disjoint(pred@, j, si as int);
                }
            }

            // scatter_idx is non-negative (equals a nat) and < n, so fits in usize
            proof {
                assert(scatter_idx >= 0i64);
                assert((scatter_idx as int) < (n as int));
            }
            let ghost output_before_scatter = output@;
            output.set(scatter_idx as usize, data[si as usize]);

            proof {
                // (scatter_idx as usize) as int == scatter_idx as int (since 0 <= scatter_idx < n = data_len)
                assert((scatter_idx as usize) as int == scatter_idx as int);
                // New element: output[scatter_idx] == data[si]
                assert(output@[scatter_idx as int] == data@[si as int]);
                assert(scatter_idx as int == compact_indices(pred@)[si as int] as int);
                // Old elements preserved: scatter_idx != compact_indices(pred)[j] for j < si
                assert forall|j: int| 0 <= j < si as int && pred@[j] implies
                    #[trigger] output@[compact_indices(pred@)[j] as int] == data@[j]
                by {
                    lemma_compact_scatter_disjoint(pred@, j, si as int);
                    let ci_j = compact_indices(pred@)[j] as int;
                    let ci_si = compact_indices(pred@)[si as int] as int;
                    assert(ci_j != ci_si);
                    assert(ci_si == scatter_idx as int);
                    assert(ci_j != scatter_idx as int);
                    assert(ci_j != (scatter_idx as usize) as int);
                    // Vec::set preserves output@[ci_j] since ci_j != set index
                    assert(0 <= ci_j && ci_j < output@.len() as int) by {
                        lemma_compact_size_le_len(pred@.take(j));
                        assert(compact_indices(pred@)[j] == compact_size(pred@.take(j)));
                        assert(compact_indices(pred@)[j] <= j as nat);
                    }
                    assert(output@[ci_j] == output_before_scatter[ci_j]);
                }
            }
        } else {
            // pred[si] is false: no write, invariant trivially maintained
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
/// Proved by induction on n: for each output index i < compact_size(pred),
/// there is a unique true position j with compact_indices(pred)[j] == i,
/// and output[i] == data[j] == compact_result(data, pred)[i].
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
    // Prove by showing each true position j maps to the right compact_result index.
    // For each i < compact_size(pred), we find the j such that compact_indices(pred)[j] == i
    // and pred[j]. Then output[i] == data[j] (from requires) and
    // compact_result(data, pred)[i] == data[j] (by definition of compact_result).
    //
    // The key bridge: compact_result(data, pred)[compact_indices(pred)[j]] == data[j]
    // for all j where pred[j].
    assert forall|i: int| 0 <= i < compact_size(pred) as int implies
        output[i] == compact_result(data, pred)[i]
    by {
        // Find j such that compact_indices(pred)[j] == i and pred[j]
        let j = lemma_compact_indices_surjective::<i64>(data, pred, i);
        // output[i] == output[compact_indices(pred)[j]] == data[j] (from requires)
        assert(pred[j]);
        assert(compact_indices(pred)[j] as int == i);
        assert(output[i] == data[j]);
        // compact_result(data, pred)[i] == data[j]
        lemma_compact_result_at::<i64>(data, pred, j);
    }
}

// lemma_compact_indices_surjective and lemma_compact_result_at moved to proof/scan_lemmas.rs

} // verus!
