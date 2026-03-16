/// Runtime implementations: three-phase block scan + compact.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_multiblock::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;
use crate::proof::swizzle_lemmas::{lemma_pow2_positive, lemma_pow2_monotone};
use crate::runtime::scan::*;

verus! {

// ============================================================
// Three-phase inclusive scan (delegates to generic)
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
    proof { lemma_bounded_implies_representable(data@); }
    let result = three_phase_inclusive_scan_generic_exec::<i64, int>(data, block_size);
    proof {
        assert forall|i: int| 0 <= i < data@.len() as int implies
            result@[i] as int == inclusive_scan_int(data@)[i]
        by {
            // From generic second ensures: result@[i].view().eqv(partial_sum_generic(data@, 0, i+1))
            // For i64/int: view() = `as int`, eqv = ==
            // So: result@[i] as int == partial_sum_generic(data@, 0, i+1)

            // Bridge partial_sum_generic → partial_sum via induction lemma
            lemma_partial_sums_equal(data@, 0, i + 1);
            // partial_sum(data@, 0, i+1) == partial_sum_generic(data@, 0, i+1)

            // Bridge partial_sum → inclusive_scan_int via closure congruence
            // partial_sum(data@, 0, i+1) = sum(|j| data@[j] as int, 0, i+1)
            // inclusive_scan_int(data@)[i] = sum(|j| as_int_seq(data@)[j], 0, i+1)
            assert forall|j: int| 0 <= j < i + 1 implies
                (data@[j] as int).eqv(as_int_seq(data@)[j])
            by {
                int::axiom_eqv_reflexive(data@[j] as int);
            }
            lemma_sum_congruence::<int>(
                |j: int| data@[j] as int,
                |j: int| as_int_seq(data@)[j],
                0, i + 1,
            );
        }
    }
    result
}

// ============================================================
// Generic three-phase inclusive scan
// ============================================================

/// Collapse: sum of block sums over [lo, hi) equals sum of view_f
/// over the contiguous range [block_start(lo), block_end(hi-1)].
proof fn lemma_block_sums_collapse<R: Ring>(
    block_sums_views: spec_fn(int) -> R,
    view_f: spec_fn(int) -> R,
    block_size: nat,
    n: nat,
    nblocks: nat,
    lo: int,
    hi: int,
)
    requires
        0 <= lo,
        lo <= hi,
        hi <= nblocks as int,
        block_size > 0,
        n > 0,
        nblocks > 0,
        nblocks as int * block_size as int >= n as int,
        ((nblocks as int - 1) * (block_size as int)) < (n as int),
        forall|bi: int| 0 <= bi < nblocks as int ==>
            (#[trigger] block_sums_views(bi)).eqv(
                sum::<R>(view_f,
                    block_start(block_size, bi as nat) as int,
                    block_end(n, block_size, bi as nat) as int)
            ),
    ensures
        lo == hi ==> sum::<R>(block_sums_views, lo, hi).eqv(R::zero()),
        lo < hi ==> sum::<R>(block_sums_views, lo, hi).eqv(
            sum::<R>(view_f,
                block_start(block_size, lo as nat) as int,
                block_end(n, block_size, (hi - 1) as nat) as int)
        ),
    decreases hi - lo,
{
    if lo == hi {
        lemma_sum_empty::<R>(block_sums_views, lo, hi);
    } else if hi == lo + 1 {
        // Single block: sum(bsv, lo, lo+1) eqv bsv(lo) eqv sum(vf, bs*lo, be(lo))
        lemma_sum_peel_last::<R>(block_sums_views, lo, hi);
        lemma_sum_empty::<R>(block_sums_views, lo, lo);
        // sum(bsv, lo, lo+1) eqv sum(bsv, lo, lo).add(bsv(lo))
        // sum(bsv, lo, lo) eqv R::zero()
        R::axiom_eqv_reflexive(block_sums_views(lo));
        use verus_algebra::lemmas::additive_group_lemmas::{lemma_add_congruence, lemma_add_zero_left};
        lemma_add_congruence::<R>(
            sum::<R>(block_sums_views, lo, lo), R::zero(),
            block_sums_views(lo), block_sums_views(lo),
        );
        // sum(bsv, lo, lo).add(bsv(lo)) eqv R::zero().add(bsv(lo))
        lemma_add_zero_left::<R>(block_sums_views(lo));
        // R::zero().add(bsv(lo)) eqv bsv(lo)
        R::axiom_eqv_transitive(
            sum::<R>(block_sums_views, lo, hi),
            sum::<R>(block_sums_views, lo, lo).add(block_sums_views(lo)),
            R::zero().add(block_sums_views(lo)),
        );
        R::axiom_eqv_transitive(
            sum::<R>(block_sums_views, lo, hi),
            R::zero().add(block_sums_views(lo)),
            block_sums_views(lo),
        );
        R::axiom_eqv_transitive(
            sum::<R>(block_sums_views, lo, hi),
            block_sums_views(lo),
            sum::<R>(view_f,
                block_start(block_size, lo as nat) as int,
                block_end(n, block_size, lo as nat) as int),
        );
    } else {
        // hi >= lo + 2: peel last, use IH, then sum_split
        let bs = block_size as int;
        let hi_m1 = hi - 1;
        let hi_m2 = hi - 2;

        lemma_sum_peel_last::<R>(block_sums_views, lo, hi);

        // IH: sum(bsv, lo, hi-1) eqv sum(vf, bs*lo, be(hi-2))
        lemma_block_sums_collapse::<R>(
            block_sums_views, view_f, block_size, n, nblocks, lo, hi - 1,
        );

        // Unfold spec functions to int for nonlinear_arith
        let bs_lo = block_start(block_size, lo as nat) as int;
        let bs_hi_m1 = block_start(block_size, hi_m1 as nat) as int;
        let be_hi_m2 = block_end(n, block_size, hi_m2 as nat) as int;
        let be_hi_m1 = block_end(n, block_size, hi_m1 as nat) as int;

        // block_start unfolds: lo_nat * bs and (hi-1)_nat * bs
        assert(bs_lo == lo * bs) by {
            assert(block_start(block_size, lo as nat) == lo as nat * block_size);
        };
        assert(bs_hi_m1 == hi_m1 * bs) by {
            assert(block_start(block_size, hi_m1 as nat) == hi_m1 as nat * block_size);
        };

        // block_end(n, bs, hi-2): raw = ((hi-2)+1)*bs = (hi-1)*bs
        // (hi-1)*bs <= (nblocks-1)*bs < n, so raw <= n, so block_end = raw = (hi-1)*bs
        assert(hi_m1 * bs <= (nblocks as int - 1) * bs) by (nonlinear_arith)
            requires hi_m1 <= nblocks as int - 1, bs > 0;
        assert(hi_m1 * bs < n as int) by (nonlinear_arith)
            requires hi_m1 * bs <= (nblocks as int - 1) * bs,
                     ((nblocks as int - 1) * bs) < (n as int);
        assert(be_hi_m2 == bs_hi_m1) by {
            // block_end(n, bs, hi-2) = let raw = ((hi-2)+1)*bs; if raw <= n { raw } else { n }
            // ((hi-2)+1) = (hi-1), raw = (hi-1)*bs < n, so block_end = raw = (hi-1)*bs
            assert(((hi_m2 as nat) + 1) == hi_m1 as nat);
            assert((hi_m1 as nat) * block_size == block_start(block_size, hi_m1 as nat));
            let raw = ((hi_m2 as nat) + 1) * block_size;
            assert(raw == (hi_m1 as nat) * block_size);
            assert((raw as int) < (n as int));
        };

        // bs*lo <= bs*(hi-1) (for sum_split precondition)
        assert(bs_lo <= bs_hi_m1) by (nonlinear_arith)
            requires bs_lo == lo * bs, bs_hi_m1 == hi_m1 * bs, lo <= hi_m1, bs > 0;

        // bs*(hi-1) <= be(hi-1) (for sum_split precondition)
        // block_end(n, bs, hi-1) = min(hi*bs, n). Both branches >= (hi-1)*bs.
        assert(bs_hi_m1 < n as int);
        // Explicit case-split on block_end
        let raw_hi = (hi_m1 as nat + 1) * block_size;
        assert((hi_m1 as nat + 1) == hi as nat);
        if raw_hi <= n {
            assert(be_hi_m1 == raw_hi as int);
            assert(bs_hi_m1 <= raw_hi as int) by (nonlinear_arith)
                requires bs_hi_m1 == hi_m1 * bs, raw_hi as int == (hi_m1 + 1) * bs,
                         bs > 0;
        } else {
            assert(be_hi_m1 == n as int);
            // bs_hi_m1 < n = be_hi_m1
        }
        assert(bs_hi_m1 <= be_hi_m1);

        // Congruence on add
        use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
        lemma_add_congruence::<R>(
            sum::<R>(block_sums_views, lo, hi - 1),
            sum::<R>(view_f, bs_lo, be_hi_m2),
            block_sums_views(hi - 1),
            sum::<R>(view_f, bs_hi_m1, be_hi_m1),
        );

        // Since be(hi-2) == bs*(hi-1), the add_congruence result uses the same
        // intermediate point as sum_split
        lemma_sum_split::<R>(view_f, bs_lo, bs_hi_m1, be_hi_m1);
        R::axiom_eqv_symmetric(
            sum::<R>(view_f, bs_lo, be_hi_m1),
            sum::<R>(view_f, bs_lo, bs_hi_m1).add(sum::<R>(view_f, bs_hi_m1, be_hi_m1)),
        );

        // Chain: sum(bsv, lo, hi) eqv peel eqv add_congruence eqv sum_split
        R::axiom_eqv_transitive(
            sum::<R>(block_sums_views, lo, hi),
            sum::<R>(block_sums_views, lo, hi - 1).add(block_sums_views(hi - 1)),
            sum::<R>(view_f, bs_lo, be_hi_m2).add(sum::<R>(view_f, bs_hi_m1, be_hi_m1)),
        );
        R::axiom_eqv_transitive(
            sum::<R>(block_sums_views, lo, hi),
            sum::<R>(view_f, bs_lo, be_hi_m2).add(sum::<R>(view_f, bs_hi_m1, be_hi_m1)),
            sum::<R>(view_f, bs_lo, be_hi_m1),
        );
    }
}

/// Generic three-phase inclusive scan for arbitrary-length arrays.
/// Uses ExecRing trait for type-generic operation.
/// Phase 1: per-block Hillis-Steele inclusive scan.
/// Phase 2: exclusive scan of block sums.
/// Phase 3: add block prefix to each element.
pub fn three_phase_inclusive_scan_generic_exec<T: ExecRing<R>, R: Ring>(
    data: &Vec<T>, block_size: u64,
) -> (output: Vec<T>)
    requires
        data@.len() > 0,
        block_size > 1,
        all_partial_sums_representable::<T, R>(data@),
        data@.len() <= u64::MAX as nat / 2,
        block_size <= u64::MAX / 2,
    ensures
        output@.len() == data@.len(),
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i].view().eqv(
                inclusive_scan::<R>(Seq::new(data@.len(), |j: int| data@[j].view()))[i]
            ),
        // Second ensures: direct partial_sum_generic form (for delegation wrappers)
        forall|i: int| 0 <= i < data@.len() as int ==>
            output@[i].view().eqv(
                partial_sum_generic::<T, R>(data@, 0, i + 1)
            ),
{
    let n: u64 = data.len() as u64;
    let data_len = data.len(); // usize bridge
    let ghost view_f = |j: int| data@[j].view();
    let ghost view_seq: Seq<R> = Seq::new(data@.len(), view_f);

    // Compute nblocks = ceil_div(n, block_size)
    let nblocks: u64 = (n + block_size - 1) / block_size;

    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, block_size as int);
        let full_blocks: int = n as int / block_size as int;
        let rem: int = n as int % block_size as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            (n as int + block_size as int - 1), block_size as int);
        assert(nblocks > 0) by (nonlinear_arith)
            requires n > 0, block_size > 1,
                     n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int,
                     nblocks as int == (n as int + block_size as int - 1) / block_size as int;
        assert(nblocks as int * block_size as int >= n as int) by (nonlinear_arith)
            requires n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int,
                     nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 0;
        assert(((nblocks as int - 1) * (block_size as int)) < (n as int)) by (nonlinear_arith)
            requires n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int,
                     nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 0, n > 0;
        assert(nblocks as int * block_size as int <= n as int + block_size as int - 1) by (nonlinear_arith)
            requires n as int == block_size as int * full_blocks + rem,
                     0 <= rem, rem < block_size as int,
                     nblocks as int == (n as int + block_size as int - 1) / block_size as int,
                     block_size > 0;
        assert(nblocks as int <= n as int) by (nonlinear_arith)
            requires nblocks as int * block_size as int <= n as int + block_size as int - 1,
                     block_size as int >= 2, nblocks as int >= 1, n as int >= 1;
    }

    // ============================================================
    // Phase 1: Per-block inclusive scan → build output + block_sums
    // ============================================================
    let mut output: Vec<T> = Vec::new();
    let mut block_sums: Vec<T> = Vec::new();
    let mut b: u64 = 0;

    while b < nblocks
        invariant
            b <= nblocks,
            nblocks > 0,
            nblocks as int <= n as int,
            nblocks as int * block_size as int >= n as int,
            ((nblocks as int - 1) * (block_size as int)) < (n as int),
            data@.len() == n as nat,
            n > 0,
            n as int == data_len as int, // usize bridge
            n <= u64::MAX / 2,
            block_size > 1,
            block_size <= u64::MAX / 2,
            block_sums@.len() == b as nat,
            all_partial_sums_representable::<T, R>(data@),
            view_f == (|j: int| data@[j].view()),
            view_seq == Seq::new(data@.len(), view_f),
            // b*bs overflow safety
            b < nblocks ==> (b as int) * (block_size as int) < (n as int),
            // Output length = min(b * block_size, n)
            output@.len() == (if (b as int * block_size as int) <= (n as int) {
                (b as int * block_size as int) as nat } else { n as nat }),
            // Output correctness: within-block inclusive scan
            forall|bi: int, j: int|
                0 <= bi < b as int && 0 <= j < block_size as int
                && (bi * block_size as int + j) < (n as int)
                ==> output@[bi * block_size as int + j].view().eqv(
                    sum::<R>(view_f, bi * block_size as int, #[trigger](bi * block_size as int + j + 1))
                ),
            // Block sums: each is the reduce of its block
            forall|bi: int| 0 <= bi < b as int ==>
                #[trigger] block_sums@[bi].view().eqv(
                    sum::<R>(view_f,
                        block_start(block_size as nat, bi as nat) as int,
                        block_end(n as nat, block_size as nat, bi as nat) as int)
                ),
        decreases nblocks - b,
    {
        // Block start and end indices
        let bsi: u64 = b * block_size;
        let this_block_len: u64 = if bsi + block_size <= n { block_size } else { n - bsi };

        // Extract block elements into sub-vector
        let mut block_data: Vec<T> = Vec::new();
        let mut j: u64 = 0;
        while j < this_block_len
            invariant
                j <= this_block_len,
                block_data@.len() == j as nat,
                this_block_len > 0,
                this_block_len <= block_size,
                bsi == b * block_size,
                bsi + this_block_len <= n,
                data@.len() == n as nat,
                n as int == data_len as int, // usize bridge
                all_partial_sums_representable::<T, R>(data@),
                view_f == (|j: int| data@[j].view()),
                forall|k: int| 0 <= k < j as int ==>
                    block_data@[k].view().eqv(data@[(bsi as int + k) as int].view()),
            decreases this_block_len - j,
        {
            proof {
                assert((bsi as int + j as int) < (n as int));
                assert(((bsi + j) as usize) as int == (bsi + j) as int);
            }
            let clone = data[(bsi + j) as usize].exec_clone();
            block_data.push(clone);
            j = j + 1;
        }

        // all_partial_sums_representable for sub-block
        proof {
            assert forall|lo: int, hi: int| 0 <= lo <= hi <= block_data@.len() implies
                T::is_representable(#[trigger] partial_sum_generic::<T, R>(block_data@, lo, hi))
            by {
                // Use view_f-based congruence to match reindex closure
                assert forall|k: int| lo <= k < hi implies
                    block_data@[k].view().eqv(view_f(k + bsi as int)) by {
                    R::axiom_eqv_reflexive(block_data@[k].view());
                    R::axiom_eqv_transitive(
                        block_data@[k].view(),
                        block_data@[k].view(),
                        data@[(bsi as int + k) as int].view(),
                    );
                }
                lemma_sum_congruence::<R>(
                    |k: int| block_data@[k].view(),
                    |k: int| view_f(k + bsi as int),
                    lo, hi,
                );
                // partial_sum_generic(block_data, lo, hi).eqv(sum(|k| view_f(k+bsi), lo, hi))

                // reindex: partial_sum_generic(data, bsi+lo, bsi+hi).eqv(sum(|i| view_f(i+bsi), lo, hi))
                lemma_sum_reindex::<R>(view_f, bsi as int + lo, bsi as int + hi, bsi as int);

                // Chain: psg(data, bsi+lo, bsi+hi) eqv sum(|k| view_f(k+bsi), ...) eqv.sym psg(block_data, lo, hi)
                R::axiom_eqv_symmetric(
                    partial_sum_generic::<T, R>(block_data@, lo, hi),
                    sum::<R>(|k: int| view_f(k + bsi as int), lo, hi),
                );
                R::axiom_eqv_transitive(
                    partial_sum_generic::<T, R>(data@, bsi as int + lo, bsi as int + hi),
                    sum::<R>(|k: int| view_f(k + bsi as int), lo, hi),
                    partial_sum_generic::<T, R>(block_data@, lo, hi),
                );

                // Trigger: psg(data, bsi+lo, bsi+hi) is representable
                assert(0 <= bsi as int + lo);
                assert(bsi as int + hi <= n as int);
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data@, bsi as int + lo, bsi as int + hi),
                    partial_sum_generic::<T, R>(block_data@, lo, hi),
                );
            }
        }

        // Inclusive scan of block
        let scan = hillis_steele_generic_exec::<T, R>(&block_data, this_block_len);
        let ghost incl_view = Seq::new(block_data@.len(), |k: int| block_data@[k].view());

        // Append scan results to output
        let ghost output_before = output@;
        let scan_len = scan.len(); // usize bridge for scan indexing
        let mut j2: u64 = 0;
        while j2 < this_block_len
            invariant
                j2 <= this_block_len,
                this_block_len > 0,
                this_block_len <= block_size,
                bsi == b * block_size,
                bsi + this_block_len <= n,
                scan@.len() == this_block_len as nat,
                scan_len as int == this_block_len as int, // usize bridge
                block_data@.len() == this_block_len as nat,
                data@.len() == n as nat,
                n as int == data_len as int, // usize bridge
                view_f == (|j: int| data@[j].view()),
                view_seq == Seq::new(data@.len(), view_f),
                incl_view == Seq::new(block_data@.len(), |k: int| block_data@[k].view()),
                output@.len() == (bsi as int + j2 as int) as nat,
                forall|k: int| 0 <= k < block_data@.len() as int ==>
                    block_data@[k].view().eqv(data@[(bsi as int + k) as int].view()),
                forall|k: int| 0 <= k < scan@.len() as int ==>
                    scan@[k].view().eqv(inclusive_scan::<R>(incl_view)[k]),
                // Existing output elements preserved
                forall|bi: int, ji: int|
                    0 <= bi < b as int && 0 <= ji < block_size as int
                    && (bi * block_size as int + ji) < (n as int)
                    ==> output@[bi * block_size as int + ji].view().eqv(
                        sum::<R>(view_f, bi * block_size as int, #[trigger](bi * block_size as int + ji + 1))
                    ),
                // New elements from current block
                forall|k: int| 0 <= k < j2 as int ==>
                    output@[(bsi as int + k) as int].view().eqv(
                        sum::<R>(view_f, bsi as int, #[trigger](bsi as int + k + 1))
                    ),
            decreases this_block_len - j2,
        {
            proof {
                assert((j2 as int) < (scan_len as int));
                assert((j2 as usize) as int == j2 as int);
            }
            let clone = scan[j2 as usize].exec_clone();
            proof {
                // Step 1: clone.view().eqv(scan@[j2].view()) — from exec_clone + usize bridge
                // Step 2: scan@[j2].view().eqv(inclusive_scan(incl_view)[j2]) — from invariant
                // Step 3: Chain to get clone.view().eqv(inclusive_scan(incl_view)[j2])
                R::axiom_eqv_transitive(
                    clone.view(),
                    scan@[j2 as int].view(),
                    inclusive_scan::<R>(incl_view)[j2 as int],
                );

                // Step 4: Bridge inclusive_scan(incl_view)[j2] to sum(view_f, bsi, bsi+j2+1)
                // incl_view[k] eqv view_f(k + bsi)
                assert forall|k: int| 0 <= k < j2 as int + 1 implies
                    incl_view[k].eqv(view_f(k + bsi as int)) by {
                    R::axiom_eqv_reflexive(block_data@[k].view());
                    R::axiom_eqv_transitive(
                        incl_view[k],
                        block_data@[k].view(),
                        data@[(bsi as int + k) as int].view(),
                    );
                    // data@[(bsi+k)] = view_f(k+bsi) since view_f = |j| data@[j].view()
                    // and bsi+k = k+bsi for int arithmetic
                }
                lemma_sum_congruence::<R>(
                    |k: int| incl_view[k],
                    |k: int| view_f(k + bsi as int),
                    0, j2 as int + 1,
                );
                // sum(|k| incl_view[k], 0, j2+1).eqv(sum(|k| view_f(k+bsi), 0, j2+1))

                // reindex: sum(view_f, bsi, bsi+j2+1).eqv(sum(|i| view_f(i+bsi), 0, j2+1))
                lemma_sum_reindex::<R>(view_f, bsi as int, bsi as int + j2 as int + 1, bsi as int);
                R::axiom_eqv_symmetric(
                    sum::<R>(view_f, bsi as int, bsi as int + j2 as int + 1),
                    sum::<R>(|i: int| view_f(i + bsi as int), 0, j2 as int + 1),
                );
                // sum(|i| view_f(i+bsi), 0, j2+1).eqv(sum(view_f, bsi, bsi+j2+1))

                // Chain: incl_scan[j2] eqv sum(|k| view_f(k+bsi), 0, j2+1) eqv sum(view_f, bsi, bsi+j2+1)
                R::axiom_eqv_transitive(
                    inclusive_scan::<R>(incl_view)[j2 as int],
                    sum::<R>(|k: int| view_f(k + bsi as int), 0, j2 as int + 1),
                    sum::<R>(view_f, bsi as int, bsi as int + j2 as int + 1),
                );

                // Step 5: clone.view().eqv(sum(view_f, bsi, bsi+j2+1))
                R::axiom_eqv_transitive(
                    clone.view(),
                    inclusive_scan::<R>(incl_view)[j2 as int],
                    sum::<R>(view_f, bsi as int, bsi as int + j2 as int + 1),
                );
            }
            output.push(clone);
            proof {
                // Old elements preserved after push
                assert forall|bi: int, ji: int|
                    0 <= bi < b as int && 0 <= ji < block_size as int
                    && (bi * block_size as int + ji) < (n as int)
                implies output@[bi * block_size as int + ji].view().eqv(
                    sum::<R>(view_f, bi * block_size as int,
                        #[trigger](bi * block_size as int + ji + 1)))
                by {
                    assert(bi * block_size as int + ji < bsi as int) by (nonlinear_arith)
                        requires bi < b as int, 0 <= ji, ji < block_size as int,
                                 bsi == b * block_size, block_size > 0;
                }
            }
            j2 = j2 + 1;
        }

        // block_sums[b] = last element of scan (= reduce of block)
        proof {
            assert(((this_block_len - 1) as int) < (scan_len as int));
            assert(((this_block_len - 1) as usize) as int == (this_block_len - 1) as int);
        }
        let last_clone = scan[(this_block_len - 1) as usize].exec_clone();
        proof {
            let be = bsi as int + this_block_len as int;
            // last_clone.view().eqv(scan@[tbl-1].view()) — exec_clone + bridge
            // scan@[tbl-1].view().eqv(inclusive_scan(incl_view)[tbl-1]) — from HS ensures
            R::axiom_eqv_transitive(
                last_clone.view(),
                scan@[(this_block_len - 1) as int].view(),
                inclusive_scan::<R>(incl_view)[(this_block_len - 1) as int],
            );
            // Bridge inclusive_scan(incl_view)[tbl-1] to sum(view_f, bsi, be)
            assert forall|k: int| 0 <= k < this_block_len as int implies
                incl_view[k].eqv(view_f(k + bsi as int)) by {
                R::axiom_eqv_reflexive(block_data@[k].view());
                R::axiom_eqv_transitive(
                    incl_view[k], block_data@[k].view(), data@[(bsi as int + k) as int].view(),
                );
            }
            lemma_sum_congruence::<R>(
                |k: int| incl_view[k],
                |k: int| view_f(k + bsi as int),
                0, this_block_len as int,
            );
            lemma_sum_reindex::<R>(view_f, bsi as int, be, bsi as int);
            R::axiom_eqv_symmetric(
                sum::<R>(view_f, bsi as int, be),
                sum::<R>(|i: int| view_f(i + bsi as int), 0, this_block_len as int),
            );
            R::axiom_eqv_transitive(
                inclusive_scan::<R>(incl_view)[(this_block_len - 1) as int],
                sum::<R>(|k: int| view_f(k + bsi as int), 0, this_block_len as int),
                sum::<R>(view_f, bsi as int, be),
            );
            R::axiom_eqv_transitive(
                last_clone.view(),
                inclusive_scan::<R>(incl_view)[(this_block_len - 1) as int],
                sum::<R>(view_f, bsi as int, be),
            );
        }
        block_sums.push(last_clone);

        proof {
            // === Block sum for block b ===
            let be = bsi as int + this_block_len as int;
            // last_clone.view() eqv sum(view_f, bsi, be) — already proved
            // Show bsi == block_start and be == block_end
            assert(bsi as int == block_start(block_size as nat, b as nat) as int);
            assert(((b as nat + 1) * block_size as nat) as int
                == b as int * block_size as int + block_size as int)
            by (nonlinear_arith)
                requires b >= 0, block_size >= 0;
            if bsi + block_size <= n {
                assert(block_end(n as nat, block_size as nat, b as nat)
                    == (b as nat + 1) * block_size as nat);
                assert(this_block_len == block_size);
            } else {
                assert(block_end(n as nat, block_size as nat, b as nat) == n as nat);
                assert(be == n as int);
            }
            assert(be == block_end(n as nat, block_size as nat, b as nat) as int);

            // === Output correctness for block b ===
            // For ji < this_block_len: output@[bsi+ji] eqv sum(view_f, bsi, bsi+ji+1)
            // covers all j < block_size where b*bs + j < n
            assert forall|ji: int| 0 <= ji && ji < block_size as int
                && b as int * block_size as int + ji < n as int implies
                output@[b as int * block_size as int + ji].view().eqv(
                    sum::<R>(view_f, b as int * block_size as int,
                        #[trigger](b as int * block_size as int + ji + 1)))
            by {
                if bsi + block_size <= n {
                    assert(this_block_len == block_size);
                } else {
                    assert(this_block_len == n - bsi);
                }
                assert(ji < this_block_len as int);
            }

            // === Preserve old block outputs ===
            assert forall|bi: int, ji: int|
                0 <= bi < b as int && 0 <= ji && ji < block_size as int
                && bi * block_size as int + ji < n as int
            implies
                output@[bi * block_size as int + ji].view().eqv(
                    sum::<R>(view_f, bi * block_size as int,
                        #[trigger](bi * block_size as int + ji + 1)))
            by {
                // bi < b → bi*bs + ji < b*bs = bsi → index in output_before range
                assert(bi * block_size as int + ji < bsi as int) by (nonlinear_arith)
                    requires bi < b as int, 0 <= ji, ji < block_size as int,
                             bsi == b * block_size, block_size > 0;
            }

            // === Output length for next iteration ===
            if bsi + block_size <= n {
                assert(output@.len() == ((b as int + 1) * block_size as int) as nat) by (nonlinear_arith)
                    requires output@.len() as int == bsi as int + this_block_len as int,
                             bsi as int == b as int * block_size as int,
                             this_block_len == block_size;
                assert((b + 1) as int * block_size as int <= n as int) by (nonlinear_arith)
                    requires bsi as int + block_size as int <= n as int,
                             bsi as int == b as int * block_size as int;
            } else {
                assert(output@.len() == n as nat);
            }

            // === b+1 < nblocks ==> (b+1)*bs < n ===
            if b + 1 < nblocks {
                assert(((b + 1) as int) * (block_size as int) < (n as int)) by (nonlinear_arith)
                    requires (b + 1) as int <= (nblocks as int - 1),
                             ((nblocks as int - 1) * (block_size as int)) < (n as int),
                             block_size > 0;
            }
        }
        b = b + 1;
    }

    // ============================================================
    // Phase 2: Exclusive scan of block_sums
    // ============================================================
    // Prove preconditions for exclusive_scan_generic_exec
    proof {
        // nblocks <= u64::MAX / 2 (since nblocks <= n <= u64::MAX / 2)
        assert(nblocks as int <= n as int);

        // all_partial_sums_representable for block_sums
        let ghost bsv = |i: int| block_sums@[i].view();
        assert forall|lo: int, hi: int| 0 <= lo <= hi <= block_sums@.len() implies
            T::is_representable(#[trigger] partial_sum_generic::<T, R>(block_sums@, lo, hi))
        by {
            if lo == hi {
                // Empty sum = R::zero(), representable from data's all_partial_sums_representable
                lemma_sum_empty::<R>(bsv, lo, hi);
                // sum(bsv, lo, lo) eqv R::zero() = partial_sum_generic(data@, 0, 0)
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data@, 0, 0),
                    partial_sum_generic::<T, R>(block_sums@, lo, hi),
                );
            } else {
                // Non-empty: collapse to contiguous data sum
                lemma_block_sums_collapse::<R>(
                    bsv, view_f, block_size as nat, n as nat, nblocks as nat, lo, hi,
                );
                // sum(bsv, lo, hi) eqv sum(view_f, bs*lo, be(hi-1))
                // = partial_sum_generic(data@, bs*lo, be(hi-1))
                // which is representable (0 <= bs*lo <= be(hi-1) <= n)
                let psg_lo = block_start(block_size as nat, lo as nat) as int;
                let psg_hi = block_end(n as nat, block_size as nat, (hi - 1) as nat) as int;
                // Unfold block_start: lo * bs
                assert(psg_lo == lo as int * block_size as int);
                assert(0 <= psg_lo) by (nonlinear_arith)
                    requires psg_lo == lo as int * block_size as int, lo >= 0, block_size > 0;
                // psg_lo <= psg_hi: lo*bs <= block_end(n, bs, hi-1)
                // Since lo <= hi-1, lo*bs <= (hi-1)*bs < n, and block_end >= min((hi)*bs, n) >= (hi-1)*bs
                assert(((hi - 1) as int * block_size as int) < (n as int)) by (nonlinear_arith)
                    requires hi - 1 <= nblocks as int - 1,
                             ((nblocks as int - 1) * block_size as int) < (n as int),
                             block_size > 0;
                assert(psg_lo <= (hi - 1) as int * block_size as int) by (nonlinear_arith)
                    requires psg_lo == lo as int * block_size as int, lo <= hi - 1, block_size > 0;
                // Case-split on block_end to prove psg_lo <= psg_hi
                let raw_psg = ((hi - 1) as nat + 1) * block_size as nat;
                assert(((hi - 1) as nat + 1) == hi as nat);
                if raw_psg <= n as nat {
                    assert(psg_hi == raw_psg as int);
                    assert(psg_lo <= raw_psg as int) by (nonlinear_arith)
                        requires psg_lo == lo as int * block_size as int,
                                 raw_psg as int == hi as int * block_size as int,
                                 lo <= hi - 1, block_size > 0;
                } else {
                    assert(psg_hi == n as int);
                }
                assert(psg_lo <= psg_hi);
                assert(psg_hi <= n as int);
                // Collapse gives block_sums eqv data, need symmetric for representable_congruence
                R::axiom_eqv_symmetric(
                    partial_sum_generic::<T, R>(block_sums@, lo, hi),
                    partial_sum_generic::<T, R>(data@, psg_lo, psg_hi),
                );
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data@, psg_lo, psg_hi),
                    partial_sum_generic::<T, R>(block_sums@, lo, hi),
                );
            }
        }
    }
    let block_prefixes = exclusive_scan_generic_exec::<T, R>(&block_sums, nblocks);

    // ============================================================
    // Phase 3: Add block prefix to each element
    // ============================================================
    let mut result: Vec<T> = Vec::new();
    let mut b3: u64 = 0;

    while b3 < nblocks
        invariant
            b3 <= nblocks,
            nblocks > 0,
            nblocks as int <= n as int,
            nblocks as int * block_size as int >= n as int,
            ((nblocks as int - 1) * (block_size as int)) < (n as int),
            data@.len() == n as nat,
            n > 0,
            n as int == data_len as int, // usize bridge
            n <= u64::MAX / 2,
            block_size > 1,
            block_size <= u64::MAX / 2,
            view_f == (|j: int| data@[j].view()),
            view_seq == Seq::new(data@.len(), view_f),
            all_partial_sums_representable::<T, R>(data@),
            output@.len() == n as nat,
            block_prefixes@.len() == nblocks as nat,
            block_sums@.len() == nblocks as nat,
            // b3*bs overflow safety
            b3 < nblocks ==> (b3 as int) * (block_size as int) < (n as int),
            result@.len() == (if (b3 as int * block_size as int) <= (n as int) {
                (b3 as int * block_size as int) as nat } else { n as nat }),
            // Output elements are within-block inclusive scans
            forall|bi: int, j: int|
                0 <= bi < nblocks as int && 0 <= j < block_size as int
                && (bi * block_size as int + j) < (n as int)
                ==> output@[bi * block_size as int + j].view().eqv(
                    sum::<R>(view_f, bi * block_size as int, #[trigger](bi * block_size as int + j + 1))
                ),
            // Block sums
            forall|bi: int| 0 <= bi < nblocks as int ==>
                #[trigger] block_sums@[bi].view().eqv(
                    sum::<R>(view_f,
                        block_start(block_size as nat, bi as nat) as int,
                        block_end(n as nat, block_size as nat, bi as nat) as int)
                ),
            // Block prefixes are exclusive scan of block sums
            forall|bi: int| 0 <= bi < nblocks as int ==>
                block_prefixes@[bi].view().eqv(
                    exclusive_scan::<R>(Seq::new(block_sums@.len(),
                        |k: int| block_sums@[k].view()))[bi]
                ),
            // Completed result elements are global inclusive scan
            forall|i: int| 0 <= i < result@.len() as int ==>
                result@[i].view().eqv(
                    inclusive_scan::<R>(view_seq)[i]
                ),
        decreases nblocks - b3,
    {
        let bsi3: u64 = b3 * block_size;
        let this_block_len3: u64 = if bsi3 + block_size <= n { block_size } else { n - bsi3 };

        // Establish block_prefixes@[b3].view() eqv sum(view_f, 0, bsi3)
        proof {
            // Use the exact same closure expression as the invariant
            let ghost bsv_seq = Seq::new(block_sums@.len(),
                |k: int| block_sums@[k].view());
            let ghost bsv = |j: int| block_sums@[j].view();

            if b3 == 0 {
                // exclusive_scan(bsv_seq)[0] = sum(|j| bsv_seq[j], 0, 0)
                // Both sum(view_f, 0, 0) and sum(|j| bsv_seq[j], 0, 0) eqv R::zero()
                lemma_sum_empty::<R>(view_f, 0int, 0int);

                // block_prefixes[0] eqv exclusive_scan(bsv_seq)[0] from invariant
                // exclusive_scan(bsv_seq)[0] = R::zero() by definition (sum over empty range)
                // Bridge: block_prefixes[0].view() eqv exc_scan[0], exc_scan[0] eqv zero, zero eqv.sym sum(vf,0,0)
                let exc_val = exclusive_scan::<R>(bsv_seq)[0];
                lemma_sum_empty::<R>(|j: int| bsv_seq[j], 0int, 0int);
                // exc_val = sum(|j| bsv_seq[j], 0, 0) which eqv R::zero()
                R::axiom_eqv_transitive(
                    block_prefixes@[0].view(), exc_val, R::zero(),
                );
                R::axiom_eqv_symmetric(sum::<R>(view_f, 0, 0), R::zero());
                R::axiom_eqv_transitive(
                    block_prefixes@[0].view(), R::zero(), sum::<R>(view_f, 0, 0),
                );
            } else {
                // From invariant: block_prefixes[b3].view() eqv exclusive_scan(bsv_seq)[b3]
                let exc_val = exclusive_scan::<R>(bsv_seq)[b3 as int];
                // exc_val = sum(|j| bsv_seq[j], 0, b3) by definition of exclusive_scan

                // Congruence: sum(|j| bsv_seq[j], 0, b3) eqv sum(bsv, 0, b3)
                assert forall|j: int| 0 <= j < b3 as int implies
                    bsv_seq[j].eqv(bsv(j)) by {
                    R::axiom_eqv_reflexive(bsv_seq[j]);
                }
                lemma_sum_congruence::<R>(|j: int| bsv_seq[j], bsv, 0, b3 as int);

                // Block sums collapse: sum(bsv, 0, b3) eqv sum(view_f, 0, block_end(n, bs, b3-1))
                lemma_block_sums_collapse::<R>(
                    bsv, view_f, block_size as nat, n as nat, nblocks as nat, 0, b3 as int,
                );
                assert(block_start(block_size as nat, 0nat) == 0nat);
                // block_end(n, bs, b3-1) = bsi3 since b3*bs < n
                assert((b3 as int * block_size as int) < (n as int));
                assert(block_end(n as nat, block_size as nat, (b3 - 1) as nat) == bsi3 as nat);

                // Chain: block_prefixes[b3] eqv exc_val eqv sum(bsv, 0, b3) eqv sum(vf, 0, bsi3)
                // exc_val = sum(|j| bsv_seq[j], 0, b3), and we have
                // sum(|j| bsv_seq[j], 0, b3) eqv sum(bsv, 0, b3)
                R::axiom_eqv_transitive(
                    block_prefixes@[b3 as int].view(),
                    exc_val,
                    sum::<R>(bsv, 0, b3 as int),
                );
                R::axiom_eqv_transitive(
                    block_prefixes@[b3 as int].view(),
                    sum::<R>(bsv, 0, b3 as int),
                    sum::<R>(view_f, 0, bsi3 as int),
                );
            }
        }

        let mut j3: u64 = 0;
        while j3 < this_block_len3
            invariant
                j3 <= this_block_len3,
                this_block_len3 > 0,
                this_block_len3 <= block_size,
                bsi3 == b3 * block_size,
                bsi3 + this_block_len3 <= n,
                b3 < nblocks,
                nblocks > 0,
                nblocks as int <= n as int,
                nblocks as int * block_size as int >= n as int,
                data@.len() == n as nat,
                n > 0,
                n as int == data_len as int, // usize bridge
                block_size > 1,
                view_f == (|j: int| data@[j].view()),
                view_seq == Seq::new(data@.len(), view_f),
                all_partial_sums_representable::<T, R>(data@),
                output@.len() == n as nat,
                block_prefixes@.len() == nblocks as nat,
                result@.len() == (bsi3 as int + j3 as int) as nat,
                // Output invariant
                forall|bi: int, ji: int|
                    0 <= bi < nblocks as int && 0 <= ji < block_size as int
                    && (bi * block_size as int + ji) < (n as int)
                    ==> output@[bi * block_size as int + ji].view().eqv(
                        sum::<R>(view_f, bi * block_size as int, #[trigger](bi * block_size as int + ji + 1))
                    ),
                // Block prefix for b3
                block_prefixes@[b3 as int].view().eqv(
                    sum::<R>(view_f, 0, bsi3 as int)
                ),
                // Completed prior blocks
                forall|i: int| 0 <= i < (b3 as int * block_size as int) && i < n as int ==>
                    result@[i].view().eqv(inclusive_scan::<R>(view_seq)[i]),
                // Current block progress
                forall|k: int| 0 <= k < j3 as int ==>
                    (#[trigger] result@[(bsi3 as int + k) as int]).view().eqv(
                        inclusive_scan::<R>(view_seq)[(bsi3 as int + k) as int]
                    ),
            decreases this_block_len3 - j3,
        {
            proof {
                let gi = bsi3 as int + j3 as int;
                assert((gi) < (n as int));
                assert(((bsi3 + j3) as usize) as int == gi); // usize bridge
            }
            let idx: usize = (bsi3 + j3) as usize;
            // result[bsi3+j3] = block_prefix[b3] + output[bsi3+j3]
            proof {
                let gi = bsi3 as int + j3 as int;
                let prefix_view = block_prefixes@[b3 as int].view();
                let elem_view = output@[gi].view();

                // Trigger representability from all_partial_sums_representable
                assert(T::is_representable(partial_sum_generic::<T, R>(data@, 0, bsi3 as int)));
                assert(T::is_representable(partial_sum_generic::<T, R>(data@, bsi3 as int, gi + 1)));
                assert(T::is_representable(partial_sum_generic::<T, R>(data@, 0, gi + 1)));

                // prefix_view eqv sum(view_f, 0, bsi3) — from invariant
                // sum(view_f, 0, bsi3) == partial_sum_generic(data@, 0, bsi3) by view_f def
                R::axiom_eqv_symmetric(prefix_view, sum::<R>(view_f, 0, bsi3 as int));
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data@, 0, bsi3 as int),
                    prefix_view,
                );

                // elem_view eqv sum(view_f, bsi3, gi+1) — from output invariant
                // Trigger output invariant: bi = b3, j = j3
                assert(output@[b3 as int * block_size as int + j3 as int].view().eqv(
                    sum::<R>(view_f, b3 as int * block_size as int, b3 as int * block_size as int + j3 as int + 1)
                ));
                R::axiom_eqv_symmetric(elem_view, sum::<R>(view_f, bsi3 as int, gi + 1));
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data@, bsi3 as int, gi + 1),
                    elem_view,
                );

                // prefix_view.add(elem_view) eqv sum(view_f, 0, bsi3).add(sum(view_f, bsi3, gi+1))
                use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
                lemma_add_congruence::<R>(
                    prefix_view, sum::<R>(view_f, 0, bsi3 as int),
                    elem_view, sum::<R>(view_f, bsi3 as int, gi + 1),
                );

                // sum_split: sum(view_f, 0, gi+1) eqv sum(view_f, 0, bsi3).add(sum(view_f, bsi3, gi+1))
                lemma_sum_split::<R>(view_f, 0, bsi3 as int, gi + 1);
                R::axiom_eqv_symmetric(
                    sum::<R>(view_f, 0, gi + 1),
                    sum::<R>(view_f, 0, bsi3 as int).add(sum::<R>(view_f, bsi3 as int, gi + 1)),
                );

                // Chain: prefix.add(elem) eqv sum(0, bsi).add(sum(bsi, gi+1)) eqv sum(0, gi+1)
                R::axiom_eqv_transitive(
                    prefix_view.add(elem_view),
                    sum::<R>(view_f, 0, bsi3 as int).add(sum::<R>(view_f, bsi3 as int, gi + 1)),
                    sum::<R>(view_f, 0, gi + 1),
                );

                // is_representable(prefix.add(elem))
                R::axiom_eqv_symmetric(
                    prefix_view.add(elem_view),
                    sum::<R>(view_f, 0, gi + 1),
                );
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data@, 0, gi + 1),
                    prefix_view.add(elem_view),
                );
            }
            proof {
                assert((b3 as int) < (nblocks as int));
                assert((b3 as int) < (n as int)) by (nonlinear_arith)
                    requires (b3 as int) < (nblocks as int), nblocks as int <= n as int;
                assert((b3 as usize) as int == b3 as int);
            }
            let added = block_prefixes[b3 as usize].exec_add(&output[idx]);
            proof {
                let gi = bsi3 as int + j3 as int;
                // added.view() eqv block_prefixes[b3].view().add(output[gi].view())
                // which is eqv to sum(view_f, 0, gi+1)
                R::axiom_eqv_transitive(
                    added.view(),
                    block_prefixes@[b3 as int].view().add(output@[gi].view()),
                    sum::<R>(view_f, 0, gi + 1),
                );

                // Bridge sum(view_f, 0, gi+1) to inclusive_scan(view_seq)[gi]
                // inclusive_scan(view_seq)[gi] = sum(|j| view_seq[j], 0, gi+1)
                // view_seq[j] = view_f(j), so sum(|j| view_seq[j], ...) eqv sum(view_f, ...)
                assert forall|j: int| 0 <= j < gi + 1 implies
                    view_seq[j].eqv(view_f(j)) by {
                    R::axiom_eqv_reflexive(view_seq[j]);
                }
                lemma_sum_congruence::<R>(|j: int| view_seq[j], view_f, 0, gi + 1);
                // sum(|j| view_seq[j], 0, gi+1).eqv(sum(view_f, 0, gi+1))
                R::axiom_eqv_symmetric(
                    sum::<R>(|j: int| view_seq[j], 0, gi + 1),
                    sum::<R>(view_f, 0, gi + 1),
                );
                // sum(view_f, 0, gi+1).eqv(sum(|j| view_seq[j], 0, gi+1))
                // = inclusive_scan(view_seq)[gi]
                R::axiom_eqv_transitive(
                    added.view(),
                    sum::<R>(view_f, 0, gi + 1),
                    inclusive_scan::<R>(view_seq)[gi],
                );
            }
            result.push(added);

            j3 = j3 + 1;
        }

        proof {
            // Output length for next iteration
            if bsi3 + block_size <= n {
                assert(result@.len() == ((b3 as int + 1) * block_size as int) as nat) by (nonlinear_arith)
                    requires result@.len() as int == bsi3 as int + this_block_len3 as int,
                             bsi3 as int == b3 as int * block_size as int,
                             this_block_len3 == block_size;
                assert((b3 + 1) as int * block_size as int <= n as int) by (nonlinear_arith)
                    requires bsi3 as int + block_size as int <= n as int,
                             bsi3 as int == b3 as int * block_size as int;
            } else {
                assert(result@.len() == n as nat);
            }

            // Bridge: (b3+1)*bs == bsi3+bs for invariant form
            assert((b3 as int + 1) * block_size as int == bsi3 as int + block_size as int)
                by (nonlinear_arith)
                requires bsi3 as int == b3 as int * block_size as int;

            // b3+1 < nblocks ==> (b3+1)*bs < n
            if b3 + 1 < nblocks {
                assert(((b3 + 1) as int) * (block_size as int) < (n as int)) by (nonlinear_arith)
                    requires (b3 + 1) as int <= (nblocks as int - 1),
                             ((nblocks as int - 1) * (block_size as int)) < (n as int),
                             block_size > 0;
            }

            // Completed result: combine prior blocks with current block
            assert forall|i: int| 0 <= i < result@.len() as int implies
                result@[i].view().eqv(inclusive_scan::<R>(view_seq)[i])
            by {
                if i < bsi3 as int {
                    // From "completed prior blocks" invariant
                } else {
                    // From "current block progress" invariant (j3 == this_block_len3)
                    let k = i - bsi3 as int;
                    assert(0 <= k);
                    assert(k < this_block_len3 as int);
                    assert(result@[(bsi3 as int + k) as int].view().eqv(
                        inclusive_scan::<R>(view_seq)[(bsi3 as int + k) as int]
                    ));
                }
            }
        }
        b3 = b3 + 1;
    }

    // Prove second ensures: bridge inclusive_scan to partial_sum_generic
    proof {
        assert forall|i: int| 0 <= i < data@.len() as int implies
            result@[i].view().eqv(partial_sum_generic::<T, R>(data@, 0, i + 1))
        by {
            // From Phase 3 invariant: result@[i].view() eqv inclusive_scan(view_seq)[i]
            // inclusive_scan(view_seq)[i] = sum(|j| view_seq[j], 0, i+1)
            // partial_sum_generic(data@, 0, i+1) = sum(|j| data@[j].view(), 0, i+1)
            // view_seq[j] = data@[j].view() by Seq::new axiom
            assert forall|j: int| 0 <= j < i + 1 implies
                view_seq[j].eqv(data@[j].view()) by {
                R::axiom_eqv_reflexive(view_seq[j]);
            }
            lemma_sum_congruence::<R>(
                |j: int| view_seq[j],
                |j: int| data@[j].view(),
                0, i + 1,
            );
            R::axiom_eqv_transitive(
                result@[i].view(),
                inclusive_scan::<R>(view_seq)[i],
                partial_sum_generic::<T, R>(data@, 0, i + 1),
            );
        }
    }

    result
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
