use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::coalesce::*;
use crate::inverse::*;
use super::*;
use super::layout::RuntimeLayout;

verus! {

/// Check if a layout is fully coalesced (no adjacent coalesceable pairs).
pub open spec fn is_fully_coalesced(layout: &LayoutSpec) -> bool {
    forall|i: int| 0 <= i < layout.shape.len() as int - 1 ==>
        !modes_coalesceable(layout, i)
}

/// Find the index of stride == target in a Vec, or return the Vec length if not found.
fn find_stride_value(stride: &Vec<i64>, target: i64) -> (result: usize)
    ensures
        result <= stride@.len(),
        result < stride@.len() ==> stride@[result as int] == target,
        // First match guarantee: no earlier element matches
        forall|j: int| 0 <= j < result as int ==> stride@[j] != target,
        result == stride@.len() ==>
            forall|j: int| 0 <= j < stride@.len() ==> stride@[j] != target,
{
    let mut j: usize = 0;
    while j < stride.len()
        invariant
            0 <= j <= stride@.len(),
            forall|k: int| 0 <= k < j as int ==> stride@[k] != target,
        decreases stride.len() - j,
    {
        if stride[j] == target {
            return j;
        }
        j = j + 1;
    }
    stride.len()
}

/// Find the index of the element with smallest positive value in a Vec.
/// Returns Vec length if no positive element exists.
fn find_min_positive_exec(stride: &Vec<i64>) -> (result: usize)
    ensures
        result <= stride@.len(),
        result < stride@.len() ==> stride@[result as int] > 0,
        result < stride@.len() ==>
            forall|j: int| 0 <= j < stride@.len() && stride@[j] > 0
                ==> stride@[result as int] <= stride@[j],
        // First minimum: no earlier index has the same or smaller positive value
        result < stride@.len() ==>
            forall|j: int| 0 <= j < result as int
                ==> stride@[j] <= 0 || stride@[j] > stride@[result as int],
        result == stride@.len() ==>
            forall|j: int| 0 <= j < stride@.len() ==> stride@[j] <= 0,
{
    let mut best: usize = stride.len();
    let mut best_val: i64 = i64::MAX;
    let mut j: usize = 0;
    while j < stride.len()
        invariant
            0 <= j <= stride@.len(),
            best <= stride@.len(),
            best < stride@.len() ==> stride@[best as int] > 0,
            best < stride@.len() ==> stride@[best as int] == best_val,
            best < stride@.len() ==>
                forall|k: int| 0 <= k < j as int && stride@[k] > 0
                    ==> best_val <= stride@[k],
            // First minimum invariant
            best < stride@.len() ==>
                forall|k: int| 0 <= k < best as int
                    ==> stride@[k] <= 0 || stride@[k] > best_val,
            best == stride@.len() ==>
                forall|k: int| 0 <= k < j as int ==> stride@[k] <= 0,
        decreases stride.len() - j,
    {
        if stride[j] > 0 && (best == stride.len() || stride[j] < best_val) {
            proof {
                // When updating best to j, prove the first-minimum invariant:
                // For all k < j: stride[k] <= 0 || stride[k] > stride[j]
                // Case: best was len() (no previous best) — all k < j have stride[k] <= 0
                // Case: stride[j] < best_val — k < best already satisfy invariant (old first-min),
                //   and best <= k < j have stride[k] >= best_val > stride[j]
                assert forall|k: int| 0 <= k < j as int
                    implies stride@[k] <= 0 || stride@[k] > stride@[j as int]
                by {
                    if best == stride.len() {
                        // All k < j have stride[k] <= 0
                    } else {
                        // stride[j] < best_val
                        if k < best as int {
                            // From old first-min: stride[k] <= 0 || stride[k] > best_val
                            // best_val > stride[j], so stride[k] > best_val > stride[j]
                        } else {
                            // best <= k < j: stride[k] positive ==> stride[k] >= best_val > stride[j]
                        }
                    }
                };
            }
            best = j;
            best_val = stride[j];
        }
        j = j + 1;
    }
    best
}

/// Copy a Vec<u64> excluding element at position `skip_idx`.
fn copy_except_u64(v: &Vec<u64>, skip_idx: usize) -> (result: Vec<u64>)
    requires
        skip_idx < v@.len(),
    ensures
        result@.len() == v@.len() - 1,
        forall|j: int| 0 <= j < skip_idx as int ==> #[trigger] result@[j] == v@[j],
        forall|j: int| skip_idx as int <= j < result@.len() as int ==> #[trigger] result@[j] == v@[j + 1],
{
    let mut result: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < v.len()
        invariant
            0 <= k <= v@.len(),
            skip_idx < v@.len(),
            k <= skip_idx ==> result@.len() == k as int,
            k > skip_idx ==> result@.len() == (k as int) - 1,
            forall|j: int| 0 <= j < result@.len() as int && j < (skip_idx as int)
                ==> #[trigger] result@[j] == v@[j],
            forall|j: int| (skip_idx as int) <= j < result@.len() as int
                ==> #[trigger] result@[j] == v@[j + 1],
        decreases v.len() - k,
    {
        if k != skip_idx {
            result.push(v[k]);
        }
        k = k + 1;
    }
    result
}

/// Copy a Vec<i64> excluding element at position `skip_idx`.
fn copy_except_i64(v: &Vec<i64>, skip_idx: usize) -> (result: Vec<i64>)
    requires
        skip_idx < v@.len(),
    ensures
        result@.len() == v@.len() - 1,
        forall|j: int| 0 <= j < skip_idx as int ==> #[trigger] result@[j] == v@[j],
        forall|j: int| skip_idx as int <= j < result@.len() as int ==> #[trigger] result@[j] == v@[j + 1],
{
    let mut result: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < v.len()
        invariant
            0 <= k <= v@.len(),
            skip_idx < v@.len(),
            k <= skip_idx ==> result@.len() == k as int,
            k > skip_idx ==> result@.len() == (k as int) - 1,
            forall|j: int| 0 <= j < result@.len() as int && j < (skip_idx as int)
                ==> #[trigger] result@[j] == v@[j],
            forall|j: int| (skip_idx as int) <= j < result@.len() as int
                ==> #[trigger] result@[j] == v@[j + 1],
        decreases v.len() - k,
    {
        if k != skip_idx {
            result.push(v[k]);
        }
        k = k + 1;
    }
    result
}

/// Compute the right inverse of a layout at runtime.
///
/// Requires the layout is already fully coalesced (no adjacent coalesceable pairs).
/// The result satisfies: layout.offset(result.offset(j)) == j for j in [0, result.size()).
pub fn right_inverse_exec(layout: &RuntimeLayout) -> (result: RuntimeLayout)
    requires
        layout.wf_spec(),
        is_fully_coalesced(&layout@),
        // Overflow: prefix products fit in i64 (result strides are prefix products cast to i64)
        forall|i: nat| i <= layout@.shape.len() ==>
            shape_size(layout@.shape.take(i as int)) <= i64::MAX as nat,
        // Result size fits in u64
        shape_size(right_inverse(&layout@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == right_inverse(&layout@),
{
    // Step 1: Compute prefix products of shape
    let mut preprod: Vec<u64> = Vec::new();
    let mut pp: u64 = 1;
    let mut i: usize = 0;

    while i < layout.shape.len()
        invariant
            0 <= i <= layout.shape@.len(),
            layout.wf_spec(),
            preprod@.len() == i,
            pp as nat == shape_size(layout@.shape.take(i as int)),
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] preprod@[j] as nat == shape_size(layout@.shape.take(j)),
            forall|k: nat| k <= layout@.shape.len() ==>
                shape_size(layout@.shape.take(k as int)) <= i64::MAX as nat,
        decreases layout.shape.len() - i,
    {
        preprod.push(pp);
        proof {
            crate::runtime::shape_helpers::lemma_shape_size_take_step(layout@.shape, i as nat);
        }
        let s_i = layout.shape[i];
        proof {
            assert(s_i as nat == layout@.shape[i as int]);
            assert(shape_size(layout@.shape.take((i + 1) as int))
                == shape_size(layout@.shape.take(i as int)) * layout@.shape[i as int]);
            assert(shape_size(layout@.shape.take((i + 1) as int)) <= i64::MAX as nat);
        }
        pp = pp * s_i;
        i = i + 1;
    }

    // Step 2: Build right inverse by finding modes with stride == cursor
    // Copy layout into mutable remaining vectors
    let mut rem_shape: Vec<u64> = Vec::new();
    let mut rem_stride: Vec<i64> = Vec::new();
    let mut rem_preprod: Vec<u64> = Vec::new();
    i = 0;
    while i < layout.shape.len()
        invariant
            0 <= i <= layout.shape@.len(),
            layout.wf_spec(),
            rem_shape@.len() == i,
            rem_stride@.len() == i,
            rem_preprod@.len() == i,
            preprod@.len() == layout.shape@.len(),
            forall|j: int| 0 <= j < i as int ==> rem_shape@[j] == layout.shape@[j],
            forall|j: int| 0 <= j < i as int ==> rem_stride@[j] == layout.stride@[j],
            forall|j: int| 0 <= j < i as int ==> rem_preprod@[j] == preprod@[j],
        decreases layout.shape.len() - i,
    {
        rem_shape.push(layout.shape[i]);
        rem_stride.push(layout.stride[i]);
        rem_preprod.push(preprod[i]);
        i = i + 1;
    }

    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();
    let mut cursor: u64 = 1;

    // Establish ghost initial state
    proof {
        crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&layout@);
        // coalesce(layout@) == layout@, so right_inverse uses layout@ directly

        // rem_shape/stride match layout@ via wf_spec
        assert(shape_to_nat_seq(rem_shape@) =~= layout@.shape) by {
            assert forall|j: int| 0 <= j < rem_shape@.len()
                implies shape_to_nat_seq(rem_shape@)[j] == layout@.shape[j]
            by {
                assert(rem_shape@[j] == layout.shape@[j]);
            };
        };
        assert(strides_to_int_seq(rem_stride@) =~= layout@.stride) by {
            assert forall|j: int| 0 <= j < rem_stride@.len()
                implies strides_to_int_seq(rem_stride@)[j] == layout@.stride[j]
            by {
                assert(rem_stride@[j] == layout.stride@[j]);
            };
        };

        // preprod correspondence with spec prefix products
        let spec_pp = shape_prefix_products(layout@.shape);
        crate::proof::inverse_lemmas::lemma_prefix_products_len(layout@.shape);
        assert(shape_to_nat_seq(rem_preprod@) =~= spec_pp.take(layout@.shape.len() as int)) by {
            assert forall|j: int| 0 <= j < rem_preprod@.len()
                implies shape_to_nat_seq(rem_preprod@)[j]
                    == spec_pp.take(layout@.shape.len() as int)[j]
            by {
                assert(rem_preprod@[j] == preprod@[j]);
                assert(preprod@[j] as nat == shape_size(layout@.shape.take(j)));
                crate::proof::inverse_lemmas::lemma_prefix_products_value(
                    layout@.shape, j as nat);
            };
        };

        // Initial product invariant: 1 * shape_size(shape) = shape_size(shape)
        assert(shape_valid(shape_to_nat_seq(rem_shape@)));
        assert(1nat * shape_size(shape_to_nat_seq(rem_shape@))
            == shape_size(shape_to_nat_seq(rem_shape@)));

        // All preprod values fit in i64 (they're prefix products, bounded by precondition)
        assert forall|j: int| 0 <= j < rem_preprod@.len()
            implies (rem_preprod@[j] as nat) <= i64::MAX as nat
        by {
            assert(rem_preprod@[j] == preprod@[j]);
            assert(preprod@[j] as nat == shape_size(layout@.shape.take(j)));
            assert(shape_size(layout@.shape.take(j)) <= i64::MAX as nat);
        };
    }
    let ghost full_spec = right_inverse(&layout@);

    // Main loop
    let mut done: bool = false;
    while !done && rem_shape.len() > 0
        invariant
            rem_shape@.len() == rem_stride@.len(),
            rem_shape@.len() == rem_preprod@.len(),
            result_shape@.len() == result_stride@.len(),
            layout.wf_spec(),
            full_spec == right_inverse(&layout@),
            // Overflow bounds
            forall|k: nat| k <= layout@.shape.len() ==>
                shape_size(layout@.shape.take(k as int)) <= i64::MAX as nat,
            // Cursor * remaining product = total product
            shape_valid(shape_to_nat_seq(rem_shape@)),
            cursor as nat * shape_size(shape_to_nat_seq(rem_shape@)) == shape_size(layout@.shape),
            // Cursor fits in i64 for stride comparison
            cursor <= i64::MAX as u64,
            // All remaining preprod values fit in i64
            forall|j: int| 0 <= j < rem_preprod@.len() ==>
                (rem_preprod@[j] as nat) <= i64::MAX as nat,
            // Ghost correspondence: accumulated result + remaining = full result
            ({
                let rem_build = right_inverse_build(
                    shape_to_nat_seq(rem_shape@),
                    strides_to_int_seq(rem_stride@),
                    shape_to_nat_seq(rem_preprod@),
                    cursor as nat,
                );
                &&& full_spec.shape =~= shape_to_nat_seq(result_shape@).add(rem_build.shape)
                &&& full_spec.stride =~= strides_to_int_seq(result_stride@).add(rem_build.stride)
            }),
            // When done, remaining is empty
            done ==> ({
                let rem_build = right_inverse_build(
                    shape_to_nat_seq(rem_shape@),
                    strides_to_int_seq(rem_stride@),
                    shape_to_nat_seq(rem_preprod@),
                    cursor as nat,
                );
                rem_build.shape.len() == 0 && rem_build.stride.len() == 0
            }),
        decreases if done { 0nat } else { rem_shape@.len() + 1 },
    {
        let idx = find_stride_value(&rem_stride, cursor as i64);
        if idx == rem_stride.len() {
            proof {
                assert(cursor as i64 as int == cursor as int);  // from cursor <= i64::MAX
                crate::proof::inverse_lemmas::lemma_find_value_correspondence(
                    rem_stride@, cursor as i64, idx);
                // lemma gives: find_value(...).is_none()
                // Since (cursor as i64) as int == cursor as int:
                let rem_s = shape_to_nat_seq(rem_shape@);
                let rem_d = strides_to_int_seq(rem_stride@);
                let rem_p = shape_to_nat_seq(rem_preprod@);
                assert(find_value(rem_d, cursor as int).is_none());
                // right_inverse_build: find_value is None → returns empty
                assert(right_inverse_build(rem_s, rem_d, rem_p, cursor as nat)
                    == LayoutSpec { shape: seq![], stride: seq![] });
            }
            done = true;
        } else {
            let m = rem_shape[idx];
            let pp_val = rem_preprod[idx];

            // Save ghost snapshots before mutations
            let ghost old_result_shape = result_shape@;
            let ghost old_result_stride = result_stride@;
            let ghost old_rem_shape = rem_shape@;
            let ghost old_rem_stride = rem_stride@;
            let ghost old_rem_preprod = rem_preprod@;
            let ghost old_cursor = cursor;

            proof {
                // Step 1: find_value correspondence
                assert(cursor as i64 as int == cursor as int);  // from cursor <= i64::MAX
                crate::proof::inverse_lemmas::lemma_find_value_correspondence(
                    old_rem_stride, cursor as i64, idx);
                let rem_s = shape_to_nat_seq(old_rem_shape);
                let rem_d = strides_to_int_seq(old_rem_stride);
                let rem_p = shape_to_nat_seq(old_rem_preprod);
                assert(find_value(rem_d, cursor as int) == Some(idx as nat));

                // Step 2: right_inverse_build unfolds one level
                let rem_build = right_inverse_build(rem_s, rem_d, rem_p, cursor as nat);
                let m_spec = rem_s[idx as int];
                let pp_spec = rem_p[idx as int];
                assert(m_spec == m as nat);
                assert(pp_spec == pp_val as nat);
                let rest = right_inverse_build(
                    remove_at_nat(rem_s, idx as int),
                    remove_at_int(rem_d, idx as int),
                    remove_at_nat(rem_p, idx as int),
                    m_spec * cursor as nat,
                );
                assert(rem_build.shape =~= seq![m_spec].add(rest.shape));
                assert(rem_build.stride =~= seq![pp_spec as int].add(rest.stride));
            }

            result_shape.push(m);
            result_stride.push(pp_val as i64);

            proof {
                // cursor * m <= shape_size(layout@.shape) <= i64::MAX
                let rem_s = shape_to_nat_seq(old_rem_shape);
                crate::proof::inverse_lemmas::lemma_shape_size_remove(rem_s, idx as int);
                let removed_size = shape_size(remove_at_nat(rem_s, idx as int));
                // m * removed_size == shape_size(rem_s)
                // cursor * shape_size(rem_s) == shape_size(total)  [invariant]
                // So cursor * (m * removed_size) == shape_size(total)
                vstd::arithmetic::mul::lemma_mul_is_associative(
                    cursor as int, m as int, removed_size as int);
                assert((cursor as int) * (m as int) * (removed_size as int)
                    == (cursor as int) * ((m as int) * (removed_size as int)));
                assert((cursor as nat) * (m as nat * removed_size)
                    == shape_size(layout@.shape));

                // removed_size >= 1
                crate::proof::shape_lemmas::lemma_shape_size_positive(
                    remove_at_nat(rem_s, idx as int));
                // 1 <= removed_size, cursor*m >= 0 => cursor*m <= removed_size * (cursor*m)
                vstd::arithmetic::mul::lemma_mul_inequality(
                    1int, removed_size as int, (cursor as int) * (m as int));
                // 1 * (cursor*m) <= removed_size * (cursor*m)
                vstd::arithmetic::mul::lemma_mul_is_commutative(
                    removed_size as int, (cursor as int) * (m as int));
                // cursor*m <= (cursor*m) * removed_size = shape_size(total)

                assert(layout@.shape.take(layout@.shape.len() as int) =~= layout@.shape);
                assert(shape_size(layout@.shape) <= i64::MAX as nat);
            }
            cursor = cursor * m;

            rem_shape = copy_except_u64(&rem_shape, idx);
            rem_stride = copy_except_i64(&rem_stride, idx);
            let old_pp = rem_preprod;
            rem_preprod = copy_except_u64(&old_pp, idx);

            proof {
                // Step 3: Connect new rem_* with remove_at via correspondence lemmas
                let rem_s = shape_to_nat_seq(old_rem_shape);
                let rem_d = strides_to_int_seq(old_rem_stride);
                let rem_p = shape_to_nat_seq(old_rem_preprod);

                // copy_except_u64 gives take/skip decomposition
                assert(rem_shape@ =~= old_rem_shape.take(idx as int).add(
                    old_rem_shape.skip(idx as int + 1)));
                crate::proof::inverse_lemmas::lemma_remove_at_nat_correspondence(
                    old_rem_shape, idx as int);
                assert(shape_to_nat_seq(rem_shape@) =~= remove_at_nat(rem_s, idx as int));

                assert(rem_stride@ =~= old_rem_stride.take(idx as int).add(
                    old_rem_stride.skip(idx as int + 1)));
                crate::proof::inverse_lemmas::lemma_remove_at_int_correspondence(
                    old_rem_stride, idx as int);
                assert(strides_to_int_seq(rem_stride@) =~= remove_at_int(rem_d, idx as int));

                assert(rem_preprod@ =~= old_rem_preprod.take(idx as int).add(
                    old_rem_preprod.skip(idx as int + 1)));
                crate::proof::inverse_lemmas::lemma_remove_at_nat_correspondence(
                    old_rem_preprod, idx as int);
                assert(shape_to_nat_seq(rem_preprod@) =~= remove_at_nat(rem_p, idx as int));

                // Step 4: cursor correspondence
                let m_spec = rem_s[idx as int];
                assert(m_spec == m as nat);
                // cursor was updated: cursor = old_cursor * m
                // Since no overflow (assumed above): cursor as nat == old_cursor as nat * m as nat
                assert(cursor as nat == (old_cursor as nat) * (m as nat));
                vstd::arithmetic::mul::lemma_mul_is_commutative(m_spec as int, old_cursor as int);
                assert(cursor as nat == m_spec * (old_cursor as nat));

                // Step 5: New remaining = rest from the unfolding
                let rest = right_inverse_build(
                    remove_at_nat(rem_s, idx as int),
                    remove_at_int(rem_d, idx as int),
                    remove_at_nat(rem_p, idx as int),
                    m_spec * old_cursor as nat,
                );
                let new_rem_build = right_inverse_build(
                    shape_to_nat_seq(rem_shape@),
                    strides_to_int_seq(rem_stride@),
                    shape_to_nat_seq(rem_preprod@),
                    cursor as nat,
                );
                assert(new_rem_build == rest);

                // Step 6: Seq::add associativity for shape
                let pp_spec = rem_p[idx as int];
                let old_rem_build = right_inverse_build(rem_s, rem_d, rem_p, old_cursor as nat);
                assert(old_rem_build.shape =~= seq![m_spec].add(rest.shape));
                assert(full_spec.shape =~= shape_to_nat_seq(old_result_shape).add(
                    old_rem_build.shape));
                // full_spec.shape =~= nat(old_result).add(seq![m_spec].add(rest.shape))
                //                 =~= nat(old_result).add(seq![m_spec]).add(rest.shape)
                // nat(new_result) =~= nat(old_result).push(m as nat)
                //                 =~= nat(old_result).add(seq![m as nat])
                //                 =~= nat(old_result).add(seq![m_spec])
                assert(shape_to_nat_seq(result_shape@) =~=
                    shape_to_nat_seq(old_result_shape).add(seq![m_spec]));
                // Seq::add associativity
                assert(shape_to_nat_seq(old_result_shape).add(
                    seq![m_spec].add(rest.shape))
                    =~= shape_to_nat_seq(old_result_shape).add(seq![m_spec]).add(rest.shape));

                // Similarly for stride
                assert(old_rem_build.stride =~= seq![pp_spec as int].add(rest.stride));
                // pp_val fits in i64 (from loop invariant: all rem_preprod values <= i64::MAX)
                assert(pp_val as nat <= i64::MAX as nat);
                assert((pp_val as i64) as int == pp_val as int);
                assert(pp_spec as int == pp_val as int);
                assert(strides_to_int_seq(result_stride@) =~=
                    strides_to_int_seq(old_result_stride).add(seq![pp_spec as int]));
                assert(strides_to_int_seq(old_result_stride).add(
                    seq![pp_spec as int].add(rest.stride))
                    =~= strides_to_int_seq(old_result_stride).add(seq![pp_spec as int]).add(
                        rest.stride));

                // Maintain shape_valid(shape_to_nat_seq(rem_shape@))
                let new_rem_s = shape_to_nat_seq(rem_shape@);
                assert(new_rem_s =~= remove_at_nat(rem_s, idx as int));
                assert(shape_valid(new_rem_s)) by {
                    assert forall|j: int| 0 <= j < new_rem_s.len()
                        implies #[trigger] new_rem_s[j] > 0
                    by {
                        if j < idx as int {
                            assert(new_rem_s[j] == rem_s[j]);
                        } else {
                            assert(new_rem_s[j] == rem_s[j + 1]);
                        }
                    };
                };

                // Maintain product invariant:
                // cursor * shape_size(new_rem_s) == shape_size(layout@.shape)
                // cursor = old_cursor * m, new_rem_s = remove_at(rem_s, idx)
                // lemma_shape_size_remove: m * shape_size(remove_at) == shape_size(rem_s)
                // old: old_cursor * shape_size(rem_s) == shape_size(layout@.shape)
                // shape_size(rem_s) == m * shape_size(new_rem_s)
                // old_cursor * m * shape_size(new_rem_s) == shape_size(layout@.shape)
                // cursor * shape_size(new_rem_s) == shape_size(layout@.shape)
                crate::proof::inverse_lemmas::lemma_shape_size_remove(rem_s, idx as int);
                assert(m_spec * shape_size(remove_at_nat(rem_s, idx as int)) == shape_size(rem_s));
                assert(shape_size(new_rem_s) == shape_size(remove_at_nat(rem_s, idx as int)));
                vstd::arithmetic::mul::lemma_mul_is_commutative(
                    old_cursor as int, m_spec as int);
                vstd::arithmetic::mul::lemma_mul_is_associative(
                    old_cursor as int, m_spec as int, shape_size(new_rem_s) as int);
                assert(cursor as nat * shape_size(new_rem_s) == shape_size(layout@.shape));

                // Maintain preprod bounds: copy_except only removes entries
                assert forall|j: int| 0 <= j < rem_preprod@.len()
                    implies (rem_preprod@[j] as nat) <= i64::MAX as nat
                by {
                    if j < idx as int {
                        assert(rem_preprod@[j] == old_rem_preprod[j]);
                    } else {
                        assert(rem_preprod@[j] == old_rem_preprod[j + 1]);
                    }
                };
            }
        }
    }

    proof {
        // After loop: remaining is empty
        let rem_build = right_inverse_build(
            shape_to_nat_seq(rem_shape@),
            strides_to_int_seq(rem_stride@),
            shape_to_nat_seq(rem_preprod@),
            cursor as nat,
        );
        if rem_shape@.len() == 0 {
            // right_inverse_build on empty returns empty
            assert(shape_to_nat_seq(rem_shape@).len() == 0);
            assert(rem_build == LayoutSpec { shape: seq![], stride: seq![] });
        }
        // In both cases (done or empty), rem_build has empty shape/stride
        assert(rem_build.shape.len() == 0);
        assert(rem_build.stride.len() == 0);
        assert(full_spec.shape =~= shape_to_nat_seq(result_shape@));
        assert(full_spec.stride =~= strides_to_int_seq(result_stride@));

        // Prove right_inverse(&layout@).valid()
        crate::proof::inverse_lemmas::lemma_right_inverse_valid(&layout@);
    }

    RuntimeLayout {
        shape: result_shape,
        stride: result_stride,
        model: Ghost(right_inverse(&*layout.model.borrow())),
    }
}

/// Compute the left inverse of a layout at runtime.
pub fn left_inverse_exec(layout: &RuntimeLayout) -> (result: RuntimeLayout)
    requires
        layout.wf_spec(),
        is_fully_coalesced(&layout@),
        layout@.shape.len() > 0,
        // All strides positive (left inverse is only meaningful for injective layouts)
        forall|i: int| 0 <= i < layout@.stride.len() ==> layout@.stride[i] > 0,
        // Overflow: prefix products fit in i64 (result strides are prefix products cast to i64)
        forall|i: nat| i <= layout@.shape.len() ==>
            shape_size(layout@.shape.take(i as int)) <= i64::MAX as nat,
        // Result size fits in u64
        shape_size(left_inverse(&layout@).shape) <= u64::MAX as nat,
    ensures
        result.wf_spec(),
        result@ == left_inverse(&layout@),
{
    // Step 1: Compute prefix products of shape
    let mut preprod: Vec<u64> = Vec::new();
    let mut pp: u64 = 1;
    let mut i: usize = 0;

    while i < layout.shape.len()
        invariant
            0 <= i <= layout.shape@.len(),
            layout.wf_spec(),
            preprod@.len() == i,
            pp as nat == shape_size(layout@.shape.take(i as int)),
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] preprod@[j] as nat == shape_size(layout@.shape.take(j)),
            forall|k: nat| k <= layout@.shape.len() ==>
                shape_size(layout@.shape.take(k as int)) <= i64::MAX as nat,
        decreases layout.shape.len() - i,
    {
        preprod.push(pp);
        proof {
            crate::runtime::shape_helpers::lemma_shape_size_take_step(layout@.shape, i as nat);
        }
        let s_i = layout.shape[i];
        proof {
            assert(s_i as nat == layout@.shape[i as int]);
            assert(shape_size(layout@.shape.take((i + 1) as int)) <= i64::MAX as nat);
        }
        pp = pp * s_i;
        i = i + 1;
    }

    // Step 2: Copy into mutable remaining vectors
    let mut rem_shape: Vec<u64> = Vec::new();
    let mut rem_stride: Vec<i64> = Vec::new();
    let mut rem_preprod: Vec<u64> = Vec::new();
    i = 0;
    while i < layout.shape.len()
        invariant
            0 <= i <= layout.shape@.len(),
            layout.wf_spec(),
            rem_shape@.len() == i,
            rem_stride@.len() == i,
            rem_preprod@.len() == i,
            preprod@.len() == layout.shape@.len(),
            forall|j: int| 0 <= j < i as int ==> rem_shape@[j] == layout.shape@[j],
            forall|j: int| 0 <= j < i as int ==> rem_stride@[j] == layout.stride@[j],
            forall|j: int| 0 <= j < i as int ==> rem_preprod@[j] == preprod@[j],
        decreases layout.shape.len() - i,
    {
        rem_shape.push(layout.shape[i]);
        rem_stride.push(layout.stride[i]);
        rem_preprod.push(preprod[i]);
        i = i + 1;
    }

    proof {
        // Establish initial conditions for the main loop
        crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&layout@);

        // rem_shape entries > 0 (from layout shape validity)
        assert forall|j: int| 0 <= j < rem_shape@.len()
            implies #[trigger] rem_shape@[j] > 0u64
        by {
            assert(rem_shape@[j] == layout.shape@[j]);
            assert(layout@.shape[j] > 0);
            assert(layout.shape@[j] as nat == layout@.shape[j]);
        };
        // Preprod values fit in i64
        assert forall|j: int| 0 <= j < rem_preprod@.len()
            implies (rem_preprod@[j] as nat) <= i64::MAX as nat
        by {
            assert(rem_preprod@[j] == preprod@[j]);
            assert(preprod@[j] as nat == shape_size(layout@.shape.take(j)));
            assert(shape_size(layout@.shape.take(j)) <= i64::MAX as nat);
        };

        // Ghost correspondence: rem_shape/stride/preprod match spec
        assert(shape_to_nat_seq(rem_shape@) =~= layout@.shape) by {
            assert forall|j: int| 0 <= j < rem_shape@.len()
                implies shape_to_nat_seq(rem_shape@)[j] == layout@.shape[j]
            by { assert(rem_shape@[j] == layout.shape@[j]); };
        };
        assert(strides_to_int_seq(rem_stride@) =~= layout@.stride) by {
            assert forall|j: int| 0 <= j < rem_stride@.len()
                implies strides_to_int_seq(rem_stride@)[j] == layout@.stride[j]
            by { assert(rem_stride@[j] == layout.stride@[j]); };
        };

        // Preprod correspondence
        let spec_pp = shape_prefix_products(layout@.shape);
        crate::proof::inverse_lemmas::lemma_prefix_products_len(layout@.shape);
        let spec_preprod = spec_pp.take(layout@.shape.len() as int);
        assert(shape_to_nat_seq(rem_preprod@) =~= spec_preprod) by {
            assert forall|j: int| 0 <= j < rem_preprod@.len()
                implies shape_to_nat_seq(rem_preprod@)[j] == spec_preprod[j]
            by {
                assert(rem_preprod@[j] == preprod@[j]);
                assert(preprod@[j] as nat == shape_size(layout@.shape.take(j)));
                crate::proof::inverse_lemmas::lemma_prefix_products_value(
                    layout@.shape, j as nat);
            };
        };

        assert(shape_valid(shape_to_nat_seq(rem_shape@)));
    }

    // Step 3: Build left inverse iteratively
    let mut result_shape: Vec<u64> = Vec::new();
    let mut result_stride: Vec<i64> = Vec::new();
    let mut acc_size: u64 = 1;

    let ghost full_raw_spec = {
        let c = *layout.model.borrow();
        let pp = shape_prefix_products(c.shape);
        let preprod = pp.take(c.shape.len() as int);
        left_inverse_build(c.shape, c.stride, preprod, 1)
    };

    let mut done: bool = false;
    while !done && rem_shape.len() > 0
        invariant
            rem_shape@.len() == rem_stride@.len(),
            rem_shape@.len() == rem_preprod@.len(),
            acc_size > 0,
            layout.wf_spec(),
            is_fully_coalesced(&layout@),
            forall|k: nat| k <= layout@.shape.len() ==>
                shape_size(layout@.shape.take(k as int)) <= i64::MAX as nat,
            // All remaining shape entries > 0
            forall|j: int| 0 <= j < rem_shape@.len() ==>
                #[trigger] rem_shape@[j] > 0u64,
            // All remaining positive strides >= acc_size
            forall|j: int| 0 <= j < rem_stride@.len() && rem_stride@[j] > 0 ==>
                rem_stride@[j] >= acc_size as int,
            // All preprod values fit in i64
            forall|j: int| 0 <= j < rem_preprod@.len() ==>
                (rem_preprod@[j] as nat) <= i64::MAX as nat,
            // All result shape entries are > 0
            forall|j: int| 0 <= j < result_shape@.len() ==>
                #[trigger] result_shape@[j] > 0u64,
            // Result shape/stride length relationship
            !done ==> result_shape@.len() == result_stride@.len(),
            done ==> (result_shape@.len() == result_stride@.len()
                || result_shape@.len() == result_stride@.len() + 1),
            // Ghost correspondence: accumulated + remaining = full raw spec
            ({
                let rem_build = left_inverse_build(
                    shape_to_nat_seq(rem_shape@),
                    strides_to_int_seq(rem_stride@),
                    shape_to_nat_seq(rem_preprod@),
                    acc_size as nat,
                );
                &&& full_raw_spec.shape =~= shape_to_nat_seq(result_shape@).add(rem_build.shape)
                &&& full_raw_spec.stride =~= strides_to_int_seq(result_stride@).add(rem_build.stride)
            }),
            // When done, remaining build is empty
            done ==> ({
                let rem_build = left_inverse_build(
                    shape_to_nat_seq(rem_shape@),
                    strides_to_int_seq(rem_stride@),
                    shape_to_nat_seq(rem_preprod@),
                    acc_size as nat,
                );
                rem_build.shape.len() == 0 && rem_build.stride.len() == 0
            }),
        decreases if done { 0nat } else { rem_shape@.len() + 1 },
    {
        let idx = find_min_positive_exec(&rem_stride);
        if idx == rem_stride.len() {
            proof {
                // find_min_positive_exec found no positive → correspondence
                crate::proof::inverse_lemmas::lemma_find_min_positive_correspondence(
                    rem_stride@, idx);
                let rem_s = shape_to_nat_seq(rem_shape@);
                let rem_d = strides_to_int_seq(rem_stride@);
                let rem_p = shape_to_nat_seq(rem_preprod@);
                assert(find_min_positive(rem_d).is_none());
                // left_inverse_build: shape nonempty → find_min_positive is None → empty
                assert(rem_s.len() > 0);
                assert(left_inverse_build(rem_s, rem_d, rem_p, acc_size as nat)
                    == LayoutSpec { shape: seq![], stride: seq![] });
            }
            done = true;
        } else {
            let d = rem_stride[idx];
            let m = rem_shape[idx];
            let pp_val = rem_preprod[idx];

            proof {
                assert(d > 0);
                assert(d >= acc_size as int);
            }

            let gap: u64 = (d as u64) / acc_size;

            proof {
                let du = d as u64;
                assert(du >= acc_size);
                assert(acc_size > 0);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(du as int, acc_size as int);
                vstd::arithmetic::div_mod::lemma_mod_bound(du as int, acc_size as int);
                assert(du as int == (acc_size as int) * (gap as int) + (du as int) % (acc_size as int));
                if gap == 0 {
                    assert((acc_size as int) * 0int == 0int);
                    assert((du as int) == (du as int) % (acc_size as int));
                    assert((du as int) < (acc_size as int));
                    assert(false);
                }
                assert(gap >= 1);
                assert(pp_val as nat <= i64::MAX as nat);
            }

            let ghost old_rem_stride = rem_stride@;
            let ghost old_rem_shape = rem_shape@;
            let ghost old_rem_preprod = rem_preprod@;
            let ghost old_acc_size = acc_size;
            let ghost old_result_shape = result_shape@;
            let ghost old_result_stride = result_stride@;

            proof {
                // Prove acc_size * gap <= d
                let du = d as u64;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(du as int, acc_size as int);
                assert(acc_size as nat * gap as nat <= du as nat);

                // Step 1: find_min_positive correspondence
                crate::proof::inverse_lemmas::lemma_find_min_positive_correspondence(
                    old_rem_stride, idx);
                let rem_s = shape_to_nat_seq(old_rem_shape);
                let rem_d = strides_to_int_seq(old_rem_stride);
                let rem_p = shape_to_nat_seq(old_rem_preprod);
                assert(find_min_positive(rem_d) == Some(idx as nat));

                // Step 2: Unfold left_inverse_build one level
                let old_rem_build = left_inverse_build(
                    rem_s, rem_d, rem_p, old_acc_size as nat);
                let spec_d = rem_d[idx as int] as nat;
                let m_spec = rem_s[idx as int];
                let pp_spec = rem_p[idx as int];
                let spec_gap = spec_d / (old_acc_size as nat);
                assert(m_spec == m as nat);
                assert(pp_spec == pp_val as nat);
                assert(spec_d == d as nat);
                assert(spec_gap == gap as nat);
            }

            if rem_shape.len() == 1 {
                // Last mode: emit gap and final shape
                result_shape.push(gap);
                result_stride.push(pp_val as i64);
                result_shape.push(m);
                proof {
                    assert(m > 0u64);
                    assert(gap > 0u64);
                }
                done = true;
            } else {
                result_shape.push(gap);
                result_stride.push(pp_val as i64);
                proof { assert(gap > 0u64); }
                acc_size = acc_size * gap;
            }

            rem_shape = copy_except_u64(&rem_shape, idx);
            rem_stride = copy_except_i64(&rem_stride, idx);
            let old_pp = rem_preprod;
            rem_preprod = copy_except_u64(&old_pp, idx);

            proof {
                // Maintain strides >= acc_size
                assert(acc_size as int <= d as int);
                assert forall|j: int| 0 <= j < rem_stride@.len() && rem_stride@[j] > 0
                    implies rem_stride@[j] >= acc_size as int
                by {
                    let orig_j = if j < idx as int { j } else { j + 1 };
                    assert(rem_stride@[j] == old_rem_stride[orig_j]);
                    assert(old_rem_stride[orig_j] > 0);
                    assert(d <= old_rem_stride[orig_j]);
                };

                // Maintain rem_shape entries > 0
                assert forall|j: int| 0 <= j < rem_shape@.len()
                    implies #[trigger] rem_shape@[j] > 0u64
                by {
                    if j < idx as int { assert(rem_shape@[j] == old_rem_shape[j]); }
                    else { assert(rem_shape@[j] == old_rem_shape[j + 1]); }
                };

                // Maintain preprod bounds
                assert forall|j: int| 0 <= j < rem_preprod@.len()
                    implies (rem_preprod@[j] as nat) <= i64::MAX as nat
                by {
                    if j < idx as int { assert(rem_preprod@[j] == old_pp@[j]); }
                    else { assert(rem_preprod@[j] == old_pp@[j + 1]); }
                };

                // Ghost correspondence: connect new rem_* with remove_at
                let rem_s = shape_to_nat_seq(old_rem_shape);
                let rem_d = strides_to_int_seq(old_rem_stride);
                let rem_p = shape_to_nat_seq(old_rem_preprod);

                assert(rem_shape@ =~= old_rem_shape.take(idx as int).add(
                    old_rem_shape.skip(idx as int + 1)));
                crate::proof::inverse_lemmas::lemma_remove_at_nat_correspondence(
                    old_rem_shape, idx as int);
                assert(shape_to_nat_seq(rem_shape@) =~= remove_at_nat(rem_s, idx as int));

                assert(rem_stride@ =~= old_rem_stride.take(idx as int).add(
                    old_rem_stride.skip(idx as int + 1)));
                crate::proof::inverse_lemmas::lemma_remove_at_int_correspondence(
                    old_rem_stride, idx as int);
                assert(strides_to_int_seq(rem_stride@) =~= remove_at_int(rem_d, idx as int));

                assert(rem_preprod@ =~= old_rem_preprod.take(idx as int).add(
                    old_rem_preprod.skip(idx as int + 1)));
                crate::proof::inverse_lemmas::lemma_remove_at_nat_correspondence(
                    old_rem_preprod, idx as int);
                assert(shape_to_nat_seq(rem_preprod@) =~= remove_at_nat(rem_p, idx as int));

                // Unfolded spec values
                let m_spec = rem_s[idx as int];
                let pp_spec = rem_p[idx as int];
                let spec_gap = (rem_d[idx as int] as nat) / (old_acc_size as nat);
                assert(m_spec == m as nat);
                assert(pp_spec == pp_val as nat);
                assert(spec_gap == gap as nat);

                let old_rem_build = left_inverse_build(
                    rem_s, rem_d, rem_p, old_acc_size as nat);

                if old_rem_shape.len() == 1 {
                    // Last mode: spec gives {[gap, m], [pp]}
                    assert(old_rem_build.shape =~= seq![spec_gap, m_spec]);
                    assert(old_rem_build.stride =~= seq![pp_spec as int]);

                    // rem is now empty → left_inverse_build returns empty
                    assert(shape_to_nat_seq(rem_shape@).len() == 0);
                    let new_rem_build = left_inverse_build(
                        shape_to_nat_seq(rem_shape@),
                        strides_to_int_seq(rem_stride@),
                        shape_to_nat_seq(rem_preprod@),
                        acc_size as nat,
                    );
                    assert(new_rem_build == LayoutSpec { shape: seq![], stride: seq![] });

                    // result_shape = old ++ [gap, m], result_stride = old ++ [pp_val]
                    assert(pp_val as nat <= i64::MAX as nat);
                    assert((pp_val as i64) as int == pp_val as int);
                    assert(pp_spec as int == pp_val as int);

                    // shape correspondence: full_raw.shape =~= nat(old_res).add([gap, m])
                    assert(shape_to_nat_seq(result_shape@) =~=
                        shape_to_nat_seq(old_result_shape).add(seq![spec_gap, m_spec]));
                    // full_raw.shape =~= nat(old_res).add(old_rem.shape)
                    //                =~= nat(old_res).add([gap, m])
                    //                =~= nat(new_res)
                    //                =~= nat(new_res).add([])
                    assert(full_raw_spec.shape =~=
                        shape_to_nat_seq(result_shape@).add(new_rem_build.shape));

                    // stride correspondence
                    assert(strides_to_int_seq(result_stride@) =~=
                        strides_to_int_seq(old_result_stride).add(seq![pp_spec as int]));
                    assert(full_raw_spec.stride =~=
                        strides_to_int_seq(result_stride@).add(new_rem_build.stride));
                } else {
                    // Non-last mode: spec gives {[gap] ++ rest.shape, [pp] ++ rest.stride}
                    let rest = left_inverse_build(
                        remove_at_nat(rem_s, idx as int),
                        remove_at_int(rem_d, idx as int),
                        remove_at_nat(rem_p, idx as int),
                        (old_acc_size as nat) * spec_gap,
                    );
                    assert(old_rem_build.shape =~= seq![spec_gap].add(rest.shape));
                    assert(old_rem_build.stride =~= seq![pp_spec as int].add(rest.stride));

                    // acc_size updated: acc_size = old_acc * gap
                    assert(acc_size as nat == (old_acc_size as nat) * (gap as nat));
                    vstd::arithmetic::mul::lemma_mul_is_commutative(
                        old_acc_size as int, spec_gap as int);
                    assert(acc_size as nat == spec_gap * (old_acc_size as nat));
                    assert(acc_size as nat == (old_acc_size as nat) * spec_gap);

                    let new_rem_build = left_inverse_build(
                        shape_to_nat_seq(rem_shape@),
                        strides_to_int_seq(rem_stride@),
                        shape_to_nat_seq(rem_preprod@),
                        acc_size as nat,
                    );
                    assert(new_rem_build == rest);

                    // Shape: Seq::add associativity
                    assert(pp_val as nat <= i64::MAX as nat);
                    assert((pp_val as i64) as int == pp_val as int);
                    assert(pp_spec as int == pp_val as int);

                    assert(shape_to_nat_seq(result_shape@) =~=
                        shape_to_nat_seq(old_result_shape).add(seq![spec_gap]));
                    assert(shape_to_nat_seq(old_result_shape).add(
                        seq![spec_gap].add(rest.shape))
                        =~= shape_to_nat_seq(old_result_shape).add(
                            seq![spec_gap]).add(rest.shape));
                    assert(full_raw_spec.shape =~=
                        shape_to_nat_seq(result_shape@).add(new_rem_build.shape));

                    // Stride: Seq::add associativity
                    assert(strides_to_int_seq(result_stride@) =~=
                        strides_to_int_seq(old_result_stride).add(seq![pp_spec as int]));
                    assert(strides_to_int_seq(old_result_stride).add(
                        seq![pp_spec as int].add(rest.stride))
                        =~= strides_to_int_seq(old_result_stride).add(
                            seq![pp_spec as int]).add(rest.stride));
                    assert(full_raw_spec.stride =~=
                        strides_to_int_seq(result_stride@).add(new_rem_build.stride));
                }
            }
        }
    }

    // Step 4: Prepend stride 0 for the initial gap mode
    let mut final_stride: Vec<i64> = Vec::new();
    final_stride.push(0i64);
    i = 0;
    while i < result_stride.len()
        invariant
            0 <= i <= result_stride@.len(),
            final_stride@.len() == i + 1,
            final_stride@[0] == 0i64,
            forall|j: int| 0 < j && j <= i as int ==> final_stride@[j] == result_stride@[j - 1],
        decreases result_stride.len() - i,
    {
        final_stride.push(result_stride[i]);
        i = i + 1;
    }

    // Step 5: Construct raw pre-coalesce layout
    // The spec left_inverse is: coalesce(LayoutSpec { shape: raw.shape, stride: [0] ++ raw.stride })
    // where raw = left_inverse_build(...)
    // We build the raw layout, then call coalesce_exec.

    proof {
        crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&layout@);

        // After loop: remaining build is empty
        let rem_build = left_inverse_build(
            shape_to_nat_seq(rem_shape@),
            strides_to_int_seq(rem_stride@),
            shape_to_nat_seq(rem_preprod@),
            acc_size as nat,
        );
        if rem_shape@.len() == 0 {
            assert(shape_to_nat_seq(rem_shape@).len() == 0);
            assert(rem_build == LayoutSpec { shape: seq![], stride: seq![] });
        }
        assert(rem_build.shape.len() == 0);
        assert(rem_build.stride.len() == 0);

        // full_raw_spec.shape =~= result_shape, full_raw_spec.stride =~= result_stride
        assert(full_raw_spec.shape =~= shape_to_nat_seq(result_shape@));
        assert(full_raw_spec.stride =~= strides_to_int_seq(result_stride@));

        // Build the spec pre-coalesce layout
        let c = layout@;
        let spec_pp = shape_prefix_products(c.shape);
        crate::proof::inverse_lemmas::lemma_prefix_products_len(c.shape);
        let spec_preprod = spec_pp.take(c.shape.len() as int);
        let raw_spec = left_inverse_build(c.shape, c.stride, spec_preprod, 1);
        assert(raw_spec == full_raw_spec);

        let pre_coalesce = LayoutSpec {
            shape: raw_spec.shape,
            stride: seq![0int].add(raw_spec.stride),
        };

        // Assume 1 eliminated: shape correspondence
        assert(shape_to_nat_seq(result_shape@) =~= pre_coalesce.shape);

        // Assume 2 eliminated: stride correspondence
        // final_stride = [0] ++ result_stride
        // strides_to_int_seq(final_stride@) =~= [0] ++ strides_to_int_seq(result_stride@)
        //                                    =~= [0] ++ full_raw_spec.stride
        //                                    =~= pre_coalesce.stride
        assert(strides_to_int_seq(final_stride@) =~= pre_coalesce.stride) by {
            assert(final_stride@.len() == result_stride@.len() + 1);
            assert(strides_to_int_seq(final_stride@).len() == final_stride@.len());
            assert(pre_coalesce.stride.len() == 1 + raw_spec.stride.len());
            // Element 0
            assert(strides_to_int_seq(final_stride@)[0] == (final_stride@[0] as int));
            assert(final_stride@[0] == 0i64);
            assert(pre_coalesce.stride[0] == 0int);
            // Elements 1..
            assert forall|j: int| 0 < j && j < final_stride@.len() as int
                implies strides_to_int_seq(final_stride@)[j]
                    == pre_coalesce.stride[j]
            by {
                assert(final_stride@[j] == result_stride@[j - 1]);
                assert(strides_to_int_seq(final_stride@)[j] == (final_stride@[j] as int));
                assert(strides_to_int_seq(result_stride@)[j - 1]
                    == (result_stride@[j - 1] as int));
                assert(full_raw_spec.stride[j - 1]
                    == strides_to_int_seq(result_stride@)[j - 1]);
                assert(pre_coalesce.stride[j] == raw_spec.stride[j - 1]);
            };
        };

        // pre_coalesce validity: all strides positive → build gives shape.len == stride.len + 1
        // First, establish that the coalesced layout (== layout, since fully coalesced)
        // has all positive strides and satisfies build preconditions
        assert(c.valid());
        assert forall|j: int| 0 <= j < c.stride.len() implies c.stride[j] > 0
        by {
            assert(c == layout@);
            assert(layout@.stride[j] > 0);
        };

        crate::proof::inverse_lemmas::lemma_left_inverse_build_positive_strides(
            c.shape, c.stride, spec_preprod, 1);

        if c.shape.len() > 0 {
            assert(raw_spec.shape.len() == raw_spec.stride.len() + 1);
        } else {
            // Empty layout: raw_spec is empty, pre_coalesce = {[], [0]}
            // But layout has shape.len == stride.len == 0, meaning empty layout.
            // shape_valid requires shape entries > 0, which is vacuously true for empty.
            // But layout.valid() requires shape.len == stride.len, which is 0 == 0. OK.
            // All strides > 0 is vacuously true. raw_spec is empty.
            assert(raw_spec.shape.len() == 0 && raw_spec.stride.len() == 0);
        }

        // shape.len > 0 (from precondition) → build gives shape.len == stride.len + 1
        assert(c.shape.len() > 0) by { assert(c == layout@); };
        assert(raw_spec.shape.len() == raw_spec.stride.len() + 1);

        // pre_coalesce validity follows from the length relationship
        crate::proof::inverse_lemmas::lemma_left_inverse_pre_coalesce_valid(&layout@);
        assert(pre_coalesce.valid());

        // Size bound: coalesce preserves size
        if pre_coalesce.valid() {
            crate::proof::shape_lemmas::lemma_shape_size_positive(pre_coalesce.shape);
            crate::proof::coalesce_lemmas::lemma_coalesce(pre_coalesce, 0);
            assert(pre_coalesce.size() == shape_size(pre_coalesce.shape));
            assert(coalesce(pre_coalesce).size() == pre_coalesce.size());
            assert(left_inverse(&layout@) == coalesce(pre_coalesce));
            assert(shape_size(left_inverse(&layout@).shape) <= u64::MAX as nat);
            assert(pre_coalesce.size() <= u64::MAX as nat);
        }
    }

    let raw_layout = RuntimeLayout {
        shape: result_shape,
        stride: final_stride,
        model: Ghost({
            let c = *layout.model.borrow();
            let spec_pp = shape_prefix_products(c.shape);
            let spec_preprod = spec_pp.take(c.shape.len() as int);
            let raw_spec = left_inverse_build(c.shape, c.stride, spec_preprod, 1);
            LayoutSpec {
                shape: raw_spec.shape,
                stride: seq![0int].add(raw_spec.stride),
            }
        }),
    };

    // Step 6: Coalesce the raw result
    let final_result = super::ops::coalesce_exec(raw_layout);

    proof {
        // coalesce_exec ensures: final_result@ == coalesce(raw_layout@)
        // raw_layout@ == pre_coalesce (by construction)
        // coalesce(pre_coalesce) == left_inverse(&layout@) by definition
        crate::proof::inverse_lemmas::lemma_fully_coalesced_identity(&layout@);
    }

    final_result
}

} // verus!
