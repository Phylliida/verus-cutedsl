/// Runtime implementations of scan/reduce primitives.
///
/// Hillis-Steele inclusive scan: O(n log n) work, O(log n) depth.
/// Tree reduce: derived from Hillis-Steele (take last element).
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::summation::*;
use crate::scan::*;
use crate::scan_tree::tree_reduce_state;
use crate::scan_blelloch::*;
use crate::swizzle::pow2;
use crate::proof::scan_lemmas::*;

verus! {

// ============================================================
// ExecRing trait: bridges exec-level operations to spec-level Ring
// ============================================================

/// Trait for exec-level ring elements that map to a spec-level Ring type.
///
/// Provides the three operations needed by scan algorithms:
/// - `exec_add`: addition with overflow guard via `is_representable`
/// - `exec_zero`: the additive identity
/// - `exec_clone`: copy/clone (needed since Verus doesn't auto-clone tracked types)
///
/// Overflow handling uses `is_representable`: a predicate on spec values R
/// that says whether a value can be stored as a T. The `exec_add` requires
/// both operand views and their sum view to be representable.
pub trait ExecRing<R: Ring>: Sized {
    /// View: map an exec element to its spec counterpart.
    spec fn view(&self) -> R;

    /// Whether a spec value can be represented as this exec type.
    /// For i64: i64::MIN <= v <= i64::MAX. For Rational: always true.
    spec fn is_representable(v: R) -> bool;

    /// is_representable respects eqv: if a.eqv(b) and is_representable(a), then is_representable(b).
    proof fn lemma_representable_congruence(a: R, b: R)
        requires a.eqv(b), Self::is_representable(a),
        ensures Self::is_representable(b);

    /// exec addition. Requires operands and result to be representable.
    fn exec_add(&self, other: &Self) -> (result: Self)
        requires
            Self::is_representable(self.view()),
            Self::is_representable(other.view()),
            Self::is_representable(self.view().add(other.view())),
        ensures result.view().eqv(self.view().add(other.view()));

    /// exec zero.
    fn exec_zero() -> (result: Self)
        ensures result.view().eqv(R::zero());

    /// exec clone.
    fn exec_clone(&self) -> (result: Self)
        ensures result.view().eqv(self.view());
}

/// Partial sum of viewed data.
pub open spec fn partial_sum_generic<T: ExecRing<R>, R: Ring>(data: Seq<T>, lo: int, hi: int) -> R {
    sum::<R>(|j: int| data[j].view(), lo, hi)
}

/// All partial sums of data (viewed through ExecRing) are representable.
pub open spec fn all_partial_sums_representable<T: ExecRing<R>, R: Ring>(data: Seq<T>) -> bool {
    forall|lo: int, hi: int| 0 <= lo <= hi <= data.len() ==>
        T::is_representable(#[trigger] partial_sum_generic::<T, R>(data, lo, hi))
}

// ============================================================
// i64 implementation of ExecRing<int>
// ============================================================

impl ExecRing<int> for i64 {
    #[verifier::inline]
    open spec fn view(&self) -> int {
        *self as int
    }

    #[verifier::inline]
    open spec fn is_representable(v: int) -> bool {
        i64::MIN as int <= v && v <= i64::MAX as int
    }

    proof fn lemma_representable_congruence(a: int, b: int)
    {
        // For int: eqv is ==, so a == b. is_representable(a) implies is_representable(b).
    }

    fn exec_add(&self, other: &Self) -> (result: Self)
    {
        // is_representable(self + other) means i64::MIN <= self+other <= i64::MAX
        // a.add(b) == a + b for int, so this is safe
        *self + *other
    }

    fn exec_zero() -> (result: Self)
    {
        0i64
    }

    fn exec_clone(&self) -> (result: Self)
    {
        *self
    }
}

/// Helper: partial_sum and partial_sum_generic are equal for i64/int.
/// Both are sum over closures that compute data[j] as int, but Z3 treats the closures
/// as distinct function symbols. Bridge by induction on sum's recursion.
pub proof fn lemma_partial_sums_equal(data: Seq<i64>, lo: int, hi: int)
    requires 0 <= lo, hi <= data.len(),
    ensures partial_sum(data, lo, hi) == partial_sum_generic::<i64, int>(data, lo, hi),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        // Both return Ring::zero() = 0
    } else {
        lemma_partial_sums_equal(data, lo + 1, hi);
        // IH: sum(cls_PS, lo+1, hi) == sum(cls_PSG, lo+1, hi)
        // Unfolding sum one step: f(lo) + sum(f, lo+1, hi) on each side
        // cls_PS(lo) = data[lo] as int, cls_PSG(lo) = data[lo].view() = data[lo] as int
    }
}

/// Bridge: all_partial_sums_bounded ==> all_partial_sums_representable for i64.
pub proof fn lemma_bounded_implies_representable(data: Seq<i64>)
    requires all_partial_sums_bounded(data),
    ensures all_partial_sums_representable::<i64, int>(data),
{
    assert forall|lo: int, hi: int| 0 <= lo <= hi <= data.len() implies
        <i64 as ExecRing<int>>::is_representable(
            #[trigger] partial_sum_generic::<i64, int>(data, lo, hi)
        )
    by {
        lemma_partial_sums_equal(data, lo, hi);
        // Now Z3 knows partial_sum == partial_sum_generic, and all_partial_sums_bounded
        // gives i64 range bounds on partial_sum.
    }
}

/// Compute ceil(log2(n)) at runtime.
pub fn log2_ceil_exec(n: u64) -> (result: u64)
    requires n > 0,
    ensures result as nat == log2_ceil(n as nat),
    decreases n,
{
    if n <= 1 {
        return 0;
    }
    // ceil(n/2) = n/2 + n%2, avoids overflow unlike (n+1)/2
    let half: u64 = n / 2 + n % 2;
    proof {
        lemma_half_ceil_bounds(n as nat);
        assert(half as nat == ((n as nat + 1) / 2) as nat);
    }
    let r = log2_ceil_exec(half);
    proof {
        if half as nat >= 2 {
            lemma_log2_ceil_lt(half as nat);
        }
        // r < n, so 1 + r doesn't overflow u64
    }
    1 + r
}

// ============================================================
// Generic Hillis-Steele specs and lemmas
// ============================================================

/// Generic hs_value: what element i should hold after `level` levels.
pub open spec fn hs_value_generic<T: ExecRing<R>, R: Ring>(data: Seq<T>, i: int, level: nat) -> R {
    let lo = if i + 1 - pow2(level) as int > 0 { i + 1 - pow2(level) as int } else { 0int };
    sum::<R>(|j: int| data[j].view(), lo, i + 1)
}

/// Generic hs_value addition lemma.
proof fn lemma_hs_addition_generic<T: ExecRing<R>, R: Ring>(data: Seq<T>, i: int, d: nat, n: nat)
    requires
        n as int == data.len(),
        0 <= i < n as int,
        i >= pow2(d) as int,
    ensures
        hs_value_generic::<T, R>(data, i, d).add(
            hs_value_generic::<T, R>(data, i - pow2(d) as int, d)
        ).eqv(hs_value_generic::<T, R>(data, i, (d + 1) as nat)),
{
    let stride = pow2(d);
    let partner = i - stride as int;
    let prev_lo = i + 1 - stride as int;
    let partner_lo = if partner + 1 - stride as int > 0 { partner + 1 - stride as int } else { 0int };
    let next_lo = if i + 1 - pow2((d + 1) as nat) as int > 0 { i + 1 - pow2((d + 1) as nat) as int } else { 0int };

    assert(pow2((d + 1) as nat) == 2 * pow2(d));
    assert(partner + 1 == prev_lo);
    assert(partner_lo == next_lo);
    assert(next_lo <= prev_lo);

    // sum(f, next_lo, i+1) = sum(f, next_lo, prev_lo) + sum(f, prev_lo, i+1)
    //                       = hs(partner, d) + hs(i, d)
    lemma_sum_split::<R>(|j: int| data[j].view(), next_lo, prev_lo, i + 1);
    // sum_split gives: sum(f, next_lo, i+1).eqv(sum(f, next_lo, prev_lo).add(sum(f, prev_lo, i+1)))
    // which is: hs(i, d+1).eqv(hs(partner, d).add(hs(i, d)))
    // We need: hs(i, d).add(hs(partner, d)).eqv(hs(i, d+1))
    // By commutativity: a.add(b).eqv(b.add(a))
    R::axiom_add_commutative(
        hs_value_generic::<T, R>(data, i, d),
        hs_value_generic::<T, R>(data, partner, d),
    );
    // Now chain: hs(i,d).add(hs(partner,d)).eqv(hs(partner,d).add(hs(i,d)))
    //        and hs(partner,d).add(hs(i,d)).eqv(hs(i,d+1))
    R::axiom_eqv_symmetric(
        hs_value_generic::<T, R>(data, i, (d + 1) as nat),
        hs_value_generic::<T, R>(data, partner, d).add(
            hs_value_generic::<T, R>(data, i, d)
        ),
    );
    R::axiom_eqv_transitive(
        hs_value_generic::<T, R>(data, i, d).add(
            hs_value_generic::<T, R>(data, partner, d)
        ),
        hs_value_generic::<T, R>(data, partner, d).add(
            hs_value_generic::<T, R>(data, i, d)
        ),
        hs_value_generic::<T, R>(data, i, (d + 1) as nat),
    );
}

/// Generic hs_value is unchanged when i < stride.
proof fn lemma_hs_no_change_generic<T: ExecRing<R>, R: Ring>(data: Seq<T>, i: int, d: nat, n: nat)
    requires
        n as int == data.len(),
        0 <= i < n as int,
        i < pow2(d) as int,
    ensures
        hs_value_generic::<T, R>(data, i, d).eqv(
            hs_value_generic::<T, R>(data, i, (d + 1) as nat)
        ),
{
    assert(pow2((d + 1) as nat) == 2 * pow2(d));
    // Both have lo = 0, so both = sum(f, 0, i+1). Reflexive.
    R::axiom_eqv_reflexive(hs_value_generic::<T, R>(data, i, d));
}

/// Generic hs_value at sufficient level equals inclusive_scan.
proof fn lemma_hs_equals_inclusive_scan_generic<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, i: int, level: nat,
)
    requires
        0 <= i < data.len() as int,
        pow2(level) >= data.len(),
    ensures
        hs_value_generic::<T, R>(data, i, level).eqv(
            inclusive_scan::<R>(Seq::new(data.len(), |j: int| data[j].view()))[i]
        ),
{
    // pow2(level) >= n > i+1, so lo = 0
    // hs_value = sum(|j| data[j].view(), 0, i+1)
    // inclusive_scan(view_seq)[i] = sum(|j| view_seq[j], 0, i+1)
    // view_seq[j] = data[j].view(), so congruence gives equality
    let view_seq = Seq::new(data.len(), |j: int| data[j].view());
    assert forall|j: int| 0 <= j < data.len() as int implies
        view_seq[j].eqv(data[j].view()) by {
        R::axiom_eqv_reflexive(data[j].view());
    }
    lemma_sum_congruence::<R>(
        |j: int| data[j].view(),
        |j: int| view_seq[j],
        0, i + 1,
    );
}

/// Generic Hillis-Steele inclusive scan.
pub fn hillis_steele_generic_exec<T: ExecRing<R>, R: Ring>(
    data: &Vec<T>, n: u64,
) -> (output: Vec<T>)
    requires
        data@.len() == n as nat,
        n > 0,
        all_partial_sums_representable::<T, R>(data@),
        n <= u64::MAX / 2,
    ensures
        output@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            output@[i].view().eqv(
                inclusive_scan::<R>(Seq::new(data@.len(), |j: int| data@[j].view()))[i]
            ),
        // Second ensures: direct partial_sum_generic form, avoids closure matching issues for callers
        forall|i: int| 0 <= i < n as int ==>
            output@[i].view().eqv(
                partial_sum_generic::<T, R>(data@, 0, i + 1)
            ),
{
    let levels = log2_ceil_exec(n);
    let data_len = data.len();

    // Initialize current buffer from data
    let mut current: Vec<T> = Vec::new();
    let mut idx: u64 = 0;
    while idx < n
        invariant
            idx <= n,
            current@.len() == idx as nat,
            data@.len() == n as nat,
            n as int == data_len as int,
            forall|j: int| 0 <= j < idx as int ==> current@[j].view().eqv(data@[j].view()),
        decreases n - idx,
    {
        let clone = data[idx as usize].exec_clone();
        current.push(clone);
        idx = idx + 1;
    }

    proof {
        // Base case: at level 0, current[i].view().eqv(data[i].view())
        //   = hs_value_generic(data, i, 0)  (which is sum(f, i, i+1) = data[i].view())
        assert forall|i: int| 0 <= i < n as int implies
            current@[i].view().eqv(
                #[trigger] hs_value_generic::<T, R>(data@, i, 0)
            )
        by {
            // hs_value_generic(data, i, 0) = sum(f, i, i+1) = data[i].view()
            lemma_sum_single::<R>(|j: int| data@[j].view(), i);
            // sum_single: sum(f, i, i+1).eqv(f(i)) = data[i].view()
            // current[i].view().eqv(data[i].view()) from invariant
            // By transitivity: current[i].view().eqv(hs_value(i, 0))
            R::axiom_eqv_symmetric(
                sum::<R>(|j: int| data@[j].view(), i, i + 1),
                data@[i].view(),
            );
            R::axiom_eqv_transitive(
                current@[i].view(),
                data@[i].view(),
                hs_value_generic::<T, R>(data@, i, 0),
            );
        }
    }

    // Apply Hillis-Steele levels
    let mut d: u64 = 0;
    let mut stride: u64 = 1;
    while d < levels
        invariant
            d <= levels,
            stride as nat == pow2(d as nat),
            current@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 0,
            n <= u64::MAX / 2,
            n as int == data_len as int,
            data@.len() == n as nat,
            all_partial_sums_representable::<T, R>(data@),
            forall|i: int| 0 <= i < n as int ==>
                current@[i].view().eqv(
                    #[trigger] hs_value_generic::<T, R>(data@, i, d as nat)
                ),
        decreases levels - d,
    {
        proof {
            if n as nat > 1 {
                lemma_pow2_lt_for_sub_levels(n as nat, d as nat);
            } else {
                assert(false);
            }
        }

        let mut next: Vec<T> = Vec::new();
        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                next@.len() == i as nat,
                current@.len() == n as nat,
                stride as nat == pow2(d as nat),
                stride < n,
                d < levels,
                levels as nat == log2_ceil(n as nat),
                n > 0,
                n <= u64::MAX / 2,
                n as int == data_len as int,
                data@.len() == n as nat,
                all_partial_sums_representable::<T, R>(data@),
                forall|k: int| 0 <= k < n as int ==>
                    current@[k].view().eqv(
                        #[trigger] hs_value_generic::<T, R>(data@, k, d as nat)
                    ),
                forall|k: int| 0 <= k < i as int ==>
                    next@[k].view().eqv(
                        #[trigger] hs_value_generic::<T, R>(data@, k, (d + 1) as nat)
                    ),
            decreases n - i,
        {
            if i >= stride {
                let partner = (i - stride) as usize;

                proof {
                    let ghost ii = i as int;
                    let ghost pi = ii - stride as int;
                    let ghost hs_i = hs_value_generic::<T, R>(data@, ii, d as nat);
                    let ghost hs_p = hs_value_generic::<T, R>(data@, pi, d as nat);
                    let ghost hs_next = hs_value_generic::<T, R>(data@, ii, (d + 1) as nat);

                    // hs(i,d).add(hs(partner,d)).eqv(hs(i,d+1))
                    lemma_hs_addition_generic::<T, R>(data@, ii, d as nat, n as nat);

                    // hs_i, hs_p, hs_next are all partial sums, hence representable
                    // Trigger all_partial_sums_representable by referencing partial_sum_generic
                    let hs_i_lo = if ii + 1 - pow2(d as nat) as int > 0 {
                        ii + 1 - pow2(d as nat) as int
                    } else { 0int };
                    let hs_p_lo = if pi + 1 - pow2(d as nat) as int > 0 {
                        pi + 1 - pow2(d as nat) as int
                    } else { 0int };
                    let hs_next_lo = if ii + 1 - pow2((d + 1) as nat) as int > 0 {
                        ii + 1 - pow2((d + 1) as nat) as int
                    } else { 0int };
                    assert(0 <= hs_i_lo && ii + 1 <= n as int);
                    assert(0 <= hs_p_lo && pi + 1 <= n as int);
                    assert(0 <= hs_next_lo && ii + 1 <= n as int);
                    // Bridge hs_value to partial_sum_generic for trigger
                    assert(hs_i.eqv(partial_sum_generic::<T, R>(data@, hs_i_lo, ii + 1))) by {
                        R::axiom_eqv_reflexive(hs_i);
                    }
                    assert(hs_p.eqv(partial_sum_generic::<T, R>(data@, hs_p_lo, pi + 1))) by {
                        R::axiom_eqv_reflexive(hs_p);
                    }
                    assert(hs_next.eqv(partial_sum_generic::<T, R>(data@, hs_next_lo, ii + 1))) by {
                        R::axiom_eqv_reflexive(hs_next);
                    }
                    // Now Z3 knows is_representable for hs_i, hs_p, hs_next via trigger

                    // current views are eqv to hs values, bridge to is_representable
                    R::axiom_eqv_symmetric(current@[ii].view(), hs_i);
                    T::lemma_representable_congruence(hs_i, current@[ii].view());
                    R::axiom_eqv_symmetric(current@[pi].view(), hs_p);
                    T::lemma_representable_congruence(hs_p, current@[pi].view());

                    // current[i].view().add(current[partner].view()) is eqv to hs_i.add(hs_p)
                    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
                    lemma_add_congruence::<R>(
                        current@[ii].view(), hs_i,
                        current@[pi].view(), hs_p,
                    );
                    // hs_i.add(hs_p).eqv(hs_next)
                    R::axiom_eqv_transitive(
                        current@[ii].view().add(current@[pi].view()),
                        hs_i.add(hs_p),
                        hs_next,
                    );
                    // is_representable(current[i].view().add(current[partner].view()))
                    R::axiom_eqv_symmetric(
                        current@[ii].view().add(current@[pi].view()),
                        hs_next,
                    );
                    T::lemma_representable_congruence(hs_next, current@[ii].view().add(current@[pi].view()));
                }

                let val = current[i as usize].exec_add(&current[partner]);
                proof {
                    let ghost ii = i as int;
                    let ghost hs_next = hs_value_generic::<T, R>(data@, ii, (d + 1) as nat);
                    // val.view().eqv(current[i].view().add(current[partner].view()))
                    // current[i].view().add(current[partner].view()).eqv(hs_next)
                    R::axiom_eqv_transitive(
                        val.view(),
                        current@[ii].view().add(current@[(ii - stride as int) as int].view()),
                        hs_next,
                    );
                }
                next.push(val);
            } else {
                let clone = current[i as usize].exec_clone();
                next.push(clone);

                proof {
                    let ghost ii = i as int;
                    lemma_hs_no_change_generic::<T, R>(data@, ii, d as nat, n as nat);
                    // hs(i,d).eqv(hs(i,d+1))
                    // current[i].view().eqv(hs(i,d))
                    // clone.view().eqv(current[i].view())
                    R::axiom_eqv_transitive(
                        clone.view(),
                        current@[ii].view(),
                        hs_value_generic::<T, R>(data@, ii, d as nat),
                    );
                    R::axiom_eqv_transitive(
                        clone.view(),
                        hs_value_generic::<T, R>(data@, ii, d as nat),
                        hs_value_generic::<T, R>(data@, ii, (d + 1) as nat),
                    );
                }
            }

            i = i + 1;
        }

        current = next;

        proof {
            assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
        }

        stride = stride * 2;
        d = d + 1;
    }

    proof {
        lemma_log2_ceil_pow2(n as nat);
        assert forall|i: int| 0 <= i < n as int implies
            current@[i].view().eqv(
                inclusive_scan::<R>(Seq::new(data@.len(), |j: int| data@[j].view()))[i]
            )
            && current@[i].view().eqv(
                partial_sum_generic::<T, R>(data@, 0, i + 1)
            )
        by {
            // current[i].view().eqv(hs(i, levels))
            lemma_hs_equals_inclusive_scan_generic::<T, R>(data@, i, levels as nat);
            // hs(i, levels).eqv(inclusive_scan(view_seq)[i])
            R::axiom_eqv_transitive(
                current@[i].view(),
                hs_value_generic::<T, R>(data@, i, levels as nat),
                inclusive_scan::<R>(Seq::new(data@.len(), |j: int| data@[j].view()))[i],
            );
            // hs(i, levels) = partial_sum_generic(data@, 0, i+1) when pow2(levels) >= n
            // (lo = max(0, i+1-pow2(levels)) = 0 since i < n <= pow2(levels))
            assert(i + 1 - pow2(levels as nat) as int <= 0) by {
                assert(pow2(levels as nat) >= data@.len());
            }
            // Now Z3 sees hs_value_generic(...) = sum(cls, 0, i+1) = partial_sum_generic(...)
            R::axiom_eqv_reflexive(hs_value_generic::<T, R>(data@, i, levels as nat));
            R::axiom_eqv_transitive(
                current@[i].view(),
                hs_value_generic::<T, R>(data@, i, levels as nat),
                partial_sum_generic::<T, R>(data@, 0, i + 1),
            );
        }
    }

    current
}

/// Generic exclusive scan via Hillis-Steele + shift.
/// result[0] = zero, result[i] = inclusive_scan(data)[i-1] for i > 0.
/// O(n log n) work, O(log n) depth. No power-of-2 requirement.
pub fn exclusive_scan_generic_exec<T: ExecRing<R>, R: Ring>(
    data: &Vec<T>, n: u64,
) -> (output: Vec<T>)
    requires
        data@.len() == n as nat,
        n > 0,
        all_partial_sums_representable::<T, R>(data@),
        n <= u64::MAX / 2,
    ensures
        output@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            output@[i].view().eqv(
                exclusive_scan::<R>(Seq::new(data@.len(), |j: int| data@[j].view()))[i]
            ),
{
    let incl = hillis_steele_generic_exec::<T, R>(data, n);
    let ghost view_seq = Seq::new(data@.len(), |j: int| data@[j].view());

    let incl_len = incl.len();

    let mut output: Vec<T> = Vec::new();
    // output[0] = zero
    let z = T::exec_zero();
    proof {
        use crate::proof::scan_lemmas::lemma_exclusive_from_inclusive;
        lemma_exclusive_from_inclusive::<R>(view_seq, 0);
        // exclusive_scan(view_seq)[0] == R::zero()
        // z.view().eqv(R::zero()) from exec_zero ensures
        // R::zero() == exclusive_scan(view_seq)[0]
        R::axiom_eqv_reflexive(exclusive_scan::<R>(view_seq)[0]);
    }
    output.push(z);

    // output[i] = incl[i-1] for i > 0
    let mut i: u64 = 1;
    while i < n
        invariant
            1 <= i <= n,
            output@.len() == i as nat,
            data@.len() == n as nat,
            n > 0,
            n as int == incl_len as int,
            incl@.len() == n as nat,
            view_seq == Seq::new(data@.len(), |j: int| data@[j].view()),
            forall|k: int| 0 <= k < n as int ==>
                incl@[k].view().eqv(inclusive_scan::<R>(view_seq)[k]),
            forall|k: int| 0 <= k < i as int ==>
                output@[k].view().eqv(exclusive_scan::<R>(view_seq)[k]),
        decreases n - i,
    {
        let prev_usize: usize = (i - 1) as usize;
        let clone = incl[prev_usize].exec_clone();
        proof {
            use crate::proof::scan_lemmas::lemma_exclusive_from_inclusive;
            let pi = (i - 1) as int;
            lemma_exclusive_from_inclusive::<R>(view_seq, i as int);
            // clone.view().eqv(incl@[pi].view()) — from exec_clone
            // incl@[pi].view().eqv(inclusive_scan(view_seq)[pi]) — from invariant
            R::axiom_eqv_transitive(
                clone.view(),
                incl@[pi].view(),
                inclusive_scan::<R>(view_seq)[pi],
            );
            // exclusive_scan(view_seq)[i] == inclusive_scan(view_seq)[i-1] (== for spec values)
        }
        output.push(clone);
        i = i + 1;
    }

    output
}

/// Hillis-Steele inclusive scan. Creates a new output Vec.
/// O(n log n) work, O(log n) depth.
pub fn hillis_steele_exec(data: &Vec<i64>, n: u64) -> (output: Vec<i64>)
    requires
        data@.len() == n as nat,
        n > 0,
        all_partial_sums_bounded(data@),
        n <= i64::MAX as u64,
    ensures
        output@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            output@[i] as int == inclusive_scan_int(data@)[i],
{
    proof { lemma_bounded_implies_representable(data@); }
    let result = hillis_steele_generic_exec::<i64, int>(data, n);
    proof {
        // Generic new ensures: result@[i].view().eqv(partial_sum_generic(data@, 0, i+1))
        // For i64/int: view() inlines, eqv is ==, so:
        //   result@[i] as int == partial_sum_generic(data@, 0, i+1)
        // Bridge chain: partial_sum_generic == partial_sum == inclusive_scan_int
        assert forall|i: int| 0 <= i < n as int implies
            result@[i] as int == inclusive_scan_int(data@)[i]
        by {
            // Step 1: partial_sum_generic == partial_sum (by induction on sum)
            lemma_partial_sums_equal(data@, 0, i + 1);
            // Step 2: partial_sum == inclusive_scan_int (by sum_congruence)
            // partial_sum(data@, 0, i+1) uses closure |j| data@[j] as int
            // inclusive_scan_int(data@)[i] uses closure |j| as_int_seq(data@)[j]
            // These are pointwise equal: as_int_seq(data@)[j] == data@[j] as int
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

/// Reduce: sum all elements. Uses Hillis-Steele and returns the last element.
pub fn reduce_exec(data: &Vec<i64>, n: u64) -> (result: i64)
    requires
        data@.len() == n as nat,
        n > 0,
        all_partial_sums_bounded(data@),
        n <= i64::MAX as u64,
    ensures
        result as int == reduce_int(data@, 0, n as int),
{
    let scan = hillis_steele_exec(data, n);
    let data_len = data.len();
    scan[(n - 1) as usize]
}

// ============================================================
// Generic tree reduce specs, lemmas, and exec
// ============================================================

/// Generic tree reduce state: what each position holds after `level` levels.
pub open spec fn tree_reduce_state_generic<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, level: nat,
) -> Seq<R>
    recommends n as int == data.len(),
    decreases level,
{
    if level == 0 {
        Seq::new(n, |i: int| data[i].view())
    } else {
        let prev = tree_reduce_state_generic::<T, R>(data, n, (level - 1) as nat);
        let stride = pow2((level - 1) as nat);
        Seq::new(n, |i: int|
            if (i + 1) % (pow2(level) as int) == 0 && i >= stride as int {
                prev[i].add(prev[(i - stride as int)])
            } else {
                prev[i]
            }
        )
    }
}

/// Generic tree reduce invariant: active positions hold correct sums via eqv.
proof fn lemma_tree_reduce_invariant_all_generic<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, total_levels: nat, level: nat,
)
    requires
        n as int == data.len(), n > 0, is_power_of_2(n),
        pow2(total_levels) == n, level <= total_levels,
    ensures ({
        let state = tree_reduce_state_generic::<T, R>(data, n, level);
        &&& state.len() == n
        &&& forall|i: int| #![trigger state[i]]
            0 <= i < n as int && (i + 1) % (pow2(level) as int) == 0
            ==> state[i].eqv(
                partial_sum_generic::<T, R>(data, i + 1 - pow2(level) as int, i + 1))
    }),
    decreases level,
{
    let state = tree_reduce_state_generic::<T, R>(data, n, level);
    let f = |j: int| data[j].view();
    if level == 0 {
        assert forall|i: int| #![trigger state[i]]
            0 <= i < n as int && (i + 1) % 1 == 0
        implies state[i].eqv(partial_sum_generic::<T, R>(data, i, i + 1))
        by {
            lemma_sum_single::<R>(f, i);
            R::axiom_eqv_symmetric(sum::<R>(f, i, i + 1), f(i));
        }
    } else {
        crate::proof::scan_blelloch_lemmas::lemma_log2_ceil_eq_for_pow2(n, total_levels);
        lemma_tree_reduce_invariant_all_generic::<T, R>(data, n, total_levels, (level - 1) as nat);
        let prev = tree_reduce_state_generic::<T, R>(data, n, (level - 1) as nat);
        let stride = pow2((level - 1) as nat);
        let ns = pow2(level);
        assert(ns == 2 * stride);

        assert forall|i: int| #![trigger state[i]]
            0 <= i < n as int && (i + 1) % (ns as int) == 0
        implies state[i].eqv(partial_sum_generic::<T, R>(data, i + 1 - ns as int, i + 1))
        by {
            crate::proof::swizzle_lemmas::lemma_pow2_positive((level - 1) as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_positive(level);

            // (i+1) % ns == 0 => (i+1) % stride == 0
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, ns as int);
            let q = (i + 1) / (ns as int);
            assert(i + 1 == ns as int * q);
            assert((i + 1) % (stride as int) == 0) by {
                assert(i + 1 == stride as int * (2 * q)) by (nonlinear_arith)
                    requires i + 1 == ns as int * q, ns == 2 * stride;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    i + 1, stride as int, 2 * q, 0
                );
            };
            assert(q >= 1) by (nonlinear_arith)
                requires i + 1 == ns as int * q, ns > 0, i >= 0;
            assert(i >= stride as int) by (nonlinear_arith)
                requires i + 1 == ns as int * q, q >= 1, ns == 2 * stride as int, stride > 0;

            // Partner active at level-1
            let p = i - stride as int;
            assert((p + 1) % (stride as int) == 0) by {
                assert(p + 1 == stride as int * (2 * q - 1)) by (nonlinear_arith)
                    requires i + 1 == ns as int * q, ns == 2 * stride, p == i - stride as int;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    p + 1, stride as int, 2 * q - 1, 0
                );
            };
            assert(0 <= p && p < n as int);

            let si = sum::<R>(f, i + 1 - stride as int, i + 1);
            let sp = sum::<R>(f, p + 1 - stride as int, p + 1);
            assert(p + 1 == i + 1 - stride as int);
            assert(p + 1 - stride as int == i + 1 - ns as int);
            let lo = i + 1 - ns as int;
            assert(lo >= 0) by (nonlinear_arith)
                requires lo == i + 1 - ns as int, i + 1 == ns as int * q, q >= 1, ns > 0;

            // sum_split: sum(f, lo, i+1).eqv(sp.add(si))
            lemma_sum_split::<R>(f, lo, i + 1 - stride as int, i + 1);

            // add_congruence: prev[i].add(prev[p]).eqv(si.add(sp))
            use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
            lemma_add_congruence::<R>(prev[i], si, prev[p], sp);

            // commutativity + transitivity chain
            R::axiom_add_commutative(si, sp);
            R::axiom_eqv_transitive(prev[i].add(prev[p]), si.add(sp), sp.add(si));
            R::axiom_eqv_symmetric(sum::<R>(f, lo, i + 1), sp.add(si));
            R::axiom_eqv_transitive(prev[i].add(prev[p]), sp.add(si), sum::<R>(f, lo, i + 1));
            assert(state[i] == prev[i].add(prev[p]));
        }
    }
}

/// All values in tree_reduce_state_generic are representable.
proof fn lemma_tree_reduce_all_representable<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, total_levels: nat, level: nat,
)
    requires
        data.len() as int == n as int, n > 0, is_power_of_2(n),
        pow2(total_levels) == n, level <= total_levels,
        all_partial_sums_representable::<T, R>(data),
    ensures
        forall|j: int| 0 <= j < n as int ==>
            T::is_representable(
                #[trigger] tree_reduce_state_generic::<T, R>(data, n, level)[j]
            ),
    decreases level,
{
    let state = tree_reduce_state_generic::<T, R>(data, n, level);
    let f = |j: int| data[j].view();
    if level == 0 {
        assert forall|j: int| 0 <= j < n as int
        implies T::is_representable(#[trigger] state[j])
        by {
            lemma_sum_single::<R>(f, j);
            R::axiom_eqv_symmetric(sum::<R>(f, j, j + 1), f(j));
            T::lemma_representable_congruence(
                partial_sum_generic::<T, R>(data, j, j + 1), state[j],
            );
        }
    } else {
        lemma_tree_reduce_all_representable::<T, R>(data, n, total_levels, (level - 1) as nat);
        lemma_tree_reduce_invariant_all_generic::<T, R>(data, n, total_levels, level);
        let stride = pow2((level - 1) as nat);
        assert forall|j: int| 0 <= j < n as int
        implies T::is_representable(#[trigger] state[j])
        by {
            if (j + 1) % (pow2(level) as int) == 0 && j >= stride as int {
                crate::proof::swizzle_lemmas::lemma_pow2_positive(level);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, pow2(level) as int);
                let k = (j + 1) / (pow2(level) as int);
                assert(j + 1 == pow2(level) as int * k);
                assert(k >= 1) by (nonlinear_arith)
                    requires j + 1 == pow2(level) as int * k, pow2(level) > 0, j >= 0;
                let lo = j + 1 - pow2(level) as int;
                assert(lo >= 0) by (nonlinear_arith)
                    requires lo == j + 1 - pow2(level) as int,
                             j + 1 == pow2(level) as int * k, k >= 1, pow2(level) > 0;
                R::axiom_eqv_symmetric(
                    state[j], partial_sum_generic::<T, R>(data, lo, j + 1));
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(data, lo, j + 1), state[j],
                );
            } else {
                // Non-active: state[j] == prev[j] by spec definition
                let prev = tree_reduce_state_generic::<T, R>(
                    data, n, (level - 1) as nat);
                assert(state[j] == prev[j]);
            }
        }
    }
}

/// Generic in-place tree reduce.
pub fn tree_reduce_in_place_generic_exec<T: ExecRing<R>, R: Ring>(
    data: &mut Vec<T>, n: u64, levels: u64,
)
    requires
        old(data)@.len() == n as nat,
        n > 1,
        pow2(levels as nat) == n as nat,
        is_power_of_2(n as nat),
        levels as nat == log2_ceil(n as nat),
        all_partial_sums_representable::<T, R>(old(data)@),
        n <= u64::MAX / 2,
    ensures
        data@.len() == n as nat,
        forall|j: int| 0 <= j < n as int ==>
            data@[j].view().eqv(
                tree_reduce_state_generic::<T, R>(old(data)@, n as nat, levels as nat)[j]
            ),
{
    let ghost original_data = old(data)@;
    let ghost total_levels = levels as nat;
    let data_len = data.len();

    proof {
        assert forall|j: int| 0 <= j < n as int implies
            data@[j].view().eqv(
                tree_reduce_state_generic::<T, R>(original_data, n as nat, 0)[j]
            )
        by {
            R::axiom_eqv_reflexive(data@[j].view());
        }
        lemma_tree_reduce_all_representable::<T, R>(
            original_data, n as nat, total_levels, 0,
        );
        // Bridge: tree_reduce_state_generic at level 0 == original data views
        assert forall|j: int| 0 <= j < n as int implies
            T::is_representable(data@[j].view())
        by {
            // state_generic(data, n, 0)[j] == data[j].view() by spec unfolding
            assert(tree_reduce_state_generic::<T, R>(
                original_data, n as nat, 0)[j] == original_data[j].view());
        }
    }

    let mut d: u64 = 0;
    let mut stride: u64 = 1;
    while d < levels
        invariant
            d <= levels,
            stride as nat == pow2(d as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= u64::MAX / 2,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_representable::<T, R>(original_data),
            original_data.len() == n as nat,
            total_levels == levels as nat,
            forall|j: int| 0 <= j < n as int ==>
                data@[j].view().eqv(
                    #[trigger] tree_reduce_state_generic::<T, R>(
                        original_data, n as nat, d as nat)[j]
                ),
            forall|j: int| 0 <= j < n as int ==>
                T::is_representable(data@[j].view()),
        decreases levels - d,
    {
        proof {
            lemma_pow2_lt_for_sub_levels(n as nat, d as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_positive(d as nat);
            lemma_tree_reduce_all_representable::<T, R>(
                original_data, n as nat, total_levels, (d + 1) as nat,
            );
        }

        let ghost prev_state = tree_reduce_state_generic::<T, R>(
            original_data, n as nat, d as nat);
        let ghost next_state = tree_reduce_state_generic::<T, R>(
            original_data, n as nat, (d + 1) as nat);
        let step: u64 = 2 * stride;

        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                data@.len() == n as nat,
                stride as nat == pow2(d as nat),
                stride > 0, stride < n,
                step == 2 * stride,
                d < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= u64::MAX / 2,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_representable::<T, R>(original_data),
                original_data.len() == n as nat,
                total_levels == levels as nat,
                prev_state == tree_reduce_state_generic::<T, R>(
                    original_data, n as nat, d as nat),
                next_state == tree_reduce_state_generic::<T, R>(
                    original_data, n as nat, (d + 1) as nat),
                forall|j: int| 0 <= j < i as int ==>
                    data@[j].view().eqv(next_state[j]),
                forall|j: int| i as int <= j < n as int ==>
                    data@[j].view().eqv(prev_state[j]),
                forall|j: int| 0 <= j < n as int ==>
                    T::is_representable(data@[j].view()),
                forall|j: int| 0 <= j < n as int ==>
                    T::is_representable(#[trigger] next_state[j]),
            decreases n - i,
        {
            if (i + 1) % step == 0 && i >= stride {
                let partner = (i - stride) as usize;

                // Capture pre-mutation views for proof chains
                let ghost old_i_view = data@[i as int].view();
                let ghost old_p_view = data@[partner as int].view();

                proof {
                    // Partner is not active at level d+1:
                    // next_state[partner] == prev_state[partner]
                    let pi = partner as int + 1;
                    assert(pi == i as int + 1 - stride as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        (i + 1) as int, step as int);
                    let q = ((i + 1) as int) / (step as int);
                    assert(i as int + 1 == step as int * q);
                    assert(q >= 1) by (nonlinear_arith)
                        requires i as int + 1 == step as int * q, step > 0,
                                 i as int + 1 > 0;
                    assert(pi == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires pi == i as int + 1 - stride as int,
                                 i as int + 1 == step as int * q,
                                 step == 2 * stride;
                    assert(pi == step as int * (q - 1) + stride as int)
                        by (nonlinear_arith)
                        requires pi == stride as int * (2 * q - 1),
                                 step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        pi, step as int, q - 1, stride as int
                    );
                    assert(pi % (step as int) != 0) by (nonlinear_arith)
                        requires pi % (step as int) == stride as int, stride > 0;
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                    assert(next_state[partner as int] == prev_state[partner as int]);

                    // Bridge partner view to prev_state
                    // partner < i, so data[partner].view().eqv(next_state[partner])
                    //   = prev_state[partner]

                    // Prove sum is representable for exec_add
                    use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
                    lemma_add_congruence::<R>(
                        old_i_view, prev_state[i as int],
                        old_p_view, prev_state[partner as int],
                    );
                    // old_i_view.add(old_p_view).eqv(prev_state[i].add(prev_state[partner]))
                    assert(next_state[i as int]
                        == prev_state[i as int].add(prev_state[partner as int]));
                    // old_i_view.add(old_p_view).eqv(next_state[i])
                    R::axiom_eqv_symmetric(
                        old_i_view.add(old_p_view), next_state[i as int],
                    );
                    T::lemma_representable_congruence(
                        next_state[i as int], old_i_view.add(old_p_view),
                    );
                }

                let val = data[i as usize].exec_add(&data[partner]);
                data.set(i as usize, val);

                proof {
                    // val.view().eqv(old_i_view.add(old_p_view)) from exec_add
                    // old_i_view.add(old_p_view).eqv(next_state[i]) proved above
                    // data@[i] == val, so data@[i].view() == val.view()
                    R::axiom_eqv_transitive(
                        data@[i as int].view(),
                        old_i_view.add(old_p_view),
                        next_state[i as int],
                    );
                    // is_representable(data@[i].view())
                    R::axiom_eqv_symmetric(
                        data@[i as int].view(), next_state[i as int]);
                    T::lemma_representable_congruence(
                        next_state[i as int], data@[i as int].view());
                }
            } else {
                proof {
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                    // Non-active: next_state[i] == prev_state[i]
                    // data@[i].view().eqv(prev_state[i]) == next_state[i]
                }
            }

            i = i + 1;
        }

        proof {
            assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
            // Re-establish representability for all positions
            assert forall|j: int| 0 <= j < n as int implies
                T::is_representable(data@[j].view())
            by {
                R::axiom_eqv_symmetric(data@[j].view(), next_state[j]);
                T::lemma_representable_congruence(next_state[j], data@[j].view());
            }
        }
        stride = stride * 2;
        d = d + 1;
    }
}

// ============================================================
// Generic Blelloch exclusive scan
// ============================================================

/// Expected value at position j after k Blelloch down-sweep levels (generic Ring version).
///
/// Positions at the current stride hold exclusive prefix sums (via eqv).
/// Other positions hold their up-sweep (tree reduce) values.
pub open spec fn blelloch_expected_generic<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, total_levels: nat, k: nat, j: int,
) -> R
    recommends 0 <= j < n as int,
{
    let s = pow2((total_levels - k) as nat);
    if (j + 1) % (s as int) == 0 {
        partial_sum_generic::<T, R>(data, 0, j + 1 - s as int)
    } else {
        tree_reduce_state_generic::<T, R>(data, n, total_levels)[j]
    }
}

/// Generic inner loop invariant: processed positions match dk+1 expected, others match dk expected.
pub open spec fn ds_inner_inv_generic<T: ExecRing<R>, R: Ring>(
    data_view: Seq<T>, j: int, ri: int, stride: int, step: int,
    orig: Seq<T>, n: nat, total_levels: nat, dk: nat,
) -> bool {
    if ds_pair_processed(j, ri, stride, step) {
        data_view[j].view().eqv(
            blelloch_expected_generic::<T, R>(orig, n, total_levels, (dk + 1) as nat, j))
    } else {
        data_view[j].view().eqv(
            blelloch_expected_generic::<T, R>(orig, n, total_levels, dk, j))
    }
}

/// Tree reduce state is stable across levels for positions not active at those levels.
proof fn lemma_tree_reduce_stable_range_generic<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, start: nat, end_level: nat, i: int,
)
    requires
        n as int == data.len(),
        start <= end_level,
        0 <= i < n as int,
        forall|L: nat| start < L && L <= end_level ==>
            (i + 1) % (pow2(L) as int) != 0,
    ensures
        tree_reduce_state_generic::<T, R>(data, n, end_level)[i]
            == tree_reduce_state_generic::<T, R>(data, n, start)[i],
    decreases end_level - start,
{
    if start == end_level {
    } else {
        lemma_tree_reduce_stable_range_generic::<T, R>(
            data, n, start, (end_level - 1) as nat, i);
    }
}

/// At the "exact level" d in the tree reduce, position i holds
/// partial_sum_generic(data, i+1-pow2(d), i+1) via eqv.
proof fn lemma_tree_reduce_value_at_exact_level_generic<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, total_levels: nat, d: nat, i: int,
)
    requires
        n as int == data.len(), n > 0, is_power_of_2(n),
        pow2(total_levels) == n,
        0 <= i < n as int,
        d <= total_levels,
        (i + 1) % (pow2(d) as int) == 0,
        d < total_levels ==> (i + 1) % (pow2((d + 1) as nat) as int) != 0,
    ensures
        tree_reduce_state_generic::<T, R>(data, n, total_levels)[i].eqv(
            partial_sum_generic::<T, R>(data, i + 1 - pow2(d) as int, i + 1)),
{
    lemma_tree_reduce_invariant_all_generic::<T, R>(data, n, total_levels, d);

    if d == total_levels {
        // state at level total_levels: invariant gives the result
    } else {
        // Stability: state doesn't change from level d to total_levels
        assert forall|L: nat| d < L && L <= total_levels
        implies (i + 1) % (pow2(L) as int) != 0
        by {
            if (i + 1) % (pow2(L) as int) == 0 {
                crate::proof::swizzle_lemmas::lemma_mod_pow2_weaken(
                    (i + 1) as nat, L, (d + 1) as nat);
            }
        };
        lemma_tree_reduce_stable_range_generic::<T, R>(data, n, d, total_levels, i);
        // state[total_levels][i] == state[d][i] (structural), and
        // state[d][i].eqv(partial_sum_generic(...)) from invariant
    }
}

/// All blelloch_expected_generic values are representable.
proof fn lemma_blelloch_expected_representable<T: ExecRing<R>, R: Ring>(
    data: Seq<T>, n: nat, total_levels: nat, k: nat, j: int,
)
    requires
        n as int == data.len(), n > 0, is_power_of_2(n),
        pow2(total_levels) == n,
        0 <= j < n as int,
        k <= total_levels,
        all_partial_sums_representable::<T, R>(data),
    ensures
        T::is_representable(
            blelloch_expected_generic::<T, R>(data, n, total_levels, k, j)),
{
    let s = pow2((total_levels - k) as nat);
    if (j + 1) % (s as int) == 0 {
        // partial_sum_generic(data, 0, j+1-s) — representable by all_partial_sums_representable
        crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - k) as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, s as int);
        let q = (j + 1) / (s as int);
        assert(j + 1 == s as int * q);
        assert(q >= 1) by (nonlinear_arith)
            requires j + 1 == s as int * q, s > 0, j >= 0;
        assert(j + 1 - s as int >= 0) by (nonlinear_arith)
            requires j + 1 == s as int * q, q >= 1, s > 0;
    } else {
        // tree_reduce_state_generic value — representable by lemma
        lemma_tree_reduce_all_representable::<T, R>(data, n, total_levels, total_levels);
    }
}

/// Generic Blelloch exclusive scan (in-place).
pub fn blelloch_exclusive_scan_generic_exec<T: ExecRing<R>, R: Ring>(
    data: &mut Vec<T>, n: u64,
)
    requires
        old(data)@.len() == n as nat,
        n > 0,
        is_power_of_2(n as nat),
        all_partial_sums_representable::<T, R>(old(data)@),
        n <= u64::MAX / 2,
    ensures
        data@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            data@[i].view().eqv(
                partial_sum_generic::<T, R>(old(data)@, 0, i)),
{
    let ghost original_data = old(data)@;
    let levels = log2_ceil_exec(n);
    let data_len = data.len();

    // Handle n = 1: exclusive_scan[0] = sum(data, 0, 0) = zero()
    if n == 1 {
        let zero_val = T::exec_zero();
        data.set(0, zero_val);
        proof {
            lemma_sum_empty::<R>(|j: int| original_data[j].view(), 0, 0);
            // zero_val.view().eqv(R::zero()) and sum(f, 0, 0).eqv(R::zero())
            // => zero_val.view().eqv(sum(f, 0, 0)) = partial_sum_generic(orig, 0, 0)
            R::axiom_eqv_symmetric(
                partial_sum_generic::<T, R>(original_data, 0, 0), R::zero());
            R::axiom_eqv_transitive(
                data@[0].view(), R::zero(),
                partial_sum_generic::<T, R>(original_data, 0, 0));
        }
        return;
    }

    // n >= 2, so levels >= 1
    proof { lemma_pow2_log2_ceil_exact(n as nat); }
    let ghost total_levels = levels as nat;

    // ============================================================
    // UP-SWEEP (generic tree reduce)
    // ============================================================
    tree_reduce_in_place_generic_exec::<T, R>(data, n, levels);

    // ============================================================
    // ROOT ZEROING
    // ============================================================
    let zero_val = T::exec_zero();
    proof {
        // Save tree reduce postcondition
        assert forall|j: int| 0 <= j < n as int implies
            data@[j].view().eqv(
                tree_reduce_state_generic::<T, R>(original_data, n as nat, total_levels)[j])
        by {}
    }
    let ghost pre_zero_data = data@;
    data.set((n - 1) as usize, zero_val);

    proof {
        // Establish blelloch_expected_generic at dk=0
        assert forall|j: int| 0 <= j < n as int implies
            data@[j].view().eqv(
                blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, 0, j))
        by {
            let s = pow2(total_levels);
            if j == n as int - 1 {
                // data[n-1] = zero_val, expected = partial_sum_generic(orig, 0, 0) = sum(f,0,0)
                assert((j + 1) % (s as int) == 0) by {
                    assert(j + 1 == n as int);
                    assert(n as nat == s);
                };
                lemma_sum_empty::<R>(|i: int| original_data[i].view(), 0, 0);
                // zero_val.view().eqv(R::zero()) and sum(f,0,0).eqv(R::zero())
                R::axiom_eqv_symmetric(
                    partial_sum_generic::<T, R>(original_data, 0, 0), R::zero());
                R::axiom_eqv_transitive(
                    data@[j].view(), R::zero(),
                    partial_sum_generic::<T, R>(original_data, 0, 0));
            } else {
                // data[j] unchanged, expected = tree_reduce_state_generic[j]
                assert((j + 1) % (s as int) != 0) by {
                    assert(0 < j + 1 && j + 1 < n as int);
                    assert(n as nat == s);
                    vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, s);
                };
                // data@[j] == pre_zero_data[j] (unchanged by set at n-1)
                assert(data@[j].view().eqv(
                    tree_reduce_state_generic::<T, R>(
                        original_data, n as nat, total_levels)[j]));
            }
        }
    }

    // ============================================================
    // DOWN-SWEEP
    // ============================================================
    let mut dk: u64 = 0;
    let mut ds_stride: u64 = n / 2;
    proof {
        crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - 1) as nat);
        assert(pow2(total_levels) == 2 * pow2((total_levels - 1) as nat));
        assert(ds_stride as nat == pow2((total_levels - 1) as nat)) by (nonlinear_arith)
            requires
                pow2(total_levels) == n as nat,
                pow2(total_levels) == 2 * pow2((total_levels - 1) as nat),
                ds_stride == n / 2, n > 1;
        // Representability at dk=0
        assert forall|j: int| 0 <= j < n as int implies
            T::is_representable(data@[j].view())
        by {
            lemma_blelloch_expected_representable::<T, R>(
                original_data, n as nat, total_levels, 0, j);
            R::axiom_eqv_symmetric(
                data@[j].view(),
                blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, 0, j));
            T::lemma_representable_congruence(
                blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, 0, j),
                data@[j].view());
        }
    }

    while dk < levels
        invariant
            dk <= levels,
            dk < levels ==> ds_stride as nat == pow2((total_levels - dk - 1) as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= u64::MAX / 2,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_representable::<T, R>(original_data),
            original_data.len() == n as nat,
            total_levels == levels as nat,
            total_levels > 0,
            forall|j: int| 0 <= j < n as int ==>
                data@[j].view().eqv(
                    blelloch_expected_generic::<T, R>(
                        original_data, n as nat, total_levels, dk as nat, j)),
            forall|j: int| 0 <= j < n as int ==>
                T::is_representable(data@[j].view()),
        decreases levels - dk,
    {
        let ghost prev_expected = |j: int|
            blelloch_expected_generic::<T, R>(
                original_data, n as nat, total_levels, dk as nat, j);
        let ghost next_expected = |j: int|
            blelloch_expected_generic::<T, R>(
                original_data, n as nat, total_levels, (dk + 1) as nat, j);
        let stride = ds_stride;

        proof {
            crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);
            assert(pow2((total_levels - dk) as nat) == 2 * pow2((total_levels - dk - 1) as nat));
            crate::proof::swizzle_lemmas::lemma_pow2_monotone(
                (total_levels - dk) as nat, total_levels);
            assert(2 * stride as nat <= n as nat);
        }

        let step: u64 = 2 * stride;
        let mut ri: u64 = step - 1;

        proof {
            assert((ri as int + 1) % (step as int) == 0) by {
                assert(ri as int + 1 == step as int);
            };
            // No pairs processed initially
            assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
            implies ds_inner_inv_generic::<T, R>(
                data@, j, ri as int, stride as int, step as int,
                original_data, n as nat, total_levels, dk as nat)
            by {
                lemma_no_pairs_processed_initially(j, stride as int, step as int);
            }
        }

        while ri < n
            invariant
                data@.len() == n as nat,
                stride as nat == pow2((total_levels - dk - 1) as nat),
                step == 2 * stride,
                stride > 0, stride < n,
                dk < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= u64::MAX / 2,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_representable::<T, R>(original_data),
                original_data.len() == n as nat,
                total_levels == levels as nat,
                total_levels > 0,
                ri >= step - 1,
                ri < n ==> ri >= stride,
                ri < n ==> (ri + 1) % (step as int) == 0,
                forall|j: int| #![trigger data@[j]] 0 <= j < n as int ==>
                    ds_inner_inv_generic::<T, R>(
                        data@, j, ri as int, stride as int, step as int,
                        original_data, n as nat, total_levels, dk as nat),
                forall|j: int| 0 <= j < n as int ==>
                    T::is_representable(data@[j].view()),
            decreases n - ri,
        {
            let right = ri as usize;
            let left = (ri - stride) as usize;

            // Capture old views
            let ghost old_right_view = data@[right as int].view();
            let ghost old_left_view = data@[left as int].view();

            proof {
                let li = ri as int - stride as int;
                // Left is unprocessed: (li+1) % step == stride, and partner ri >= ri
                assert((li + 1) % (step as int) == stride as int) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        (ri + 1) as int, step as int);
                    let q = ((ri + 1) as int) / (step as int);
                    assert(ri as int + 1 == step as int * q);
                    assert(li + 1 == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires li == ri as int - stride as int,
                                 ri as int + 1 == step as int * q,
                                 step == 2 * stride;
                    assert(li + 1 == step as int * (q - 1) + stride as int) by (nonlinear_arith)
                        requires li + 1 == stride as int * (2 * q - 1),
                                 step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        li + 1, step as int, q - 1, stride as int
                    );
                };

                // Both unprocessed: match prev expected
                assert(!ds_pair_processed(ri as int, ri as int, stride as int, step as int));
                assert(!ds_pair_processed(li, ri as int, stride as int, step as int));

                // Prove sum is representable for exec_add
                // old_left.view().eqv(expected_dk(left))
                // old_right.view().eqv(expected_dk(right))
                // sum = expected_dk(left).add(expected_dk(right))
                // Need: sum.eqv(expected_dk+1(right)), and expected_dk+1(right) is representable
                lemma_blelloch_expected_representable::<T, R>(
                    original_data, n as nat, total_levels, (dk + 1) as nat, ri as int);

                // Show old_left + old_right is representable via eqv chain
                use verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence;
                let exp_left = blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, dk as nat, li);
                let exp_right = blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, dk as nat, ri as int);
                lemma_add_congruence::<R>(
                    old_left_view, exp_left, old_right_view, exp_right);
                // old_left.add(old_right).eqv(exp_left.add(exp_right))

                // Now prove exp_left.add(exp_right).eqv(expected_dk+1(right))
                // expected_dk(right) = partial_sum_generic(orig, 0, ri+1-s_prev)
                let s_prev = pow2((total_levels - dk) as nat);
                assert(s_prev == 2 * stride as nat);
                assert((ri as int + 1) % (s_prev as int) == 0);
                // expected_dk(left): (li+1) % s_prev == stride != 0, so = tree_reduce[li]
                assert((li + 1) % (s_prev as int) != 0) by (nonlinear_arith)
                    requires (li + 1) % (step as int) == stride as int,
                             step == 2 * stride, stride > 0,
                             s_prev == 2 * stride as nat;
                // tree_reduce[li] at exact level d = total_levels - dk - 1
                let d = (total_levels - dk - 1) as nat;
                // First prove (li+1) % stride == 0
                assert((li + 1) % (stride as int) == 0) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        li + 1, step as int);
                    let k = (li + 1) / (step as int);
                    assert(li + 1 == step as int * k + stride as int);
                    assert(li + 1 == stride as int * (2 * k + 1)) by (nonlinear_arith)
                        requires li + 1 == step as int * k + stride as int,
                                 step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        li + 1, stride as int, 2 * k + 1, 0);
                };
                assert((li + 1) % (pow2(d) as int) == 0) by {
                    assert(pow2(d) == stride as nat);
                };
                if d < total_levels {
                    assert((li + 1) % (pow2((d + 1) as nat) as int) != 0) by {
                        assert(pow2((d + 1) as nat) == s_prev);
                    };
                }
                lemma_tree_reduce_value_at_exact_level_generic::<T, R>(
                    original_data, n as nat, total_levels, d, li);
                // tree_reduce[li].eqv(partial_sum_generic(orig, li+1-stride, li+1))
                // = partial_sum_generic(orig, ri+1-s_prev, ri+1-stride)
                assert(li + 1 - stride as int == ri as int + 1 - s_prev as int) by (nonlinear_arith)
                    requires li == ri as int - stride as int, s_prev == 2 * stride as nat;

                // Now: exp_left = tree_reduce[li].eqv(partial_sum_generic(orig, ri+1-s_prev, ri+1-stride))
                //       exp_right = partial_sum_generic(orig, 0, ri+1-s_prev)
                // Sum split: partial_sum_generic(orig, 0, ri+1-stride).eqv(
                //   partial_sum_generic(orig, 0, ri+1-s_prev).add(partial_sum_generic(orig, ri+1-s_prev, ri+1-stride)))
                let f = |j: int| original_data[j].view();
                let lo = ri as int + 1 - s_prev as int;
                let mid = ri as int + 1 - stride as int;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                    (ri + 1) as int, s_prev as int);
                let q = ((ri + 1) as int) / (s_prev as int);
                assert(ri as int + 1 == s_prev as int * q);
                assert(q >= 1) by (nonlinear_arith)
                    requires ri as int + 1 == s_prev as int * q, s_prev > 0, ri >= 0;
                assert(lo >= 0) by (nonlinear_arith)
                    requires lo == ri as int + 1 - s_prev as int,
                             ri as int + 1 == s_prev as int * q, q >= 1, s_prev > 0;
                lemma_sum_split::<R>(f, 0, lo, mid);
                // sum(f, 0, mid).eqv(sum(f, 0, lo).add(sum(f, lo, mid)))
                // = partial_sum(orig, 0, mid).eqv(exp_right.add(exp_left_val))
                // where exp_left_val = partial_sum(orig, lo, mid) and exp_left.eqv(exp_left_val)

                // Chain: old_left.add(old_right).eqv(exp_left.add(exp_right))
                // exp_left.eqv(partial_sum(orig, lo, mid)) [from exact level]
                // Need: exp_left.add(exp_right).eqv(partial_sum(orig, lo, mid).add(exp_right))
                let psg_lo_mid = partial_sum_generic::<T, R>(original_data, lo, mid);
                R::axiom_eqv_reflexive(exp_right);
                lemma_add_congruence::<R>(exp_left, psg_lo_mid, exp_right, exp_right);
                // exp_left.add(exp_right).eqv(psg_lo_mid.add(exp_right))

                // Commutativity: psg_lo_mid.add(exp_right).eqv(exp_right.add(psg_lo_mid))
                R::axiom_add_commutative(psg_lo_mid, exp_right);
                R::axiom_eqv_transitive(
                    exp_left.add(exp_right), psg_lo_mid.add(exp_right),
                    exp_right.add(psg_lo_mid));

                // sum_split gave: sum(f,0,mid).eqv(sum(f,0,lo).add(sum(f,lo,mid)))
                // = partial_sum(0,mid).eqv(exp_right.add(psg_lo_mid))
                R::axiom_eqv_symmetric(
                    partial_sum_generic::<T, R>(original_data, 0, mid),
                    exp_right.add(psg_lo_mid));

                // Chain: old_left.add(old_right).eqv(exp_left.add(exp_right))
                //        .eqv(exp_right.add(psg_lo_mid)).eqv(partial_sum(0, mid))
                R::axiom_eqv_transitive(
                    old_left_view.add(old_right_view),
                    exp_left.add(exp_right),
                    exp_right.add(psg_lo_mid));
                R::axiom_eqv_transitive(
                    old_left_view.add(old_right_view),
                    exp_right.add(psg_lo_mid),
                    partial_sum_generic::<T, R>(original_data, 0, mid));

                // expected_dk+1(right): (ri+1) % stride == 0, so partial_sum(0, ri+1-stride) = partial_sum(0, mid)
                assert((ri as int + 1) % (stride as int) == 0) by {
                    crate::proof::swizzle_lemmas::lemma_mod_pow2_weaken(
                        (ri as int + 1) as nat,
                        (total_levels - dk) as nat,
                        (total_levels - dk - 1) as nat);
                };

                // Representability of the sum value
                R::axiom_eqv_symmetric(
                    old_left_view.add(old_right_view),
                    partial_sum_generic::<T, R>(original_data, 0, mid));
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(original_data, 0, mid),
                    old_left_view.add(old_right_view));

                // Left position: expected_dk+1(li)
                // (li+1) % stride == 0 (shown above), so expected_dk+1(li) = partial_sum(0, li+1-stride)
                // = partial_sum(0, ri+1-s_prev) = exp_right
                // old_right.view().eqv(exp_right) already established
                // And expected_dk+1(li) matches exp_right

                // Representability for left (clone of right)
                lemma_blelloch_expected_representable::<T, R>(
                    original_data, n as nat, total_levels, (dk + 1) as nat, li);
            }

            let old_right_clone = data[right].exec_clone();
            let sum_val = data[left].exec_add(&data[right]);
            data.set(left, old_right_clone);
            data.set(right, sum_val);

            proof {
                let li = ri as int - stride as int;
                let s_prev = pow2((total_levels - dk) as nat);
                let mid = ri as int + 1 - stride as int;

                // Prove data[ri].view().eqv(expected_dk+1(ri))
                // sum_val.view().eqv(old_left_view.add(old_right_view))
                // old_left_view.add(old_right_view).eqv(partial_sum(0, mid))
                // expected_dk+1(ri) = partial_sum(0, mid)
                R::axiom_eqv_transitive(
                    data@[ri as int].view(),
                    old_left_view.add(old_right_view),
                    partial_sum_generic::<T, R>(original_data, 0, mid));

                // Prove data[li].view().eqv(expected_dk+1(li))
                // old_right_clone.view().eqv(old_right_view)
                // old_right_view.eqv(expected_dk(ri)) = partial_sum(0, ri+1-s_prev)
                let exp_right = blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, dk as nat, ri as int);
                R::axiom_eqv_transitive(
                    data@[li].view(), old_right_view, exp_right);
                // expected_dk+1(li) = partial_sum(0, li+1-stride) = partial_sum(0, ri+1-s_prev)
                assert(li + 1 - stride as int == ri as int + 1 - s_prev as int) by (nonlinear_arith)
                    requires li == ri as int - stride as int, s_prev == 2 * stride as nat;

                // Representability
                R::axiom_eqv_symmetric(data@[ri as int].view(),
                    partial_sum_generic::<T, R>(original_data, 0, mid));
                T::lemma_representable_congruence(
                    partial_sum_generic::<T, R>(original_data, 0, mid),
                    data@[ri as int].view());

                R::axiom_eqv_symmetric(data@[li].view(), exp_right);
                T::lemma_representable_congruence(exp_right, data@[li].view());
            }

            // Advance ri
            let ghost old_ri = ri as int;
            if ri + step < n {
                ri = ri + step;
                proof {
                    let li = old_ri - stride as int;
                    assert(ri as int == old_ri + step as int);
                    assert(ri as int + 1 == old_ri + 1 + step as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        (old_ri + 1) as int, step as int);
                    let q = ((old_ri + 1) as int) / (step as int);
                    assert(old_ri + 1 == step as int * q);
                    assert(ri as int + 1 == step as int * (q + 1)) by (nonlinear_arith)
                        requires ri as int + 1 == old_ri + 1 + step as int,
                                 old_ri + 1 == step as int * q;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        ri as int + 1, step as int, q + 1, 0int
                    );

                    assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                    implies ds_inner_inv_generic::<T, R>(
                        data@, j, ri as int, stride as int, step as int,
                        original_data, n as nat, total_levels, dk as nat)
                    by {
                        if j == old_ri || j == li {
                            assert(ds_pair_processed(
                                j, ri as int, stride as int, step as int));
                        } else {
                            lemma_ds_pair_processed_frame(
                                j, old_ri, ri as int, stride as int,
                                step as int, n as int);
                        }
                    }
                }
            } else {
                ri = n;
                proof {
                    let li = old_ri - stride as int;
                    assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                    implies ds_inner_inv_generic::<T, R>(
                        data@, j, ri as int, stride as int, step as int,
                        original_data, n as nat, total_levels, dk as nat)
                    by {
                        if j == old_ri || j == li {
                            assert(ds_pair_processed(
                                j, ri as int, stride as int, step as int));
                        } else {
                            lemma_ds_pair_processed_frame(
                                j, old_ri, n as int, stride as int,
                                step as int, n as int);
                        }
                    }
                }
            }
        }

        // After inner loop: all pairs processed, data matches dk+1 expected
        proof {
            let ghost num_pairs = pow2(dk as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_mul(
                (total_levels - dk) as nat, dk as nat);
            assert(n as nat == step as nat * num_pairs) by {
                assert(step as nat == pow2((total_levels - dk) as nat));
                assert((total_levels - dk) as nat + dk as nat == total_levels);
            };

            assert forall|j: int| 0 <= j < n as int
            implies data@[j].view().eqv(
                blelloch_expected_generic::<T, R>(
                    original_data, n as nat, total_levels, (dk + 1) as nat, j))
            by {
                let new_stride = pow2((total_levels - (dk + 1) as nat) as nat);
                assert(new_stride == stride as nat);

                if (j + 1) % (step as int) == 0 && j >= stride as int {
                    // Right position: processed
                    assert(ds_pair_processed(
                        j, ri as int, stride as int, step as int));
                } else if (j + 1) % (step as int) == stride as int {
                    // Left position: show its partner exists (partner < n)
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        j + 1, (2 * stride as int));
                    let q_left = (j + 1) / (2 * stride as int);
                    assert(j + 1 == (2 * stride as int) * q_left + stride as int);
                    let partner = j + stride as int;
                    assert(partner + 1 == (2 * stride as int) * (q_left + 1)) by (nonlinear_arith)
                        requires partner == j + stride as int,
                                 j + 1 == (2 * stride as int) * q_left + stride as int;
                    let np = num_pairs as int;
                    assert(q_left + 1 <= np) by (nonlinear_arith)
                        requires j + 1 <= n as int,
                                 j + 1 == (2 * stride as int) * q_left + stride as int,
                                 n as int == step as int * np,
                                 stride > 0, step == 2 * stride;
                    assert(partner < n as int) by (nonlinear_arith)
                        requires partner + 1 == (2 * stride as int) * (q_left + 1),
                                 q_left + 1 <= np, n as int == step as int * np,
                                 step > 0, step == 2 * stride, stride > 0;
                    assert(partner < ri as int);
                    assert(ds_pair_processed(
                        j, ri as int, stride as int, step as int));
                } else {
                    // Unchanged position
                    assert(!ds_pair_processed(
                        j, ri as int, stride as int, step as int));
                    // expected_dk+1(j): (j+1) % stride != 0 → tree_reduce[j]
                    // data[j].eqv(expected_dk(j)) = tree_reduce[j] (since (j+1)%s_prev != 0)
                    // expected_dk+1(j) = tree_reduce[j] (since (j+1)%stride != 0)
                    let s_prev = pow2((total_levels - dk) as nat);
                    crate::proof::scan_blelloch_lemmas::lemma_else_branch_not_divisible(
                        j, stride as nat, s_prev);
                    assert((j + 1) % (s_prev as int) != 0) by {
                        if (j + 1) % (s_prev as int) == 0 {
                            crate::proof::swizzle_lemmas::lemma_mod_pow2_weaken(
                                (j + 1) as nat,
                                (total_levels - dk) as nat,
                                (total_levels - dk - 1) as nat);
                        }
                    };
                }
            }

            // Representability at dk+1
            assert forall|j: int| 0 <= j < n as int implies
                T::is_representable(data@[j].view())
            by {
                lemma_blelloch_expected_representable::<T, R>(
                    original_data, n as nat, total_levels, (dk + 1) as nat, j);
                R::axiom_eqv_symmetric(
                    data@[j].view(),
                    blelloch_expected_generic::<T, R>(
                        original_data, n as nat, total_levels, (dk + 1) as nat, j));
                T::lemma_representable_congruence(
                    blelloch_expected_generic::<T, R>(
                        original_data, n as nat, total_levels, (dk + 1) as nat, j),
                    data@[j].view());
            }
        }

        dk = dk + 1;
        if dk < levels {
            proof {
                assert(pow2((total_levels - dk - 1) as nat) == ds_stride as nat / 2) by {
                    assert(pow2((total_levels - (dk - 1) - 1) as nat) == ds_stride as nat);
                    assert((total_levels - (dk - 1) - 1) as nat == (total_levels - dk) as nat);
                    assert(pow2((total_levels - dk) as nat)
                        == 2 * pow2((total_levels - dk - 1) as nat));
                    crate::proof::swizzle_lemmas::lemma_pow2_positive(
                        (total_levels - dk - 1) as nat);
                };
            }
            ds_stride = ds_stride / 2;
        }
    }

    // ============================================================
    // FINAL: dk == levels, expected = exclusive prefix sum
    // ============================================================
    proof {
        assert forall|j: int| 0 <= j < n as int
        implies data@[j].view().eqv(
            partial_sum_generic::<T, R>(original_data, 0, j))
        by {
            // At dk = total_levels, stride = pow2(0) = 1, divides all j+1
            assert((total_levels - total_levels) as nat == 0nat);
            assert(pow2(0nat) == 1nat);
            let s = pow2((total_levels - total_levels) as nat);
            assert(s == 1nat);
            assert((j + 1) % 1int == 0int);
            assert((j + 1) % (s as int) == 0);
            // blelloch_expected_generic(orig, n, levels, levels, j)
            //   = partial_sum_generic(orig, 0, j+1-1) = partial_sum_generic(orig, 0, j)
            assert(blelloch_expected_generic::<T, R>(
                original_data, n as nat, total_levels, levels as nat, j)
                == partial_sum_generic::<T, R>(original_data, 0, j));
        }
    }
}

// ============================================================
// Blelloch exclusive scan (i64)
// ============================================================

/// Tree reduce state at level d matches partial sums for positions active at level d.
/// Used for overflow safety: the addition result is a partial sum of original data.
proof fn lemma_upsweep_overflow_bound(
    original_data: Seq<i64>,
    original_int: Seq<int>,
    n: nat,
    total_levels: nat,
    d: nat,
    i: int,
)
    requires
        original_data.len() == n,
        original_int == as_int_seq(original_data),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        d < total_levels,
        0 <= i < n as int,
        (i + 1) % (pow2((d + 1) as nat) as int) == 0,
        all_partial_sums_bounded(original_data),
    ensures ({
        let next_val = tree_reduce_state(original_int, n, (d + 1) as nat)[i];
        i64::MIN as int <= next_val && next_val <= i64::MAX as int
    }),
{
    use crate::proof::scan_blelloch_lemmas::lemma_tree_reduce_invariant_all;

    let p = pow2((d + 1) as nat);
    crate::proof::swizzle_lemmas::lemma_pow2_positive((d + 1) as nat);

    // i+1 >= pow2(d+1) since (i+1) % pow2(d+1) == 0 and i+1 >= 1
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, p as int);
    let k = (i + 1) / (p as int);
    assert(i + 1 == p as int * k);
    assert(k >= 1) by (nonlinear_arith)
        requires i + 1 == p as int * k, p > 0, i >= 0;

    let lo = i + 1 - p as int;
    let hi = i + 1;
    assert(lo >= 0) by (nonlinear_arith)
        requires i + 1 == p as int * k, k >= 1, p > 0, lo == i + 1 - p as int;

    lemma_tree_reduce_invariant_all(original_int, n, total_levels, (d + 1) as nat);
    // tree_reduce_invariant: state[i] == sum(|j| original_int[j], lo, hi)
    let next_val = tree_reduce_state(original_int, n, (d + 1) as nat)[i];
    assert(next_val == sum::<int>(|j: int| original_int[j], lo, hi));

    // Bridge: sum(|j| original_int[j], lo, hi) == partial_sum(original_data, lo, hi)
    assert forall|j: int| lo <= j < hi implies
        original_int[j] == original_data[j] as int by {}
    lemma_sum_congruence::<int>(
        |j: int| original_int[j],
        |j: int| original_data[j] as int,
        lo, hi,
    );
    assert(partial_sum(original_data, lo, hi) == next_val);
}

/// Down-sweep overflow bound: the addition result at each step is a prefix sum.
proof fn lemma_downsweep_overflow_bound(
    original_data: Seq<i64>,
    original_int: Seq<int>,
    n: nat,
    total_levels: nat,
    dk: nat,
    i: int,
    prev_left: int,
    prev_right: int,
)
    requires
        original_data.len() == n,
        original_int == as_int_seq(original_data),
        n > 0,
        is_power_of_2(n),
        pow2(total_levels) == n,
        total_levels > 0,
        dk < total_levels,
        0 <= i < n as int,
        all_partial_sums_bounded(original_data),
        blelloch_downsweep_invariant(original_int, n, total_levels, dk),
        ({
            let stride = pow2((total_levels - dk - 1) as nat);
            let step = 2 * stride;
            (i + 1) % (step as int) == 0 && i >= stride as int
            && prev_left == blelloch_downsweep_state(original_int, n, total_levels, dk)[(i - stride as int) as int]
            && prev_right == blelloch_downsweep_state(original_int, n, total_levels, dk)[i]
        }),
    ensures
        i64::MIN as int <= prev_left + prev_right && prev_left + prev_right <= i64::MAX as int,
{
    let stride = pow2((total_levels - dk - 1) as nat);
    let step = 2 * stride;
    crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);

    // prev_left + prev_right = next_ds[i] by blelloch_downsweep_state definition
    use crate::proof::scan_blelloch_lemmas::*;
    lemma_blelloch_step(original_int, n, total_levels, dk);
    // blelloch_downsweep_invariant holds at dk+1
    let next = blelloch_downsweep_state(original_int, n, total_levels, (dk + 1) as nat);
    let prev = blelloch_downsweep_state(original_int, n, total_levels, dk);
    // By spec definition: next[i] = prev[i] + prev[i-stride] = prev_right + prev_left
    assert(next[i] == prev[i] + prev[(i - stride as int) as int]);
    assert(next[i] == prev_left + prev_right);

    // next[i] == blelloch_expected at dk+1 == sum(original_int, 0, i+1-stride)
    assert((i + 1) % (stride as int) == 0) by {
        crate::proof::swizzle_lemmas::lemma_mod_pow2_weaken(
            (i + 1) as nat,
            (total_levels - dk) as nat,
            (total_levels - dk - 1) as nat,
        );
    };

    // hi = i + 1 - stride >= 0
    let hi = i + 1 - stride as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i + 1, step as int);
    let q = (i + 1) / (step as int);
    assert(i + 1 == step as int * q);
    assert(q >= 1) by (nonlinear_arith)
        requires i + 1 == step as int * q, step > 0, i + 1 > 0;
    assert(hi >= 0) by (nonlinear_arith)
        requires i + 1 == step as int * q, q >= 1, step == 2 * stride, hi == i + 1 - stride as int;

    // next[i] = blelloch_expected at dk+1
    // blelloch_expected at dk+1 with stride = pow2(total_levels - dk - 1):
    //   s = pow2(total_levels - (dk+1)) = pow2(total_levels - dk - 1) = stride
    //   (i+1) % s == 0, so expected = sum(data, 0, i+1-stride) = sum(data, 0, hi)
    assert(next[i] == sum::<int>(|j: int| original_int[j], 0, hi));

    // Bridge: sum(|j| original_int[j], 0, hi) == partial_sum(original_data, 0, hi)
    assert forall|j: int| 0 <= j < hi implies
        original_int[j] == original_data[j] as int by {}
    lemma_sum_congruence::<int>(
        |j: int| original_int[j],
        |j: int| original_data[j] as int,
        0, hi,
    );
    assert(partial_sum(original_data, 0, hi) == next[i]);
    assert(partial_sum(original_data, 0, hi) == prev_left + prev_right);
}

/// ds_pair_processed(j, new_ri, ...) == ds_pair_processed(j, old_ri, ...)
/// when j != old_ri and j != old_ri - stride, and new_ri > old_ri with new_ri <= old_ri + step.
/// The only newly processed positions when advancing ri are old_ri (right) and old_ri - stride (left).
proof fn lemma_ds_pair_processed_frame(
    j: int, old_ri: int, new_ri: int, stride: int, step: int, n: int,
)
    requires
        stride > 0,
        step == 2 * stride,
        0 <= j < n,
        (old_ri + 1) % step == 0,
        old_ri >= stride,
        old_ri < new_ri,
        new_ri <= old_ri + step,
        j != old_ri,
        j != old_ri - stride,
    ensures
        ds_pair_processed(j, new_ri, stride, step)
        == ds_pair_processed(j, old_ri, stride, step),
{
    // Right case: (j+1) % step == 0 && j >= stride && j < ri
    // The only difference is j < old_ri+step vs j < old_ri
    // For j in [old_ri, old_ri+step): could j satisfy (j+1)%step==0 && j >= stride?
    // j != old_ri, so j > old_ri. Then j in (old_ri, old_ri+step).
    // (j+1)%step==0 means j+1 = step*k. old_ri+1 = step*q, so j+1 > step*q.
    // Next multiple: step*(q+1) = old_ri+1+step = old_ri+step+1. But j < old_ri+step, so j+1 <= old_ri+step < old_ri+step+1. So no multiple in range.
    if (j + 1) % step == 0 && j >= stride {
        // j < old_ri iff j < old_ri + step (since j != old_ri and there's no other multiple in [old_ri, old_ri+step))
        if j >= old_ri {
            // j > old_ri (since j != old_ri), j < old_ri + step (for the new case)
            // (j+1) % step == 0 and j+1 > old_ri + 1 = step*q
            // Next multiple after step*q is step*(q+1) = old_ri+1+step
            // j+1 <= old_ri+step, so j+1 < step*(q+1). Contradiction with (j+1)%step==0 and j+1 > step*q
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, step);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(old_ri + 1, step);
            let qj = (j + 1) / step;
            let qr = (old_ri + 1) / step;
            assert(j + 1 == step * qj);
            assert(old_ri + 1 == step * qr);
            assert(qj > qr) by (nonlinear_arith)
                requires j + 1 == step * qj, old_ri + 1 == step * qr, j > old_ri, step > 0;
            assert(qj >= qr + 1) by (nonlinear_arith)
                requires qj > qr;
            assert(j + 1 >= step * (qr + 1)) by (nonlinear_arith)
                requires j + 1 == step * qj, qj >= qr + 1, step > 0;
            assert(j >= old_ri + step) by (nonlinear_arith)
                requires j + 1 >= step * (qr + 1), old_ri + 1 == step * qr, step > 0;
            // j >= old_ri + step contradicts j < old_ri + step (from old_ri+step <= n and j < n... wait, j could equal old_ri + step)
            // Actually we need j < old_ri + step for the claim. But j >= old_ri + step means j is NOT in [old_ri, old_ri+step)
            // So ds_pair_processed(j, old_ri+step, ...) requires j < old_ri+step, but j >= old_ri+step: false = false ✓
            // And ds_pair_processed(j, old_ri, ...) requires j < old_ri, but j >= old_ri: false ✓
            // Both false, so equal ✓
        }
    }
    // Left case: (j+1) % step == stride && j + stride < ri
    if (j + 1) % step == stride {
        // j + stride < old_ri iff j + stride < old_ri + step (for j != old_ri - stride)
        if j + stride >= old_ri {
            // j + stride >= old_ri and j != old_ri - stride, so j + stride > old_ri, i.e., j + stride >= old_ri + 1
            // (j+1)%step == stride means j+1 = step*k + stride, so j+stride = step*k + 2*stride - 1 = step*(k+1) - 1
            // old_ri = step*q - 1 (from (old_ri+1)%step==0)
            // j + stride = step*(k+1) - 1 >= old_ri + 1 = step*q, so step*(k+1) >= step*q + 1, k+1 > q, k >= q
            // j + stride = step*(k+1) - 1. For j + stride < old_ri + step = step*(q+1) - 1: step*(k+1) - 1 < step*(q+1) - 1, k < q.
            // But k >= q, contradiction. So j + stride >= old_ri + step.
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, step);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(old_ri + 1, step);
            let kj = (j + 1) / step;
            let qr = (old_ri + 1) / step;
            assert(j + 1 == step * kj + stride);
            assert(old_ri + 1 == step * qr);
            assert(j + stride == step * (kj + 1) - 1) by (nonlinear_arith)
                requires j + 1 == step * kj + stride, step == 2 * stride;
            assert(kj + 1 > qr) by (nonlinear_arith)
                requires j + stride >= old_ri + 1, j + stride == step * (kj + 1) - 1,
                         old_ri + 1 == step * qr, step > 0, j + stride > old_ri;
            assert(kj >= qr) by (nonlinear_arith) requires kj + 1 > qr;
            assert(j + stride >= old_ri + step) by (nonlinear_arith)
                requires j + stride == step * (kj + 1) - 1,
                         old_ri == step * qr - 1, kj >= qr, step > 0;
        }
    }
}

/// No pairs are processed when ri = step - 1 (initial state of inner loop).
proof fn lemma_no_pairs_processed_initially(j: int, stride: int, step: int)
    requires
        stride > 0,
        step == 2 * stride,
        j >= 0,
    ensures !ds_pair_processed(j, step - 1, stride, step),
{
    // Right case: (j+1) % step == 0 && j >= stride && j < step-1
    if (j + 1) % step == 0 {
        if j >= stride {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j + 1, step);
            let q = (j + 1) / step;
            assert(j + 1 == step * q);
            assert(q >= 1) by (nonlinear_arith)
                requires j + 1 == step * q, step > 0, j >= 0;
            assert(j >= step - 1) by (nonlinear_arith)
                requires j + 1 == step * q, q >= 1, step > 0;
            // j >= step - 1 means j < step - 1 is false
        }
    }
    // Left case: (j+1) % step == stride && j + stride < step - 1
    if (j + 1) % step == stride {
        if j + stride < step - 1 {
            assert(j + 1 < step) by (nonlinear_arith)
                requires j + stride < step - 1, step == 2 * stride, stride > 0;
            assert(j + 1 >= 1);
            vstd::arithmetic::div_mod::lemma_small_mod((j + 1) as nat, step as nat);
            // (j+1) % step == j+1, but we assumed (j+1) % step == stride
            // j+1 == stride but j + stride < step - 1 = 2*stride - 1 => j < stride - 1 => j+1 < stride
            assert(false);
        }
    }
}

/// Whether position j has been processed in the down-sweep inner loop.
/// A position is processed if it's a right position of a processed pair (j < ri)
/// or the left partner of a processed pair (j + stride < ri).
pub open spec fn ds_pair_processed(j: int, ri: int, stride: int, step: int) -> bool {
    ((j + 1) % step == 0 && j >= stride && j < ri)
    || ((j + 1) % step == stride && j + stride < ri)
}

/// Down-sweep inner loop invariant: processed positions match next_ds, others match prev_ds.
pub open spec fn ds_inner_inv(
    data_view: Seq<i64>, j: int, ri: int, stride: int, step: int,
    prev_ds: Seq<int>, next_ds: Seq<int>,
) -> bool {
    if ds_pair_processed(j, ri, stride, step) {
        data_view[j] as int == next_ds[j]
    } else {
        data_view[j] as int == prev_ds[j]
    }
}

/// In-place tree reduce (up-sweep phase shared by Blelloch and Brent-Kung).
/// After completion, data[j] == tree_reduce_state(as_int_seq(old(data)), n, levels)[j].
pub fn tree_reduce_in_place_exec(data: &mut Vec<i64>, n: u64, levels: u64)
    requires
        old(data)@.len() == n as nat,
        n > 1,
        pow2(levels as nat) == n as nat,
        is_power_of_2(n as nat),
        levels as nat == log2_ceil(n as nat),
        all_partial_sums_bounded(old(data)@),
        n <= i64::MAX as u64,
    ensures
        data@.len() == n as nat,
        forall|j: int| 0 <= j < n as int ==>
            data@[j] as int == tree_reduce_state(as_int_seq(old(data)@), n as nat, levels as nat)[j],
{
    let ghost original_data = old(data)@;
    let ghost original_int = as_int_seq(original_data);
    let ghost total_levels = levels as nat;
    let data_len = data.len();

    let mut d: u64 = 0;
    let mut stride: u64 = 1;
    while d < levels
        invariant
            d <= levels,
            stride as nat == pow2(d as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == tree_reduce_state(original_int, n as nat, d as nat)[j],
        decreases levels - d,
    {
        proof {
            lemma_pow2_lt_for_sub_levels(n as nat, d as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_positive(d as nat);
        }

        let ghost prev_state = tree_reduce_state(original_int, n as nat, d as nat);
        let ghost next_state = tree_reduce_state(original_int, n as nat, (d + 1) as nat);
        let step: u64 = 2 * stride;

        let mut i: u64 = 0;
        while i < n
            invariant
                i <= n,
                data@.len() == n as nat,
                stride as nat == pow2(d as nat),
                stride > 0,
                stride < n,
                step == 2 * stride,
                d < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                prev_state == tree_reduce_state(original_int, n as nat, d as nat),
                next_state == tree_reduce_state(original_int, n as nat, (d + 1) as nat),
                // Processed positions match next level
                forall|j: int| 0 <= j < i as int ==>
                    data@[j] as int == next_state[j],
                // Unprocessed positions match current level
                forall|j: int| i as int <= j < n as int ==>
                    data@[j] as int == prev_state[j],
            decreases n - i,
        {
            if (i + 1) % step == 0 && i >= stride {
                // Active position: data[i] += data[i - stride]
                let partner = (i - stride) as usize;

                proof {
                    // data[partner] was already processed (partner < i).
                    // next_state[partner] == prev_state[partner] because partner is not active.
                    // Show (partner+1) % pow2(d+1) != 0:
                    let pi = partner as int + 1;
                    assert(pi == i as int + 1 - stride as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 1) as int, step as int);
                    let q = ((i + 1) as int) / (step as int);
                    assert(i as int + 1 == step as int * q);
                    assert(q >= 1) by (nonlinear_arith)
                        requires i as int + 1 == step as int * q, step > 0, i as int + 1 > 0;
                    assert(pi == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires pi == i as int + 1 - stride as int,
                                 i as int + 1 == step as int * q, step == 2 * stride;
                    assert(pi == step as int * (q - 1) + stride as int) by (nonlinear_arith)
                        requires pi == stride as int * (2 * q - 1), step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        pi, step as int, q - 1, stride as int
                    );
                    assert(pi % (step as int) != 0) by (nonlinear_arith)
                        requires pi % (step as int) == stride as int, stride > 0;

                    // So next_state[partner] == prev_state[partner]
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                    assert(next_state[partner as int] == prev_state[partner as int]);

                    // Overflow proof
                    lemma_upsweep_overflow_bound(
                        original_data, original_int, n as nat, total_levels,
                        d as nat, i as int,
                    );
                }

                let val = data[i as usize] + data[partner];
                data.set(i as usize, val);
            } else {
                // Non-active: next_state[i] == prev_state[i] (Z3 sees via definition unfolding)
                proof {
                    assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
                }
            }

            i = i + 1;
        }

        proof {
            assert(pow2((d + 1) as nat) == 2 * pow2(d as nat));
        }
        stride = stride * 2;
        d = d + 1;
    }
}

/// Blelloch in-place exclusive scan. O(n) work, O(2 log n) depth.
/// Requires power-of-2 sized input.
pub fn blelloch_exclusive_scan_exec(data: &mut Vec<i64>, n: u64)
    requires
        old(data)@.len() == n as nat,
        n > 0,
        is_power_of_2(n as nat),
        all_partial_sums_bounded(old(data)@),
        n <= i64::MAX as u64,
    ensures
        data@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            data@[i] as int == exclusive_scan_int(old(data)@)[i],
{
    let ghost original_data = old(data)@;
    let ghost original_int = as_int_seq(original_data);
    let levels = log2_ceil_exec(n);
    let data_len = data.len();

    // Handle n = 1: exclusive_scan[0] = sum(data, 0, 0) = 0
    if n == 1 {
        data.set(0, 0i64);
        proof {
            lemma_sum_empty::<int>(|j: int| as_int_seq(original_data)[j], 0, 0);
        }
        return;
    }

    // n >= 2, so levels >= 1
    proof {
        lemma_pow2_log2_ceil_exact(n as nat);
        // pow2(levels) == n
    }

    let ghost total_levels = levels as nat;

    // ============================================================
    // UP-SWEEP (shared tree reduce)
    // ============================================================
    tree_reduce_in_place_exec(data, n, levels);

    // ============================================================
    // ROOT ZEROING
    // ============================================================
    let ghost upsweep_final = tree_reduce_state(original_int, n as nat, total_levels);
    data.set((n - 1) as usize, 0i64);

    proof {
        use crate::scan_blelloch::*;
        // Prove data now matches blelloch_downsweep_state(original_int, n, levels, 0)
        let ds0 = blelloch_downsweep_state(original_int, n as nat, total_levels, 0);
        assert forall|j: int| 0 <= j < n as int
        implies data@[j] as int == ds0[j]
        by {
            if j == n as int - 1 {
                // data[n-1] = 0, ds0[n-1] = 0 (root set to 0)
            } else {
                // data[j] unchanged, ds0[j] = upsweep_final[j]
            }
        }
    }

    // ============================================================
    // DOWN-SWEEP
    // ============================================================
    let mut dk: u64 = 0;
    let mut ds_stride: u64 = n / 2;  // pow2(levels - 1)
    proof {
        crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - 1) as nat);
        assert(pow2(total_levels) == 2 * pow2((total_levels - 1) as nat));
        assert(ds_stride as nat == pow2((total_levels - 1) as nat)) by (nonlinear_arith)
            requires
                pow2(total_levels) == n as nat,
                pow2(total_levels) == 2 * pow2((total_levels - 1) as nat),
                ds_stride == n / 2,
                n > 1;
    }

    proof {
        use crate::proof::scan_blelloch_lemmas::lemma_blelloch_base;
        lemma_blelloch_base(original_int, n as nat, total_levels);
    }

    while dk < levels
        invariant
            dk <= levels,
            dk < levels ==> ds_stride as nat == pow2((total_levels - dk - 1) as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            total_levels > 0,
            blelloch_downsweep_invariant(original_int, n as nat, total_levels, dk as nat),
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == blelloch_downsweep_state(original_int, n as nat, total_levels, dk as nat)[j],
        decreases levels - dk,
    {
        let ghost prev_ds = blelloch_downsweep_state(original_int, n as nat, total_levels, dk as nat);
        let ghost next_ds = blelloch_downsweep_state(original_int, n as nat, total_levels, (dk + 1) as nat);
        let stride = ds_stride;

        proof {
            crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);
            // 2 * stride = pow2(total_levels - dk) <= pow2(total_levels) = n
            assert(pow2((total_levels - dk) as nat) == 2 * pow2((total_levels - dk - 1) as nat));
            crate::proof::swizzle_lemmas::lemma_pow2_monotone((total_levels - dk) as nat, total_levels);
            assert(2 * stride as nat <= n as nat);
        }

        let step: u64 = 2 * stride;

        // Inner loop: iterate right positions
        let mut ri: u64 = step - 1;  // first right position

        // Establish invariants before the loop
        proof {
            // (ri + 1) % step == 0: ri = step - 1, so ri + 1 = step, step % step = 0
            assert((ri as int + 1) % (step as int) == 0) by {
                assert(ri as int + 1 == step as int);
            };

            // ds_inner_inv: no pairs processed yet (ri = step-1)
            assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
            implies ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds)
            by {
                assert(data@[j] as int == prev_ds[j]);
                lemma_no_pairs_processed_initially(j, stride as int, step as int);
            }
        }

        while ri < n
            invariant
                data@.len() == n as nat,
                stride as nat == pow2((total_levels - dk - 1) as nat),
                step == 2 * stride,
                stride > 0,
                dk < levels,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                total_levels > 0,
                prev_ds == blelloch_downsweep_state(original_int, n as nat, total_levels, dk as nat),
                next_ds == blelloch_downsweep_state(original_int, n as nat, total_levels, (dk + 1) as nat),
                blelloch_downsweep_invariant(original_int, n as nat, total_levels, dk as nat),
                ri >= step - 1,
                ri < n ==> ri >= stride,
                ri < n ==> (ri + 1) % (step as int) == 0,
                // All positions: match next_ds if processed, prev_ds otherwise
                forall|j: int| #![trigger data@[j]] 0 <= j < n as int ==>
                    ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds),
            decreases n - ri,
        {
            let right = ri as usize;
            let left = (ri - stride) as usize;

            // Capture old values
            let temp_right = data[right];
            let temp_left = data[left];

            proof {
                // Verify left and right are unprocessed: ri is the current right,
                // so ri >= ri means it's unprocessed. And left = ri - stride,
                // (left+1) % step == stride, and left + stride == ri >= ri, so unprocessed.
                let li = ri as int - stride as int;
                assert((li + 1) % (step as int) == stride as int) by {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((ri + 1) as int, step as int);
                    let q = ((ri + 1) as int) / (step as int);
                    assert(ri as int + 1 == step as int * q);
                    assert(li + 1 == stride as int * (2 * q - 1)) by (nonlinear_arith)
                        requires li == ri as int - stride as int,
                                 ri as int + 1 == step as int * q,
                                 step == 2 * stride;
                    assert(li + 1 == step as int * (q - 1) + stride as int) by (nonlinear_arith)
                        requires li + 1 == stride as int * (2 * q - 1),
                                 step == 2 * stride;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        li + 1, step as int, q - 1, stride as int
                    );
                };

                // ri is an unprocessed right (ri >= ri), so data[ri] == prev_ds[ri]
                // left is an unprocessed left (left + stride == ri >= ri), so data[left] == prev_ds[left]
                assert(temp_right as int == prev_ds[ri as int]);
                assert(temp_left as int == prev_ds[li]);

                // Overflow: temp_left + temp_right = next_ds[ri] which is a bounded prefix sum
                lemma_downsweep_overflow_bound(
                    original_data, original_int, n as nat, total_levels,
                    dk as nat, ri as int,
                    temp_left as int, temp_right as int,
                );
            }

            // new_left = old_right, new_right = old_left + old_right
            data.set(left, temp_right);
            data.set(right, (temp_left + temp_right));

            proof {
                let li = ri as int - stride as int;

                // Show data@[ri] == next_ds[ri]
                assert(data@[ri as int] as int == temp_left as int + temp_right as int);
                assert(data@[ri as int] as int == next_ds[ri as int]);
                // Show data@[li] == next_ds[li]
                assert(data@[li] as int == temp_right as int);
                assert(data@[li] as int == next_ds[li]);

                // For j != ri && j != li: data unchanged, old ds_inner_inv still applies
                // Since ri and li are the only modified positions, and data.set preserves other indices
            }

            // Advance to next right position
            let ghost old_ri = ri as int;
            if ri + step < n {
                ri = ri + step;
                proof {
                    let li = old_ri - stride as int;
                    // Prove (ri + 1) % step == 0
                    assert(ri as int == old_ri + step as int);
                    assert(ri as int + 1 == old_ri + 1 + step as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((old_ri + 1) as int, step as int);
                    let q = ((old_ri + 1) as int) / (step as int);
                    assert(old_ri + 1 == step as int * q);
                    assert(ri as int + 1 == step as int * (q + 1)) by (nonlinear_arith)
                        requires ri as int + 1 == old_ri + 1 + step as int,
                                 old_ri + 1 == step as int * q;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        ri as int + 1, step as int, q + 1, 0int
                    );

                    // Re-establish ds_inner_inv for new ri = old_ri + step
                    assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                    implies ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds)
                    by {
                        if j == old_ri {
                            // Right position just processed: data == next_ds
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else if j == li {
                            // Left position just processed: data == next_ds
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else {
                            // data@[j] unchanged, ds_pair_processed unchanged
                            lemma_ds_pair_processed_frame(
                                j, old_ri, ri as int, stride as int, step as int, n as int
                            );
                        }
                    }
                }
            } else {
                ri = n; // exit
                proof {
                    let li = old_ri - stride as int;
                    // Re-establish ds_inner_inv for ri = n
                    assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                    implies ds_inner_inv(data@, j, ri as int, stride as int, step as int, prev_ds, next_ds)
                    by {
                        if j == old_ri {
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else if j == li {
                            assert(data@[j] as int == next_ds[j]);
                            assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                        } else {
                            lemma_ds_pair_processed_frame(
                                j, old_ri, n as int, stride as int, step as int, n as int
                            );
                        }
                    }
                }
            }
        }

        // After inner loop: all pairs processed, data matches next_ds
        proof {
            // Show n == step * pow2(dk) for left-partner bound proofs
            let ghost num_pairs = pow2(dk as nat);
            crate::proof::swizzle_lemmas::lemma_pow2_mul((total_levels - dk) as nat, dk as nat);
            assert(n as nat == step as nat * num_pairs) by {
                assert(step as nat == pow2((total_levels - dk) as nat));
                assert((total_levels - dk) as nat + dk as nat == total_levels);
            };

            assert forall|j: int| 0 <= j < n as int
            implies data@[j] as int == next_ds[j]
            by {
                if (j + 1) % (step as int) == 0 && j >= stride as int {
                    // Right position, j < n <= ri, so processed
                    assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                } else if (j + 1) % (step as int) == stride as int {
                    // Left position: show j + stride < n (so its right partner exists)
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((j + 1) as int, step as int);
                    let q = ((j + 1) as int) / (step as int);
                    assert(j + 1 == step as int * q + stride as int);
                    // j + stride + 1 = step*(q+1)
                    let partner = j + stride as int;
                    assert(partner + 1 == step as int * (q + 1)) by (nonlinear_arith)
                        requires j + 1 == step as int * q + stride as int,
                                 partner == j + stride as int, step == 2 * stride;
                    // q+1 <= num_pairs since j+1 <= n = step * num_pairs
                    let np = num_pairs as int;
                    assert(q + 1 <= np) by (nonlinear_arith)
                        requires j + 1 <= n as int,
                                 j + 1 == step as int * q + stride as int,
                                 n as int == step as int * np,
                                 stride > 0;
                    assert(partner < n as int) by (nonlinear_arith)
                        requires partner + 1 == step as int * (q + 1),
                                 q + 1 <= np, n as int == step as int * np, step > 0;
                    assert(partner < ri as int);
                    assert(ds_pair_processed(j, ri as int, stride as int, step as int));
                } else {
                    // Not a pair position: next_ds[j] == prev_ds[j]
                    assert(!ds_pair_processed(j, ri as int, stride as int, step as int));
                    assert(data@[j] as int == prev_ds[j]);
                    assert(prev_ds[j] == next_ds[j]);
                }
            }
        }

        proof {
            use crate::proof::scan_blelloch_lemmas::lemma_blelloch_step;
            lemma_blelloch_step(original_int, n as nat, total_levels, dk as nat);
        }

        dk = dk + 1;
        if dk < levels {
            proof {
                assert(pow2((total_levels - dk - 1) as nat) == ds_stride as nat / 2) by {
                    assert(pow2((total_levels - (dk - 1) - 1) as nat) == ds_stride as nat);
                    assert((total_levels - (dk - 1) - 1) as nat == (total_levels - dk) as nat);
                    assert(pow2((total_levels - dk) as nat) == 2 * pow2((total_levels - dk - 1) as nat));
                    crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 1) as nat);
                };
            }
            ds_stride = ds_stride / 2;
        }
    }

    // ============================================================
    // FINAL: blelloch_result == exclusive_scan_int
    // ============================================================
    proof {
        use crate::proof::scan_blelloch_lemmas::lemma_blelloch_correct;
        lemma_blelloch_correct(original_int, n as nat, total_levels);
        // blelloch_result[j] == exclusive_scan::<int>(original_int)[j]
        // exclusive_scan_int(original_data) = exclusive_scan::<int>(as_int_seq(original_data))
        //                                   = exclusive_scan::<int>(original_int)
        assert forall|j: int| 0 <= j < n as int
        implies data@[j] as int == exclusive_scan_int(original_data)[j]
        by {
            assert(data@[j] as int == blelloch_downsweep_state(original_int, n as nat, total_levels, total_levels)[j]);
            assert(blelloch_result(original_int, n as nat, total_levels)[j] == exclusive_scan::<int>(original_int)[j]);
        }
    }
}

// ============================================================
// Brent-Kung inclusive scan
// ============================================================

/// Whether position j is active at Brent-Kung down-sweep level with given stride.
/// Active = (j+1) is an odd multiple of stride, and j >= stride.
pub open spec fn bk_active(j: int, stride: int, step: int) -> bool {
    (j + 1) % step == stride && j >= stride
}

/// Whether position j has been processed in the Brent-Kung inner loop.
pub open spec fn bk_pair_processed(j: int, ri: int, stride: int, step: int) -> bool {
    bk_active(j, stride, step) && j < ri
}

/// Brent-Kung inner loop invariant: processed positions match next state, others match prev.
pub open spec fn bk_inner_inv(
    data_view: Seq<i64>, j: int, ri: int, stride: int, step: int,
    prev: Seq<int>, next: Seq<int>,
) -> bool {
    if bk_pair_processed(j, ri, stride, step) {
        data_view[j] as int == next[j]
    } else {
        data_view[j] as int == prev[j]
    }
}


/// Brent-Kung inclusive scan. In-place, modifies data.
/// O(n) work, O(2 log n) depth. Requires power-of-2 sized input.
pub fn brent_kung_inclusive_scan_exec(data: &mut Vec<i64>, n: u64)
    requires
        old(data)@.len() == n as nat,
        n > 0,
        is_power_of_2(n as nat),
        all_partial_sums_bounded(old(data)@),
        n <= i64::MAX as u64,
    ensures
        data@.len() == n as nat,
        forall|i: int| 0 <= i < n as int ==>
            data@[i] as int == inclusive_scan_int(old(data)@)[i],
{
    let ghost original_data = old(data)@;
    let ghost original_int = as_int_seq(original_data);
    let levels = log2_ceil_exec(n);
    let data_len = data.len();

    // Handle n = 1: inclusive_scan[0] = data[0]
    if n == 1 {
        proof {
            lemma_sum_single::<int>(|j: int| as_int_seq(original_data)[j], 0);
            assert forall|j: int| 0 <= j < 1 implies
                as_int_seq(original_data)[j] == original_data[j] as int by {}
            lemma_sum_congruence::<int>(
                |j: int| as_int_seq(original_data)[j],
                |j: int| original_data[j] as int,
                0, 1,
            );
        }
        return;
    }

    // n >= 2, so levels >= 1
    proof {
        lemma_pow2_log2_ceil_exact(n as nat);
    }

    let ghost total_levels = levels as nat;

    // ============================================================
    // UP-SWEEP (shared tree reduce)
    // ============================================================
    tree_reduce_in_place_exec(data, n, levels);

    // ============================================================
    // DOWN-SWEEP (Brent-Kung specific)
    // ============================================================
    // At this point, data matches tree_reduce_state(original_int, n, total_levels)
    // which is bk_downsweep_state(original_int, n, total_levels, 0).

    proof {
        use crate::proof::scan_brent_kung_lemmas::*;
        lemma_bk_downsweep_base(original_int, n as nat, total_levels);
    }

    if levels <= 1 {
        // n == 2, levels == 1, no down-sweep needed (0 iterations of k < levels - 1)
        // bk_result = bk_downsweep_state at k = 0 = tree_reduce_state
        // For n=2: tree_reduce_state[0] = data[0], tree_reduce_state[1] = data[0]+data[1]
        // inclusive_scan[0] = data[0], inclusive_scan[1] = data[0]+data[1] ✓
        proof {
            use crate::proof::scan_brent_kung_lemmas::*;
            lemma_bk_correct(original_int, n as nat, total_levels);
            let result = crate::scan_brent_kung::bk_result(original_int, n as nat, total_levels);
            assert forall|j: int| 0 <= j < n as int
            implies data@[j] as int == inclusive_scan_int(original_data)[j]
            by {
                assert(data@[j] as int == tree_reduce_state(original_int, n as nat, total_levels)[j]);
                assert forall|k: int| 0 <= k < n as int implies
                    as_int_seq(original_data)[k] == original_data[k] as int by {}
                lemma_sum_congruence::<int>(
                    |k: int| as_int_seq(original_data)[k],
                    |k: int| original_data[k] as int,
                    0, j + 1,
                );
            }
        }
        return;
    }

    // levels >= 2, run down-sweep levels 0..levels-2
    let mut dk: u64 = 0;
    let mut ds_stride: u64 = n / 4;  // pow2(total_levels - 2)
    proof {
        crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - 2) as nat);
        assert(pow2(total_levels) == 2 * pow2((total_levels - 1) as nat));
        assert(pow2((total_levels - 1) as nat) == 2 * pow2((total_levels - 2) as nat));
        assert(pow2(total_levels) == 4 * pow2((total_levels - 2) as nat)) by (nonlinear_arith)
            requires pow2(total_levels) == 2 * pow2((total_levels - 1) as nat),
                     pow2((total_levels - 1) as nat) == 2 * pow2((total_levels - 2) as nat);
        assert(ds_stride as nat == pow2((total_levels - 2) as nat)) by (nonlinear_arith)
            requires
                pow2(total_levels) == n as nat,
                pow2(total_levels) == 4 * pow2((total_levels - 2) as nat),
                ds_stride == n / 4,
                n > 1;
    }

    while dk < levels - 1
        invariant
            dk <= levels - 1,
            dk < levels - 1 ==> ds_stride as nat == pow2((total_levels - dk - 2) as nat),
            data@.len() == n as nat,
            levels as nat == log2_ceil(n as nat),
            n > 1,
            n <= i64::MAX as u64,
            n as int == data_len as int,
            is_power_of_2(n as nat),
            pow2(total_levels) == n as nat,
            all_partial_sums_bounded(original_data),
            original_data.len() == n as nat,
            original_int == as_int_seq(original_data),
            total_levels == levels as nat,
            total_levels > 1,
            crate::scan_brent_kung::bk_downsweep_invariant(original_int, n as nat, total_levels, dk as nat),
            forall|j: int| 0 <= j < n as int ==>
                data@[j] as int == crate::scan_brent_kung::bk_downsweep_state(
                    original_int, n as nat, total_levels, dk as nat)[j],
        decreases levels - 1 - dk,
    {
        let ghost prev_bk = crate::scan_brent_kung::bk_downsweep_state(
            original_int, n as nat, total_levels, dk as nat);
        let ghost next_bk = crate::scan_brent_kung::bk_downsweep_state(
            original_int, n as nat, total_levels, (dk + 1) as nat);
        let stride = ds_stride;

        proof {
            crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 2) as nat);
            assert(pow2((total_levels - dk - 1) as nat) == 2 * pow2((total_levels - dk - 2) as nat));
            crate::proof::swizzle_lemmas::lemma_pow2_monotone(
                (total_levels - dk - 1) as nat, total_levels);
            assert(2 * stride as nat <= n as nat);
        }

        let step: u64 = 2 * stride;

        let mut i: u64 = 0;

        proof {
            assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
            implies bk_inner_inv(data@, j, 0, stride as int, step as int, prev_bk, next_bk)
            by {
                assert(!bk_pair_processed(j, 0, stride as int, step as int));
                assert(data@[j] as int == prev_bk[j]);
            }
        }

        while i < n
            invariant
                i <= n,
                data@.len() == n as nat,
                stride as nat == pow2((total_levels - dk - 2) as nat),
                stride > 0,
                step == 2 * stride,
                dk < levels - 1,
                levels as nat == log2_ceil(n as nat),
                n > 1,
                n <= i64::MAX as u64,
                n as int == data_len as int,
                is_power_of_2(n as nat),
                pow2(total_levels) == n as nat,
                all_partial_sums_bounded(original_data),
                original_data.len() == n as nat,
                original_int == as_int_seq(original_data),
                total_levels == levels as nat,
                total_levels > 1,
                prev_bk == crate::scan_brent_kung::bk_downsweep_state(
                    original_int, n as nat, total_levels, dk as nat),
                next_bk == crate::scan_brent_kung::bk_downsweep_state(
                    original_int, n as nat, total_levels, (dk + 1) as nat),
                crate::scan_brent_kung::bk_downsweep_invariant(
                    original_int, n as nat, total_levels, dk as nat),
                // Processed positions match next state, others match prev
                forall|j: int| #![trigger data@[j]] 0 <= j < n as int ==>
                    bk_inner_inv(data@, j, i as int, stride as int, step as int, prev_bk, next_bk),
            decreases n - i,
        {
            if (i + 1) % step == stride && i >= stride {
                // Active position: data[i] += data[i - stride]
                let partner = (i - stride) as usize;

                proof {
                    // data[i] == prev_bk[i] (not yet processed)
                    assert(!bk_pair_processed(i as int, i as int, stride as int, step as int));
                    assert(data@[i as int] as int == prev_bk[i as int]);
                    // data[partner] == ? We need prev_bk[partner]
                    // partner < i, so it may have been processed.
                    // If processed: data[partner] == next_bk[partner]
                    // If not: data[partner] == prev_bk[partner]
                    // But next_bk[partner] == prev_bk[partner] because partner is not active
                    // at this level (only positions with (j+1)%step == stride are active).
                    // Is partner active?
                    // partner + 1 = i + 1 - stride. i+1 = step*q + stride (from activity condition).
                    // partner + 1 = step*q. (partner+1) % step == 0 != stride. So partner is NOT active.
                    // So next_bk[partner] == prev_bk[partner].
                    // Therefore data[partner] == prev_bk[partner] regardless of processing status.
                    let pi = partner as int;
                    assert(pi + 1 == i as int + 1 - stride as int);
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod((i + 1) as int, step as int);
                    let q = ((i + 1) as int) / (step as int);
                    assert(i as int + 1 == step as int * q + stride as int);
                    assert(pi + 1 == step as int * q) by (nonlinear_arith)
                        requires pi + 1 == i as int + 1 - stride as int,
                                 i as int + 1 == step as int * q + stride as int;
                    assert(pi + 1 == q * step as int) by (nonlinear_arith)
                        requires pi + 1 == step as int * q;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                        pi + 1, step as int, q, 0
                    );
                    assert((pi + 1) % (step as int) == 0);
                    assert((pi + 1) % (step as int) != stride as int) by (nonlinear_arith)
                        requires (pi + 1) % (step as int) == 0, stride > 0;
                    assert(!bk_active(pi, stride as int, step as int));
                    assert(next_bk[pi] == prev_bk[pi]);

                    // If partner was processed: data == next_bk == prev_bk ✓
                    // If not: data == prev_bk ✓

                    // Overflow: next_bk[i] is a prefix sum of original data (bounded)
                    // next_bk[i] = prev_bk[i] + prev_bk[partner] by BK definition
                    // By BK invariant at dk+1: next_bk[i] = bk_expected(data, n, total_levels, dk+1, i)
                    // bk_expected = sum(original_int, 0, i+1) = partial_sum(original_data, 0, i+1)
                    crate::proof::scan_brent_kung_lemmas::lemma_bk_downsweep_step(
                        original_int, n as nat, total_levels, dk as nat);
                    let next_val = next_bk[i as int];
                    // next_bk[i] = sum(original_int, 0, i+1) since (i+1)%stride==0
                    assert((i as int + 1) % (stride as int) == 0) by {
                        assert(i as int + 1 == step as int * q + stride as int);
                        assert(i as int + 1 == stride as int * (2 * q + 1)) by (nonlinear_arith)
                            requires i as int + 1 == step as int * q + stride as int, step == 2 * stride;
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                            i as int + 1, stride as int, 2 * q + 1, 0
                        );
                    };
                    // Bridge to partial_sum for overflow
                    let hi = i as int + 1;
                    assert forall|k: int| 0 <= k < hi implies
                        original_int[k] == original_data[k] as int by {}
                    lemma_sum_congruence::<int>(
                        |k: int| original_int[k],
                        |k: int| original_data[k] as int,
                        0, hi,
                    );
                    assert(partial_sum(original_data, 0, hi) == next_val);
                }

                let val = data[i as usize] + data[partner];
                data.set(i as usize, val);
            }

            proof {
                // Re-establish invariant for all j
                assert forall|j: int| #![trigger data@[j]] 0 <= j < n as int
                implies bk_inner_inv(data@, j, (i + 1) as int, stride as int, step as int, prev_bk, next_bk)
                by {
                    if j == i as int {
                        if bk_active(j, stride as int, step as int) {
                            // Just processed: data == next_bk
                            assert(bk_pair_processed(j, (i + 1) as int, stride as int, step as int));
                        } else {
                            // Not active, unchanged
                            assert(!bk_pair_processed(j, (i + 1) as int, stride as int, step as int));
                        }
                    } else {
                        // j < i: bk_pair_processed(j, i+1) == bk_pair_processed(j, i)
                        // since only j == i could become newly processed
                        if bk_active(i as int, stride as int, step as int) && j < i as int {
                            // j was either already processed or not
                            // bk_pair_processed(j, i+1) iff bk_active(j) && j < i+1
                            // bk_pair_processed(j, i)   iff bk_active(j) && j < i
                            // j < i < i+1, so both are the same for j < i
                        }
                        // j > i: unchanged, not processed at either i or i+1
                    }
                }
            }

            i = i + 1;
        }

        // After inner loop: all active positions processed, data matches next_bk
        proof {
            assert forall|j: int| 0 <= j < n as int
            implies data@[j] as int == next_bk[j]
            by {
                if bk_active(j, stride as int, step as int) {
                    assert(bk_pair_processed(j, n as int, stride as int, step as int));
                } else {
                    assert(!bk_pair_processed(j, n as int, stride as int, step as int));
                    assert(next_bk[j] == prev_bk[j]);
                }
            }

            crate::proof::scan_brent_kung_lemmas::lemma_bk_downsweep_step(
                original_int, n as nat, total_levels, dk as nat);
        }

        dk = dk + 1;
        if dk < levels - 1 {
            proof {
                assert(pow2((total_levels - dk - 2) as nat) == ds_stride as nat / 2) by {
                    assert(pow2((total_levels - (dk - 1) - 2) as nat) == ds_stride as nat);
                    assert((total_levels - (dk - 1) - 2) as nat == (total_levels - dk - 1) as nat);
                    assert(pow2((total_levels - dk - 1) as nat) == 2 * pow2((total_levels - dk - 2) as nat));
                    crate::proof::swizzle_lemmas::lemma_pow2_positive((total_levels - dk - 2) as nat);
                };
            }
            ds_stride = ds_stride / 2;
        }
    }

    // ============================================================
    // FINAL: bk_result == inclusive_scan_int
    // ============================================================
    proof {
        use crate::proof::scan_brent_kung_lemmas::lemma_bk_correct;
        lemma_bk_correct(original_int, n as nat, total_levels);
        let result = crate::scan_brent_kung::bk_result(original_int, n as nat, total_levels);

        assert forall|j: int| 0 <= j < n as int
        implies data@[j] as int == inclusive_scan_int(original_data)[j]
        by {
            assert(data@[j] as int == crate::scan_brent_kung::bk_downsweep_state(
                original_int, n as nat, total_levels, (total_levels - 1) as nat)[j]);
            assert(result[j] == inclusive_scan::<int>(original_int)[j]);
            // Bridge inclusive_scan(original_int) to inclusive_scan_int(original_data)
            assert forall|k: int| 0 <= k < n as int implies
                as_int_seq(original_data)[k] == original_data[k] as int by {}
            lemma_sum_congruence::<int>(
                |k: int| as_int_seq(original_data)[k],
                |k: int| original_data[k] as int,
                0, j + 1,
            );
        }
    }
}

} // verus!
