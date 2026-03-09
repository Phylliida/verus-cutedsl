use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use super::*;
use super::shape_helpers::*;

verus! {

/// Helper: partial dot product at step k is within i64 range.
pub open spec fn partial_dot_in_range(coords: Seq<nat>, strides: Seq<int>, k: nat) -> bool {
    dot_product_nat_int(coords.take(k as int), strides.take(k as int)) >= i64::MIN as int &&
    dot_product_nat_int(coords.take(k as int), strides.take(k as int)) <= i64::MAX as int
}

/// Runtime layout: concrete Vec<u64> shape + Vec<i64> stride, with ghost LayoutSpec model.
pub struct RuntimeLayout {
    pub shape: Vec<u64>,
    pub stride: Vec<i64>,
    pub model: Ghost<LayoutSpec>,
}

impl View for RuntimeLayout {
    type V = LayoutSpec;
    open spec fn view(&self) -> LayoutSpec {
        self.model@
    }
}

impl RuntimeLayout {
    /// Well-formedness: the concrete Vecs match the ghost model, and the model is valid.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self@.valid()
        &&& self.shape@.len() == self@.shape.len()
        &&& self.stride@.len() == self@.stride.len()
        &&& self@.shape == shape_to_nat_seq(self.shape@)
        &&& self@.stride == strides_to_int_seq(self.stride@)
        &&& self@.size() <= u64::MAX as nat
    }

    /// Create a new RuntimeLayout from shape and stride vectors.
    pub fn new(shape: Vec<u64>, stride: Vec<i64>) -> (result: RuntimeLayout)
        requires
            shape@.len() == stride@.len(),
            shape_valid_u64(shape@),
            shape_size(shape_to_nat_seq(shape@)) <= u64::MAX as nat,
        ensures
            result.wf_spec(),
            result@.shape == shape_to_nat_seq(shape@),
            result@.stride == strides_to_int_seq(stride@),
    {
        let ghost model = LayoutSpec {
            shape: shape_to_nat_seq(shape@),
            stride: strides_to_int_seq(stride@),
        };
        proof {
            lemma_shape_valid_bridge(shape@);
        }
        RuntimeLayout {
            shape,
            stride,
            model: Ghost(model),
        }
    }

    /// Number of dimensions.
    pub fn rank(&self) -> (result: usize)
        requires self.wf_spec(),
        ensures result as nat == self@.rank(),
    {
        self.shape.len()
    }

    /// Total number of elements.
    pub fn size(&self) -> (result: u64)
        requires self.wf_spec(),
        ensures result as nat == self@.size(),
    {
        proof { Self::lemma_wf_shape_valid_u64(self); }
        shape_size_exec(&self.shape)
    }

    /// Bridge: wf_spec implies shape_valid_u64 on the concrete shape.
    pub proof fn lemma_wf_shape_valid_u64(s: &Self)
        requires s.wf_spec(),
        ensures shape_valid_u64(s.shape@),
    {
        assert forall|j: int| 0 <= j < s.shape@.len() implies #[trigger] s.shape@[j] > 0 by {
            assert(s@.shape[j] == shape_to_nat_seq(s.shape@)[j]);
            assert(s@.shape[j] > 0);
        }
    }

    /// Compute the memory offset for a given linear index.
    pub fn offset(&self, idx: u64) -> (result: i64)
        requires
            self.wf_spec(),
            self@.non_negative_strides(),
            (idx as nat) < self@.size(),
            self@.offset(idx as nat) >= i64::MIN as int,
            self@.offset(idx as nat) <= i64::MAX as int,
            // Each partial dot product sum fits in i64
            forall|k: nat| k <= self@.shape.len() ==>
                #[trigger] partial_dot_in_range(delinearize(idx as nat, self@.shape), self@.stride, k),
        ensures
            result as int == self@.offset(idx as nat),
    {
        proof {
            // Bridge wf_spec → shape_valid_u64
            assert(shape_valid_u64(self.shape@)) by {
                assert forall|j: int| 0 <= j < self.shape@.len() implies #[trigger] self.shape@[j] > 0 by {
                    assert(self@.shape[j] > 0);
                    assert(self@.shape[j] == shape_to_nat_seq(self.shape@)[j]);
                    assert(self.shape@[j] as nat == self@.shape[j]);
                }
            }
        }
        let coords = delinearize_exec(idx, &self.shape);

        proof {
            crate::proof::shape_lemmas::lemma_delinearize_len(idx as nat, self@.shape);
            crate::proof::shape_lemmas::lemma_delinearize_bounds(idx as nat, self@.shape);
            let spec_coords = delinearize(idx as nat, self@.shape);
            assert(shape_to_nat_seq(coords@) =~= spec_coords) by {
                assert forall|j: int| 0 <= j < coords@.len() implies
                    shape_to_nat_seq(coords@)[j] == spec_coords[j]
                by {
                    assert(coords@[j] as nat == spec_coords[j]);
                }
            }
            assert(strides_to_int_seq(self.stride@) =~= self@.stride);

            // Bridge non-negative strides to concrete Vec
            assert forall|j: int| 0 <= j < self.stride@.len() implies
                #[trigger] self.stride@[j] >= 0
            by {
                assert(self@.stride[j] >= 0);
                assert(self@.stride[j] == strides_to_int_seq(self.stride@)[j]);
            }

            // Bridge partial sums from spec to concrete coords/strides
            assert forall|k: nat| k <= coords@.len() implies
                dot_product_nat_int(
                    shape_to_nat_seq(coords@).take(k as int),
                    strides_to_int_seq(self.stride@).take(k as int)
                ) >= i64::MIN as int &&
                dot_product_nat_int(
                    shape_to_nat_seq(coords@).take(k as int),
                    strides_to_int_seq(self.stride@).take(k as int)
                ) <= i64::MAX as int
            by {
                assert(partial_dot_in_range(spec_coords, self@.stride, k));
            }
        }

        dot_product_exec(&coords, &self.stride)
    }

    /// Check if all strides are non-negative.
    pub fn has_non_negative_strides(&self) -> (result: bool)
        requires self.wf_spec(),
        ensures result == self@.non_negative_strides(),
    {
        let mut i: usize = 0;
        while i < self.stride.len()
            invariant
                0 <= i <= self.stride.len(),
                self.wf_spec(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.stride@[j] >= 0,
            decreases self.stride.len() - i,
        {
            if self.stride[i] < 0 {
                proof {
                    assert(self@.stride[i as int] < 0);
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            assert(self@.non_negative_strides()) by {
                assert forall|j: int| 0 <= j < self@.stride.len()
                    implies #[trigger] self@.stride[j] >= 0
                by {
                    assert(self.stride@[j] >= 0);
                }
            }
        }
        true
    }

    /// Check if strides are sorted (non-decreasing).
    pub fn is_sorted(&self) -> (result: bool)
        requires self.wf_spec(),
        ensures result == self@.is_sorted(),
    {
        if self.stride.len() <= 1 {
            return true;
        }
        let mut i: usize = 0;
        while i + 1 < self.stride.len()
            invariant
                0 <= i,
                i < self.stride.len(),
                self.wf_spec(),
                forall|a: int, b: int| 0 <= a < b <= i as int ==>
                    #[trigger] self@.stride[a] <= #[trigger] self@.stride[b],
            decreases self.stride.len() - i,
        {
            if self.stride[i] > self.stride[i + 1] {
                proof {
                    assert(self@.stride[i as int] > self@.stride[(i + 1) as int]);
                }
                return false;
            }
            proof {
                assert forall|a: int, b: int| 0 <= a < b <= (i + 1) as int
                    implies #[trigger] self@.stride[a] <= #[trigger] self@.stride[b]
                by {
                    if b == (i + 1) as int {
                        if a == i as int {
                        } else {
                            assert(self@.stride[a] <= self@.stride[i as int]);
                            assert(self@.stride[i as int] <= self@.stride[b]);
                        }
                    }
                }
            }
            i = i + 1;
        }
        true
    }

    /// Check tractability: for adjacent modes, (M_i * d_i) divides d_{i+1}.
    pub fn is_tractable(&self) -> (result: bool)
        requires
            self.wf_spec(),
        ensures result == self@.is_tractable(),
    {
        if self.shape.len() <= 1 {
            return true;
        }
        let n = self.shape.len();
        let mut i: usize = 0;
        while i < n - 1
            invariant
                self.wf_spec(),
                n == self.shape.len(),
                n > 1,
                0 <= i <= n - 1,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] self@.tractable_at(j),
            decreases n - 1 - i,
        {
            proof {
                assert(self@.shape[i as int] == self.shape@[i as int] as nat);
                assert(self@.stride[i as int] == self.stride@[i as int] as int);
                assert(self@.stride[(i + 1) as int] == self.stride@[(i + 1) as int] as int);
            }

            let shape_val = self.shape[i] as i128;
            let stride_val = self.stride[i] as i128;

            proof {
                assert(i128::MIN as int <= (shape_val as int) * (stride_val as int)
                    <= i128::MAX as int) by (nonlinear_arith)
                    requires
                        0 <= shape_val as int <= u64::MAX as int,
                        i64::MIN as int <= stride_val as int <= i64::MAX as int,
                ;
            }

            let product = shape_val * stride_val;
            let ghost sp = (self@.shape[i as int] as int) * self@.stride[i as int];

            proof {
                assert(product as int == sp);
            }

            if product <= 0 {
                proof {
                    assert(!self@.tractable_at(i as int));
                }
                return false;
            }

            // Use abs(stride_next) so both operands of % are non-negative
            // (Z3's EucMod bounds axiom only fires for non-negative dividend)
            let stride_next = self.stride[i + 1] as i128;
            let abs_next: i128 = if stride_next >= 0 { stride_next } else { -stride_next };
            let rem = abs_next % product;

            if rem != 0 {
                proof {
                    let s = self@.stride[(i + 1) as int];
                    assert(sp > 0);
                    assert((abs_next as int) % sp != 0);
                    assert(abs_next as int == if stride_next >= 0 { s } else { -s });

                    if self@.tractable_at(i as int) {
                        assert(s % sp == 0);
                        Self::lemma_abs_mod_zero(s, sp, abs_next as int, stride_next >= 0);
                        assert(false);
                    }
                    assert(!self@.tractable_at(i as int));
                }
                return false;
            }

            proof {
                let s = self@.stride[(i + 1) as int];
                assert(sp > 0);
                assert((abs_next as int) % sp == 0);
                assert(abs_next as int == if stride_next >= 0 { s } else { -s });

                Self::lemma_abs_mod_zero_rev(s, sp, abs_next as int, stride_next >= 0);
                assert(s % sp == 0);
                assert(self@.tractable_at(i as int));

                assert forall|j: int| 0 <= j < (i + 1) as int implies
                    #[trigger] self@.tractable_at(j)
                by {
                    if j == i as int {
                    }
                }
            }

            i = i + 1;
        }
        true
    }

    /// Helper: if a % d == 0 and abs_a == |a|, then abs_a % d == 0
    proof fn lemma_abs_mod_zero(a: int, d: int, abs_a: int, is_nonneg: bool)
        requires
            d > 0,
            a % d == 0,
            abs_a == if is_nonneg { a } else { -a },
        ensures
            abs_a % d == 0,
    {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, d);
        let q = a / d;
        assert(a == d * q + a % d);
        assert(a == d * q);
        if is_nonneg {
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q, d);
        } else {
            assert(abs_a == -a == -(d * q));
            assert(-(d * q) == (-q) * d) by (nonlinear_arith)
                requires d == d, q == q;
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(-q, d);
        }
    }

    /// Helper: if abs_a % d == 0 and abs_a == |a|, then a % d == 0
    proof fn lemma_abs_mod_zero_rev(a: int, d: int, abs_a: int, is_nonneg: bool)
        requires
            d > 0,
            abs_a % d == 0,
            abs_a == if is_nonneg { a } else { -a },
        ensures
            a % d == 0,
    {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(abs_a, d);
        let k = abs_a / d;
        assert(abs_a == d * k + abs_a % d);
        assert(abs_a == d * k);
        if is_nonneg {
            assert(a == abs_a);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k, d);
        } else {
            assert(a == -abs_a == -(d * k));
            assert(-(d * k) == (-k) * d) by (nonlinear_arith)
                requires d == d, k == k;
            assert(a == (-k) * d);
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(-k, d);
        }
    }

    /// Compute cosize (minimum codomain size) for non-negative strides.
    pub fn cosize(&self) -> (result: u64)
        requires
            self.wf_spec(),
            self@.non_negative_strides(),
            self@.cosize_nonneg() <= u64::MAX as nat,
            forall|i: int| 0 <= i < self@.shape.len() ==>
                ((self@.shape[i] - 1) as int) * self@.stride[i] <= u64::MAX as int,
        ensures
            result as nat == self@.cosize_nonneg(),
    {
        if self.shape.len() == 0 {
            return 1;
        }
        let mut sum: u64 = 0;
        let mut i: usize = 0;
        proof {
            crate::proof::offset_lemmas::lemma_cosize_equals_dot_plus_one(self@);
        }
        while i < self.shape.len()
            invariant
                0 <= i <= self.shape.len(),
                self.wf_spec(),
                self@.non_negative_strides(),
                self@.cosize_nonneg() <= u64::MAX as nat,
                forall|j: int| 0 <= j < self@.shape.len() ==>
                    ((self@.shape[j] - 1) as int) * self@.stride[j] <= u64::MAX as int,
                sum as nat <= self@.cosize_nonneg() as nat,
                sum as int == dot_product_nat_int(
                    shape_minus_one(self@.shape).take(i as int),
                    self@.stride.take(i as int)
                ),
                dot_product_nat_int(shape_minus_one(self@.shape), self@.stride) + 1
                    == self@.cosize_nonneg() as int,
            decreases self.shape.len() - i,
        {
            proof {
                lemma_shape_minus_one_len(self@.shape);
                lemma_shape_minus_one_index(self@.shape, i as nat);
                let sm = shape_minus_one(self@.shape);
                assert(sm.len() == self@.stride.len());
                lemma_dot_product_take_step_nat(sm, self@.stride, i as nat);
                lemma_dot_product_partial_le_total_nat(sm, self@.stride, (i + 1) as nat);
            }

            let s_minus_1: u64 = self.shape[i] - 1;
            let contribution: u64 = s_minus_1 * (self.stride[i] as u64);
            sum = sum + contribution;
            i = i + 1;
        }

        proof {
            lemma_shape_minus_one_len(self@.shape);
            let sm = shape_minus_one(self@.shape);
            assert(sm.len() == self@.shape.len());
            assert(sm.take(sm.len() as int) =~= sm);
            assert(self@.stride.take(self@.stride.len() as int) =~= self@.stride);
        }

        sum + 1
    }
}

// === Helper lemmas ===

/// shape_minus_one(s)[i] == (s[i] - 1) as nat
proof fn lemma_shape_minus_one_index(s: Seq<nat>, i: nat)
    requires shape_valid(s), i < s.len(),
    ensures shape_minus_one(s).len() == s.len(),
        shape_minus_one(s)[i as int] == (s[i as int] - 1) as nat,
    decreases i,
{
    lemma_shape_minus_one_len(s);
    if i == 0 {
    } else {
        let s1 = s.skip(1);
        assert(shape_valid(s1)) by {
            assert forall|j: int| 0 <= j < s1.len() implies #[trigger] s1[j] > 0 by {
                assert(s[j + 1] > 0);
            }
        }
        lemma_shape_minus_one_skip(s);
        assert(shape_minus_one(s)[i as int] == shape_minus_one(s1)[(i - 1) as int]);
        lemma_shape_minus_one_index(s1, (i - 1) as nat);
        assert(s1[(i - 1) as int] == s[i as int]);
    }
}

proof fn lemma_shape_minus_one_len(s: Seq<nat>)
    requires shape_valid(s),
    ensures shape_minus_one(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s1 = s.skip(1);
        assert(shape_valid(s1)) by {
            assert forall|j: int| 0 <= j < s1.len() implies #[trigger] s1[j] > 0 by {
                assert(s[j + 1] > 0);
            }
        }
        lemma_shape_minus_one_len(s1);
    }
}

proof fn lemma_shape_minus_one_skip(s: Seq<nat>)
    requires shape_valid(s), s.len() > 0,
    ensures ({
        let s1 = s.skip(1);
        &&& shape_minus_one(s).len() > 0
        &&& shape_minus_one(s).skip(1) =~= shape_minus_one(s1)
    }),
{
    lemma_shape_minus_one_len(s);
}

/// dot_product take-step for Seq<nat> x Seq<int> (used by cosize computation).
proof fn lemma_dot_product_take_step_nat(coords: Seq<nat>, strides: Seq<int>, i: nat)
    requires coords.len() == strides.len(), i < coords.len(),
    ensures
        dot_product_nat_int(coords.take((i + 1) as int), strides.take((i + 1) as int))
            == dot_product_nat_int(coords.take(i as int), strides.take(i as int))
                + (coords[i as int] as int) * strides[i as int],
    decreases i,
{
    let ct = coords.take((i + 1) as int);
    let st = strides.take((i + 1) as int);
    if i == 0 {
        assert(ct.first() == coords[0]);
        assert(st.first() == strides[0]);
        assert(ct.skip(1) =~= Seq::<nat>::empty());
        assert(st.skip(1) =~= Seq::<int>::empty());
        assert(coords.take(0int) =~= Seq::<nat>::empty());
        assert(strides.take(0int) =~= Seq::<int>::empty());
    } else {
        assert(ct.first() == coords[0]);
        assert(st.first() == strides[0]);
        assert(ct.skip(1) =~= coords.skip(1).take(i as int));
        assert(st.skip(1) =~= strides.skip(1).take(i as int));
        let c1 = coords.skip(1);
        let s1 = strides.skip(1);
        let ct0 = coords.take(i as int);
        let st0 = strides.take(i as int);
        assert(ct0.first() == coords[0]);
        assert(st0.first() == strides[0]);
        assert(ct0.skip(1) =~= c1.take((i - 1) as int));
        assert(st0.skip(1) =~= s1.take((i - 1) as int));
        assert(c1[(i - 1) as int] == coords[i as int]);
        assert(s1[(i - 1) as int] == strides[i as int]);
        lemma_dot_product_take_step_nat(c1, s1, (i - 1) as nat);
    }
}

/// Partial dot product with non-negative terms <= full dot product.
proof fn lemma_dot_product_partial_le_total_nat(coords: Seq<nat>, strides: Seq<int>, k: nat)
    requires
        coords.len() == strides.len(),
        k <= coords.len(),
        forall|j: int| 0 <= j < strides.len() ==> #[trigger] strides[j] >= 0,
    ensures
        dot_product_nat_int(coords.take(k as int), strides.take(k as int))
            <= dot_product_nat_int(coords, strides),
    decreases coords.len(),
{
    if coords.len() == 0 {
        assert(coords.take(k as int) =~= Seq::<nat>::empty());
        assert(strides.take(k as int) =~= Seq::<int>::empty());
    } else if k == 0 {
        assert(coords.take(0int) =~= Seq::<nat>::empty());
        assert(strides.take(0int) =~= Seq::<int>::empty());
        crate::proof::offset_lemmas::lemma_dot_product_nonneg(coords, strides);
    } else {
        let c1 = coords.skip(1);
        let s1 = strides.skip(1);
        assert forall|j: int| 0 <= j < s1.len() implies #[trigger] s1[j] >= 0 by {
            assert(strides[j + 1] >= 0);
        }
        lemma_dot_product_partial_le_total_nat(c1, s1, (k - 1) as nat);
        assert(coords.take(k as int).first() == coords[0]);
        assert(strides.take(k as int).first() == strides[0]);
        assert(coords.take(k as int).skip(1) =~= c1.take((k - 1) as int));
        assert(strides.take(k as int).skip(1) =~= s1.take((k - 1) as int));
    }
}

} // verus!

// Display/Debug outside verus! macro (external_body impls)
use std::fmt;

#[cfg(verus_keep_ghost)]
#[verifier::external]
impl fmt::Display for RuntimeLayout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, s) in self.shape.iter().enumerate() {
            if i > 0 { write!(f, ",")?; }
            write!(f, "{}", s)?;
        }
        write!(f, "):(")?;
        for (i, d) in self.stride.iter().enumerate() {
            if i > 0 { write!(f, ",")?; }
            write!(f, "{}", d)?;
        }
        write!(f, ")")
    }
}

#[cfg(verus_keep_ghost)]
#[verifier::external]
impl fmt::Debug for RuntimeLayout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
