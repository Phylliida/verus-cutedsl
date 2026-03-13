use vstd::prelude::*;
use crate::contraction::*;
use super::*;

verus! {

/// Runtime contraction spec: concrete representation.
pub struct RuntimeContractionSpec {
    pub batch_modes_a: Vec<u64>,
    pub batch_modes_b: Vec<u64>,
    pub contraction_modes_a: Vec<u64>,
    pub contraction_modes_b: Vec<u64>,
    pub free_modes_a: Vec<u64>,
    pub free_modes_b: Vec<u64>,
}

impl View for RuntimeContractionSpec {
    type V = ContractionSpec;
    open spec fn view(&self) -> ContractionSpec {
        ContractionSpec {
            batch_modes_a: shape_to_nat_seq(self.batch_modes_a@),
            batch_modes_b: shape_to_nat_seq(self.batch_modes_b@),
            contraction_modes_a: shape_to_nat_seq(self.contraction_modes_a@),
            contraction_modes_b: shape_to_nat_seq(self.contraction_modes_b@),
            free_modes_a: shape_to_nat_seq(self.free_modes_a@),
            free_modes_b: shape_to_nat_seq(self.free_modes_b@),
        }
    }
}

impl RuntimeContractionSpec {
    /// Well-formedness: paired mode lists have equal lengths.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.batch_modes_a.len() == self.batch_modes_b.len()
        &&& self.contraction_modes_a.len() == self.contraction_modes_b.len()
    }
}

/// Helper: check all elements of modes are < rank.
/// Ensures both u64-level and nat-level postconditions for trigger compatibility.
fn check_modes_in_range(modes: &Vec<u64>, rank: u64) -> (result: bool)
    ensures
        result == (forall|i: nat| i < modes.len() ==> (#[trigger] modes@[i as int]) < rank),
        result == (forall|i: nat| i < shape_to_nat_seq(modes@).len()
            ==> #[trigger] shape_to_nat_seq(modes@)[i as int] < rank as nat),
{
    let mut i: usize = 0;
    while i < modes.len()
        invariant
            0 <= i <= modes.len(),
            forall|j: nat| j < i ==> (#[trigger] modes@[j as int]) < rank,
        decreases modes.len() - i,
    {
        if modes[i] >= rank {
            proof {
                // Explicit counterexample for the nat-level forall
                let wi = i as nat;
                assert(shape_to_nat_seq(modes@)[wi as int] == modes@[wi as int] as nat);
                assert(modes@[wi as int] >= rank);
                assert(shape_to_nat_seq(modes@)[wi as int] >= rank as nat);
                assert(wi < shape_to_nat_seq(modes@).len());
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert forall|j: nat| j < shape_to_nat_seq(modes@).len()
        implies #[trigger] shape_to_nat_seq(modes@)[j as int] < rank as nat
        by {
            assert(modes@[j as int] < rank);
        };
    }
    true
}

/// Validate a contraction spec at runtime.
pub fn validate_contraction(
    spec: &RuntimeContractionSpec,
    a_rank: u64, b_rank: u64,
) -> (result: bool)
    requires
        spec.wf_spec(),
        spec.batch_modes_a.len() + spec.contraction_modes_a.len() + spec.free_modes_a.len() <= u64::MAX as nat,
        spec.batch_modes_b.len() + spec.contraction_modes_b.len() + spec.free_modes_b.len() <= u64::MAX as nat,
    ensures result == contraction_mode_sets_valid(&spec@, a_rank as nat, b_rank as nat),
{
    if spec.batch_modes_a.len() != spec.batch_modes_b.len() {
        return false;
    }
    if spec.contraction_modes_a.len() != spec.contraction_modes_b.len() {
        return false;
    }

    let ba_len = spec.batch_modes_a.len() as u64;
    let ca_len = spec.contraction_modes_a.len() as u64;
    let fa_len = spec.free_modes_a.len() as u64;
    let bb_len = spec.batch_modes_b.len() as u64;
    let cb_len = spec.contraction_modes_b.len() as u64;
    let fb_len = spec.free_modes_b.len() as u64;

    let total_a = ba_len + ca_len + fa_len;
    let total_b = bb_len + cb_len + fb_len;
    if total_a != a_rank || total_b != b_rank {
        return false;
    }

    // Compute all range checks without early returns
    let ba_in = check_modes_in_range(&spec.batch_modes_a, a_rank);
    let ca_in = check_modes_in_range(&spec.contraction_modes_a, a_rank);
    let fa_in = check_modes_in_range(&spec.free_modes_a, a_rank);
    let bb_in = check_modes_in_range(&spec.batch_modes_b, b_rank);
    let cb_in = check_modes_in_range(&spec.contraction_modes_b, b_rank);
    let fb_in = check_modes_in_range(&spec.free_modes_b, b_rank);

    let all_in = ba_in && ca_in && fa_in && bb_in && cb_in && fb_in;

    proof {
        // Bridge lengths: shape_to_nat_seq preserves length
        let sv = spec@;
        assert(sv.batch_modes_a.len() == spec.batch_modes_a@.len());
        assert(sv.batch_modes_b.len() == spec.batch_modes_b@.len());
        assert(sv.contraction_modes_a.len() == spec.contraction_modes_a@.len());
        assert(sv.contraction_modes_b.len() == spec.contraction_modes_b@.len());
        assert(sv.free_modes_a.len() == spec.free_modes_a@.len());
        assert(sv.free_modes_b.len() == spec.free_modes_b@.len());

        // Rank coverage
        assert(sv.batch_modes_a.len() + sv.contraction_modes_a.len() + sv.free_modes_a.len() == a_rank as nat);
        assert(sv.batch_modes_b.len() + sv.contraction_modes_b.len() + sv.free_modes_b.len() == b_rank as nat);
    }

    all_in
}

/// Gather shape values at given mode indices.
pub fn gather_shape_exec(
    shape: &Vec<u64>, modes: &Vec<u64>,
) -> (result: Vec<u64>)
    requires
        forall|i: nat| i < modes.len() ==> (#[trigger] modes@[i as int] as nat) < shape.len(),
    ensures
        result.len() == modes.len(),
        forall|i: nat| i < modes.len() ==>
            (#[trigger] result@[i as int]) as nat == gather_shape(
                &shape_to_nat_seq(shape@), &shape_to_nat_seq(modes@))[i as int],
{
    let mut out: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < modes.len()
        invariant
            0 <= i <= modes.len(),
            out.len() == i,
            forall|j: nat| j < i ==>
                (#[trigger] out@[j as int]) as nat == gather_shape(
                    &shape_to_nat_seq(shape@), &shape_to_nat_seq(modes@))[j as int],
            forall|j: nat| j < modes.len() ==> (#[trigger] modes@[j as int] as nat) < shape.len(),
        decreases modes.len() - i,
    {
        let mode_idx = modes[i] as usize;
        let val = shape[mode_idx];
        out.push(val);
        i = i + 1;
    }
    out
}

/// Concatenate three Vec<u64>s.
fn concat3(a: &Vec<u64>, b: &Vec<u64>, c: &Vec<u64>) -> (result: Vec<u64>)
    ensures
        result.len() == a.len() + b.len() + c.len(),
        forall|j: nat| j < a.len() ==> (#[trigger] result@[j as int]) == a@[j as int],
        forall|j: nat| j < b.len() ==> (#[trigger] result@[(a.len() + j) as int]) == b@[j as int],
        forall|j: nat| j < c.len() ==> (#[trigger] result@[(a.len() + b.len() + j) as int]) == c@[j as int],
{
    let mut result: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: nat| j < i ==> (#[trigger] result@[j as int]) == a@[j as int],
        decreases a.len() - i,
    {
        result.push(a[i]);
        i = i + 1;
    }
    let a_len = result.len();

    i = 0;
    while i < b.len()
        invariant
            0 <= i <= b.len(),
            result.len() == a_len + i,
            a_len == a.len(),
            forall|j: nat| j < a_len ==> (#[trigger] result@[j as int]) == a@[j as int],
            forall|j: nat| j < i ==> (#[trigger] result@[(a_len + j) as int]) == b@[j as int],
        decreases b.len() - i,
    {
        result.push(b[i]);
        i = i + 1;
    }
    let ab_len = result.len();

    i = 0;
    while i < c.len()
        invariant
            0 <= i <= c.len(),
            result.len() == ab_len + i,
            a_len == a.len(),
            ab_len == a_len + b.len(),
            forall|j: nat| j < a_len ==> (#[trigger] result@[j as int]) == a@[j as int],
            forall|j: nat| j < b.len() ==> (#[trigger] result@[(a_len + j) as int]) == b@[j as int],
            forall|j: nat| j < i ==> (#[trigger] result@[(ab_len + j) as int]) == c@[j as int],
        decreases c.len() - i,
    {
        result.push(c[i]);
        i = i + 1;
    }

    result
}

/// Compute contraction output shape at runtime.
pub fn contraction_output_shape_exec(
    spec: &RuntimeContractionSpec,
    a_shape: &Vec<u64>, b_shape: &Vec<u64>,
) -> (result: Vec<u64>)
    requires
        spec.wf_spec(),
        contraction_admissible(&spec@, &shape_to_nat_seq(a_shape@), &shape_to_nat_seq(b_shape@)),
    ensures
        shape_to_nat_seq(result@) =~= contraction_output_shape(
            &spec@, &shape_to_nat_seq(a_shape@), &shape_to_nat_seq(b_shape@)),
{
    proof {
        let sv = spec@;
        let as_ = shape_to_nat_seq(a_shape@);
        let bs_ = shape_to_nat_seq(b_shape@);
        assert(contraction_mode_sets_valid(&sv, as_.len(), bs_.len()));
        assert forall|i: nat| i < spec.batch_modes_a.len()
        implies (#[trigger] spec.batch_modes_a@[i as int] as nat) < a_shape.len()
        by { assert(sv.batch_modes_a[i as int] < as_.len()); };
        assert forall|i: nat| i < spec.free_modes_a.len()
        implies (#[trigger] spec.free_modes_a@[i as int] as nat) < a_shape.len()
        by { assert(sv.free_modes_a[i as int] < as_.len()); };
        assert forall|i: nat| i < spec.free_modes_b.len()
        implies (#[trigger] spec.free_modes_b@[i as int] as nat) < b_shape.len()
        by { assert(sv.free_modes_b[i as int] < bs_.len()); };
    }

    let batch = gather_shape_exec(a_shape, &spec.batch_modes_a);
    let free_a = gather_shape_exec(a_shape, &spec.free_modes_a);
    let free_b = gather_shape_exec(b_shape, &spec.free_modes_b);

    let result = concat3(&batch, &free_a, &free_b);

    proof {
        let spec_out = contraction_output_shape(
            &spec@, &shape_to_nat_seq(a_shape@), &shape_to_nat_seq(b_shape@));
        let batch_spec = gather_shape(&shape_to_nat_seq(a_shape@), &spec@.batch_modes_a);
        let free_a_spec = gather_shape(&shape_to_nat_seq(a_shape@), &spec@.free_modes_a);
        let free_b_spec = gather_shape(&shape_to_nat_seq(b_shape@), &spec@.free_modes_b);

        assert(spec_out =~= batch_spec.add(free_a_spec).add(free_b_spec));

        let bl = batch.len();
        let fl = free_a.len();
        let cl = free_b.len();

        assert forall|j: int| 0 <= j < shape_to_nat_seq(result@).len()
        implies #[trigger] shape_to_nat_seq(result@)[j] == spec_out[j]
        by {
            if j < bl as int {
                assert(result@[j] == batch@[j]);
                assert(batch@[j] as nat == batch_spec[j]);
            } else if j < (bl + fl) as int {
                let k = (j - bl as int) as nat;
                assert(result@[(bl + k) as int] == free_a@[k as int]);
                assert(result@[j] == free_a@[k as int]);
                assert(free_a@[k as int] as nat == free_a_spec[k as int]);
                assert(spec_out[j] == batch_spec.add(free_a_spec).add(free_b_spec)[j]);
                assert(batch_spec.add(free_a_spec)[j] == free_a_spec[k as int]);
            } else {
                let k = (j - bl as int - fl as int) as nat;
                assert(result@[(bl + fl + k) as int] == free_b@[k as int]);
                assert(result@[j] == free_b@[k as int]);
                assert(free_b@[k as int] as nat == free_b_spec[k as int]);
                let combined = batch_spec.add(free_a_spec);
                assert(combined.add(free_b_spec)[j] == free_b_spec[k as int]);
            }
        };
    }

    result
}

/// Helper: compare two Vec<u64> for element-wise equality.
fn vec_eq(a: &Vec<u64>, b: &Vec<u64>) -> (result: bool)
    ensures
        result == (a@ =~= b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            forall|j: nat| j < i ==> a@[j as int] == b@[j as int],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        i = i + 1;
    }
    assert(a@ =~= b@);
    true
}

/// Compute gathered_product at runtime.
///
/// gathered_product(shape, modes) is the product of shape[modes[i]] for all i.
pub fn gathered_product_exec(
    shape: &Vec<u64>, modes: &Vec<u64>,
) -> (result: u64)
    requires
        forall|i: nat| i < modes.len() ==> (#[trigger] modes@[i as int] as nat) < shape.len(),
        forall|i: nat| i < shape.len() ==> (#[trigger] shape@[i as int]) > 0u64,
        gathered_product(&shape_to_nat_seq(shape@), &shape_to_nat_seq(modes@)) <= u64::MAX as nat,
    ensures
        result as nat == gathered_product(&shape_to_nat_seq(shape@), &shape_to_nat_seq(modes@)),
{
    let sn = Ghost(shape_to_nat_seq(shape@));
    let mn = Ghost(shape_to_nat_seq(modes@));
    let mut acc: u64 = 1;
    let mut i: usize = 0;
    while i < modes.len()
        invariant
            0 <= i <= modes.len(),
            sn@ == shape_to_nat_seq(shape@),
            mn@ == shape_to_nat_seq(modes@),
            acc as nat == gathered_product(&sn@, &mn@.take(i as int)),
            gathered_product(&sn@, &mn@) <= u64::MAX as nat,
            forall|k: nat| k < modes.len() ==> (#[trigger] modes@[k as int] as nat) < shape.len(),
            forall|k: nat| k < shape.len() ==> (#[trigger] shape@[k as int]) > 0u64,
        decreases modes.len() - i,
    {
        let mode_idx = modes[i] as usize;
        let val = shape[mode_idx];
        proof {
            let ti = mn@.take(i as int);
            let ti1 = mn@.take((i + 1) as int);
            assert(ti1.len() > 0);
            assert(ti1.last() == mn@[i as int]);
            assert(ti1.drop_last() =~= ti);

            // Bridge val to spec level
            assert(mn@[i as int] == modes@[i as int] as nat);
            assert(sn@[mn@[i as int] as int] == shape@[modes@[i as int] as int] as nat);
            assert(val as nat == sn@[mn@[i as int] as int]);

            // Prove shapes positive at nat level for monotonicity
            assert forall|k: nat| k < sn@.len()
            implies (#[trigger] sn@[k as int]) > 0nat
            by {
                assert(shape@[k as int] > 0u64);
            };
            lemma_gathered_product_monotone(&sn@, &mn@, i as nat);
            // gp(modes.take(i+1)) <= gp(modes) <= u64::MAX
            let gp_i1 = gathered_product(&sn@, &ti1);
            assert(gp_i1 == sn@[mn@[i as int] as int] * gathered_product(&sn@, &ti));
            assert(gp_i1 == (val as nat) * (acc as nat));
            assert(gp_i1 <= u64::MAX as nat);
        }
        acc = acc * val;
        i = i + 1;
    }
    proof {
        assert(mn@.take(modes@.len() as int) =~= mn@);
    }
    acc
}

/// gathered_product of a prefix is <= gathered_product of the whole.
proof fn lemma_gathered_product_monotone(
    shape: &Seq<nat>, modes: &Seq<nat>, k: nat,
)
    requires
        k < modes.len(),
        forall|i: nat| i < modes.len() ==> (#[trigger] modes[i as int]) < shape.len(),
        forall|i: nat| i < shape.len() ==> (#[trigger] shape[i as int]) > 0nat,
    ensures
        gathered_product(shape, &modes.take((k + 1) as int))
        <= gathered_product(shape, modes),
    decreases modes.len() - k,
{
    if k + 1 == modes.len() {
        assert(modes.take((k + 1) as int) =~= *modes);
    } else {
        assert(modes.drop_last().take((k + 1) as int)
            =~= modes.take((k + 1) as int));
        // Modes in range for drop_last
        assert forall|j: nat| j < modes.drop_last().len()
        implies (#[trigger] modes.drop_last()[j as int]) < shape.len()
        by {
            assert(modes[j as int] < shape.len());
            assert(modes.drop_last()[j as int] == modes[j as int]);
        };
        lemma_gathered_product_monotone(shape, &modes.drop_last(), k);
        let last_val = shape[modes.last() as int];
        assert(last_val >= 1nat);
        let gp_dl = gathered_product(shape, &modes.drop_last());
        assert(gathered_product(shape, modes) == last_val * gp_dl);
        assert(gp_dl <= last_val * gp_dl) by (nonlinear_arith)
            requires last_val >= 1nat, gp_dl >= 0nat;
    }
}

/// Compute contraction_reduction_size at runtime.
pub fn contraction_reduction_size_exec(
    spec: &RuntimeContractionSpec,
    a_shape: &Vec<u64>,
) -> (result: u64)
    requires
        forall|i: nat| i < spec.contraction_modes_a.len()
            ==> (#[trigger] spec.contraction_modes_a@[i as int] as nat) < a_shape.len(),
        forall|i: nat| i < a_shape.len() ==> (#[trigger] a_shape@[i as int]) > 0u64,
        gathered_product(
            &shape_to_nat_seq(a_shape@),
            &shape_to_nat_seq(spec.contraction_modes_a@),
        ) <= u64::MAX as nat,
    ensures
        result as nat == contraction_reduction_size(&spec@, &shape_to_nat_seq(a_shape@)),
{
    gathered_product_exec(a_shape, &spec.contraction_modes_a)
}

/// Check contraction_shapes_match at runtime.
fn check_shapes_match(
    spec: &RuntimeContractionSpec,
    a_shape: &Vec<u64>, b_shape: &Vec<u64>,
) -> (result: bool)
    requires
        contraction_mode_sets_valid(&spec@, a_shape.len() as nat, b_shape.len() as nat),
        spec.wf_spec(),
    ensures
        result == contraction_shapes_match(&spec@, &shape_to_nat_seq(a_shape@), &shape_to_nat_seq(b_shape@)),
{
    proof {
        let sv = spec@;
        let as_ = shape_to_nat_seq(a_shape@);
        let bs_ = shape_to_nat_seq(b_shape@);
        // batch modes in range
        assert forall|i: nat| i < spec.batch_modes_a.len()
        implies (#[trigger] spec.batch_modes_a@[i as int] as nat) < a_shape.len()
        by { assert(sv.batch_modes_a[i as int] < as_.len()); };
        assert forall|i: nat| i < spec.batch_modes_b.len()
        implies (#[trigger] spec.batch_modes_b@[i as int] as nat) < b_shape.len()
        by { assert(sv.batch_modes_b[i as int] < bs_.len()); };
        // contraction modes in range
        assert forall|i: nat| i < spec.contraction_modes_a.len()
        implies (#[trigger] spec.contraction_modes_a@[i as int] as nat) < a_shape.len()
        by { assert(sv.contraction_modes_a[i as int] < as_.len()); };
        assert forall|i: nat| i < spec.contraction_modes_b.len()
        implies (#[trigger] spec.contraction_modes_b@[i as int] as nat) < b_shape.len()
        by { assert(sv.contraction_modes_b[i as int] < bs_.len()); };
    }

    let batch_a = gather_shape_exec(a_shape, &spec.batch_modes_a);
    let batch_b = gather_shape_exec(b_shape, &spec.batch_modes_b);
    let contr_a = gather_shape_exec(a_shape, &spec.contraction_modes_a);
    let contr_b = gather_shape_exec(b_shape, &spec.contraction_modes_b);

    let batch_match = vec_eq(&batch_a, &batch_b);
    let contr_match = vec_eq(&contr_a, &contr_b);

    proof {
        let sv = spec@;
        let as_ = shape_to_nat_seq(a_shape@);
        let bs_ = shape_to_nat_seq(b_shape@);
        let batch_a_spec = gather_shape(&as_, &sv.batch_modes_a);
        let batch_b_spec = gather_shape(&bs_, &sv.batch_modes_b);
        let contr_a_spec = gather_shape(&as_, &sv.contraction_modes_a);
        let contr_b_spec = gather_shape(&bs_, &sv.contraction_modes_b);

        // Bridge: batch_a@ =~= batch_b@ ↔ batch_a_spec =~= batch_b_spec
        if batch_match {
            assert(batch_a@ =~= batch_b@);
            assert forall|j: int| 0 <= j < batch_a_spec.len()
            implies batch_a_spec[j] == batch_b_spec[j]
            by {
                assert(batch_a@[j] as nat == batch_a_spec[j]);
                assert(batch_b@[j] as nat == batch_b_spec[j]);
                assert(batch_a@[j] == batch_b@[j]);
            };
            assert(batch_a_spec =~= batch_b_spec);
        } else {
            // batch_a@ !=~= batch_b@
            // Need: batch_a_spec !=~= batch_b_spec
            if batch_a.len() != batch_b.len() {
                assert(batch_a_spec.len() != batch_b_spec.len());
            } else {
                // Same length, some element differs
                // batch_a@ != batch_b@ and same len → exists witness
                let wit = choose|j: int| 0 <= j < batch_a@.len() && batch_a@[j] != batch_b@[j];
                assert(batch_a@[wit] != batch_b@[wit]);
                assert(batch_a@[wit] as nat == batch_a_spec[wit]);
                assert(batch_b@[wit] as nat == batch_b_spec[wit]);
                assert(batch_a_spec[wit] != batch_b_spec[wit]);
            }
        }

        if contr_match {
            assert(contr_a@ =~= contr_b@);
            assert forall|j: int| 0 <= j < contr_a_spec.len()
            implies contr_a_spec[j] == contr_b_spec[j]
            by {
                assert(contr_a@[j] as nat == contr_a_spec[j]);
                assert(contr_b@[j] as nat == contr_b_spec[j]);
                assert(contr_a@[j] == contr_b@[j]);
            };
            assert(contr_a_spec =~= contr_b_spec);
        } else {
            if contr_a.len() != contr_b.len() {
                assert(contr_a_spec.len() != contr_b_spec.len());
            } else {
                let wit = choose|j: int| 0 <= j < contr_a@.len() && contr_a@[j] != contr_b@[j];
                assert(contr_a@[wit] != contr_b@[wit]);
                assert(contr_a@[wit] as nat == contr_a_spec[wit]);
                assert(contr_b@[wit] as nat == contr_b_spec[wit]);
                assert(contr_a_spec[wit] != contr_b_spec[wit]);
            }
        }
    }

    batch_match && contr_match
}

/// Check contraction_admissible at runtime.
pub fn contraction_admissible_exec(
    spec: &RuntimeContractionSpec,
    a_shape: &Vec<u64>, b_shape: &Vec<u64>,
) -> (result: bool)
    requires
        spec.wf_spec(),
        spec.batch_modes_a.len() + spec.contraction_modes_a.len() + spec.free_modes_a.len() <= u64::MAX as nat,
        spec.batch_modes_b.len() + spec.contraction_modes_b.len() + spec.free_modes_b.len() <= u64::MAX as nat,
    ensures
        result == contraction_admissible(&spec@, &shape_to_nat_seq(a_shape@), &shape_to_nat_seq(b_shape@)),
{
    let a_rank = a_shape.len() as u64;
    let b_rank = b_shape.len() as u64;

    let valid = validate_contraction(spec, a_rank, b_rank);
    if !valid {
        return false;
    }

    check_shapes_match(spec, a_shape, b_shape)
}

} // verus!
