use vstd::prelude::*;
use crate::shape::*;
use super::*;

verus! {

/// Compute shape_size at runtime: product of all shape elements.
pub fn shape_size_exec(shape: &Vec<u64>) -> (result: u64)
    requires
        shape_valid_u64(shape@),
        shape_size(shape_to_nat_seq(shape@)) <= u64::MAX as nat,
    ensures
        result as nat == shape_size(shape_to_nat_seq(shape@)),
{
    let mut result: u64 = 1;
    let mut i: usize = 0;
    let ghost spec_shape = shape_to_nat_seq(shape@);

    proof {
        crate::proof::shape_lemmas::lemma_shape_size_positive(spec_shape);
    }

    while i < shape.len()
        invariant
            0 <= i <= shape.len(),
            shape_valid_u64(shape@),
            spec_shape == shape_to_nat_seq(shape@),
            result as nat == shape_size(spec_shape.take(i as int)),
            shape_size(spec_shape.take(i as int)) <= u64::MAX as nat,
            shape_size(spec_shape) <= u64::MAX as nat,
        decreases shape.len() - i,
    {
        proof {
            lemma_shape_size_take_step(spec_shape, i as nat);
            lemma_shape_size_take_monotone(spec_shape, i as nat);
        }
        result = result * shape[i];
        i = i + 1;
    }

    proof {
        assert(spec_shape.take(shape@.len() as int) =~= spec_shape);
    }

    result
}

/// Helper: shape_size of take(i+1) = shape_size(take(i)) * s[i].
proof fn lemma_shape_size_take_step(s: Seq<nat>, i: nat)
    requires
        shape_valid(s),
        i < s.len(),
    ensures
        shape_size(s.take((i + 1) as int)) == shape_size(s.take(i as int)) * s[i as int],
    decreases i,
{
    lemma_take_shape_valid(s, (i + 1) as nat);
    let ti1 = s.take((i + 1) as int);
    let ti = s.take(i as int);
    assert(ti1.take(i as int) =~= ti);
    let tail = ti1.skip(i as int);
    assert(tail =~= seq![s[i as int]]);
    lemma_shape_size_split(ti1, i);
    // Now: shape_size(ti1) == shape_size(ti) * shape_size(tail)
    // Need: shape_size(tail) == s[i]
    let si = s[i as int];
    assert(tail.len() == 1);
    assert(tail.first() == si);
    assert(tail.skip(1) =~= Seq::<nat>::empty());
    // shape_size(tail) = tail.first() * shape_size(tail.skip(1)) = si * 1 = si
    assert(shape_size(Seq::<nat>::empty()) == 1nat);
    assert(shape_size(tail) == si * shape_size(tail.skip(1)));
    assert(shape_size(tail) == si);
}

/// Helper: shape_size(take(i+1)) <= shape_size(s) so it fits in u64.
proof fn lemma_shape_size_take_monotone(s: Seq<nat>, i: nat)
    requires
        shape_valid(s),
        i < s.len(),
        shape_size(s) <= u64::MAX as nat,
    ensures
        shape_size(s.take((i + 1) as int)) <= u64::MAX as nat,
    decreases s.len() - i,
{
    if i + 1 == s.len() {
        assert(s.take(s.len() as int) =~= s);
    } else {
        lemma_shape_size_split(s, (i + 1) as nat);
        let rest = s.skip((i + 1) as int);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0 by {
                assert(s[(j + i + 1) as int] > 0);
            }
        }
        crate::proof::shape_lemmas::lemma_shape_size_positive(rest);
        let a_val = shape_size(s.take((i + 1) as int));
        let b_val = shape_size(rest);
        assert(a_val * b_val == shape_size(s));
        assert(b_val >= 1);
        assert(a_val <= shape_size(s)) by (nonlinear_arith)
            requires a_val * b_val == shape_size(s), b_val >= 1nat, a_val >= 0nat,
        {}
    }
}

/// shape_size(s) == shape_size(take(k)) * shape_size(skip(k))
pub proof fn lemma_shape_size_split(s: Seq<nat>, k: nat)
    requires shape_valid(s), k <= s.len(),
    ensures shape_size(s) == shape_size(s.take(k as int)) * shape_size(s.skip(k as int)),
    decreases k,
{
    if k == 0 {
        assert(s.take(0int) =~= Seq::<nat>::empty());
        assert(s.skip(0int) =~= s);
    } else {
        let s1 = s.skip(1);
        assert(shape_valid(s1)) by {
            assert forall|j: int| 0 <= j < s1.len() implies #[trigger] s1[j] > 0 by {
                assert(s[j + 1] > 0);
            }
        }
        lemma_shape_size_split(s1, (k - 1) as nat);
        // IH: shape_size(s1) == shape_size(s1.take((k-1) as int)) * shape_size(s1.skip((k-1) as int))
        assert(s1.take((k - 1) as int) =~= s.take(k as int).skip(1));
        assert(s1.skip((k - 1) as int) =~= s.skip(k as int));
        // shape_size(s) = s.first() * shape_size(s1) [by def]
        assert(s.first() == s[0]);
        assert(s.len() > 0);
        // shape_size(s.take(k)) = s.take(k).first() * shape_size(s.take(k).skip(1)) [by def]
        let tk = s.take(k as int);
        assert(tk.len() > 0);
        assert(tk.first() == s[0]);
        assert(tk.skip(1) =~= s1.take((k - 1) as int));
        // So shape_size(tk) = s[0] * shape_size(s1.take(k-1))
        // And shape_size(s) = s[0] * shape_size(s1) = s[0] * shape_size(s1.take(k-1)) * shape_size(s.skip(k))
        //                    = shape_size(tk) * shape_size(s.skip(k))
        // Unfold shape_size(s): s.len() > 0, so shape_size(s) = s.first() * shape_size(s.skip(1))
        assert(s.skip(1) =~= s1);
        // shape_size(s) = s[0] * shape_size(s1) -- by def since s.len() > 0
        // Unfold shape_size(tk): tk.len() > 0 (since k >= 1), so shape_size(tk) = tk.first() * shape_size(tk.skip(1))
        // tk.first() = s[0], tk.skip(1) =~= s1.take(k-1)
        // IH gave us: shape_size(s1) = shape_size(s1.take(k-1)) * shape_size(s1.skip(k-1))
        // And s1.skip(k-1) =~= s.skip(k)
        // So shape_size(s) = s[0] * shape_size(s1.take(k-1)) * shape_size(s.skip(k))
        //                   = shape_size(tk) * shape_size(s.skip(k))
        let a_val = shape_size(s1.take((k - 1) as int));
        let b_val = shape_size(s.skip(k as int));
        assert(shape_size(s1) == a_val * b_val);
        assert(shape_size(tk) == s[0] * a_val);
        assert(s[0] * (a_val * b_val) == (s[0] * a_val) * b_val) by (nonlinear_arith) {}
    }
}

/// Delinearize a linear index into per-dimension coordinates at runtime.
pub fn delinearize_exec(idx: u64, shape: &Vec<u64>) -> (result: Vec<u64>)
    requires
        shape_valid_u64(shape@),
        (idx as nat) < shape_size(shape_to_nat_seq(shape@)),
    ensures
        result@.len() == shape@.len(),
        forall|j: int| 0 <= j < result@.len() ==>
            #[trigger] result@[j] as nat == delinearize(idx as nat, shape_to_nat_seq(shape@))[j],
{
    let mut result: Vec<u64> = Vec::new();
    let mut remaining: u64 = idx;
    let mut i: usize = 0;
    let ghost spec_shape = shape_to_nat_seq(shape@);
    let ghost spec_delinearized = delinearize(idx as nat, spec_shape);

    proof {
        crate::proof::shape_lemmas::lemma_delinearize_len(idx as nat, spec_shape);
        crate::proof::shape_lemmas::lemma_delinearize_bounds(idx as nat, spec_shape);
        // At i=0: take(0) = empty, shape_size(empty) = 1, idx/1 = idx
        assert(spec_shape.take(0int) =~= Seq::<nat>::empty());
        assert(shape_size(Seq::<nat>::empty()) == 1nat);
    }

    while i < shape.len()
        invariant
            0 <= i <= shape.len(),
            shape_valid_u64(shape@),
            spec_shape == shape_to_nat_seq(shape@),
            spec_delinearized == delinearize(idx as nat, spec_shape),
            spec_delinearized.len() == spec_shape.len(),
            result@.len() == i as nat,
            remaining as nat == idx as nat / shape_size(spec_shape.take(i as int)),
            forall|j: int| 0 <= j < i ==>
                #[trigger] result@[j] as nat == spec_delinearized[j],
            (idx as nat) < shape_size(spec_shape),
        decreases shape.len() - i,
    {
        proof {
            // Link: delinearize(idx, s)[i] == (idx / shape_size(s.take(i))) % s[i]
            lemma_delinearize_index_formula(idx as nat, spec_shape, i as nat);
        }

        let coord = remaining % shape[i];
        let new_remaining = remaining / shape[i];

        proof {
            // coord == delinearize(idx, spec_shape)[i]
            assert(coord as nat == remaining as nat % (spec_shape[i as int]));
            assert(coord as nat == spec_delinearized[i as int]);

            // new_remaining = idx / shape_size(take(i+1))
            lemma_shape_size_take_step(spec_shape, i as nat);
            // Prove prefix > 0
            let prefix = shape_size(spec_shape.take(i as int));
            lemma_take_shape_valid(spec_shape, i as nat);
            crate::proof::shape_lemmas::lemma_shape_size_positive(spec_shape.take(i as int));
            let si = spec_shape[i as int];
            assert(si > 0);
            assert(shape_size(spec_shape.take((i + 1) as int)) == prefix * si);
            assert((idx as nat / prefix) / si == idx as nat / (prefix * si)) by (nonlinear_arith)
                requires (idx as nat) >= 0, prefix > 0, si > 0,
            {}
        }

        result.push(coord);
        remaining = new_remaining;
        i = i + 1;
    }

    result
}

/// take of a valid shape is valid.
proof fn lemma_take_shape_valid(s: Seq<nat>, k: nat)
    requires shape_valid(s), k <= s.len(),
    ensures shape_valid(s.take(k as int)),
{
    assert forall|j: int| 0 <= j < s.take(k as int).len() implies #[trigger] s.take(k as int)[j] > 0 by {
        assert(s[j] > 0);
    }
}

/// delinearize(idx, s)[k] == (idx / shape_size(s.take(k))) % s[k]
proof fn lemma_delinearize_index_formula(idx: nat, s: Seq<nat>, k: nat)
    requires shape_valid(s), k < s.len(), idx < shape_size(s),
    ensures delinearize(idx, s)[k as int] == (idx / shape_size(s.take(k as int))) % s[k as int],
    decreases k,
{
    crate::proof::shape_lemmas::lemma_delinearize_len(idx, s);
    if k == 0 {
        assert(s.take(0int) =~= Seq::<nat>::empty());
    } else {
        let s1 = s.skip(1);
        assert(shape_valid(s1)) by {
            assert forall|j: int| 0 <= j < s1.len() implies #[trigger] s1[j] > 0 by {
                assert(s[j + 1] > 0);
            }
        }
        crate::proof::shape_lemmas::lemma_shape_size_positive(s1);

        // Prove idx / s[0] < shape_size(s1)
        assert(s.first() == s[0]);
        assert(s.skip(1int) =~= s1);
        // shape_size(s) = s[0] * shape_size(s1)
        // (unfold shape_size: first() * shape_size(skip(1)))
        assert(shape_size(s) == s.first() * shape_size(s1));
        assert(idx / s[0] < shape_size(s1)) by (nonlinear_arith)
            requires idx < s[0] * shape_size(s1), s[0] > 0, shape_size(s1) > 0nat,
        {}

        // delinearize(idx, s) = [idx % s[0]] ++ delinearize(idx / s[0], s1)
        // So delinearize(idx, s)[k] = delinearize(idx / s[0], s1)[k-1]
        crate::proof::shape_lemmas::lemma_delinearize_len(idx / s.first(), s1);
        let d_full = delinearize(idx, s);
        let d_rest = delinearize(idx / s.first(), s1);
        assert(d_full.len() == s.len());
        assert(d_rest.len() == s1.len());
        // d_full = seq![idx % s[0]] ++ d_rest
        assert(d_full.first() == idx % s.first());
        assert(d_full.skip(1) =~= d_rest) by {
            // By definition of delinearize
            assert(d_full =~= seq![idx % s.first()].add(d_rest));
        }
        assert(d_full[k as int] == d_rest[(k - 1) as int]);

        lemma_delinearize_index_formula(idx / s.first(), s1, (k - 1) as nat);

        assert(s1[(k - 1) as int] == s[k as int]);
        assert(s1.take((k - 1) as int) =~= s.take(k as int).skip(1));

        let tk = s.take(k as int);
        assert(tk.first() == s[0]);
        assert(tk.skip(1) =~= s1.take((k - 1) as int));
        // shape_size(tk) = s[0] * shape_size(s1.take(k-1))
        assert(shape_size(tk) == tk.first() * shape_size(tk.skip(1)));

        let a = idx;
        let b = s[0];
        let c = shape_size(s1.take((k - 1) as int));
        lemma_take_shape_valid(s1, (k - 1) as nat);
        crate::proof::shape_lemmas::lemma_shape_size_positive(s1.take((k - 1) as int));
        assert((a / b) / c == a / (b * c)) by (nonlinear_arith)
            requires a >= 0, b > 0, c > 0,
        {}
    }
}

/// Compute dot product of coords (u64) with strides (i64) at runtime.
pub fn dot_product_exec(coords: &Vec<u64>, strides: &Vec<i64>) -> (result: i64)
    requires
        coords@.len() == strides@.len(),
        dot_product_nat_int(shape_to_nat_seq(coords@), strides_to_int_seq(strides@)) >= i64::MIN as int,
        dot_product_nat_int(shape_to_nat_seq(coords@), strides_to_int_seq(strides@)) <= i64::MAX as int,
        // Each individual product and each partial sum fits in i64
        forall|j: int| 0 <= j < coords@.len() ==>
            (coords@[j] as int) * (strides@[j] as int) >= i64::MIN as int &&
            #[trigger] ((coords@[j] as int) * (strides@[j] as int)) <= i64::MAX as int,
        forall|k: nat| k <= coords@.len() ==>
            dot_product_nat_int(
                shape_to_nat_seq(coords@).take(k as int),
                strides_to_int_seq(strides@).take(k as int)
            ) >= i64::MIN as int &&
            dot_product_nat_int(
                shape_to_nat_seq(coords@).take(k as int),
                strides_to_int_seq(strides@).take(k as int)
            ) <= i64::MAX as int,
        // coords fit in i64 (needed for cast)
        forall|j: int| 0 <= j < coords@.len() ==> coords@[j] <= i64::MAX as u64,
    ensures
        result as int == dot_product_nat_int(shape_to_nat_seq(coords@), strides_to_int_seq(strides@)),
{
    let mut result: i64 = 0;
    let mut i: usize = 0;
    let ghost spec_coords = shape_to_nat_seq(coords@);
    let ghost spec_strides = strides_to_int_seq(strides@);

    while i < coords.len()
        invariant
            0 <= i <= coords.len(),
            coords@.len() == strides@.len(),
            spec_coords == shape_to_nat_seq(coords@),
            spec_strides == strides_to_int_seq(strides@),
            result as int == dot_product_nat_int(spec_coords.take(i as int), spec_strides.take(i as int)),
            result as int >= i64::MIN as int,
            result as int <= i64::MAX as int,
            forall|j: int| 0 <= j < coords@.len() ==>
                (coords@[j] as int) * (strides@[j] as int) >= i64::MIN as int &&
                #[trigger] ((coords@[j] as int) * (strides@[j] as int)) <= i64::MAX as int,
            forall|k: nat| k <= coords@.len() ==>
                dot_product_nat_int(spec_coords.take(k as int), spec_strides.take(k as int)) >= i64::MIN as int &&
                dot_product_nat_int(spec_coords.take(k as int), spec_strides.take(k as int)) <= i64::MAX as int,
            forall|j: int| 0 <= j < coords@.len() ==> coords@[j] <= i64::MAX as u64,
        decreases coords.len() - i,
    {
        proof {
            lemma_dot_product_take_step(spec_coords, spec_strides, i as nat);
        }

        let product = (coords[i] as i64) * strides[i];
        result = result + product;
        i = i + 1;
    }

    proof {
        assert(spec_coords.take(coords@.len() as int) =~= spec_coords);
        assert(spec_strides.take(strides@.len() as int) =~= spec_strides);
    }

    result
}

/// dot_product(take(i+1), take(i+1)) == dot_product(take(i), take(i)) + coords[i]*strides[i]
pub proof fn lemma_dot_product_take_step(coords: Seq<nat>, strides: Seq<int>, i: nat)
    requires
        coords.len() == strides.len(),
        i < coords.len(),
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
        lemma_dot_product_take_step(c1, s1, (i - 1) as nat);
    }
}

} // verus!
