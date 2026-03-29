///  Exec-level ArithExpr evaluator WITH array support.
///
///  Like `runtime_arith_eval` in arith_expr.rs, but takes an additional
///  `arrays` parameter for `Index(arr, idx)` nodes to read from.
///  This enables exec evaluation of Map kernels that read input buffers.
///
///  In a separate file to avoid rlimit pollution of the 1900-line arith_expr.rs.

use vstd::prelude::*;
use crate::arith_expr::*;

//  NOTE: Shr support requires replicating ~30 lines of pow2 proof logic
//  from runtime_arith_eval. Deferred — add when fixed-point kernels need it.
//  All integer kernels (Hillis-Steele, compact, GEMM) work without Shr.

verus! {

///  Spec: all intermediate values fit in i64, including array reads.
pub open spec fn eval_with_arrays_fits_i64(
    expr: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
) -> bool
    decreases expr,
{
    i64::MIN as int <= arith_eval_with_arrays(expr, env, arrays)
    && arith_eval_with_arrays(expr, env, arrays) <= i64::MAX as int
    && match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b) =>
            eval_with_arrays_fits_i64(a, env, arrays) && eval_with_arrays_fits_i64(b, env, arrays),
        ArithExpr::Shr(a, b) =>
            eval_with_arrays_fits_i64(a, env, arrays) && eval_with_arrays_fits_i64(b, env, arrays)
            && arith_eval_with_arrays(a, env, arrays) >= 0
            && arith_eval_with_arrays(b, env, arrays) >= 0,
        ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) =>
            eval_with_arrays_fits_i64(a, env, arrays) && eval_with_arrays_fits_i64(b, env, arrays)
            && arith_eval_with_arrays(a, env, arrays) >= 0
            && arith_eval_with_arrays(b, env, arrays) > 0,
        ArithExpr::Index(arr_idx, idx_expr) =>
            eval_with_arrays_fits_i64(idx_expr, env, arrays)
            && (*arr_idx as int) < arrays.len()
            && arith_eval_with_arrays(idx_expr, env, arrays) >= 0
            && arith_eval_with_arrays(idx_expr, env, arrays) < arrays[*arr_idx as int].len(),
        ArithExpr::Cmp(_, a, b) =>
            eval_with_arrays_fits_i64(a, env, arrays) && eval_with_arrays_fits_i64(b, env, arrays),
        ArithExpr::Reduce(_, bound, _) =>
            eval_with_arrays_fits_i64(bound, env, arrays),
    }
}

///  Exec ArithExpr evaluator with arrays.
///  Ensures result matches `arith_eval_with_arrays` spec.
pub fn runtime_eval_with_arrays(
    expr: &RuntimeArithExpr,
    env: &Vec<i64>,
    arrays: &Vec<Vec<i64>>,
) -> (result: i64)
    requires
        eval_with_arrays_fits_i64(
            &expr.view_spec(),
            i64_seq_to_int(env@),
            i64_vecs_to_int(arrays@)),
        no_reduce(&expr.view_spec()),
        no_shr(&expr.view_spec()),
    ensures
        result as int == arith_eval_with_arrays(
            &expr.view_spec(),
            i64_seq_to_int(env@),
            i64_vecs_to_int(arrays@)),
    decreases expr,
{
    let ghost env_spec = i64_seq_to_int(env@);
    let ghost arrays_spec = i64_vecs_to_int(arrays@);
    match expr {
        RuntimeArithExpr::Const(c) => *c,
        RuntimeArithExpr::Var(i) => {
            if (*i as usize) < env.len() {
                proof {
                    assert(i64_seq_to_int(env@)[*i as int] == env@[*i as int] as int);
                }
                env[*i as usize]
            } else {
                0i64
            }
        },
        RuntimeArithExpr::Add(a, b) => {
            let va = runtime_eval_with_arrays(a, env, arrays);
            let vb = runtime_eval_with_arrays(b, env, arrays);
            va + vb
        },
        RuntimeArithExpr::Sub(a, b) => {
            let va = runtime_eval_with_arrays(a, env, arrays);
            let vb = runtime_eval_with_arrays(b, env, arrays);
            va - vb
        },
        RuntimeArithExpr::Mul(a, b) => {
            let va = runtime_eval_with_arrays(a, env, arrays);
            let vb = runtime_eval_with_arrays(b, env, arrays);
            va * vb
        },
        RuntimeArithExpr::Div(a, b) => {
            let va = runtime_eval_with_arrays(a, env, arrays);
            let vb = runtime_eval_with_arrays(b, env, arrays);
            if vb > 0 { va / vb } else { 0i64 }
        },
        RuntimeArithExpr::Mod(a, b) => {
            let va = runtime_eval_with_arrays(a, env, arrays);
            let vb = runtime_eval_with_arrays(b, env, arrays);
            if vb > 0 { va % vb } else { 0i64 }
        },
        RuntimeArithExpr::Index(arr_idx, idx_expr) => {
            let idx = runtime_eval_with_arrays(idx_expr, env, arrays);
            proof {
                assert(i64_vecs_to_int(arrays@)[*arr_idx as int]
                    =~= i64_seq_to_int(arrays@[*arr_idx as int]@));
            }
            if (*arr_idx as usize) < arrays.len() && idx >= 0
                && (idx as usize) < arrays[*arr_idx as usize].len()
            {
                let val = arrays[*arr_idx as usize][idx as usize];
                proof {
                    assert(i64_seq_to_int(arrays@[*arr_idx as int]@)[idx as int]
                        == arrays@[*arr_idx as int]@[idx as int] as int);
                }
                val
            } else {
                0i64
            }
        },
        RuntimeArithExpr::Shr(_, _) => {
            //  Unreachable by no_shr precondition
            proof { assert(false); }
            0i64
        },
        RuntimeArithExpr::Cmp(op, a, b) => {
            let va = runtime_eval_with_arrays(a, env, arrays);
            let vb = runtime_eval_with_arrays(b, env, arrays);
            match op {
                RuntimeCmpOp::Lt => if va < vb { 1 } else { 0 },
                RuntimeCmpOp::Le => if va <= vb { 1 } else { 0 },
                RuntimeCmpOp::Gt => if va > vb { 1 } else { 0 },
                RuntimeCmpOp::Ge => if va >= vb { 1 } else { 0 },
                RuntimeCmpOp::Eq => if va == vb { 1 } else { 0 },
                RuntimeCmpOp::Ne => if va != vb { 1 } else { 0 },
            }
        },
        RuntimeArithExpr::Reduce(_, _, _) => {
            //  Reduce not supported at exec level (requires no_reduce precondition)
            0i64
        },
    }
}

///  Predicate: expression contains no Shr nodes.
pub open spec fn no_shr(expr: &ArithExpr) -> bool
    decreases expr,
{
    match expr {
        ArithExpr::Shr(_, _) => false,
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) =>
            no_shr(a) && no_shr(b),
        ArithExpr::Index(_, idx) => no_shr(idx),
        ArithExpr::Cmp(_, a, b) => no_shr(a) && no_shr(b),
        ArithExpr::Reduce(_, bound, body) => no_shr(bound) && no_shr(body),
    }
}

///  Convert Vec<Vec<i64>> view to Seq<Seq<int>> for spec.
pub open spec fn i64_vecs_to_int(vecs: Seq<Vec<i64>>) -> Seq<Seq<int>> {
    Seq::new(vecs.len(), |i: int| i64_seq_to_int(vecs[i]@))
}

} //  verus!
