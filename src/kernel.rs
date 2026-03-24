use vstd::prelude::*;
use crate::arith_expr::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Kernel: Gather → Compute → Scatter with verified semantics
// ══════════════════════════════════════════════════════════════

/// A GPU compute kernel spec.
///
/// For each thread i where guard(i) != 0:
///   output[scatter(i)] = compute(i, inputs)
///
/// Scatter must be injective under guard (deterministic, order-independent).
pub struct KernelSpec {
    /// Guard: thread executes only if eval(guard, thread_env) != 0.
    pub guard: ArithExpr,
    /// Scatter: maps thread id → output buffer index.
    pub scatter: ArithExpr,
    /// Compute: the value to store. Uses arith_eval_with_arrays for buffer reads.
    pub compute: ArithExpr,
}

/// Thread environment: maps thread index to variable bindings.
/// For 1D dispatch: env = [tid]
/// For 2D dispatch: env = [gid_x, gid_y]
pub open spec fn thread_env_1d(tid: nat) -> Seq<int> {
    seq![tid as int]
}

pub open spec fn thread_env_2d(gid_x: nat, gid_y: nat) -> Seq<int> {
    seq![gid_x as int, gid_y as int]
}

/// What a single thread produces (if active).
/// Returns Some((output_index, value)) if guard passes, None otherwise.
pub open spec fn kernel_thread_result(
    k: &KernelSpec,
    env: Seq<int>,
    inputs: Seq<Seq<int>>,
) -> Option<(int, int)> {
    let guard_val = arith_eval_with_arrays(&k.guard, env, inputs);
    if guard_val != 0 {
        let idx = arith_eval_with_arrays(&k.scatter, env, inputs);
        let val = arith_eval_with_arrays(&k.compute, env, inputs);
        Some((idx, val))
    } else {
        None
    }
}

/// Kernel evaluation for 2D dispatch (M × N threads).
/// Returns the output buffer: output[j] = value written by the unique thread
/// whose scatter(env) == j, or 0 if no thread writes to j.
pub open spec fn kernel_eval_2d(
    k: &KernelSpec,
    inputs: Seq<Seq<int>>,
    output_size: nat,
    m: nat, n: nat,
) -> Seq<int> {
    Seq::new(output_size, |j: int|
        kernel_find_writer_2d(k, inputs, m, n, j as nat, 0, 0))
}

/// Search for the thread that writes to output index target_j.
/// With injective scatter, at most one thread writes to any given index.
pub open spec fn kernel_find_writer_2d(
    k: &KernelSpec,
    inputs: Seq<Seq<int>>,
    m: nat, n: nat,
    target_j: nat,
    gi: nat, gj: nat,
) -> int
    decreases m - gi, n - gj,
{
    if gi >= m { 0 }
    else if gj >= n {
        kernel_find_writer_2d(k, inputs, m, n, target_j, gi + 1, 0)
    } else {
        let env = thread_env_2d(gi, gj);
        let result = kernel_thread_result(k, env, inputs);
        match result {
            Some((idx, val)) => {
                if idx == target_j as int { val }
                else { kernel_find_writer_2d(k, inputs, m, n, target_j, gi, gj + 1) }
            },
            None => kernel_find_writer_2d(k, inputs, m, n, target_j, gi, gj + 1),
        }
    }
}

// ══════════════════════════════════════════════════════════════
// GEMM kernel constructor + correctness proof
// ══════════════════════════════════════════════════════════════

/// Build the GEMM kernel spec:
///   C[i*N+j] = Σ_{k=0}^{K-1} A[i*K+k] * B[k*N+j]
///
/// Variables: 0 = gid.x (i), 1 = gid.y (j)
/// Reduce variable: 2 (k)
/// Buffers: 0 = A, 1 = B
pub open spec fn gemm_kernel(m: nat, k_size: nat, n: nat) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Mul(
            Box::new(ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(m as int)))),
            Box::new(ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(1)), Box::new(ArithExpr::Const(n as int)))),
        ),
        scatter: ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Var(1)),
        ),
        compute: ArithExpr::Reduce(
            2,  // k variable
            Box::new(ArithExpr::Const(k_size as int)),
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Add(
                    Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(k_size as int)))),
                    Box::new(ArithExpr::Var(2)),
                )))),
                Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Add(
                    Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(2)), Box::new(ArithExpr::Const(n as int)))),
                    Box::new(ArithExpr::Var(1)),
                )))),
            )),
        ),
    }
}

/// The GEMM kernel compute expression evaluates to gemm_partial_sum.
///
/// For thread (i, j): arith_eval_with_arrays(compute, [i, j], [A, B])
///   == Σ_{k=0}^{K-1} A[i*K+k] * B[k*N+j]
///   == gemm_partial_sum(A, B, K, N, i, j, K)
pub proof fn lemma_gemm_kernel_element_correct(
    a: Seq<int>, b: Seq<int>,
    m: nat, k_size: nat, n: nat,
    i: nat, j: nat,
)
    requires
        i < m,
        j < n,
        // A has M*K elements, B has K*N elements
        a.len() >= (m * k_size) as int,
        b.len() >= (k_size * n) as int,
        // All index accesses in bounds
        forall|kk: nat| kk < k_size ==> {
            &&& 0 <= (i * k_size + kk) as int && (i * k_size + kk) < a.len()
            &&& 0 <= (kk * n + j) as int && (kk * n + j) < b.len()
        },
    ensures ({
        let k = gemm_kernel(m, k_size, n);
        let env = thread_env_2d(i, j);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.compute, env, inputs)
            == gemm_partial_sum_int(a, b, k_size, n, i, j, k_size)
    }),
    decreases k_size,
{
    let k = gemm_kernel(m, k_size, n);
    let env = thread_env_2d(i, j);
    let inputs = seq![a, b];

    // The compute expression is Reduce(2, Const(K), body)
    // arith_eval_with_arrays evaluates to reduce_sum_arrays(2, K, body, env, inputs)
    // We need to show this equals gemm_partial_sum_int(a, b, K, N, i, j, K)
    // Both are recursive sums; prove by induction on k_size.

    // Base case: k_size == 0
    if k_size == 0 {
        // reduce_sum_arrays(2, 0, body, env, inputs) == 0
        // gemm_partial_sum_int(a, b, 0, n, i, j, 0) == 0
    } else {
        // IH: for k_size - 1
        lemma_gemm_kernel_element_correct(a, b, m, (k_size - 1) as nat, n, i, j);

        // We need to show that the (k_size-1)-th term matches
        // reduce_sum_arrays adds: arith_eval_with_arrays(body, env_with(env, 2, k_size-1), inputs)
        // gemm_partial_sum_int adds: a[i*K + (k_size-1)] * b[(k_size-1)*N + j]
        // These should be equal by unfolding the body expression.
    }
}

/// Integer version of gemm_partial_sum (over Seq<int> instead of Seq<i64>).
pub open spec fn gemm_partial_sum_int(
    a: Seq<int>, b: Seq<int>,
    k_size: nat, n: nat,
    i: nat, j: nat, kk: nat,
) -> int
    decreases kk,
{
    if kk == 0 { 0int }
    else {
        gemm_partial_sum_int(a, b, k_size, n, i, j, (kk - 1) as nat)
            + a[(i * k_size + (kk - 1)) as int] * b[((kk - 1) * n + j) as int]
    }
}

/// Build a vector-add kernel spec: out[i] = A[i] + B[i]
pub open spec fn vector_add_kernel(n: nat) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(n as int))),
        scatter: ArithExpr::Var(0),
        compute: ArithExpr::Add(
            Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(0)))),
            Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(0)))),
        ),
    }
}

/// Vector-add element correctness: compute(i) = A[i] + B[i]
pub proof fn lemma_vector_add_kernel_correct(
    a: Seq<int>, b: Seq<int>, n: nat, i: nat,
)
    requires
        i < n,
        a.len() >= n as int,
        b.len() >= n as int,
    ensures ({
        let k = vector_add_kernel(n);
        let env = thread_env_1d(i);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.compute, env, inputs) == a[i as int] + b[i as int]
    }),
{}

} // verus!
