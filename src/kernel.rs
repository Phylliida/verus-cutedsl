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
/// The GEMM kernel compute expression evaluates to gemm_partial_sum_int.
///
/// For thread (i, j): arith_eval_with_arrays(compute, [i, j], [A, B])
///   == Σ_{k=0}^{K-1} A[i*K+k] * B[k*N+j]
pub proof fn lemma_gemm_kernel_element_correct(
    a: Seq<int>, b: Seq<int>,
    m: nat, k_size: nat, n: nat,
    i: nat, j: nat,
)
    requires
        i < m, j < n,
        m > 0, n > 0,
        a.len() == (m * k_size) as int,
        b.len() == (k_size * n) as int,
    ensures ({
        let k = gemm_kernel(m, k_size, n);
        let env = thread_env_2d(i, j);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.compute, env, inputs)
            == gemm_partial_sum_int(a, b, k_size, n, i, j, k_size)
    }),
    decreases k_size,
{
    let kern = gemm_kernel(m, k_size, n);
    let env = thread_env_2d(i, j);
    let inputs = seq![a, b];
    let body = gemm_kernel_body(k_size, n);

    // Help Z3 unfold: k.compute is Reduce(2, Const(K), body)
    // arith_eval_with_arrays(Reduce(2, Const(K), body), env, inputs)
    //   = reduce_sum_arrays(2, K, &body, env, inputs)
    let bound_expr = ArithExpr::Const(k_size as int);
    assert(arith_eval_with_arrays(&bound_expr, env, inputs) == k_size as int);

    // Connect arith_eval_with_arrays on the Reduce node to reduce_sum_arrays
    assert(arith_eval_with_arrays(&kern.compute, env, inputs)
        == reduce_sum_arrays(2, k_size as int, &body, env, inputs));

    if k_size == 0 {
        // Both sides are 0
    } else {
        assert(a.len() >= (i * k_size + k_size) as int) by (nonlinear_arith)
            requires i < m, m > 0, a.len() == m * k_size;
        lemma_gemm_reduce_matches_partial_sum(a, b, k_size, n, i, j, k_size);
    }
}

/// The body expression for GEMM: A[i*K+k] * B[k*N+j]
pub open spec fn gemm_kernel_body(k_size: nat, n: nat) -> ArithExpr {
    ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(k_size as int)))),
            Box::new(ArithExpr::Var(2)),
        )))),
        Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(2)), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Var(1)),
        )))),
    )
}

/// Core inductive lemma: reduce_sum_arrays over the GEMM body matches gemm_partial_sum_int.
proof fn lemma_gemm_reduce_matches_partial_sum(
    a: Seq<int>, b: Seq<int>,
    k_size: nat, n: nat,
    i: nat, j: nat,
    kk: nat,
)
    requires
        kk <= k_size,
        a.len() >= (i * k_size + k_size) as int,
        b.len() >= (k_size * n) as int,
        j < n, n > 0,
    ensures ({
        let body = gemm_kernel_body(k_size, n);
        let env = thread_env_2d(i, j);
        let inputs = seq![a, b];
        reduce_sum_arrays(2, kk as int, &body, env, inputs)
            == gemm_partial_sum_int(a, b, k_size, n, i, j, kk)
    }),
    decreases kk,
{
    let body = gemm_kernel_body(k_size, n);
    let env = thread_env_2d(i, j);
    let inputs = seq![a, b];

    if kk == 0 {
        // Both sides are 0
    } else {
        // IH
        lemma_gemm_reduce_matches_partial_sum(a, b, k_size, n, i, j, (kk - 1) as nat);

        let ext_env = env_with(env, 2, (kk - 1) as int);
        assert(ext_env.len() == 3);
        assert(ext_env[0] == i as int);
        assert(ext_env[1] == j as int);
        assert(ext_env[2] == (kk - 1) as int);

        // Index bounds
        assert(0 <= i * k_size + (kk - 1) < a.len()) by (nonlinear_arith)
            requires kk >= 1, kk <= k_size, a.len() >= i * k_size + k_size;
        assert(0 <= (kk - 1) * n + j < b.len()) by (nonlinear_arith)
            requires kk >= 1, kk <= k_size, j < n, n > 0, b.len() >= k_size * n;

        // Use existing Box-unfolding helpers for the linear index pattern
        // a_idx = Add(Mul(Var(0), Const(K)), Var(2)) = i*K + (kk-1)
        crate::arith_expr::lemma_eval_with_arrays_linear_index(
            0, k_size as int, 2, ext_env, inputs);
        // b_idx = Add(Mul(Var(2), Const(N)), Var(1)) = (kk-1)*N + j
        crate::arith_expr::lemma_eval_with_arrays_linear_index(
            2, n as int, 1, ext_env, inputs);

        // Now Z3 knows the index values. Help with the full body via
        // Index + Mul unfolding.
        let a_idx_expr = ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(k_size as int)))),
            Box::new(ArithExpr::Var(2)),
        );
        let b_idx_expr = ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(2)), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Var(1)),
        );
        let a_idx_val = (i * k_size + (kk - 1)) as int;
        let b_idx_val = ((kk - 1) * n + j) as int;
        crate::arith_expr::lemma_eval_with_arrays_index(
            0, &a_idx_expr, ext_env, inputs, a_idx_val);
        crate::arith_expr::lemma_eval_with_arrays_index(
            1, &b_idx_expr, ext_env, inputs, b_idx_val);
        let idx_a = ArithExpr::Index(0, Box::new(a_idx_expr));
        let idx_b = ArithExpr::Index(1, Box::new(b_idx_expr));
        crate::arith_expr::lemma_eval_with_arrays_mul(&idx_a, &idx_b, ext_env, inputs);
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
{
    let k = vector_add_kernel(n);
    let env = thread_env_1d(i);
    let inputs = seq![a, b];

    // Help Z3 unfold through Box wrappers
    let var0 = ArithExpr::Var(0);
    let idx_a = ArithExpr::Index(0, Box::new(var0));
    let idx_b = ArithExpr::Index(1, Box::new(ArithExpr::Var(0)));

    assert(env[0] == i as int);
    assert(arith_eval_with_arrays(&ArithExpr::Var(0), env, inputs) == i as int);
    assert(arith_eval_with_arrays(&idx_a, env, inputs) == a[i as int]);
    assert(arith_eval_with_arrays(&idx_b, env, inputs) == b[i as int]);
}

// ══════════════════════════════════════════════════════════════
// Layout offset kernel — connects CuTe algebra to Kernel framework
// ══════════════════════════════════════════════════════════════

/// Build a layout-offset kernel: out[x] = layout.offset(x)
/// Uses the verified offset_expr from arith_expr.rs.
pub open spec fn offset_kernel(shape: Seq<nat>, stride: Seq<int>) -> KernelSpec
    recommends shape.len() == stride.len(),
{
    KernelSpec {
        guard: ArithExpr::Cmp(
            CmpOp::Lt,
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(crate::shape::shape_size(shape) as int)),
        ),
        scatter: ArithExpr::Var(0),
        compute: crate::arith_expr::offset_expr(0, shape, stride),
    }
}

/// Offset kernel correctness: compute(x) == layout.offset(x).
/// This connects the Kernel framework to the CuTe layout algebra.
pub proof fn lemma_offset_kernel_correct(
    shape: Seq<nat>, stride: Seq<int>, x: nat,
)
    requires
        crate::shape::shape_valid(shape),
        shape.len() == stride.len(),
        x < crate::shape::shape_size(shape),
    ensures ({
        let k = offset_kernel(shape, stride);
        let env = thread_env_1d(x);
        arith_eval(&k.compute, env)
            == (crate::layout::LayoutSpec { shape, stride }).offset(x)
    }),
{
    // offset_kernel.compute IS offset_expr — use the existing proof directly
    crate::arith_expr::lemma_offset_expr_correct(shape, stride, x);
}

// ══════════════════════════════════════════════════════════════
// Dot product / reduction kernel
// ══════════════════════════════════════════════════════════════

/// Dot product spec: Σ_{i=0}^{n-1} a[i] * b[i]
pub open spec fn dot_product_spec(a: Seq<int>, b: Seq<int>, n: nat) -> int
    decreases n,
{
    if n == 0 { 0 }
    else { dot_product_spec(a, b, (n - 1) as nat) + a[(n - 1) as int] * b[(n - 1) as int] }
}

/// Build a dot-product kernel (single-thread spec):
///   out[0] = Σ_{k=0}^{n-1} a[k] * b[k]
pub open spec fn dot_product_kernel(n: nat) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Eq, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(0))),
        scatter: ArithExpr::Const(0),
        compute: ArithExpr::Reduce(
            1,  // reduction variable (Var(1) = k)
            Box::new(ArithExpr::Const(n as int)),
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(1)))),
                Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
            )),
        ),
    }
}

/// Dot product kernel correctness: compute(0) == Σ a[k]*b[k].
pub proof fn lemma_dot_product_kernel_correct(
    a: Seq<int>, b: Seq<int>, n: nat,
)
    requires
        a.len() >= n as int,
        b.len() >= n as int,
    ensures ({
        let k = dot_product_kernel(n);
        let env = thread_env_1d(0);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.compute, env, inputs)
            == dot_product_spec(a, b, n)
    }),
{
    let k = dot_product_kernel(n);
    let env = thread_env_1d(0);
    let inputs = seq![a, b];

    // compute = Reduce(1, Const(n), body)
    // arith_eval_with_arrays unfolds to reduce_sum_arrays(1, n, body, [0], [a, b])
    // We prove this equals dot_product_spec by induction.
    let body = ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(1)))),
        Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
    );
    let bound_expr = ArithExpr::Const(n as int);
    assert(arith_eval_with_arrays(&bound_expr, env, inputs) == n as int);

    lemma_dot_reduce_matches(a, b, n, env, inputs, &body);
}

/// Inductive helper: reduce_sum_arrays for dot product body matches dot_product_spec.
proof fn lemma_dot_reduce_matches(
    a: Seq<int>, b: Seq<int>, kk: nat,
    env: Seq<int>, inputs: Seq<Seq<int>>,
    body: &ArithExpr,
)
    requires
        a.len() >= kk as int,
        b.len() >= kk as int,
        env.len() >= 1,
        inputs.len() == 2,
        inputs[0] == a,
        inputs[1] == b,
        *body == ArithExpr::Mul(
            Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(1)))),
            Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
        ),
    ensures
        reduce_sum_arrays(1, kk as int, body, env, inputs)
            == dot_product_spec(a, b, kk),
    decreases kk,
{
    if kk == 0 {
    } else {
        lemma_dot_reduce_matches(a, b, (kk - 1) as nat, env, inputs, body);

        // Show the kk-1'th term matches: a[kk-1] * b[kk-1]
        let ext_env = env_with(env, 1, (kk - 1) as int);
        assert(ext_env.len() >= 2);
        assert(ext_env[1] == (kk - 1) as int);

        // Help Z3 unfold body through Box wrappers
        let idx = (kk - 1) as nat;
        let var1 = ArithExpr::Var(1);
        assert(arith_eval_with_arrays(&var1, ext_env, inputs) == idx as int);

        // Index(0, Var(1)) = a[kk-1], Index(1, Var(1)) = b[kk-1]
        crate::arith_expr::lemma_eval_with_arrays_index(
            0, &var1, ext_env, inputs, idx as int);
        crate::arith_expr::lemma_eval_with_arrays_index(
            1, &var1, ext_env, inputs, idx as int);

        // Mul(Index(0,...), Index(1,...)) = a[kk-1] * b[kk-1]
        let idx_a = ArithExpr::Index(0, Box::new(ArithExpr::Var(1)));
        let idx_b = ArithExpr::Index(1, Box::new(ArithExpr::Var(1)));
        crate::arith_expr::lemma_eval_with_arrays_mul(&idx_a, &idx_b, ext_env, inputs);
    }
}

} // verus!
