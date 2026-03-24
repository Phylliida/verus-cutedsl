use vstd::prelude::*;
use crate::arith_expr::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Kernel: guard + multiple (scatter, compute) outputs
// ══════════════════════════════════════════════════════════════

/// A single output of a kernel: write compute(env) to buffer at scatter(env).
pub struct OutputSpec {
    pub scatter: ArithExpr,
    pub compute: ArithExpr,
}

/// A GPU compute kernel spec.
///
/// For each thread i where guard(i) != 0:
///   for each output o:
///     output_buffer_o[scatter_o(i)] = compute_o(i, inputs)
///
/// Each output's scatter must be injective under guard (deterministic).
pub struct KernelSpec {
    pub guard: ArithExpr,
    pub outputs: Seq<OutputSpec>,
}

/// Thread environment constructors.
pub open spec fn thread_env_1d(tid: nat) -> Seq<int> {
    seq![tid as int]
}

pub open spec fn thread_env_2d(gid_x: nat, gid_y: nat) -> Seq<int> {
    seq![gid_x as int, gid_y as int]
}

/// Evaluate a single output for a single thread.
pub open spec fn eval_output(
    o: &OutputSpec, env: Seq<int>, inputs: Seq<Seq<int>>,
) -> (int, int) {
    (arith_eval_with_arrays(&o.scatter, env, inputs),
     arith_eval_with_arrays(&o.compute, env, inputs))
}

// ══════════════════════════════════════════════════════════════
// Helper: single-output kernel constructor
// ══════════════════════════════════════════════════════════════

/// Convenience: build a single-output KernelSpec.
pub open spec fn single_output_kernel(
    guard: ArithExpr, scatter: ArithExpr, compute: ArithExpr,
) -> KernelSpec {
    KernelSpec {
        guard,
        outputs: seq![OutputSpec { scatter, compute }],
    }
}

// ══════════════════════════════════════════════════════════════
// GEMM kernel
// ══════════════════════════════════════════════════════════════

/// GEMM kernel: C[i*N+j] = Σ_{k=0}^{K-1} A[i*K+k] * B[k*N+j]
/// Variables: 0=gid.x(i), 1=gid.y(j), 2=reduce var(k). Buffers: 0=A, 1=B.
pub open spec fn gemm_kernel(m: nat, k_size: nat, n: nat) -> KernelSpec {
    single_output_kernel(
        ArithExpr::Mul(
            Box::new(ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(m as int)))),
            Box::new(ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(1)), Box::new(ArithExpr::Const(n as int)))),
        ),
        ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Var(1)),
        ),
        ArithExpr::Reduce(
            2,
            Box::new(ArithExpr::Const(k_size as int)),
            Box::new(gemm_kernel_body(k_size, n)),
        ),
    )
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

/// GEMM correctness: output 0's compute == Σ_k A[i*K+k] * B[k*N+j]
pub proof fn lemma_gemm_kernel_element_correct(
    a: Seq<int>, b: Seq<int>,
    m: nat, k_size: nat, n: nat,
    i: nat, j: nat,
)
    requires
        i < m, j < n, m > 0, n > 0,
        a.len() == (m * k_size) as int,
        b.len() == (k_size * n) as int,
    ensures ({
        let k = gemm_kernel(m, k_size, n);
        let env = thread_env_2d(i, j);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.outputs[0].compute, env, inputs)
            == gemm_partial_sum_int(a, b, k_size, n, i, j, k_size)
    }),
    decreases k_size,
{
    let kern = gemm_kernel(m, k_size, n);
    let env = thread_env_2d(i, j);
    let inputs = seq![a, b];
    let body = gemm_kernel_body(k_size, n);

    let bound_expr = ArithExpr::Const(k_size as int);
    assert(arith_eval_with_arrays(&bound_expr, env, inputs) == k_size as int);
    assert(arith_eval_with_arrays(&kern.outputs[0].compute, env, inputs)
        == reduce_sum_arrays(2, k_size as int, &body, env, inputs));

    if k_size == 0 {
    } else {
        assert(a.len() >= (i * k_size + k_size) as int) by (nonlinear_arith)
            requires i < m, m > 0, a.len() == m * k_size;
        lemma_gemm_reduce_matches_partial_sum(a, b, k_size, n, i, j, k_size);
    }
}

/// Core inductive helper for GEMM.
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
    } else {
        lemma_gemm_reduce_matches_partial_sum(a, b, k_size, n, i, j, (kk - 1) as nat);

        let ext_env = env_with(env, 2, (kk - 1) as int);
        assert(ext_env.len() == 3);
        assert(ext_env[0] == i as int);
        assert(ext_env[1] == j as int);
        assert(ext_env[2] == (kk - 1) as int);

        assert(0 <= i * k_size + (kk - 1) < a.len()) by (nonlinear_arith)
            requires kk >= 1, kk <= k_size, a.len() >= i * k_size + k_size;
        assert(0 <= (kk - 1) * n + j < b.len()) by (nonlinear_arith)
            requires kk >= 1, kk <= k_size, j < n, n > 0, b.len() >= k_size * n;

        crate::arith_expr::lemma_eval_with_arrays_linear_index(
            0, k_size as int, 2, ext_env, inputs);
        crate::arith_expr::lemma_eval_with_arrays_linear_index(
            2, n as int, 1, ext_env, inputs);

        let a_idx_expr = ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(k_size as int)))),
            Box::new(ArithExpr::Var(2)),
        );
        let b_idx_expr = ArithExpr::Add(
            Box::new(ArithExpr::Mul(Box::new(ArithExpr::Var(2)), Box::new(ArithExpr::Const(n as int)))),
            Box::new(ArithExpr::Var(1)),
        );
        crate::arith_expr::lemma_eval_with_arrays_index(
            0, &a_idx_expr, ext_env, inputs, (i * k_size + (kk - 1)) as int);
        crate::arith_expr::lemma_eval_with_arrays_index(
            1, &b_idx_expr, ext_env, inputs, ((kk - 1) * n + j) as int);
        let idx_a = ArithExpr::Index(0, Box::new(a_idx_expr));
        let idx_b = ArithExpr::Index(1, Box::new(b_idx_expr));
        crate::arith_expr::lemma_eval_with_arrays_mul(&idx_a, &idx_b, ext_env, inputs);
    }
}

/// Integer GEMM partial sum spec.
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

// ══════════════════════════════════════════════════════════════
// Vector add kernel
// ══════════════════════════════════════════════════════════════

/// Vector add: out[i] = A[i] + B[i]
pub open spec fn vector_add_kernel(n: nat) -> KernelSpec {
    single_output_kernel(
        ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(n as int))),
        ArithExpr::Var(0),
        ArithExpr::Add(
            Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(0)))),
            Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(0)))),
        ),
    )
}

/// Vector add correctness.
pub proof fn lemma_vector_add_kernel_correct(
    a: Seq<int>, b: Seq<int>, n: nat, i: nat,
)
    requires i < n, a.len() >= n as int, b.len() >= n as int,
    ensures ({
        let k = vector_add_kernel(n);
        let env = thread_env_1d(i);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.outputs[0].compute, env, inputs) == a[i as int] + b[i as int]
    }),
{
    let k = vector_add_kernel(n);
    let env = thread_env_1d(i);
    let inputs = seq![a, b];
    let var0 = ArithExpr::Var(0);
    let idx_a = ArithExpr::Index(0, Box::new(var0));
    let idx_b = ArithExpr::Index(1, Box::new(ArithExpr::Var(0)));
    assert(arith_eval_with_arrays(&ArithExpr::Var(0), env, inputs) == i as int);
    assert(arith_eval_with_arrays(&idx_a, env, inputs) == a[i as int]);
    assert(arith_eval_with_arrays(&idx_b, env, inputs) == b[i as int]);
}

// ══════════════════════════════════════════════════════════════
// Layout offset kernel
// ══════════════════════════════════════════════════════════════

/// Layout offset: out[x] = layout.offset(x)
pub open spec fn offset_kernel(shape: Seq<nat>, stride: Seq<int>) -> KernelSpec
    recommends shape.len() == stride.len(),
{
    single_output_kernel(
        ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(crate::shape::shape_size(shape) as int))),
        ArithExpr::Var(0),
        crate::arith_expr::offset_expr(0, shape, stride),
    )
}

/// Offset kernel correctness: connects to CuTe layout algebra.
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
        arith_eval(&k.outputs[0].compute, env)
            == (crate::layout::LayoutSpec { shape, stride }).offset(x)
    }),
{
    crate::arith_expr::lemma_offset_expr_correct(shape, stride, x);
}

// ══════════════════════════════════════════════════════════════
// Dot product kernel
// ══════════════════════════════════════════════════════════════

/// Dot product spec: Σ_{i=0}^{n-1} a[i] * b[i]
pub open spec fn dot_product_spec(a: Seq<int>, b: Seq<int>, n: nat) -> int
    decreases n,
{
    if n == 0 { 0 }
    else { dot_product_spec(a, b, (n - 1) as nat) + a[(n - 1) as int] * b[(n - 1) as int] }
}

/// Dot product: out[0] = Σ_k a[k] * b[k]
pub open spec fn dot_product_kernel(n: nat) -> KernelSpec {
    single_output_kernel(
        ArithExpr::Cmp(CmpOp::Eq, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(0))),
        ArithExpr::Const(0),
        ArithExpr::Reduce(
            1,
            Box::new(ArithExpr::Const(n as int)),
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(1)))),
                Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
            )),
        ),
    )
}

/// Dot product correctness.
pub proof fn lemma_dot_product_kernel_correct(
    a: Seq<int>, b: Seq<int>, n: nat,
)
    requires a.len() >= n as int, b.len() >= n as int,
    ensures ({
        let k = dot_product_kernel(n);
        let env = thread_env_1d(0);
        let inputs = seq![a, b];
        arith_eval_with_arrays(&k.outputs[0].compute, env, inputs)
            == dot_product_spec(a, b, n)
    }),
{
    let k = dot_product_kernel(n);
    let env = thread_env_1d(0);
    let inputs = seq![a, b];
    let body = ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(1)))),
        Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
    );
    let bound_expr = ArithExpr::Const(n as int);
    assert(arith_eval_with_arrays(&bound_expr, env, inputs) == n as int);
    lemma_dot_reduce_matches(a, b, n, env, inputs, &body);
}

/// Inductive helper for dot product.
proof fn lemma_dot_reduce_matches(
    a: Seq<int>, b: Seq<int>, kk: nat,
    env: Seq<int>, inputs: Seq<Seq<int>>,
    body: &ArithExpr,
)
    requires
        a.len() >= kk as int, b.len() >= kk as int,
        env.len() >= 1,
        inputs.len() == 2, inputs[0] == a, inputs[1] == b,
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
        let ext_env = env_with(env, 1, (kk - 1) as int);
        assert(ext_env.len() >= 2);
        assert(ext_env[1] == (kk - 1) as int);
        let idx = (kk - 1) as nat;
        let var1 = ArithExpr::Var(1);
        assert(arith_eval_with_arrays(&var1, ext_env, inputs) == idx as int);
        crate::arith_expr::lemma_eval_with_arrays_index(
            0, &var1, ext_env, inputs, idx as int);
        crate::arith_expr::lemma_eval_with_arrays_index(
            1, &var1, ext_env, inputs, idx as int);
        let idx_a = ArithExpr::Index(0, Box::new(ArithExpr::Var(1)));
        let idx_b = ArithExpr::Index(1, Box::new(ArithExpr::Var(1)));
        crate::arith_expr::lemma_eval_with_arrays_mul(&idx_a, &idx_b, ext_env, inputs);
    }
}

// ══════════════════════════════════════════════════════════════
// 1D Convolution kernel — demonstrates sliding-window gather
// ══════════════════════════════════════════════════════════════

/// 1D convolution spec: out[i] = Σ_{d=0}^{W-1} input[i+d] * weight[d]
/// where W is the kernel width. No padding — output is N-W+1 elements.
pub open spec fn conv1d_spec(
    input: Seq<int>, weight: Seq<int>, w: nat, i: nat,
) -> int
    decreases w,
{
    if w == 0 { 0 }
    else {
        conv1d_spec(input, weight, (w - 1) as nat, i)
            + input[(i + (w - 1)) as int] * weight[(w - 1) as int]
    }
}

/// 1D convolution kernel: out[i] = Σ_{d=0}^{W-1} input[i+d] * weight[d]
/// Variable 0 = thread id (output position i), Variable 1 = reduce var (d).
/// Buffer 0 = input, Buffer 1 = weight.
pub open spec fn conv1d_kernel(n: nat, w: nat) -> KernelSpec {
    single_output_kernel(
        // Guard: i < n - w + 1 (valid output range)
        ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const((n - w + 1) as int))),
        // Scatter: identity (output[i] = result)
        ArithExpr::Var(0),
        // Compute: Σ_{d=0}^{W-1} input[i+d] * weight[d]
        ArithExpr::Reduce(
            1,  // reduce variable d
            Box::new(ArithExpr::Const(w as int)),
            Box::new(ArithExpr::Mul(
                // input[i + d]
                Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Add(
                    Box::new(ArithExpr::Var(0)),
                    Box::new(ArithExpr::Var(1)),
                )))),
                // weight[d]
                Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
            )),
        ),
    )
}

/// 1D convolution correctness.
pub proof fn lemma_conv1d_kernel_correct(
    input: Seq<int>, weight: Seq<int>,
    n: nat, w: nat, i: nat,
)
    requires
        w > 0,
        i + w <= n,
        input.len() >= n as int,
        weight.len() >= w as int,
    ensures ({
        let k = conv1d_kernel(n, w);
        let env = thread_env_1d(i);
        let inputs = seq![input, weight];
        arith_eval_with_arrays(&k.outputs[0].compute, env, inputs)
            == conv1d_spec(input, weight, w, i)
    }),
{
    let k = conv1d_kernel(n, w);
    let env = thread_env_1d(i);
    let inputs = seq![input, weight];
    let body = ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Add(
            Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Var(1)),
        )))),
        Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
    );
    let bound_expr = ArithExpr::Const(w as int);
    assert(arith_eval_with_arrays(&bound_expr, env, inputs) == w as int);
    lemma_conv1d_reduce_matches(input, weight, w, i, env, inputs, &body);
}

/// Inductive helper for convolution.
proof fn lemma_conv1d_reduce_matches(
    input: Seq<int>, weight: Seq<int>,
    w: nat, i: nat,
    env: Seq<int>, inputs: Seq<Seq<int>>,
    body: &ArithExpr,
)
    requires
        input.len() >= (i + w) as int,
        weight.len() >= w as int,
        env.len() >= 1,
        env[0] == i as int,
        inputs.len() == 2,
        inputs[0] == input,
        inputs[1] == weight,
        *body == ArithExpr::Mul(
            Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Var(0)),
                Box::new(ArithExpr::Var(1)),
            )))),
            Box::new(ArithExpr::Index(1, Box::new(ArithExpr::Var(1)))),
        ),
    ensures
        reduce_sum_arrays(1, w as int, body, env, inputs)
            == conv1d_spec(input, weight, w, i),
    decreases w,
{
    if w == 0 {
    } else {
        lemma_conv1d_reduce_matches(input, weight, (w - 1) as nat, i, env, inputs, body);

        let d = (w - 1) as nat;
        let ext_env = env_with(env, 1, d as int);
        assert(ext_env.len() >= 2);
        assert(ext_env[0] == i as int);
        assert(ext_env[1] == d as int);

        // Bounds
        let id = i + d;
        assert(id < input.len());
        assert(d < weight.len());

        // Help Z3 unfold: Add(Var(0), Var(1)) = i + d
        assert(arith_eval_with_arrays(&ArithExpr::Var(0), ext_env, inputs) == i as int);
        assert(arith_eval_with_arrays(&ArithExpr::Var(1), ext_env, inputs) == d as int);
        let add_expr = ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Var(1)));
        crate::arith_expr::lemma_eval_with_arrays_add(
            &ArithExpr::Var(0), &ArithExpr::Var(1), ext_env, inputs);

        // Help Z3: Index(0, i+d) = input[i+d], Index(1, d) = weight[d]
        crate::arith_expr::lemma_eval_with_arrays_index(
            0, &add_expr, ext_env, inputs, id as int);
        let var1 = ArithExpr::Var(1);
        crate::arith_expr::lemma_eval_with_arrays_index(
            1, &var1, ext_env, inputs, d as int);

        // Help Z3: Mul
        let idx_input = ArithExpr::Index(0, Box::new(add_expr));
        let idx_weight = ArithExpr::Index(1, Box::new(ArithExpr::Var(1)));
        crate::arith_expr::lemma_eval_with_arrays_mul(&idx_input, &idx_weight, ext_env, inputs);
    }
}

// ══════════════════════════════════════════════════════════════
// Scan (prefix sum) kernel — demonstrates variable-bound Reduce
// ══════════════════════════════════════════════════════════════

/// Partial sum spec: Σ_{j=0}^{kk-1} input[j]. Works for kk=0 (returns 0).
pub open spec fn partial_sum(input: Seq<int>, kk: nat) -> int
    decreases kk,
{
    if kk == 0 { 0 }
    else { partial_sum(input, (kk - 1) as nat) + input[(kk - 1) as int] }
}

/// Inclusive prefix sum: out[i] = partial_sum(input, i + 1) = Σ_{j=0}^{i} input[j]
pub open spec fn prefix_sum_spec(input: Seq<int>, i: nat) -> int {
    partial_sum(input, i + 1)
}

/// Inclusive scan kernel: out[i] = Σ_{j=0}^{i} input[j]
/// Variable 0 = thread id (i), Variable 1 = reduce var (j).
/// The bound is Add(Var(0), Const(1)) — depends on thread id!
pub open spec fn scan_kernel(n: nat) -> KernelSpec {
    single_output_kernel(
        ArithExpr::Cmp(CmpOp::Lt, Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(n as int))),
        ArithExpr::Var(0),
        ArithExpr::Reduce(
            1,  // reduce variable j
            Box::new(ArithExpr::Add(Box::new(ArithExpr::Var(0)), Box::new(ArithExpr::Const(1)))),
            Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(1)))),
        ),
    )
}

/// Scan kernel correctness: connects to prefix_sum_spec.
pub proof fn lemma_scan_kernel_correct(
    input: Seq<int>, n: nat, i: nat,
)
    requires
        n > 0,
        i < n,
        input.len() >= n as int,
    ensures ({
        let k = scan_kernel(n);
        let env = thread_env_1d(i);
        let inputs = seq![input];
        arith_eval_with_arrays(&k.outputs[0].compute, env, inputs)
            == prefix_sum_spec(input, i)
    }),
{
    let k = scan_kernel(n);
    let env = thread_env_1d(i);
    let inputs = seq![input];
    let body = ArithExpr::Index(0, Box::new(ArithExpr::Var(1)));

    // The bound is Add(Var(0), Const(1)) which evaluates to i+1
    assert(arith_eval_with_arrays(&ArithExpr::Var(0), env, inputs) == i as int);
    assert(arith_eval_with_arrays(&ArithExpr::Const(1), env, inputs) == 1);
    crate::arith_expr::lemma_eval_with_arrays_add(
        &ArithExpr::Var(0), &ArithExpr::Const(1), env, inputs);

    lemma_scan_reduce_matches(input, i + 1, i, env, inputs, &body);
    // i + 1 > 0, so the second ensures gives us the prefix_sum_spec equality
}

/// Inductive helper: reduce_sum_arrays for scan body matches partial_sum.
proof fn lemma_scan_reduce_matches(
    input: Seq<int>, kk: nat, i: nat,
    env: Seq<int>, inputs: Seq<Seq<int>>,
    body: &ArithExpr,
)
    requires
        kk <= i + 1,
        input.len() > i as int,
        env.len() >= 1,
        env[0] == i as int,
        inputs.len() == 1,
        inputs[0] == input,
        *body == ArithExpr::Index(0, Box::new(ArithExpr::Var(1))),
    ensures
        reduce_sum_arrays(1, kk as int, body, env, inputs) == partial_sum(input, kk),
    decreases kk,
{
    if kk == 0 {
    } else {
        lemma_scan_reduce_matches(input, (kk - 1) as nat, i, env, inputs, body);

        let d = (kk - 1) as nat;
        let ext_env = env_with(env, 1, d as int);
        assert(ext_env[1] == d as int);
        assert(d < input.len());

        crate::arith_expr::lemma_eval_with_arrays_index(
            0, &ArithExpr::Var(1), ext_env, inputs, d as int);
        assert(arith_eval_with_arrays(body, ext_env, inputs) == input[d as int]);
    }
}

} // verus!
