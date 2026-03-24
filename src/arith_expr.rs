use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Verified arithmetic expression language for GPU codegen
// ══════════════════════════════════════════════════════════════

/// Arithmetic expression — the IR shared between Verus verification and GPU codegen.
/// Every CuTe index computation reduces to this language.
pub enum ArithExpr {
    /// Integer constant
    Const(int),
    /// Variable reference by index (into an environment)
    Var(nat),
    /// Addition
    Add(Box<ArithExpr>, Box<ArithExpr>),
    /// Multiplication
    Mul(Box<ArithExpr>, Box<ArithExpr>),
    /// Integer division (truncating toward zero)
    Div(Box<ArithExpr>, Box<ArithExpr>),
    /// Integer modulo
    Mod(Box<ArithExpr>, Box<ArithExpr>),
    /// Array index: arrays[arr_idx][index_expr]
    /// Evaluates index_expr, looks up in the arrays environment.
    Index(nat, Box<ArithExpr>),
}

/// Evaluate an arithmetic expression.
/// - `env`: scalar variable bindings (for Var)
/// - `arrays`: array data (for Index) — arrays[arr_idx] is a Seq<int>
pub open spec fn arith_eval(expr: &ArithExpr, env: Seq<int>) -> int
    decreases expr,
{
    match expr {
        ArithExpr::Const(c) => *c,
        ArithExpr::Var(i) => if (*i as int) < env.len() { env[*i as int] } else { 0 },
        ArithExpr::Add(a, b) => arith_eval(a, env) + arith_eval(b, env),
        ArithExpr::Mul(a, b) => arith_eval(a, env) * arith_eval(b, env),
        ArithExpr::Div(a, b) => {
            let denom = arith_eval(b, env);
            if denom != 0 { arith_eval(a, env) / denom } else { 0 }
        },
        ArithExpr::Mod(a, b) => {
            let denom = arith_eval(b, env);
            if denom != 0 { arith_eval(a, env) % denom } else { 0 }
        },
        ArithExpr::Index(arr_idx, idx_expr) => {
            // Index evaluates the index expression, then looks up in env
            // For simplicity, Index is a marker — actual array lookup is handled
            // by the caller mapping Index results to array accesses.
            // We evaluate to just the index value (the offset into the array).
            arith_eval(idx_expr, env)
        },
    }
}

/// Evaluate with full array support: arrays[arr_idx][eval(idx_expr)].
pub open spec fn arith_eval_with_arrays(
    expr: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
) -> int
    decreases expr,
{
    match expr {
        ArithExpr::Const(c) => *c,
        ArithExpr::Var(i) => if (*i as int) < env.len() { env[*i as int] } else { 0 },
        ArithExpr::Add(a, b) =>
            arith_eval_with_arrays(a, env, arrays) + arith_eval_with_arrays(b, env, arrays),
        ArithExpr::Mul(a, b) =>
            arith_eval_with_arrays(a, env, arrays) * arith_eval_with_arrays(b, env, arrays),
        ArithExpr::Div(a, b) => {
            let denom = arith_eval_with_arrays(b, env, arrays);
            if denom != 0 { arith_eval_with_arrays(a, env, arrays) / denom } else { 0 }
        },
        ArithExpr::Mod(a, b) => {
            let denom = arith_eval_with_arrays(b, env, arrays);
            if denom != 0 { arith_eval_with_arrays(a, env, arrays) % denom } else { 0 }
        },
        ArithExpr::Index(arr_idx, idx_expr) => {
            let idx = arith_eval_with_arrays(idx_expr, env, arrays);
            if (*arr_idx as int) < arrays.len() && 0 <= idx && idx < arrays[*arr_idx as int].len() {
                arrays[*arr_idx as int][idx]
            } else { 0 }
        },
    }
}

// ══════════════════════════════════════════════════════════════
// ArithExpr constructors for CuTe operations
// ══════════════════════════════════════════════════════════════

/// Build an ArithExpr for: (x / prefix_product) % shape_i
/// This is delinearize(x, shape)[i] — extracting coordinate i from linear index x.
pub open spec fn delinearize_coord_expr(
    x_var: nat,          // variable index for x
    shape: Seq<nat>,
    i: nat,
) -> ArithExpr
    recommends i < shape.len(),
{
    let prefix_prod = shape_prefix_product(shape, i);
    let shape_i = shape[i as int];
    ArithExpr::Mod(
        Box::new(ArithExpr::Div(
            Box::new(ArithExpr::Var(x_var)),
            Box::new(ArithExpr::Const(prefix_prod as int)),
        )),
        Box::new(ArithExpr::Const(shape_i as int)),
    )
}

/// Prefix product: product of shape[0..i].
pub open spec fn shape_prefix_product(shape: Seq<nat>, i: nat) -> nat
    decreases i,
{
    if i == 0 { 1 }
    else { shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat) }
}

/// Build an ArithExpr for: sum_i (coord_i * stride_i)
/// This is the dot product of delinearized coordinates with strides — i.e., layout.offset(x).
pub open spec fn offset_expr(
    x_var: nat,
    shape: Seq<nat>,
    stride: Seq<int>,
) -> ArithExpr
    recommends shape.len() == stride.len(),
    decreases shape.len(),
{
    if shape.len() == 0 {
        ArithExpr::Const(0)
    } else {
        let coord_expr = delinearize_coord_expr(x_var, shape, 0);
        let term = ArithExpr::Mul(
            Box::new(coord_expr),
            Box::new(ArithExpr::Const(stride[0])),
        );
        if shape.len() == 1 {
            term
        } else {
            ArithExpr::Add(
                Box::new(term),
                Box::new(offset_expr_skip(x_var, shape, stride, 1)),
            )
        }
    }
}

/// Helper: offset expression starting from mode `start`.
pub open spec fn offset_expr_skip(
    x_var: nat,
    shape: Seq<nat>,
    stride: Seq<int>,
    start: nat,
) -> ArithExpr
    recommends shape.len() == stride.len(), start <= shape.len(),
    decreases shape.len() - start,
{
    if start >= shape.len() {
        ArithExpr::Const(0)
    } else {
        let coord_expr = delinearize_coord_expr(x_var, shape, start);
        let term = ArithExpr::Mul(
            Box::new(coord_expr),
            Box::new(ArithExpr::Const(stride[start as int])),
        );
        if start + 1 >= shape.len() {
            term
        } else {
            ArithExpr::Add(
                Box::new(term),
                Box::new(offset_expr_skip(x_var, shape, stride, start + 1)),
            )
        }
    }
}

/// GEMM A-index expression: i*K + k (row-major addressing).
/// Variables: 0=i, 1=j, 2=k.
pub open spec fn gemm_a_index_expr(k_size: nat) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Var(0)),        // i
            Box::new(ArithExpr::Const(k_size as int)),
        )),
        Box::new(ArithExpr::Var(2)),            // k
    )
}

/// GEMM B-index expression: k*N + j (row-major addressing).
/// Variables: 0=i, 1=j, 2=k.
pub open spec fn gemm_b_index_expr(n: nat) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Var(2)),        // k
            Box::new(ArithExpr::Const(n as int)),
        )),
        Box::new(ArithExpr::Var(1)),            // j
    )
}

/// GEMM MAC expression: A[i*K+k] * B[k*N+j].
/// Array 0 = A, Array 1 = B. Variables: 0=i, 1=j, 2=k.
pub open spec fn gemm_mac_expr(k_size: nat, n: nat) -> ArithExpr {
    ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(gemm_a_index_expr(k_size)))),
        Box::new(ArithExpr::Index(1, Box::new(gemm_b_index_expr(n)))),
    )
}

// ══════════════════════════════════════════════════════════════
// Correctness proofs: ArithExpr matches CuTe operations
// ══════════════════════════════════════════════════════════════

/// shape_prefix_product(shape, 0) == 1.
pub proof fn lemma_prefix_product_base(shape: Seq<nat>)
    ensures shape_prefix_product(shape, 0) == 1nat,
{}

/// shape_prefix_product is the product of shape[0..i].
pub proof fn lemma_prefix_product_step(shape: Seq<nat>, i: nat)
    requires i > 0, i <= shape.len(),
    ensures shape_prefix_product(shape, i) == shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat),
{}

/// Helper: arith_eval of Mod(Div(Var(v), Const(d)), Const(m)) = (env[v] / d) % m.
/// This isolates the ArithExpr unfolding so z3 doesn't have to unfold 5 levels deep.
proof fn lemma_arith_eval_mod_div(v: nat, d: int, m: int, env: Seq<int>)
    requires
        (v as int) < env.len(),
        d > 0,
        m > 0,
    ensures
        arith_eval(&ArithExpr::Mod(
            Box::new(ArithExpr::Div(
                Box::new(ArithExpr::Var(v)),
                Box::new(ArithExpr::Const(d)),
            )),
            Box::new(ArithExpr::Const(m)),
        ), env) == (env[v as int] / d) % m,
{
    // Unfold step by step:
    let inner_div = ArithExpr::Div(
        Box::new(ArithExpr::Var(v)),
        Box::new(ArithExpr::Const(d)),
    );
    assert(arith_eval(&ArithExpr::Const(d), env) == d);
    assert(arith_eval(&ArithExpr::Var(v), env) == env[v as int]);
    assert(arith_eval(&inner_div, env) == env[v as int] / d);
    assert(arith_eval(&ArithExpr::Const(m), env) == m);
}

/// Delinearize coordinate expr is correct:
/// arith_eval(delinearize_coord_expr(0, shape, i), [x]) == delinearize(x, shape)[i]
///
/// Proof sketch: delinearize(x, shape)[i] = (x / prefix_product(i)) % shape[i]
/// by induction on the recursive delinearize definition. The ArithExpr computes
/// exactly this expression.
pub proof fn lemma_delinearize_coord_expr_correct(
    shape: Seq<nat>, i: nat, x: nat,
)
    requires
        shape_valid(shape),
        i < shape.len(),
        x < shape_size(shape),
    ensures
        arith_eval(&delinearize_coord_expr(0, shape, i), seq![x as int])
            == delinearize(x, shape)[i as int] as int,
    decreases i,
{
    lemma_prefix_product_positive(shape, i);
    let pp = shape_prefix_product(shape, i);
    assert(pp > 0nat);

    if i == 0 {
        assert(shape_prefix_product(shape, 0) == 1nat);
        assert(shape[0] > 0nat);
        // Use helper for ArithExpr eval
        lemma_arith_eval_mod_div(0, pp as int, shape[0] as int, seq![x as int]);
        // (x / 1) % shape[0] = x % shape[0]
        assert((x as int) / 1int == x as int);
        // delinearize(x, shape)[0] = x % shape[0]
        crate::proof::shape_lemmas::lemma_delinearize_len(x, shape);
    } else {
        // delinearize(x, shape)[i] = delinearize(x / shape[0], skip(1))[i-1]
        // By IH: = ((x/shape[0]) / pp_rest(i-1)) % shape_rest[i-1]
        //        = (x / (shape[0] * pp_rest(i-1))) % shape[i]
        //        = (x / pp(i)) % shape[i]
        // ArithExpr evaluates to the same.
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0
            by { assert(rest[j] == shape[j + 1]); };
        };
        crate::proof::shape_lemmas::lemma_delinearize_len(x, shape);
        // The delinearize spec gives [i] = delinearize(x / shape[0], skip(1))[i-1]
        // And prefix_product(shape, i) = shape[i-1] * prefix_product(shape, i-1)
        // This matches the ArithExpr evaluation.
        // Full inductive proof requires connecting delinearize recursion to prefix_product.
        // The key identity: (x / pp(i)) % shape[i] = delinearize(x, shape)[i]
        // is proved by the mixed-radix theorem (each coordinate extracts the i-th digit).
        // x / shape[0] < shape_size(rest) (from x < shape[0] * shape_size(rest))
        crate::runtime::shape_helpers::lemma_shape_size_split(shape, 1);
        assert(shape.take(1) =~= seq![shape.first()]);
        crate::proof::shape_lemmas::lemma_shape_size_single(shape.first());
        crate::proof::shape_lemmas::lemma_shape_size_positive(rest);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, shape.first(), shape_size(rest));
        lemma_delinearize_coord_expr_correct(rest, (i - 1) as nat, x / shape.first());
        // Bridge: shape_prefix_product(shape, i) = shape[i-1] * pp(i-1)
        // For the rest: shape_prefix_product(rest, i-1) and shape_prefix_product(shape, i)
        // pp(shape, i) = shape[i-1] * pp(shape, i-1)
        // pp(rest, i-1) = rest[i-2] * pp(rest, i-2) = shape[i-1] * pp(rest, i-2) ... complex
        // Actually: pp(shape, i) counts shape[0..i], pp(rest, i-1) counts rest[0..i-1] = shape[1..i]
        // So pp(shape, i) = shape[0] * pp(rest, i-1)
        // div_div: x / (a * b) = (x / a) / b
        let pp_rest = shape_prefix_product(rest, (i - 1) as nat);
        lemma_prefix_product_positive(rest, (i - 1) as nat);

        // Key bridge: pp(shape, i) == shape[0] * pp(rest, i-1)
        lemma_prefix_product_split(shape, i);
        assert(pp == shape.first() * pp_rest);

        // div_div: x / (shape[0] * pp_rest) == (x / shape[0]) / pp_rest
        crate::proof::integer_helpers::lemma_div_div(x, shape.first(), pp_rest);
        assert((x as int) / (pp as int) == ((x / shape.first()) as int) / (pp_rest as int)) by (nonlinear_arith)
            requires pp == shape.first() * pp_rest,
                     (x as int) / ((shape.first() as int) * (pp_rest as int)) == ((x as int) / (shape.first() as int)) / (pp_rest as int);

        // IH gave: arith_eval(delinearize_coord_expr(0, rest, i-1), [x/shape[0]])
        //        == delinearize(x/shape[0], rest)[i-1]
        // delinearize(x, shape)[i] == delinearize(x/shape[0], rest)[i-1]  (from delinearize spec)
        // rest[i-1] == shape[i]  (from skip(1))
        assert(rest[(i - 1) as int] == shape[i as int]);

        // Step A: arith_eval of our expr at [x] = (x / pp) % shape[i]
        assert(shape[i as int] > 0nat);
        lemma_arith_eval_mod_div(0, pp as int, shape[i as int] as int, seq![x as int]);

        // Step B: (x / pp) == (x/shape[0]) / pp_rest  [div_div + prefix_split]
        // Already proved above

        // Step C: IH gave:
        //   arith_eval(delinearize_coord_expr(0, rest, i-1), [x/shape[0]])
        //   == delinearize(x/shape[0], rest)[i-1]
        // And from the helper:
        //   arith_eval(delinearize_coord_expr(0, rest, i-1), [x/shape[0]])
        //   == ((x/shape[0]) / pp_rest) % rest[i-1]
        lemma_arith_eval_mod_div(0, pp_rest as int, rest[(i - 1) as int] as int, seq![(x / shape.first()) as int]);

        // Step D: delinearize(x, shape)[i] == delinearize(x/shape[0], rest)[i-1]
        crate::proof::shape_lemmas::lemma_delinearize_concat(x, seq![shape.first()], rest);
        crate::proof::shape_lemmas::lemma_shape_size_single(shape.first());
        assert(shape =~= seq![shape.first()].add(rest));

        // Step E: chain
        // (x/pp) % shape[i] == ((x/shape[0])/pp_rest) % rest[i-1]  [div_div + rest index]
        // == delinearize(x/shape[0], rest)[i-1]                      [IH via helper]
        // == delinearize(x, shape)[i]                                 [concat]
        assert(rest[(i - 1) as int] == shape[i as int]);
        assert((x as int / (pp as int)) % (shape[i as int] as int)
            == ((x / shape.first()) as int / (pp_rest as int)) % (rest[(i - 1) as int] as int));
    }
}

/// Prefix product splits: pp(shape, i) == shape[0] * pp(skip(1), i-1) for i >= 1.
/// This connects the whole-shape prefix product to the rest-shape prefix product.
proof fn lemma_prefix_product_split(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        shape.len() > 0,
        i >= 1,
        i <= shape.len(),
    ensures
        shape_prefix_product(shape, i) == shape.first() * shape_prefix_product(shape.skip(1), (i - 1) as nat),
    decreases i,
{
    if i == 1 {
        // pp(shape, 1) = shape[0] * pp(shape, 0) = shape[0] * 1
        // shape[0] * pp(rest, 0) = shape[0] * 1
        // Both equal shape[0].
        assert(shape_prefix_product(shape, 0) == 1nat);
        assert(shape_prefix_product(shape.skip(1), 0) == 1nat);
        assert(shape[(1 - 1) as int] == shape.first());
        // pp(shape, 1) = shape.first() * 1 = shape.first()
        // shape.first() * pp(rest, 0) = shape.first() * 1 = shape.first()
        assert(shape.first() * 1nat == shape.first()) by (nonlinear_arith)
            requires shape.first() >= 0;
    } else {
        // pp(shape, i) = shape[i-1] * pp(shape, i-1)
        // By IH: pp(shape, i-1) = shape[0] * pp(rest, i-2)
        // So pp(shape, i) = shape[i-1] * shape[0] * pp(rest, i-2)
        //                 = shape[0] * (shape[i-1] * pp(rest, i-2))
        //                 = shape[0] * pp(rest, i-1)  [since rest[i-2] = shape[i-1]]
        lemma_prefix_product_split(shape, (i - 1) as nat);
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0
            by { assert(rest[j] == shape[j + 1]); };
        };
        // pp(rest, i-1) = rest[i-2] * pp(rest, i-2) = shape[i-1] * pp(rest, i-2)
        assert(rest[(i - 2) as int] == shape[(i - 1) as int]);
        // pp(shape, i) = shape[i-1] * pp(shape, i-1) = shape[i-1] * (shape[0] * pp(rest, i-2))
        //             = shape[0] * (shape[i-1] * pp(rest, i-2)) = shape[0] * pp(rest, i-1)
        assert(shape_prefix_product(shape, i)
            == shape.first() * shape_prefix_product(rest, (i - 1) as nat))
            by (nonlinear_arith)
            requires
                shape_prefix_product(shape, i) == shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat),
                shape_prefix_product(shape, (i - 1) as nat) == shape.first() * shape_prefix_product(rest, (i - 2) as nat),
                shape_prefix_product(rest, (i - 1) as nat) == rest[(i - 2) as int] * shape_prefix_product(rest, (i - 2) as nat),
                rest[(i - 2) as int] == shape[(i - 1) as int];
    }
}

/// Prefix product is always positive for valid shapes.
proof fn lemma_prefix_product_positive(shape: Seq<nat>, i: nat)
    requires shape_valid(shape), i <= shape.len(),
    ensures shape_prefix_product(shape, i) > 0,
    decreases i,
{
    if i == 0 {
    } else {
        lemma_prefix_product_positive(shape, (i - 1) as nat);
        assert(shape[(i - 1) as int] > 0nat);
        assert(shape_prefix_product(shape, i) > 0nat) by (nonlinear_arith)
            requires shape_prefix_product(shape, i)
                == shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat),
                     shape[(i - 1) as int] > 0nat,
                     shape_prefix_product(shape, (i - 1) as nat) > 0nat;
    }
}

// ══════════════════════════════════════════════════════════════
// GEMM index expression correctness
// ══════════════════════════════════════════════════════════════

/// Helper: eval of Mul(Var(v), Const(c)) = env[v] * c.
proof fn lemma_arith_eval_mul_var_const(v: nat, c: int, env: Seq<int>)
    requires (v as int) < env.len(),
    ensures arith_eval(&ArithExpr::Mul(
        Box::new(ArithExpr::Var(v)), Box::new(ArithExpr::Const(c)),
    ), env) == env[v as int] * c,
{
    assert(arith_eval(&ArithExpr::Var(v), env) == env[v as int]);
    assert(arith_eval(&ArithExpr::Const(c), env) == c);
}

/// Helper: eval of Add(a, Var(v)) = eval(a) + env[v].
proof fn lemma_arith_eval_add_var(a: &ArithExpr, v: nat, env: Seq<int>)
    requires (v as int) < env.len(),
    ensures arith_eval(&ArithExpr::Add(
        Box::new(*a), Box::new(ArithExpr::Var(v)),
    ), env) == arith_eval(a, env) + env[v as int],
{
    assert(arith_eval(&ArithExpr::Var(v), env) == env[v as int]);
}

/// Helper: eval of Add(Mul(Var(v1), Const(c)), Var(v2)) = env[v1]*c + env[v2].
proof fn lemma_arith_eval_linear_index(v1: nat, c: int, v2: nat, env: Seq<int>)
    requires
        (v1 as int) < env.len(),
        (v2 as int) < env.len(),
    ensures
        arith_eval(&ArithExpr::Add(
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Var(v1)),
                Box::new(ArithExpr::Const(c)),
            )),
            Box::new(ArithExpr::Var(v2)),
        ), env) == env[v1 as int] * c + env[v2 as int],
{
    let mul_expr = ArithExpr::Mul(
        Box::new(ArithExpr::Var(v1)), Box::new(ArithExpr::Const(c)),
    );
    lemma_arith_eval_mul_var_const(v1, c, env);
    lemma_arith_eval_add_var(&mul_expr, v2, env);
}

/// GEMM A-index is correct: evaluates to i*K + k.
pub proof fn lemma_gemm_a_index_correct(k_size: nat, i: int, j: int, k: int)
    ensures
        arith_eval(&gemm_a_index_expr(k_size), seq![i, j, k]) == i * (k_size as int) + k,
{
    lemma_arith_eval_linear_index(0, k_size as int, 2, seq![i, j, k]);
}

/// GEMM B-index is correct: evaluates to k*N + j.
pub proof fn lemma_gemm_b_index_correct(n: nat, i: int, j: int, k: int)
    ensures
        arith_eval(&gemm_b_index_expr(n), seq![i, j, k]) == k * (n as int) + j,
{
    lemma_arith_eval_linear_index(2, n as int, 1, seq![i, j, k]);
}

/// Helper: eval_with_arrays of Index(arr, idx_expr) = arrays[arr][eval_with_arrays(idx_expr)].
proof fn lemma_eval_with_arrays_index(
    arr: nat, idx_expr: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
    expected_idx: int,
)
    requires
        arith_eval_with_arrays(idx_expr, env, arrays) == expected_idx,
        (arr as int) < arrays.len(),
        0 <= expected_idx,
        expected_idx < arrays[arr as int].len(),
    ensures
        arith_eval_with_arrays(
            &ArithExpr::Index(arr, Box::new(*idx_expr)), env, arrays,
        ) == arrays[arr as int][expected_idx],
{}

/// Helper: eval_with_arrays of Mul(a, b) = eval(a) * eval(b).
proof fn lemma_eval_with_arrays_mul(
    a: &ArithExpr, b: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures
        arith_eval_with_arrays(
            &ArithExpr::Mul(Box::new(*a), Box::new(*b)), env, arrays,
        ) == arith_eval_with_arrays(a, env, arrays) * arith_eval_with_arrays(b, env, arrays),
{}

/// GEMM MAC expression is correct with arrays:
/// evaluates to A[i*K+k] * B[k*N+j].
pub proof fn lemma_gemm_mac_correct(
    k_size: nat, n: nat,
    a_data: Seq<int>, b_data: Seq<int>,
    i: nat, j: nat, k: nat,
)
    requires
        (i as int) * (k_size as int) + (k as int) >= 0,
        (i as int) * (k_size as int) + (k as int) < a_data.len(),
        (k as int) * (n as int) + (j as int) >= 0,
        (k as int) * (n as int) + (j as int) < b_data.len(),
    ensures
        arith_eval_with_arrays(
            &gemm_mac_expr(k_size, n),
            seq![i as int, j as int, k as int],
            seq![a_data, b_data],
        ) == a_data[(i as int) * (k_size as int) + (k as int)]
           * b_data[(k as int) * (n as int) + (j as int)],
{
    let env = seq![i as int, j as int, k as int];
    let arrays = seq![a_data, b_data];
    let a_idx_expr = gemm_a_index_expr(k_size);
    let b_idx_expr = gemm_b_index_expr(n);
    let a_idx_val = (i as int) * (k_size as int) + (k as int);
    let b_idx_val = (k as int) * (n as int) + (j as int);

    // Step 1: Index(0, a_idx_expr) evaluates to a_data[i*K+k]
    lemma_eval_with_arrays_index(0, &a_idx_expr, env, arrays, a_idx_val);
    let idx_a = ArithExpr::Index(0, Box::new(a_idx_expr));

    // Step 2: Index(1, b_idx_expr) evaluates to b_data[k*N+j]
    lemma_eval_with_arrays_index(1, &b_idx_expr, env, arrays, b_idx_val);
    let idx_b = ArithExpr::Index(1, Box::new(b_idx_expr));

    // Step 3: Mul(idx_a, idx_b) = a_data[i*K+k] * b_data[k*N+j]
    lemma_eval_with_arrays_mul(&idx_a, &idx_b, env, arrays);
}

// NOTE: Exec ArithExpr evaluator requires a separate runtime ArithExpr type
// (with i64/usize instead of int/nat). This lives in the codegen crate as
// the WgslExpr type, which mirrors ArithExpr for runtime use.

} // verus!
