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
/// arith_eval(delinearize_coord_expr(0, shape, i), [x]) == delinearize(x, shape)[i].
///
/// The mixed-radix identity: delinearize(x, shape)[i] = (x / prefix_product(i)) % shape[i].
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

    if i == 0 {
        lemma_arith_eval_mod_div(0, pp as int, shape[0] as int, seq![x as int]);
        assert((x as int) / 1int == x as int);
        crate::proof::shape_lemmas::lemma_delinearize_len(x, shape);
    } else {
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0
            by { assert(rest[j] == shape[j + 1]); };
        };
        crate::proof::shape_lemmas::lemma_delinearize_len(x, shape);

        // x / shape[0] < shape_size(rest)
        crate::runtime::shape_helpers::lemma_shape_size_split(shape, 1);
        assert(shape.take(1) =~= seq![shape.first()]);
        crate::proof::shape_lemmas::lemma_shape_size_single(shape.first());
        crate::proof::shape_lemmas::lemma_shape_size_positive(rest);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, shape.first(), shape_size(rest));

        // IH on rest
        lemma_delinearize_coord_expr_correct(rest, (i - 1) as nat, x / shape.first());

        // pp(shape, i) == shape[0] * pp(rest, i-1), then div_div
        let pp_rest = shape_prefix_product(rest, (i - 1) as nat);
        lemma_prefix_product_positive(rest, (i - 1) as nat);
        lemma_prefix_product_split(shape, i);
        assert(pp == shape.first() * pp_rest);
        crate::proof::integer_helpers::lemma_div_div(x, shape.first(), pp_rest);
        assert((x as int) / (pp as int) == ((x / shape.first()) as int) / (pp_rest as int)) by (nonlinear_arith)
            requires pp == shape.first() * pp_rest,
                     (x as int) / ((shape.first() as int) * (pp_rest as int)) == ((x as int) / (shape.first() as int)) / (pp_rest as int);

        assert(rest[(i - 1) as int] == shape[i as int]);

        // ArithExpr evaluation and delinearize connection
        lemma_arith_eval_mod_div(0, pp as int, shape[i as int] as int, seq![x as int]);
        lemma_arith_eval_mod_div(0, pp_rest as int, rest[(i - 1) as int] as int, seq![(x / shape.first()) as int]);
        crate::proof::shape_lemmas::lemma_delinearize_concat(x, seq![shape.first()], rest);
        crate::proof::shape_lemmas::lemma_shape_size_single(shape.first());
        assert(shape =~= seq![shape.first()].add(rest));
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
// Bridge: shape_prefix_product ↔ shape_size ↔ shape_prefix_products ↔ column_major_strides
// ══════════════════════════════════════════════════════════════

/// shape_prefix_product(shape, i) == shape_size(shape.take(i)).
/// This is the fundamental identity connecting prefix products to shape_size.
pub proof fn lemma_prefix_product_eq_shape_size(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        i <= shape.len(),
    ensures
        shape_prefix_product(shape, i) == shape_size(shape.take(i as int)),
    decreases i,
{
    if i == 0 {
        assert(shape.take(0) =~= Seq::<nat>::empty());
    } else {
        lemma_prefix_product_eq_shape_size(shape, (i - 1) as nat);
        assert(shape.take(i as int) =~= shape.take((i - 1) as int).add(seq![shape[(i - 1) as int]]));
        crate::proof::product_lemmas::lemma_shape_size_append(
            shape.take((i - 1) as int),
            seq![shape[(i - 1) as int]],
        );
        crate::proof::shape_lemmas::lemma_shape_size_single(shape[(i - 1) as int]);
        // pp(shape, i) = shape[i-1] * pp(shape, i-1)
        // shape_size(take(i)) = shape_size(take(i-1)) * shape[i-1]
        // = pp(shape, i-1) * shape[i-1] (by IH)
        // Commutativity: a * b == b * a
        assert(shape_prefix_product(shape, i) == shape_size(shape.take(i as int)))
            by (nonlinear_arith)
            requires
                shape_prefix_product(shape, i) == shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat),
                shape_prefix_product(shape, (i - 1) as nat) == shape_size(shape.take((i - 1) as int)),
                shape_size(shape.take(i as int)) == shape_size(shape.take((i - 1) as int)) * shape_size(seq![shape[(i - 1) as int]]),
                shape_size(seq![shape[(i - 1) as int]]) == shape[(i - 1) as int];
    }
}

/// shape_prefix_product(shape, i) == shape_prefix_products(shape)[i].
pub proof fn lemma_prefix_product_eq_prefix_products(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        i <= shape.len(),
    ensures
        shape_prefix_product(shape, i) == crate::inverse::shape_prefix_products(shape)[i as int],
{
    lemma_prefix_product_eq_shape_size(shape, i);
    crate::proof::inverse_lemmas::lemma_prefix_products_value(shape, i);
}

/// shape_prefix_product(shape, i) as int == column_major_strides(shape)[i] for i < shape.len().
pub proof fn lemma_prefix_product_eq_cm_stride(shape: Seq<nat>, i: nat)
    requires
        shape_valid(shape),
        i < shape.len(),
    ensures
        shape_prefix_product(shape, i) as int == column_major_strides(shape)[i as int],
    decreases i,
{
    crate::proof::injectivity_lemmas::lemma_column_major_strides_len(shape);
    if i == 0 {
        crate::proof::inverse_lemmas::lemma_column_major_strides_first(shape);
    } else {
        // cm(shape)[i] = shape[0] * cm(shape.skip(1))[i-1]  (from cm recursive def + scale)
        // pp(shape, i) = shape[i-1] * pp(shape, i-1)
        // By IH on shape.skip(1) with index i-1:
        //   pp(skip(1), i-1) as int == cm(skip(1))[i-1]
        // pp_split: pp(shape, i) == shape[0] * pp(skip(1), i-1)
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0
            by { assert(rest[j] == shape[j + 1]); };
        };
        lemma_prefix_product_split(shape, i);
        // pp(shape, i) == shape[0] * pp(rest, i-1)
        lemma_prefix_product_eq_cm_stride(rest, (i - 1) as nat);
        // pp(rest, i-1) as int == cm(rest)[i-1]
        // So pp(shape, i) as int == shape[0] * cm(rest)[i-1] (as int)
        // Need: cm(shape)[i] == shape[0] * cm(rest)[i-1]
        // This follows from the cm definition: cm(shape) = [1] ++ scale(cm(rest), shape[0])
        // cm(shape)[i] = scale(cm(rest), shape[0])[i-1] = shape[0] * cm(rest)[i-1]
        crate::proof::injectivity_lemmas::lemma_column_major_strides_len(rest);
        assert(column_major_strides(shape)[i as int]
            == (shape.first() as int) * column_major_strides(rest)[(i - 1) as int]);
    }
}

// ══════════════════════════════════════════════════════════════
// General Box-unfolding helpers for arith_eval
// ══════════════════════════════════════════════════════════════

/// Helper: arith_eval of Mul(expr, Const(c)) = arith_eval(expr, env) * c.
proof fn lemma_arith_eval_mul_expr_const(expr: &ArithExpr, c: int, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Mul(Box::new(*expr), Box::new(ArithExpr::Const(c))), env)
            == arith_eval(expr, env) * c,
{
    assert(arith_eval(&ArithExpr::Const(c), env) == c);
}

/// Helper: arith_eval of Add(a, b) = arith_eval(a, env) + arith_eval(b, env).
proof fn lemma_arith_eval_add(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Add(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) + arith_eval(b, env),
{}

/// Helper: arith_eval of Mul(a, b) = arith_eval(a, env) * arith_eval(b, env).
proof fn lemma_arith_eval_mul(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Mul(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) * arith_eval(b, env),
{}

/// Helper: arith_eval of Index(arr, idx) = arith_eval(idx, env).
proof fn lemma_arith_eval_index(arr: nat, idx: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Index(arr, Box::new(*idx)), env) == arith_eval(idx, env),
{}

/// Helper: arith_eval of Div(a, b) — handles both zero and nonzero denom.
proof fn lemma_arith_eval_div(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(b, env) != 0 ==> arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) / arith_eval(b, env),
        arith_eval(b, env) == 0 ==> arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env) == 0,
{}

/// Helper: arith_eval of Mod(a, b) — handles both zero and nonzero denom.
proof fn lemma_arith_eval_mod(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(b, env) != 0 ==> arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) % arith_eval(b, env),
        arith_eval(b, env) == 0 ==> arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env) == 0,
{}

/// Helper: arith_eval_fits_i64 for an Add node.
proof fn lemma_fits_i64_add(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Add(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(a, env) + arith_eval(b, env),
        arith_eval(a, env) + arith_eval(b, env) <= i64::MAX as int,
{}

/// Helper: arith_eval_fits_i64 for a Mul node.
proof fn lemma_fits_i64_mul(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Mul(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(a, env) * arith_eval(b, env),
        arith_eval(a, env) * arith_eval(b, env) <= i64::MAX as int,
{}

/// Helper: arith_eval_fits_i64 for a Div node.
proof fn lemma_fits_i64_div(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env),
        arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env) <= i64::MAX as int,
{}

/// Helper: arith_eval_fits_i64 for a Mod node.
proof fn lemma_fits_i64_mod(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env),
        arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env) <= i64::MAX as int,
{}

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

/// Helper: for a linear index expr (Add(Mul(Var,Const),Var)), eval_with_arrays == arith_eval.
proof fn lemma_eval_with_arrays_linear_index(v1: nat, c: int, v2: nat, env: Seq<int>, arrays: Seq<Seq<int>>)
    requires (v1 as int) < env.len(), (v2 as int) < env.len(),
    ensures
        arith_eval_with_arrays(&ArithExpr::Add(
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Var(v1)), Box::new(ArithExpr::Const(c)),
            )),
            Box::new(ArithExpr::Var(v2)),
        ), env, arrays) == env[v1 as int] * c + env[v2 as int],
{
    // eval_with_arrays for Var and Const is the same as arith_eval
    assert(arith_eval_with_arrays(&ArithExpr::Var(v1), env, arrays) == env[v1 as int]);
    assert(arith_eval_with_arrays(&ArithExpr::Const(c), env, arrays) == c);
    assert(arith_eval_with_arrays(&ArithExpr::Var(v2), env, arrays) == env[v2 as int]);
    let mul_expr = ArithExpr::Mul(Box::new(ArithExpr::Var(v1)), Box::new(ArithExpr::Const(c)));
    assert(arith_eval_with_arrays(&mul_expr, env, arrays) == env[v1 as int] * c);
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

    // Establish that eval_with_arrays of the index exprs gives the expected values
    lemma_eval_with_arrays_linear_index(0, k_size as int, 2, env, arrays);
    assert(arith_eval_with_arrays(&a_idx_expr, env, arrays) == a_idx_val);
    lemma_eval_with_arrays_linear_index(2, n as int, 1, env, arrays);
    assert(arith_eval_with_arrays(&b_idx_expr, env, arrays) == b_idx_val);

    // Step 1: Index(0, a_idx_expr) evaluates to a_data[i*K+k]
    lemma_eval_with_arrays_index(0, &a_idx_expr, env, arrays, a_idx_val);
    let idx_a = ArithExpr::Index(0, Box::new(a_idx_expr));

    // Step 2: Index(1, b_idx_expr) evaluates to b_data[k*N+j]
    lemma_eval_with_arrays_index(1, &b_idx_expr, env, arrays, b_idx_val);
    let idx_b = ArithExpr::Index(1, Box::new(b_idx_expr));

    // Step 3: Mul(idx_a, idx_b) = a_data[i*K+k] * b_data[k*N+j]
    lemma_eval_with_arrays_mul(&idx_a, &idx_b, env, arrays);
}

// ══════════════════════════════════════════════════════════════
// Offset expression correctness
// ══════════════════════════════════════════════════════════════

/// Inductive helper: offset_expr_skip evaluates to the tail dot product.
///
/// arith_eval(offset_expr_skip(0, shape, stride, start), [x])
///     == dot_product_nat_int(delinearize(x, shape).skip(start), stride.skip(start))
proof fn lemma_offset_expr_skip_correct(
    shape: Seq<nat>, stride: Seq<int>, x: nat, start: nat,
)
    requires
        shape_valid(shape),
        shape.len() == stride.len(),
        start <= shape.len(),
        x < shape_size(shape),
    ensures
        arith_eval(&offset_expr_skip(0, shape, stride, start), seq![x as int])
            == dot_product_nat_int(
                delinearize(x, shape).skip(start as int),
                stride.skip(start as int),
            ),
    decreases shape.len() - start,
{
    let coords = delinearize(x, shape);
    let env = seq![x as int];
    crate::proof::shape_lemmas::lemma_delinearize_len(x, shape);

    if start >= shape.len() {
        // offset_expr_skip = Const(0), coords/stride tails are empty
        let tail_c = coords.skip(start as int);
        let tail_s = stride.skip(start as int);
        assert(tail_c.len() == 0);
        assert(tail_s.len() == 0);
        crate::proof::offset_lemmas::lemma_dot_product_empty(tail_s);
    } else {
        // arith_eval of coord_expr == delinearize(x, shape)[start]
        lemma_delinearize_coord_expr_correct(shape, start, x);
        let coord_expr = delinearize_coord_expr(0, shape, start);
        let coord_val = coords[start as int];

        // Mul(coord_expr, Const(stride[start])) evaluates to coord_val * stride[start]
        lemma_arith_eval_mul_expr_const(&coord_expr, stride[start as int], env);
        let term = ArithExpr::Mul(
            Box::new(coord_expr),
            Box::new(ArithExpr::Const(stride[start as int])),
        );
        let term_val = (coord_val as int) * stride[start as int];
        assert(arith_eval(&term, env) == term_val);

        // Dot product decomposition: skip(start) has coords[start] as first element
        let tail_coords = coords.skip(start as int);
        let tail_stride = stride.skip(start as int);
        assert(tail_coords.len() > 0);
        assert(tail_coords.first() == coord_val);
        assert(tail_stride.first() == stride[start as int]);
        assert(tail_coords.skip(1) =~= coords.skip((start + 1) as int));
        assert(tail_stride.skip(1) =~= stride.skip((start + 1) as int));

        // dot_product(tail, tail) = first*first + dot_product(rest, rest) by definition
        let dp_rest = dot_product_nat_int(
            coords.skip((start + 1) as int),
            stride.skip((start + 1) as int),
        );

        if start + 1 >= shape.len() {
            // Last mode: offset_expr_skip = term (just the Mul)
            assert(coords.skip((start + 1) as int).len() == 0);
            assert(stride.skip((start + 1) as int).len() == 0);
            crate::proof::offset_lemmas::lemma_dot_product_empty(
                stride.skip((start + 1) as int),
            );
            assert(dp_rest == 0);
            // Connect: offset_expr_skip produces `term`, eval = term_val = dp
            assert(dot_product_nat_int(tail_coords, tail_stride)
                == term_val + dp_rest);
        } else {
            // offset_expr_skip = Add(term, offset_expr_skip(start+1))
            // By IH: offset_expr_skip(start+1) evaluates to the remaining dot product
            lemma_offset_expr_skip_correct(shape, stride, x, start + 1);
            let rest_expr = offset_expr_skip(0, shape, stride, start + 1);
            assert(arith_eval(&rest_expr, env) == dp_rest);

            // Add unfolding: eval(Add(term, rest)) = eval(term) + eval(rest)
            lemma_arith_eval_add(&term, &rest_expr, env);
            assert(arith_eval(
                &ArithExpr::Add(Box::new(term), Box::new(rest_expr)), env,
            ) == term_val + dp_rest);

            // dot_product connection
            assert(dot_product_nat_int(tail_coords, tail_stride)
                == term_val + dp_rest);
        }
    }
}

/// The offset expression correctly computes layout.offset(x):
/// arith_eval(offset_expr(0, shape, stride), [x]) == LayoutSpec{shape, stride}.offset(x).
///
/// This is the key theorem connecting ArithExpr to CuTe layout offsets.
/// Combined with lemma_delinearize_coord_expr_correct, it proves that
/// the entire index computation pipeline is faithfully represented in ArithExpr.
pub proof fn lemma_offset_expr_correct(
    shape: Seq<nat>, stride: Seq<int>, x: nat,
)
    requires
        shape_valid(shape),
        shape.len() == stride.len(),
        x < shape_size(shape),
    ensures
        arith_eval(&offset_expr(0, shape, stride), seq![x as int])
            == (LayoutSpec { shape, stride }).offset(x),
{
    let coords = delinearize(x, shape);
    crate::proof::shape_lemmas::lemma_delinearize_len(x, shape);

    // offset_expr(0, shape, stride) == offset_expr_skip(0, shape, stride, 0)
    // for all cases (empty, single, multi-mode). Verus can see this from the specs.

    // Use the inductive helper with start=0
    lemma_offset_expr_skip_correct(shape, stride, x, 0);

    // skip(0) is identity
    assert(coords.skip(0) =~= coords);
    assert(stride.skip(0) =~= stride);

    // offset(x) = dot_product(delinearize(x, shape), stride) by definition
}

// ══════════════════════════════════════════════════════════════
// Runtime ArithExpr: exec-mode type mirroring ArithExpr with i64/u32
// ══════════════════════════════════════════════════════════════

/// Runtime arithmetic expression with concrete integer types for exec code.
pub enum RuntimeArithExpr {
    Const(i64),
    Var(u32),
    Add(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Mul(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Div(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Mod(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Index(u32, Box<RuntimeArithExpr>),
}

impl RuntimeArithExpr {
    /// Map to spec ArithExpr.
    pub open spec fn view_spec(&self) -> ArithExpr
        decreases self,
    {
        match self {
            RuntimeArithExpr::Const(c) => ArithExpr::Const(*c as int),
            RuntimeArithExpr::Var(i) => ArithExpr::Var(*i as nat),
            RuntimeArithExpr::Add(a, b) => ArithExpr::Add(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Mul(a, b) => ArithExpr::Mul(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Div(a, b) => ArithExpr::Div(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Mod(a, b) => ArithExpr::Mod(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Index(arr, idx) => ArithExpr::Index(*arr as nat, Box::new(idx.view_spec())),
        }
    }
}

/// All intermediate results of evaluating expr with env fit in i64.
pub open spec fn arith_eval_fits_i64(expr: &ArithExpr, env: Seq<int>) -> bool
    decreases expr,
{
    i64::MIN as int <= arith_eval(expr, env)
    && arith_eval(expr, env) <= i64::MAX as int
    && match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) =>
            arith_eval_fits_i64(a, env) && arith_eval_fits_i64(b, env),
        ArithExpr::Index(_, idx) => arith_eval_fits_i64(idx, env),
    }
}

/// Convert i64 sequence to int sequence.
pub open spec fn i64_seq_to_int(s: Seq<i64>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[i] as int)
}

/// Evaluate a RuntimeArithExpr at exec time (scalar, no arrays).
pub fn runtime_arith_eval(expr: &RuntimeArithExpr, env: &Vec<i64>) -> (result: i64)
    requires
        arith_eval_fits_i64(&expr.view_spec(), i64_seq_to_int(env@)),
    ensures
        result as int == arith_eval(&expr.view_spec(), i64_seq_to_int(env@)),
    decreases expr,
{
    let ghost env_spec = i64_seq_to_int(env@);
    match expr {
        RuntimeArithExpr::Const(c) => {
            return *c;
        },
        RuntimeArithExpr::Var(i) => {
            if (*i as usize) < env.len() {
                proof {
                    assert(i64_seq_to_int(env@)[*i as int] == env@[*i as int] as int);
                }
                return env[*i as usize];
            } else {
                return 0i64;
            }
        },
        RuntimeArithExpr::Add(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                lemma_arith_eval_add(&a.view_spec(), &b.view_spec(), env_spec);
                lemma_fits_i64_add(&a.view_spec(), &b.view_spec(), env_spec);
            }
            return va + vb;
        },
        RuntimeArithExpr::Mul(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                lemma_arith_eval_mul(&a.view_spec(), &b.view_spec(), env_spec);
                lemma_fits_i64_mul(&a.view_spec(), &b.view_spec(), env_spec);
            }
            return va * vb;
        },
        RuntimeArithExpr::Div(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                assert(expr.view_spec() == ArithExpr::Div(
                    Box::new(a.view_spec()), Box::new(b.view_spec())));
                lemma_arith_eval_div(&a.view_spec(), &b.view_spec(), env_spec);
            }
            if vb == 0 {
                return 0i64;
            } else {
                proof {
                    lemma_fits_i64_div(&a.view_spec(), &b.view_spec(), env_spec);
                    let div_val = (va as int) / (vb as int);
                    assert(div_val <= i64::MAX as int);
                    assert(div_val >= i64::MIN as int);
                    assert((i64::MIN as int) / (-1int) > i64::MAX as int) by (nonlinear_arith);
                    // Connect arith_eval on the Div node to va/vb
                    let div_expr = ArithExpr::Div(
                        Box::new(a.view_spec()), Box::new(b.view_spec()));
                    assert(arith_eval(&div_expr, env_spec) == div_val);
                    assert(arith_eval(&expr.view_spec(), env_spec) == div_val);
                }
                return va / vb;
            }
        },
        RuntimeArithExpr::Mod(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                assert(expr.view_spec() == ArithExpr::Mod(
                    Box::new(a.view_spec()), Box::new(b.view_spec())));
                lemma_arith_eval_mod(&a.view_spec(), &b.view_spec(), env_spec);
            }
            if vb == 0 {
                return 0i64;
            } else if va == i64::MIN && vb == -1i64 {
                proof {
                    assert((i64::MIN as int) % (-1int) == 0int) by (nonlinear_arith);
                }
                return 0i64;
            } else {
                proof {
                    let mod_expr = ArithExpr::Mod(
                        Box::new(a.view_spec()), Box::new(b.view_spec()));
                    assert(arith_eval(&mod_expr, env_spec) == (va as int) % (vb as int));
                    assert(arith_eval(&expr.view_spec(), env_spec) == (va as int) % (vb as int));
                }
                return va % vb;
            }
        },
        RuntimeArithExpr::Index(_arr, idx) => {
            proof { lemma_arith_eval_index(*_arr as nat, &idx.view_spec(), env_spec); }
            return runtime_arith_eval(idx, env);
        },
    }
}

} // verus!
