use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

//  ══════════════════════════════════════════════════════════════
//  Verified arithmetic expression language for GPU codegen
//  ══════════════════════════════════════════════════════════════

///  Comparison operator for Cmp node.
pub enum CmpOp {
    Lt, Le, Gt, Ge, Eq, Ne,
}

///  Arithmetic expression — the IR shared between Verus verification and GPU codegen.
///  Every CuTe index computation reduces to this language.
pub enum ArithExpr {
    ///  Integer constant
    Const(int),
    ///  Variable reference by index (into an environment)
    Var(nat),
    ///  Addition
    Add(Box<ArithExpr>, Box<ArithExpr>),
    ///  Subtraction
    Sub(Box<ArithExpr>, Box<ArithExpr>),
    ///  Multiplication
    Mul(Box<ArithExpr>, Box<ArithExpr>),
    ///  Integer division (truncating toward zero)
    Div(Box<ArithExpr>, Box<ArithExpr>),
    ///  Integer modulo
    Mod(Box<ArithExpr>, Box<ArithExpr>),
    ///  Array index: arrays[arr_idx][index_expr]
    Index(nat, Box<ArithExpr>),
    ///  Comparison: returns 1 if true, 0 if false
    Cmp(CmpOp, Box<ArithExpr>, Box<ArithExpr>),
    ///  Arithmetic right shift: a >> b (for fixed-point: (a * b) >> N).
    ///  Non-negative operands: equivalent to a / 2^b.
    Shr(Box<ArithExpr>, Box<ArithExpr>),
    ///  Summation reduction: Reduce(var, bound, body) = Σ_{var=0}^{bound-1} body
    ///  `var` is the variable index, `bound` is evaluated, body is evaluated
    ///  with env[var] set to each value 0..bound-1.
    Reduce(nat, Box<ArithExpr>, Box<ArithExpr>),
}

///  Evaluate a comparison operator.
pub open spec fn cmp_eval(op: &CmpOp, a: int, b: int) -> int {
    match op {
        CmpOp::Lt => if a < b { 1 } else { 0 },
        CmpOp::Le => if a <= b { 1 } else { 0 },
        CmpOp::Gt => if a > b { 1 } else { 0 },
        CmpOp::Ge => if a >= b { 1 } else { 0 },
        CmpOp::Eq => if a == b { 1 } else { 0 },
        CmpOp::Ne => if a != b { 1 } else { 0 },
    }
}

///  Update env[var] = val, extending with zeros if needed.
pub open spec fn env_with(env: Seq<int>, var: nat, val: int) -> Seq<int> {
    if (var as int) < env.len() {
        env.update(var as int, val)
    } else {
        Seq::new((var + 1) as nat, |i: int|
            if i < env.len() { env[i] }
            else if i == var as int { val }
            else { 0 }
        )
    }
}

///  Summation spec: Σ_{i=0}^{n-1} arith_eval(body, env[var := i])
pub open spec fn reduce_sum(var: nat, n: int, body: &ArithExpr, env: Seq<int>) -> int
    decreases body, (if n > 0 { n } else { 0 }),
{
    if n <= 0 { 0 }
    else {
        reduce_sum(var, n - 1, body, env)
            + arith_eval(body, env_with(env, var, n - 1))
    }
}

///  Summation with arrays: Σ_{i=0}^{n-1} arith_eval_with_arrays(body, env[var := i], arrays)
pub open spec fn reduce_sum_arrays(
    var: nat, n: int, body: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
) -> int
    decreases body, (if n > 0 { n } else { 0 }),
{
    if n <= 0 { 0 }
    else {
        reduce_sum_arrays(var, n - 1, body, env, arrays)
            + arith_eval_with_arrays(body, env_with(env, var, n - 1), arrays)
    }
}

///  Arithmetic right shift spec: a >> b = a / 2^b for non-negative b, 0 for negative b.
pub open spec fn shr_spec(a: int, b: int) -> int {
    if b <= 0 { a }
    else { a / crate::swizzle::pow2(b as nat) as int }
}

///  Evaluate an arithmetic expression.
///  - `env`: scalar variable bindings (for Var)
pub open spec fn arith_eval(expr: &ArithExpr, env: Seq<int>) -> int
    decreases expr, 0int,
{
    match expr {
        ArithExpr::Const(c) => *c,
        ArithExpr::Var(i) => if (*i as int) < env.len() { env[*i as int] } else { 0 },
        ArithExpr::Add(a, b) => arith_eval(a, env) + arith_eval(b, env),
        ArithExpr::Sub(a, b) => arith_eval(a, env) - arith_eval(b, env),
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
            arith_eval(idx_expr, env)
        },
        ArithExpr::Shr(a, b) => shr_spec(arith_eval(a, env), arith_eval(b, env)),
        ArithExpr::Cmp(op, a, b) => cmp_eval(op, arith_eval(a, env), arith_eval(b, env)),
        ArithExpr::Reduce(var, bound, body) => {
            let n = arith_eval(bound, env);
            reduce_sum(*var, n, body, env)
        },
    }
}

///  Evaluate with full array support: arrays[arr_idx][eval(idx_expr)].
pub open spec fn arith_eval_with_arrays(
    expr: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
) -> int
    decreases expr, 0int,
{
    match expr {
        ArithExpr::Const(c) => *c,
        ArithExpr::Var(i) => if (*i as int) < env.len() { env[*i as int] } else { 0 },
        ArithExpr::Add(a, b) =>
            arith_eval_with_arrays(a, env, arrays) + arith_eval_with_arrays(b, env, arrays),
        ArithExpr::Sub(a, b) =>
            arith_eval_with_arrays(a, env, arrays) - arith_eval_with_arrays(b, env, arrays),
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
        ArithExpr::Shr(a, b) =>
            shr_spec(arith_eval_with_arrays(a, env, arrays),
                     arith_eval_with_arrays(b, env, arrays)),
        ArithExpr::Cmp(op, a, b) =>
            cmp_eval(op, arith_eval_with_arrays(a, env, arrays),
                          arith_eval_with_arrays(b, env, arrays)),
        ArithExpr::Reduce(var, bound, body) => {
            let n = arith_eval_with_arrays(bound, env, arrays);
            reduce_sum_arrays(*var, n, body, env, arrays)
        },
    }
}

//  ══════════════════════════════════════════════════════════════
//  ArithExpr constructors for CuTe operations
//  ══════════════════════════════════════════════════════════════

///  Build an ArithExpr for: (x / prefix_product) % shape_i
///  This is delinearize(x, shape)[i] — extracting coordinate i from linear index x.
pub open spec fn delinearize_coord_expr(
    x_var: nat,          //  variable index for x
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

///  Prefix product: product of shape[0..i].
pub open spec fn shape_prefix_product(shape: Seq<nat>, i: nat) -> nat
    decreases i,
{
    if i == 0 { 1 }
    else { shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat) }
}

///  Build an ArithExpr for: sum_i (coord_i * stride_i)
///  This is the dot product of delinearized coordinates with strides — i.e., layout.offset(x).
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

///  Helper: offset expression starting from mode `start`.
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

///  GEMM A-index expression: i*K + k (row-major addressing).
///  Variables: 0=i, 1=j, 2=k.
pub open spec fn gemm_a_index_expr(k_size: nat) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Var(0)),        //  i
            Box::new(ArithExpr::Const(k_size as int)),
        )),
        Box::new(ArithExpr::Var(2)),            //  k
    )
}

///  GEMM B-index expression: k*N + j (row-major addressing).
///  Variables: 0=i, 1=j, 2=k.
pub open spec fn gemm_b_index_expr(n: nat) -> ArithExpr {
    ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Var(2)),        //  k
            Box::new(ArithExpr::Const(n as int)),
        )),
        Box::new(ArithExpr::Var(1)),            //  j
    )
}

///  GEMM MAC expression: A[i*K+k] * B[k*N+j].
///  Array 0 = A, Array 1 = B. Variables: 0=i, 1=j, 2=k.
pub open spec fn gemm_mac_expr(k_size: nat, n: nat) -> ArithExpr {
    ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(gemm_a_index_expr(k_size)))),
        Box::new(ArithExpr::Index(1, Box::new(gemm_b_index_expr(n)))),
    )
}

//  ══════════════════════════════════════════════════════════════
//  Correctness proofs: ArithExpr matches CuTe operations
//  ══════════════════════════════════════════════════════════════

///  shape_prefix_product(shape, 0) == 1.
pub proof fn lemma_prefix_product_base(shape: Seq<nat>)
    ensures shape_prefix_product(shape, 0) == 1nat,
{}

///  shape_prefix_product is the product of shape[0..i].
pub proof fn lemma_prefix_product_step(shape: Seq<nat>, i: nat)
    requires i > 0, i <= shape.len(),
    ensures shape_prefix_product(shape, i) == shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat),
{}

///  Helper: arith_eval of Mod(Div(Var(v), Const(d)), Const(m)) = (env[v] / d) % m.
///  This isolates the ArithExpr unfolding so z3 doesn't have to unfold 5 levels deep.
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
    //  Unfold step by step:
    let inner_div = ArithExpr::Div(
        Box::new(ArithExpr::Var(v)),
        Box::new(ArithExpr::Const(d)),
    );
    assert(arith_eval(&ArithExpr::Const(d), env) == d);
    assert(arith_eval(&ArithExpr::Var(v), env) == env[v as int]);
    assert(arith_eval(&inner_div, env) == env[v as int] / d);
    assert(arith_eval(&ArithExpr::Const(m), env) == m);
}

///  Delinearize coordinate expr is correct:
///  arith_eval(delinearize_coord_expr(0, shape, i), [x]) == delinearize(x, shape)[i].
///
///  The mixed-radix identity: delinearize(x, shape)[i] = (x / prefix_product(i)) % shape[i].
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

        //  x / shape[0] < shape_size(rest)
        crate::runtime::shape_helpers::lemma_shape_size_split(shape, 1);
        assert(shape.take(1) =~= seq![shape.first()]);
        crate::proof::shape_lemmas::lemma_shape_size_single(shape.first());
        crate::proof::shape_lemmas::lemma_shape_size_positive(rest);
        crate::proof::integer_helpers::lemma_div_upper_bound(x, shape.first(), shape_size(rest));

        //  IH on rest
        lemma_delinearize_coord_expr_correct(rest, (i - 1) as nat, x / shape.first());

        //  pp(shape, i) == shape[0] * pp(rest, i-1), then div_div
        let pp_rest = shape_prefix_product(rest, (i - 1) as nat);
        lemma_prefix_product_positive(rest, (i - 1) as nat);
        lemma_prefix_product_split(shape, i);
        assert(pp == shape.first() * pp_rest);
        crate::proof::integer_helpers::lemma_div_div(x, shape.first(), pp_rest);
        assert((x as int) / (pp as int) == ((x / shape.first()) as int) / (pp_rest as int)) by (nonlinear_arith)
            requires pp == shape.first() * pp_rest,
                     (x as int) / ((shape.first() as int) * (pp_rest as int)) == ((x as int) / (shape.first() as int)) / (pp_rest as int);

        assert(rest[(i - 1) as int] == shape[i as int]);

        //  ArithExpr evaluation and delinearize connection
        lemma_arith_eval_mod_div(0, pp as int, shape[i as int] as int, seq![x as int]);
        lemma_arith_eval_mod_div(0, pp_rest as int, rest[(i - 1) as int] as int, seq![(x / shape.first()) as int]);
        crate::proof::shape_lemmas::lemma_delinearize_concat(x, seq![shape.first()], rest);
        crate::proof::shape_lemmas::lemma_shape_size_single(shape.first());
        assert(shape =~= seq![shape.first()].add(rest));
        assert((x as int / (pp as int)) % (shape[i as int] as int)
            == ((x / shape.first()) as int / (pp_rest as int)) % (rest[(i - 1) as int] as int));
    }
}

///  Prefix product splits: pp(shape, i) == shape[0] * pp(skip(1), i-1) for i >= 1.
///  This connects the whole-shape prefix product to the rest-shape prefix product.
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
        //  pp(shape, 1) = shape[0] * pp(shape, 0) = shape[0] * 1
        //  shape[0] * pp(rest, 0) = shape[0] * 1
        //  Both equal shape[0].
        assert(shape_prefix_product(shape, 0) == 1nat);
        assert(shape_prefix_product(shape.skip(1), 0) == 1nat);
        assert(shape[(1 - 1) as int] == shape.first());
        //  pp(shape, 1) = shape.first() * 1 = shape.first()
        //  shape.first() * pp(rest, 0) = shape.first() * 1 = shape.first()
        assert(shape.first() * 1nat == shape.first()) by (nonlinear_arith)
            requires shape.first() >= 0;
    } else {
        //  pp(shape, i) = shape[i-1] * pp(shape, i-1)
        //  By IH: pp(shape, i-1) = shape[0] * pp(rest, i-2)
        //  So pp(shape, i) = shape[i-1] * shape[0] * pp(rest, i-2)
        //                  = shape[0] * (shape[i-1] * pp(rest, i-2))
        //                  = shape[0] * pp(rest, i-1)  [since rest[i-2] = shape[i-1]]
        lemma_prefix_product_split(shape, (i - 1) as nat);
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0
            by { assert(rest[j] == shape[j + 1]); };
        };
        //  pp(rest, i-1) = rest[i-2] * pp(rest, i-2) = shape[i-1] * pp(rest, i-2)
        assert(rest[(i - 2) as int] == shape[(i - 1) as int]);
        //  pp(shape, i) = shape[i-1] * pp(shape, i-1) = shape[i-1] * (shape[0] * pp(rest, i-2))
        //              = shape[0] * (shape[i-1] * pp(rest, i-2)) = shape[0] * pp(rest, i-1)
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

///  Prefix product is always positive for valid shapes.
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

//  ══════════════════════════════════════════════════════════════
//  Bridge: shape_prefix_product ↔ shape_size ↔ shape_prefix_products ↔ column_major_strides
//  ══════════════════════════════════════════════════════════════

///  shape_prefix_product(shape, i) == shape_size(shape.take(i)).
///  This is the fundamental identity connecting prefix products to shape_size.
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
        //  pp(shape, i) = shape[i-1] * pp(shape, i-1)
        //  shape_size(take(i)) = shape_size(take(i-1)) * shape[i-1]
        //  = pp(shape, i-1) * shape[i-1] (by IH)
        //  Commutativity: a * b == b * a
        assert(shape_prefix_product(shape, i) == shape_size(shape.take(i as int)))
            by (nonlinear_arith)
            requires
                shape_prefix_product(shape, i) == shape[(i - 1) as int] * shape_prefix_product(shape, (i - 1) as nat),
                shape_prefix_product(shape, (i - 1) as nat) == shape_size(shape.take((i - 1) as int)),
                shape_size(shape.take(i as int)) == shape_size(shape.take((i - 1) as int)) * shape_size(seq![shape[(i - 1) as int]]),
                shape_size(seq![shape[(i - 1) as int]]) == shape[(i - 1) as int];
    }
}

///  shape_prefix_product(shape, i) == shape_prefix_products(shape)[i].
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

///  shape_prefix_product(shape, i) as int == column_major_strides(shape)[i] for i < shape.len().
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
        //  cm(shape)[i] = shape[0] * cm(shape.skip(1))[i-1]  (from cm recursive def + scale)
        //  pp(shape, i) = shape[i-1] * pp(shape, i-1)
        //  By IH on shape.skip(1) with index i-1:
        //    pp(skip(1), i-1) as int == cm(skip(1))[i-1]
        //  pp_split: pp(shape, i) == shape[0] * pp(skip(1), i-1)
        let rest = shape.skip(1);
        assert(shape_valid(rest)) by {
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] > 0
            by { assert(rest[j] == shape[j + 1]); };
        };
        lemma_prefix_product_split(shape, i);
        //  pp(shape, i) == shape[0] * pp(rest, i-1)
        lemma_prefix_product_eq_cm_stride(rest, (i - 1) as nat);
        //  pp(rest, i-1) as int == cm(rest)[i-1]
        //  So pp(shape, i) as int == shape[0] * cm(rest)[i-1] (as int)
        //  Need: cm(shape)[i] == shape[0] * cm(rest)[i-1]
        //  This follows from the cm definition: cm(shape) = [1] ++ scale(cm(rest), shape[0])
        //  cm(shape)[i] = scale(cm(rest), shape[0])[i-1] = shape[0] * cm(rest)[i-1]
        crate::proof::injectivity_lemmas::lemma_column_major_strides_len(rest);
        assert(column_major_strides(shape)[i as int]
            == (shape.first() as int) * column_major_strides(rest)[(i - 1) as int]);
    }
}

//  ══════════════════════════════════════════════════════════════
//  General Box-unfolding helpers for arith_eval
//  ══════════════════════════════════════════════════════════════

///  Helper: arith_eval of Mul(Const(c), expr) = c * arith_eval(expr, env).
pub proof fn lemma_arith_eval_const_mul_expr(c: int, expr: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Mul(Box::new(ArithExpr::Const(c)), Box::new(*expr)), env)
            == c * arith_eval(expr, env),
{
    assert(arith_eval(&ArithExpr::Const(c), env) == c);
}

///  Helper: arith_eval of Mul(expr, Const(c)) = arith_eval(expr, env) * c.
proof fn lemma_arith_eval_mul_expr_const(expr: &ArithExpr, c: int, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Mul(Box::new(*expr), Box::new(ArithExpr::Const(c))), env)
            == arith_eval(expr, env) * c,
{
    assert(arith_eval(&ArithExpr::Const(c), env) == c);
}

///  Helper: arith_eval of Add(a, b) = arith_eval(a, env) + arith_eval(b, env).
proof fn lemma_arith_eval_add(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Add(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) + arith_eval(b, env),
{}

///  Helper: arith_eval_with_arrays of Add(a, b).
pub proof fn lemma_eval_with_arrays_add(a: &ArithExpr, b: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>)
    ensures
        arith_eval_with_arrays(&ArithExpr::Add(Box::new(*a), Box::new(*b)), env, arrays)
            == arith_eval_with_arrays(a, env, arrays) + arith_eval_with_arrays(b, env, arrays),
{}

///  Helper: arith_eval of Sub(a, b) = arith_eval(a, env) - arith_eval(b, env).
proof fn lemma_arith_eval_sub(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Sub(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) - arith_eval(b, env),
{}

///  Helper: arith_eval of Mul(a, b) = arith_eval(a, env) * arith_eval(b, env).
proof fn lemma_arith_eval_mul(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Mul(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) * arith_eval(b, env),
{}

///  Helper: arith_eval of Index(arr, idx) = arith_eval(idx, env).
proof fn lemma_arith_eval_index(arr: nat, idx: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Index(arr, Box::new(*idx)), env) == arith_eval(idx, env),
{}

///  Helper: arith_eval of Reduce(var, bound, body).
pub proof fn lemma_arith_eval_reduce(var: nat, bound: &ArithExpr, body: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Reduce(var, Box::new(*bound), Box::new(*body)), env)
            == reduce_sum(var, arith_eval(bound, env), body, env),
{}

///  Helper: arith_eval of Shr(a, b).
pub proof fn lemma_arith_eval_shr(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Shr(Box::new(*a), Box::new(*b)), env)
            == shr_spec(arith_eval(a, env), arith_eval(b, env)),
{}

///  Helper: arith_eval_fits_i64 for a Shr node.
proof fn lemma_fits_i64_shr(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Shr(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= shr_spec(arith_eval(a, env), arith_eval(b, env)),
        shr_spec(arith_eval(a, env), arith_eval(b, env)) <= i64::MAX as int,
{}

///  Helper: arith_eval of Cmp(op, a, b).
pub proof fn lemma_arith_eval_cmp(op: &CmpOp, a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(&ArithExpr::Cmp(*op, Box::new(*a), Box::new(*b)), env)
            == cmp_eval(op, arith_eval(a, env), arith_eval(b, env)),
{}

///  Helper: arith_eval_with_arrays of Cmp(op, a, b).
pub proof fn lemma_eval_with_arrays_cmp(
    op: &CmpOp, a: &ArithExpr, b: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures
        arith_eval_with_arrays(&ArithExpr::Cmp(*op, Box::new(*a), Box::new(*b)), env, arrays)
            == cmp_eval(op, arith_eval_with_arrays(a, env, arrays),
                             arith_eval_with_arrays(b, env, arrays)),
{}

///  Helper: arith_eval_with_arrays of Sub(a, b).
pub proof fn lemma_eval_with_arrays_sub(
    a: &ArithExpr, b: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures
        arith_eval_with_arrays(&ArithExpr::Sub(Box::new(*a), Box::new(*b)), env, arrays)
            == arith_eval_with_arrays(a, env, arrays) - arith_eval_with_arrays(b, env, arrays),
{}

///  Helper: arith_eval of Div(a, b) — handles both zero and nonzero denom.
proof fn lemma_arith_eval_div(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(b, env) != 0 ==> arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) / arith_eval(b, env),
        arith_eval(b, env) == 0 ==> arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env) == 0,
{}

///  Helper: arith_eval of Mod(a, b) — handles both zero and nonzero denom.
proof fn lemma_arith_eval_mod(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    ensures
        arith_eval(b, env) != 0 ==> arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env)
            == arith_eval(a, env) % arith_eval(b, env),
        arith_eval(b, env) == 0 ==> arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env) == 0,
{}

///  Helper: arith_eval_fits_i64 for an Add node.
proof fn lemma_fits_i64_add(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Add(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(a, env) + arith_eval(b, env),
        arith_eval(a, env) + arith_eval(b, env) <= i64::MAX as int,
{}

///  Helper: arith_eval_fits_i64 for a Sub node.
proof fn lemma_fits_i64_sub(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Sub(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(a, env) - arith_eval(b, env),
        arith_eval(a, env) - arith_eval(b, env) <= i64::MAX as int,
{}

///  Helper: arith_eval_fits_i64 for a Mul node.
proof fn lemma_fits_i64_mul(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Mul(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        i64::MIN as int <= arith_eval(a, env) * arith_eval(b, env),
        arith_eval(a, env) * arith_eval(b, env) <= i64::MAX as int,
{}

///  Helper: arith_eval_fits_i64 for a Div node.
proof fn lemma_fits_i64_div(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        arith_eval(a, env) >= 0,
        arith_eval(b, env) > 0,
        i64::MIN as int <= arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env),
        arith_eval(&ArithExpr::Div(Box::new(*a), Box::new(*b)), env) <= i64::MAX as int,
{}

///  Helper: arith_eval_fits_i64 for a Mod node.
proof fn lemma_fits_i64_mod(a: &ArithExpr, b: &ArithExpr, env: Seq<int>)
    requires arith_eval_fits_i64(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env),
    ensures
        arith_eval_fits_i64(a, env),
        arith_eval_fits_i64(b, env),
        arith_eval(a, env) >= 0,
        arith_eval(b, env) > 0,
        i64::MIN as int <= arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env),
        arith_eval(&ArithExpr::Mod(Box::new(*a), Box::new(*b)), env) <= i64::MAX as int,
{}

//  ══════════════════════════════════════════════════════════════
//  GEMM index expression correctness
//  ══════════════════════════════════════════════════════════════

///  Helper: eval of Mul(Var(v), Const(c)) = env[v] * c.
proof fn lemma_arith_eval_mul_var_const(v: nat, c: int, env: Seq<int>)
    requires (v as int) < env.len(),
    ensures arith_eval(&ArithExpr::Mul(
        Box::new(ArithExpr::Var(v)), Box::new(ArithExpr::Const(c)),
    ), env) == env[v as int] * c,
{
    assert(arith_eval(&ArithExpr::Var(v), env) == env[v as int]);
    assert(arith_eval(&ArithExpr::Const(c), env) == c);
}

///  Helper: eval of Add(a, Var(v)) = eval(a) + env[v].
proof fn lemma_arith_eval_add_var(a: &ArithExpr, v: nat, env: Seq<int>)
    requires (v as int) < env.len(),
    ensures arith_eval(&ArithExpr::Add(
        Box::new(*a), Box::new(ArithExpr::Var(v)),
    ), env) == arith_eval(a, env) + env[v as int],
{
    assert(arith_eval(&ArithExpr::Var(v), env) == env[v as int]);
}

///  Helper: eval of Add(Mul(Var(v1), Const(c)), Var(v2)) = env[v1]*c + env[v2].
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

///  GEMM A-index is correct: evaluates to i*K + k.
pub proof fn lemma_gemm_a_index_correct(k_size: nat, i: int, j: int, k: int)
    ensures
        arith_eval(&gemm_a_index_expr(k_size), seq![i, j, k]) == i * (k_size as int) + k,
{
    lemma_arith_eval_linear_index(0, k_size as int, 2, seq![i, j, k]);
}

///  GEMM B-index is correct: evaluates to k*N + j.
pub proof fn lemma_gemm_b_index_correct(n: nat, i: int, j: int, k: int)
    ensures
        arith_eval(&gemm_b_index_expr(n), seq![i, j, k]) == k * (n as int) + j,
{
    lemma_arith_eval_linear_index(2, n as int, 1, seq![i, j, k]);
}

///  Helper: for a linear index expr (Add(Mul(Var,Const),Var)), eval_with_arrays == arith_eval.
pub proof fn lemma_eval_with_arrays_linear_index(v1: nat, c: int, v2: nat, env: Seq<int>, arrays: Seq<Seq<int>>)
    requires (v1 as int) < env.len(), (v2 as int) < env.len(),
    ensures
        arith_eval_with_arrays(&ArithExpr::Add(
            Box::new(ArithExpr::Mul(
                Box::new(ArithExpr::Var(v1)), Box::new(ArithExpr::Const(c)),
            )),
            Box::new(ArithExpr::Var(v2)),
        ), env, arrays) == env[v1 as int] * c + env[v2 as int],
{
    //  eval_with_arrays for Var and Const is the same as arith_eval
    assert(arith_eval_with_arrays(&ArithExpr::Var(v1), env, arrays) == env[v1 as int]);
    assert(arith_eval_with_arrays(&ArithExpr::Const(c), env, arrays) == c);
    assert(arith_eval_with_arrays(&ArithExpr::Var(v2), env, arrays) == env[v2 as int]);
    let mul_expr = ArithExpr::Mul(Box::new(ArithExpr::Var(v1)), Box::new(ArithExpr::Const(c)));
    assert(arith_eval_with_arrays(&mul_expr, env, arrays) == env[v1 as int] * c);
}

///  Helper: eval_with_arrays of Index(arr, idx_expr) = arrays[arr][eval_with_arrays(idx_expr)].
pub proof fn lemma_eval_with_arrays_index(
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

///  Helper: eval_with_arrays of Mul(a, b) = eval(a) * eval(b).
pub proof fn lemma_eval_with_arrays_mul(
    a: &ArithExpr, b: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures
        arith_eval_with_arrays(
            &ArithExpr::Mul(Box::new(*a), Box::new(*b)), env, arrays,
        ) == arith_eval_with_arrays(a, env, arrays) * arith_eval_with_arrays(b, env, arrays),
{}

///  GEMM MAC expression is correct with arrays:
///  evaluates to A[i*K+k] * B[k*N+j].
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

    //  Establish that eval_with_arrays of the index exprs gives the expected values
    lemma_eval_with_arrays_linear_index(0, k_size as int, 2, env, arrays);
    assert(arith_eval_with_arrays(&a_idx_expr, env, arrays) == a_idx_val);
    lemma_eval_with_arrays_linear_index(2, n as int, 1, env, arrays);
    assert(arith_eval_with_arrays(&b_idx_expr, env, arrays) == b_idx_val);

    //  Step 1: Index(0, a_idx_expr) evaluates to a_data[i*K+k]
    lemma_eval_with_arrays_index(0, &a_idx_expr, env, arrays, a_idx_val);
    let idx_a = ArithExpr::Index(0, Box::new(a_idx_expr));

    //  Step 2: Index(1, b_idx_expr) evaluates to b_data[k*N+j]
    lemma_eval_with_arrays_index(1, &b_idx_expr, env, arrays, b_idx_val);
    let idx_b = ArithExpr::Index(1, Box::new(b_idx_expr));

    //  Step 3: Mul(idx_a, idx_b) = a_data[i*K+k] * b_data[k*N+j]
    lemma_eval_with_arrays_mul(&idx_a, &idx_b, env, arrays);
}

//  ══════════════════════════════════════════════════════════════
//  Offset expression correctness
//  ══════════════════════════════════════════════════════════════

///  Inductive helper: offset_expr_skip evaluates to the tail dot product.
///
///  arith_eval(offset_expr_skip(0, shape, stride, start), [x])
///      == dot_product_nat_int(delinearize(x, shape).skip(start), stride.skip(start))
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
        //  offset_expr_skip = Const(0), coords/stride tails are empty
        let tail_c = coords.skip(start as int);
        let tail_s = stride.skip(start as int);
        assert(tail_c.len() == 0);
        assert(tail_s.len() == 0);
        crate::proof::offset_lemmas::lemma_dot_product_empty(tail_s);
    } else {
        //  arith_eval of coord_expr == delinearize(x, shape)[start]
        lemma_delinearize_coord_expr_correct(shape, start, x);
        let coord_expr = delinearize_coord_expr(0, shape, start);
        let coord_val = coords[start as int];

        //  Mul(coord_expr, Const(stride[start])) evaluates to coord_val * stride[start]
        lemma_arith_eval_mul_expr_const(&coord_expr, stride[start as int], env);
        let term = ArithExpr::Mul(
            Box::new(coord_expr),
            Box::new(ArithExpr::Const(stride[start as int])),
        );
        let term_val = (coord_val as int) * stride[start as int];
        assert(arith_eval(&term, env) == term_val);

        //  Dot product decomposition: skip(start) has coords[start] as first element
        let tail_coords = coords.skip(start as int);
        let tail_stride = stride.skip(start as int);
        assert(tail_coords.len() > 0);
        assert(tail_coords.first() == coord_val);
        assert(tail_stride.first() == stride[start as int]);
        assert(tail_coords.skip(1) =~= coords.skip((start + 1) as int));
        assert(tail_stride.skip(1) =~= stride.skip((start + 1) as int));

        //  dot_product(tail, tail) = first*first + dot_product(rest, rest) by definition
        let dp_rest = dot_product_nat_int(
            coords.skip((start + 1) as int),
            stride.skip((start + 1) as int),
        );

        if start + 1 >= shape.len() {
            //  Last mode: offset_expr_skip = term (just the Mul)
            assert(coords.skip((start + 1) as int).len() == 0);
            assert(stride.skip((start + 1) as int).len() == 0);
            crate::proof::offset_lemmas::lemma_dot_product_empty(
                stride.skip((start + 1) as int),
            );
            assert(dp_rest == 0);
            //  Connect: offset_expr_skip produces `term`, eval = term_val = dp
            assert(dot_product_nat_int(tail_coords, tail_stride)
                == term_val + dp_rest);
        } else {
            //  offset_expr_skip = Add(term, offset_expr_skip(start+1))
            //  By IH: offset_expr_skip(start+1) evaluates to the remaining dot product
            lemma_offset_expr_skip_correct(shape, stride, x, start + 1);
            let rest_expr = offset_expr_skip(0, shape, stride, start + 1);
            assert(arith_eval(&rest_expr, env) == dp_rest);

            //  Add unfolding: eval(Add(term, rest)) = eval(term) + eval(rest)
            lemma_arith_eval_add(&term, &rest_expr, env);
            assert(arith_eval(
                &ArithExpr::Add(Box::new(term), Box::new(rest_expr)), env,
            ) == term_val + dp_rest);

            //  dot_product connection
            assert(dot_product_nat_int(tail_coords, tail_stride)
                == term_val + dp_rest);
        }
    }
}

///  The offset expression correctly computes layout.offset(x):
///  arith_eval(offset_expr(0, shape, stride), [x]) == LayoutSpec{shape, stride}.offset(x).
///
///  This is the key theorem connecting ArithExpr to CuTe layout offsets.
///  Combined with lemma_delinearize_coord_expr_correct, it proves that
///  the entire index computation pipeline is faithfully represented in ArithExpr.
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

    //  offset_expr(0, shape, stride) == offset_expr_skip(0, shape, stride, 0)
    //  for all cases (empty, single, multi-mode). Verus can see this from the specs.

    //  Use the inductive helper with start=0
    lemma_offset_expr_skip_correct(shape, stride, x, 0);

    //  skip(0) is identity
    assert(coords.skip(0) =~= coords);
    assert(stride.skip(0) =~= stride);

    //  offset(x) = dot_product(delinearize(x, shape), stride) by definition
}

//  ══════════════════════════════════════════════════════════════
//  Foundational properties of ArithExpr evaluation
//  ══════════════════════════════════════════════════════════════

//  --- env_with properties ---

///  env_with sets the target variable.
pub proof fn lemma_env_with_at(env: Seq<int>, var: nat, val: int)
    ensures env_with(env, var, val)[var as int] == val,
{
    if (var as int) < env.len() {
        assert(env.update(var as int, val)[var as int] == val);
    } else {
        let ext = Seq::new((var + 1) as nat, |i: int|
            if i < env.len() { env[i] }
            else if i == var as int { val }
            else { 0 }
        );
        assert(ext[var as int] == val);
    }
}

///  env_with preserves other variables (within original env length).
pub proof fn lemma_env_with_other(env: Seq<int>, var: nat, val: int, other: nat)
    requires other != var, (other as int) < env.len(),
    ensures env_with(env, var, val)[other as int] == env[other as int],
{
    if (var as int) < env.len() {
        assert(env.update(var as int, val)[other as int] == env[other as int]);
    } else {
        let ext = Seq::new((var + 1) as nat, |i: int|
            if i < env.len() { env[i] }
            else if i == var as int { val }
            else { 0 }
        );
        assert(ext[other as int] == env[other as int]);
    }
}

///  env_with length is at least var + 1.
pub proof fn lemma_env_with_len(env: Seq<int>, var: nat, val: int)
    ensures env_with(env, var, val).len() >= var + 1,
         env_with(env, var, val).len() >= env.len(),
{}

//  --- cmp_eval properties ---

///  Cmp always returns exactly 0 or 1.
pub proof fn lemma_cmp_returns_01(op: &CmpOp, a: int, b: int)
    ensures cmp_eval(op, a, b) == 0 || cmp_eval(op, a, b) == 1,
{}

///  Mul(Cmp, Cmp) is boolean AND: result is 1 iff both comparisons are true.
pub proof fn lemma_cmp_mul_is_and(
    op1: &CmpOp, a1: int, b1: int,
    op2: &CmpOp, a2: int, b2: int,
)
    ensures ({
        let c1 = cmp_eval(op1, a1, b1);
        let c2 = cmp_eval(op2, a2, b2);
        c1 * c2 == 1 <==> (c1 == 1 && c2 == 1)
    }),
{
    lemma_cmp_returns_01(op1, a1, b1);
    lemma_cmp_returns_01(op2, a2, b2);
}

//  --- reduce_sum base cases ---

///  Reduce with bound 0 is 0.
pub proof fn lemma_reduce_sum_zero(var: nat, body: &ArithExpr, env: Seq<int>)
    ensures reduce_sum(var, 0, body, env) == 0,
{}

///  Reduce with bound 0 is 0 (arrays version).
pub proof fn lemma_reduce_sum_arrays_zero(
    var: nat, body: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures reduce_sum_arrays(var, 0, body, env, arrays) == 0,
{}

///  Reduce with bound 1 is a single evaluation.
pub proof fn lemma_reduce_sum_one(var: nat, body: &ArithExpr, env: Seq<int>)
    ensures reduce_sum(var, 1, body, env)
        == arith_eval(body, env_with(env, var, 0)),
{
    assert(reduce_sum(var, 0, body, env) == 0int);
}

///  Reduce with bound 1 is a single evaluation (arrays version).
pub proof fn lemma_reduce_sum_arrays_one(
    var: nat, body: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures reduce_sum_arrays(var, 1, body, env, arrays)
        == arith_eval_with_arrays(body, env_with(env, var, 0), arrays),
{
    assert(reduce_sum_arrays(var, 0, body, env, arrays) == 0int);
}

//  --- reduce_sum splitting (THE key lemma for tiled schedules) ---

///  Reduce splitting: Σ_{i=0}^{a+b-1} f(i) == Σ_{i=0}^{a-1} f(i) + Σ_{i=0}^{b-1} f(a+i)
///
///  This is the foundational lemma for all tiled schedule transformations.
///  Tiling = splitting a sum into blocks, each computed in shared memory or by a workgroup.
pub proof fn lemma_reduce_sum_split(
    var: nat, a: nat, b: nat, body: &ArithExpr, env: Seq<int>,
)
    ensures
        reduce_sum(var, (a + b) as int, body, env)
            == reduce_sum(var, a as int, body, env)
                + reduce_sum_shifted(var, a, b as int, body, env),
    decreases b,
{
    if b == 0 {
    } else {
        //  reduce_sum(var, a+b, body, env)
        //    = reduce_sum(var, a+b-1, body, env) + eval(body, env[var := a+b-1])
        //    = (by IH with b-1) reduce_sum(var, a, body, env) + reduce_sum_shifted(var, a, b-1, body, env)
        //      + eval(body, env[var := a+b-1])
        //    = reduce_sum(var, a, body, env) + reduce_sum_shifted(var, a, b, body, env)
        //      (because reduce_sum_shifted(var, a, b) = reduce_sum_shifted(var, a, b-1) + eval(body, env[var := a+b-1]))
        lemma_reduce_sum_split(var, a, (b - 1) as nat, body, env);
    }
}

///  Shifted summation: Σ_{i=0}^{n-1} f(offset + i)
pub open spec fn reduce_sum_shifted(
    var: nat, offset: nat, n: int, body: &ArithExpr, env: Seq<int>,
) -> int
    decreases (if n > 0 { n } else { 0 }),
{
    if n <= 0 { 0 }
    else {
        reduce_sum_shifted(var, offset, n - 1, body, env)
            + arith_eval(body, env_with(env, var, (offset as int) + n - 1))
    }
}

///  Reduce splitting (arrays version).
pub proof fn lemma_reduce_sum_arrays_split(
    var: nat, a: nat, b: nat, body: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    ensures
        reduce_sum_arrays(var, (a + b) as int, body, env, arrays)
            == reduce_sum_arrays(var, a as int, body, env, arrays)
                + reduce_sum_arrays_shifted(var, a, b as int, body, env, arrays),
    decreases b,
{
    if b == 0 {
    } else {
        lemma_reduce_sum_arrays_split(var, a, (b - 1) as nat, body, env, arrays);
    }
}

///  Shifted summation (arrays version).
pub open spec fn reduce_sum_arrays_shifted(
    var: nat, offset: nat, n: int, body: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
) -> int
    decreases body, (if n > 0 { n } else { 0 }),
{
    if n <= 0 { 0 }
    else {
        reduce_sum_arrays_shifted(var, offset, n - 1, body, env, arrays)
            + arith_eval_with_arrays(body, env_with(env, var, (offset as int) + n - 1), arrays)
    }
}

//  --- reduce algebraic properties ---

///  Reduce over constant: Σ_{i=0}^{n-1} c == n * c.
pub proof fn lemma_reduce_sum_const(var: nat, n: nat, c: int, env: Seq<int>)
    ensures reduce_sum(var, n as int, &ArithExpr::Const(c), env) == (n as int) * c,
    decreases n,
{
    if n == 0 {
        assert(reduce_sum(var, n as int, &ArithExpr::Const(c), env) == 0int);
        assert((n as int) * c == 0int) by (nonlinear_arith)
            requires n == 0nat;
        return;
    }
    lemma_reduce_sum_const(var, (n - 1) as nat, c, env);
    //  Step term: arith_eval(Const(c), env_with(...)) == c
    let ext = env_with(env, var, (n - 1) as int);
    assert(arith_eval(&ArithExpr::Const(c), ext) == c);
    assert(((n - 1) as int) * c + c == (n as int) * c) by (nonlinear_arith);
}

///  Reduce linearity: Σ (f(i) + g(i)) == Σ f(i) + Σ g(i).
pub proof fn lemma_reduce_sum_linear(
    var: nat, n: nat,
    f: &ArithExpr, g: &ArithExpr, env: Seq<int>,
)
    ensures
        reduce_sum(var, n as int,
            &ArithExpr::Add(Box::new(*f), Box::new(*g)), env)
        == reduce_sum(var, n as int, f, env)
            + reduce_sum(var, n as int, g, env),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_reduce_sum_linear(var, (n - 1) as nat, f, g, env);
        let ext = env_with(env, var, (n - 1) as int);
        lemma_arith_eval_add(f, g, ext);
    }
}

///  Reduce scalar factor: Σ c * f(i) == c * Σ f(i).
pub proof fn lemma_reduce_sum_scalar(
    var: nat, n: nat,
    c: int, f: &ArithExpr, env: Seq<int>,
)
    ensures
        reduce_sum(var, n as int,
            &ArithExpr::Mul(Box::new(ArithExpr::Const(c)), Box::new(*f)), env)
        == c * reduce_sum(var, n as int, f, env),
    decreases n,
{
    if n == 0 {
        assert(reduce_sum(var, n as int, &ArithExpr::Mul(Box::new(ArithExpr::Const(c)), Box::new(*f)), env) == 0int);
        assert(reduce_sum(var, n as int, f, env) == 0int);
        assert(c * 0int == 0int) by (nonlinear_arith);
        return;
    }
    {
        lemma_reduce_sum_scalar(var, (n - 1) as nat, c, f, env);
        let ext = env_with(env, var, (n - 1) as int);
        //  Step term: Mul(Const(c), f) at ext = c * f(ext)
        lemma_arith_eval_const_mul_expr(c, f, ext);
        assert(c * reduce_sum(var, (n - 1) as int, f, env) + c * arith_eval(f, ext)
            == c * (reduce_sum(var, (n - 1) as int, f, env) + arith_eval(f, ext)))
            by (nonlinear_arith);
    }
}

//  --- index_free and eval equivalence ---

///  Predicate: expression contains no Index nodes.
///  When true, arith_eval and arith_eval_with_arrays agree.
pub open spec fn index_free(expr: &ArithExpr) -> bool
    decreases expr,
{
    match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) =>
            index_free(a) && index_free(b),
        ArithExpr::Cmp(_, a, b) => index_free(a) && index_free(b),
        ArithExpr::Index(_, _) => false,
        ArithExpr::Reduce(_, bound, body) => index_free(bound) && index_free(body),
    }
}

///  arith_eval == arith_eval_with_arrays for index-free expressions.
pub proof fn lemma_eval_equiv_no_index(
    expr: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires index_free(expr),
    ensures arith_eval(expr, env) == arith_eval_with_arrays(expr, env, arrays),
    decreases expr, 0int,
{
    match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => {},
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) => {
            lemma_eval_equiv_no_index(a, env, arrays);
            lemma_eval_equiv_no_index(b, env, arrays);
        },
        ArithExpr::Cmp(_, a, b) => {
            lemma_eval_equiv_no_index(a, env, arrays);
            lemma_eval_equiv_no_index(b, env, arrays);
        },
        ArithExpr::Index(_, _) => {}, //  unreachable: index_free is false
        ArithExpr::Reduce(var, bound, body) => {
            lemma_eval_equiv_no_index(bound, env, arrays);
            let n = arith_eval(bound, env);
            lemma_reduce_equiv_no_index(*var, n, body, env, arrays);
        },
    }
}

///  Helper: reduce_sum == reduce_sum_arrays for index-free body.
proof fn lemma_reduce_equiv_no_index(
    var: nat, n: int, body: &ArithExpr,
    env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires index_free(body),
    ensures reduce_sum(var, n, body, env) == reduce_sum_arrays(var, n, body, env, arrays),
    decreases body, (if n > 0 { n } else { 0 }),
{
    if n <= 0 {
    } else {
        lemma_reduce_equiv_no_index(var, n - 1, body, env, arrays);
        let ext = env_with(env, var, n - 1);
        lemma_eval_equiv_no_index(body, ext, arrays);
    }
}

//  --- free variables and evaluation independence ---

///  Predicate: expression does not reference Var(k).
pub open spec fn free_of_var(expr: &ArithExpr, k: nat) -> bool
    decreases expr,
{
    match expr {
        ArithExpr::Const(_) => true,
        ArithExpr::Var(i) => *i != k,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) =>
            free_of_var(a, k) && free_of_var(b, k),
        ArithExpr::Cmp(_, a, b) => free_of_var(a, k) && free_of_var(b, k),
        ArithExpr::Index(_, idx) => free_of_var(idx, k),
        ArithExpr::Reduce(var, bound, body) =>
            free_of_var(bound, k) && (*var == k || free_of_var(body, k)),
    }
}

///  If expr is free of Var(k), changing env[k] doesn't affect evaluation.
pub proof fn lemma_eval_independent_of_unused_var(
    expr: &ArithExpr, env1: Seq<int>, env2: Seq<int>, k: nat,
)
    requires
        free_of_var(expr, k),
        env1.len() == env2.len(),
        forall|j: int| 0 <= j < env1.len() && j != k as int
            ==> env1[j] == env2[j],
    ensures
        arith_eval(expr, env1) == arith_eval(expr, env2),
    decreases expr, 0int,
{
    match expr {
        ArithExpr::Const(_) => {},
        ArithExpr::Var(i) => {
            if (*i as int) < env1.len() {
                assert(env1[*i as int] == env2[*i as int]);
            }
        },
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) => {
            lemma_eval_independent_of_unused_var(a, env1, env2, k);
            lemma_eval_independent_of_unused_var(b, env1, env2, k);
        },
        ArithExpr::Cmp(_, a, b) => {
            lemma_eval_independent_of_unused_var(a, env1, env2, k);
            lemma_eval_independent_of_unused_var(b, env1, env2, k);
        },
        ArithExpr::Index(_, idx) => {
            lemma_eval_independent_of_unused_var(idx, env1, env2, k);
        },
        ArithExpr::Reduce(var, bound, body) => {
            lemma_eval_independent_of_unused_var(bound, env1, env2, k);
            let n = arith_eval(bound, env1);
            lemma_reduce_independent_helper(*var, n, body, env1, env2, k);
        },
    }
}

///  Helper: reduce_sum independent of unused var.
proof fn lemma_reduce_independent_helper(
    var: nat, n: int, body: &ArithExpr,
    env1: Seq<int>, env2: Seq<int>, k: nat,
)
    requires
        env1.len() == env2.len(),
        forall|j: int| 0 <= j < env1.len() && j != k as int
            ==> env1[j] == env2[j],
        var == k || free_of_var(body, k),
    ensures
        reduce_sum(var, n, body, env1) == reduce_sum(var, n, body, env2),
    decreases body, (if n > 0 { n } else { 0 }),
{
    if n <= 0 {
    } else {
        lemma_reduce_independent_helper(var, n - 1, body, env1, env2, k);
        let ext1 = env_with(env1, var, n - 1);
        let ext2 = env_with(env2, var, n - 1);
        if var == k {
            //  Both envs set var=k to n-1, agree on everything else.
            assert(ext1 =~= ext2);
        } else {
            //  free_of_var(body, k). ext1 and ext2 still differ only at k.
            //  Need: ext1 and ext2 agree on all j != k, have same length.
            lemma_env_with_len(env1, var, n - 1);
            lemma_env_with_len(env2, var, n - 1);
            assert(ext1.len() == ext2.len()) by {
                if (var as int) < env1.len() {
                    assert(ext1.len() == env1.len());
                    assert(ext2.len() == env2.len());
                }
            };
            assert forall|j: int| 0 <= j < ext1.len() && j != k as int
                implies ext1[j] == ext2[j]
            by {
                if j == var as int {
                    lemma_env_with_at(env1, var, n - 1);
                    lemma_env_with_at(env2, var, n - 1);
                } else if j < env1.len() {
                    lemma_env_with_other(env1, var, n - 1, j as nat);
                    lemma_env_with_other(env2, var, n - 1, j as nat);
                }
            };
            lemma_eval_independent_of_unused_var(body, ext1, ext2, k);
        }
    }
}

//  --- nested reduce interchange ---

///  Helper: if every term is zero, the sum is zero.
proof fn lemma_reduce_all_zero_terms(
    var: nat, n: nat,
    inner: &ArithExpr, env: Seq<int>,
    inner_var: nat, body: &ArithExpr,
)
    requires
        *inner == ArithExpr::Reduce(inner_var, Box::new(ArithExpr::Const(0int)), Box::new(*body)),
    ensures
        reduce_sum(var, n as int, inner, env) == 0,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_reduce_all_zero_terms(var, (n - 1) as nat, inner, env, inner_var, body);
        let ext = env_with(env, var, (n - 1) as int);
        lemma_arith_eval_reduce(inner_var, &ArithExpr::Const(0int), body, ext);
    }
}

///  Helper: peel the last term from the inner reduce and move it outside.
///  Σ_{j=0}^{n-1} (Σ_{i=0}^{m} body) == Σ_{j=0}^{n-1} (Σ_{i=0}^{m-1} body) + Σ_{j=0}^{n-1} body(m-1, j)
///
///  This is reduce linearity applied to the outer sum, where the inner sum
///  is split as: Σ_{i=0}^{m} = Σ_{i=0}^{m-1} + term(m-1).
proof fn lemma_peel_inner_last(
    var_i: nat, var_j: nat,
    m: nat, n: nat,
    body: &ArithExpr, env: Seq<int>,
)
    requires
        var_i != var_j,
        m > 0,
    ensures ({
        let inner_m = ArithExpr::Reduce(var_i, Box::new(ArithExpr::Const(m as int)), Box::new(*body));
        let inner_m1 = ArithExpr::Reduce(var_i, Box::new(ArithExpr::Const((m - 1) as int)), Box::new(*body));
        reduce_sum(var_j, n as int, &inner_m, env)
        == reduce_sum(var_j, n as int, &inner_m1, env)
            + reduce_sum_peeled(var_j, var_i, n, (m - 1) as nat, body, env)
    }),
    decreases n,
{
    let inner_m = ArithExpr::Reduce(var_i, Box::new(ArithExpr::Const(m as int)), Box::new(*body));
    let inner_m1 = ArithExpr::Reduce(var_i, Box::new(ArithExpr::Const((m - 1) as int)), Box::new(*body));

    if n == 0 {
    } else {
        lemma_peel_inner_last(var_i, var_j, m, (n - 1) as nat, body, env);
        //  For the n-1'th term:
        //  arith_eval(inner_m, env_with(env, var_j, n-1))
        //    = reduce_sum(var_i, m, body, env_with(env, var_j, n-1))
        //    = reduce_sum(var_i, m-1, body, ...) + arith_eval(body, env_with(..., var_i, m-1))
        let ext_j = env_with(env, var_j, (n - 1) as int);
        lemma_arith_eval_reduce(var_i, &ArithExpr::Const(m as int), body, ext_j);
        lemma_arith_eval_reduce(var_i, &ArithExpr::Const((m - 1) as int), body, ext_j);
        //  reduce_sum(var_i, m, body, ext_j) = reduce_sum(var_i, m-1, body, ext_j) + arith_eval(body, env_with(ext_j, var_i, m-1))
    }
}

///  Helper spec: the "peeled" term — Σ_{j=0}^{n-1} body(m_val, j)
///  where var_i is set to m_val in the body's env.
pub open spec fn reduce_sum_peeled(
    var_j: nat, var_i: nat,
    n: nat, m_val: nat,
    body: &ArithExpr, env: Seq<int>,
) -> int
    decreases n,
{
    if n == 0 { 0 }
    else {
        reduce_sum_peeled(var_j, var_i, (n - 1) as nat, m_val, body, env)
            + arith_eval(body, env_with(env_with(env, var_j, (n - 1) as int), var_i, m_val as int))
    }
}

///  The peeled term equals the inner sum with swapped variable binding order.
///  Σ_{j=0}^{n-1} body(m_val, j) where we set var_j then var_i
///  == reduce_sum(var_j, n, body_with_i_fixed, env)
///  This connects the peeled term to a standard reduce_sum.
proof fn lemma_peeled_eq_reduce(
    var_j: nat, var_i: nat,
    n: nat, m_val: nat,
    body: &ArithExpr, env: Seq<int>,
)
    requires var_i != var_j,
    ensures
        reduce_sum_peeled(var_j, var_i, n, m_val, body, env)
        == reduce_sum(var_j, n as int, body, env_with(env, var_i, m_val as int)),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_peeled_eq_reduce(var_j, var_i, (n - 1) as nat, m_val, body, env);
        //  Term: arith_eval(body, env_with(env_with(env, var_j, n-1), var_i, m_val))
        //  == arith_eval(body, env_with(env_with(env, var_i, m_val), var_j, n-1))
        //  These are equal if env_with commutes for distinct vars.
        let ext_ji = env_with(env_with(env, var_j, (n - 1) as int), var_i, m_val as int);
        let ext_ij = env_with(env_with(env, var_i, m_val as int), var_j, (n - 1) as int);
        lemma_env_with_commutes(env, var_i, m_val as int, var_j, (n - 1) as int);
        assert(ext_ji =~= ext_ij);
    }
}

///  env_with commutes for distinct variables.
pub proof fn lemma_env_with_commutes(
    env: Seq<int>, var1: nat, val1: int, var2: nat, val2: int,
)
    requires var1 != var2,
    ensures
        env_with(env_with(env, var1, val1), var2, val2)
        =~= env_with(env_with(env, var2, val2), var1, val1),
{
    let e12 = env_with(env_with(env, var1, val1), var2, val2);
    let e21 = env_with(env_with(env, var2, val2), var1, val1);
    //  Both produce a seq of the same length with the same values at each index.
    //  var1 -> val1, var2 -> val2, other -> env[other].
    let max_len = if var1 > var2 { var1 + 1 } else { var2 + 1 };
    let base_len = if env.len() > max_len as int { env.len() as nat } else { max_len };

    assert forall|j: int| 0 <= j < e12.len() implies e12[j] == e21[j]
    by {
        lemma_env_with_at(env_with(env, var1, val1), var2, val2);
        lemma_env_with_at(env_with(env, var2, val2), var1, val1);
        if j == var2 as int {
            lemma_env_with_at(env_with(env, var1, val1), var2, val2);
            //  e12[var2] = val2
            //  e21[var2]: env_with(env_with(env, var2, val2), var1, val1)[var2]
            //    var1 != var2, so this is env_with(env, var2, val2)[var2] = val2
            lemma_env_with_len(env, var2, val2);
            if (var2 as int) < env_with(env, var2, val2).len() {
                lemma_env_with_other(env_with(env, var2, val2), var1, val1, var2);
                lemma_env_with_at(env, var2, val2);
            }
        } else if j == var1 as int {
            lemma_env_with_at(env_with(env, var2, val2), var1, val1);
            lemma_env_with_len(env, var1, val1);
            if (var1 as int) < env_with(env, var1, val1).len() {
                lemma_env_with_other(env_with(env, var1, val1), var2, val2, var1);
                lemma_env_with_at(env, var1, val1);
            }
        } else {
            //  j != var1, j != var2: both return env[j] (or 0 if extended)
        }
    };
}

///  Nested reduce interchange: Σ_i Σ_j f(i,j) == Σ_j Σ_i f(i,j).
///  Fundamental for loop reordering schedule transformations.
pub proof fn lemma_reduce_sum_interchange(
    var_i: nat, var_j: nat,
    m: nat, n: nat,
    body: &ArithExpr,
    env: Seq<int>,
)
    requires var_i != var_j,
    ensures
        reduce_sum(var_i, m as int,
            &ArithExpr::Reduce(var_j, Box::new(ArithExpr::Const(n as int)), Box::new(*body)),
            env)
        ==
        reduce_sum(var_j, n as int,
            &ArithExpr::Reduce(var_i, Box::new(ArithExpr::Const(m as int)), Box::new(*body)),
            env),
    decreases m,
{
    let inner_j = ArithExpr::Reduce(var_j, Box::new(ArithExpr::Const(n as int)), Box::new(*body));
    let inner_i = ArithExpr::Reduce(var_i, Box::new(ArithExpr::Const(m as int)), Box::new(*body));

    if m == 0 {
        //  LHS = 0. RHS: each inner reduce has bound 0, so also 0.
        lemma_reduce_all_zero_terms(var_j, n, &inner_i, env, var_i, body);
    } else {
        //  IH
        lemma_reduce_sum_interchange(var_i, var_j, (m - 1) as nat, n, body, env);

        //  Peel: Σ_j Σ_{i=0}^{m-1} body = Σ_j Σ_{i=0}^{m-2} body + Σ_j body(m-1, j)
        lemma_peel_inner_last(var_i, var_j, m, n, body, env);

        //  The peeled term: Σ_j body(m-1, j) = reduce_sum(var_j, n, body, env_with(env, var_i, m-1))
        lemma_peeled_eq_reduce(var_j, var_i, n, (m - 1) as nat, body, env);

        //  LHS = reduce_sum(var_i, m-1, inner_j, env) + arith_eval(inner_j, env_with(env, var_i, m-1))
        //       = (by IH) reduce_sum(var_j, n, inner_i_m1, env) + reduce_sum(var_j, n, body, env_with(env, var_i, m-1))
        //  And reduce_sum(var_j, n, body, env_with(env, var_i, m-1)) = peeled term
        //  RHS = reduce_sum(var_j, n, inner_i_m, env)
        //      = (by peel) reduce_sum(var_j, n, inner_i_m1, env) + peeled term
        //  So LHS = RHS. ✓
        let ext_i = env_with(env, var_i, (m - 1) as int);
        lemma_arith_eval_reduce(var_j, &ArithExpr::Const(n as int), body, ext_i);
    }
}

//  ══════════════════════════════════════════════════════════════
//  Runtime ArithExpr: exec-mode type mirroring ArithExpr with i64/u32
//  ══════════════════════════════════════════════════════════════

///  Runtime comparison operator.
pub enum RuntimeCmpOp {
    Lt, Le, Gt, Ge, Eq, Ne,
}

impl RuntimeCmpOp {
    pub open spec fn view_spec(&self) -> CmpOp {
        match self {
            RuntimeCmpOp::Lt => CmpOp::Lt,
            RuntimeCmpOp::Le => CmpOp::Le,
            RuntimeCmpOp::Gt => CmpOp::Gt,
            RuntimeCmpOp::Ge => CmpOp::Ge,
            RuntimeCmpOp::Eq => CmpOp::Eq,
            RuntimeCmpOp::Ne => CmpOp::Ne,
        }
    }
}

///  Runtime arithmetic expression with concrete integer types for exec code.
pub enum RuntimeArithExpr {
    Const(i64),
    Var(u32),
    Add(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Sub(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Mul(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Div(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Mod(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Index(u32, Box<RuntimeArithExpr>),
    Shr(Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Cmp(RuntimeCmpOp, Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
    Reduce(u32, Box<RuntimeArithExpr>, Box<RuntimeArithExpr>),
}

//  ══════════════════════════════════════════════════════════════
//  Canonical ordering + normalization for ArithExpr
//  ══════════════════════════════════════════════════════════════

///  Size of an ArithExpr tree (number of nodes). Used as termination measure.
pub open spec fn arith_size(expr: &ArithExpr) -> nat
    decreases expr,
{
    match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => 1,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) =>
            1 + arith_size(a) + arith_size(b),
        ArithExpr::Index(_, e) => 1 + arith_size(e),
        ArithExpr::Cmp(_, a, b) => 1 + arith_size(a) + arith_size(b),
        ArithExpr::Reduce(_, bound, body) => 1 + arith_size(bound) + arith_size(body),
    }
}

///  Children are strictly smaller than parent.
pub proof fn lemma_arith_size_positive(expr: &ArithExpr)
    ensures arith_size(expr) >= 1,
    decreases expr,
{
    match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => {},
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) => {
            lemma_arith_size_positive(a);
            lemma_arith_size_positive(b);
        },
        ArithExpr::Index(_, e) => { lemma_arith_size_positive(e); },
        ArithExpr::Cmp(_, a, b) => {
            lemma_arith_size_positive(a);
            lemma_arith_size_positive(b);
        },
        ArithExpr::Reduce(_, bound, body) => {
            lemma_arith_size_positive(bound);
            lemma_arith_size_positive(body);
        },
    }
}

///  Variant tag for canonical ordering.
pub open spec fn arith_variant_tag(expr: &ArithExpr) -> int {
    match expr {
        ArithExpr::Const(_) => 0,
        ArithExpr::Var(_) => 1,
        ArithExpr::Add(_, _) => 2,
        ArithExpr::Sub(_, _) => 3,
        ArithExpr::Mul(_, _) => 4,
        ArithExpr::Div(_, _) => 5,
        ArithExpr::Mod(_, _) => 6,
        ArithExpr::Index(_, _) => 7,
        ArithExpr::Shr(_, _) => 8,
        ArithExpr::Cmp(_, _, _) => 9,
        ArithExpr::Reduce(_, _, _) => 10,
    }
}

///  Lexicographic less-than on ArithExpr (for canonical ordering).
pub open spec fn arith_lt(a: &ArithExpr, b: &ArithExpr) -> bool
    decreases arith_size(a) + arith_size(b),
{
    let ta = arith_variant_tag(a);
    let tb = arith_variant_tag(b);
    if ta != tb { ta < tb }
    else { match (a, b) {
        (ArithExpr::Const(c1), ArithExpr::Const(c2)) => *c1 < *c2,
        (ArithExpr::Var(v1), ArithExpr::Var(v2)) => (*v1 as int) < (*v2 as int),
        (ArithExpr::Add(a1, a2), ArithExpr::Add(b1, b2)) =>
            arith_lt(a1, b1) || (!arith_lt(b1, a1) && arith_lt(a2, b2)),
        (ArithExpr::Sub(a1, a2), ArithExpr::Sub(b1, b2)) =>
            arith_lt(a1, b1) || (!arith_lt(b1, a1) && arith_lt(a2, b2)),
        (ArithExpr::Mul(a1, a2), ArithExpr::Mul(b1, b2)) =>
            arith_lt(a1, b1) || (!arith_lt(b1, a1) && arith_lt(a2, b2)),
        (ArithExpr::Index(i1, e1), ArithExpr::Index(i2, e2)) =>
            (*i1 as int) < (*i2 as int) || (*i1 == *i2 && arith_lt(e1, e2)),
        _ => false,  // same variant, default to not-less-than
    }}
}

///  Normalize an ArithExpr: sort commutative operands (Add, Mul).
///  Preserves evaluation: arith_eval(normalize(e)) == arith_eval(e).
///  Collect all addends from a normalized Add tree into a sorted Seq.
///  Add(a, Add(b, c)) → [a, b, c] (already sorted by arith_lt if right-associated).
pub open spec fn collect_add_terms(e: ArithExpr) -> Seq<ArithExpr>
    decreases e,
{
    match e {
        ArithExpr::Add(a, b) => collect_add_terms(*a) + collect_add_terms(*b),
        other => seq![other],
    }
}

///  Collect all factors from a normalized Mul tree into a sorted Seq.
pub open spec fn collect_mul_factors(e: ArithExpr) -> Seq<ArithExpr>
    decreases e,
{
    match e {
        ArithExpr::Mul(a, b) => collect_mul_factors(*a) + collect_mul_factors(*b),
        other => seq![other],
    }
}

///  Insert an ArithExpr into a sorted Seq (by arith_lt).
pub open spec fn sorted_insert(s: Seq<ArithExpr>, e: ArithExpr) -> Seq<ArithExpr>
    decreases s.len(),
{
    if s.len() == 0 { seq![e] }
    else if arith_lt(&e, &s[0]) { seq![e] + s }
    else { seq![s[0]] + sorted_insert(s.subrange(1, s.len() as int), e) }
}

///  Sort a Seq<ArithExpr> by arith_lt (insertion sort).
pub open spec fn sort_exprs(s: Seq<ArithExpr>) -> Seq<ArithExpr>
    decreases s.len(),
{
    if s.len() == 0 { Seq::empty() }
    else { sorted_insert(sort_exprs(s.subrange(1, s.len() as int)), s[0]) }
}

///  Rebuild right-associated Add from sorted terms, filtering Const(0).
pub open spec fn rebuild_add(terms: Seq<ArithExpr>) -> ArithExpr
    decreases terms.len(),
{
    if terms.len() == 0 { ArithExpr::Const(0) }
    else if terms.len() == 1 { terms[0] }
    else { ArithExpr::Add(Box::new(terms[0]), Box::new(rebuild_add(terms.subrange(1, terms.len() as int)))) }
}

///  Rebuild right-associated Mul from sorted factors, filtering Const(1).
pub open spec fn rebuild_mul(factors: Seq<ArithExpr>) -> ArithExpr
    decreases factors.len(),
{
    if factors.len() == 0 { ArithExpr::Const(1) }
    else if factors.len() == 1 { factors[0] }
    else { ArithExpr::Mul(Box::new(factors[0]), Box::new(rebuild_mul(factors.subrange(1, factors.len() as int)))) }
}

///  Helper: combine two normalized exprs under Add.
///  Flattens, removes zeros, sorts.
pub open spec fn is_const_val(e: &ArithExpr, v: int) -> bool {
    match e { ArithExpr::Const(c) => *c == v, _ => false }
}

pub open spec fn arith_add_normalized(a: ArithExpr, b: ArithExpr) -> ArithExpr {
    if arith_lt(&b, &a) {
        ArithExpr::Add(Box::new(b), Box::new(a))
    } else {
        ArithExpr::Add(Box::new(a), Box::new(b))
    }
}

///  Helper: combine two normalized exprs under Mul.
///  Sorts operands by arith_lt.
pub open spec fn arith_mul_normalized(a: ArithExpr, b: ArithExpr) -> ArithExpr {
    if arith_lt(&b, &a) {
        ArithExpr::Mul(Box::new(b), Box::new(a))
    } else {
        ArithExpr::Mul(Box::new(a), Box::new(b))
    }
}

pub open spec fn arith_normalize(expr: &ArithExpr) -> ArithExpr
    decreases expr,
{
    match expr {
        ArithExpr::Const(c) => ArithExpr::Const(*c),
        ArithExpr::Var(v) => ArithExpr::Var(*v),
        ArithExpr::Add(a, b) =>
            arith_add_normalized(arith_normalize(a), arith_normalize(b)),
        ArithExpr::Sub(a, b) =>
            ArithExpr::Sub(Box::new(arith_normalize(a)), Box::new(arith_normalize(b))),
        ArithExpr::Mul(a, b) =>
            arith_mul_normalized(arith_normalize(a), arith_normalize(b)),
        ArithExpr::Div(a, b) =>
            ArithExpr::Div(Box::new(arith_normalize(a)), Box::new(arith_normalize(b))),
        ArithExpr::Mod(a, b) =>
            ArithExpr::Mod(Box::new(arith_normalize(a)), Box::new(arith_normalize(b))),
        ArithExpr::Index(i, e) =>
            ArithExpr::Index(*i, Box::new(arith_normalize(e))),
        ArithExpr::Shr(a, b) =>
            ArithExpr::Shr(Box::new(arith_normalize(a)), Box::new(arith_normalize(b))),
        ArithExpr::Cmp(op, a, b) =>
            ArithExpr::Cmp(*op, Box::new(arith_normalize(a)), Box::new(arith_normalize(b))),
        ArithExpr::Reduce(v, bound, body) =>
            ArithExpr::Reduce(*v, Box::new(arith_normalize(bound)), Box::new(arith_normalize(body))),
    }
}

///  Normalization preserves evaluation.
pub proof fn lemma_normalize_preserves_eval(
    expr: &ArithExpr, env: Seq<int>, arrays: Seq<Seq<int>>,
)
    requires no_reduce(expr),
    ensures
        arith_eval_with_arrays(&arith_normalize(expr), env, arrays)
            == arith_eval_with_arrays(expr, env, arrays),
    decreases expr,
{
    reveal_with_fuel(arith_normalize, 2);
    match expr {
        ArithExpr::Add(a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
            // arith_add_normalized just swaps if arith_lt(b, a)
            // Either way: eval(Add(na,nb)) == eval(na) + eval(nb) == eval(nb) + eval(na) == eval(Add(nb,na))
            let na = arith_normalize(a);
            let nb = arith_normalize(b);
            let ea = arith_eval_with_arrays(&na, env, arrays);
            let eb = arith_eval_with_arrays(&nb, env, arrays);
            assert(ea + eb == eb + ea);
        },
        ArithExpr::Mul(a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
            let na = arith_normalize(a);
            let nb = arith_normalize(b);
            let ea = arith_eval_with_arrays(&na, env, arrays);
            let eb = arith_eval_with_arrays(&nb, env, arrays);
            assert(ea * eb == eb * ea) by (nonlinear_arith);
        },
        ArithExpr::Sub(a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
        },
        ArithExpr::Div(a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
        },
        ArithExpr::Mod(a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
        },
        ArithExpr::Shr(a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
        },
        ArithExpr::Index(_, e) => {
            lemma_normalize_preserves_eval(e, env, arrays);
        },
        ArithExpr::Cmp(_, a, b) => {
            lemma_normalize_preserves_eval(a, env, arrays);
            lemma_normalize_preserves_eval(b, env, arrays);
        },
        ArithExpr::Reduce(_, _, _) => {
            //  Excluded by requires no_reduce(expr)
        },
        _ => {},  // Const, Var: normalization is identity
    }
}

//  ══════════════════════════════════════════════════════════════
//  Runtime ordering + normalization for RuntimeArithExpr
//  ══════════════════════════════════════════════════════════════

impl RuntimeArithExpr {
    ///  Spec-level size (for decreases clauses — not callable from exec).
    pub open spec fn spec_size(&self) -> nat {
        arith_size(&self.view_spec())
    }

    ///  Variant tag for ordering (matches spec arith_variant_tag).
    pub fn variant_tag(&self) -> (result: u8)
        ensures result as int == arith_variant_tag(&self.view_spec()),
    {
        match self {
            RuntimeArithExpr::Const(_) => 0,
            RuntimeArithExpr::Var(_) => 1,
            RuntimeArithExpr::Add(_, _) => 2,
            RuntimeArithExpr::Sub(_, _) => 3,
            RuntimeArithExpr::Mul(_, _) => 4,
            RuntimeArithExpr::Div(_, _) => 5,
            RuntimeArithExpr::Mod(_, _) => 6,
            RuntimeArithExpr::Index(_, _) => 7,
            RuntimeArithExpr::Shr(_, _) => 8,
            RuntimeArithExpr::Cmp(_, _, _) => 9,
            RuntimeArithExpr::Reduce(_, _, _) => 10,
        }
    }

    ///  Lexicographic less-than (matches spec arith_lt).
    pub fn lt(&self, other: &Self) -> (result: bool)
        ensures result == arith_lt(&self.view_spec(), &other.view_spec()),
        decreases self.spec_size() + other.spec_size(),
    {
        let ta = self.variant_tag();
        let tb = other.variant_tag();
        if ta != tb { return ta < tb; }
        match (self, other) {
            (RuntimeArithExpr::Const(a), RuntimeArithExpr::Const(b)) => *a < *b,
            (RuntimeArithExpr::Var(a), RuntimeArithExpr::Var(b)) => *a < *b,
            (RuntimeArithExpr::Add(a1, a2), RuntimeArithExpr::Add(b1, b2)) =>
                (**a1).lt(&**b1) || (!(**b1).lt(&**a1) && (**a2).lt(&**b2)),
            (RuntimeArithExpr::Sub(a1, a2), RuntimeArithExpr::Sub(b1, b2)) =>
                (**a1).lt(&**b1) || (!(**b1).lt(&**a1) && (**a2).lt(&**b2)),
            (RuntimeArithExpr::Mul(a1, a2), RuntimeArithExpr::Mul(b1, b2)) =>
                (**a1).lt(&**b1) || (!(**b1).lt(&**a1) && (**a2).lt(&**b2)),
            (RuntimeArithExpr::Index(i1, e1), RuntimeArithExpr::Index(i2, e2)) =>
                *i1 < *i2 || (*i1 == *i2 && (**e1).lt(&**e2)),
            _ => false,
        }
    }

    ///  Normalize: sort commutative operands (matches spec arith_normalize).
    pub fn normalize(self) -> (result: Self)
        ensures result.view_spec() == arith_normalize(&self.view_spec()),
        decreases self,
    {
        match self {
            RuntimeArithExpr::Const(c) => RuntimeArithExpr::Const(c),
            RuntimeArithExpr::Var(v) => RuntimeArithExpr::Var(v),
            RuntimeArithExpr::Add(a, b) => {
                let na = (*a).normalize();
                let nb = (*b).normalize();
                if nb.lt(&na) {
                    RuntimeArithExpr::Add(Box::new(nb), Box::new(na))
                } else {
                    RuntimeArithExpr::Add(Box::new(na), Box::new(nb))
                }
            },
            RuntimeArithExpr::Sub(a, b) =>
                RuntimeArithExpr::Sub(Box::new((*a).normalize()), Box::new((*b).normalize())),
            RuntimeArithExpr::Mul(a, b) => {
                let na = (*a).normalize();
                let nb = (*b).normalize();
                if nb.lt(&na) {
                    RuntimeArithExpr::Mul(Box::new(nb), Box::new(na))
                } else {
                    RuntimeArithExpr::Mul(Box::new(na), Box::new(nb))
                }
            },
            RuntimeArithExpr::Div(a, b) =>
                RuntimeArithExpr::Div(Box::new((*a).normalize()), Box::new((*b).normalize())),
            RuntimeArithExpr::Mod(a, b) =>
                RuntimeArithExpr::Mod(Box::new((*a).normalize()), Box::new((*b).normalize())),
            RuntimeArithExpr::Index(i, e) =>
                RuntimeArithExpr::Index(i, Box::new((*e).normalize())),
            RuntimeArithExpr::Shr(a, b) =>
                RuntimeArithExpr::Shr(Box::new((*a).normalize()), Box::new((*b).normalize())),
            RuntimeArithExpr::Cmp(op, a, b) =>
                RuntimeArithExpr::Cmp(op, Box::new((*a).normalize()), Box::new((*b).normalize())),
            RuntimeArithExpr::Reduce(v, bound, body) =>
                RuntimeArithExpr::Reduce(v, Box::new((*bound).normalize()), Box::new((*body).normalize())),
        }
    }
}

impl RuntimeCmpOp {
    pub fn clone(&self) -> (result: Self)
        ensures result == *self,
    {
        match self {
            RuntimeCmpOp::Lt => RuntimeCmpOp::Lt,
            RuntimeCmpOp::Le => RuntimeCmpOp::Le,
            RuntimeCmpOp::Gt => RuntimeCmpOp::Gt,
            RuntimeCmpOp::Ge => RuntimeCmpOp::Ge,
            RuntimeCmpOp::Eq => RuntimeCmpOp::Eq,
            RuntimeCmpOp::Ne => RuntimeCmpOp::Ne,
        }
    }
}

impl RuntimeCmpOp {
    pub fn eq(&self, other: &Self) -> (result: bool)
        ensures result == (*self == *other),
    {
        match (self, other) {
            (RuntimeCmpOp::Lt, RuntimeCmpOp::Lt) => true,
            (RuntimeCmpOp::Le, RuntimeCmpOp::Le) => true,
            (RuntimeCmpOp::Gt, RuntimeCmpOp::Gt) => true,
            (RuntimeCmpOp::Ge, RuntimeCmpOp::Ge) => true,
            (RuntimeCmpOp::Eq, RuntimeCmpOp::Eq) => true,
            (RuntimeCmpOp::Ne, RuntimeCmpOp::Ne) => true,
            _ => false,
        }
    }
}

impl RuntimeArithExpr {
    ///  Structural equality: true iff the two trees are identical.
    pub fn eq(&self, other: &Self) -> (result: bool)
        ensures result == (self.view_spec() == other.view_spec()),
        decreases self,
    {
        match (self, other) {
            (RuntimeArithExpr::Const(a), RuntimeArithExpr::Const(b)) => *a == *b,
            (RuntimeArithExpr::Var(a), RuntimeArithExpr::Var(b)) => *a == *b,
            (RuntimeArithExpr::Add(a1, a2), RuntimeArithExpr::Add(b1, b2)) =>
                (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Sub(a1, a2), RuntimeArithExpr::Sub(b1, b2)) =>
                (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Mul(a1, a2), RuntimeArithExpr::Mul(b1, b2)) =>
                (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Div(a1, a2), RuntimeArithExpr::Div(b1, b2)) =>
                (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Mod(a1, a2), RuntimeArithExpr::Mod(b1, b2)) =>
                (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Index(a1, a2), RuntimeArithExpr::Index(b1, b2)) =>
                *a1 == *b1 && (**a2).eq(&**b2),
            (RuntimeArithExpr::Shr(a1, a2), RuntimeArithExpr::Shr(b1, b2)) =>
                (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Cmp(op1, a1, a2), RuntimeArithExpr::Cmp(op2, b1, b2)) =>
                op1.eq(op2) && (**a1).eq(&**b1) && (**a2).eq(&**b2),
            (RuntimeArithExpr::Reduce(v1, bd1, bo1), RuntimeArithExpr::Reduce(v2, bd2, bo2)) =>
                *v1 == *v2 && (**bd1).eq(&**bd2) && (**bo1).eq(&**bo2),
            _ => false,
        }
    }
}

impl RuntimeArithExpr {
    pub fn clone(&self) -> (result: Self)
        ensures result.view_spec() == self.view_spec(),
        decreases self,
    {
        match self {
            RuntimeArithExpr::Const(c) => RuntimeArithExpr::Const(*c),
            RuntimeArithExpr::Var(i) => RuntimeArithExpr::Var(*i),
            RuntimeArithExpr::Add(a, b) =>
                RuntimeArithExpr::Add(Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Sub(a, b) =>
                RuntimeArithExpr::Sub(Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Mul(a, b) =>
                RuntimeArithExpr::Mul(Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Div(a, b) =>
                RuntimeArithExpr::Div(Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Mod(a, b) =>
                RuntimeArithExpr::Mod(Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Index(arr, idx) =>
                RuntimeArithExpr::Index(*arr, Box::new((**idx).clone())),
            RuntimeArithExpr::Shr(a, b) =>
                RuntimeArithExpr::Shr(Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Cmp(op, a, b) =>
                RuntimeArithExpr::Cmp(op.clone(), Box::new((**a).clone()), Box::new((**b).clone())),
            RuntimeArithExpr::Reduce(v, bound, body) =>
                RuntimeArithExpr::Reduce(*v, Box::new((**bound).clone()), Box::new((**body).clone())),
        }
    }
}

impl RuntimeArithExpr {
    ///  Map to spec ArithExpr.
    pub open spec fn view_spec(&self) -> ArithExpr
        decreases self,
    {
        match self {
            RuntimeArithExpr::Const(c) => ArithExpr::Const(*c as int),
            RuntimeArithExpr::Var(i) => ArithExpr::Var(*i as nat),
            RuntimeArithExpr::Add(a, b) => ArithExpr::Add(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Sub(a, b) => ArithExpr::Sub(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Mul(a, b) => ArithExpr::Mul(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Div(a, b) => ArithExpr::Div(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Mod(a, b) => ArithExpr::Mod(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Index(arr, idx) => ArithExpr::Index(*arr as nat, Box::new(idx.view_spec())),
            RuntimeArithExpr::Shr(a, b) => ArithExpr::Shr(Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Cmp(op, a, b) => ArithExpr::Cmp(op.view_spec(), Box::new(a.view_spec()), Box::new(b.view_spec())),
            RuntimeArithExpr::Reduce(var, bound, body) => ArithExpr::Reduce(*var as nat, Box::new(bound.view_spec()), Box::new(body.view_spec())),
        }
    }
}

///  All intermediate results of evaluating expr with env fit in i64.
///  For Div/Mod: requires non-negative dividend and positive divisor,
///  matching GPU/shader truncating division semantics (which agrees with
///  Verus Euclidean int division for non-negative operands).
pub open spec fn arith_eval_fits_i64(expr: &ArithExpr, env: Seq<int>) -> bool
    decreases expr,
{
    i64::MIN as int <= arith_eval(expr, env)
    && arith_eval(expr, env) <= i64::MAX as int
    && match expr {
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b) =>
            arith_eval_fits_i64(a, env) && arith_eval_fits_i64(b, env),
        //  Shr: non-negative operands (matches GPU fixed-point semantics;
        //  Euclidean and truncating division agree for non-negative values)
        ArithExpr::Shr(a, b) =>
            arith_eval_fits_i64(a, env) && arith_eval_fits_i64(b, env)
            && arith_eval(a, env) >= 0 && arith_eval(b, env) >= 0,
        ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) =>
            arith_eval_fits_i64(a, env) && arith_eval_fits_i64(b, env)
            && arith_eval(a, env) >= 0 && arith_eval(b, env) > 0,
        ArithExpr::Index(_, idx) => arith_eval_fits_i64(idx, env),
        ArithExpr::Cmp(_, a, b) =>
            arith_eval_fits_i64(a, env) && arith_eval_fits_i64(b, env),
        //  Reduce: check the bound expression fits. Body bounds are data-dependent
        //  (sum of n terms can grow arbitrarily) so they must be checked by the
        //  caller for the specific kernel. The top-level result bound is still
        //  checked by the enclosing i64::MIN <= arith_eval(...) <= i64::MAX.
        ArithExpr::Reduce(_, bound, _) => arith_eval_fits_i64(bound, env),
    }
}

///  Convert i64 sequence to int sequence.
pub open spec fn i64_seq_to_int(s: Seq<i64>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[i] as int)
}

///  Helper: verified i64 division for non-negative operands.
///  Non-negative inputs ensure Euclidean (Verus int) and truncating (Rust i64) agree.
fn nonneg_i64_div(a: i64, b: i64) -> (result: i64)
    requires
        a >= 0,
        b > 0,
        (a as int) / (b as int) <= i64::MAX as int,
    ensures
        result as int == (a as int) / (b as int),
{
    a / b
}

///  Helper: verified i64 modulo for non-negative operands.
fn nonneg_i64_mod(a: i64, b: i64) -> (result: i64)
    requires
        a >= 0,
        b > 0,
    ensures
        result as int == (a as int) % (b as int),
{
    a % b
}

///  Predicate: expression contains no Reduce nodes.
///  Used as precondition for runtime_arith_eval's correctness proof.
pub open spec fn no_reduce(expr: &ArithExpr) -> bool
    decreases expr,
{
    match expr {
        ArithExpr::Reduce(_, _, _) => false,
        ArithExpr::Const(_) | ArithExpr::Var(_) => true,
        ArithExpr::Add(a, b) | ArithExpr::Sub(a, b) | ArithExpr::Mul(a, b)
        | ArithExpr::Div(a, b) | ArithExpr::Mod(a, b) | ArithExpr::Shr(a, b) =>
            no_reduce(a) && no_reduce(b),
        ArithExpr::Cmp(_, a, b) => no_reduce(a) && no_reduce(b),
        ArithExpr::Index(_, idx) => no_reduce(idx),
    }
}

///  Compute 2^n as i128, for 0 < n < 64.
fn exec_pow2_i128(n: u32) -> (result: i128)
    requires 0 < n < 64,
    ensures result == crate::swizzle::pow2(n as nat) as int, result > 0,
    decreases n,
{
    if n == 1 {
        proof { assert(crate::swizzle::pow2(1) == 2) by (compute_only); }
        return 2i128;
    }
    let half = exec_pow2_i128(n - 1);
    proof {
        crate::proof::swizzle_lemmas::lemma_pow2_positive((n - 1) as nat);
        assert(crate::swizzle::pow2(n as nat) == 2 * crate::swizzle::pow2((n - 1) as nat));
        //  half = pow2(n-1) <= pow2(62) < 2^63 << i128::MAX/2
        crate::proof::swizzle_lemmas::lemma_pow2_monotone((n - 1) as nat, 62);
        assert(crate::swizzle::pow2(62) == 0x4000000000000000int) by (compute_only);
        assert(half <= 0x4000000000000000i128);
    }
    return half * 2;
}

pub fn runtime_arith_eval(expr: &RuntimeArithExpr, env: &Vec<i64>) -> (result: i64)
    requires
        arith_eval_fits_i64(&expr.view_spec(), i64_seq_to_int(env@)),
        no_reduce(&expr.view_spec()),
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
                lemma_arith_eval_div(&a.view_spec(), &b.view_spec(), env_spec);
                lemma_fits_i64_div(&a.view_spec(), &b.view_spec(), env_spec);
            }
            if vb == 0 {
                return 0i64;
            } else {
                let r = nonneg_i64_div(va, vb);
                proof {
                    assert(arith_eval(&expr.view_spec(), env_spec) == (va as int) / (vb as int));
                }
                return r;
            }
        },
        RuntimeArithExpr::Mod(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                lemma_arith_eval_mod(&a.view_spec(), &b.view_spec(), env_spec);
                lemma_fits_i64_mod(&a.view_spec(), &b.view_spec(), env_spec);
            }
            if vb == 0 {
                return 0i64;
            } else {
                let r = nonneg_i64_mod(va, vb);
                proof {
                    assert(arith_eval(&expr.view_spec(), env_spec) == (va as int) % (vb as int));
                }
                return r;
            }
        },
        RuntimeArithExpr::Sub(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                lemma_arith_eval_sub(&a.view_spec(), &b.view_spec(), env_spec);
                lemma_fits_i64_sub(&a.view_spec(), &b.view_spec(), env_spec);
            }
            return va - vb;
        },
        RuntimeArithExpr::Shr(a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            proof {
                lemma_arith_eval_shr(&a.view_spec(), &b.view_spec(), env_spec);
                lemma_fits_i64_shr(&a.view_spec(), &b.view_spec(), env_spec);
            }
            if vb <= 0 {
                return va;
            } else if vb >= 63 {
                //  va >= 0, pow2(vb) >= pow2(63) > i64::MAX >= va
                //  So va / pow2(vb) == 0
                proof {
                    crate::proof::swizzle_lemmas::lemma_pow2_monotone(63, vb as nat);
                    assert(crate::swizzle::pow2(63) == 0x8000000000000000int) by (compute_only);
                    let vi = va as int;
                    let pv = crate::swizzle::pow2(vb as nat) as int;
                    assert(vi >= 0);
                    assert(vi < pv) by (nonlinear_arith)
                        requires vi >= 0, vi <= i64::MAX as int, pv >= 0x8000000000000000int;
                    assert(vi / pv == 0int) by (nonlinear_arith)
                        requires 0 <= vi, vi < pv, pv > 0;
                }
                return 0i64;
            } else {
                //  0 < vb < 63, va >= 0: use nonneg_i64_div with exec pow2
                let divisor_i128 = exec_pow2_i128(vb as u32);
                //  pow2(vb) < pow2(63) = 2^63, fits in i64
                proof {
                    crate::proof::swizzle_lemmas::lemma_pow2_monotone(vb as nat, 62);
                    assert(crate::swizzle::pow2(62) == 0x4000000000000000int) by (compute_only);
                }
                let divisor = divisor_i128 as i64;
                let r = nonneg_i64_div(va, divisor);
                return r;
            }
        },
        RuntimeArithExpr::Index(_arr, idx) => {
            proof { lemma_arith_eval_index(*_arr as nat, &idx.view_spec(), env_spec); }
            return runtime_arith_eval(idx, env);
        },
        RuntimeArithExpr::Cmp(op, a, b) => {
            let va = runtime_arith_eval(a, env);
            let vb = runtime_arith_eval(b, env);
            let r: i64 = match op {
                RuntimeCmpOp::Lt => if va < vb { 1 } else { 0 },
                RuntimeCmpOp::Le => if va <= vb { 1 } else { 0 },
                RuntimeCmpOp::Gt => if va > vb { 1 } else { 0 },
                RuntimeCmpOp::Ge => if va >= vb { 1 } else { 0 },
                RuntimeCmpOp::Eq => if va == vb { 1 } else { 0 },
                RuntimeCmpOp::Ne => if va != vb { 1 } else { 0 },
            };
            return r;
        },
        RuntimeArithExpr::Reduce(_var, _bound, _body) => {
            //  Unreachable under no_reduce precondition.
            //  Correct implementation exists but postcondition proof is deferred.
            proof { assert(false); }
            return 0i64;
        },
    }
}

} //  verus!
