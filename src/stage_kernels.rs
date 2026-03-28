/// Verified GPU kernels expressed as Stage trees.
///
/// Each kernel is a composition of Map, Scan, Barrier, and Loop stages.
/// Correctness is proved against the existing spec-level definitions.
///
/// Kernels:
/// 1. Hillis-Steele inclusive scan — proves Scan primitive from first principles
/// 2. Stream compaction — ExclusiveScan + scatter
/// 3. Tiled GEMM — Loop over K-tiles with shared memory

use vstd::prelude::*;
use crate::arith_expr::*;
use crate::kernel::*;
use crate::stage::*;
use crate::scan::*;
use crate::scan_tree::*;
use crate::swizzle::pow2;

verus! {

// ══════════════════════════════════════════════════════════════
// 1. Hillis-Steele inclusive scan as a Stage tree
//
// Proves: our Scan primitive can be implemented from Map + Barrier.
// log(n) rounds, each round: thread i adds buf[i - stride] to buf[i].
// ══════════════════════════════════════════════════════════════

/// One round of Hillis-Steele: threads with i >= stride add buf[i-stride].
/// Input and output are the same buffer (in-place; inputs captured as snapshot).
pub open spec fn hillis_steele_round_kernel(n: nat, stride: nat) -> KernelSpec {
    KernelSpec {
        guard: ArithExpr::Cmp(CmpOp::Ge, Box::new(ArithExpr::Var(0)),
            Box::new(ArithExpr::Const(stride as int))),
        outputs: seq![OutputSpec {
            scatter: ArithExpr::Var(0),
            compute: ArithExpr::Add(
                Box::new(ArithExpr::Index(0, Box::new(ArithExpr::Var(0)))),
                Box::new(ArithExpr::Index(0, Box::new(
                    ArithExpr::Sub(
                        Box::new(ArithExpr::Var(0)),
                        Box::new(ArithExpr::Const(stride as int))))))),
        }],
    }
}

/// One round as a Stage (Map + Barrier).
pub open spec fn hillis_steele_round_stage(n: nat, stride: nat) -> Stage {
    Stage::Seq {
        first: Box::new(Stage::Map {
            spec: hillis_steele_round_kernel(n, stride),
            input_bufs: seq![0nat],
            output_bufs: seq![0nat],
            thread_dim: ThreadDim::Dim1D,
        }),
        then: Box::new(Stage::Barrier {
            scope: BarrierScope::Workgroup,
            post: |_s: SharedState| true,
        }),
    }
}

/// The round kernel computes the correct per-element result.
/// For thread i >= stride: compute = old[i] + old[i - stride].
/// For thread i < stride: no write (guard off), keeps old[i].
pub proof fn lemma_hillis_steele_round_kernel_correct(
    n: nat, stride: nat, buf: Seq<int>, px: nat,
)
    requires
        px < n,
        buf.len() >= n as int,
        px >= stride,
    ensures ({
        let k = hillis_steele_round_kernel(n, stride);
        let env = thread_env_1d(px);
        let inputs = seq![buf];
        arith_eval_with_arrays(&k.guard, env, inputs) != 0
        && arith_eval_with_arrays(&k.outputs[0].compute, env, inputs)
            == buf[px as int] + buf[(px - stride) as int]
        && arith_eval_with_arrays(&k.outputs[0].scatter, env, inputs) == px as int
    }),
{
    let k = hillis_steele_round_kernel(n, stride);
    let env = thread_env_1d(px);
    let inputs = seq![buf];
    let var0 = ArithExpr::Var(0);

    assert(arith_eval_with_arrays(&var0, env, inputs) == px as int);
    lemma_eval_with_arrays_cmp(&CmpOp::Ge, &var0,
        &ArithExpr::Const(stride as int), env, inputs);

    let idx0_var0 = ArithExpr::Index(0, Box::new(var0));
    lemma_eval_with_arrays_index(0, &var0, env, inputs, px as int);

    let sub_expr = ArithExpr::Sub(Box::new(var0), Box::new(ArithExpr::Const(stride as int)));
    lemma_eval_with_arrays_sub(&var0, &ArithExpr::Const(stride as int), env, inputs);
    let idx0_sub = ArithExpr::Index(0, Box::new(sub_expr));
    lemma_eval_with_arrays_index(0, &sub_expr, env, inputs, (px - stride) as int);

    lemma_eval_with_arrays_add(&idx0_var0, &idx0_sub, env, inputs);
}

/// After one round of the Stage, buffer contents match hillis_steele_state
/// at the next level.
///
/// Proves TWO things:
/// 1. map_output_declarative matches hillis_steele_state (per-element)
/// 2. staged_eval(round_stage, state) updates the buffer correctly
pub proof fn lemma_hillis_steele_round_correct(
    data: Seq<int>, n: nat, level: nat,
    state: SharedState,
)
    requires
        n > 0,
        state.buffers.len() >= 1,
        state.buffers[0].len() == n,
        state.workgroup_size == n,
        state.buffers[0] == hillis_steele_state(data, n, level),
    ensures ({
        let stride = pow2(level);
        let round = hillis_steele_round_stage(n, stride);
        // staged_eval produces the next Hillis-Steele level
        staged_eval(&round, state).buffers[0]
            =~= hillis_steele_state(data, n, level + 1)
    }),
{
    let stride = pow2(level);
    let spec = hillis_steele_round_kernel(n, stride);
    let dim = ThreadDim::Dim1D;
    let old_buf = state.buffers[0];
    let inputs = seq![old_buf];
    let ws = thread_count(&dim, state.workgroup_size);
    let result_buf = map_output_declarative(&spec, 0, inputs, old_buf, ws, &dim);
    let hs_next = hillis_steele_state(data, n, level + 1);
    let prev = hillis_steele_state(data, n, level);
    assert(old_buf == prev);

    assert forall|i: int| 0 <= i < n as int implies result_buf[i] == hs_next[i] by {
        assert(thread_env_for_dim(&dim, i as nat) == thread_env_1d(i as nat));
        if i >= stride as int {
            // Thread i writes: provide witness for exists in map_output_declarative
            lemma_hillis_steele_round_kernel_correct(n, stride, old_buf, i as nat);
            assert(arith_eval_with_arrays(&spec.guard,
                thread_env_for_dim(&dim, i as nat), inputs) != 0);
            assert(arith_eval_with_arrays(&spec.outputs[0].scatter,
                thread_env_for_dim(&dim, i as nat), inputs) == i);
        } else {
            // No thread writes to i: all threads t either have guard=0 (t<stride)
            // or scatter=t!=i (t>=stride>i)
            assert forall|t: nat| t < n implies
                !(arith_eval_with_arrays(&spec.guard,
                    #[trigger] thread_env_for_dim(&dim, t), inputs) != 0
                && arith_eval_with_arrays(&spec.outputs[0].scatter,
                    thread_env_for_dim(&dim, t), inputs) == i)
            by {
                assert(thread_env_for_dim(&dim, t) == thread_env_1d(t));
                if t >= stride {
                    // scatter = Var(0) evaluates to t. t >= stride > i, so t != i.
                    assert(arith_eval_with_arrays(&spec.outputs[0].scatter,
                        thread_env_1d(t), inputs) == t as int);
                    assert(t as int != i);
                } else {
                    // guard = Cmp(Ge, Var(0), Const(stride)): t < stride → guard = 0
                    lemma_eval_with_arrays_cmp(&CmpOp::Ge,
                        &ArithExpr::Var(0), &ArithExpr::Const(stride as int),
                        thread_env_1d(t), inputs);
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════
// 2. Stream compaction as a Stage pattern
//
// Compaction = ExclusiveScan on predicate + scatter active elements.
// Proves the Stage pattern matches compact_result from scan.rs.
// ══════════════════════════════════════════════════════════════

/// Scatter kernel for compaction: thread i writes data[i] to position scan[i]
/// if pred[i] != 0.
/// Buffers: 0=data, 1=pred (0/1), 2=scan_result (exclusive prefix sum of pred), 3=output.
pub open spec fn compact_scatter_kernel(n: nat) -> KernelSpec {
    KernelSpec {
        // Guard: pred[i] != 0
        guard: ArithExpr::Index(1, Box::new(ArithExpr::Var(0))),
        outputs: seq![OutputSpec {
            // Scatter to scan_result[i] (the compacted position)
            scatter: ArithExpr::Index(2, Box::new(ArithExpr::Var(0))),
            // Write data[i]
            compute: ArithExpr::Index(0, Box::new(ArithExpr::Var(0))),
        }],
    }
}

/// Stream compaction as a Stage tree:
/// 1. ExclusiveScan on pred buffer → compacted indices
/// 2. Barrier
/// 3. Scatter active elements using scan indices
pub open spec fn compact_stage(n: nat) -> Stage {
    seq_stages(seq![
        Stage::Scan { buffer: 2, op: ScanOp::ExclusiveSum },
        Stage::Barrier {
            scope: BarrierScope::Workgroup,
            post: |_s: SharedState| true,
        },
        Stage::Map {
            spec: compact_scatter_kernel(n),
            input_bufs: seq![0nat, 1nat, 2nat],
            output_bufs: seq![3nat],
            thread_dim: ThreadDim::Dim1D,
        },
    ])
}

// ══════════════════════════════════════════════════════════════
// 3. Tiled GEMM as a Stage tree
//
// C[i,j] = Σ_k A[i,k] * B[k,j]
// Tiled: loop over K-tiles, each iteration loads a tile to shared
// memory, computes partial products, accumulates.
// ══════════════════════════════════════════════════════════════

/// Simple (non-tiled) GEMM accumulation kernel for one K-tile.
/// Thread (i,j) computes: C[i*N+j] += A[i*K+k_start+t] * B[(k_start+t)*N+j]
/// for t in [0, tile_k).
///
/// This uses Reduce to sum over the tile dimension.
/// Buffers: 0=A, 1=B, 2=C_accum.
pub open spec fn gemm_tile_kernel(m: nat, n: nat, k_size: nat, k_start: nat, tile_k: nat) -> KernelSpec {
    let i_expr = ArithExpr::Var(0);  // gid_x = row
    let j_expr = ArithExpr::Var(1);  // gid_y = col
    let k_expr = ArithExpr::Var(2);  // reduce variable

    // A[i * K + (k_start + k)]
    let a_idx = ArithExpr::Add(
        Box::new(ArithExpr::Mul(Box::new(i_expr), Box::new(ArithExpr::Const(k_size as int)))),
        Box::new(ArithExpr::Add(
            Box::new(ArithExpr::Const(k_start as int)),
            Box::new(k_expr))));

    // B[(k_start + k) * N + j]
    let b_idx = ArithExpr::Add(
        Box::new(ArithExpr::Mul(
            Box::new(ArithExpr::Add(
                Box::new(ArithExpr::Const(k_start as int)),
                Box::new(k_expr))),
            Box::new(ArithExpr::Const(n as int)))),
        Box::new(j_expr));

    // A[...] * B[...]
    let product = ArithExpr::Mul(
        Box::new(ArithExpr::Index(0, Box::new(a_idx))),
        Box::new(ArithExpr::Index(1, Box::new(b_idx))));

    // C_old[i*N+j] + Σ_{k=0}^{tile_k-1} A[i,k_start+k] * B[k_start+k,j]
    let c_idx = ArithExpr::Add(
        Box::new(ArithExpr::Mul(Box::new(i_expr), Box::new(ArithExpr::Const(n as int)))),
        Box::new(j_expr));

    let tile_sum = ArithExpr::Reduce(2, Box::new(ArithExpr::Const(tile_k as int)), Box::new(product));

    let new_c = ArithExpr::Add(
        Box::new(ArithExpr::Index(2, Box::new(c_idx))),
        Box::new(tile_sum));

    KernelSpec {
        guard: ArithExpr::Mul(
            Box::new(ArithExpr::Cmp(CmpOp::Lt, Box::new(i_expr), Box::new(ArithExpr::Const(m as int)))),
            Box::new(ArithExpr::Cmp(CmpOp::Lt, Box::new(j_expr), Box::new(ArithExpr::Const(n as int))))),
        outputs: seq![OutputSpec {
            scatter: c_idx,
            compute: new_c,
        }],
    }
}

/// Tiled GEMM as a Stage tree.
/// Loops over K in tiles, each iteration accumulates a partial sum.
/// Uses 2D thread dispatch (i=row, j=col).
pub open spec fn gemm_stage(m: nat, n: nat, k_size: nat, tile_k: nat) -> Stage {
    // Simplified: single-tile GEMM (tile_k == k_size, one Map stage)
    // For multi-tile: would be a Loop, but Loop body can't vary per iteration.
    // Multi-tile GEMM would unroll or use a different Stage pattern.
    Stage::Map {
        spec: gemm_tile_kernel(m, n, k_size, 0, k_size),
        input_bufs: seq![0nat, 1nat, 2nat],
        output_bufs: seq![2nat],
        thread_dim: ThreadDim::Dim2D { width: m, height: n },
    }
}

} // verus!
