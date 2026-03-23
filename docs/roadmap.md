# verus-cutedsl: Roadmap & Implementation Guide

## Current State (as of March 2026)

**1383 verified functions, 0 errors, 0 assumes.**

### What exists

**Spec layer** (pure math):
- `shape.rs` — shapes, delinearize, linearize, dot_product
- `layout.rs` — LayoutSpec with offset, cosize, validity, sortedness, tractability, injectivity, surjectivity, bijectivity, has_no_unit_modes
- `composition.rs` — `compose` (CuTe recursive, correct), `compose_linear` (legacy, first-mode only), `compose_single` (recursive single-mode building block), `compose_extended` (deprecated), `compose_single_mode` / `compose_single_mode_extended` (building blocks for legacy compose)
- `complement.rs` — complement(A, M), complement_admissible, stride_product
- `divide.rs` — `logical_divide` (CuTe recursive, correct), `logical_divide_linear` (legacy), `logical_divide_mode` (convenience first-mode), `logical_divide_extended` (deprecated), divide_tile, divide_rest, num_tiles
- `product.rs` — logical_product, blocked_product, raked_product, scalar_layout, scale_strides
- `coalesce.rs` — coalesce, coalesce_pair, flatten (canonical, idempotent), flatten_partial (one-pass), remove_units_iter, modes_coalesceable, is_fully_coalesced, group_modes
- `inverse.rs` — right_inverse, left_inverse, shape_prefix_products
- `swizzle.rs` — swizzle, pow2, bit operations
- `permutation.rs` — permute_modes, compose_permutations, swap_permutation
- `slice.rs` — slice_layout, dice_layout
- `tiling.rs` — DividedLayout, zipped_divide, tile_shape, rest_shape, predicated_divide, warp_partition, register_partition
- `predication.rs` — ceil_div, padded_size, predicated layouts
- `compatibility.rs` — offset_equivalent, size_compatible, offset_compatible
- `gemm.rs` — TensorSpec, GemmSpec, gemm_spec, tiled GEMM specs
- `contraction.rs` — tensor contraction specs (Einstein summation)
- `scan.rs` — reduce, inclusive_scan, exclusive_scan, compact operations
- `scan_blelloch.rs`, `scan_brent_kung.rs`, `scan_tree.rs`, `scan_multiblock.rs`, `scan_segmented.rs` — algorithm-specific scan specs
- `radix_sort.rs` — radix_step, radix_sort, scatter specs

**Proof layer** (~800 proof functions):
- All key theorems proved with zero assumes (see README.md for full list)
- Key files: composition_lemmas.rs (compose_single correctness), coalesce_lemmas.rs (canonicality), divide_lemmas.rs, product_lemmas.rs, inverse_lemmas.rs, complement_lemmas.rs, injectivity_lemmas.rs, integer_helpers.rs

**Runtime layer** (exec functions):
- `runtime/layout.rs` — RuntimeLayout with Ghost<LayoutSpec>, wf_spec(), offset computation, Display/Debug
- `runtime/ops.rs` — compose_linear_exec (NOTE: implements compose_linear, NOT compose!), complement_exec, logical_product_exec, coalesce_exec, flatten_exec, slice_exec, dice_exec, divide_tile_exec, divide_rest_exec, divide_mode_exec, group_modes_exec, remove_units_iter_exec, zipped_divide_exec
- `runtime/inverse.rs` — right_inverse_exec
- `runtime/scan.rs` — hillis_steele, tree_reduce, blelloch_exclusive_scan, brent_kung_inclusive_scan (all generic over ExecRing trait)
- `runtime/scan_multiblock.rs` — three_phase_inclusive_scan, compact, histogram, multi_split, reduce
- `runtime/scan_segmented.rs` — segmented scan exec
- `runtime/radix_sort.rs` — radix_step_exec, radix_sort_exec
- `runtime/swizzle.rs` — swizzled_offset_exec, bxor/shr/shl/band_mask external body wrappers
- `runtime/gemm.rs` — gemm_staged_cta_kernel, gemm_k_tile_loop, gemm_dispatch
- `runtime/tiling.rs` — zipped_divide_exec, tile_shape_exec, rest_shape_exec
- `runtime/predication.rs` — ceil_div_exec, padded_size_exec, predicate_exec
- `runtime/contraction.rs` — contraction_output_shape_exec
- `runtime/shape_helpers.rs` — shape_size_exec, delinearize_exec, dot_product_exec

### Naming conventions (important!)

After our rename:
- `compose` = CuTe recursive (correct). Spec in composition.rs line ~228. Uses `compose_single` internally.
- `compose_linear` = legacy first-mode-only. Spec in composition.rs line ~141. Uses `compose_single_mode` internally.
- `compose_linear_exec` = exec for `compose_linear` (NOT `compose`!). This is the key gap.
- `logical_divide` = CuTe recursive (correct). Uses `compose` internally.
- `logical_divide_linear` = legacy. Uses `compose_linear` internally.
- `flatten` = canonical idempotent form = `coalesce(flatten_partial(L))`.
- `flatten_partial` = one pass = `remove_units_iter(coalesce(L), 0)`. NOT idempotent.

### Key proof patterns discovered

1. **`return` per branch** — isolates postcondition checking. Essential for multi-case inductive proofs.
2. **Duplicate proof into if-else branches** — z3 can't merge conditional facts across branches for spec function applications.
3. **Recursive `open spec fn` predicates** don't auto-unfold reliably. Assert branch conditions explicitly (`assert(!(cond1)); assert(cond2);`) to guide z3.
4. **`lemma_offset_eq_layout`** bridges `=~=` to offset equality. Z3 can't do this even with `==`.
5. **Minimize helper requires** — use `a.valid(), b_shape > 0` instead of recursive predicates when possible.
6. **`by (compute_only)`** for concrete values — 98% rlimit reduction.
7. **`delinearize_concat` + `dot_product_append`** is the universal offset decomposition.
8. **Modular scaling** (`lemma_mod_scale`, `lemma_div_scale`) enables straddle case proofs.

### Key integer helpers available (in proof/integer_helpers.rs)

- `lemma_div_div(x, a, b)` — `(x/a)/b == x/(a*b)`
- `lemma_mod_mod(x, a, b)` — `(x%(a*b))%a == x%a`
- `lemma_mod_div_mixed(x, a, b)` — `(x%(a*b))/a == (x/a)%b`
- `lemma_mod_scale(x, a, b)` — `a*(x%b) == (a*x)%(a*b)`
- `lemma_div_scale(x, a, b)` — `x/b == (a*x)/(a*b)`
- `lemma_div_mod_decompose(a, b, d)` — `(a + d*b) % d == a, (a + d*b) / d == b`
- `lemma_div_upper_bound(x, d, y)` — `x < d*y ==> x/d < y`
- `lemma_mixed_radix_bound` — `coord + extent*rest < extent*rest_size`
- Plus: mul_pos, mul_nonneg, mul_le_right, multiple_scaled, sum_multiples, diff_multiples, divisibility_transitive

### Key shape/offset helpers available

- `lemma_delinearize_concat(x, s_a, s_b)` — delinearize distributes over shape concat
- `lemma_dot_product_append(c_a, c_b, s_a, s_b)` — dot product splits over concat
- `lemma_offset_within_first_mode(layout, x)` — `x < shape[0] ==> offset(x) == x * stride[0]`
- `lemma_offset_at_split_mode(layout, i, x)` — `offset(pp[i]*x) == x * stride[i]`
- `lemma_shape_size_split(s, k)` — `size(s) == size(take(k)) * size(skip(k))`
- `lemma_take1_eq_first(s)` — `s.take(1) =~= seq![s.first()]`
- `lemma_zipped_setup(a, b)` — one-call: zipped layout valid + nonneg strides + size == M
- `lemma_shape0_lt_size(layout)` — `shape[0] < size` for rank >= 2 with no unit modes
- `lemma_skip1_preserves_canonical(layout)` — skip(1) preserves valid/sorted/tractable/coalesced/unit-free

---

## Next Steps: Implementation Guide

### 1. Runtime `compose_exec` for the correct compose

**What:** Add an exec function that implements `compose` (= `compose_single` distributed over B's modes) at runtime, producing a `RuntimeLayout` whose `@` equals `compose(a@, b@)`.

**Why it's needed:** Currently `compose_linear_exec` implements `compose_linear` (first-mode only). Runtime code using it gets wrong strides for non-column-major multi-rank A.

**Difficulty:** Medium-Hard. The challenge is the straddle case: `compose_single` can produce MULTI-mode output from a single input mode. So the output rank isn't known at compile time — it depends on how B's strides align with A's modes.

**Approach:**
1. Implement `compose_single_exec(a: &RuntimeLayout, b_shape: u64, b_stride: u64) -> RuntimeLayout` that mirrors the spec:
   - Case 1 (within first mode): trivial, same as compose_single_mode
   - Case 2 (straddle): compute `q = m/b_stride`, build `[q] ++ recursive_result` shape/stride
   - Case 3 (skip): recurse on `a.skip(1)` with `b_stride / m`
   - Case 4 (fallback): same as case 1
2. Implement `compose_exec(a, b)` that distributes `compose_single_exec` over B's modes, concatenating shapes/strides
3. Requires proving: `compose_single_admissible` holds for the runtime inputs (this is checked by the caller's requires)
4. Overflow: need `shape_size(result.shape) <= u64::MAX` and intermediate stride products fit in i64

**Key files to modify:**
- `runtime/ops.rs` — add `compose_single_exec`, add new `compose_exec` (rename old to `compose_linear_exec`)
- Need `lemma_crs_shape_valid`, `lemma_crs_len_match`, `lemma_crs_size` for the proof obligations

**Estimated lines:** ~150 exec + ~50 proof annotations

### 2. End-to-end GEMM verification with correct compose

**What:** Update the GEMM infrastructure to use `compose` (correct) instead of `compose_linear` (broken).

**Why:** The GEMM pipeline (`gemm.rs`, `runtime/gemm.rs`, `proof/gemm_lemmas.rs`) was built with `compose_linear`. For column-major matrices this works (compose_linear == compose for column-major). But for non-column-major (e.g., row-major, strided) matrices, the tiling is wrong.

**Difficulty:** Medium. Most changes are mechanical (s/compose_linear/compose/). The hard part is establishing `compose_single_admissible` for GEMM-specific layouts.

**Approach:**
1. Audit `gemm.rs` and `proof/gemm_lemmas.rs` for `compose_linear` / `logical_divide_linear` usage
2. Replace with `compose` / `logical_divide` where applicable
3. Prove `compose_single_admissible` for the specific tile shapes used in GEMM (typically column-major tiles dividing column-major matrices, where admissibility holds trivially)
4. Update `runtime/gemm.rs` exec functions to use the new `compose_exec` (once task #1 is done)
5. Verify the end-to-end correctness theorem `lemma_gemm_e2e_correctness` still holds

**Key insight:** For column-major layouts (the common GEMM case), `compose` and `compose_linear` produce identical results. So the existing proofs should mostly work unchanged. The value is in EXTENDING correctness to non-column-major cases.

**Key files:**
- `gemm.rs` — spec definitions
- `proof/gemm_lemmas.rs` — 108 proof functions, most reference compose_linear
- `runtime/gemm.rs` — exec functions
- `verus-vulkan/src/gemm_dispatch.rs` — downstream consumer

**Estimated effort:** 2-3 sessions for mechanical rename + admissibility proofs

### 3. Tensor contraction proofs

**What:** Add proof lemmas for tensor contraction correctness. The spec (`contraction.rs`) and exec (`runtime/contraction.rs`) exist but have no proof module.

**Why:** Tensor contraction (Einstein summation) generalizes matrix multiplication. Proving its correctness would close a gap in the GEMM pipeline and enable verified general tensor operations.

**Difficulty:** Hard. Contraction involves summing over contracted indices, which requires reasoning about permutations and reductions simultaneously.

**Approach:**
1. Create `proof/contraction_lemmas.rs`
2. Start with the simplest case: matrix multiplication as a contraction (contract one index of a 2D x 2D → 2D tensor)
3. Prove: `contraction_output[i,j] == sum_k A[i,k] * B[k,j]` using the layout algebra
4. Key proof technique: use `lemma_delinearize_concat` to decompose the multi-index, then show the contraction sum equals the expected dot product

**Current contraction spec** (from contraction.rs):
- `ContractionSpec` has `input_layouts`, `output_layout`, `contracted_modes`
- The contraction pairs modes from different inputs and sums over them
- `runtime/contraction.rs` has `contraction_output_shape_exec` but no `contraction_exec`

**Key files:**
- `contraction.rs` — spec
- `runtime/contraction.rs` — exec (partial)
- New: `proof/contraction_lemmas.rs`

**Estimated effort:** 3-4 sessions

### 4. Multi-mode compose correctness

**What:** Prove `compose(A, B).offset(x) == A.offset(B.offset(x))` for multi-mode B, using the recursive compose.

**Why:** We proved `compose_single(A, N, r).offset(x) == A.offset(r*x)` for single-mode B. The multi-mode version distributes over B's modes. The missing piece is showing the sum of per-mode contributions equals `A.offset(B.offset(x))`.

**Difficulty:** Hard. This is the same offset-additivity challenge we faced with `compose_extended_correct`. The key difference: `compose_single` handles mode boundaries correctly, so the additivity should hold more broadly.

**Approach:**
Two possible strategies:

**Strategy A: Direct additivity proof**
Prove that for the specific B layouts produced by complement (used in logical_divide), A.offset is additive over the mode decomposition. This uses `lemma_offset_at_split_mode` to show each mode contribution addresses a distinct mode of A.

Preconditions: each B mode's stride is a prefix product of A's shape (or fits within A's first mode). Under these conditions, the contributions don't interfere.

**Strategy B: Use the existing `compose_extended_correct_at` framework**
The predicate `compose_extended_correct_at` captures offset additivity. We could prove that for `compose_single`-based composition, this predicate is satisfied when `compose_single_admissible` holds. Then the existing `lemma_compose_extended_correct` gives the multi-mode result.

This requires showing: `compose_single(A, N, r).offset(x) == A.offset(r*x)` implies the additivity condition for the recursive compose's output.

**Strategy C: Induction on B's rank (recommended)**
Follow the same structure as `lemma_compose_extended_correct` but using `compose_single` instead of `compose_single_mode_extended`. The proof is by induction on B's rank:
- Base: B has 0 modes → both sides 0
- Step: decompose B into first mode + rest, use `compose_single` correctness for first mode, IH for rest, and additivity for the combination

The additivity precondition can be: "A.offset(r*c + rest_offset) == A.offset(r*c) + A.offset(rest_offset)" when r*c and rest_offset address disjoint modes of A.

**Key insight:** The hardest part isn't the induction — it's proving the additivity condition. For the divide use case (zipped layout with identity offset), additivity follows from the delinearize decomposition of A. For the general case, it needs a careful characterization of when mode contributions are independent.

**Key files:**
- `proof/composition_lemmas.rs` — add `lemma_compose_correct` for the new compose
- Reuse: `lemma_compose_single_correct`, `lemma_crs_shape_valid`, `lemma_crs_len_match`, `lemma_crs_size`

**Estimated effort:** 2-3 sessions

### 5. Codegen layer (WGSL/PTX emission)

**What:** Add a proc macro layer that takes Rust functions using CuTe operations and emits GPU shader code (WGSL for WebGPU, PTX for CUDA).

**Why:** This is the bridge from "verified algebra" to "verified GPU kernels." The algebra proves tiling/partitioning is correct; codegen turns those proofs into actual GPU code.

**Difficulty:** Very Hard (but different kind — software engineering, not theorem proving).

**Approach:**
1. **Phase 1: WGSL string emission** (simplest backend)
   - Define a `#[kernel]` proc macro attribute
   - Parse the function body for CuTe operations (layout.offset, compose, divide, etc.)
   - Emit WGSL compute shader source with the index arithmetic inlined
   - Shared memory → `var<workgroup>`, barriers → `workgroupBarrier()`

2. **Phase 2: Intrinsic axiomatization**
   - Add `#[verifier::external_body]` functions for GPU operations: `global_load`, `shared_store`, `mma_sync`, `barrier`
   - Each has `ensures` clauses matching the spec-level operation
   - Property-based testing validates the ensures against CPU reference

3. **Phase 3: Per-kernel verification**
   - Write a verified GEMM kernel using the intrinsics
   - The proof uses layout algebra lemmas to establish:
     - Thread-to-element mapping is bijective (no missed/redundant work)
     - Shared memory indexing is in-bounds
     - The accumulation loop computes the correct matrix product
   - Codegen emits the shader; Verus verifies the coordination logic

**Trust boundary:**
- VERIFIED: Layout algebra, kernel coordination, functional correctness
- TRUSTED: Proc macro codegen, WGSL compiler, GPU hardware
- TESTED: Intrinsic specs (property-based testing vs CPU reference)

**Key files:**
- New crate: `verus-cutedsl-codegen/` (proc macro crate)
- New in verus-cutedsl: `intrinsics.rs` for external_body GPU operations
- New in verus-vulkan: kernel implementations using the codegen

**Estimated effort:** 5+ sessions for Phase 1, ongoing for Phases 2-3

---

## Dependency order

```
#1 (compose_exec) ← independent, start immediately
#4 (multi-mode compose proof) ← independent, start immediately
#2 (GEMM update) ← depends on #1 (needs runtime compose_exec)
#3 (contraction proofs) ← independent but benefits from #4
#5 (codegen) ← depends on #1 and #2 (needs working runtime)
```

**Recommended order:** Start #1 and #4 in parallel, then #2, then #3 and #5.

---

## Crate statistics

- **Spec functions:** ~400
- **Proof functions:** ~800
- **Exec functions:** ~180
- **Types:** 11 types, 1 trait
- **Total rlimit:** ~63M (optimized from ~66M)
- **Hot functions:** left_inverse_exec (3.1M), coalesce_pair_offset_general (2.9M), right_inverse_build_correct (2.2M)
- **External body functions:** 4 (bxor, shr, shl, band_mask) — all with verified ensures
