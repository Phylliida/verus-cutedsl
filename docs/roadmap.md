# verus-cutedsl Roadmap

## Current State (168 verified, 0 assume, 4 external_body)

**Spec**: shape, layout (injectivity, surjectivity, bijectivity, column-major, identity), compose, complement, divide, product, coalesce, swizzle, slice, dice
**Proof**: round-trips, offset preservation (coalesce), element-wise compose, complement rank/size, divide rank/tiling, product rank/size/validity, swizzle involution, column-major injectivity/bijectivity, identity injectivity/bijectivity, compose correctness (rank-1 A), compose preserves injectivity, coalesce preserves injectivity, dot product scale, identity-offset implies bijective
**Runtime**: all ops fully verified (compose, complement, product, coalesce, offset, cosize, is_tractable, is_sorted, has_non_negative_strides, slice, dice)

## Phase 1: Injectivity (No-Aliasing Property)

The key safety property: distinct indices map to distinct offsets.

### 1a. Injectivity Spec ✅
- `LayoutSpec::is_injective() -> bool` — `forall i, j: i != j ==> offset(i) != offset(j)` ✅
- `LayoutSpec::offset_hit(k) -> bool` — existential helper for surjectivity ✅
- `LayoutSpec::is_surjective_upto(m: nat) -> bool` — `forall k < m: offset_hit(k)` ✅
- `LayoutSpec::is_bijective_upto(m: nat) -> bool` — injective + surjective ✅

### 1b. Injectivity of Standard Layouts ✅
- `lemma_column_major_injective(shape)` ✅ — stride = (1, M0, M0*M1, ...) is injective
- `lemma_column_major_bijective(shape)` ✅ — bijective onto [0, size)
- `lemma_identity_injective(m)` ✅ — (M):(1) is injective
- `lemma_identity_bijective(m)` ✅ — bijective onto [0, m)
- `lemma_row_major_injective(shape)` — stride = (..., M1*M2, M2, 1) is injective (deferred: complex proof)
- Helpers: `make_column_major`, `make_identity`, `column_major_strides`, `scale_strides_spec` ✅

### 1c. Injectivity Preservation (partial) ✅
- `lemma_compose_preserves_injectivity_1d_a(a, b)` ✅ — rank-1 A injective + B injective => A∘B injective
- `lemma_coalesce_preserves_injectivity(l)` ✅ — coalesce at position 0 preserves injectivity
- `lemma_identity_offset_implies_injective(l)` ✅ — general: identity-offset => injective
- `lemma_identity_offset_implies_bijective(l)` ✅ — general: identity-offset => bijective
- `lemma_complement_injective(a, m)` — complement is always injective (deferred)
- `lemma_divide_bijective(a, b)` — logical_divide is a bijective rearrangement (deferred)

### 1d. Runtime Injectivity Check
- `RuntimeLayout::is_injective() -> bool` — exec check (O(n²) pairwise or structural)

## Phase 2: Full Composition Correctness (partial) ✅

### 2a. Compose Correctness ✅
- `lemma_compose_correct_1d_a(a, b, x)` ✅ — `compose(a,b).offset(x) == a.offset(b.offset(x))` for rank-1 A, arbitrary B
- `lemma_compose_shape(a, b)` ✅ — `compose(a,b).shape =~= b.shape`
- Helpers: `lemma_offset_eq_layout`, `lemma_compose_stride_1d`, `lemma_compose_single_mode_stride_1d` ✅
- `lemma_compose_correct(a, b, x)` — general multi-mode A (deferred: complex)

### 2b. Composition Associativity
- `lemma_compose_associative(a, b, c)` — `compose(compose(a,b),c).offset(x) == compose(a,compose(b,c)).offset(x)` (deferred)

## Phase 3: Coalesce Correctness

### 3a. Full Coalesce Chain
- `coalesce(layout) -> LayoutSpec` — iteratively coalesce all adjacent coalesceable pairs
- `lemma_coalesce_offset(layout, idx)` — `coalesce(layout).offset(idx) == layout.offset(idx)` for all idx
- `lemma_coalesce_size(layout)` — `size(coalesce(layout)) == size(layout)`

### 3b. Remove Unit Modes
- `lemma_remove_unit_modes_offset(layout, idx)` — unit mode removal preserves offset
- `lemma_remove_unit_modes_size(layout)` — size preserved

### 3c. Runtime
- `coalesce_exec(layout) -> RuntimeLayout` — full coalesce chain (loop until stable)

## Phase 4: Division & Product Correctness

### 4a. Division Correctness
- `lemma_divide_size(a, b)` — `size(logical_divide(a,b)) == size(a)`
- `lemma_divide_offset(a, b, x)` — `logical_divide(a,b).offset(x) == a.offset(x)` (bijective rearrangement)
  - Depends on complement bijectivity (Phase 1c)

### 4b. Product Correctness
- `lemma_product_valid(a, b)` ✅ — logical_product is valid
- `lemma_product_offset(a, b, x)` — offset decomposition into A-part and B-part (deferred)
- `lemma_product_compatible(a, b)` — first modes compatible with A (deferred)

## Phase 5: Slice & Dice ✅

### 5a. Slice/Dice Spec ✅
- `slice_layout(layout, mode, coord) -> LayoutSpec` ✅ — fix coordinate in one mode, rank-1
- `slice_offset(layout, mode, coord) -> int` ✅ — constant offset from fixing the coordinate
- `dice_layout(layout, mode) -> LayoutSpec` ✅ — keep only one mode, rank-1

### 5b. Slice/Dice Proofs ✅
- `lemma_slice_rank`, `lemma_slice_shape_valid`, `lemma_slice_valid` ✅
- `lemma_slice_mode0`, `lemma_slice_last_mode` ✅
- `lemma_dice_rank`, `lemma_dice_valid`, `lemma_dice_size` ✅

### 5c. Runtime ✅
- `slice_exec(layout, mode, coord) -> (RuntimeLayout, i64)` ✅ — returns residual layout + constant offset
- `dice_exec(layout, mode) -> RuntimeLayout` ✅

## Phase 6: Flatten / Unflatten

### 6a. Flatten Spec
- `flatten(layout: LayoutSpec) -> LayoutSpec` — already flat (our layouts are non-hierarchical)
  - In CuTe, flatten removes nesting. Our `LayoutSpec` is already flat, so this is a no-op.
  - BUT: we could add hierarchical `HierLayout` if needed for tiled_divide/zipped_divide

### 6b. Group Modes
- `group_modes(layout, begin, end) -> LayoutSpec` — group a range of modes
  - This is structural: doesn't change offset, just groups modes
  - Useful for zipped_divide/tiled_divide output

## Phase 7: Inverse Operations

### 7a. Right Inverse
- `right_inverse(layout: LayoutSpec) -> LayoutSpec` — `compose(layout, right_inverse(layout)) == identity`
  - Requires surjective layout
  - Algorithm: coalesce, sort by stride, compute inverse strides

### 7b. Left Inverse
- `left_inverse(layout: LayoutSpec) -> LayoutSpec` — `compose(left_inverse(layout), layout) == identity`
  - Requires injective layout

### 7c. Proofs
- `lemma_right_inverse_correct(layout, x)` — `layout.offset(right_inverse(layout).offset(x)) == x`
- `lemma_left_inverse_correct(layout, x)` — `left_inverse(layout).offset(layout.offset(x)) == x`

### 7d. Runtime
- `right_inverse_exec(layout) -> RuntimeLayout`
- `left_inverse_exec(layout) -> RuntimeLayout`

## Phase 8: Zipped/Tiled Divide & Product

These are structural rearrangements of logical_divide/product outputs.

### 8a. Zipped Divide
- `zipped_divide(a, b) -> (LayoutSpec, LayoutSpec)` — tile modes + rest modes separated
  - Tile layout: first rank(B) modes from logical_divide
  - Rest layout: remaining modes

### 8b. Tiled Divide
- `tiled_divide(a, b) -> (LayoutSpec, LayoutSpec)` — similar but flattened differently

### 8c. Blocked/Raked Product
- `blocked_product(a, b)` — contiguous block distribution
- `raked_product(a, b)` — cyclic/interleaved distribution

## Phase 9: verus-vulkan Integration

- Use `RuntimeLayout` for GPU buffer access patterns
- Prove no-aliasing for tile assignments (thread safety)
- Map CuTe tiling hierarchy to Vulkan compute shader dispatches:
  - WorkGroup <-> Thread Block tile
  - Invocation <-> Thread partition
- Verified bounds checking: offset < buffer_size

## Phase 10: Tiling DSL

High-level API where users describe decompositions declaratively:

```rust
let tiled = tile(global_layout)
    .by(block_shape)       // logical_divide
    .at(block_coord)       // slice
    .partition(thread_layout)  // zipped_divide
    .at(thread_id);        // slice
```

Each step produces a verified `RuntimeLayout` with proof that:
- All offsets are in bounds
- No aliasing between different thread_ids
- Full coverage of the input

## Implementation Order

Priority by value × feasibility:

1. **Phase 1** (Injectivity) — highest value, moderate difficulty
2. **Phase 2** (Compose correctness) — needed by Phase 1c and 4
3. **Phase 4a** (Division correctness) — proves the tiling is valid
4. **Phase 5** (Slice/Dice) — enables practical tiling workflows
5. **Phase 3** (Coalesce correctness) — needed for inverses
6. **Phase 7** (Inverses) — nice-to-have, complex
7. **Phase 8** (Zipped/Tiled variants) — mostly structural
8. **Phase 6** (Flatten) — trivial for flat layouts
9. **Phase 9** (vulkan integration) — depends on 1-5
10. **Phase 10** (DSL) — depends on everything
