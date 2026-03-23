# verus-cutedsl

A formally verified implementation of NVIDIA CuTe's layout algebra in Rust + [Verus](https://github.com/verus-lang/verus).

**1383 verified functions, 0 errors, 0 assumes.**

## What is this?

CuTe (CUDA Templates) is NVIDIA's layout algebra for GPU kernel programming. It describes how logical tensor indices map to memory offsets through *layouts* — pairs of shape and stride sequences. Operations like composition, complement, and logical divide let you tile, partition, and rearrange data access patterns algebraically.

This crate formalizes that algebra in Verus and proves its key properties correct. Every theorem is machine-checked by Z3 with zero proof debt (`assume(false)`).

## Key verified theorems

### Composition correctness (CuTe-style recursive)
```
compose_single(A, N, r).offset(x) == A.offset(r * x)
```
The recursive composition correctly handles mode boundary crossings — when B's stride straddles multiple modes of A, it splits the result into multiple modes. This is the "correct" CuTe composition that the original `compose` (now `compose_linear`) couldn't do.

### Layout canonicality
```
offset_equivalent(L1, L2) ==> full_flatten(L1) == full_flatten(L2)
```
For sorted, tractable, fully-coalesced layouts with no unit modes: if two layouts compute the same offset function, they are structurally identical. Proved by induction on rank.

### Tiling decomposition
```
logical_divide(A, B).offset(x) == A.offset(x)
```
Dividing a layout by a tile preserves the offset function — every element maps to the same memory location before and after tiling.

### Product algebra
```
logical_product(logical_product(A, B), C).offset(x) == logical_product(A, logical_product(B, C)).offset(x)
```
Logical product is associative. Also: scalar identity (left and right), size/cosize decomposition, injectivity/surjectivity/bijectivity preservation.

### Inverse unification
```
left_inverse(L).offset(j) == right_inverse(L).offset(j)
```
For bijective, sorted, tractable layouts: left and right inverses agree pointwise.

### Scan algorithms
- **Blelloch exclusive scan**: `blelloch_result(data) == exclusive_scan(data)` (end-to-end correctness)
- **Brent-Kung inclusive scan**: `bk_result(data) == inclusive_scan(data)`
- **Multiblock scan**: three-phase correctness + decoupled lookback accumulate correctness
- **Radix sort**: `is_sorted(radix_sort(data))` (stable sort correctness)
- **Segmented scan**: segment boundary properties, decomposition within segments

### Flatten canonicality
```
flatten(flatten(L)) == flatten(L)
```
`flatten` (coalesce + remove units + coalesce) is idempotent and produces the canonical form.

## Architecture

```
verus-cutedsl/
  src/
    shape.rs              # Shapes, delinearize, linearize
    layout.rs             # LayoutSpec: offset, cosize, validity, injectivity, etc.
    composition.rs        # compose (CuTe recursive), compose_linear (legacy)
    complement.rs         # complement(A, M) — gap-filling layout
    divide.rs             # logical_divide, logical_divide_mode
    product.rs            # logical_product, raked_product, blocked_product
    coalesce.rs           # coalesce, flatten, flatten_partial
    inverse.rs            # right_inverse, left_inverse
    swizzle.rs            # XOR-based bank conflict avoidance
    scan*.rs              # Scan algorithm specs (Blelloch, Brent-Kung, multiblock, segmented)
    radix_sort.rs         # Radix sort spec

    proof/                # All verified lemmas (~800 proof functions)
      composition_lemmas.rs   # compose_single correctness, compose_extended, etc.
      divide_lemmas.rs        # Tiling decomposition proofs
      coalesce_lemmas.rs      # Flatten idempotence, canonicality
      complement_lemmas.rs    # Size, validity, tractability, injectivity
      product_lemmas.rs       # Associativity, identity, offset decomposition
      inverse_lemmas.rs       # Left/right inverse correctness, unification
      injectivity_lemmas.rs   # Compose preserves injectivity, column-major properties
      scan_*_lemmas.rs        # Algorithm correctness proofs
      integer_helpers.rs      # div/mod identities, modular scaling
      ...

    runtime/              # Exec-level implementations
      layout.rs           # RuntimeLayout with Ghost<LayoutSpec> model
      ops.rs              # compose_exec, flatten_exec, divide_mode_exec, etc.
      scan.rs             # Hillis-Steele, Blelloch, Brent-Kung exec
      scan_multiblock.rs  # Three-phase scan, compact, histogram, multi-split
      radix_sort.rs       # Full radix sort exec
      ...
```

## Naming conventions

| Name | Meaning |
|------|---------|
| `compose` | CuTe recursive composition (correct, handles mode boundaries) |
| `compose_linear` | Legacy first-mode-only composition (deprecated) |
| `compose_single` | Single-mode recursive composition building block |
| `logical_divide` | CuTe recursive divide (correct) |
| `logical_divide_linear` | Legacy divide using `compose_linear` (deprecated) |
| `logical_divide_mode` | Convenience: first-mode division without compose |
| `flatten` | Canonical form (idempotent: coalesce + remove units + coalesce) |
| `flatten_partial` | One-pass flatten (NOT idempotent, use `flatten` instead) |

## Key proof techniques

See `docs/design.md` for the mathematical foundations and [the rlimit guide](../docs/rlimit-optimization-guide.md) for proof engineering patterns. Key techniques discovered during development:

- **`return` per branch** isolates postcondition checking in multi-case proofs
- **`delinearize_concat` + `dot_product_append`** is the universal offset decomposition pattern
- **`lemma_offset_at_split_mode`** generalizes offset computation to arbitrary modes via prefix products
- **Modular scaling** (`a*(x%b) == (a*x)%(a*b)`) enables the straddle case proof
- **`by (compute_only)`** for concrete values (98% rlimit reduction on pow2 lemmas)

## Dependencies

- [Verus](https://github.com/verus-lang/verus) for verification
- [verus-algebra](../verus-algebra) for the `Ring` trait (used by scan algorithms)

## Consumers

- [verus-vulkan](../verus-vulkan) — GEMM dispatch and SM80 kernel verification
- [verus-ray-marching](../verus-ray-marching) — Compute dispatch layout specs
