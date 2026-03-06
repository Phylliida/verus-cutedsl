# verus-cutedsl Design Document

## 1. Overview

verus-cutedsl is a Verus crate that formalizes NVIDIA CuTe's layout algebra and verifies
its key properties. A layout is a function from logical coordinates to memory offsets,
defined by a shape (extents per dimension) and stride (offset jumps per dimension). CuTe's
operations on layouts -- composition, complement, logical divide, logical product -- form a
closed algebra that governs every data movement in a GPU kernel: tiling, partitioning across
threads, shared memory addressing, and tensor core operand layout.

The thesis is that this algebra, being pure integer arithmetic with no pointers or mutation,
is an ideal verification target for Verus/Z3. By proving bounds safety, bijectivity, and
tiling decomposition at the layout level, we can establish per-kernel correctness properties
(no out-of-bounds access, complete coverage, no redundant work) that compose from verified
building blocks rather than requiring monolithic per-kernel proofs.

The crate follows verus-cad's three-layer pattern:
- **Spec layer**: Pure mathematical definitions using `Seq<nat>` and `int`. These are the
  statements we prove things about.
- **Proof layer**: Verus lemmas establishing the algebraic properties. These are the verified
  theorems.
- **Exec layer**: Runtime types (`RuntimeLayout`) with `Ghost<LayoutSpec>` models, `View`
  impls, and `wf_spec()` predicates, following the same pattern as `RuntimeVec2`, `RuntimeRational`,
  etc. These let verified code actually compute layout offsets.

GPU codegen (proc macros, WGSL emission, TVM lowering) is a future layer that consumes the
verified algebra. It is explicitly out of scope for v0.1 but the algebra is designed with
codegen in mind.

---

## 2. Mathematical Foundations

This section defines the layout algebra precisely. All definitions here become Verus spec
functions. The notation follows Jay Shah's formalization and NVIDIA's official documentation.

### 2.1 Shapes

A **shape** is a sequence of positive natural numbers representing extents per dimension:

```
S = (M_0, M_1, ..., M_{k-1})    where M_i > 0 for all i
```

The **size** of a shape is the product of its extents:

```
size(S) = M_0 * M_1 * ... * M_{k-1}
```

The **rank** of a shape is its length k.

In Verus:
```rust
pub open spec fn shape_valid(s: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] > 0
}

pub open spec fn shape_size(s: Seq<nat>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 1 }
    else { s[0] * shape_size(s.skip(1)) }
}
```

### 2.2 Delinearization (Mixed-Radix Decomposition)

Given a linear index `x` in `[0, size(S))`, **delinearization** decomposes it into
per-dimension coordinates via iterated division:

```
coords(x, S) = (x mod M_0,  floor(x/M_0) mod M_1,  ...,  floor(x/(M_0*...*M_{k-2})) mod M_{k-1})
```

This is the standard mixed-radix number system. The key property is that it's a bijection
between `[0, size(S))` and the cartesian product `[0,M_0) x [0,M_1) x ... x [0,M_{k-1})`.

In Verus:
```rust
pub open spec fn delinearize(idx: nat, shape: Seq<nat>) -> Seq<nat>
    recommends shape_valid(shape), idx < shape_size(shape),
    decreases shape.len(),
{
    if shape.len() == 0 { seq![] }
    else {
        seq![idx % shape[0]].add(delinearize(idx / shape[0], shape.skip(1)))
    }
}

pub open spec fn linearize(coords: Seq<nat>, shape: Seq<nat>) -> nat
    recommends coords.len() == shape.len(),
    decreases shape.len(),
{
    if shape.len() == 0 { 0 }
    else {
        coords[0] + shape[0] * linearize(coords.skip(1), shape.skip(1))
    }
}
```

**Verified properties:**
- Roundtrip: `linearize(delinearize(x, S), S) == x` for `x < size(S)`
- Inverse roundtrip: `delinearize(linearize(c, S), S) == c` for in-bounds `c`
- Coordinate bounds: `delinearize(x, S)[i] < S[i]` for all `i`

### 2.3 Layouts

A **layout** is a pair `(S, D)` where `S` is a shape and `D` is a stride sequence of the
same length. It defines a function from `[0, size(S))` to integers:

```
L(x) = dot(delinearize(x, S), D) = sum_i coords_i * D_i
```

In Verus:
```rust
pub struct LayoutSpec {
    pub shape: Seq<nat>,
    pub stride: Seq<int>,
}

impl LayoutSpec {
    pub open spec fn valid(&self) -> bool {
        &&& shape_valid(self.shape)
        &&& self.shape.len() == self.stride.len()
    }

    pub open spec fn size(&self) -> nat {
        shape_size(self.shape)
    }

    pub open spec fn rank(&self) -> nat {
        self.shape.len()
    }

    pub open spec fn offset(&self, idx: nat) -> int
        recommends self.valid(), idx < self.size(),
    {
        let coords = delinearize(idx, self.shape);
        dot_product(coords, self.stride)
    }
}
```

### 2.4 Cosize

The **cosize** of a layout is the maximum offset plus one (the minimum codomain size needed):

```
cosize(L) = sum_i (M_i - 1) * |D_i| + 1      (for non-negative strides)
cosize(L) = max_{x < size(L)} L(x) + 1        (general definition)
```

For layouts with non-negative strides (the common case in GPU kernels), the closed-form
`sum_i (M_i - 1) * D_i + 1` holds because the maximum is achieved by maximizing each
coordinate independently.

### 2.5 Sortedness and Tractability

A layout is **sorted** if its strides are non-decreasing: `D_0 <= D_1 <= ... <= D_{k-1}`.

A layout is **tractable** (well-behaved for complement) if for each adjacent pair of modes,
the stride gap is divisible:

```
tractable(L) <==> for all 0 < i < k: (M_{i-1} * D_{i-1}) divides D_i
```

Tractability ensures the modes tile the codomain without gaps or overlaps within each
"column" of the mixed-radix decomposition. It is the admissibility condition for complement.

### 2.6 Composition

**Composition** `A compose B` produces a layout whose offset function is `A(B(x))`.

For `A = (S_A, D_A)` and a single-mode `B = (N):(r)`:
1. Find the split index `i` such that `r = M_0 * ... * M_{i-1} * c` where `c | M_i`
2. The result shape slices through A's modes starting at the split point

For multi-mode B, composition distributes: `A compose (B_0, B_1, ...) = (A compose B_0, A compose B_1, ...)`

The key verified property:

```
(A compose B)(x) == A(B(x))    for all x < size(B)
```

This is the fundamental correctness theorem for composition: the algebraic construction
on shape/stride pairs produces the same result as functional composition.

### 2.7 Complement

The **complement** of layout A with respect to a target size M produces a layout R
that covers exactly the offsets A misses:

Given sorted `A = (M_0, ..., M_k):(d_0, ..., d_k)` with tractability condition:

```
complement(A, M) = (d_0, d_1/(M_0*d_0), ..., M/(M_k*d_k)) : (1, M_0*d_0, ..., M_k*d_k)
```

**Verified properties:**
- **Size**: `size(complement(A, M)) == M / size(A)`
- **Disjointness**: For `0 < x < size(A)` and `0 < y < size(R)`: `A(x) != R(y)` (modulo the shared origin)
- **Completeness**: The union `{A(x) | x in [0,size(A))} union {R(y) | y in [0,size(R))}` covers `[0, M)`
- **Ordered**: complement's strides are strictly increasing (the result is coalesced)

### 2.8 Logical Divide

**Logical divide** partitions a layout into a "tile" and a "rest":

```
logical_divide(A, B) = A compose (B, complement(B, size(A)))
```

The result is a 2-mode layout:
- Mode 0 (tile): has shape matching B, covers one tile's worth of elements
- Mode 1 (rest): iterates over tiles

**Verified property (tiling decomposition):**
Iterating over all (tile_coord, rest_coord) pairs visits every element of A exactly once:

```
for all x < size(A), there exist unique (t, r) with t < size(B), r < size(A)/size(B):
  A(x) == logical_divide(A, B)(t, r)
```

This is the central theorem that makes CuTe's tiling correct.

### 2.9 Logical Product

**Logical product** is the dual of division -- it builds a layout by replicating a pattern:

```
logical_product(A, B) = (A, B * cosize(A))
```

where `B * cosize(A)` scales B's strides by the cosize of A. This tiles space by placing
copies of A at offsets determined by B.

### 2.10 Coalesce

**Coalesce** merges adjacent modes whose strides are compatible (contiguous):

```
coalesce((M_i, M_{i+1}) : (d_i, d_{i+1})) =
    (M_i * M_{i+1}) : (d_i)    when d_{i+1} == M_i * d_i
```

This is an optimization that reduces rank without changing the layout function.

**Verified property:**
```
coalesce(L)(x) == L(x)    for all x < size(L)
```

### 2.11 Swizzle

**Swizzle** applies an XOR-based permutation to offsets, used to avoid shared memory bank
conflicts. A swizzle is parameterized by `(B, M, S)` -- base bits, mask bits, shift bits:

```
swizzle(offset, B, M, S) = offset XOR ((offset >> B) & mask(M) << S)
```

This is a self-inverse bijection on `[0, 2^{B+M+S})`. Verification focuses on the
bijectivity proof (swizzle composed with itself is identity).

---

## 3. Verification Targets

### 3.1 Layer 1: Layout Algebra (v0.1 scope)

These are the core theorems about layouts as mathematical objects. They are proved once
and used as building blocks for everything else.

| Property | Statement | Difficulty |
|----------|-----------|------------|
| Delinearize roundtrip | `linearize(delinearize(x, S), S) == x` | Easy (induction on rank) |
| Coordinate bounds | `delinearize(x, S)[i] < S[i]` | Easy |
| Offset bounds | `0 <= L(x) < cosize(L)` for non-neg strides | Medium |
| Composition correctness | `(A compose B)(x) == A(B(x))` | Hard (case split on mode boundaries) |
| Complement disjointness | Codomains of A and complement(A,M) intersect only at 0 | Hard |
| Complement completeness | Union of codomains covers [0,M) | Hard |
| Complement size | `size(complement(A,M)) == M / size(A)` | Medium |
| Division decomposition | logical_divide visits every element exactly once | Hard (follows from complement) |
| Coalesce equivalence | `coalesce(L)(x) == L(x)` | Medium |
| Swizzle involution | `swizzle(swizzle(x)) == x` | Easy (XOR self-inverse) |
| Swizzle bijectivity | swizzle is a bijection on its domain | Medium (follows from involution) |

### 3.2 Layer 2: Operation Specifications (future)

Once the layout algebra is verified, we can write specs for GPU operations:

- **Copy**: `copy(src, dst, tiled_copy)` ensures `dst[i] == src[i]` for all `i` in the
  tiled_copy's domain, using the tiled_copy's layout to describe which thread copies which element.
- **MMA**: `mma(A, B, C, tiled_mma)` ensures `C[i][j] == sum_k A[i][k] * B[k][j]` (using
  verus-algebra Ring trait for genericity).
- **Reduce**: `reduce(src, dst, op, axis)` ensures the reduction result matches the spec fold.

These would use `#[verifier::external_body]` with `ensures` clauses -- the GPU hardware
implements the operation, we axiomatize its behavior.

### 3.3 Layer 3: Kernel Correctness (future)

Per-kernel proofs compose Layer 1 and Layer 2:

```
// Example: verified tiled GEMM outline
fn gemm_kernel<T: Ring>(A: Tensor<T>, B: Tensor<T>, C: &mut Tensor<T>)
    requires
        A.layout.shape == seq![M, K],
        B.layout.shape == seq![K, N],
        C.layout.shape == seq![M, N],
    ensures
        forall|i, j| 0 <= i < M && 0 <= j < N ==>
            C@[i * N + j].eqv(dot_product_spec(A@, B@, i, j, K))
```

The proof would use layout algebra lemmas to show that the tiling covers all (i,j) pairs,
that shared memory indexing is in-bounds, and that the accumulation loop computes the
correct dot products.

---

## 4. Crate Architecture

### 4.1 Dependency Position

```
verus-algebra  (Ring, OrderedRing traits -- needed for Tensor<T: Ring>)
  |
  v
verus-cutedsl  (layout algebra over nat/int, Tensor<T: Ring> specs)
```

verus-cutedsl depends on verus-algebra only for the `Ring` trait bound on tensor element
types. The layout algebra itself (shape, stride, offset, composition, complement, divide)
is pure `nat`/`int` arithmetic with no trait generics.

For the runtime layer (Phase 3+), verus-cutedsl would additionally depend on:
- `vstd` (always)
- `verus-algebra` (for Ring trait)

It does NOT depend on verus-linalg, verus-geometry, verus-rational, or verus-bigint.
The layout algebra is a new mathematical domain orthogonal to the geometric algebra stack.

### 4.2 Module Structure

```
verus-cutedsl/
  Cargo.toml
  docs/
    design.md              # this document
  src/
    lib.rs                 # crate root, re-exports

    # --- Spec layer (gated behind verus_keep_ghost) ---
    shape.rs               # Shape: Seq<nat>, size, delinearize, linearize
    layout.rs              # LayoutSpec, offset, cosize, valid
    coalesce.rs            # coalesce operation
    composition.rs         # layout composition A compose B
    complement.rs          # complement(A, M)
    divide.rs              # logical_divide, zipped_divide
    product.rs             # logical_product
    swizzle.rs             # XOR-based swizzle

    # --- Proof layer (gated behind verus_keep_ghost) ---
    proof/
      mod.rs
      shape_lemmas.rs      # delinearize/linearize roundtrip, coordinate bounds
      offset_lemmas.rs     # offset bounds, cosize correctness
      composition_lemmas.rs
      complement_lemmas.rs # disjointness, completeness, size
      divide_lemmas.rs     # tiling decomposition
      coalesce_lemmas.rs
      swizzle_lemmas.rs    # involution, bijectivity
      integer_helpers.rs   # div/mod identities, divisibility chains

    # --- Tensor spec layer (gated behind verus_keep_ghost) ---
    tensor.rs              # TensorSpec<T: Ring> = Seq<T> + LayoutSpec

    # --- Exec/runtime layer (always compiled) ---
    runtime/
      mod.rs
      layout.rs            # RuntimeLayout { shape: Vec<usize>, stride: Vec<isize>,
                           #                  model: Ghost<LayoutSpec> }
      tensor.rs            # RuntimeTensor<T> (future, when we have exec element types)
```

### 4.3 Spec Layer Details

All spec modules are gated behind `#[cfg(verus_keep_ghost)]` following verus-cad convention.
They define pure mathematical objects using `Seq<nat>` and `int`.

Key design choice: **flat representation**. Layouts are `(Seq<nat>, Seq<int>)` pairs, not
type-level hierarchical tuples. Reasons:

1. Z3 handles `Seq` with quantifier triggers well. Recursive algebraic datatypes (trees)
   generate more complex SMT terms and risk rlimit blowup.
2. The layout *function* (idx -> offset) doesn't depend on hierarchical structure. Hierarchy
   is metadata about how modes are grouped, not about the mathematical mapping.
3. verus-cad's existing patterns use `Seq` throughout (mesh half-edges, polygon vertices,
   gui widget children). This is proven to work at scale.

For operations that produce hierarchical results (logical_divide returns a 2-level layout),
we represent the output as a flat layout plus **mode boundaries** -- a `Seq<nat>` indicating
where each logical mode starts in the flat representation.

```rust
pub struct DividedLayout {
    pub layout: LayoutSpec,       // flat layout with all modes
    pub tile_modes: nat,          // first tile_modes modes are the "tile"
                                  // remaining modes are the "rest"
}
```

### 4.4 Proof Layer Details

Proofs are organized by operation, one module per algebraic operation. Each module contains
lemmas that establish the properties listed in Section 3.1.

The proof layer depends heavily on integer arithmetic lemmas. Some exist in vstd
(`vstd::arithmetic::div_mod`), but we'll likely need custom helpers for:

- Mixed-radix decomposition properties (div/mod chains)
- Divisibility preservation through composition
- Stride arithmetic (products of extents * strides)

These go in `integer_helpers.rs` and are analogous to verus-algebra's `ring_lemmas.rs` --
a library of reusable proof building blocks.

Expected proof difficulty pattern from verus-cad experience:
- Shape/delinearize lemmas: straightforward induction, low rlimit
- Offset bounds: medium, needs careful stride sign handling
- Composition: hardest -- the mode-boundary case split generates many paths. Will need
  helper extraction to keep rlimit manageable (same pattern as verus-topology's
  construction_proofs.rs)
- Complement: hard -- disjointness requires reasoning about the "gap filling" structure.
  Completeness may need a counting argument (pigeonhole)

### 4.5 Exec Layer Details

The runtime layer follows verus-cad's `RuntimeX` pattern exactly:

```rust
pub struct RuntimeLayout {
    pub shape: Vec<usize>,
    pub stride: Vec<isize>,
    pub model: Ghost<LayoutSpec>,
}

impl View for RuntimeLayout {
    type V = LayoutSpec;
    open spec fn view(&self) -> LayoutSpec { self.model@ }
}

impl RuntimeLayout {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self@.valid()
        &&& self.shape@.len() == self@.shape.len()
        &&& self.stride@.len() == self@.stride.len()
        &&& forall|i: int| 0 <= i < self.shape@.len() as int ==>
                self.shape@[i] as nat == self@.shape[i]
        &&& forall|i: int| 0 <= i < self.stride@.len() as int ==>
                self.stride@[i] as int == self@.stride[i]
    }

    pub fn offset(&self, idx: usize) -> (out: isize)
        requires self.wf_spec(), (idx as nat) < self@.size(),
        ensures out as int == self@.offset(idx as nat),
    {
        // exec implementation: delinearize then dot product
        // or direct iterative computation
    }

    pub fn size(&self) -> (out: usize)
        requires self.wf_spec(),
        ensures out as nat == self@.size(),
    {
        // product of shape elements
    }
}
```

---

## 5. Representation Decisions

### 5.1 Why Seq<nat> Over Type-Level Hierarchies

CuTe C++ encodes layout structure at the type level using variadic templates. This enables
zero-cost abstraction (all index math is compile-time constant). A Rust port could use const
generics or recursive tuple types.

We choose `Seq<nat>` for the spec layer because:

1. **Verus/Z3 compatibility**: Type-level encoding would require trait-based recursion (the
   `Shape` trait with `impl Shape for (A, B) where A: Shape, B: Shape` pattern). Each level
   adds quantifier nesting. For hierarchical layouts with 3-4 levels of nesting (common in
   CuTe GEMM kernels), the SMT terms become large. `Seq<nat>` with index-based access
   generates flat quantifiers with clean triggers.

2. **Proof reuse**: A single `lemma_delinearize_roundtrip` works for all ranks. With type-level
   encoding, you'd need rank-specific lemma instances or a trait-based proof dispatching mechanism
   that Verus doesn't directly support.

3. **Dynamic rank support**: Some operations change rank (coalesce reduces it, composition can
   increase it). With type-level encoding, the return type depends on the input values, requiring
   dependent types. With `Seq`, rank is just `.len()`.

The runtime layer CAN use fixed-size arrays or const generics for performance-critical inner
loops (e.g., `[usize; 2]` for 2D layouts) while maintaining a `Ghost<LayoutSpec>` model
that uses the `Seq` representation. This is exactly the pattern verus-cad uses for
`RuntimeVec3 { x, y, z, model: Ghost<Vec3<Rational>> }` -- concrete fields for performance,
ghost model for proofs.

### 5.2 Integer Types

- **Spec layer**: `nat` for shapes (always positive), `int` for strides (can be negative for
  reverse iteration or transposition). The offset function returns `int`.
- **Exec layer**: `usize` for shapes, `isize` for strides. Overflow is handled by requiring
  `wf_spec()` which implicitly bounds all values to fit in machine words.
- **Bridging**: The `wf_spec()` predicate asserts `self.shape@[i] as nat == self@.shape[i]`
  etc., connecting the two representations.

### 5.3 Non-Negative Stride Convention

Most GPU layouts have non-negative strides (negative strides are rare, used only for
flipped/reversed access). We define operations assuming non-negative strides where it
simplifies proofs, and note where negative stride support would require additional work.

The complement operation specifically requires sorted non-negative strides for its
admissibility condition. Composition works with arbitrary strides.

---

## 6. Implementation Plan

### Phase 0: Shape Arithmetic (Week 1-2)

Foundation: shape representation, delinearization, linearization, and their roundtrip proofs.
This exercises the basic proof infrastructure and establishes the integer arithmetic helper
library.

**Deliverables:**
- `shape.rs`: `shape_valid`, `shape_size`, `delinearize`, `linearize`
- `proof/shape_lemmas.rs`: roundtrip, coordinate bounds, size positivity
- `proof/integer_helpers.rs`: div/mod identities needed by shape lemmas

**Key lemmas:**
```
lemma_delinearize_roundtrip(x, S):    linearize(delinearize(x, S), S) == x
lemma_linearize_roundtrip(c, S):      delinearize(linearize(c, S), S) == c
lemma_delinearize_bounds(x, S, i):    delinearize(x, S)[i] < S[i]
lemma_delinearize_len(x, S):          delinearize(x, S).len() == S.len()
```

### Phase 1: Layout Core (Weeks 3-4)

Layout type, offset computation, cosize, and basic properties.

**Deliverables:**
- `layout.rs`: `LayoutSpec`, `offset`, `cosize`, `valid`, `is_sorted`, `is_tractable`
- `proof/offset_lemmas.rs`: offset bounds, cosize correctness

**Key lemmas:**
```
lemma_offset_bounds(L, x):       0 <= L.offset(x) < L.cosize()
lemma_offset_zero(L):            L.offset(0) == 0   (for non-neg strides)
lemma_cosize_formula(L):         L.cosize() == sum_i (M_i - 1) * D_i + 1
```

### Phase 2: Coalesce (Week 5)

Mode merging, which simplifies layouts without changing their function.

**Deliverables:**
- `coalesce.rs`: `coalesce` spec function
- `proof/coalesce_lemmas.rs`: functional equivalence

**Key lemma:**
```
lemma_coalesce_equiv(L, x):      coalesce(L).offset(x) == L.offset(x)
```

### Phase 3: Composition (Weeks 6-8)

The hardest operation to verify. Start with the single-mode case, then generalize.

**Deliverables:**
- `composition.rs`: `compose_single_mode`, `compose` (multi-mode, distributing)
- `proof/composition_lemmas.rs`: correctness + admissibility

**Key lemma:**
```
lemma_compose_correct(A, B, x):  compose(A, B).offset(x) == A.offset(B.offset(x))
```

This proof requires:
1. Showing that the algebraic construction on shape/stride pairs produces coordinates that,
   when dotted with A's strides, give the same result as first computing B(x) then A(B(x)).
2. The divisibility conditions ensure clean mode boundaries.

Expected to require helper extraction for rlimit management. The single-mode case is the
core; multi-mode distributes over it.

### Phase 4: Complement (Weeks 9-11)

Complement and its properties. Depends on Phase 1 (offset bounds) and Phase 3 (composition,
since the proofs share integer arithmetic helpers).

**Deliverables:**
- `complement.rs`: `complement` spec function, admissibility predicate
- `proof/complement_lemmas.rs`: size, disjointness, completeness, ordering

**Key lemmas:**
```
lemma_complement_size(A, M):         size(complement(A, M)) == M / size(A)
lemma_complement_disjoint(A, M):     codomains disjoint (except origin)
lemma_complement_complete(A, M):     codomains union to [0, M)
lemma_complement_ordered(A, M):      complement strides are strictly increasing
```

The completeness proof is the hardest. Strategy: counting argument. Both layouts together
have `size(A) + M/size(A)` domain elements mapping to `M` codomain elements. With
disjointness established, a pigeonhole-style argument (or direct constructive proof via
the complement formula) gives completeness.

### Phase 5: Logical Divide (Week 12)

Once composition and complement are verified, logical divide falls out as their combination.

**Deliverables:**
- `divide.rs`: `logical_divide`, `zipped_divide`
- `proof/divide_lemmas.rs`: tiling decomposition

**Key lemma:**
```
lemma_divide_covers(A, B, x):
    exists unique (t, r): logical_divide(A, B).offset(t, r) == A.offset(x)
```

### Phase 6: Product + Swizzle (Week 13)

Logical product and XOR swizzle. Both are simpler than composition/complement.

**Deliverables:**
- `product.rs`: `logical_product`
- `swizzle.rs`: `swizzle`, parameterized by (B, M, S)
- `proof/swizzle_lemmas.rs`: involution, bijectivity

### Phase 7: Runtime Layer (Weeks 14-16)

Exec functions for all spec operations, following the RuntimeLayout pattern from Section 4.5.

**Deliverables:**
- `runtime/layout.rs`: `RuntimeLayout` with all exec operations
- `runtime/mod.rs`: helpers, type aliases

Each exec function ensures its result matches the spec-level operation:
```rust
pub fn compose(&self, other: &RuntimeLayout) -> (out: RuntimeLayout)
    requires self.wf_spec(), other.wf_spec(), /* admissibility */,
    ensures out.wf_spec(), out@ == compose_spec(self@, other@),
```

### Phase 8: Tensor Specs (future)

Spec-level tensor type pairing data (Seq<T>) with layout, and operation specifications.

### Phase 9: Codegen (future)

Proc macro layer for GPU kernel generation. See Section 7.

---

## 7. Future: GPU Codegen Architecture

This section outlines the eventual codegen layer. It is NOT part of v0.1 but informs
design decisions in the algebra layer.

### 7.1 Trust Boundary

```
VERIFIED (by Verus):
  - Layout algebra (this crate, Phases 0-7)
  - Kernel coordination logic (tiling, loop bounds, shared memory sizing)
  - Per-kernel functional correctness (output matches spec)

TRUSTED (axiomatized via #[verifier::external_body]):
  - GPU intrinsics (copy, MMA, barrier)
  - The proc macro's codegen (Rust AST -> WGSL/PTX)
  - WGSL compiler, PTX assembler, GPU hardware

TESTED (empirically validated):
  - Intrinsic specs (property-based testing against CPU reference)
  - Codegen correctness (snapshot tests + end-to-end tests)
```

### 7.2 Backend Strategy

**WebGPU (primary, simpler):** Direct WGSL string emission from a proc macro or build script.
No intermediate compiler. Layout offset computations become inline arithmetic in the shader.
Shared memory becomes `var<workgroup>`. Barriers become `workgroupBarrier()`.

**CUDA (secondary, higher performance):** Two options:
1. **CuTe C++ emission**: Generate C++ source using NVIDIA's CuTe headers, compile with nvcc.
   Simpler but ties to NVIDIA toolchain.
2. **TVM lowering**: Translate to TVM TensorIR for target-specific optimization. More complex
   but enables auto-scheduling and multi-target support.

Option 1 is recommended for initial CUDA support. TVM can be added later as an optimization
backend.

### 7.3 Proc Macro Design

The `#[kernel]` attribute macro would:
1. Parse the Rust function body containing CuTe operations
2. Leave `requires`/`ensures`/`proof` blocks intact for Verus (they compile to nothing under
   standard rustc via `#[cfg(verus_keep_ghost)]`)
3. Generate a companion module with the WGSL/C++ source and a dispatch function

The kernel body uses the same `RuntimeLayout` types that the runtime layer provides. The
proc macro recognizes patterns like `layout.offset(idx)` and emits the corresponding
shader arithmetic.

### 7.4 Intrinsic Axiomatization

GPU intrinsics use `#[verifier::external_body]` with `ensures`:

```rust
#[verifier::external_body]
pub fn global_load<T>(buf: &[T], layout: &RuntimeLayout, idx: usize) -> (out: T)
    requires
        layout.wf_spec(),
        (idx as nat) < layout@.size(),
        layout@.offset(idx as nat) < buf@.len(),
    ensures
        out == buf@[layout@.offset(idx as nat) as int],
{ unimplemented!() }  // body replaced by codegen
```

This is the same pattern as verus-cad's `RuntimeRational::add` -- the exec body is
irrelevant to verification, the `ensures` clause is what Verus reasons about.

---

## 8. Key Design Decisions

**Layout algebra is concrete integer arithmetic, not abstract algebra.** Unlike verus-cad's
geometry stack (which is generic over Ring/OrderedRing), the layout algebra operates on
`nat` and `int` directly. There's no need for abstract `eqv()` equivalence -- integer
equality is decidable and native to Z3. The `Ring` trait enters only at the tensor level
(for element type genericity in GEMM specs), not at the layout level.

**Flat Seq representation over type-level hierarchies.** See Section 5.1 for rationale.
The exec layer can use fixed-size types for performance while maintaining `Seq`-based ghost
models.

**Proofs first, codegen later.** The verified algebra is valuable independently of GPU
targeting. It can be used to validate hand-written kernels, generate verified test oracles,
or serve as a reference implementation. Codegen adds value but also adds a large unverified
TCB (the proc macro). Better to establish the verified foundation first.

**No `assume(false)` in the algebra layer.** All layout algebra proofs should be complete
(no proof debt). `#[verifier::external_body]` is used only for GPU intrinsics in the future
codegen layer, and each such use is documented and tested.

**Follow verus-cad patterns exactly.** Same `wf_spec()` pattern, same `Ghost<Model>` + `View`
bridging, same module organization (`proof/` subdirectory, `runtime/` subdirectory), same
`#[cfg(verus_keep_ghost)]` gating. No novel patterns unless forced by the domain.

---

## 9. Open Questions

**Q1: How to handle hierarchical mode grouping?**
CuTe's operations produce results with specific hierarchical structure (e.g., logical_divide
returns `((tile_modes), (rest_modes))`). Our flat `Seq` representation loses this grouping.
The `DividedLayout` struct (Section 4.3) recovers it via a mode boundary index. Is this
sufficient, or do we need a tree representation for some operations?

Current answer: start with flat + mode boundaries. Add tree representation only if proofs
become unwieldy without it.

**Q2: Negative strides?**
CuTe supports negative strides for reversed iteration. Our complement operation requires
non-negative sorted strides. Should we:
(a) Restrict to non-negative strides (covers 95% of GPU use cases)
(b) Support negative strides with a normalization step (sort + absolute value) before complement

Current answer: (a) for v0.1, extend to (b) if needed.

**Q3: Static vs dynamic rank?**
Should `RuntimeLayout` have a fixed rank (const generic `N`) or dynamic rank (`Vec<usize>`)?
Fixed rank enables stack allocation and loop unrolling. Dynamic rank is more flexible.

Current answer: dynamic rank (`Vec`) for v0.1 to match the spec layer. Add fixed-rank
specializations (`Layout2D`, `Layout3D`) as optimization in the runtime layer if profiling
shows it matters.

**Q4: What integer overflow model?**
Layout offsets can be large (e.g., a 4096x4096 matrix with stride 4096 has cosize ~16M).
Products of shapes can overflow `usize` on 32-bit targets. Do we:
(a) Require 64-bit targets
(b) Add overflow checks to `wf_spec()`
(c) Use `u64` regardless of platform

Current answer: (b) -- `wf_spec()` asserts that all intermediate products fit in `usize`.
This is checked at runtime when constructing a `RuntimeLayout` and verified by Verus to be
sufficient for all subsequent operations.

**Q5: Connection to verus-linalg?**
verus-linalg has `Vec2<T>`, `Mat2x2<T>`, etc. Should `TensorSpec` unify with these, or is
it a separate abstraction? A 2x2 matrix stored in a `Tensor<T>` with layout `(2,2):(1,2)`
should be relatable to `Mat2x2<T>`.

Current answer: keep them separate for now. Add conversion lemmas (TensorSpec <-> Mat/Vec)
as a future bridge module. The layout algebra is for arbitrary-rank tensors; verus-linalg's
types are for small fixed-size vectors and matrices used in geometric computation.
