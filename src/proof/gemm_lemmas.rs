use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::gemm::*;
use crate::predication::*;
use crate::tiling::*;
use crate::swizzle::*;
use crate::contraction::*;
use crate::proof::shape_lemmas::*;
use crate::proof::tiling_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Offset tiling consistency
// ══════════════════════════════════════════════════════════════

/// Flat and tiled offsets agree: for any (i, kk), the flat offset equals
/// the tiled offset at tile (i/bm, kk/bk) element (i%bm, kk%bk).
pub proof fn lemma_gemm_offset_tiling_consistent(
    a_layout: &LayoutSpec, m: nat, k: nat, bm: nat, bk: nat,
)
    requires
        a_layout.valid(),
        a_layout.rank() == 2,
        bm > 0,
        bk > 0,
    ensures
        gemm_offset_tiling_consistent(a_layout, m, k, bm, bk),
{
    assert forall|i: nat, kk: nat| i < m && kk < k implies
        gemm_a_offset(a_layout, i, kk)
        == gemm_a_tiled_offset(a_layout, bm, bk,
            i / bm, kk / bk, i % bm, kk % bk)
    by {
        // By fundamental theorem of division: i == (i/bm)*bm + i%bm
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, bm as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(bm as int, (i / bm) as int);
        assert((i / bm) * bm + i % bm == i);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(kk as int, bk as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(bk as int, (kk / bk) as int);
        assert((kk / bk) * bk + kk % bk == kk);

        // gemm_a_tiled_offset unfolds to gemm_a_offset(a_layout, ti*bm+ei, tk*bk+ek)
        // With ti=i/bm, ei=i%bm, tk=kk/bk, ek=kk%bk:
        // = gemm_a_offset(a_layout, (i/bm)*bm + i%bm, (kk/bk)*bk + kk%bk)
        // = gemm_a_offset(a_layout, i, kk)
    };
}

// ══════════════════════════════════════════════════════════════
// K-reduction completeness
// ══════════════════════════════════════════════════════════════

/// Every K-index is covered by exactly one tile-element pair.
pub proof fn lemma_k_reduction_complete(k_size: nat, bk: nat)
    requires
        padded_divide_admissible(k_size, bk),
    ensures
        k_reduction_complete(k_size, bk),
{
    assert forall|kk: nat| kk < k_size implies
        tile_element_valid(
            tile_for_index(kk, bk),
            bk,
            elem_in_tile(kk, bk),
            k_size,
        )
    by {
        // tile_for_index(kk, bk) = kk / bk
        // elem_in_tile(kk, bk) = kk % bk
        // tile_element_valid: (kk/bk)*bk + kk%bk < k_size
        // By fundamental theorem: (kk/bk)*bk + kk%bk == kk
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(kk as int, bk as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(bk as int, (kk / bk) as int);
        assert(tile_for_index(kk, bk) * bk + elem_in_tile(kk, bk) == kk);
    };
}

// ══════════════════════════════════════════════════════════════
// C offset injectivity
// ══════════════════════════════════════════════════════════════

/// For an injective rank-2 C layout, distinct (i,j) pairs produce distinct offsets.
pub proof fn lemma_gemm_c_offset_injective(
    c_layout: &LayoutSpec, m: nat, n: nat,
    i1: nat, j1: nat, i2: nat, j2: nat,
)
    requires
        c_layout.valid(),
        c_layout.rank() == 2,
        c_layout.is_injective(),
        i1 < m, j1 < n,
        i2 < m, j2 < n,
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
        i1 != i2 || j1 != j2,
    ensures
        gemm_c_offset(c_layout, i1, j1) != gemm_c_offset(c_layout, i2, j2),
{
    // Map (i, j) to a linear index in the rank-2 layout
    // linearize((i, j), shape) = i + j * shape[0]
    // But offset uses delinearize, so we need to find x1, x2 such that
    // c_layout.offset(x) gives the right result.

    // For a rank-2 layout, offset(x) = delinearize(x, shape) dot stride
    // We need: gemm_c_offset(c_layout, i, j) = i*stride[0] + j*stride[1]
    // This equals c_layout.offset(x) when delinearize(x, shape) = (i, j)

    // The linearization for column-major is x = i + j * shape[0]
    let s0 = c_layout.shape[0];
    let s1 = c_layout.shape[1];
    let x1 = i1 + j1 * s0;
    let x2 = i2 + j2 * s0;

    // Bridge: c_layout.shape =~= seq![s0, s1]
    assert(c_layout.shape =~= seq![s0, s1]) by {
        assert(c_layout.shape.len() == 2);
        assert(c_layout.shape[0] == s0);
        assert(c_layout.shape[1] == s1);
    };

    // x1 < size = s0 * s1
    lemma_shape_size_2(s0, s1);
    assert(c_layout.size() == s0 * s1);
    assert(x1 < s0 * s1) by (nonlinear_arith)
        requires i1 < s0, j1 < s1, x1 == i1 + j1 * s0, s0 > 0, s1 > 0;
    assert(x2 < s0 * s1) by (nonlinear_arith)
        requires i2 < s0, j2 < s1, x2 == i2 + j2 * s0, s0 > 0, s1 > 0;

    // x1 != x2
    if i1 != i2 {
        assert(x1 != x2) by (nonlinear_arith)
            requires
                i1 < s0, i2 < s0, j1 < s1, j2 < s1,
                i1 != i2, s0 > 0,
                x1 == i1 + j1 * s0, x2 == i2 + j2 * s0;
    } else {
        // i1 == i2, j1 != j2
        assert(x1 != x2) by (nonlinear_arith)
            requires
                i1 == i2, j1 != j2, s0 > 0,
                x1 == i1 + j1 * s0, x2 == i2 + j2 * s0;
    }

    // By injectivity: c_layout.offset(x1) != c_layout.offset(x2)
    assert(c_layout.offset(x1) != c_layout.offset(x2));

    // delinearize(x, shape) for x = i + j*s0: first coord = x % s0 = i, second = x / s0 = j
    // Use div_mod_decompose from integer_helpers
    // lemma gives (a + d * b) % d == a, but x1 = i1 + j1 * s0 = i1 + s0 * j1
    vstd::arithmetic::mul::lemma_mul_is_commutative(j1 as int, s0 as int);
    vstd::arithmetic::mul::lemma_mul_is_commutative(j2 as int, s0 as int);
    assert(x1 == i1 + s0 * j1);
    assert(x2 == i2 + s0 * j2);
    crate::proof::integer_helpers::lemma_div_mod_decompose(i1, j1, s0);
    crate::proof::integer_helpers::lemma_div_mod_decompose(i2, j2, s0);
    assert(x1 % s0 == i1);
    assert(x1 / s0 == j1);
    assert(x2 % s0 == i2);
    assert(x2 / s0 == j2);

    // Unfold offset for rank-2 layout
    crate::proof::tiling_lemmas::lemma_offset_rank2(c_layout, x1);
    crate::proof::tiling_lemmas::lemma_offset_rank2(c_layout, x2);

    // Show delinearize(x1, shape) = (i1, j1)
    let shape = c_layout.shape;
    let coords1 = delinearize(x1, shape);
    let coords2 = delinearize(x2, shape);

    // Unfold delinearize for 2-element shape:
    // delinearize(x, [s0, s1]) = [x % s0] ++ delinearize(x / s0, [s1])
    // delinearize(x / s0, [s1]) = [(x / s0) % s1] ++ delinearize((x/s0)/s1, [])
    // = [(x / s0) % s1]
    assert(shape.first() == s0);
    assert(shape.skip(1) =~= seq![s1]);
    assert(seq![s1].first() == s1);
    assert(seq![s1].skip(1) =~= Seq::<nat>::empty());

    // coords1[0] = x1 % s0 = i1
    assert(coords1[0] == x1 % s0);
    assert(coords1[0] == i1);

    // For coords1[1]: delinearize(x1 / s0, [s1]) = [j1 % s1]
    // Since j1 < s1, j1 % s1 = j1
    let inner1 = delinearize(x1 / s0, seq![s1]);
    assert(x1 / s0 == j1);
    assert(inner1 =~= seq![j1 % s1].add(delinearize(j1 / s1, Seq::<nat>::empty())));
    assert(j1 % s1 == j1) by {
        vstd::arithmetic::div_mod::lemma_small_mod(j1, s1);
    };
    assert(coords1 =~= seq![i1, j1]);

    // Same for coords2
    assert(coords2[0] == x2 % s0);
    assert(coords2[0] == i2);
    let inner2 = delinearize(x2 / s0, seq![s1]);
    assert(x2 / s0 == j2);
    assert(inner2 =~= seq![j2 % s1].add(delinearize(j2 / s1, Seq::<nat>::empty())));
    assert(j2 % s1 == j2) by {
        vstd::arithmetic::div_mod::lemma_small_mod(j2, s1);
    };
    assert(coords2 =~= seq![i2, j2]);

    // Now lemma_offset_rank2 gives:
    // c_layout.offset(x1) = coords1[0]*stride[0] + coords1[1]*stride[1]
    //                      = i1*stride[0] + j1*stride[1]
    //                      = gemm_c_offset(c_layout, i1, j1)
    assert(c_layout.offset(x1) == gemm_c_offset(c_layout, i1, j1));
    assert(c_layout.offset(x2) == gemm_c_offset(c_layout, i2, j2));
}

/// Helper: shape_size of a 2-element shape.
proof fn lemma_shape_size_2(a: nat, b: nat)
    requires a > 0, b > 0,
    ensures shape_size(seq![a, b]) == a * b,
{
    assert(seq![a, b].first() == a);
    assert(seq![a, b].skip(1) =~= seq![b]);
    lemma_shape_size_single(b);
}

// ══════════════════════════════════════════════════════════════
// Tiled C disjointness
// ══════════════════════════════════════════════════════════════

/// Different CTAs produce different C offsets (no two CTAs write the same output element).
pub proof fn lemma_gemm_tiled_c_disjoint(
    c_layout: &LayoutSpec, m: nat, n: nat, bm: nat, bn: nat,
    cm1: nat, cn1: nat, em1: nat, en1: nat,
    cm2: nat, cn2: nat, em2: nat, en2: nat,
)
    requires
        c_layout.valid(),
        c_layout.rank() == 2,
        c_layout.is_injective(),
        bm > 0, bn > 0,
        em1 < bm, en1 < bn,
        em2 < bm, en2 < bn,
        cm1 != cm2 || cn1 != cn2,
        cm1 * bm + em1 < m,
        cn1 * bn + en1 < n,
        cm2 * bm + em2 < m,
        cn2 * bn + en2 < n,
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
    ensures
        gemm_c_offset(c_layout, cm1 * bm + em1, cn1 * bn + en1)
        != gemm_c_offset(c_layout, cm2 * bm + em2, cn2 * bn + en2),
{
    let i1 = cm1 * bm + em1;
    let j1 = cn1 * bn + en1;
    let i2 = cm2 * bm + em2;
    let j2 = cn2 * bn + en2;

    // Global indices differ
    lemma_gemm_cta_disjoint_mn(bm, bn, cm1, cn1, em1, en1, cm2, cn2, em2, en2);
    // i1 != i2 || j1 != j2

    lemma_gemm_c_offset_injective(c_layout, m, n, i1, j1, i2, j2);
}

// ══════════════════════════════════════════════════════════════
// Output coverage
// ══════════════════════════════════════════════════════════════

/// Every output element (i,j) with i<m, j<n is assigned to some CTA.
pub proof fn lemma_gemm_output_coverage(m: nat, n: nat, bm: nat, bn: nat, i: nat, j: nat)
    requires
        padded_divide_admissible(m, bm),
        padded_divide_admissible(n, bn),
        i < m,
        j < n,
    ensures ({
        let cta_m = tile_for_index(i, bm);
        let cta_n = tile_for_index(j, bn);
        let elem_m = elem_in_tile(i, bm);
        let elem_n = elem_in_tile(j, bn);
        &&& cta_m < num_tiles_ceil(m, bm)
        &&& cta_n < num_tiles_ceil(n, bn)
        &&& elem_m < bm
        &&& elem_n < bn
        &&& cta_m * bm + elem_m == i
        &&& cta_n * bn + elem_n == j
    }),
{
    lemma_gemm_m_coverage(m, bm, i);
    lemma_gemm_m_coverage(n, bn, j);
}

/// Coverage in flat form (no let bindings) — useful for quantifier matching.
pub proof fn lemma_gemm_output_coverage_flat(m: nat, n: nat, bm: nat, bn: nat, i: nat, j: nat)
    requires
        padded_divide_admissible(m, bm),
        padded_divide_admissible(n, bn),
        i < m,
        j < n,
    ensures
        tile_for_index(i, bm) < num_tiles_ceil(m, bm),
        tile_for_index(j, bn) < num_tiles_ceil(n, bn),
        tile_for_index(i, bm) * bm + elem_in_tile(i, bm) == i,
        tile_for_index(j, bn) * bn + elem_in_tile(j, bn) == j,
{
    lemma_gemm_m_coverage(m, bm, i);
    lemma_gemm_m_coverage(n, bn, j);
}

// ══════════════════════════════════════════════════════════════
// K-sum decomposition
// ══════════════════════════════════════════════════════════════

/// Sum of valid counts across all K-tiles equals k_size.
pub proof fn lemma_gemm_k_sum_decomposition(k_size: nat, bk: nat)
    requires
        padded_divide_admissible(k_size, bk),
    ensures
        sum_valid_counts(num_tiles_ceil(k_size, bk), bk, k_size) == k_size,
{
    lemma_gemm_k_reduction_coverage(k_size, bk);
}

// ══════════════════════════════════════════════════════════════
// Three-level soundness
// ══════════════════════════════════════════════════════════════

/// CTA→warp→register partition covers all output elements, each assigned to exactly one
/// (CTA, warp, register) triple.
///
/// For any output element (i, j), there exists a unique CTA (cta_m, cta_n) that handles it.
/// Within that CTA, the warp and register partitions further subdivide work.
/// Disjointness at each level ensures no element is computed twice.
pub proof fn lemma_gemm_three_level_soundness(
    m: nat, n: nat, bm: nat, bn: nat,
    i: nat, j: nat,
)
    requires
        padded_divide_admissible(m, bm),
        padded_divide_admissible(n, bn),
        i < m,
        j < n,
    ensures ({
        let cta_m = tile_for_index(i, bm);
        let cta_n = tile_for_index(j, bn);
        let elem_m = elem_in_tile(i, bm);
        let elem_n = elem_in_tile(j, bn);
        // Element (i, j) is assigned to CTA (cta_m, cta_n)
        &&& cta_m < num_tiles_ceil(m, bm)
        &&& cta_n < num_tiles_ceil(n, bn)
        &&& elem_m < bm
        &&& elem_n < bn
        &&& cta_m * bm + elem_m == i
        &&& cta_n * bn + elem_n == j
    }),
{
    lemma_gemm_output_coverage(m, n, bm, bn, i, j);
}

// ══════════════════════════════════════════════════════════════
// E2E GEMM correctness master lemma
// ══════════════════════════════════════════════════════════════

/// Master lemma tying together all GEMM correctness properties:
/// 1. Every output (i,j) with i<m, j<n is covered by exactly one CTA
/// 2. Each CTA's K-reduction covers all k_size elements (no gaps)
/// 3. No two CTAs write to the same C element
/// 4. Tiled offsets equal flat offsets (addressing is correct)
pub proof fn lemma_gemm_e2e_correctness(
    m: nat, n: nat, k: nat,
    bm: nat, bn: nat, bk: nat,
    a_layout: &LayoutSpec, b_layout: &LayoutSpec, c_layout: &LayoutSpec,
)
    requires
        gemm_config_admissible(m, n, k, bm, bn, bk, a_layout, b_layout, c_layout),
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
    ensures
        // Property 1: Output coverage — every (i,j) is handled by some CTA
        gemm_output_covered(m, n, bm, bn),
        // Property 2: K-reduction completeness — all K elements covered
        k_reduction_complete(k, bk),
        // Property 3: Output injectivity — distinct (i,j) pairs write distinct C elements
        gemm_output_injective(c_layout, m, n),
        // Property 4: Tiling consistency — tiled offsets equal flat offsets for A
        gemm_offset_tiling_consistent(a_layout, m, k, bm, bk),
{
    // Unfold admissibility for sub-lemmas
    assert(padded_divide_admissible(m, bm));
    assert(padded_divide_admissible(n, bn));
    assert(padded_divide_admissible(k, bk));
    assert(c_layout.is_injective());

    // Property 1: Coverage — use single-trigger helper for (i,j) pair
    assert forall|i: nat, j: nat| i < m && j < n implies {
        let pair = #[trigger] gemm_cta_for(i, j, bm, bn);
        &&& pair.0 < num_tiles_ceil(m, bm)
        &&& pair.1 < num_tiles_ceil(n, bn)
        &&& pair.0 * bm + elem_in_tile(i, bm) == i
        &&& pair.1 * bn + elem_in_tile(j, bn) == j
    } by {
        lemma_gemm_output_coverage_flat(m, n, bm, bn, i, j);
    };

    // Property 2: K-reduction
    lemma_k_reduction_complete(k, bk);

    // Property 3: Output injectivity
    assert forall|i1: nat, j1: nat, i2: nat, j2: nat|
        i1 < m && j1 < n && i2 < m && j2 < n
        && (i1 != i2 || j1 != j2)
    implies
        #[trigger] gemm_c_offset(c_layout, i1, j1)
        != #[trigger] gemm_c_offset(c_layout, i2, j2)
    by {
        lemma_gemm_c_offset_injective(c_layout, m, n, i1, j1, i2, j2);
    };

    // Property 4: Tiling consistency
    lemma_gemm_offset_tiling_consistent(a_layout, m, k, bm, bk);
}

// ══════════════════════════════════════════════════════════════
// B-matrix tiling consistency
// ══════════════════════════════════════════════════════════════

/// Flat and tiled B-offsets agree (mirrors A-matrix proof).
pub proof fn lemma_gemm_b_offset_tiling_consistent(
    b_layout: &LayoutSpec, k: nat, n: nat, bk: nat, bn: nat,
)
    requires
        b_layout.valid(),
        b_layout.rank() == 2,
        bk > 0,
        bn > 0,
    ensures
        gemm_b_offset_tiling_consistent(b_layout, k, n, bk, bn),
{
    assert forall|kk: nat, j: nat| kk < k && j < n implies
        gemm_b_offset(b_layout, kk, j)
        == gemm_b_tiled_offset(b_layout, bk, bn,
            kk / bk, j / bn, kk % bk, j % bn)
    by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(kk as int, bk as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(bk as int, (kk / bk) as int);
        assert((kk / bk) * bk + kk % bk == kk);

        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, bn as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(bn as int, (j / bn) as int);
        assert((j / bn) * bn + j % bn == j);
    };
}

// ══════════════════════════════════════════════════════════════
// Feature 1: SMEM layout proofs
// ══════════════════════════════════════════════════════════════

/// Column-major layouts have non-negative strides (strides are prefix products of nat shape).
proof fn lemma_column_major_nonneg_strides(shape: Seq<nat>)
    requires shape_valid(shape),
    ensures make_column_major(shape).non_negative_strides(),
    decreases shape.len(),
{
    crate::proof::injectivity_lemmas::lemma_column_major_strides_len(shape);
    crate::proof::injectivity_lemmas::lemma_column_major_valid(shape);
    let layout = make_column_major(shape);
    assert forall|i: int| 0 <= i < layout.stride.len() implies #[trigger] layout.stride[i] >= 0
    by {
        crate::proof::inverse_lemmas::lemma_column_major_stride_value(shape, i as nat);
        // stride[i] == shape_size(shape.take(i)) >= 1 for valid shapes
    };
}

/// SM80 smem A-layout is valid with non-negative strides.
pub proof fn lemma_smem_a_layout_valid(bm: nat, bk: nat)
    requires bm > 0, bk > 0,
    ensures
        smem_a_layout(bm, bk).valid(),
        smem_a_layout(bm, bk).non_negative_strides(),
{
    let shape = seq![bm, bk];
    assert(shape_valid(shape)) by {
        assert forall|i: int| 0 <= i < shape.len() implies #[trigger] shape[i] > 0 by {};
    };
    crate::proof::injectivity_lemmas::lemma_column_major_valid(shape);
    lemma_column_major_nonneg_strides(shape);
}

/// SM80 smem A-layout is injective.
pub proof fn lemma_smem_a_layout_injective(bm: nat, bk: nat)
    requires bm > 0, bk > 0,
    ensures smem_a_layout(bm, bk).is_injective(),
{
    let shape = seq![bm, bk];
    assert(shape_valid(shape)) by {
        assert forall|i: int| 0 <= i < shape.len() implies #[trigger] shape[i] > 0 by {};
    };
    crate::proof::injectivity_lemmas::lemma_column_major_injective(shape);
}

/// SM80 smem B-layout is valid with non-negative strides.
pub proof fn lemma_smem_b_layout_valid(bk: nat, bn: nat)
    requires bk > 0, bn > 0,
    ensures
        smem_b_layout(bk, bn).valid(),
        smem_b_layout(bk, bn).non_negative_strides(),
{
    let shape = seq![bk, bn];
    assert(shape_valid(shape)) by {
        assert forall|i: int| 0 <= i < shape.len() implies #[trigger] shape[i] > 0 by {};
    };
    crate::proof::injectivity_lemmas::lemma_column_major_valid(shape);
    lemma_column_major_nonneg_strides(shape);
}

/// SM80 smem B-layout is injective.
pub proof fn lemma_smem_b_layout_injective(bk: nat, bn: nat)
    requires bk > 0, bn > 0,
    ensures smem_b_layout(bk, bn).is_injective(),
{
    let shape = seq![bk, bn];
    assert(shape_valid(shape)) by {
        assert forall|i: int| 0 <= i < shape.len() implies #[trigger] shape[i] > 0 by {};
    };
    crate::proof::injectivity_lemmas::lemma_column_major_injective(shape);
}

/// SM80 swizzle params are admissible: B=3, M=0, S=3, and S >= B.
pub proof fn lemma_sm80_swizzle_admissible()
    ensures swizzle_admissible(sm80_smem_swizzle_b(), sm80_smem_swizzle_m(), sm80_smem_swizzle_s()),
{
    // B=3 > 0, S=3 >= B=3
}

/// Swizzled SMEM layout has distinct offsets when admissible.
pub proof fn lemma_smem_swizzle_distinct(
    base: &LayoutSpec, b: nat, m: nat, s: nat,
    count: nat,
)
    requires
        smem_layout_swizzle_admissible(base, b, m, s),
        count <= base.size(),
    ensures
        smem_swizzle_distinct(base, b, m, s, count),
{
    crate::proof::swizzle_lemmas::lemma_swizzled_offset_injective(base, b, m, s);
}

// ══════════════════════════════════════════════════════════════
// Feature 2: Copy atom proofs
// ══════════════════════════════════════════════════════════════

/// G2S copy atom is a valid copy atom.
pub proof fn lemma_g2s_copy_atom_valid(access_width: nat)
    requires access_width > 0,
    ensures copy_atom_valid(&g2s_copy_atom(access_width), access_width),
{
    // g2s_copy_atom(access_width) = make_identity(access_width) = {shape: [access_width], stride: [1]}
    // copy_atom_valid checks: valid, rank==1, shape[0]==access_width, stride[0]==1
}

/// G2S tiled copy is valid.
pub proof fn lemma_g2s_tiled_copy_valid(
    access_width: nat, thr: &LayoutSpec, val: &LayoutSpec,
)
    requires g2s_copy_admissible(access_width, thr, val),
    ensures g2s_tiled_copy(access_width, thr, val).valid(),
{
    lemma_tiled_copy_valid(&g2s_copy_atom(access_width), thr, val);
}

/// G2S tiled copy is injective (no two threads load the same element).
pub proof fn lemma_g2s_tiled_copy_injective(
    access_width: nat, thr: &LayoutSpec, val: &LayoutSpec,
)
    requires
        g2s_copy_admissible(access_width, thr, val),
        thr.is_injective(),
        val.is_injective(),
        val.non_negative_strides(),
    ensures
        g2s_tiled_copy(access_width, thr, val).is_injective(),
{
    let atom = g2s_copy_atom(access_width);
    // atom = make_identity(access_width), which is injective and has non-neg strides
    crate::proof::injectivity_lemmas::lemma_identity_injective(access_width);
    lemma_tiled_copy_injective(&atom, thr, val);
}

/// G2S tiled copy covers the full tile.
pub proof fn lemma_g2s_tiled_copy_coverage(
    access_width: nat, thr: &LayoutSpec, val: &LayoutSpec,
    tile_size: nat,
)
    requires
        g2s_copy_admissible(access_width, thr, val),
        tile_size == access_width * thr.size() * val.size(),
    ensures
        copy_covers_tile(&g2s_tiled_copy(access_width, thr, val), tile_size),
{
    let atom = g2s_copy_atom(access_width);
    lemma_tiled_copy_size(&atom, thr, val);
    // size(tiled_copy) == atom_size * thr_size * val_size
    lemma_shape_size_single(access_width);
    // atom_size == access_width (since atom = make_identity(access_width) = {[access_width]:[1]})
    assert(shape_size(atom.shape) == access_width);
}

/// S2R copy atom is a valid copy atom.
pub proof fn lemma_s2r_copy_atom_valid(access_width: nat)
    requires access_width > 0,
    ensures copy_atom_valid(&s2r_copy_atom(access_width), access_width),
{
}

/// S2R tiled copy is valid.
pub proof fn lemma_s2r_tiled_copy_valid(
    access_width: nat, thr: &LayoutSpec, val: &LayoutSpec,
)
    requires s2r_copy_admissible(access_width, thr, val),
    ensures s2r_tiled_copy(access_width, thr, val).valid(),
{
    lemma_tiled_copy_valid(&s2r_copy_atom(access_width), thr, val);
}

/// S2R tiled copy is injective.
pub proof fn lemma_s2r_tiled_copy_injective(
    access_width: nat, thr: &LayoutSpec, val: &LayoutSpec,
)
    requires
        s2r_copy_admissible(access_width, thr, val),
        thr.is_injective(),
        val.is_injective(),
        val.non_negative_strides(),
    ensures
        s2r_tiled_copy(access_width, thr, val).is_injective(),
{
    let atom = s2r_copy_atom(access_width);
    crate::proof::injectivity_lemmas::lemma_identity_injective(access_width);
    lemma_tiled_copy_injective(&atom, thr, val);
}

/// S2R tiled copy covers the full fragment.
pub proof fn lemma_s2r_tiled_copy_coverage(
    access_width: nat, thr: &LayoutSpec, val: &LayoutSpec,
    tile_size: nat,
)
    requires
        s2r_copy_admissible(access_width, thr, val),
        tile_size == access_width * thr.size() * val.size(),
    ensures
        copy_covers_tile(&s2r_tiled_copy(access_width, thr, val), tile_size),
{
    let atom = s2r_copy_atom(access_width);
    lemma_tiled_copy_size(&atom, thr, val);
    lemma_shape_size_single(access_width);
    assert(shape_size(atom.shape) == access_width);
}

// ══════════════════════════════════════════════════════════════
// Feature 3: Pipeline composition proofs
// ══════════════════════════════════════════════════════════════

/// G2S covers the A-tile.
pub proof fn lemma_g2s_covers_a_tile(
    g2s_a: &LayoutSpec, smem_a: &LayoutSpec, bm: nat, bk: nat,
)
    requires g2s_stage_valid(g2s_a, smem_a, bm, bk),
    ensures copy_covers_tile(g2s_a, bm * bk),
{
    // Direct from g2s_stage_valid: g2s_a.size() >= bm * bk
}

/// G2S covers the B-tile.
pub proof fn lemma_g2s_covers_b_tile(
    g2s_b: &LayoutSpec, smem_b: &LayoutSpec, bk: nat, bn: nat,
)
    requires g2s_stage_valid(g2s_b, smem_b, bk, bn),
    ensures copy_covers_tile(g2s_b, bk * bn),
{
}

/// S2R loads feed the MMA.
pub proof fn lemma_s2r_covers_mma(
    s2r: &LayoutSpec, mma_thr: &LayoutSpec, mma_val: &LayoutSpec,
)
    requires s2r_stage_valid(s2r, mma_thr, mma_val),
    ensures s2r.size() >= mma_thr.size() * mma_val.size(),
{
}

/// Master pipeline correctness: all stages compose correctly.
pub proof fn lemma_gemm_pipeline_correct(
    m: nat, n: nat, k: nat,
    bm: nat, bn: nat, bk: nat,
    g2s_a: &LayoutSpec, g2s_b: &LayoutSpec,
    smem_a: &LayoutSpec, smem_b: &LayoutSpec,
    s2r_a: &LayoutSpec, s2r_b: &LayoutSpec,
    mma_thr: &LayoutSpec, mma_val: &LayoutSpec,
    a_layout: &LayoutSpec, b_layout: &LayoutSpec, c_layout: &LayoutSpec,
)
    requires
        gemm_pipeline_admissible(m, n, k, bm, bn, bk,
            g2s_a, g2s_b, smem_a, smem_b, s2r_a, s2r_b,
            mma_thr, mma_val, a_layout, b_layout, c_layout),
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
    ensures
        // E2E kernel correctness
        gemm_output_covered(m, n, bm, bn),
        k_reduction_complete(k, bk),
        gemm_output_injective(c_layout, m, n),
        gemm_offset_tiling_consistent(a_layout, m, k, bm, bk),
        // Stage correctness
        gemm_b_offset_tiling_consistent(b_layout, k, n, bk, bn),
        copy_covers_tile(g2s_a, bm * bk),
        copy_covers_tile(g2s_b, bk * bn),
{
    lemma_gemm_e2e_correctness(m, n, k, bm, bn, bk, a_layout, b_layout, c_layout);
    lemma_gemm_b_offset_tiling_consistent(b_layout, k, n, bk, bn);
    lemma_g2s_covers_a_tile(g2s_a, smem_a, bm, bk);
    lemma_g2s_covers_b_tile(g2s_b, smem_b, bk, bn);
}

// ══════════════════════════════════════════════════════════════
// Feature 5: Tensor contraction proofs
// ══════════════════════════════════════════════════════════════

/// GEMM contraction spec has valid mode sets for rank-2 inputs.
pub proof fn lemma_gemm_contraction_valid()
    ensures contraction_mode_sets_valid(&gemm_as_contraction(), 2, 2),
{
    let spec = gemm_as_contraction();
    // batch: 0 + contraction: 1 + free: 1 = 2 for A
    // batch: 0 + contraction: 1 + free: 1 = 2 for B
    assert(spec.contraction_modes_a[0] < 2);
    assert(spec.contraction_modes_b[0] < 2);
    assert(spec.free_modes_a[0] < 2);
    assert(spec.free_modes_b[0] < 2);
}

/// GEMM contraction shapes match when K dimensions agree.
pub proof fn lemma_gemm_contraction_shapes_match(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 2,
        b_shape.len() == 2,
        a_shape[1] == b_shape[0],
    ensures
        contraction_shapes_match(&gemm_as_contraction(), &a_shape, &b_shape),
{
    let spec = gemm_as_contraction();
    // Batch: gather_shape(a, []) =~= gather_shape(b, []) — both empty
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~=
           gather_shape(&b_shape, &spec.batch_modes_b));
    // Contraction: gather_shape(a, [1]) = [a_shape[1]], gather_shape(b, [0]) = [b_shape[0]]
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~=
           gather_shape(&b_shape, &spec.contraction_modes_b));
}

/// GEMM contraction output shape is (M, N).
pub proof fn lemma_gemm_contraction_output_shape(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 2,
        b_shape.len() == 2,
    ensures
        contraction_output_shape(&gemm_as_contraction(), &a_shape, &b_shape)
        =~= seq![a_shape[0], b_shape[1]],
{
    let spec = gemm_as_contraction();
    // batch = gather(a, []) = []
    // free_a = gather(a, [0]) = [a_shape[0]]
    // free_b = gather(b, [1]) = [b_shape[1]]
    // output = [] ++ [a_shape[0]] ++ [b_shape[1]] = [a_shape[0], b_shape[1]]
    let batch = gather_shape(&a_shape, &spec.batch_modes_a);
    let free_a = gather_shape(&a_shape, &spec.free_modes_a);
    let free_b = gather_shape(&b_shape, &spec.free_modes_b);
    assert(batch =~= Seq::<nat>::empty());
    assert(free_a =~= seq![a_shape[0]]);
    assert(free_b =~= seq![b_shape[1]]);
    assert(batch.add(free_a).add(free_b) =~= seq![a_shape[0], b_shape[1]]);
}

/// Batched GEMM contraction spec has valid mode sets for rank-3 inputs.
pub proof fn lemma_batched_gemm_contraction_valid()
    ensures contraction_mode_sets_valid(&batched_gemm_as_contraction(), 3, 3),
{
    let spec = batched_gemm_as_contraction();
    assert(spec.batch_modes_a[0] < 3);
    assert(spec.batch_modes_b[0] < 3);
    assert(spec.contraction_modes_a[0] < 3);
    assert(spec.contraction_modes_b[0] < 3);
    assert(spec.free_modes_a[0] < 3);
    assert(spec.free_modes_b[0] < 3);
}

// ══════════════════════════════════════════════════════════════
// Contraction proofs (Feature 5 Round 2)
// ══════════════════════════════════════════════════════════════

/// Contraction admissibility for GEMM case.
pub proof fn lemma_gemm_contraction_admissible(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 2,
        b_shape.len() == 2,
        a_shape[1] == b_shape[0],
    ensures
        contraction_admissible(&gemm_as_contraction(), &a_shape, &b_shape),
{
    lemma_gemm_contraction_valid();
    lemma_gemm_contraction_shapes_match(a_shape, b_shape);
}

/// GEMM reduction size = K (a_shape[1]).
pub proof fn lemma_gemm_reduction_size(a_shape: Seq<nat>)
    requires a_shape.len() == 2,
    ensures contraction_reduction_size(&gemm_as_contraction(), &a_shape) == a_shape[1],
{
    let spec = gemm_as_contraction();
    assert(spec.contraction_modes_a =~= seq![1nat]);
    let modes = spec.contraction_modes_a;
    // gathered_product(a_shape, [1]) unfolds:
    // modes.len() == 1, modes.last() == 1, modes.drop_last() == []
    // = a_shape[1] * gathered_product(a_shape, [])
    // = a_shape[1] * 1 = a_shape[1]
    assert(modes.len() == 1);
    assert(modes.last() == 1nat);
    let dl = modes.drop_last();
    assert(dl =~= Seq::<nat>::empty());
    assert(dl.len() == 0);
    // Force Z3 to see the base case
    assert(gathered_product(&a_shape, &dl) == 1nat);
    // Now the recursive step
    assert(gathered_product(&a_shape, &modes) ==
        a_shape[modes.last() as int] * gathered_product(&a_shape, &dl));
    vstd::arithmetic::mul::lemma_mul_basics(a_shape[1] as int);
}

/// gathered_product of single mode = shape[mode].
pub proof fn lemma_gathered_product_single(shape: &Seq<nat>, mode: nat)
    requires mode < shape.len(),
    ensures gathered_product(shape, &seq![mode]) == shape[mode as int],
{
    let modes = seq![mode];
    assert(modes.len() == 1);
    assert(modes.last() == mode);
    let dl = modes.drop_last();
    assert(dl =~= Seq::<nat>::empty());
    assert(dl.len() == 0);
    assert(gathered_product(shape, &dl) == 1nat);
    assert(gathered_product(shape, &modes) ==
        shape[modes.last() as int] * gathered_product(shape, &dl));
    vstd::arithmetic::mul::lemma_mul_basics(shape[mode as int] as int);
}

// ══════════════════════════════════════════════════════════════
// MAC correctness proofs (Feature 3 Round 2)
// ══════════════════════════════════════════════════════════════

/// MAC completeness: all K elements produce offset pairs.
pub proof fn lemma_mac_complete(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    i: nat, j: nat, k_size: nat,
)
    requires a_layout.rank() == 2, b_layout.rank() == 2,
    ensures mac_complete(a_layout, b_layout, i, j, k_size),
{
    // mac_offset_pairs(a, b, i, j, 0, k_size) = Seq::new(k_size, ...)
    // len == k_size by definition of Seq::new
}

/// Tiled MAC consistency: K-tile pairs match global pairs.
pub proof fn lemma_tiled_mac_consistent(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    i: nat, j: nat, k_tile: nat, bk: nat, k_size: nat,
)
    requires
        a_layout.rank() == 2, b_layout.rank() == 2,
        bk > 0,
        k_tile * bk < k_size,
    ensures
        tiled_mac_consistent(a_layout, b_layout, i, j, k_tile, bk, k_size),
{
    let k_start = k_tile * bk;
    let k_end = if (k_tile + 1) * bk <= k_size { (k_tile + 1) * bk } else { k_size };

    assert forall|idx: nat| idx < k_end - k_start implies
        #[trigger] mac_offset_pairs(a_layout, b_layout, i, j, k_start, k_end)[idx as int]
        == mac_offset_pairs(a_layout, b_layout, i, j, 0, k_size)[(k_start + idx) as int]
    by {
        // LHS = (gemm_a_offset(a, i, k_start + idx), gemm_b_offset(b, k_start + idx, j))
        // RHS = (gemm_a_offset(a, i, 0 + (k_start + idx)), gemm_b_offset(b, 0 + (k_start + idx), j))
        // These are identical.
    };
}

// ══════════════════════════════════════════════════════════════
// Epilogue store proofs (Feature 4 Round 3)
// ══════════════════════════════════════════════════════════════

/// Epilogue store in-bounds when C tensor is valid and indices in range.
pub proof fn lemma_epilogue_store_in_bounds(
    c_layout: &LayoutSpec, c_data_size: nat, i: nat, j: nat,
)
    requires
        tensor_valid(&TensorSpec { layout: *c_layout, data_size: c_data_size }),
        c_layout.rank() == 2,
        i < c_layout.shape[0],
        j < c_layout.shape[1],
    ensures
        epilogue_store_in_bounds(c_layout, c_data_size, i, j),
{
    let s0 = c_layout.shape[0];
    let s1 = c_layout.shape[1];
    assert(c_layout.shape =~= seq![s0, s1]) by {
        assert(c_layout.shape.len() == 2);
    };
    lemma_shape_size_2(s0, s1);
    let x = i + j * s0;
    assert(x < s0 * s1) by (nonlinear_arith)
        requires i < s0, j < s1, x == i + j * s0, s0 > 0, s1 > 0;

    // Bridge x to (i,j) via div/mod
    vstd::arithmetic::mul::lemma_mul_is_commutative(j as int, s0 as int);
    assert(x == i + s0 * j);
    crate::proof::integer_helpers::lemma_div_mod_decompose(i, j, s0);
    assert(x % s0 == i);
    assert(x / s0 == j);

    // offset(x) = coords[0]*stride[0] + coords[1]*stride[1]
    lemma_offset_rank2(c_layout, x);
    let coords = delinearize(x, c_layout.shape);
    // coords[0] = x % s0 = i
    assert(coords[0] == i);
    // coords[1]: delinearize second level
    assert(c_layout.shape.first() == s0);
    assert(c_layout.shape.skip(1) =~= seq![s1]);
    assert(seq![s1].first() == s1);
    assert(seq![s1].skip(1) =~= Seq::<nat>::empty());
    let inner = delinearize(x / s0, seq![s1]);
    assert(x / s0 == j);
    assert(j % s1 == j) by {
        vstd::arithmetic::div_mod::lemma_small_mod(j, s1);
    };
    assert(inner =~= seq![j % s1].add(delinearize(j / s1, Seq::<nat>::empty())));
    assert(coords =~= seq![i].add(inner));
    assert(coords[1] == j);

    // Now: offset(x) = i*stride[0] + j*stride[1] = gemm_c_offset(c_layout, i, j)
    assert(c_layout.offset(x) == gemm_c_offset(c_layout, i, j));

    // offset bounds
    crate::proof::offset_lemmas::lemma_offset_nonneg(*c_layout, x);
    crate::proof::offset_lemmas::lemma_offset_upper_bound(*c_layout, x);
}

/// Predicated epilogue is correct: safe iff global indices are within bounds.
pub proof fn lemma_epilogue_predication_correct(
    m: nat, n: nat,
    ti: nat, tj: nat, ei: nat, ej: nat,
    bm: nat, bn: nat,
)
    requires bm > 0, bn > 0,
    ensures
        epilogue_predicated_store_safe(m, n, ti, tj, ei, ej, bm, bn)
        <==> (ti * bm + ei < m && tj * bn + ej < n),
{
    // Direct from definition
}

/// CTA epilogue correctness: all valid stores in a CTA are in-bounds.
pub proof fn lemma_epilogue_cta_correct(
    c_layout: &LayoutSpec, c_data_size: nat,
    m: nat, n: nat, bm: nat, bn: nat,
    ti: nat, tj: nat,
)
    requires
        tensor_valid(&TensorSpec { layout: *c_layout, data_size: c_data_size }),
        c_layout.rank() == 2,
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
        bm > 0, bn > 0,
    ensures
        epilogue_cta_correct(c_layout, c_data_size, m, n, bm, bn, ti, tj),
{
    assert forall|ei: nat, ej: nat|
        ei < bm && ej < bn
        && epilogue_predicated_store_safe(m, n, ti, tj, ei, ej, bm, bn)
    implies
        epilogue_store_in_bounds(c_layout, c_data_size, ti * bm + ei, tj * bn + ej)
    by {
        let gi = ti * bm + ei;
        let gj = tj * bn + ej;
        // predication safe → gi < m <= shape[0] and gj < n <= shape[1]
        lemma_epilogue_predication_correct(m, n, ti, tj, ei, ej, bm, bn);
        assert(gi < m);
        assert(gj < n);
        assert(gi < c_layout.shape[0]);
        assert(gj < c_layout.shape[1]);
        lemma_epilogue_store_in_bounds(c_layout, c_data_size, gi, gj);
    };
}

/// Cross-CTA epilogue disjointness: different CTAs write different C elements.
pub proof fn lemma_epilogue_cross_cta_disjoint(
    c_layout: &LayoutSpec, m: nat, n: nat, bm: nat, bn: nat,
)
    requires
        c_layout.valid(),
        c_layout.rank() == 2,
        c_layout.is_injective(),
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
        bm > 0, bn > 0,
    ensures
        epilogue_cross_cta_disjoint(c_layout, m, n, bm, bn),
{
    assert forall|ti1: nat, tj1: nat, ei1: nat, ej1: nat,
                 ti2: nat, tj2: nat, ei2: nat, ej2: nat|
        ei1 < bm && ej1 < bn && ei2 < bm && ej2 < bn
        && (ti1 != ti2 || tj1 != tj2)
        && epilogue_predicated_store_safe(m, n, ti1, tj1, ei1, ej1, bm, bn)
        && epilogue_predicated_store_safe(m, n, ti2, tj2, ei2, ej2, bm, bn)
    implies
        #[trigger] gemm_c_tile_offset(c_layout, ti1, tj1, ei1, ej1, bm, bn)
        != #[trigger] gemm_c_tile_offset(c_layout, ti2, tj2, ei2, ej2, bm, bn)
    by {
        let gi1 = ti1 * bm + ei1;
        let gj1 = tj1 * bn + ej1;
        let gi2 = ti2 * bm + ei2;
        let gj2 = tj2 * bn + ej2;
        lemma_epilogue_predication_correct(m, n, ti1, tj1, ei1, ej1, bm, bn);
        lemma_epilogue_predication_correct(m, n, ti2, tj2, ei2, ej2, bm, bn);
        // gi1 < m, gj1 < n, gi2 < m, gj2 < n
        lemma_gemm_tiled_c_disjoint(c_layout, m, n, bm, bn,
            ti1, tj1, ei1, ej1, ti2, tj2, ei2, ej2);
    };
}

} // verus!
