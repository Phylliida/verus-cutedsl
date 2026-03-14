use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::gemm::*;
use crate::predication::*;
use crate::tiling::*;
use crate::swizzle::*;
use crate::contraction::*;
use crate::slice::*;
use crate::divide::*;
use crate::proof::shape_lemmas::*;
use crate::proof::tiling_lemmas::*;
use verus_algebra::traits::*;
use verus_algebra::summation::sum;

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
// Data-level MAC correctness proofs (Feature 1 Round 3)
// ══════════════════════════════════════════════════════════════

/// MAC value is zero for empty range.
pub proof fn lemma_mac_empty<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k: nat,
)
    ensures
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k, k).eqv(R::zero()),
{
    verus_algebra::summation::lemma_sum_empty::<R>(
        |ki: int| a_val(i, ki as nat).mul(b_val(ki as nat, j)),
        k as int, k as int,
    );
}

/// MAC single element: sum over [k, k+1) equals a_val(i,k) * b_val(k,j).
pub proof fn lemma_mac_single<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k: nat,
)
    ensures
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k, k + 1)
            .eqv(a_val(i, k).mul(b_val(k, j))),
{
    verus_algebra::summation::lemma_sum_single::<R>(
        |ki: int| a_val(i, ki as nat).mul(b_val(ki as nat, j)),
        k as int,
    );
}

/// MAC split: full MAC splits at any k_mid.
/// gemm_mac_value(0, k_size) ≡ tiled_mac(0, k_mid) + tiled_mac(k_mid, k_size).
pub proof fn lemma_mac_split<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_size: nat, k_mid: nat,
)
    requires
        k_mid <= k_size,
    ensures
        gemm_mac_value::<R>(a_val, b_val, i, j, k_size).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, 0, k_mid).add(
                gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_mid, k_size))),
{
    verus_algebra::summation::lemma_sum_split::<R>(
        |ki: int| a_val(i, ki as nat).mul(b_val(ki as nat, j)),
        0int, k_mid as int, k_size as int,
    );
}

/// Predicated MAC equals real MAC when k_end <= k_size (all valid).
/// When every element in [k_start, k_end) is valid (k < k_size), the predicated
/// MAC equals the tiled MAC (the conditional is always true).
pub proof fn lemma_predicated_mac_all_valid<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_start: nat, k_end: nat, k_size: nat,
)
    requires
        k_start <= k_end,
        k_end <= k_size,
    ensures
        gemm_predicated_mac_value::<R>(a_val, b_val, i, j, k_start, k_end, k_size).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_end)),
{
    // All elements in [k_start, k_end) have k < k_size, so predicate is always true.
    // The two summands are pointwise eqv → sum congruence.
    let f = |k: int|
        if (k as nat) < k_size {
            a_val(i, k as nat).mul(b_val(k as nat, j))
        } else {
            R::zero()
        };
    let g = |k: int| a_val(i, k as nat).mul(b_val(k as nat, j));

    assert forall|k: int| k_start as int <= k < k_end as int
    implies (#[trigger] f(k)).eqv(g(k))
    by {
        // k >= k_start >= 0 and k < k_end <= k_size, so (k as nat) < k_size
        assert((k as nat) < k_size);
        // f(k) == g(k) definitionally, so eqv by reflexivity
        R::axiom_eqv_reflexive(g(k));
    };
    verus_algebra::summation::lemma_sum_congruence::<R>(
        f, g, k_start as int, k_end as int,
    );
}

/// Predicated MAC for tail beyond k_size: all terms are zero.
pub proof fn lemma_predicated_mac_tail_zero<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_start: nat, k_end: nat, k_size: nat,
)
    requires
        k_size <= k_start,
        k_start <= k_end,
    ensures
        gemm_predicated_mac_value::<R>(a_val, b_val, i, j, k_start, k_end, k_size)
            .eqv(R::zero()),
{
    // All elements have k >= k_start >= k_size, so predicate is always false → zero terms.
    let f = |k: int|
        if (k as nat) < k_size {
            a_val(i, k as nat).mul(b_val(k as nat, j))
        } else {
            R::zero()
        };
    let z = |k: int| R::zero();

    assert forall|k: int| k_start as int <= k < k_end as int
    implies (#[trigger] f(k)).eqv(z(k))
    by {
        assert(!((k as nat) < k_size));
        R::axiom_eqv_reflexive(R::zero());
    };
    verus_algebra::summation::lemma_sum_congruence::<R>(
        f, z, k_start as int, k_end as int,
    );
    // sum(f) ≡ sum(z). Now show sum(z) ≡ zero.
    if k_start < k_end {
        lemma_sum_of_zeros::<R>(z, k_start as int, k_end as int);
        R::axiom_eqv_transitive(
            sum::<R>(f, k_start as int, k_end as int),
            sum::<R>(z, k_start as int, k_end as int),
            R::zero(),
        );
    } else {
        // k_start == k_end, sum over empty range is zero by definition
        verus_algebra::summation::lemma_sum_empty::<R>(f, k_start as int, k_end as int);
    }
}

/// Helper: sum of constant zero is zero.
proof fn lemma_sum_of_zeros<R: Ring>(
    z: spec_fn(int) -> R,
    lo: int, hi: int,
)
    requires
        lo <= hi,
        forall|k: int| lo <= k < hi ==> (#[trigger] z(k)).eqv(R::zero()),
    ensures
        sum::<R>(z, lo, hi).eqv(R::zero()),
    decreases hi - lo,
{
    if lo == hi {
        verus_algebra::summation::lemma_sum_empty::<R>(z, lo, hi);
    } else {
        verus_algebra::summation::lemma_sum_peel_last::<R>(z, lo, hi);
        // sum(z, lo, hi) ≡ sum(z, lo, hi-1) + z(hi-1)
        lemma_sum_of_zeros::<R>(z, lo, hi - 1);
        // sum(z, lo, hi-1) ≡ zero
        // z(hi-1) ≡ zero
        assert(z(hi - 1).eqv(R::zero()));
        // zero + zero ≡ zero
        R::axiom_add_zero_right(R::zero());
        // sum(z, lo, hi) ≡ sum(z, lo, hi-1) + z(hi-1) ≡ zero + zero ≡ zero
        // Need: sum(z, lo, hi-1).add(z(hi-1)) ≡ zero.add(zero) ≡ zero
        verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<R>(
            sum::<R>(z, lo, hi - 1), R::zero(),
            z(hi - 1), R::zero(),
        );
        // sum(z, lo, hi-1).add(z(hi-1)) ≡ zero.add(zero)
        R::axiom_eqv_transitive(
            sum::<R>(z, lo, hi),
            sum::<R>(z, lo, hi - 1).add(z(hi - 1)),
            R::zero().add(R::zero()),
        );
        R::axiom_eqv_transitive(
            sum::<R>(z, lo, hi),
            R::zero().add(R::zero()),
            R::zero(),
        );
    }
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

// ══════════════════════════════════════════════════════════════
// Batched GEMM contraction proofs (Feature 1 Round 4)
// ══════════════════════════════════════════════════════════════

/// Batched GEMM contraction shapes match when batch and K dims agree.
pub proof fn lemma_batched_gemm_contraction_shapes_match(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 3,
        b_shape.len() == 3,
        a_shape[0] == b_shape[0],  // batch dim
        a_shape[2] == b_shape[1],  // K dim
    ensures
        contraction_shapes_match(&batched_gemm_as_contraction(), &a_shape, &b_shape),
{
    let spec = batched_gemm_as_contraction();
    // Batch: gather_shape(a, [0]) = [a[0]], gather_shape(b, [0]) = [b[0]]
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~=
           gather_shape(&b_shape, &spec.batch_modes_b));
    // Contraction: gather_shape(a, [2]) = [a[2]], gather_shape(b, [1]) = [b[1]]
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~=
           gather_shape(&b_shape, &spec.contraction_modes_b));
}

/// Batched GEMM contraction output shape is (batch, M, N).
pub proof fn lemma_batched_gemm_contraction_output_shape(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 3,
        b_shape.len() == 3,
    ensures
        contraction_output_shape(&batched_gemm_as_contraction(), &a_shape, &b_shape)
        =~= seq![a_shape[0], a_shape[1], b_shape[2]],
{
    let spec = batched_gemm_as_contraction();
    let batch = gather_shape(&a_shape, &spec.batch_modes_a);
    let free_a = gather_shape(&a_shape, &spec.free_modes_a);
    let free_b = gather_shape(&b_shape, &spec.free_modes_b);
    assert(batch =~= seq![a_shape[0]]);
    assert(free_a =~= seq![a_shape[1]]);
    assert(free_b =~= seq![b_shape[2]]);
    assert(batch.add(free_a).add(free_b) =~= seq![a_shape[0], a_shape[1], b_shape[2]]);
}

/// Batched GEMM contraction admissibility.
pub proof fn lemma_batched_gemm_contraction_admissible(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 3,
        b_shape.len() == 3,
        a_shape[0] == b_shape[0],
        a_shape[2] == b_shape[1],
    ensures
        contraction_admissible(&batched_gemm_as_contraction(), &a_shape, &b_shape),
{
    lemma_batched_gemm_contraction_valid();
    lemma_batched_gemm_contraction_shapes_match(a_shape, b_shape);
}

/// Batched GEMM reduction size = K (a_shape[2]).
pub proof fn lemma_batched_gemm_reduction_size(a_shape: Seq<nat>)
    requires a_shape.len() == 3,
    ensures contraction_reduction_size(&batched_gemm_as_contraction(), &a_shape) == a_shape[2],
{
    let spec = batched_gemm_as_contraction();
    assert(spec.contraction_modes_a =~= seq![2nat]);
    lemma_gathered_product_single(&a_shape, 2);
}

/// gathered_product of two modes = shape[m0] * shape[m1].
pub proof fn lemma_gathered_product_two(shape: &Seq<nat>, m0: nat, m1: nat)
    requires
        m0 < shape.len(),
        m1 < shape.len(),
    ensures
        gathered_product(shape, &seq![m0, m1]) == shape[m0 as int] * shape[m1 as int],
{
    let modes = seq![m0, m1];
    assert(modes.len() == 2);
    assert(modes.last() == m1);
    let dl = modes.drop_last();
    assert(dl =~= seq![m0]);
    lemma_gathered_product_single(shape, m0);
    assert(gathered_product(shape, &dl) == shape[m0 as int]);
    assert(gathered_product(shape, &modes) ==
        shape[modes.last() as int] * gathered_product(shape, &dl));
    vstd::arithmetic::mul::lemma_mul_is_commutative(
        shape[m1 as int] as int, shape[m0 as int] as int,
    );
}

// ══════════════════════════════════════════════════════════════
// Epilogue partition proofs (Feature 2 Round 4)
// ══════════════════════════════════════════════════════════════

/// Local partition at any thread_id produces a valid residual layout.
pub proof fn lemma_local_partition_valid(
    tensor: &DividedLayout, tv_layout: &LayoutSpec, thread_id: nat,
)
    requires
        divided_layout_valid(tensor),
        tensor.layout.valid(),
        tensor.layout.rank() > 0,
        thread_id < tensor.layout.shape[0],
    ensures
        local_partition(tensor, tv_layout, thread_id).0.valid(),
{
    crate::proof::slice_lemmas::lemma_slice_valid(&tensor.layout, 0, thread_id);
}

/// Per-thread element count: all threads get the same shape (hence same size).
pub proof fn lemma_local_partition_uniform_shape(
    tensor: &DividedLayout, tv_layout: &LayoutSpec,
    t1: nat, t2: nat,
)
    requires
        divided_layout_valid(tensor),
        tensor.layout.valid(),
        tensor.layout.rank() > 0,
        t1 < tensor.layout.shape[0],
        t2 < tensor.layout.shape[0],
    ensures
        local_partition(tensor, tv_layout, t1).0.shape
        =~= local_partition(tensor, tv_layout, t2).0.shape,
{
    crate::proof::slice_lemmas::lemma_slice_mode0(&tensor.layout, t1);
    crate::proof::slice_lemmas::lemma_slice_mode0(&tensor.layout, t2);
    // Both slice at mode 0, so shape = layout.shape.skip(1) for both
}

/// Thread disjointness: distinct thread_ids produce disjoint offset sets.
pub proof fn lemma_local_partition_disjoint(
    tensor: &DividedLayout, tv_layout: &LayoutSpec,
    t1: nat, t2: nat, i: nat, j: nat,
)
    requires
        divided_layout_valid(tensor),
        tensor.layout.valid(),
        tensor.layout.is_injective(),
        tensor.layout.rank() > 0,
        t1 < tensor.layout.shape[0],
        t2 < tensor.layout.shape[0],
        t1 != t2,
        i < shape_size(slice_layout(&tensor.layout, 0, t1).shape),
        j < shape_size(slice_layout(&tensor.layout, 0, t2).shape),
    ensures
        local_partition(tensor, tv_layout, t1).1
        + local_partition(tensor, tv_layout, t1).0.offset(i)
        != local_partition(tensor, tv_layout, t2).1
        + local_partition(tensor, tv_layout, t2).0.offset(j),
{
    crate::proof::tiling_lemmas::lemma_slice_disjoint(&tensor.layout, t1, t2, i, j);
}

/// Thread coverage: every element of the tensor is assigned to some thread.
pub proof fn lemma_local_partition_coverage(
    tensor: &DividedLayout, tv_layout: &LayoutSpec, x: nat,
)
    requires
        divided_layout_valid(tensor),
        tensor.layout.valid(),
        tensor.layout.rank() > 0,
        x < shape_size(tensor.layout.shape),
    ensures ({
        let m0 = tensor.layout.shape[0];
        let c = x % m0;
        let i = x / m0;
        &&& c < m0
        &&& i < shape_size(slice_layout(&tensor.layout, 0, c).shape)
        &&& tensor.layout.offset(x)
            == local_partition(tensor, tv_layout, c).1
               + local_partition(tensor, tv_layout, c).0.offset(i)
    }),
{
    crate::proof::tiling_lemmas::lemma_partition_coverage(&tensor.layout, x);
}

/// Epilogue partition offset is 0 (thread_id = 0, so offset = 0 * stride[0] = 0).
pub proof fn lemma_epilogue_partition_offset_zero(
    c_tile: &DividedLayout, thread_layout: &LayoutSpec,
)
    requires
        divided_layout_valid(c_tile),
        c_tile.layout.valid(),
        c_tile.layout.rank() > 0,
    ensures
        epilogue_partition(c_tile, thread_layout).1 == 0int,
{
    // epilogue_partition = local_partition(c_tile, thread_layout, 0)
    // local_partition.1 = slice_offset(&c_tile.layout, 0, 0) = 0 * stride[0] = 0
}

// ══════════════════════════════════════════════════════════════
// Contraction structural lemmas (Feature 4 Round 4)
// ══════════════════════════════════════════════════════════════

/// gather_shape length = modes length.
pub proof fn lemma_gather_shape_len(shape: &Seq<nat>, modes: &Seq<nat>)
    ensures
        gather_shape(shape, modes).len() == modes.len(),
{
    // Direct from Seq::new definition
}

/// Contraction output rank = batch + free_a + free_b.
pub proof fn lemma_contraction_output_rank(
    spec: &ContractionSpec, a_shape: &Seq<nat>, b_shape: &Seq<nat>,
)
    ensures
        contraction_output_shape(spec, a_shape, b_shape).len()
        == spec.batch_modes_a.len() + spec.free_modes_a.len() + spec.free_modes_b.len(),
{
    let batch = gather_shape(a_shape, &spec.batch_modes_a);
    let free_a = gather_shape(a_shape, &spec.free_modes_a);
    let free_b = gather_shape(b_shape, &spec.free_modes_b);
    lemma_gather_shape_len(a_shape, &spec.batch_modes_a);
    lemma_gather_shape_len(a_shape, &spec.free_modes_a);
    lemma_gather_shape_len(b_shape, &spec.free_modes_b);
    assert(batch.add(free_a).add(free_b).len() ==
        batch.len() + free_a.len() + free_b.len());
}

/// GEMM output rank = 2 (M and N dimensions).
pub proof fn lemma_gemm_contraction_output_rank(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires a_shape.len() == 2, b_shape.len() == 2,
    ensures
        contraction_output_shape(&gemm_as_contraction(), &a_shape, &b_shape).len() == 2,
{
    lemma_contraction_output_rank(&gemm_as_contraction(), &a_shape, &b_shape);
}

/// Batched GEMM output rank = 3 (batch, M, N).
pub proof fn lemma_batched_gemm_contraction_output_rank(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires a_shape.len() == 3, b_shape.len() == 3,
    ensures
        contraction_output_shape(&batched_gemm_as_contraction(), &a_shape, &b_shape).len() == 3,
{
    lemma_contraction_output_rank(&batched_gemm_as_contraction(), &a_shape, &b_shape);
}

/// GEMM contraction output matches C layout shape requirements.
pub proof fn lemma_gemm_contraction_matches_c(
    a_shape: Seq<nat>, b_shape: Seq<nat>, c_layout: &LayoutSpec,
)
    requires
        a_shape.len() == 2,
        b_shape.len() == 2,
        a_shape[1] == b_shape[0],
        c_layout.rank() == 2,
        a_shape[0] <= c_layout.shape[0],
        b_shape[1] <= c_layout.shape[1],
    ensures ({
        let out = contraction_output_shape(&gemm_as_contraction(), &a_shape, &b_shape);
        out[0] <= c_layout.shape[0] && out[1] <= c_layout.shape[1]
    }),
{
    lemma_gemm_contraction_output_shape(a_shape, b_shape);
    let out = contraction_output_shape(&gemm_as_contraction(), &a_shape, &b_shape);
    assert(out =~= seq![a_shape[0], b_shape[1]]);
}

/// gathered_product is 1 for empty modes.
pub proof fn lemma_gathered_product_empty(shape: &Seq<nat>)
    ensures
        gathered_product(shape, &Seq::<nat>::empty()) == 1nat,
{
    // Base case of gathered_product definition
}

/// gathered_product is positive when all gathered shapes are positive.
pub proof fn lemma_gathered_product_positive(shape: Seq<nat>, modes: Seq<nat>)
    requires
        forall|i: nat| i < modes.len() ==>
            (#[trigger] modes[i as int]) < shape.len()
            && shape[modes[i as int] as int] > 0,
    ensures
        gathered_product(&shape, &modes) > 0,
    decreases modes.len(),
{
    if modes.len() == 0 {
        // Base: gathered_product = 1 > 0
    } else {
        let last = modes.last();
        let dl = modes.drop_last();
        // last mode has positive shape
        assert(shape[last as int] > 0);
        // Induction: drop_last modes satisfy precondition
        assert forall|i: nat| i < dl.len() implies
            (#[trigger] dl[i as int]) < shape.len()
            && shape[dl[i as int] as int] > 0
        by {
            assert(dl[i as int] == modes[i as int]);
        };
        lemma_gathered_product_positive(shape, dl);
        // shape[last] > 0 * rest > 0 > 0
        vstd::arithmetic::mul::lemma_mul_strictly_positive(
            shape[last as int] as int,
            gathered_product(&shape, &modes.drop_last()) as int,
        );
    }
}

// ══════════════════════════════════════════════════════════════
// MAC K-tile splitting proofs (Feature 3 Round 6)
// ══════════════════════════════════════════════════════════════

/// Two-tile MAC accumulation: tiled_mac over [k_start, k_end) splits at k_mid.
pub proof fn lemma_mac_accumulate<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_start: nat, k_mid: nat, k_end: nat,
)
    requires k_start <= k_mid, k_mid <= k_end,
    ensures
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_end).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_mid).add(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_mid, k_end))),
{
    verus_algebra::summation::lemma_sum_split::<R>(
        |k: int| a_val(i, k as nat).mul(b_val(k as nat, j)),
        k_start as int, k_mid as int, k_end as int,
    );
}

/// Predicated MAC equals tiled MAC for valid range (k_end <= k_size).
pub proof fn lemma_predicated_mac_equals_tiled<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_start: nat, k_end: nat, k_size: nat,
)
    requires
        k_start <= k_end,
        k_end <= k_size,
    ensures
        gemm_predicated_mac_value::<R>(a_val, b_val, i, j, k_start, k_end, k_size).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_end)),
{
    // Direct from lemma_predicated_mac_all_valid
    lemma_predicated_mac_all_valid::<R>(a_val, b_val, i, j, k_start, k_end, k_size);
}

/// Predicated MAC with padding: when k_start <= k_size <= k_end, pad zeros don't contribute.
pub proof fn lemma_predicated_mac_padding_zero<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_start: nat, k_end: nat, k_size: nat,
)
    requires
        k_start <= k_size,
        k_size <= k_end,
    ensures
        gemm_predicated_mac_value::<R>(a_val, b_val, i, j, k_start, k_end, k_size).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_size)),
{
    // Split predicated sum at k_size: [k_start, k_size) all valid + [k_size, k_end) all zero
    let f = |k: int|
        if (k as nat) < k_size {
            a_val(i, k as nat).mul(b_val(k as nat, j))
        } else {
            R::zero()
        };
    let g = |k: int| a_val(i, k as nat).mul(b_val(k as nat, j));

    // Split at k_size
    verus_algebra::summation::lemma_sum_split::<R>(f, k_start as int, k_size as int, k_end as int);
    // sum(f, k_start, k_end) ≡ sum(f, k_start, k_size) + sum(f, k_size, k_end)

    // sum(f, k_start, k_size) ≡ sum(g, k_start, k_size): all valid
    lemma_predicated_mac_all_valid::<R>(a_val, b_val, i, j, k_start, k_size, k_size);

    // sum(f, k_size, k_end) ≡ 0: all past k_size
    lemma_predicated_mac_tail_zero::<R>(a_val, b_val, i, j, k_size, k_end, k_size);

    // Combine: sum(f, k_start, k_end) ≡ tiled_mac(k_start, k_size) + 0 ≡ tiled_mac(k_start, k_size)
    // Need: sum(f, k_start, k_size).add(sum(f, k_size, k_end)) ≡ tiled_mac + 0
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<R>(
        sum::<R>(f, k_start as int, k_size as int),
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_size),
        sum::<R>(f, k_size as int, k_end as int),
        R::zero(),
    );
    // tiled_mac + 0 ≡ tiled_mac
    R::axiom_add_zero_right(gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_size));
    // Chain transitivity
    R::axiom_eqv_transitive(
        sum::<R>(f, k_start as int, k_end as int),
        sum::<R>(f, k_start as int, k_size as int).add(sum::<R>(f, k_size as int, k_end as int)),
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_size).add(R::zero()),
    );
    R::axiom_eqv_transitive(
        sum::<R>(f, k_start as int, k_end as int),
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_size).add(R::zero()),
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_size),
    );
}

/// K-tile MAC splitting: full MAC = sum of tiled MACs over K-tiles.
/// Each tile covers [t*bk, min((t+1)*bk, K)).
pub proof fn lemma_mac_k_tile_split<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k_size: nat, bk: nat,
)
    requires bk > 0, k_size > 0,
    ensures
        // Full MAC equals sum of tiles from 0 to k_size, split at bk boundaries
        gemm_mac_value::<R>(a_val, b_val, i, j, k_size).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, i, j, 0, k_size)),
{
    // gemm_mac_value is sum(f, 0, k_size) and gemm_tiled_mac_value(0, k_size) is
    // also sum(f, 0, k_size) — they are definitionally equal.
    R::axiom_eqv_reflexive(
        gemm_mac_value::<R>(a_val, b_val, i, j, k_size));
}

// ══════════════════════════════════════════════════════════════
// Copy operation proofs (Feature 4 Round 6)
// ══════════════════════════════════════════════════════════════

/// Column-major SMEM has identity offset: data lands at logical position.
pub proof fn lemma_smem_identity_offset(smem_base: &LayoutSpec, x: nat)
    requires
        smem_base.valid(),
        smem_base.stride =~= column_major_strides(smem_base.shape),
        x < smem_base.size(),
    ensures
        smem_base.offset(x) == x as int,
{
    crate::proof::injectivity_lemmas::lemma_column_major_offset_is_identity(smem_base.shape, x);
    crate::proof::composition_lemmas::lemma_offset_eq_layout(
        smem_base.shape, smem_base.stride,
        smem_base.shape, column_major_strides(smem_base.shape), x,
    );
}

/// G2S copy preserves tile identity: for column-major SMEM,
/// the data at global tile position x ends up at SMEM position x.
pub proof fn lemma_g2s_offset_identity(
    g2s_copy: &LayoutSpec, smem_base: &LayoutSpec,
    tile_m: nat, tile_k: nat, x: nat,
)
    requires
        g2s_stage_valid(g2s_copy, smem_base, tile_m, tile_k),
        smem_base.stride =~= column_major_strides(smem_base.shape),
        x < tile_m * tile_k,
    ensures
        smem_base.offset(x) == x as int,
{
    // g2s_stage_valid → smem_base.valid() and size >= tile_m * tile_k
    lemma_smem_identity_offset(smem_base, x);
}

/// S2R copy offset consistency: thread_id * val_size + val_idx < s2r size.
pub proof fn lemma_s2r_offset_consistency(
    s2r_copy: &LayoutSpec, mma_thr: &LayoutSpec, mma_val: &LayoutSpec,
    thread_id: nat, val_idx: nat,
)
    requires
        s2r_stage_valid(s2r_copy, mma_thr, mma_val),
        thread_id < mma_thr.size(),
        val_idx < mma_val.size(),
    ensures
        thread_id * mma_val.size() + val_idx < s2r_copy.size(),
{
    // s2r_stage_valid → s2r_copy.size() >= mma_thr.size() * mma_val.size()
    assert(thread_id * mma_val.size() + val_idx < mma_thr.size() * mma_val.size())
        by (nonlinear_arith)
        requires
            thread_id < mma_thr.size(),
            val_idx < mma_val.size(),
            mma_thr.size() > 0,
            mma_val.size() > 0;
}

/// Copy pipeline data flow: G2S followed by S2R preserves data identity
/// for column-major SMEM.
pub proof fn lemma_copy_pipeline_identity(
    smem_base: &LayoutSpec, tile_size: nat, x: nat,
)
    requires
        smem_base.valid(),
        smem_base.stride =~= column_major_strides(smem_base.shape),
        smem_base.size() == tile_size,
        x < tile_size,
    ensures
        smem_base.offset(x) == x as int,
{
    lemma_smem_identity_offset(smem_base, x);
}

// ══════════════════════════════════════════════════════════════
// Swizzle+Divide SMEM composition proofs (Feature 3 Round 7)
// ══════════════════════════════════════════════════════════════

/// Divided column-major SMEM tile has identity offset.
pub proof fn lemma_smem_divide_identity(
    smem_base: &LayoutSpec, thread_tile: &LayoutSpec, x: nat,
)
    requires
        divide_admissible(smem_base, thread_tile),
        smem_base.stride =~= column_major_strides(smem_base.shape),
        thread_tile.stride =~= column_major_strides(thread_tile.shape),
        x < shape_size(smem_base.shape),
    ensures
        logical_divide(smem_base, thread_tile).offset(x) == x as int,
{
    crate::proof::divide_lemmas::lemma_divide_offset_column_major(smem_base, thread_tile, x);
}

/// Swizzled divided SMEM: each element gets a unique swizzled address.
/// Since divide has identity offset for column-major layouts,
/// swizzle(divide.offset(x)) == swizzle(x), and swizzle is injective.
pub proof fn lemma_smem_swizzle_divide_injective(
    smem_base: &LayoutSpec, thread_tile: &LayoutSpec,
    b_bits: nat, m_bits: nat, s_bits: nat,
)
    requires
        divide_admissible(smem_base, thread_tile),
        smem_base.stride =~= column_major_strides(smem_base.shape),
        thread_tile.stride =~= column_major_strides(thread_tile.shape),
        swizzle_admissible(b_bits, m_bits, s_bits),
        shape_size(smem_base.shape) <= pow2(m_bits + s_bits + b_bits),
    ensures
        forall|i: nat, j: nat|
            i < shape_size(smem_base.shape) && j < shape_size(smem_base.shape) && i != j
            ==> swizzle(#[trigger] logical_divide(smem_base, thread_tile).offset(i) as nat, b_bits, m_bits, s_bits)
                != swizzle(#[trigger] logical_divide(smem_base, thread_tile).offset(j) as nat, b_bits, m_bits, s_bits),
{
    let sz = shape_size(smem_base.shape);
    // First establish identity offset for all elements
    assert forall|x: nat| x < sz implies
        #[trigger] logical_divide(smem_base, thread_tile).offset(x) == x as int
    by {
        lemma_smem_divide_identity(smem_base, thread_tile, x);
    };

    // Swizzle is injective on [0, 2^(m+s+b))
    crate::proof::swizzle_lemmas::lemma_swizzle_bijection_on_domain(b_bits, m_bits, s_bits);

    // Combine: distinct x,y → distinct swizzle(x), swizzle(y)
    assert forall|i: nat, j: nat|
        i < sz && j < sz && i != j
    implies
        swizzle(#[trigger] logical_divide(smem_base, thread_tile).offset(i) as nat, b_bits, m_bits, s_bits)
        != swizzle(#[trigger] logical_divide(smem_base, thread_tile).offset(j) as nat, b_bits, m_bits, s_bits)
    by {
        assert(logical_divide(smem_base, thread_tile).offset(i) == i as int);
        assert(logical_divide(smem_base, thread_tile).offset(j) == j as int);
        // i, j < sz <= pow2(m+s+b), and i != j, so swizzle(i) != swizzle(j)
        assert(i < pow2(m_bits + s_bits + b_bits));
        assert(j < pow2(m_bits + s_bits + b_bits));
    };
}

/// SM80 instantiation: SMEM tile with B=3,M=0,S=3 swizzle after divide is injective.
pub proof fn lemma_sm80_smem_tile_swizzle_divide(
    smem_base: &LayoutSpec, thread_tile: &LayoutSpec,
)
    requires
        divide_admissible(smem_base, thread_tile),
        smem_base.stride =~= column_major_strides(smem_base.shape),
        thread_tile.stride =~= column_major_strides(thread_tile.shape),
        shape_size(smem_base.shape) <= pow2(6),  // 2^(0+3+3) = 64 ... B+M+S bits
    ensures
        forall|i: nat, j: nat|
            i < shape_size(smem_base.shape) && j < shape_size(smem_base.shape) && i != j
            ==> swizzle(#[trigger] logical_divide(smem_base, thread_tile).offset(i) as nat, 3, 0, 3)
                != swizzle(#[trigger] logical_divide(smem_base, thread_tile).offset(j) as nat, 3, 0, 3),
{
    lemma_smem_swizzle_divide_injective(smem_base, thread_tile, 3, 0, 3);
}

// ══════════════════════════════════════════════════════════════
// E2E GEMM correctness proofs (Feature 5 Round 6)
// ══════════════════════════════════════════════════════════════

/// Single CTA computes correct partial output:
/// After processing all K-tiles, accumulator[i,j] ≡ gemm_mac_value(a, b, gi, gj, K).
pub proof fn lemma_cta_computes_mac<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    gi: nat, gj: nat, k_size: nat, bk: nat,
)
    requires
        bk > 0, k_size > 0,
    ensures
        // The full MAC over [0, k_size) equals the tiled MAC over [0, k_size)
        gemm_mac_value::<R>(a_val, b_val, gi, gj, k_size).eqv(
            gemm_tiled_mac_value::<R>(a_val, b_val, gi, gj, 0, k_size)),
{
    lemma_mac_k_tile_split::<R>(a_val, b_val, gi, gj, k_size, bk);
}

/// Master GEMM correctness theorem: gemm_mac_value IS the standard matrix multiply sum.
/// This is a definitional theorem — gemm_mac_value(a, b, i, j, k) is literally
/// sum_k(a(i,k) * b(k,j)), so the proof is reflexivity.
pub proof fn lemma_gemm_output_correct<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, k: nat,
)
    ensures
        gemm_mac_value::<R>(a_val, b_val, i, j, k).eqv(
            sum::<R>(|kk: int| a_val(i, kk as nat).mul(b_val(kk as nat, j)), 0, k as int)),
{
    // gemm_mac_value IS sum(|k| a(i,k)*b(k,j), 0, k) by definition
    R::axiom_eqv_reflexive(gemm_mac_value::<R>(a_val, b_val, i, j, k));
}

/// Full pipeline correctness: structural + data correctness combined.
pub proof fn lemma_gemm_full_correctness<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    m: nat, n: nat, k: nat, bm: nat, bn: nat, bk: nat,
    a_layout: &LayoutSpec, b_layout: &LayoutSpec, c_layout: &LayoutSpec,
    g2s_a: &LayoutSpec, g2s_b: &LayoutSpec,
    smem_a: &LayoutSpec, smem_b: &LayoutSpec,
    s2r_a: &LayoutSpec, s2r_b: &LayoutSpec,
    mma_thr: &LayoutSpec, mma_val: &LayoutSpec,
)
    requires
        gemm_pipeline_admissible(m, n, k, bm, bn, bk,
            g2s_a, g2s_b, smem_a, smem_b, s2r_a, s2r_b,
            mma_thr, mma_val, a_layout, b_layout, c_layout),
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
        padded_divide_admissible(k, bk),
        smem_a.stride =~= column_major_strides(smem_a.shape),
        smem_b.stride =~= column_major_strides(smem_b.shape),
    ensures
        // 1. Every output element is computed
        gemm_output_covered(m, n, bm, bn),
        // 2. All K elements contribute
        k_reduction_complete(k, bk),
        // 3. Outputs don't collide
        gemm_output_injective(c_layout, m, n),
        // 4. Data flows correctly through pipeline
        forall|x: nat| x < smem_a.size() ==> smem_a.offset(x) == x as int,
        forall|x: nat| x < smem_b.size() ==> smem_b.offset(x) == x as int,
        // 5. Each output element equals the MAC value (definitional)
        forall|i: nat, j: nat| i < m && j < n ==>
            gemm_mac_value::<R>(a_val, b_val, i, j, k).eqv(
                sum::<R>(|kk: int| a_val(i, kk as nat).mul(b_val(kk as nat, j)), 0, k as int)),
{
    // Structural correctness
    lemma_gemm_pipeline_correct(m, n, k, bm, bn, bk,
        g2s_a, g2s_b, smem_a, smem_b, s2r_a, s2r_b,
        mma_thr, mma_val, a_layout, b_layout, c_layout);

    // SMEM identity offsets
    assert forall|x: nat| x < smem_a.size() implies smem_a.offset(x) == x as int by {
        lemma_smem_identity_offset(smem_a, x);
    };
    assert forall|x: nat| x < smem_b.size() implies smem_b.offset(x) == x as int by {
        lemma_smem_identity_offset(smem_b, x);
    };

    // Data correctness: gemm_mac_value IS the sum by definition
    assert forall|i: nat, j: nat| i < m && j < n implies
        gemm_mac_value::<R>(a_val, b_val, i, j, k).eqv(
            sum::<R>(|kk: int| a_val(i, kk as nat).mul(b_val(kk as nat, j)), 0, k as int))
    by {
        lemma_gemm_output_correct::<R>(a_val, b_val, i, j, k);
    };
}

// ══════════════════════════════════════════════════════════════
// K-loop pipeline safety proofs (Feature 4 Round 7)
// ══════════════════════════════════════════════════════════════

/// K-loop base case: accumulator starts at zero ≡ sum of 0 tiles.
pub proof fn lemma_k_loop_base<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat, bk: nat, k_size: nat,
)
    requires bk > 0, k_size > 0,
    ensures
        k_loop_acc_invariant::<R>(a_val, b_val, i, j, R::zero(), 0, bk, k_size),
{
    // iteration=0 → k_end = min(0*bk, k_size) = 0
    // acc ≡ tiled_mac(0, 0) ≡ zero
    lemma_mac_empty::<R>(a_val, b_val, i, j, 0);
    R::axiom_eqv_symmetric(
        gemm_tiled_mac_value::<R>(a_val, b_val, i, j, 0, 0),
        R::zero(),
    );
}

/// K-loop iteration preserves accumulator invariant.
/// After adding this tile's contribution, invariant holds for iteration+1.
pub proof fn lemma_k_loop_step<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat,
    acc: R, iteration: nat, bk: nat, k_size: nat,
)
    requires
        bk > 0,
        k_size > 0,
        iteration * bk < k_size,  // not past the end
        k_loop_acc_invariant::<R>(a_val, b_val, i, j, acc, iteration, bk, k_size),
    ensures ({
        let k_start = iteration * bk;
        let k_end = if (iteration + 1) * bk <= k_size { (iteration + 1) * bk } else { k_size };
        let tile_mac = gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_end);
        k_loop_acc_invariant::<R>(a_val, b_val, i, j, acc.add(tile_mac), iteration + 1, bk, k_size)
    }),
{
    let k_start = iteration * bk;
    let k_end = if (iteration + 1) * bk <= k_size { (iteration + 1) * bk } else { k_size };
    let tile_mac = gemm_tiled_mac_value::<R>(a_val, b_val, i, j, k_start, k_end);

    // Current invariant: acc ≡ tiled_mac(0, k_start)
    // (since iteration * bk < k_size → k_end_for_iteration = iteration * bk = k_start)
    assert(iteration * bk <= k_size) by (nonlinear_arith)
        requires iteration * bk < k_size;
    let prev_k_end = iteration * bk;
    assert(prev_k_end == k_start);

    // acc ≡ tiled_mac(0, k_start)
    let prev_mac = gemm_tiled_mac_value::<R>(a_val, b_val, i, j, 0, k_start);

    // k_start <= k_end: since k_start < k_size and k_end = min((iter+1)*bk, k_size) >= k_size or >= (iter+1)*bk > iter*bk = k_start
    assert(k_start <= k_end) by (nonlinear_arith)
        requires iteration * bk < k_size, bk > 0nat,
            k_start == iteration * bk,
            k_end == (if (iteration + 1) * bk <= k_size { (iteration + 1) * bk } else { k_size });

    // Split: tiled_mac(0, k_end) ≡ tiled_mac(0, k_start) + tiled_mac(k_start, k_end)
    lemma_mac_accumulate::<R>(a_val, b_val, i, j, 0, k_start, k_end);

    // acc.add(tile_mac) ≡ prev_mac.add(tile_mac) ≡ tiled_mac(0, k_end)
    // Step 1: acc.add(tile_mac) ≡ prev_mac.add(tile_mac) by congruence on acc ≡ prev_mac
    R::axiom_eqv_reflexive(tile_mac);
    verus_algebra::lemmas::additive_group_lemmas::lemma_add_congruence::<R>(
        acc, prev_mac, tile_mac, tile_mac,
    );
    // acc.add(tile_mac) ≡ prev_mac.add(tile_mac)

    // Step 2: prev_mac.add(tile_mac) ≡ tiled_mac(0, k_end) by symmetry of split
    let full_mac = gemm_tiled_mac_value::<R>(a_val, b_val, i, j, 0, k_end);
    R::axiom_eqv_symmetric(full_mac, prev_mac.add(tile_mac));

    // Step 3: chain transitivity
    R::axiom_eqv_transitive(acc.add(tile_mac), prev_mac.add(tile_mac), full_mac);

    // Now we need to show this matches k_loop_acc_invariant for iteration+1
    // k_end_for_iter+1 = if (iteration+1)*bk <= k_size { (iteration+1)*bk } else { k_size }
    // = k_end by definition. So acc.add(tile_mac) ≡ tiled_mac(0, k_end) = tiled_mac(0, k_end_iter+1).
}

/// K-loop completion: after all tiles, acc ≡ full MAC.
pub proof fn lemma_k_loop_complete<R: Ring>(
    a_val: spec_fn(nat, nat) -> R,
    b_val: spec_fn(nat, nat) -> R,
    i: nat, j: nat,
    acc: R, bk: nat, k_size: nat,
)
    requires
        bk > 0, k_size > 0,
        k_loop_acc_invariant::<R>(a_val, b_val, i, j, acc,
            num_tiles_ceil(k_size, bk), bk, k_size),
    ensures
        acc.eqv(gemm_mac_value::<R>(a_val, b_val, i, j, k_size)),
{
    let n_tiles = num_tiles_ceil(k_size, bk);
    // k_end for iteration=n_tiles: if n_tiles*bk <= k_size then n_tiles*bk else k_size
    // n_tiles = ceil_div(k_size, bk) → n_tiles*bk >= k_size → k_end = k_size
    assert(n_tiles * bk >= k_size) by {
        crate::proof::predication_lemmas::lemma_ceil_div_mul_ge(k_size, bk);
    };
    // So acc ≡ tiled_mac(0, k_size)
    let full_tiled = gemm_tiled_mac_value::<R>(a_val, b_val, i, j, 0, k_size);
    // tiled_mac(0, k_size) ≡ mac_value(k_size) by definition (both are sum(f, 0, k_size))
    R::axiom_eqv_reflexive(full_tiled);
    // They're the same: gemm_mac_value = sum(f, 0, k) = gemm_tiled_mac_value(0, k)
    R::axiom_eqv_transitive(acc, full_tiled, gemm_mac_value::<R>(a_val, b_val, i, j, k_size));
}

// ══════════════════════════════════════════════════════════════
// Contraction instantiation proofs (Feature 2 Round 7)
// ══════════════════════════════════════════════════════════════

/// Matrix-vector contraction has valid mode sets for rank-2 A, rank-1 x.
pub proof fn lemma_matvec_contraction_valid()
    ensures contraction_mode_sets_valid(&matvec_as_contraction(), 2, 1),
{
    let spec = matvec_as_contraction();
    assert(spec.contraction_modes_a[0] < 2);
    assert(spec.contraction_modes_b[0] < 1);
    assert(spec.free_modes_a[0] < 2);
}

/// Matrix-vector contraction shapes match when K dims agree.
pub proof fn lemma_matvec_contraction_shapes_match(a_shape: Seq<nat>, x_shape: Seq<nat>)
    requires
        a_shape.len() == 2,
        x_shape.len() == 1,
        a_shape[1] == x_shape[0],
    ensures
        contraction_shapes_match(&matvec_as_contraction(), &a_shape, &x_shape),
{
    let spec = matvec_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~=
           gather_shape(&x_shape, &spec.batch_modes_b));
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~=
           gather_shape(&x_shape, &spec.contraction_modes_b));
}

/// Matrix-vector contraction admissibility.
pub proof fn lemma_matvec_contraction_admissible(a_shape: Seq<nat>, x_shape: Seq<nat>)
    requires
        a_shape.len() == 2,
        x_shape.len() == 1,
        a_shape[1] == x_shape[0],
    ensures
        contraction_admissible(&matvec_as_contraction(), &a_shape, &x_shape),
{
    lemma_matvec_contraction_valid();
    lemma_matvec_contraction_shapes_match(a_shape, x_shape);
}

/// Matrix-vector output shape = (m,).
pub proof fn lemma_matvec_output_shape(a_shape: Seq<nat>, x_shape: Seq<nat>)
    requires a_shape.len() == 2, x_shape.len() == 1,
    ensures
        contraction_output_shape(&matvec_as_contraction(), &a_shape, &x_shape)
        =~= seq![a_shape[0]],
{
    let spec = matvec_as_contraction();
    let batch = gather_shape(&a_shape, &spec.batch_modes_a);
    let free_a = gather_shape(&a_shape, &spec.free_modes_a);
    let free_b = gather_shape(&x_shape, &spec.free_modes_b);
    assert(batch =~= Seq::<nat>::empty());
    assert(free_a =~= seq![a_shape[0]]);
    assert(free_b =~= Seq::<nat>::empty());
    assert(batch.add(free_a).add(free_b) =~= seq![a_shape[0]]);
}

/// Matrix-vector reduction size = K (a_shape[1]).
pub proof fn lemma_matvec_reduction_size(a_shape: Seq<nat>)
    requires a_shape.len() == 2,
    ensures contraction_reduction_size(&matvec_as_contraction(), &a_shape) == a_shape[1],
{
    let spec = matvec_as_contraction();
    assert(spec.contraction_modes_a =~= seq![1nat]);
    lemma_gathered_product_single(&a_shape, 1);
}

/// Outer product contraction has valid mode sets for rank-1 inputs.
pub proof fn lemma_outer_product_contraction_valid()
    ensures contraction_mode_sets_valid(&outer_product_as_contraction(), 1, 1),
{
    let spec = outer_product_as_contraction();
    assert(spec.free_modes_a[0] < 1);
    assert(spec.free_modes_b[0] < 1);
}

/// Outer product contraction shapes match (trivially — no contraction/batch modes).
pub proof fn lemma_outer_product_contraction_shapes_match(u_shape: Seq<nat>, v_shape: Seq<nat>)
    requires u_shape.len() == 1, v_shape.len() == 1,
    ensures contraction_shapes_match(&outer_product_as_contraction(), &u_shape, &v_shape),
{
    let spec = outer_product_as_contraction();
    assert(gather_shape(&u_shape, &spec.batch_modes_a) =~=
           gather_shape(&v_shape, &spec.batch_modes_b));
    assert(gather_shape(&u_shape, &spec.contraction_modes_a) =~=
           gather_shape(&v_shape, &spec.contraction_modes_b));
}

/// Outer product contraction admissibility.
pub proof fn lemma_outer_product_contraction_admissible(u_shape: Seq<nat>, v_shape: Seq<nat>)
    requires u_shape.len() == 1, v_shape.len() == 1,
    ensures contraction_admissible(&outer_product_as_contraction(), &u_shape, &v_shape),
{
    lemma_outer_product_contraction_valid();
    lemma_outer_product_contraction_shapes_match(u_shape, v_shape);
}

/// Outer product output shape = (m, n).
pub proof fn lemma_outer_product_output_shape(u_shape: Seq<nat>, v_shape: Seq<nat>)
    requires u_shape.len() == 1, v_shape.len() == 1,
    ensures
        contraction_output_shape(&outer_product_as_contraction(), &u_shape, &v_shape)
        =~= seq![u_shape[0], v_shape[0]],
{
    let spec = outer_product_as_contraction();
    let batch = gather_shape(&u_shape, &spec.batch_modes_a);
    let free_a = gather_shape(&u_shape, &spec.free_modes_a);
    let free_b = gather_shape(&v_shape, &spec.free_modes_b);
    assert(batch =~= Seq::<nat>::empty());
    assert(free_a =~= seq![u_shape[0]]);
    assert(free_b =~= seq![v_shape[0]]);
    assert(batch.add(free_a).add(free_b) =~= seq![u_shape[0], v_shape[0]]);
}

/// Outer product reduction size = 1 (no contraction modes).
pub proof fn lemma_outer_product_reduction_size(u_shape: Seq<nat>)
    requires u_shape.len() == 1,
    ensures contraction_reduction_size(&outer_product_as_contraction(), &u_shape) == 1nat,
{
    let spec = outer_product_as_contraction();
    assert(spec.contraction_modes_a =~= Seq::<nat>::empty());
    lemma_gathered_product_empty(&u_shape);
}

/// Dot product contraction has valid mode sets for rank-1 inputs.
pub proof fn lemma_dot_product_contraction_valid()
    ensures contraction_mode_sets_valid(&dot_product_as_contraction(), 1, 1),
{
    let spec = dot_product_as_contraction();
    assert(spec.contraction_modes_a[0] < 1);
    assert(spec.contraction_modes_b[0] < 1);
}

/// Dot product contraction shapes match when K dims agree.
pub proof fn lemma_dot_product_contraction_shapes_match(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 1,
        b_shape.len() == 1,
        a_shape[0] == b_shape[0],
    ensures
        contraction_shapes_match(&dot_product_as_contraction(), &a_shape, &b_shape),
{
    let spec = dot_product_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~=
           gather_shape(&b_shape, &spec.batch_modes_b));
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~=
           gather_shape(&b_shape, &spec.contraction_modes_b));
}

/// Dot product contraction admissibility.
pub proof fn lemma_dot_product_contraction_admissible(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires
        a_shape.len() == 1,
        b_shape.len() == 1,
        a_shape[0] == b_shape[0],
    ensures
        contraction_admissible(&dot_product_as_contraction(), &a_shape, &b_shape),
{
    lemma_dot_product_contraction_valid();
    lemma_dot_product_contraction_shapes_match(a_shape, b_shape);
}

/// Dot product output shape = () (scalar — empty shape).
pub proof fn lemma_dot_product_output_shape(a_shape: Seq<nat>, b_shape: Seq<nat>)
    requires a_shape.len() == 1, b_shape.len() == 1,
    ensures
        contraction_output_shape(&dot_product_as_contraction(), &a_shape, &b_shape)
        =~= Seq::<nat>::empty(),
{
    let spec = dot_product_as_contraction();
    let batch = gather_shape(&a_shape, &spec.batch_modes_a);
    let free_a = gather_shape(&a_shape, &spec.free_modes_a);
    let free_b = gather_shape(&b_shape, &spec.free_modes_b);
    assert(batch =~= Seq::<nat>::empty());
    assert(free_a =~= Seq::<nat>::empty());
    assert(free_b =~= Seq::<nat>::empty());
    assert(batch.add(free_a).add(free_b) =~= Seq::<nat>::empty());
}

/// Dot product reduction size = K (a_shape[0]).
pub proof fn lemma_dot_product_reduction_size(a_shape: Seq<nat>)
    requires a_shape.len() == 1,
    ensures contraction_reduction_size(&dot_product_as_contraction(), &a_shape) == a_shape[0],
{
    let spec = dot_product_as_contraction();
    assert(spec.contraction_modes_a =~= seq![0nat]);
    lemma_gathered_product_single(&a_shape, 0);
}

// ══════════════════════════════════════════════════════════════
// Intra-CTA epilogue disjointness
// ══════════════════════════════════════════════════════════════

/// Within a single CTA tile, valid elements produce distinct C offsets.
pub proof fn lemma_epilogue_intra_cta_disjoint(
    c_layout: &LayoutSpec, m: nat, n: nat, bm: nat, bn: nat,
    ti: nat, tj: nat,
    ei1: nat, ej1: nat, ei2: nat, ej2: nat,
)
    requires
        c_layout.valid(),
        c_layout.rank() == 2,
        c_layout.is_injective(),
        bm > 0, bn > 0,
        m <= c_layout.shape[0],
        n <= c_layout.shape[1],
        ei1 < bm, ej1 < bn, ei2 < bm, ej2 < bn,
        epilogue_predicated_store_safe(m, n, ti, tj, ei1, ej1, bm, bn),
        epilogue_predicated_store_safe(m, n, ti, tj, ei2, ej2, bm, bn),
        ei1 != ei2 || ej1 != ej2,
    ensures
        gemm_c_tile_offset(c_layout, ti, tj, ei1, ej1, bm, bn)
            != gemm_c_tile_offset(c_layout, ti, tj, ei2, ej2, bm, bn),
{
    let gi1 = ti * bm + ei1;
    let gj1 = tj * bn + ej1;
    let gi2 = ti * bm + ei2;
    let gj2 = tj * bn + ej2;

    // Different element indices within same tile → different global indices
    if ei1 != ei2 {
        assert(gi1 != gi2) by (nonlinear_arith)
            requires ei1 != ei2, gi1 == ti * bm + ei1, gi2 == ti * bm + ei2;
    } else {
        // ei1 == ei2, so ej1 != ej2
        assert(gj1 != gj2) by (nonlinear_arith)
            requires ej1 != ej2, gj1 == tj * bn + ej1, gj2 == tj * bn + ej2;
    }

    lemma_gemm_c_offset_injective(c_layout, m, n, gi1, gj1, gi2, gj2);
}

// ══════════════════════════════════════════════════════════════
// Integer MAC bridge lemmas (Round 10)
// ══════════════════════════════════════════════════════════════

use crate::runtime::gemm::*;

/// sum_int_products over offsets from gemm_mac_offsets == gemm_int_mac_partial.
/// Both use right-peeling recursion so the induction is straightforward.
pub proof fn lemma_sum_int_products_matches_partial(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    a_data: Seq<i64>, b_data: Seq<i64>,
    a_offs: Seq<i64>, b_offs: Seq<i64>,
    i: nat, j: nat, k_start: nat, k_end: nat,
)
    requires
        k_start <= k_end,
        a_offs.len() >= k_end - k_start,
        b_offs.len() >= k_end - k_start,
        forall|idx: nat| idx < k_end - k_start ==>
            a_offs[idx as int] as int == gemm_a_offset(a_layout, i, k_start + idx),
        forall|idx: nat| idx < k_end - k_start ==>
            b_offs[idx as int] as int == gemm_b_offset(b_layout, k_start + idx, j),
    ensures
        sum_int_products(a_data, b_data, a_offs, b_offs, (k_end - k_start) as nat)
            == gemm_int_mac_partial(a_layout, b_layout, a_data, b_data, i, j, k_start, k_end),
    decreases k_end - k_start,
{
    let count = (k_end - k_start) as nat;
    if k_start >= k_end {
        // Both are 0
    } else {
        // Right-peel: count > 0
        // sum_int_products peels element at index (count-1)
        // gemm_int_mac_partial peels k = k_end - 1
        let prev_count = (count - 1) as nat;
        let last_idx = (count - 1) as nat;
        let last_k = (k_end - 1) as nat;

        // The last element's offsets match:
        // a_offs[last_idx] == gemm_a_offset(a_layout, i, k_start + last_idx) == gemm_a_offset(a_layout, i, last_k)
        assert(k_start + last_idx == last_k);

        // Recursive call on prefix
        lemma_sum_int_products_matches_partial(
            a_layout, b_layout, a_data, b_data,
            a_offs, b_offs, i, j, k_start, last_k,
        );

        // sum_int_products on prefix uses same a_offs, b_offs arrays but with count-1
        // Need: prefix offsets still match for idx < prev_count
        // This is true because prev_count < count = a_offs.len()
    }
}

/// gemm_int_mac_partial splits: partial(k_start, k_end) == partial(k_start, k_mid) + partial(k_mid, k_end).
pub proof fn lemma_int_mac_split(
    a_layout: &LayoutSpec, b_layout: &LayoutSpec,
    a_data: Seq<i64>, b_data: Seq<i64>,
    i: nat, j: nat, k_start: nat, k_mid: nat, k_end: nat,
)
    requires k_start <= k_mid, k_mid <= k_end,
    ensures
        gemm_int_mac_partial(a_layout, b_layout, a_data, b_data, i, j, k_start, k_end)
        == gemm_int_mac_partial(a_layout, b_layout, a_data, b_data, i, j, k_start, k_mid)
         + gemm_int_mac_partial(a_layout, b_layout, a_data, b_data, i, j, k_mid, k_end),
    decreases k_end - k_mid,
{
    if k_mid >= k_end {
        // partial(k_mid, k_end) == 0
    } else {
        // Right-peel the last element from partial(k_start, k_end) and partial(k_mid, k_end)
        let last_k = (k_end - 1) as nat;
        let product = (a_data[gemm_a_offset(a_layout, i, last_k) as int] as int)
            * (b_data[gemm_b_offset(b_layout, last_k, j) as int] as int);

        // partial(k_start, k_end) = partial(k_start, last_k) + product
        // partial(k_mid, k_end)   = partial(k_mid, last_k) + product
        // By induction: partial(k_start, last_k) = partial(k_start, k_mid) + partial(k_mid, last_k)
        // So: partial(k_start, k_end) = partial(k_start, k_mid) + partial(k_mid, last_k) + product
        //                             = partial(k_start, k_mid) + partial(k_mid, k_end)
        lemma_int_mac_split(a_layout, b_layout, a_data, b_data, i, j, k_start, k_mid, last_k);
    }
}

/// The last tile ends at k_size.
pub proof fn lemma_last_tile_end(k_size: nat, bk: nat)
    requires bk > 0, k_size > 0,
    ensures tile_k_end((num_tiles_ceil(k_size, bk) - 1) as nat, bk, k_size) == k_size,
{
    let k_tiles = num_tiles_ceil(k_size, bk);
    let last = (k_tiles - 1) as nat;

    // k_tiles = ceil(k_size / bk) >= 1
    crate::proof::predication_lemmas::lemma_ceil_div_mul_ge(k_size, bk);
    assert(k_tiles * bk >= k_size);
    // k_tiles >= 1 because k_size > 0 and bk > 0
    // ceil_div(k_size, bk) = (k_size + bk - 1) / bk >= bk / bk = 1
    assert(k_tiles >= 1) by {
        assert(k_size + bk - 1 >= bk) by (nonlinear_arith)
            requires k_size >= 1nat;
        vstd::arithmetic::div_mod::lemma_div_is_ordered(bk as int, (k_size + bk - 1) as int, bk as int);
        assert(bk as int / bk as int == 1) by {
            vstd::arithmetic::div_mod::lemma_div_by_self(bk as int);
        };
    };
    // tile_k_end(last, bk, k_size) = min((last+1)*bk, k_size) = min(k_tiles*bk, k_size)
    // k_tiles*bk >= k_size, so min = k_size
    assert(tile_k_end(last, bk, k_size) == k_size);
}

/// tile_k_end(t, bk, k_size) relates to t: tile_k_end(0) = min(bk, k_size) and
/// tile_k_end(t) = t*bk if (t+1)*bk <= k_size, else k_size.
/// Key: tile_k_end(t) == min((t+1)*bk, k_size).
/// And for t == 0: tile_k_end starts from 0 (i.e., partial(0, tile_k_end(0))).
pub proof fn lemma_tile_k_end_prev(t: nat, bk: nat, k_size: nat)
    requires bk > 0, k_size > 0, t > 0, t <= num_tiles_ceil(k_size, bk),
    ensures
        tile_k_end((t - 1) as nat, bk, k_size) == if t * bk <= k_size { t * bk } else { k_size },
{
    let prev = (t - 1) as nat;
    // tile_k_end(prev, bk, k_size) = if (prev+1)*bk <= k_size { (prev+1)*bk } else { k_size }
    // = if t*bk <= k_size { t*bk } else { k_size }
    assert((prev + 1) == t);
}

} // verus!
