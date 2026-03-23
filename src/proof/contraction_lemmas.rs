use vstd::prelude::*;
use crate::contraction::*;
use crate::proof::shape_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Tensor contraction proofs: GEMM and basic cases
// ══════════════════════════════════════════════════════════════

/// GEMM-as-contraction is admissible for 2D tensors with matching inner dimension.
pub proof fn lemma_gemm_contraction_admissible(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 2,
        b_shape.len() == 2,
        a_shape[0] > 0,
        a_shape[1] > 0,
        b_shape[0] > 0,
        b_shape[1] > 0,
        a_shape[1] == b_shape[0],  // K dimensions match
    ensures
        contraction_admissible(&gemm_as_contraction(), &a_shape, &b_shape),
{
    let spec = gemm_as_contraction();
    // Mode sets valid
    assert(contraction_mode_sets_valid(&spec, a_shape.len(), b_shape.len()));
    // Shapes match: contracted dimensions
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~= seq![a_shape[1]]);
    assert(gather_shape(&b_shape, &spec.contraction_modes_b) =~= seq![b_shape[0]]);
    // Batch shapes match (both empty)
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&b_shape, &spec.batch_modes_b) =~= Seq::<nat>::empty());
}

/// GEMM output shape is (M, N) for A[M, K] * B[K, N].
pub proof fn lemma_gemm_contraction_output_shape(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 2,
        b_shape.len() == 2,
    ensures
        contraction_output_shape(&gemm_as_contraction(), &a_shape, &b_shape)
            =~= seq![a_shape[0], b_shape[1]],
{
    let spec = gemm_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&a_shape, &spec.free_modes_a) =~= seq![a_shape[0]]);
    assert(gather_shape(&b_shape, &spec.free_modes_b) =~= seq![b_shape[1]]);
}

/// GEMM contraction reduction size is K (the inner dimension).
pub proof fn lemma_gemm_reduction_size(a_shape: Seq<nat>)
    requires
        a_shape.len() == 2,
        a_shape[1] > 0,
    ensures
        contraction_reduction_size(&gemm_as_contraction(), &a_shape) == a_shape[1],
{
    let spec = gemm_as_contraction();
    assert(spec.contraction_modes_a =~= seq![1nat]);
    // gathered_product with single mode = shape[mode]
    lemma_gathered_product_single(&a_shape, 1nat);
}

/// Batched GEMM is admissible for 3D tensors.
pub proof fn lemma_batched_gemm_admissible(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 3,
        b_shape.len() == 3,
        forall|i: int| 0 <= i < 3 ==> #[trigger] a_shape[i] > 0,
        forall|i: int| 0 <= i < 3 ==> #[trigger] b_shape[i] > 0,
        a_shape[0] == b_shape[0],  // batch dimensions match
        a_shape[2] == b_shape[1],  // K dimensions match
    ensures
        contraction_admissible(&batched_gemm_as_contraction(), &a_shape, &b_shape),
{
    let spec = batched_gemm_as_contraction();
    assert(contraction_mode_sets_valid(&spec, a_shape.len(), b_shape.len()));
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= seq![a_shape[0]]);
    assert(gather_shape(&b_shape, &spec.batch_modes_b) =~= seq![b_shape[0]]);
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~= seq![a_shape[2]]);
    assert(gather_shape(&b_shape, &spec.contraction_modes_b) =~= seq![b_shape[1]]);
}

/// Batched GEMM output shape is (Batch, M, N).
pub proof fn lemma_batched_gemm_output_shape(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 3,
        b_shape.len() == 3,
    ensures
        contraction_output_shape(&batched_gemm_as_contraction(), &a_shape, &b_shape)
            =~= seq![a_shape[0], a_shape[1], b_shape[2]],
{
    let spec = batched_gemm_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= seq![a_shape[0]]);
    assert(gather_shape(&a_shape, &spec.free_modes_a) =~= seq![a_shape[1]]);
    assert(gather_shape(&b_shape, &spec.free_modes_b) =~= seq![b_shape[2]]);
}

/// Matrix-vector contraction is admissible.
pub proof fn lemma_matvec_admissible(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 2,
        b_shape.len() == 1,
        a_shape[0] > 0,
        a_shape[1] > 0,
        b_shape[0] > 0,
        a_shape[1] == b_shape[0],
    ensures
        contraction_admissible(&matvec_as_contraction(), &a_shape, &b_shape),
{
    let spec = matvec_as_contraction();
    assert(contraction_mode_sets_valid(&spec, a_shape.len(), b_shape.len()));
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~= seq![a_shape[1]]);
    assert(gather_shape(&b_shape, &spec.contraction_modes_b) =~= seq![b_shape[0]]);
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&b_shape, &spec.batch_modes_b) =~= Seq::<nat>::empty());
}

/// Matrix-vector output shape is (M,).
pub proof fn lemma_matvec_output_shape(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 2,
        b_shape.len() == 1,
    ensures
        contraction_output_shape(&matvec_as_contraction(), &a_shape, &b_shape)
            =~= seq![a_shape[0]],
{
    let spec = matvec_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&a_shape, &spec.free_modes_a) =~= seq![a_shape[0]]);
    assert(gather_shape(&b_shape, &spec.free_modes_b) =~= Seq::<nat>::empty());
}

/// Dot product contraction is admissible.
pub proof fn lemma_dot_product_contraction_admissible(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 1,
        b_shape.len() == 1,
        a_shape[0] > 0,
        b_shape[0] > 0,
        a_shape[0] == b_shape[0],
    ensures
        contraction_admissible(&dot_product_as_contraction(), &a_shape, &b_shape),
{
    let spec = dot_product_as_contraction();
    assert(contraction_mode_sets_valid(&spec, a_shape.len(), b_shape.len()));
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~= seq![a_shape[0]]);
    assert(gather_shape(&b_shape, &spec.contraction_modes_b) =~= seq![b_shape[0]]);
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&b_shape, &spec.batch_modes_b) =~= Seq::<nat>::empty());
}

/// Dot product output is scalar (empty shape).
pub proof fn lemma_dot_product_output_shape(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 1,
        b_shape.len() == 1,
    ensures
        contraction_output_shape(&dot_product_as_contraction(), &a_shape, &b_shape)
            =~= Seq::<nat>::empty(),
{
    let spec = dot_product_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&a_shape, &spec.free_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&b_shape, &spec.free_modes_b) =~= Seq::<nat>::empty());
}

/// Outer product contraction is admissible.
pub proof fn lemma_outer_product_admissible(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 1,
        b_shape.len() == 1,
        a_shape[0] > 0,
        b_shape[0] > 0,
    ensures
        contraction_admissible(&outer_product_as_contraction(), &a_shape, &b_shape),
{
    let spec = outer_product_as_contraction();
    assert(contraction_mode_sets_valid(&spec, a_shape.len(), b_shape.len()));
    assert(gather_shape(&a_shape, &spec.contraction_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&b_shape, &spec.contraction_modes_b) =~= Seq::<nat>::empty());
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&b_shape, &spec.batch_modes_b) =~= Seq::<nat>::empty());
}

/// Outer product output shape is (M, N).
pub proof fn lemma_outer_product_output_shape(
    a_shape: Seq<nat>, b_shape: Seq<nat>,
)
    requires
        a_shape.len() == 1,
        b_shape.len() == 1,
    ensures
        contraction_output_shape(&outer_product_as_contraction(), &a_shape, &b_shape)
            =~= seq![a_shape[0], b_shape[0]],
{
    let spec = outer_product_as_contraction();
    assert(gather_shape(&a_shape, &spec.batch_modes_a) =~= Seq::<nat>::empty());
    assert(gather_shape(&a_shape, &spec.free_modes_a) =~= seq![a_shape[0]]);
    assert(gather_shape(&b_shape, &spec.free_modes_b) =~= seq![b_shape[0]]);
}

/// Gathered product distributes: adding one mode multiplies by its size.
pub proof fn lemma_gathered_product_append(
    shape: &Seq<nat>, modes: &Seq<nat>, extra_mode: nat,
)
    requires
        forall|i: nat| i < modes.len() ==> #[trigger] modes[i as int] < shape.len(),
        extra_mode < shape.len(),
    ensures
        gathered_product(shape, &modes.push(extra_mode))
            == shape[extra_mode as int] * gathered_product(shape, modes),
{
    assert(modes.push(extra_mode).drop_last() =~= *modes);
}

/// Gathered product of empty modes is 1.
pub proof fn lemma_gathered_product_empty(shape: &Seq<nat>)
    ensures
        gathered_product(shape, &Seq::<nat>::empty()) == 1nat,
{
}

/// Gathered product of single mode equals that shape dimension.
pub proof fn lemma_gathered_product_single(shape: &Seq<nat>, mode: nat)
    requires mode < shape.len(),
    ensures gathered_product(shape, &seq![mode]) == shape[mode as int],
{
    let modes = seq![mode];
    assert(modes.last() == mode);
    assert(modes.drop_last() =~= Seq::<nat>::empty());
    assert(gathered_product(shape, &modes.drop_last()) == 1nat);
    assert(shape[mode as int] * 1nat == shape[mode as int]) by (nonlinear_arith)
        requires shape[mode as int] >= 0;
}

} // verus!
