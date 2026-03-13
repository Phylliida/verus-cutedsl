use vstd::prelude::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Tensor contraction generalization (einsum-style)
// ══════════════════════════════════════════════════════════════

/// Mode classification for a tensor contraction.
/// Generalizes GEMM to arbitrary tensor contractions.
pub struct ContractionSpec {
    pub batch_modes_a: Seq<nat>,       // indices into A that are batch dims
    pub batch_modes_b: Seq<nat>,       // corresponding indices into B
    pub contraction_modes_a: Seq<nat>, // indices into A that are summed
    pub contraction_modes_b: Seq<nat>, // corresponding indices into B
    pub free_modes_a: Seq<nat>,        // indices into A that are free (→ output rows)
    pub free_modes_b: Seq<nat>,        // indices into B that are free (→ output cols)
}

/// Gather shapes at the given mode indices.
pub open spec fn gather_shape(shape: &Seq<nat>, modes: &Seq<nat>) -> Seq<nat> {
    Seq::new(modes.len(), |i: int| shape[modes[i] as int])
}

/// All mode indices are valid and non-overlapping, covering all modes.
pub open spec fn contraction_mode_sets_valid(
    spec: &ContractionSpec, rank_a: nat, rank_b: nat,
) -> bool {
    // All indices in range
    &&& forall|i: nat| i < spec.batch_modes_a.len()
        ==> #[trigger] spec.batch_modes_a[i as int] < rank_a
    &&& forall|i: nat| i < spec.batch_modes_b.len()
        ==> #[trigger] spec.batch_modes_b[i as int] < rank_b
    &&& forall|i: nat| i < spec.contraction_modes_a.len()
        ==> #[trigger] spec.contraction_modes_a[i as int] < rank_a
    &&& forall|i: nat| i < spec.contraction_modes_b.len()
        ==> #[trigger] spec.contraction_modes_b[i as int] < rank_b
    &&& forall|i: nat| i < spec.free_modes_a.len()
        ==> #[trigger] spec.free_modes_a[i as int] < rank_a
    &&& forall|i: nat| i < spec.free_modes_b.len()
        ==> #[trigger] spec.free_modes_b[i as int] < rank_b
    // Paired modes have matching counts
    &&& spec.batch_modes_a.len() == spec.batch_modes_b.len()
    &&& spec.contraction_modes_a.len() == spec.contraction_modes_b.len()
    // All A-modes covered: batch + contraction + free = rank_a
    &&& spec.batch_modes_a.len() + spec.contraction_modes_a.len()
        + spec.free_modes_a.len() == rank_a
    // All B-modes covered
    &&& spec.batch_modes_b.len() + spec.contraction_modes_b.len()
        + spec.free_modes_b.len() == rank_b
}

/// Shapes of contracted and batch modes match between A and B.
pub open spec fn contraction_shapes_match(
    spec: &ContractionSpec, a_shape: &Seq<nat>, b_shape: &Seq<nat>,
) -> bool {
    // Batch shapes match
    &&& gather_shape(a_shape, &spec.batch_modes_a)
        =~= gather_shape(b_shape, &spec.batch_modes_b)
    // Contraction shapes match
    &&& gather_shape(a_shape, &spec.contraction_modes_a)
        =~= gather_shape(b_shape, &spec.contraction_modes_b)
}

/// Output shape = batch_shapes ++ free_a_shapes ++ free_b_shapes.
pub open spec fn contraction_output_shape(
    spec: &ContractionSpec, a_shape: &Seq<nat>, b_shape: &Seq<nat>,
) -> Seq<nat> {
    gather_shape(a_shape, &spec.batch_modes_a)
        .add(gather_shape(a_shape, &spec.free_modes_a))
        .add(gather_shape(b_shape, &spec.free_modes_b))
}

/// GEMM is a special case of contraction: no batch modes,
/// contraction on A's column (mode 1) and B's row (mode 0),
/// free modes are A's row (mode 0) and B's column (mode 1).
pub open spec fn gemm_as_contraction() -> ContractionSpec {
    ContractionSpec {
        batch_modes_a: seq![],
        batch_modes_b: seq![],
        contraction_modes_a: seq![1nat],
        contraction_modes_b: seq![0nat],
        free_modes_a: seq![0nat],
        free_modes_b: seq![1nat],
    }
}

/// Batched GEMM: batch on mode 0 of both A and B,
/// contract A's mode 2 with B's mode 1,
/// free modes are A's mode 1 and B's mode 2.
pub open spec fn batched_gemm_as_contraction() -> ContractionSpec {
    ContractionSpec {
        batch_modes_a: seq![0nat],
        batch_modes_b: seq![0nat],
        contraction_modes_a: seq![2nat],
        contraction_modes_b: seq![1nat],
        free_modes_a: seq![1nat],
        free_modes_b: seq![2nat],
    }
}

} // verus!
