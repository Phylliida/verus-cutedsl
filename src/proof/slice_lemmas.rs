use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;
use crate::slice::*;
use crate::proof::shape_lemmas::*;

verus! {

// ══════════════════════════════════════════════════════════════
// Slice rank
// ══════════════════════════════════════════════════════════════

/// Slicing reduces the rank by 1.
pub proof fn lemma_slice_rank(layout: &LayoutSpec, mode: nat, coord: nat)
    requires
        layout.valid(),
        mode < layout.rank(),
        coord < layout.shape[mode as int],
    ensures
        slice_layout(layout, mode, coord).shape.len() == layout.rank() - 1,
        slice_layout(layout, mode, coord).stride.len() == layout.rank() - 1,
        slice_layout(layout, mode, coord).shape.len()
            == slice_layout(layout, mode, coord).stride.len(),
{
}

// ══════════════════════════════════════════════════════════════
// Slice validity
// ══════════════════════════════════════════════════════════════

/// The sliced layout has a valid shape (all entries > 0).
pub proof fn lemma_slice_shape_valid(layout: &LayoutSpec, mode: nat, coord: nat)
    requires
        layout.valid(),
        mode < layout.rank(),
        coord < layout.shape[mode as int],
    ensures
        shape_valid(slice_layout(layout, mode, coord).shape),
{
    let sl = slice_layout(layout, mode, coord);
    assert forall|i: int| 0 <= i < sl.shape.len() implies #[trigger] sl.shape[i] > 0 by {
        if i < mode as int {
            assert(sl.shape[i] == layout.shape[i]);
        } else {
            assert(sl.shape[i] == layout.shape[i + 1]);
        }
    }
}

/// The sliced layout is valid.
pub proof fn lemma_slice_valid(layout: &LayoutSpec, mode: nat, coord: nat)
    requires
        layout.valid(),
        mode < layout.rank(),
        coord < layout.shape[mode as int],
    ensures
        slice_layout(layout, mode, coord).valid(),
{
    lemma_slice_rank(layout, mode, coord);
    lemma_slice_shape_valid(layout, mode, coord);
}

// ══════════════════════════════════════════════════════════════
// Dice rank and validity
// ══════════════════════════════════════════════════════════════

/// Dicing produces a rank-1 layout.
pub proof fn lemma_dice_rank(layout: &LayoutSpec, mode: nat)
    requires
        layout.valid(),
        mode < layout.rank(),
    ensures
        dice_layout(layout, mode).shape.len() == 1,
        dice_layout(layout, mode).stride.len() == 1,
{
}

/// The diced layout is valid.
pub proof fn lemma_dice_valid(layout: &LayoutSpec, mode: nat)
    requires
        layout.valid(),
        mode < layout.rank(),
    ensures
        dice_layout(layout, mode).valid(),
{
}

// ══════════════════════════════════════════════════════════════
// Dice size
// ══════════════════════════════════════════════════════════════

/// Dice size equals the mode's extent.
pub proof fn lemma_dice_size(layout: &LayoutSpec, mode: nat)
    requires
        layout.valid(),
        mode < layout.rank(),
    ensures
        dice_layout(layout, mode).size() == layout.shape[mode as int],
{
    let d = dice_layout(layout, mode);
    assert(shape_size(d.shape)
        == d.shape.first() * shape_size(d.shape.skip(1)));
    assert(d.shape.skip(1).len() == 0);
    vstd::arithmetic::mul::lemma_mul_basics(d.shape.first() as int);
}

// ══════════════════════════════════════════════════════════════
// Slice at mode 0: simplest case
// ══════════════════════════════════════════════════════════════

/// Slicing at mode 0 removes the first element of shape and stride.
pub proof fn lemma_slice_mode0(layout: &LayoutSpec, coord: nat)
    requires
        layout.valid(),
        layout.rank() > 0,
        coord < layout.shape[0],
    ensures
        slice_layout(layout, 0, coord).shape =~= layout.shape.skip(1),
        slice_layout(layout, 0, coord).stride =~= layout.stride.skip(1),
{
    let sl = slice_layout(layout, 0, coord);
    assert forall|i: int| 0 <= i < sl.shape.len()
    implies #[trigger] sl.shape[i] == layout.shape.skip(1)[i] by {
        assert(sl.shape[i] == layout.shape.remove(0)[i]);
        assert(layout.shape.remove(0)[i] == layout.shape[i + 1]);
        assert(layout.shape.skip(1)[i] == layout.shape[i + 1]);
    }
    assert forall|i: int| 0 <= i < sl.stride.len()
    implies #[trigger] sl.stride[i] == layout.stride.skip(1)[i] by {
        assert(sl.stride[i] == layout.stride.remove(0)[i]);
        assert(layout.stride.remove(0)[i] == layout.stride[i + 1]);
        assert(layout.stride.skip(1)[i] == layout.stride[i + 1]);
    }
}

// ══════════════════════════════════════════════════════════════
// Slice at last mode: also simple
// ══════════════════════════════════════════════════════════════

/// Slicing at the last mode removes the last element of shape and stride.
pub proof fn lemma_slice_last_mode(layout: &LayoutSpec, coord: nat)
    requires
        layout.valid(),
        layout.rank() > 0,
        coord < layout.shape.last(),
    ensures ({
        let mode = (layout.rank() - 1) as nat;
        &&& slice_layout(layout, mode, coord).shape =~= layout.shape.take(mode as int)
        &&& slice_layout(layout, mode, coord).stride =~= layout.stride.take(mode as int)
    }),
{
    let mode = (layout.rank() - 1) as nat;
    let sl = slice_layout(layout, mode, coord);
    assert forall|i: int| 0 <= i < sl.shape.len()
    implies #[trigger] sl.shape[i] == layout.shape.take(mode as int)[i] by {
        assert(sl.shape[i] == layout.shape.remove(mode as int)[i]);
    }
    assert forall|i: int| 0 <= i < sl.stride.len()
    implies #[trigger] sl.stride[i] == layout.stride.take(mode as int)[i] by {
        assert(sl.stride[i] == layout.stride.remove(mode as int)[i]);
    }
}

} // verus!
