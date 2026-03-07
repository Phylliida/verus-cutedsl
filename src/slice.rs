use vstd::prelude::*;
use crate::layout::*;

verus! {

/// Slice a layout by fixing a coordinate in one mode.
///
/// Given layout L with shape (M_0, ..., M_{k-1}) and stride (d_0, ..., d_{k-1}),
/// `slice(L, mode, coord)` removes mode `mode` and shifts the base offset by `coord * d_mode`.
///
/// Result shape: remove_at(L.shape, mode)
/// Result stride: remove_at(L.stride, mode)
/// The returned layout computes: offset(x) = coord * d_mode + L_rest.offset(x)
///
/// Note: The constant offset (coord * d_mode) is tracked separately.
/// The returned layout is the "residual" after fixing the coordinate.
pub open spec fn slice_layout(layout: &LayoutSpec, mode: nat, coord: nat) -> LayoutSpec
    recommends
        layout.valid(),
        mode < layout.rank(),
        coord < layout.shape[mode as int],
{
    LayoutSpec {
        shape: layout.shape.remove(mode as int),
        stride: layout.stride.remove(mode as int),
    }
}

/// The constant offset produced by slicing (fixing coord in mode).
pub open spec fn slice_offset(layout: &LayoutSpec, mode: nat, coord: nat) -> int
    recommends
        layout.valid(),
        mode < layout.rank(),
        coord < layout.shape[mode as int],
{
    (coord as int) * layout.stride[mode as int]
}

/// Dice: keep only one mode, discarding all others.
///
/// `dice(L, mode)` extracts mode `mode` as a rank-1 layout.
/// Result: shape = (M_mode), stride = (d_mode).
pub open spec fn dice_layout(layout: &LayoutSpec, mode: nat) -> LayoutSpec
    recommends
        layout.valid(),
        mode < layout.rank(),
{
    LayoutSpec {
        shape: seq![layout.shape[mode as int]],
        stride: seq![layout.stride[mode as int]],
    }
}

} // verus!
