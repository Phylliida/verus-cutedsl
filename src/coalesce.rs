use vstd::prelude::*;
use crate::shape::*;
use crate::layout::*;

verus! {

/// Two adjacent modes (i, i+1) are coalesceable if stride[i+1] == shape[i] * stride[i].
/// This means they tile contiguously: the "next row" starts exactly where the "current row" ends.
pub open spec fn modes_coalesceable(layout: &LayoutSpec, i: int) -> bool
    recommends layout.valid(), 0 <= i < layout.shape.len() as int - 1,
{
    layout.stride[i + 1] == (layout.shape[i] as int) * layout.stride[i]
}

/// Coalesce a single pair of adjacent modes at position i.
/// Merges modes i and i+1 into a single mode of size shape[i]*shape[i+1] with stride stride[i].
pub open spec fn coalesce_pair(layout: LayoutSpec, i: nat) -> LayoutSpec
    recommends
        layout.valid(),
        (i as int) < layout.shape.len() as int - 1,
        modes_coalesceable(&layout, i as int),
{
    let ii = i as int;
    let new_shape = layout.shape.take(ii)
        .add(seq![layout.shape[ii] * layout.shape[ii + 1]])
        .add(layout.shape.skip(ii + 2));
    let new_stride = layout.stride.take(ii)
        .add(seq![layout.stride[ii]])
        .add(layout.stride.skip(ii + 2));
    LayoutSpec { shape: new_shape, stride: new_stride }
}

/// Coalesce all coalesceable adjacent pairs, scanning left to right.
/// When a pair is coalesced, re-check the same position (the merged mode might
/// coalesce with its new neighbor). When not coalesceable, advance to the next position.
pub open spec fn coalesce_pass(layout: LayoutSpec, start: nat) -> LayoutSpec
    decreases layout.shape.len() as int - start as int,
{
    if start as int >= layout.shape.len() as int - 1 {
        layout
    } else if modes_coalesceable(&layout, start as int) {
        coalesce_pass(coalesce_pair(layout, start), start)
    } else {
        coalesce_pass(layout, start + 1)
    }
}

/// Full coalesce: scan from position 0 and merge all adjacent coalesceable pairs.
pub open spec fn coalesce(layout: LayoutSpec) -> LayoutSpec {
    coalesce_pass(layout, 0)
}

/// Remove all size-1 modes from a layout (they contribute nothing to the offset).
pub open spec fn remove_unit_modes(layout: LayoutSpec) -> LayoutSpec {
    let indices = filter_non_unit(layout.shape, 0);
    LayoutSpec {
        shape: gather(layout.shape, indices),
        stride: gather(layout.stride, indices),
    }
}

/// Remove all size-1 modes iteratively, scanning from position `pos`.
/// Each removal drops one mode, preserving the layout's offset function.
pub open spec fn remove_units_iter(layout: LayoutSpec, pos: nat) -> LayoutSpec
    decreases layout.shape.len() as int - pos as int,
{
    if pos as int >= layout.shape.len() as int {
        layout
    } else if layout.shape[pos as int] == 1 {
        let removed = LayoutSpec {
            shape: layout.shape.take(pos as int).add(layout.shape.skip(pos as int + 1)),
            stride: layout.stride.take(pos as int).add(layout.stride.skip(pos as int + 1)),
        };
        remove_units_iter(removed, pos)
    } else {
        remove_units_iter(layout, pos + 1)
    }
}

/// Gather elements from a sequence at specified indices.
pub open spec fn gather<A>(s: Seq<A>, indices: Seq<int>) -> Seq<A>
    decreases indices.len(),
{
    if indices.len() == 0 {
        seq![]
    } else {
        seq![s[indices.first()]].add(gather(s, indices.skip(1)))
    }
}

/// Filter out indices where shape[i] == 1.
pub open spec fn filter_non_unit(shape: Seq<nat>, start: int) -> Seq<int>
    decreases (shape.len() - start) as nat,
{
    if start >= shape.len() {
        seq![]
    } else if shape[start] > 1 {
        seq![start].add(filter_non_unit(shape, start + 1))
    } else {
        filter_non_unit(shape, start + 1)
    }
}

} // verus!
