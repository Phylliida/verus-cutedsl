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

/// Remove all size-1 modes from a layout (they contribute nothing to the offset).
pub open spec fn remove_unit_modes(layout: LayoutSpec) -> LayoutSpec {
    let indices = filter_non_unit(layout.shape, 0);
    LayoutSpec {
        shape: gather(layout.shape, indices),
        stride: gather(layout.stride, indices),
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
