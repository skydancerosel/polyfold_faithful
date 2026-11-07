import Polyfold
/-! Blind formalization of V7_48 (the text's §7.3, before Definition 7.14, p. 247; the 2017
book, arXiv 1707.08941, Part II).

Text: for a general ep-groupoid `X`, the induced topology on a given subset of `|X|` is again
locally metrizable, regular and Hausdorff.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0), and an arbitrary subset `A ⊆ |X|`.  `|X|`: `X.OrbitSpace` with
  the instance found, checked by `rfl` (not kept here) to be the quotient topology `coinduced X.π`;
  `A` carries the subspace topology (`↥A`).
- "locally metrizable" (as in Lemma 7.4): every point of `A` has a neighbourhood `V`, open in
  `A`, whose subspace topology is metrizable (`LocallyMetrizable ↥A`).
- "regular": the text's definition (p. 246), stated literally (`IsRegularText`, Mathlib's
  `RegularSpace` without T₁); "Hausdorff": Mathlib's `T2Space`.
- B is the conjunction of the three claims for every subset.  Nothing looks false to me.
-/
namespace RoundTrip.V7_48
open Polyfold

/-- Locally metrizable: every point has an open neighbourhood whose subspace topology is
metrizable. -/
def LocallyMetrizable (Y : Type) [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ TopologicalSpace.MetrizableSpace V

/-- The text's regularity (p. 246): a nonempty closed set and a point outside it have disjoint
open neighbourhoods. -/
def IsRegularText (Y : Type) [TopologicalSpace Y] : Prop :=
  ∀ A : Set Y, A.Nonempty → IsClosed A → ∀ z : Y, z ∉ A →
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ A ⊆ V ∧ U ∩ V = ∅

/-- Every subset of the orbit space `|X|` of an ep-groupoid, with the induced topology, is
locally metrizable, regular and Hausdorff. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (A : Set X.OrbitSpace),
    LocallyMetrizable A ∧ IsRegularText A ∧ T2Space A

end RoundTrip.V7_48
