import Polyfold
/-! Blind formalization of V7_46 (the text's §7.3, Lemma 7.7 and the paragraph before it,
p. 246; the 2017 book, arXiv 1707.08941, Part II).

Text: for an ep-groupoid `(X, 𝐗)`, `|X|` is a regular topological space, where a space is
regular if for a nonempty closed subset `A` and a point `z ∉ A` there are open `U`, `V` with
`z ∈ U`, `A ⊆ V` and `U ∩ V = ∅`.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0).  `|X|`: `X.OrbitSpace` with the instance found, checked by `rfl`
  (not kept here) to be the quotient topology `coinduced X.π`.
- "regular": the text's definition, stated literally (`IsRegularText`); it is equivalent to
  Mathlib's `RegularSpace` (no T₁ condition is part of it).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_46
open Polyfold

/-- The text's regularity (p. 246): a nonempty closed set and a point outside it have disjoint
open neighbourhoods. -/
def IsRegularText (Y : Type) [TopologicalSpace Y] : Prop :=
  ∀ A : Set Y, A.Nonempty → IsClosed A → ∀ z : Y, z ∉ A →
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ z ∈ U ∧ A ⊆ V ∧ U ∩ V = ∅

/-- Lemma 7.7: the orbit space `|X|` of an ep-groupoid is regular. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    IsRegularText X.OrbitSpace

end RoundTrip.V7_46
