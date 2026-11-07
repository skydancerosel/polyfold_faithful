import Polyfold
/-! Blind formalization of V7_45 (the text's §7.3, Lemma 7.6, p. 245, proof pp. 245–246; the
2017 book, arXiv 1707.08941, Part II).

Text: the orbit space `|X|` of an ep-groupoid `(X, 𝐗)` is Hausdorff.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0).
- `|X|`: `X.OrbitSpace` (`Quotient` of `Obj` by "there is a morphism `x → y`") with the instance
  found, checked by `rfl` (not kept here) to be the quotient topology `coinduced X.π`.
- "Hausdorff": Mathlib's `T2Space`.  Nothing looks false to me.
-/
namespace RoundTrip.V7_45
open Polyfold

/-- Lemma 7.6: the orbit space `|X|` of an ep-groupoid is Hausdorff. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    T2Space X.OrbitSpace

end RoundTrip.V7_45
