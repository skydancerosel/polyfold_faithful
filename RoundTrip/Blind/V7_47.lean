import Polyfold
/-! Blind formalization of V7_47 (the text's §7.3, Corollary 7.1, p. 247; the 2017 book,
arXiv 1707.08941, Part II).

Text: let `X` be an ep-groupoid whose induced topology `𝒯` on `|X|` is second countable, i.e.
`𝒯` has a countable basis.  Then `|X|` is metrizable.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0).
- "the induced topology `𝒯` on `|X|`": the quotient topology on `X.OrbitSpace` (the instance
  found, checked by `rfl`, not kept here, to be `coinduced X.π`).
- "second countable": Mathlib's `SecondCountableTopology`; "metrizable": Mathlib's
  `TopologicalSpace.MetrizableSpace`.  Nothing looks false to me.
-/
namespace RoundTrip.V7_47
open Polyfold

/-- Corollary 7.1: if the orbit space `|X|` of an ep-groupoid is second countable, it is
metrizable. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    SecondCountableTopology X.OrbitSpace → TopologicalSpace.MetrizableSpace X.OrbitSpace

end RoundTrip.V7_47
