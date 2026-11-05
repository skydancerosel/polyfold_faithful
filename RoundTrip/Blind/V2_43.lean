import Polyfold
/-! Blind formalization of V2_43 (the text's §2.4, Definition 2.37, p. 42).

Text: a tame M-polyfold is an M-polyfold with an equivalent atlas whose charts are all modelled on
tame sc-smooth retracts.

Choices:
- This item is a definition (no further property asserted), so B says the project's notion
  `MPolyfold.IsTame` is equivalent to my rendering `IsTameMB` of the text's definition.
- Setting: `X : Type` (spaces in `Type`; the project's `MPolyfold` is universe-polymorphic, this
  is `u = 0`) with `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]` and `P : MPolyfold X`
  (Definition 2.13; `P.atlas` is its atlas).  Atlases are the project's `MAtlas X` (checked with
  `#print`: a set of charts, pairwise compatible, covering `X`), charts `MChart X` with their
  local model `φ.model = (O, C, E)`.
- "Equivalent atlas" (Definition 2.12: the union of the two atlases is an atlas): my `EquivB`,
  every two charts of `A.charts ∪ B.charts` are compatible (`MChart.Compatible`, Definition 2.11,
  checked: both transition maps sc-smooth between the overlap retracts); covering is automatic
  for a union of atlases.  I did not use the project's `MAtlas.Equiv` (which asks for an atlas
  whose chart set is the union; equivalent).
- "Modelled on a tame sc-smooth retract": `IsTameRetract φ.model.E φ.model.C φ.model.O`
  (Definition 2.34, checked with `#print`: `O = r(U)` for a tame retraction `r`; my
  `RoundTrip/Blind/V2_40.lean` states this is the text's notion).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_43
open Polyfold

section
variable {X : Type} [TopologicalSpace X]

/-- Definition 2.12: two atlases are equivalent if their union is an atlas, i.e. all charts of the
union are pairwise compatible. -/
def EquivB (A B : MAtlas X) : Prop :=
  ∀ φ ∈ A.charts ∪ B.charts, ∀ ψ ∈ A.charts ∪ B.charts, φ.Compatible ψ

/-- Definition 2.37: an M-polyfold is tame if it has an equivalent atlas all of whose charts are
modelled on tame sc-smooth retracts. -/
def IsTameMB [T2Space X] [ParacompactSpace X] (P : MPolyfold X) : Prop :=
  ∃ A : MAtlas X, EquivB A P.atlas ∧
    ∀ φ ∈ A.charts, IsTameRetract φ.model.E φ.model.C φ.model.O

end

/-- Definition 2.37: the project's tame M-polyfolds are the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame ↔ IsTameMB P

end RoundTrip.V2_43
