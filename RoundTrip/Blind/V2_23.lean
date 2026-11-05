import Polyfold
/-! Blind formalization of V2_23 (the text's §2.2, Definition 2.20, p. 28).

Text: `A ⊆ X` is a sub-M-polyfold if every `a ∈ A` has an open neighbourhood `V` and an
sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`.

Choices:
- This item is a definition; it asserts no further property.  Setting: `X : Type` (spaces in
  `Type`; the project's `MPolyfold` is universe-polymorphic, this is `u = 0`) with
  `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]`, `P : MPolyfold X` (Definition 2.13; see
  my `RoundTrip/Blind/V2_13.lean`).  Charts of `X`: `MChart X` with `P.IsChart φ` (maximal atlas,
  checked with `#print`).
- `r : V → V` is a total map `r : X → X` with `r(V) ⊆ V`; only its values on `V` matter.  "Sc-smooth
  retraction": `r ∘ r = r` on `V` and `r` is sc-smooth as a map of the M-polyfold `V` (an open
  subset of `X`, whose charts are the charts of `X` with domain inside `V`) to itself, in the
  sense of Definition 2.14 read existentially as in V2_13 (`IsScSmoothOnB`: every `x ∈ V` has
  charts `φ` around `x` and `φ'` around `r(x)`, both with domains in `V`, with
  `r(dom φ) ⊆ dom φ'` and `φ' ∘ r ∘ φ⁻¹ : O → O'` sc-smooth in the sense of Definition 2.7,
  existential reading `IsScSmoothRetractMapB`).  V2_13 asserts that this existential reading
  agrees with the universal one.
- B: the project's `P.IsSubMPolyfold A` (Definition 2.20) is equivalent to my `IsSubMPolyfoldB`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_23
open Polyfold

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **Definition 2.14** for a map `f : V → V` of the open subset `V` of `X` (an M-polyfold whose
charts are the charts of `X` with domain in `V`): every `x ∈ V` has charts `φ` around `x` and `φ'`
around `f(x)` in `V` with `f(dom φ) ⊆ dom φ'` and `φ' ∘ f ∘ φ⁻¹` sc-smooth. -/
def IsScSmoothOnB (P : MPolyfold X) (f : X → X) (V : Set X) : Prop :=
  ∀ x ∈ V, ∃ φ ψ : MChart X, P.IsChart φ ∧ P.IsChart ψ ∧ x ∈ φ.source ∧
    φ.source ⊆ V ∧ ψ.source ⊆ V ∧ Set.MapsTo f φ.source ψ.source ∧
    IsScSmoothRetractMapB φ.model.E φ.model.C φ.model.O ψ.model.E ψ.model.O
      ((ψ.toPartialEquiv : X → ψ.model.E.lvl 0) ∘ f ∘ φ.symm)

/-- **Definition 2.20**: `A ⊆ X` is a sub-M-polyfold: every `a ∈ A` has an open neighbourhood
`V` and an sc-smooth retraction `r : V → V` with `r(V) = A ∩ V`. -/
def IsSubMPolyfoldB (P : MPolyfold X) (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∃ r : X → X,
    Set.MapsTo r V V ∧ IsScSmoothOnB P r V ∧ (∀ x ∈ V, r (r x) = r x) ∧ r '' V = A ∩ V

end

/-- Definition 2.20: the project's sub-M-polyfolds are the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsSubMPolyfold A ↔ IsSubMPolyfoldB P A

end RoundTrip.V2_23
