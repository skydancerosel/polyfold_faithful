import Polyfold
/-! Blind formalization of V2_13 (the text's §2.2, Definition 2.14, p. 24).

Text: `f : X → Y` (between M-polyfolds) is sc-smooth if, for charts `φ` around `x` and `φ'`
around `f(x)` with `f(V) ⊆ V'`, the map `φ' ∘ f ∘ φ⁻¹ : O → O'` is sc-smooth (Definition 2.7);
"the definition does not depend on the choice of charts".

Choices:
- This item is a definition plus a property.  Setting: `X Y : Type` (spaces put in `Type`; the
  project's `MPolyfold` is universe-polymorphic, this is the instance `u = v = 0`) with
  `[TopologicalSpace] [T2Space] [ParacompactSpace]` and M-polyfold structures `P : MPolyfold X`,
  `Q : MPolyfold Y` (Definition 2.13; the project's `MPolyfold`, checked with `#print`: one
  `MAtlas` of pairwise compatible `MChart`s covering the space, standing for its equivalence
  class).  A chart (Definition 2.11) is a project `MChart` (checked in my
  `RoundTrip/Blind/V2_10.lean`: a local model `(O, C, E)` and a homeomorphism `φ : V → O`, `V`
  open).
- "chart (of `X`) around `x`": an `MChart X` with `P.IsChart φ` (checked with `#print`: `φ` is
  compatible with every chart of `P.atlas`, i.e. `φ` lies in an atlas of the equivalence class —
  the maximal atlas) and `x ∈ φ.source`.
- "f is sc-smooth if for charts ... with `f(V) ⊆ V'`": read as the definition "for every
  `x ∈ X` there are charts `φ` around `x`, `φ'` around `f(x)` with `f(V) ⊆ V'` and
  `φ' ∘ f ∘ φ⁻¹` sc-smooth" (`IsScSmoothB`), and the quoted independence as the property: if `f`
  is sc-smooth then for EVERY `x` and EVERY such pair of charts the representative is sc-smooth.
  The two conjuncts together say the existential and the universal readings agree, so B covers
  both readings.  Continuity of `f` is not written into `IsScSmoothB`: it follows from the
  existential condition (the representative is sc⁰, hence continuous, and the charts are
  homeomorphisms); if the text's definition assumes `f` continuous, nothing changes.
- `φ' ∘ f ∘ φ⁻¹` is the total map `φ' ∘ f ∘ φ.symm : E₀ → E'₀` (`φ.symm` is the inverse of the
  chart, meaningful on `O`, checked); only its values on `O` matter.  "sc-smooth (Definition
  2.7)" between the retracts `(O, C, E)` and `(O', C', E')`: `IsScSmoothRetractMapB` (maps `O`
  into `O'` and `g ∘ r` is sc-smooth for SOME retraction `r` onto `O`, as in
  `RoundTrip/Blind/V2_6.lean`).
- B: the project's `P.IsScSmoothMap Q f` (Definition 2.14) is equivalent to `IsScSmoothB`, and the
  independence property holds.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_13
open Polyfold

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]

/-- The representative `φ' ∘ f ∘ φ⁻¹ : O → O'` of `f` in the charts `φ`, `φ'` is sc-smooth
(Definition 2.7). -/
def RepScSmoothB (f : X → Y) (φ : MChart X) (ψ : MChart Y) : Prop :=
  IsScSmoothRetractMapB φ.model.E φ.model.C φ.model.O ψ.model.E ψ.model.O
    ((ψ.toPartialEquiv : Y → ψ.model.E.lvl 0) ∘ f ∘ φ.symm)

/-- **Definition 2.14**: `f : X → Y` is sc-smooth: every `x ∈ X` has charts `φ` around `x` and
`φ'` around `f(x)` with `f(V) ⊆ V'` and `φ' ∘ f ∘ φ⁻¹` sc-smooth. -/
def IsScSmoothB (P : MPolyfold X) (Q : MPolyfold Y) (f : X → Y) : Prop :=
  ∀ x : X, ∃ (φ : MChart X) (ψ : MChart Y), P.IsChart φ ∧ Q.IsChart ψ ∧ x ∈ φ.source ∧
    Set.MapsTo f φ.source ψ.source ∧ RepScSmoothB f φ ψ

end

/-- Definition 2.14: the project's sc-smooth maps between M-polyfolds are the text's, and the
definition does not depend on the choice of charts. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : MPolyfold X) (Q : MPolyfold Y) (f : X → Y),
    -- the definition
    (P.IsScSmoothMap Q f ↔ IsScSmoothB P Q f) ∧
    -- independence of the charts
    (IsScSmoothB P Q f →
      ∀ (x : X) (φ : MChart X) (ψ : MChart Y), P.IsChart φ → Q.IsChart ψ → x ∈ φ.source →
        Set.MapsTo f φ.source ψ.source → RepScSmoothB f φ ψ)

end RoundTrip.V2_13
