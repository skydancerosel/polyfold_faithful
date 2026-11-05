import Polyfold
/-! Blind formalization of V3_91 (the text's §3.1, Theorem 3.18, p. 74). Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51); `n : ℕ`.
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart is
  tame".
- "sc-Fredholm section" (§3.1): Definition 3.14, the project's `StrongBundle.IsScFredholmSection`
  (sc-smooth, regularizing, an sc-Fredholm germ (Definition 3.11) at every smooth point), used for
  `f` and for the section of the pull-back bundle.  Doubt (recorded, from its docstring): the
  project's Definition 3.14 lets the germ data live in any compatible strong bundle chart, while
  the text states Definition 3.14 for tame strong bundles (its fillings, Definition 3.4, are for
  tame local bundles); I used it as the text's notion.  The §3.6 variant with tame germ data
  (Definition 3.51) is the separate blind item V3_106.  The conclusion presupposes that the
  pull-back bundle is tame (true: `ℝⁿ × X` is tame and charts pull back to tame charts); this is
  not claimed separately, as the quote does not claim it.
- `s₁, …, sₙ ∈ Γ⁺(P)`: `s : Fin n → X → Y` with `Bd.IsScPlusSection (s i)` (Definition 2.52).
- `ℝⁿ × X` is the product M-polyfold `(rnPolyfold n).prod PX` (`ℝⁿ` with its identity chart and
  the constant sc-structure); `π : ℝⁿ × X → X` is `Prod.snd`, and `π*(P) : π*Y → ℝⁿ × X` is
  `Bd.pullback hπ` (Proposition 2.54, the pull-back bundle with the pulled-back atlas).  Side
  conditions that the text takes for granted, needed only to *form* these objects, are hypotheses
  of `B` (all are true facts): `ℝⁿ × X` and `π*Y` paracompact (instance arguments of
  `MPolyfold.prod` and `StrongBundle.pullback`), `π` sc-smooth (`hπ`; by proof irrelevance the
  bundle does not depend on the proof).
- The section `(r, x) ↦ f(x) + Σᵢ rᵢ sᵢ(x)`: `paramSection f hf s hs` (the combination computed
  in the fibre `P⁻¹(x)` and regarded as a point of the fibre of `π*Y` over `(r, x)`).  It needs
  the proofs that `f` and the `sᵢ` are sections (`IsSection`), taken as hypotheses (they follow
  from the others).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_91
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

end

/-- Theorem 3.18: for an sc-Fredholm section `f` of a tame strong bundle and sc⁺-sections
`s₁, …, sₙ`, `(r, x) ↦ f(x) + Σ rᵢ sᵢ(x)` is an sc-Fredholm section of the pull-back bundle
`π*(P) → ℝⁿ × X`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (n : ℕ) (f : X → Y) (s : Fin n → X → Y)
    [ParacompactSpace ((Fin n → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (hπ : ((rnPolyfold n).prod PX).IsScSmoothMap PX Prod.snd)
    (hf : IsSection P f) (hs : ∀ i, IsSection P (s i)),
    IsTameStrongBundle Bd → Bd.IsScFredholmSection f → (∀ i, Bd.IsScPlusSection (s i)) →
      (Bd.pullback hπ).IsScFredholmSection (paramSection f hf s hs)

end RoundTrip.V3_91
