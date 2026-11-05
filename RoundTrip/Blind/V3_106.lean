import Polyfold
/-! Blind formalization of V3_106 (the text's §3.1, Theorem 3.18, p. 74, for tame germ data).
Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51); `n : ℕ`.
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart is
  tame".
- "sc-Fredholm section" with tame germ data (the item's title): `IsScFredholmSectionTame`
  (Definition 3.51), both for `f` and for the section of the pull-back bundle.
- `s₁, …, sₙ ∈ Γ⁺(P)`: `s : Fin n → X → Y` with `Bd.IsScPlusSection (s i)` (Definition 2.52).
- `ℝⁿ × X` is the product M-polyfold `(rnPolyfold n).prod PX` (`ℝⁿ` with its single identity
  chart and the constant sc-structure); `π : ℝⁿ × X → X` is `Prod.snd`, and `π*(P)` is
  `Bd.pullback hπ` (Proposition 2.54, the pull-back bundle with the pulled-back atlas).
  Side conditions that the text takes for granted are hypotheses of `B` (all are true facts, needed
  only to *form* these objects): `ℝⁿ × X` and the pull-back space `π*Y` are paracompact
  (instance arguments of `MPolyfold.prod` and `StrongBundle.pullback`; Lean does not find them
  automatically), and `π` is sc-smooth (`hπ`, the argument of `StrongBundle.pullback`; by proof
  irrelevance the bundle does not depend on the proof).
- The section `(r, x) ↦ f(x) + Σ rᵢ sᵢ(x)`: `paramSection f hf s hs` (the fibre combination in
  `P⁻¹(x)`, regarded as a point of the fibre of `π*Y` over `(r, x)`).  It needs the proofs that `f`
  and the `sᵢ` are sections (`IsSection`), taken as hypotheses (they follow from the others).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_106
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

/-- Theorem 3.18 (tame germ data): for an sc-Fredholm section `f` of a tame strong bundle and
sc⁺-sections `s₁, …, sₙ`, `(r, x) ↦ f(x) + Σ rᵢ sᵢ(x)` is an sc-Fredholm section of the pull-back
bundle `π*(P) → ℝⁿ × X`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (n : ℕ) (f : X → Y) (s : Fin n → X → Y)
    [ParacompactSpace ((Fin n → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (hπ : ((rnPolyfold n).prod PX).IsScSmoothMap PX Prod.snd)
    (hf : IsSection P f) (hs : ∀ i, IsSection P (s i)),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → (∀ i, Bd.IsScPlusSection (s i)) →
      (Bd.pullback hπ).IsScFredholmSectionTame (paramSection f hf s hs)

end RoundTrip.V3_106
