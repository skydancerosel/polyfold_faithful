import Polyfold
/-! Blind formalization of V3_50 (the text's §3.6, Theorem 3.56, p. 115). Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`, Definition 2.37) and an *equivalent* strong bundle atlas all of whose
  charts have a tame base retraction (`ScRetraction.IsTame`, Definition 2.34).  A property of the
  given structure (an existential over atlases), not "every compatible chart is tame".
- "`∂X = ∅`": `PX.boundary = ∅` (`MPolyfold.boundary`, Definition 2.25: `{x | d_X(x) ≥ 1}`).
- "`f` an sc-Fredholm section" (of the tame strong bundle, §3.6): `IsScFredholmSectionTame`
  (Definition 3.51, Definition 3.14 with the germ data in tame strong bundle charts).
- `S = {f = 0}`: `solutionSet P f`.
- "surjective linearization at every point of `S`": `StrongBundle.IsLinSurjAt` (in some strong
  bundle chart around `x`, at the level-`1` point over `φ(x)`, `D(f̂ ∘ r)(z)|_{T_zO}` maps onto the
  fibre `K_z`).  A hypothesis, so the existential over charts is the weakest (intrinsic) reading.
- "`S` is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold without
  boundary": `PX.IsSubMPolyfold S` (Definition 2.20); `S` paracompact (an instance argument of the
  induced structure `subPolyfold`, Proposition 2.21; asserted as part of the claim, it is true);
  and the induced structure has an *equivalent* atlas of charts onto open subsets of
  finite-dimensional spaces with the constant sc-structure and the identity retraction
  (`HasBoundarylessManifoldStructure`, defined here: corner charts in the sense of
  `MChart.IsCornerChart` whose partial quadrant is the whole space).  The dimension may vary from
  chart to chart, as nothing in the statement fixes it.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_50
open Polyfold

/-- The M-polyfold `QZ` has an equivalent atlas of charts onto open subsets of finite-dimensional
spaces with the constant sc-structure: a compatible smooth manifold structure without boundary. -/
def HasBoundarylessManifoldStructure {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (QZ : MPolyfold Z) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧ ∀ χ ∈ A.charts,
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
      (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
      χ.model = LocalModel.ofRelOpen hU

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

/-- Theorem 3.56 (global implicit function theorem, `∂X = ∅`): if the sc-Fredholm section `f` of a
tame strong bundle has surjective linearization at every zero, then `S = {f = 0}` is a
sub-M-polyfold whose induced structure is equivalent to a smooth manifold without boundary. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → PX.boundary = ∅ → Bd.IsScFredholmSectionTame f →
    (∀ x ∈ solutionSet P f, Bd.IsLinSurjAt f x) →
      ∃ (hS : PX.IsSubMPolyfold (solutionSet P f)) (_ : ParacompactSpace (solutionSet P f)),
        HasBoundarylessManifoldStructure (PX.subPolyfold hS)

end RoundTrip.V3_50
