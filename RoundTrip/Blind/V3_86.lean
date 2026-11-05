import Polyfold
/-! Blind formalization of V3_86 (the text's §3.6, Theorem 3.56, p. 115). Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the fibrewise
  linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P`.
- "tame strong bundle": `IsTameStrongBundle` (defined here): tame base (`MPolyfold.IsTame`) and an
  equivalent strong bundle atlas all of whose charts have a tame base retraction
  (`ScRetraction.IsTame`).  A property of the given structure, not "every chart is tame".
- "`∂X = ∅`": `PX.boundary = ∅` (`MPolyfold.boundary`, Definition 2.25: `{x | d_X(x) ≥ 1}`).
- "`f` an sc-Fredholm section": `StrongBundle.IsScFredholmSectionTame` (Definition 3.51, the §3.6
  recall of Definition 3.14 for a tame strong bundle, germ data in a tame chart).
- `S = {f = 0}`: `solutionSet P f`.
- "surjective linearization at every point of `S`": `StrongBundle.IsLinSurjAt` (in some strong
  bundle chart around `x`, at the level-`1` point over `φ(x)`, `D(f̂ ∘ r)(z)|_{T_zO}` maps onto the
  fibre `K_z`).  It is an existential over charts, i.e. a property of the given structure.
- "`S` is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold without
  boundary": `IsSubMPolyfold S` (Definition 2.20), `S` paracompact (needed for the induced
  structure `subPolyfold`, asserted as part of the claim), and the induced structure has an
  equivalent atlas of charts onto *open* subsets of finite-dimensional spaces with the constant
  sc-structure (`HasBoundarylessManifoldStructure`, defined here like `MChart.IsCornerChart` /
  `HasCornerStructure` but with the partial quadrant `C` the whole space).  The dimension may vary
  from component to component, as nothing in the statement fixes it.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_86
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

/-- Theorem 3.56 (global implicit function theorem, `∂X = ∅`): if the linearization of the
sc-Fredholm section `f` is onto at every zero, then `S = {f = 0}` is a sub-M-polyfold whose induced
structure is equivalent to a smooth manifold without boundary. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → PX.boundary = ∅ → Bd.IsScFredholmSectionTame f →
    (∀ x ∈ solutionSet P f, Bd.IsLinSurjAt f x) →
      ∃ (hS : PX.IsSubMPolyfold (solutionSet P f)) (_ : ParacompactSpace (solutionSet P f)),
        HasBoundarylessManifoldStructure (PX.subPolyfold hS)

end RoundTrip.V3_86
