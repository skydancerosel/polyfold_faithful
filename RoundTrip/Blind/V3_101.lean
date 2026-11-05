import Polyfold
/-! Blind formalization of V3_101 (the text's §3.1, Theorem 3.19, p. 74, and §3.6, Theorem 3.56,
p. 115, both with the hypothesis "`f'(x)` surjective").  `B` is the conjunction of the two
claims.  Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- The quote gives no setting of its own; I use the settings of the two theorems as the text states
  them (as in my blind files V3_68 and V3_50): (3.19) `f` an sc-Fredholm section of a strong bundle
  (no tameness; `StrongBundle.IsScFredholmSection`, Definition 3.14, germ data in some compatible
  chart); (3.56) a *tame* strong bundle and `f` an sc-Fredholm section in the sense of §3.6
  (`IsScFredholmSectionTame`, Definition 3.51).  Doubt: the project's docstring of
  `IsScFredholmSection` says the text states Definition 3.14 for tame strong bundles; if (3.19)
  presupposes tameness, conjunct (3.19) here is stronger than the text.
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart
  is tame".
- `d_X ≡ 0`: `MPolyfold.IsWithoutBoundary`; `∂X = ∅`: `PX.boundary = ∅` (Definition 2.25).
- `f(x₀) = 0`: `IsZeroAt`; `S = solutionSet P f`.
- "`f'(x)` surjective": `StrongBundle.IsLinSurjAt` (in some strong bundle chart, at the level-`1`
  point over `φ(x)`, `D(f̂ ∘ r)(z)|_{T_zO}` maps onto `K_z`); a hypothesis, so the existential over
  charts is the weakest, intrinsic reading.
- (3.19) "the local solution set is a smooth manifold of dimension the Fredholm index": there is an
  open `U ∋ x₀` such that `S(f, U) = {y ∈ U | f(y) = 0}` is a sub-M-polyfold (Definition 2.20;
  paracompact, an instance argument of `subPolyfold`, asserted, it is true) whose induced structure
  (Proposition 2.21) has an equivalent atlas of charts onto open subsets of `d`-dimensional spaces
  with the constant sc-structure (`HasManifoldStructureOfDim`, defined here; a manifold without
  boundary, as `d_X ≡ 0`), where `d` is the Fredholm index of `f'(x₀)`: in every strong bundle
  chart around `x₀`, the linearization `T_zO → K_z` (`z = φ(x₀)`) is an sc-Fredholm operator
  between the induced sc-subspaces with `scIndex = d` (`ChartLinScFredholm`, as in V3_46/V3_68).
- (3.56) conclusion: `IsSubMPolyfold S`, `S` paracompact (asserted), and the induced structure has
  an equivalent atlas of charts onto open subsets of finite-dimensional spaces
  (`HasBoundarylessManifoldStructure`, defined here; the dimension may vary from chart to chart).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_101
open Polyfold

/-- The M-polyfold `QZ` has an equivalent atlas of charts onto open subsets of `d`-dimensional
spaces with the constant sc-structure: a compatible smooth `d`-manifold structure without
boundary. -/
def HasManifoldStructureOfDim {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) (d : ℕ) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧ ∀ χ ∈ A.charts,
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
      (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
      Module.finrank ℝ V = d ∧ χ.model = LocalModel.ofRelOpen hU

/-- The M-polyfold `QZ` has an equivalent atlas of charts onto open subsets of finite-dimensional
spaces with the constant sc-structure: a compatible smooth manifold structure without boundary. -/
def HasBoundarylessManifoldStructure {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (QZ : MPolyfold Z) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧ ∀ χ ∈ A.charts,
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
      (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
      χ.model = LocalModel.ofRelOpen hU

/-- `S(f, U) = {y ∈ U | f(y) = 0}`. -/
def zeroSetIn {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y)
    (U : Set X) : Set X :=
  {y | y ∈ U ∧ IsZeroAt P f y}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- In the strong bundle chart `c` around `x`, with `z = φ(x)` (lifted to `z₁ ∈ E₁`), the
linearization `D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` is an sc-Fredholm operator of index `i` between
the sc-subspaces `T_zO = Dr(z)E ⊆ E` and `K_z = {h | (z, h) ∈ K} ⊆ F` (induced sc-structures). -/
def ChartLinScFredholm (c : StrongBundleChart PX P) (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
  ∃ Kz : Submodule ℝ (c.F.lvl 0),
    (Kz : Set (c.F.lvl 0)) = {h | (c.φ.toPartialEquiv x, h) ∈ c.K} ∧
  ∃ (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)))
    (hK : c.F.IsScSubspace Kz)
    (L₀ : ↥(c.φ.model.E.levelSub (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) 0) →L[ℝ]
      ↥(c.F.levelSub Kz 0)),
    (∀ v, (L₀ v : c.F.lvl 0) =
      scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ (v : c.φ.model.E.lvl 0)) ∧
    ∃ hL : @IsScOperator (c.φ.model.E.ofSubspace hT) (c.F.ofSubspace hK) L₀,
      IsScFredholm hL.toScOperator ∧ scIndex hL.toScOperator = i

end

/-- (3.19) For `d_X ≡ 0` and `f'(x₀)` onto at a zero `x₀`, the local solution set is a smooth
manifold of dimension the Fredholm index; (3.56) for a tame strong bundle with `∂X = ∅` and `f'`
onto at every zero, `S` is a sub-M-polyfold equivalent to a smooth manifold without boundary. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    PX.IsWithoutBoundary → Bd.IsScFredholmSection f → IsZeroAt P f x₀ →
    Bd.IsLinSurjAt f x₀ →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f U)) (_ : ParacompactSpace (zeroSetIn P f U)),
          ∃ d : ℕ, HasManifoldStructureOfDim (PX.subPolyfold hS) d ∧
            ∀ c : StrongBundleChart PX P, Bd.IsChart c → x₀ ∈ c.φ.source →
              ChartLinScFredholm c f x₀ d) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → PX.boundary = ∅ → Bd.IsScFredholmSectionTame f →
    (∀ x ∈ solutionSet P f, Bd.IsLinSurjAt f x) →
      ∃ (hS : PX.IsSubMPolyfold (solutionSet P f)) (_ : ParacompactSpace (solutionSet P f)),
        HasBoundarylessManifoldStructure (PX.subPolyfold hS))

end RoundTrip.V3_101
