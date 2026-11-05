import Polyfold
/-! Blind formalization of V3_45 (the text's §3.6, Definitions 3.50 and 3.51, p. 110). Choices:
- This item is two definitions.  Following the convention of the earlier blind definition
  files, `B` states that the project's notions are the text's ones: (a) the project's
  `StrongBundle.IsScFredholmGermTame` (docstring: Definition 3.50) is equivalent to `IsFredGermB`
  below, and (b) the project's `StrongBundle.IsScFredholmSectionTame` (docstring: Definition 3.51)
  is equivalent to `IsFredSectionB` below, both for an sc-smooth section `f` of a tame strong
  bundle (the standing hypothesis of §3.6).
- Setting: `X Y : Type` (universe 0; nothing depends on it), `PX : MPolyfold X`, `P : Y → X` with
  the fibrewise linear structure as instances, `Bd : StrongBundle PX P` (Definition 2.51).
  "Tame strong bundle": `IsTameStrongBundle` (as in the earlier blind files V3_14/V3_94): tame base
  and an *equivalent* strong bundle atlas of charts with tame base retractions — a property of the
  given structure, not "every compatible chart is tame".  "`f` sc-smooth section": the project's
  `StrongBundle.IsScSmoothSection` (Definition 2.52).
- (3.50) `IsFredGermB f x` (Definition 3.11 with a tame chart): `x` is a smooth point
  (`PX.smoothSet`); there is a strong bundle chart `c` of the bundle (`Bd.IsChart c`: compatible
  with its atlas, Definition 2.50) "where `K → O` is a tame strong local bundle" (the base
  retraction of `c` is tame, `ScRetraction.IsTame`), with `x ∈ dom φ`, `φ(x) = 0`; in it the
  principal part `f̂` (`StrongBundleChart.principal`) has a filling `(g, 0)` in the text's germ
  sense (`IsFillingB`, copied from my V3_43: `g` an sc-smooth germ on an sc-germ of
  neighbourhoods, conditions (1)–(3) of Definition 3.4 near `0`); there is a local sc⁺-section `s`
  of `U ◁ F → U` — `s : U₀ → F¹` sc-smooth on a relatively open neighbourhood `U₀ ⊆ U` of `0` in
  `C` — with `s(0) = g(0)`; and `g − s` is conjugated near `0` to a basic germ on `U₀`
  (`IsConjugateToBasicGerm U₀ (g − s)`, the project's rendering of Definition 3.11's second
  paragraph: a strong bundle isomorphism `U₀ ◁ F → U' ◁ (ℝᴺ ⊕ W)` covering an sc-diffeomorphism
  `ψ` with `ψ(0) = 0` that pushes `g − s` forward to a basic germ near `0`; I trusted it).
- (3.51) `IsFredSectionB f` (Definition 3.14 without "`f` is sc-smooth"): (1) `f` is regularizing:
  `x ∈ X_m` and `f(x) ∈ Y_{m,m+1}` imply `x ∈ X_{m+1}` (the project's `levelSet` and
  `StrongBundle.doubleLevel`, the text's `X_m` and `Y_{m,k}`); (2) `IsFredGermB f x` at every
  smooth point `x`.
- Doubt (recorded, not adjusted): the text's filling and sc⁺-section are local/germs; I expect the
  project's version (filled version sc-smooth on the whole chart domain `U`) to be stronger, so the
  `←` directions may fail.
- Nothing in the text looks false to me.
-/
namespace RoundTrip.V3_45
open Polyfold

/-- The map `k(y) = [1 − ρ(r(y))]g(y)` of Definition 3.4 (3). -/
def fillDefect {E F : ScBanach} (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (g : E.lvl 0 → F.lvl 0) : E.lvl 0 → F.lvl 0 :=
  fun y => g y - StrongRetr.ρ R (StrongRetr.r R y) (g y)

/-- **Definition 3.4 / 3.48**: `(g, 0)` is a filling of the sc-smooth section germ `(f, 0)` of the
tame strong local bundle `K = R(U ◁ F) → O`: `g` is an sc-smooth germ at `0`, (1) `f = g` on `O`
near `0`, (2) zeros of `[1 − ρ(r(·))]g` near `0` lie in `O`, (3) `Dk(0)|_{ker Dr(0)}` is a
topological isomorphism onto `ker ρ(0)`. -/
def IsFillingB {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}
    (_hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : 0 ∈ U)
    (f g : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G g ∧
    -- (1) `f = g` on `O` near `0`
    (∀ᶠ y in nhds (0 : E.lvl 0), y ∈ StrongRetr.r R '' U → f y = g y) ∧
    -- (2) `g(y) = ρ(r(y))g(y)` for `y ∈ U` near `0` forces `y ∈ O`
    (∀ᶠ y in nhds (0 : E.lvl 0),
      y ∈ U → g y = StrongRetr.ρ R (StrongRetr.r R y) (g y) → y ∈ StrongRetr.r R '' U) ∧
    -- (3) `Dk(0) : ker Dr(0) → ker ρ(0)` is a topological linear isomorphism
    ∃ Dk : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0, IsSc1GermWith G (fillDefect R g) Dk ∧
      ∃ e : LinearMap.ker (scDeriv U (StrongRetr.r R) 0 : E.lvl 0 →ₗ[ℝ] E.lvl 0) ≃L[ℝ]
          LinearMap.ker (StrongRetr.ρCLM hR h0 : F.lvl 0 →ₗ[ℝ] F.lvl 0),
        ∀ v, (e v : F.lvl 0) = Dk 0 (v : E.lvl 0)

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- **Definition 3.50** (Definition 3.11 for a tame strong bundle): `(f, x)` is an sc-Fredholm germ:
in a strong bundle chart centred at the smooth point `x` whose local strong bundle is tame, the
principal part has a filling `(g, 0)`, and there is a local sc⁺-section `s` with `s(0) = g(0)` such
that `g − s` is conjugated near `0` to a basic germ. -/
def IsFredGermB (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  x ∈ PX.smoothSet ∧
    ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧
      (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame ∧
      x ∈ c.φ.source ∧ c.φ.toPartialEquiv x = 0 ∧
      ∃ (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
        (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0) (U₀ : Set (c.φ.model.E.lvl 0)),
        IsFillingB c.relOpen c.isRetraction h0 (c.principal f) g ∧
        IsRelOpenInQuadrant c.φ.model.E c.φ.model.C U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ c.U ∧
        @IsScSmooth _ c.F.shift U₀ s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        IsConjugateToBasicGerm U₀ (fun u => g u - c.F.toBase 1 (s u))

/-- **Definition 3.51** (Definition 3.14 for a tame strong bundle, `f` sc-smooth being a standing
hypothesis): `f` is regularizing and `(f, x)` is an sc-Fredholm germ at every smooth point. -/
def IsFredSectionB (Bd : StrongBundle PX P) (f : X → Y) : Prop :=
  (∀ (m : ℕ), ∀ x ∈ PX.levelSet m, f x ∈ Bd.doubleLevel m (m + 1) → x ∈ PX.levelSet (m + 1)) ∧
    ∀ x ∈ PX.smoothSet, IsFredGermB Bd f x

end

/-- Definitions 3.50 and 3.51: for an sc-smooth section `f` of a tame strong bundle, the project's
`IsScFredholmGermTame` and `IsScFredholmSectionTame` are the text's sc-Fredholm germ (in a chart
with tame local bundle) and sc-Fredholm section. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f →
      (Bd.IsScFredholmGermTame f x ↔ IsFredGermB Bd f x)) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f →
      (Bd.IsScFredholmSectionTame f ↔ IsFredSectionB Bd f))

end RoundTrip.V3_45
