import Polyfold
/-! Blind formalization of V3_98 (the text's §6.1, Definition 6.1, pp. 200–201, and Proposition
6.2, p. 201; the statement along the solution set read off §3.6, Theorem 3.54 (1), p. 111), second
blind statement (r2).  `B` is the conjunction of three claims: (0) the index of Definition 6.1 is
well defined, (a) it is constant along the solution set near a zero in good position, (b) it is
constant along sc-smooth paths (Proposition 6.2).  Choices:
- Setting: `X Y : Type` (universe 0, as in the other blind files; nothing depends on it).
  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`,
  `Bd : StrongBundle PX P` (Definition 2.51), `f : X → Y`.
- "sc-Fredholm section": `StrongBundle.IsScFredholmSection` (Definition 3.14, the germ reading) in
  (0) and (b); in (a), the setting of Theorem 3.54: a tame strong bundle (`IsTameStrongBundle`,
  defined here as in my other blind files: tame base and an EQUIVALENT strong bundle atlas whose
  charts have tame base retractions; a property of the structure, not "every chart is tame") and
  `IsScFredholmSectionTame` (Definition 3.51).
- (0): the md attaches no tameness to Definition 6.1, so none is assumed there.  (b): "over a tame
  M-polyfold" is `PX.IsTame` (Definition 2.37); nothing else is assumed of the bundle.  Doubt: if
  Chapter 6 means the sc-Fredholm sections of Definition 3.51 (tame germ data), (b) here has a
  weaker hypothesis than the text.
- Smooth point: `IsSmoothPt PX x := ∀ m, x ∈ PX.levelSet m` (`x ∈ X_∞`).
- The index `ind(f, x) = i` (Definition 6.1) is `HasIndex Bd f x i`, defined here from the
  chart-level data (I did not use the project's `IsIndexAt`/`IsIndexAtLocal`/`IsLinOfIndex`, which
  formalize the very notion under audit): for EVERY strong bundle chart `c` of `Bd`
  (`Bd.IsChart c`) with `x ∈ c.φ.source` and EVERY sc⁺-section `s` of the local strong bundle
  `K → O` of `c` (`IsChartScPlusSection`: principal part `ŝ` with `(y, ŝ y) ∈ K` on `O`, and
  `ŝ ∘ r` lifts to an sc-smooth map `U → F¹`) with `ŝ(z) = f̂(z)`, `z = φ(x)`, the linearization
  `(f − s)'(x)`, read in `c` as `D((f̂ − ŝ) ∘ r)(z)` restricted to `T_zO = Dr(z)E₀` (`rangeS` of
  `scDeriv c.U r z₁`, `z₁` the level-1 lift of `z`), maps into `K_z = {h | (z, h) ∈ K}` and, as a
  linear map `T_zO → K_z` on level 0, is Fredholm of index `i` (`IsFredholmOfIndex`: kernel and
  cokernel finite-dimensional, `dim ker − dim coker = i`).  "Local" sc⁺-sections are covered by
  the quantifier over all charts: a local sc⁺-section near `x` is a whole-chart one in the chart
  restricted to its domain.  The "∀ charts, ∀ s" form encodes "it does not depend on `s`" (and on
  the chart, implicit in the text).  The index is the level-0 Fredholm index (for the sc-Fredholm
  operator `(f − s)'(x)` it is the same on every level); `B` does not claim sc-Fredholmness.
- (0) is `∀` smooth `x`, `∃ i, HasIndex Bd f x i`: the index exists and does not depend on `s`.
- (b) "sc-smooth path `φ : [0, 1] → X`": `γ : ℝ → X` (values off `[0, 1]` ignored) with
  `IsScSmoothPath PX γ`, defined here: around each `t ∈ [0, 1]`, in every chart `φ` of `X` at
  `γ t`, on `J = [0, 1] ∩ (t − ε, t + ε)` the path stays in the chart domain and `s ↦ φ(γ s)` lifts
  to every level `E_m` as a `C^∞` map on `J` (`ContDiffOn` within `J`; one-sided at `0`, `1`).  This
  is sc-smoothness from the manifold with boundary `[0, 1]` (constant sc-structure on `ℝ`), for
  which sc-smooth means `C^∞` into every level.  `ind(f, x₀) = ind(f, x₁)` is
  `∀ i, HasIndex Bd f x₀ i ↔ HasIndex Bd f x₁ i`.
- (a) "the statement along the solution set, implicit in Theorem 3.54 (1)": my reading is that,
  under the hypotheses of Theorem 3.54 (tame strong bundle, Definition 3.51, `f(x) = 0`, `(f, x)` in
  good position: `StrongBundle.IsGoodPositionGermSc`, as in my blind V3_94_r2), there is an open
  `V ∋ x` such that `ind(f, y) = ind(f, x)` for every zero `y ∈ V` (`solutionSet P f`).  This is a
  guess at what the md means; the md gives no precise statement.  No smoothness of `y` is assumed
  (zeros of a regularizing section are smooth).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_98_r2
open Polyfold

/-- A linear map `L : T → K` is Fredholm of index `i`: finite-dimensional kernel and cokernel,
`dim ker L − dim (K / range L) = i`. -/
def IsFredholmOfIndex {T K : Type} [AddCommGroup T] [Module ℝ T] [AddCommGroup K] [Module ℝ K]
    (L : T →ₗ[ℝ] K) (i : ℤ) : Prop :=
  FiniteDimensional ℝ (LinearMap.ker L) ∧ FiniteDimensional ℝ (K ⧸ LinearMap.range L) ∧
    (Module.finrank ℝ (LinearMap.ker L) : ℤ) - (Module.finrank ℝ (K ⧸ LinearMap.range L) : ℤ) = i

/-- The parameter set `[0, 1] ∩ (t − ε, t + ε)`. -/
def pathNbhd (t ε : ℝ) : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ Set.Ioo (t - ε) (t + ε)

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- `x` is a smooth point: `x ∈ X_∞ = ⋂ X_m`. -/
def IsSmoothPt (PX : MPolyfold X) (x : X) : Prop := ∀ m : ℕ, x ∈ PX.levelSet m

/-- `γ|[0, 1]` is an sc-smooth path in `X`: near every `t ∈ [0, 1]`, in every chart `φ` of `X` at
`γ t`, the path stays in the chart domain and `s ↦ φ(γ s)` is `C^∞` (within `[0, 1]`) into every
level `E_m`. -/
def IsScSmoothPath (PX : MPolyfold X) (γ : ℝ → X) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ φ : MChart X, PX.IsChart φ → γ t ∈ φ.source →
    ∃ ε > 0, (∀ s ∈ pathNbhd t ε, γ s ∈ φ.source) ∧
      ∀ m : ℕ, ∃ g : ℝ → φ.model.E.lvl m,
        (∀ s ∈ pathNbhd t ε, φ.model.E.toBase m (g s) = φ.toPartialEquiv (γ s)) ∧
        ∀ n : ℕ, ContDiffOn ℝ n g (pathNbhd t ε)

/-- `ŝ : O → F` is the principal part of an sc⁺-section of the local strong bundle `K → O` of the
chart `c`: `(y, ŝ y) ∈ K` for `y ∈ O`, and `ŝ ∘ r : U → F` lifts to an sc-smooth map `U → F¹`. -/
def IsChartScPlusSection (c : StrongBundleChart PX P) (ŝ : c.φ.model.E.lvl 0 → c.F.lvl 0) :
    Prop :=
  (∀ y ∈ c.φ.model.O, (y, ŝ y) ∈ c.K) ∧
    ∃ σ : c.φ.model.E.lvl 0 → c.F.shift.lvl 0, IsScSmooth c.U σ ∧
      ∀ u ∈ c.U, c.F.shiftIncl.lvl 0 (σ u) = ŝ (StrongRetr.r c.R u)

/-- In the chart `c`, at `z = φ(x)` (lifted to `z₁ ∈ E₁`), the linearization
`D((f̂ − ŝ) ∘ r)(z)|_{T_zO}` maps `T_zO = Dr(z)E₀` into `K_z = {h | (z, h) ∈ K}` and is, as a map
`T_zO → K_z`, Fredholm of index `i`. -/
def ChartLinIndex (c : StrongBundleChart PX P) (f : X → Y) (ŝ : c.φ.model.E.lvl 0 → c.F.lvl 0)
    (x : X) (i : ℤ) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
  ∃ Kz : Submodule ℝ (c.F.lvl 0),
    (Kz : Set (c.F.lvl 0)) = {h | (c.φ.toPartialEquiv x, h) ∈ c.K} ∧
  ∃ L : ↥(rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) →ₗ[ℝ] ↥Kz,
    (∀ v, (L v : c.F.lvl 0) =
      scDeriv c.U ((fun y => c.principal f y - ŝ y) ∘ StrongRetr.r c.R) z₁
        (v : c.φ.model.E.lvl 0)) ∧
    IsFredholmOfIndex L i

/-- Definition 6.1: `ind(f, x) = i`: for every strong bundle chart at `x` and every sc⁺-section
`s` of it with `s(x) = f(x)`, `(f − s)'(x)` is Fredholm of index `i`. -/
def HasIndex (Bd : StrongBundle PX P) (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
    ∀ ŝ : c.φ.model.E.lvl 0 → c.F.lvl 0, IsChartScPlusSection c ŝ →
      ŝ (c.φ.toPartialEquiv x) = c.principal f (c.φ.toPartialEquiv x) →
        ChartLinIndex c f ŝ x i

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

end

/-- Definition 6.1 / Proposition 6.2: (0) at every smooth point the index `ind(f, x)` of
`(f − s)'(x)` exists and does not depend on `s`; (a) near a zero in good position (Theorem 3.54
setting) it is constant along the solution set; (b) over a tame M-polyfold it is the same at the
ends of an sc-smooth path. -/
def B : Prop :=
  -- (0) Definition 6.1: the index is well defined
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    Bd.IsScFredholmSection f →
      ∀ x : X, IsSmoothPt PX x → ∃ i : ℤ, HasIndex Bd f x i) ∧
  -- (a) along the solution set (implicit in Theorem 3.54 (1))
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → x ∈ solutionSet P f →
    Bd.IsGoodPositionGermSc f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, y ∈ solutionSet P f → ∀ i : ℤ, HasIndex Bd f y i ↔ HasIndex Bd f x i) ∧
  -- (b) Proposition 6.2: along sc-smooth paths
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    PX.IsTame → Bd.IsScFredholmSection f →
      ∀ (x₀ x₁ : X) (γ : ℝ → X), IsSmoothPt PX x₀ → IsSmoothPt PX x₁ →
        IsScSmoothPath PX γ → γ 0 = x₀ → γ 1 = x₁ →
          ∀ i : ℤ, HasIndex Bd f x₀ i ↔ HasIndex Bd f x₁ i)

end RoundTrip.V3_98_r2
