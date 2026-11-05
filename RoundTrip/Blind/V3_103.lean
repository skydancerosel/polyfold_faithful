import Polyfold
/-! Blind formalization of V3_103 (the text's §3.6, Definitions 3.50, 3.51, p. 110; Definition 3.53,
p. 111; the tame strong bundle retraction, p. 49). Choices:
- This item is definitions.  Following the convention of the earlier blind definition files
  (V3_13, V3_16, V3_45, V3_47), `B` states that the project's notions are the text's ones, written
  out here; `B` is the conjunction of four equivalences:
  (i) tame strong bundle chart: the project's `StrongBundle.IsTameChart` iff the chart is a strong
      bundle chart of the bundle (`StrongBundle.IsChart`, compatible with its atlas) whose strong
      bundle retraction is tame, i.e. ("a strong bundle retraction is tame when its base retraction
      `r` is", p. 49) whose base retraction is tame (`ScRetraction.IsTame` of `baseRetraction`,
      Definition 2.34): `K → O` is a tame strong local bundle;
  (ii) (3.50) the project's `IsScFredholmGermTame` iff `IsFredGermB` (below);
  (iii) (3.51) the project's `IsScFredholmSectionTame` iff `IsFredSectionB` (below);
  (iv) (3.53) the project's `IsGoodPositionGermTame` iff `IsGoodPositionB` (below).
- Setting: `X Y : Type` (universe 0; nothing depends on it), `PX : MPolyfold X`, `P : Y → X` with
  the fibrewise linear structure as instances, `Bd : StrongBundle PX P` (Definition 2.51).  "The
  tame strong bundle": `IsTameStrongBundle` (as in the earlier blind files: tame base and an
  *equivalent* strong bundle atlas of charts with tame base retractions — a property of the given
  structure, not "every compatible chart is tame"), a hypothesis of (ii)–(iv).  "`f` an sc-smooth
  section": `StrongBundle.IsScSmoothSection` (Definition 2.52), a hypothesis of (ii)–(iv) (the
  text's setting of 3.50; in 3.51 "an sc-smooth section ... is sc-Fredholm if ...").
- (3.50) `IsFredGermB f x` (copied from my V3_45): `x` is a smooth point; there is a strong bundle
  chart `c` of the bundle around `x` covering `φ : (V, x) → (O, 0)` (`φ(x) = 0`) whose local strong
  bundle `K → O` is tame (base retraction tame); in it the principal part `f̂`
  (`StrongBundleChart.principal`) has a filling `(g, 0)` in the text's germ sense (`IsFillingB`:
  `g` an sc-smooth germ on an sc-germ of neighbourhoods, conditions (1)–(3) of Definition 3.4 near
  `0`, (3) as a topological linear isomorphism `ker Dr(0) ≃ ker ρ(0)` agreeing with `Dk(0)`); there
  is a local sc⁺-section `s : U₀ → F¹`, sc-smooth on a relatively open neighbourhood `U₀ ⊆ U` of
  `0` in `C`, with `s(0) = g(0)`; and `g − s` is conjugated near `0` to a basic germ on `U₀`
  (`IsConjugateToBasicGerm U₀ (g − s)`, the project's rendering of Definition 3.11's second
  paragraph, trusted).
- (3.51) `IsFredSectionB f` (copied from V3_45; sc-smoothness is the hypothesis): (1) `f` is
  regularizing: `x ∈ X_m` and `f(x) ∈ Y_{m,m+1}` imply `x ∈ X_{m+1}` (the project's `levelSet` and
  `StrongBundle.doubleLevel`, the text's `X_m`, `Y_{m,k}`); (2) `IsFredGermB f x` at every smooth
  point `x`.
- (3.53) "Good position is defined for an sc-Fredholm germ of a tame strong bundle" at a zero `x`
  (`IsZeroAt`, a hypothesis of (iv)): `IsGoodPositionB` (as in my V3_47, but with the germ
  condition `IsFredGermB` of (3.50) written out instead of the project's `IsScFredholmGermTame`):
  `(f, x)` is an sc-Fredholm germ (3.50), and in a strong bundle chart centred at `x` (`0 ∈ U`)
  with tame local bundle, with `D` a derivative family of `f̂ ∘ r` as an sc¹-germ at `0`,
  (1) `f'(x) = D(0)|_{T₀O} : T₀O → K₀` is onto (`T₀O = range Dr(0)`, `K₀ = {k | (0, k) ∈ K}`), and
  (2) if `d_X(x) ≥ 1` (`PX.degIndex`), `ker D(0) ∩ T₀O` is in good position to the partial cone
  `C₀O = T₀O ∩ C` in `T₀O` (Definition 3.21 with an sc-complement, `IsInGoodPositionSc`).  The
  linear conditions are chart independent, so their chart may differ from the germ's chart.
- Doubt (recorded, not adjusted): the text's filling and sc⁺-section are germs; if the project
  requires them on the whole chart domain, the `←` directions of (ii)–(iv) need shrinking of
  charts.
- Nothing in the text looks false to me.
-/
namespace RoundTrip.V3_103
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

/-- Definition 3.21 inside the subspace `T`, with an sc-complement: `N ⊆ T`, `N ∩ C` has nonempty
interior in `N`, and `N` has an sc-complement `P` in `T` (`T_m = N_m ⊕ P_m` on every level) such
that `n ∈ C ⟺ n + p ∈ C` for `n ∈ N`, `p ∈ P`, `|p|₀ ≤ ε|n|₀`. -/
def IsInGoodPositionSc (E : ScBanach) (T : Submodule ℝ (E.lvl 0)) (C : Set (E.lvl 0))
    (N : Submodule ℝ (E.lvl 0)) : Prop :=
  N ≤ T ∧ (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧
    ∃ Pc : Submodule ℝ (E.lvl 0), Pc ≤ T ∧ E.IsScSubspace Pc ∧
      (∀ m, E.levelSub N m ⊓ E.levelSub Pc m = ⊥ ∧
        E.levelSub N m ⊔ E.levelSub Pc m = E.levelSub T m) ∧
      ∃ ε > 0, ∀ n ∈ N, ∀ p ∈ Pc, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- A strong bundle chart of the bundle whose local strong bundle `K → O` is tame: its strong
bundle retraction is tame, i.e. its base retraction `r` is tame (p. 49). -/
def IsTameChartB (Bd : StrongBundle PX P) (c : StrongBundleChart PX P) : Prop :=
  Bd.IsChart c ∧ (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- **Definition 3.50** (Definition 3.11 for a tame strong bundle): `(f, x)` is an sc-Fredholm germ:
in a strong bundle chart centred at the smooth point `x` whose local strong bundle is tame, the
principal part has a filling `(g, 0)`, and there is a local sc⁺-section `s` with `s(0) = g(0)` such
that `g − s` is conjugated near `0` to a basic germ. -/
def IsFredGermB (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  x ∈ PX.smoothSet ∧
    ∃ c : StrongBundleChart PX P, IsTameChartB Bd c ∧
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

/-- The tangent space `T₀O = Dr(0)E` of the chart's retract at `0`. -/
noncomputable def tangent0 (c : StrongBundleChart PX P) : Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range
    (scDeriv c.U (StrongRetr.r c.R) 0 : c.φ.model.E.lvl 0 →ₗ[ℝ] c.φ.model.E.lvl 0)

/-- **Definition 3.53**: the sc-Fredholm germ `(f, x)` (at a zero `x`) of the tame strong bundle is
in good position: it is an sc-Fredholm germ (3.50) and, in a strong bundle chart centred at `x`
with tame local bundle, (1) `f'(x) = D(f̂ ∘ r)(0)|_{T₀O} : T₀O → K₀` is onto, and (2) if
`d_X(x) ≥ 1`, its kernel is in good position to the partial cone `C₀O = T₀O ∩ C` in `T₀O`. -/
def IsGoodPositionB (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  IsFredGermB Bd f x ∧
    ∃ c : StrongBundleChart PX P, IsTameChartB Bd c ∧
      x ∈ c.φ.source ∧ c.φ.toPartialEquiv x = 0 ∧ 0 ∈ c.U ∧
      ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (D : c.φ.model.E.lvl 1 → c.φ.model.E.lvl 0 →L[ℝ] c.F.lvl 0),
        G.U 0 ⊆ c.U ∧ IsSc1GermWith G (c.principal f ∘ StrongRetr.r c.R) D ∧
        -- (1) `f'(x) : T_xX → Y_x` is surjective
        (∀ k : c.F.lvl 0, ((0 : c.φ.model.E.lvl 0), k) ∈ c.K →
          ∃ v ∈ tangent0 c, D 0 v = k) ∧
        -- (2) if `d_X(x) ≥ 1`, `ker f'(x)` is in good position to `C_xX` in `T_xX`
        (1 ≤ PX.degIndex x →
          IsInGoodPositionSc c.φ.model.E (tangent0 c)
            ((tangent0 c : Set (c.φ.model.E.lvl 0)) ∩ c.φ.model.C)
            (LinearMap.ker (D 0 : c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓ tangent0 c))

end

/-- Definitions 3.50, 3.51, 3.53 in a tame chart: the project's tame strong bundle charts,
sc-Fredholm germs, sc-Fredholm sections and germs in good position are the text's. -/
def B : Prop :=
  -- (i) a tame strong bundle chart: a chart of the bundle with tame base retraction
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (c : StrongBundleChart PX P),
      Bd.IsTameChart c ↔ IsTameChartB Bd c) ∧
  -- (ii) Definition 3.50
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f →
      (Bd.IsScFredholmGermTame f x ↔ IsFredGermB Bd f x)) ∧
  -- (iii) Definition 3.51
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f →
      (Bd.IsScFredholmSectionTame f ↔ IsFredSectionB Bd f)) ∧
  -- (iv) Definition 3.53
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScSmoothSection f → IsZeroAt P f x →
      (Bd.IsGoodPositionGermTame f x ↔ IsGoodPositionB Bd f x))

end RoundTrip.V3_103
