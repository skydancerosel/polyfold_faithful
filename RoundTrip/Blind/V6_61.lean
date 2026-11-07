import Polyfold
/-! Blind formalization of V6_61 (the text's §6.5, Theorem 6.41 and its proof, p. 229; the
paragraph after it, pp. 229–230).

Text: over a tame `X`, for a proper sc-Fredholm section `f` with `(f, x)` in general position at
every zero and an orientation `o^f` of `f`, the solution set `S = f⁻¹(0)` is a smooth compact
manifold with boundary with corners with a natural orientation.  Proof: `T_xS = ker f'(x)` is
oriented by `o^f_x` since `f'(x)` is onto, and the local prolongation of this orientation on `S` is
the Fredholm one.  For `f` not generic, a small perturbation `s` supported near the zero set
orients `S_{f+s}`.

Choices:
- B is the conjunction of (1) Theorem 6.41 and (2) the sentence on the non-generic case.
- Setting: `X Y : Type` (universe 0), `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances, `Bd : StrongBundle PX P`; paracompactness of `ℝⁿ × X` and of the
  pulled-back bundles as instance binders (true anyway; arguments of the push-forward vocabulary).
- "tame `X`": `PX.IsTame` (Definition 2.37).  "sc-Fredholm": `Bd.IsScFredholmSection f`
  (Definition 3.14; the orientation vocabulary is indexed by such a proof).  "proper": the
  project's `Bd.IsProper f` (Definition 5.4 (3)).  "`(f, x)` in general position" at every zero:
  the project's `Bd.IsGeneralPositionGerm f x` (Definition 5.17 in a tame chart; audited in V5_31).
- "an orientation `o^f` of `f`": a map `y ↦ o_y ∈ Or_y^f` (`Orx`, trusted) satisfying the text's
  Definition 6.40, `D640` (copied from my `V6_60.lean`, with the sc-smoothly contractible
  orientable neighbourhoods of Definition 6.36; NOT the project's `IsSectionOrientation`).
- "smooth compact manifold with boundary with corners" (as in `RoundTrip/Blind/V5_40.lean`):
  `S` compact, a sub-M-polyfold (Definition 2.20) whose induced structure (`subPolyfold`,
  paracompactness asserted) has a compatible manifold-with-corners structure
  (`HasCornerStructure`, Definition 4.1).
- "the natural orientation": at a zero `y`, `T_yS = ker f'(y)` is oriented by `o^f_y` through
  `det f'(y) = λ(ker f'(y)) ⊗ λ*({0}) ≅ λ(ker f'(y))`: the project's `tangentOrAt` (read in a
  chart `c` at `y`, `ker f'(y)` the kernel `c.linKer f z_y ⊆ E₀` of the linearization at the
  level-`1` lift `z_y`; trusted), applied to `o_y` read in `c` (`toChartOr`).  "It is an
  orientation of `S`" / "the local prolongation of this orientation on `S` is the Fredholm one":
  my `TangentOrContinuous`: every `x₀ ∈ S` has a chart `c`, an open `W ∋ x₀` in its domain and
  maps `v₁, …, vₙ : X → E₀`, continuous on `W ∩ S`, which at every `y ∈ W ∩ S` form a basis of
  `ker f'(y)` (their wedge is non-zero, `n = dim ker f'(y)`) whose wedge lies in the ray of the
  natural orientation.  (A continuous orientation of the line bundle `λ(TS)`, `T_yS = ker f'(y)`
  in the chart.)  The smoothness `y ∈ X_∞` and the surjectivity `f'(y)` onto (`IsLinSurjAt`) of a
  zero `y`, needed to state it, are universally quantified proofs (they hold: Theorem 5.7,
  general position).
- The non-generic case, read as: for every sc⁺-section `s` (`Bd.IsScPlusSection s`) such that
  `f + s` (`sectionAdd`, fibrewise sum) is proper and in general position at all its zeros
  ("small, supported near the zero set" is what makes `f + s` proper; the existence of such `s`
  is Chapter 5, not restated), `S_{f+s}` is a compact manifold with corners and `o^f` orients
  it: there is an orientation `o'` of `f + s` (Definition 6.40) agreeing with `o^f` at every common
  linearization (`orEquivRay`, in every chart: `DET(f + s, y)` and `DET(f, y)` are the same bundle
  over the same set `Lin`), whose natural orientation of `S_{f+s}` is continuous.  That `f + s` is
  sc-Fredholm (Chapter 3) is a universally quantified proof `hfs`.
- Nothing looks false to me, with one doubt: the hypothesis `D640` constrains `o` only on
  orientable neighbourhoods, so the continuity conclusion relies on such neighbourhoods existing
  around the points of `S` (Theorem 6.35, which the text proves with Proposition 6.28 (3), (4),
  sc⁺-sections through given points); B uses only the text's hypotheses.
-/
namespace RoundTrip.V6_61
open Polyfold

/-- The solution set `S_g = {x | g(x) = 0_x}`. -/
def solSet {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (g : X → Y) : Set X :=
  {x | IsZeroAt P g x}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- `S` is a compact manifold with boundary with corners, as a sub-M-polyfold with its induced
structure. -/
def IsCompactCornerManifold (PX : MPolyfold X) (S : Set X) : Prop :=
  IsCompact S ∧ ∃ (hS : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
    (PX.subPolyfold hS).HasCornerStructure

/-- `U` is **sc-smoothly contractible**: an sc-smooth `H : ℝ¹ × X → X` on an open neighbourhood of
`[0, 1] × U`, mapping `[0, 1] × U` into `U`, with `H(1, ·) = id` and `H(0, ·)` constant on `U`. -/
def IsScContractibleB (PX : MPolyfold X) (U : Set X) : Prop :=
  ∃ (H : (Fin 1 → ℝ) × X → X) (y₀ : X) (W : Set ((Fin 1 → ℝ) × X)),
    IsOpen W ∧ Set.Icc (0 : Fin 1 → ℝ) 1 ×ˢ U ⊆ W ∧
    ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W ∧
    (∀ t ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ∀ y ∈ U, H (t, y) ∈ U) ∧
    (∀ y ∈ U, H (pt1 1, y) = y) ∧ (∀ y ∈ U, H (pt1 0, y) = y₀)

/-- **Definition 6.40** (the text's): `y ↦ o_y` is a continuous orientation on every orientable
neighbourhood (open, sc-smoothly contractible, local propagation property in the chart `c`). -/
def D640 {Bd : StrongBundle PX P} (f : X → Y) (hf : Bd.IsScFredholmSection f)
    (o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy) : Prop :=
  ∀ x ∈ PX.smoothSet, ∀ (U : Set X) (c : StrongBundleChart PX P) (hc : Bd.IsChart c)
    (hUc : U ⊆ c.φ.source),
    IsOpen U → x ∈ U → IsScContractibleB PX U → HasLocalPropagation f hf c hc U →
      IsContinuousOrientation f hf c hc hUc (le_refl U)
        (fun y hy hys => toChartOr hf hys c hc (hUc hy) (o y hys))

/-- **The natural orientation of `S_g` is continuous**: near every zero `x₀` there are a chart `c`
and maps `v₁, …, vₙ : X → E₀`, continuous on `W ∩ S_g`, forming at every zero `y ∈ W` a basis of
`T_yS = ker g'(y)` whose wedge is in the ray given by `o_y` (`tangentOrAt`). -/
def TangentOrContinuous (Bd : StrongBundle PX P) (g : X → Y) (hg : Bd.IsScFredholmSection g)
    (o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx g hg y hy) : Prop :=
  ∀ x₀ ∈ solSet P g, ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (W : Set X)
    (hWc : W ⊆ c.φ.source), IsOpen W ∧ x₀ ∈ W ∧
    ∃ (n : ℕ) (v : Fin n → X → c.φ.model.E.lvl 0), (∀ i, ContinuousOn (v i) (W ∩ solSet P g)) ∧
      ∀ (y : X) (hyW : y ∈ W) (hz : IsZeroAt P g y) (hys : y ∈ PX.smoothSet)
        (hsurj : Bd.IsLinSurjAt g y),
        ∃ (hmem : ∀ i, v i y ∈ c.linKer g (chartPtOf c hc (hWc hyW) hys).z)
          (hn : n = Module.finrank ℝ (c.linKer g (chartPtOf c hc (hWc hyW) hys).z))
          (hne : wedge (fun i => (⟨v i y, hmem i⟩ : c.linKer g (chartPtOf c hc (hWc hyW) hys).z))
            hn ≠ 0),
          rayOfNeZero ℝ _ hne =
            tangentOrAt g hg c hc (hWc hyW) hys hz hsurj (toChartOr hg hys c hc (hWc hyW) (o y hys))

/-- `o'` (an orientation of `f + s`) is induced by `o` (an orientation of `f`): at every smooth
`y`, in every chart, the two agree at every common linearization. -/
def IsInducedOr {Bd : StrongBundle PX P} {f g : X → Y} (hf : Bd.IsScFredholmSection f)
    (hg : Bd.IsScFredholmSection g) (o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy)
    (o' : (y : X) → (hy : y ∈ PX.smoothSet) → Orx g hg y hy) : Prop :=
  ∀ (y : X) (hys : y ∈ PX.smoothSet) (c : StrongBundleChart PX P) (hc : Bd.IsChart c)
    (hy : y ∈ c.φ.source)
    (L : (chartPtOf (B := Bd) c hc hy hys).T →L[ℝ] (chartPtOf (B := Bd) c hc hy hys).K)
    (hL : L ∈ ChartPoint.linSet f (chartPtOf c hc hy hys))
    (hL' : L ∈ ChartPoint.linSet g (chartPtOf c hc hy hys)),
    ChartPoint.orEquivRay _ hg hL' (toChartOr hg hys c hc hy (o' y hys)) =
      ChartPoint.orEquivRay _ hf hL (toChartOr hf hys c hc hy (o y hys))

end

/-- Theorem 6.41: over a tame `X`, for `f` proper sc-Fredholm in general position at its zeros and
an orientation `o^f`, `S = f⁻¹(0)` is a compact manifold with boundary with corners naturally
oriented by `o^f`; and for an sc⁺-perturbation `s` with `f + s` proper and generic, `o^f` orients
`S_{f+s}`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f)
    (o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy),
    PX.IsTame → Bd.IsProper f → D640 f hf o →
    -- (1) Theorem 6.41
    ((∀ x, IsZeroAt P f x → Bd.IsGeneralPositionGerm f x) →
      IsCompactCornerManifold PX (solSet P f) ∧ TangentOrContinuous Bd f hf o) ∧
    -- (2) the non-generic case: an sc⁺-perturbation making `f + s` proper and generic
    (∀ (s : X → Y), Bd.IsScPlusSection s →
      ∀ hfs : Bd.IsScFredholmSection (sectionAdd P f s),
      Bd.IsProper (sectionAdd P f s) →
      (∀ x, IsZeroAt P (sectionAdd P f s) x → Bd.IsGeneralPositionGerm (sectionAdd P f s) x) →
        IsCompactCornerManifold PX (solSet P (sectionAdd P f s)) ∧
        ∃ o' : (y : X) → (hy : y ∈ PX.smoothSet) → Orx (sectionAdd P f s) hfs y hy,
          D640 (sectionAdd P f s) hfs o' ∧ IsInducedOr hf hfs o o' ∧
          TangentOrContinuous Bd (sectionAdd P f s) hfs o')

end RoundTrip.V6_61
