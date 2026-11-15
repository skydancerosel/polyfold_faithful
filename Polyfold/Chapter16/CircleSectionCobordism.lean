import Polyfold.Chapter15.CylinderOrientationInvariance
import Polyfold.Chapter16.OrientationNonEffectiveWitness
import Polyfold.Chapter15.Cylinder
import Polyfold.Chapter6.UntamedIndexJump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) on an example with sheets of positive dimension.

# Corollary 15.4.4 for the circle section over `ℝ²`

## What is formalized (namespace `Polyfold.TrivialBundle`)

The example is the trivial bundle `ℝ² × ℝ → ℝ²` over the trivial ep-groupoid of `ℝ²`
(`epSEP 2 1`) with the section `f(x) = (x, x₀² + x₁² − 1)`, whose solution set is the unit circle.

* `centredChartPoint`, `isIndexAt_graphSection_epSEP`: the graph section of a `C^∞` map
  `ℝⁿ → ℝᵏ` has index `n − k` at every point.
* `circleMap`, `circleSection`, `hasCompactSolutionSetEp_circleSection`: the solution set is
  compact.
* `circleSectionOrientation`, `isSectionOrientation_circleSectionOrientation`,
  `isOrInvariant_circleSectionOrientation`: an orientation of `f` (Definitions 6.6.16, 12.5.4).
* **`corollary_15_4_4_hypotheses_circleSection`**: every hypothesis of
  `corollary_15_4_4_oriented` holds with `m = 0`: `d_X ≡ 0`, `|X|` paracompact, sc-smooth
  partitions of unity on `X` and on `[0, 1] × X`, `f` an sc-Fredholm section functor with tame
  germ data, compact solution set and index `1`, oriented; the fibres are non-zero.
* **`corollary_15_4_4_circleSection`**: the conclusion of Corollary 15.4.4 there.

## Reading

The morphisms of the example are units; an example of the invariance of `õ` with isotropy is
`StrongBundleLocalizationExamples.isOrInvariant_cubeOrientation_z3`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15 SEP
  StrongBundleEquivalenceExamples StrongBundleLocalizationExamples

/-! ### The index of a graph section over `ℝⁿ` -/

section Index

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- The chart point of the translation chart centred at `x₀`: the level-`1` point over
`x₀ − x₀ = 0` is `0`. -/
def centredChartPoint (x₀ : Fin n → ℝ) : ChartPoint (bundle n k) x₀ where
  c := chart x₀
  isChart := isChart_chart x₀
  mem_source := mem_univ _
  z := 0
  toBase_z := by rw [map_zero]; exact (sub_self x₀).symm

/-- `T_0O = ℝⁿ` in the chart centred at `x₀`. -/
theorem T_centredChartPoint (x₀ : Fin n → ℝ) : (centredChartPoint (k := k) x₀).T = ⊤ := by
  change rangeS (scDeriv (chart (k := k) x₀).U (r (chart (k := k) x₀).R) 0) = ⊤
  rw [rangeS, scDeriv_r]
  exact LinearMap.range_id

/-- `K_0 = ℝᵏ` in the chart centred at `x₀`. -/
theorem K_centredChartPoint (x₀ : Fin n → ℝ) : (centredChartPoint (k := k) x₀).K = ⊤ :=
  eq_top_iff.2 fun h _ => ⟨h, rfl⟩

instance (x₀ : Fin n → ℝ) : FiniteDimensional ℝ ↥(centredChartPoint (k := k) x₀).T :=
  haveI : FiniteDimensional ℝ ((centredChartPoint (k := k) x₀).c.φ.model.E 0) :=
    (inferInstance : FiniteDimensional ℝ (Fin n → ℝ))
  inferInstance

instance (x₀ : Fin n → ℝ) : FiniteDimensional ℝ ↥(centredChartPoint (k := k) x₀).K :=
  haveI : FiniteDimensional ℝ ((centredChartPoint (k := k) x₀).c.F 0) :=
    (inferInstance : FiniteDimensional ℝ (Fin k → ℝ))
  inferInstance

theorem finrank_T_centredChartPoint (x₀ : Fin n → ℝ) :
    finrank ℝ ↥(centredChartPoint (k := k) x₀).T = n := by
  rw [T_centredChartPoint]
  have h : finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
  exact (finrank_top ℝ _).trans h

theorem finrank_K_centredChartPoint (x₀ : Fin n → ℝ) :
    finrank ℝ ↥(centredChartPoint (k := k) x₀).K = k := by
  rw [K_centredChartPoint]
  have h : finrank ℝ (Fin k → ℝ) = k := Module.finrank_fin_fun ℝ
  exact (finrank_top ℝ _).trans h

/-- **The index of the graph section** (Definition 6.2.1): on `ℝⁿ × ℝᵏ → ℝⁿ` the graph section
of a `C^∞` map `φ` has index `n − k` at every point: a member of `Lin(f, x₀)` is an operator
`ℝⁿ → ℝᵏ` in the chart centred at `x₀`. -/
theorem isIndexAt_graphSection_epSEP (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    (epSEP n k).B.IsIndexAt (graphSection φ) x₀ ((n : ℤ) - (k : ℕ)) := by
  have hf : (bundle n k).IsScFredholmSection (graphSection φ) :=
    (graphSection_mem_fredholmSectionFunctors_epBundle hφ).2
  obtain ⟨L, hL⟩ := (centredChartPoint (k := k) x₀).linSet_nonempty hf
    (by rw [rnPolyfold_smoothSet]; exact mem_univ x₀) (hasScPlusSectionsThrough_epSEP n k)
  have h := ((centredChartPoint (k := k) x₀).isFredholm_isIndexAt_of_mem_linSet hf hL).2
  rwa [fredholmIndex_of_finiteDimensional, finrank_T_centredChartPoint,
    finrank_K_centredChartPoint] at h

end Index

/-! ### Transversality to the zero section -/

section Transversal

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- `Λ₀(f(x)) > 0` iff `φ(x) = 0`, for the multisection `Λ₀` of the zero section. -/
theorem zeroMultisection_graphSection_epSEP_pos_iff (x : Fin n → ℝ) :
    0 < zeroMultisection (epSEP n k) (graphSection φ x) ↔ φ x = 0 := by
  classical
  have aux : ∀ w : (epSEP n k).W, w = graphSection φ x →
      (0 < zeroMultisection (epSEP n k) w ↔ φ x = 0) := by
    intro w hw
    have key : w = fiberZero (epSEP n k).P ((epSEP n k).P w) ↔ φ x = 0 := by
      subst hw
      exact isZeroAt_graphSection_iff (n := n) (k := k) (φ := φ) (x := x)
    unfold zeroMultisection
    by_cases h : w = fiberZero (epSEP n k).P ((epSEP n k).P w)
    · rw [if_pos h]
      exact iff_of_true one_pos (key.1 h)
    · rw [if_neg h]
      exact iff_of_false (lt_irrefl _) fun h' => h (key.2 h')
  exact aux _ rfl

/-- **The graph section of a `C^∞` map with `0` a regular value is transversal to the zero
section** (Definition 15.2.1 for `Λ₀`): at a zero `x₀`, in the chart centred at `x₀`,
`(f − 0)'(x₀) = Dφ(x₀)` is onto `ℝᵏ`. -/
theorem isTransversal_graphSection_epSEP (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x, φ x = 0 → Surjective (fderiv ℝ φ x)) :
    IsTransversal (A := epSEP n k) (graphSection φ) (zeroMultisection (epSEP n k)) := by
  classical
  have hf : (epSEP n k).E.IsScFredholmSectionFunctor (graphSection φ) :=
    graphSection_mem_fredholmSectionFunctors_epBundle hφ
  intro x₀ hpos
  have h0 : φ x₀ = 0 := (zeroMultisection_graphSection_epSEP_pos_iff x₀).1 hpos
  have hx1 : x₀ ∈ (epSEP n k).X.PObj.levelSet 1 := by
    have h : (x₀ : Fin n → ℝ) ∈ (rnPolyfold n).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hpos, hx1, ?_⟩
  set x := (epSEP n k).X.PObj.levelMk 1 x₀ hx1 with hxdef
  intro L hL
  have hxv : (epSEP n k).X.PObj.levelVal 1 x = x₀ := (epSEP n k).X.PObj.levelVal_levelMk _ _ _
  let c : StrongBundleChart (epSEP n k).X.PObj (epSEP n k).P := chart (k := k) x₀
  have hc : (epSEP n k).B.IsChart c := isChart_chart x₀
  have hx : (epSEP n k).X.PObj.levelVal 1 x ∈ c.φ.source := mem_univ _
  have hx0 : graphSection φ ((epSEP n k).X.PObj.levelVal 1 x) =
      fiberZero (epSEP n k).P ((epSEP n k).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (n := n) (k := k) (φ := φ) (x := x₀)).2 h0
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (isScPlusSectionOn_fiberZero isOpen_univ) hc
    (subset_univ _) hx hx0).2 ?_
  set z := levelLift c.φ 1 ((epSEP n k).X.PObj.levelVal 1 x) with hzdef
  have hz : z = 0 := by
    have h1 : c.φ.model.E.toBase 1 z = c.φ ((epSEP n k).X.PObj.levelVal 1 x) :=
      (epSEP n k).X.PObj.toBase_levelLift c.isChart hx ((epSEP n k).X.PObj.levelVal_mem x)
    rw [hxv] at h1
    have h2 : c.φ x₀ = (0 : Fin n → ℝ) := sub_self (show Fin n → ℝ from x₀)
    exact h1.trans h2
  have he : ((fun y => c.principal (graphSection φ) y -
      c.principal (fiberZero (epSEP n k).P) y) ∘ r c.R) = loc φ x₀ := by
    funext u
    have h2 : c.principal (fiberZero (epSEP n k).P) u = 0 :=
      c.snd_fiberZero (x := c.φ.symm u) (mem_univ _)
    change c.principal (graphSection φ) u - c.principal (fiberZero (epSEP n k).P) u = _
    rw [h2, sub_zero]
    rfl
  intro w _
  obtain ⟨v, hv⟩ := hreg x₀ h0 w
  refine ⟨v, ⟨v, ?_⟩, ?_⟩
  · rw [hz]
    exact congrArg (fun T : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => T v) (scDeriv_r (k := k) x₀)
  · change scDeriv c.U ((fun y => c.principal (graphSection φ) y -
      c.principal (fiberZero (epSEP n k).P) y) ∘ r c.R) z v = w
    rw [he, hz]
    exact (congrArg (fun T : (rnSc n) 0 →L[ℝ] (rnSc k) 0 => T v) (scDeriv_loc hφ x₀)).trans hv

end Transversal

/-! ### The circle section -/

/-- `φ(x) = x₀² + x₁² − 1`. -/
def circleMap : (Fin 2 → ℝ) → (Fin 1 → ℝ) := fun x _ => x 0 ^ 2 + x 1 ^ 2 - 1

theorem contDiff_circleMap : ContDiff ℝ ∞ circleMap :=
  contDiff_pi.2 fun _ => (((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add
    ((contDiff_apply ℝ ℝ (1 : Fin 2)).pow 2)).sub contDiff_const

/-- `φ(x) = 0` iff `x₀² + x₁² = 1`. -/
theorem circleMap_eq_zero_iff (x : Fin 2 → ℝ) : circleMap x = 0 ↔ x 0 ^ 2 + x 1 ^ 2 = 1 := by
  constructor
  · intro h
    have := congrFun h 0
    simp only [circleMap, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [circleMap, Pi.zero_apply]
    linarith

/-- The zero set of `φ` (the unit circle) is compact. -/
theorem isCompact_circleMap_zero : IsCompact (circleMap ⁻¹' {0}) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_singleton.preimage contDiff_circleMap.continuous) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun p hp => ?_
  have h := (circleMap_eq_zero_iff p).1 hp
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
  fin_cases i
  · change p 0 ^ 2 ≤ 1
    nlinarith [sq_nonneg (p 1)]
  · change p 1 ^ 2 ≤ 1
    nlinarith [sq_nonneg (p 0)]

/-- The section `f(x) = (x, x₀² + x₁² − 1)` of `ℝ² × ℝ → ℝ²`. -/
abbrev circleSection : (epSEP 2 1).Obj → (epSEP 2 1).W := graphSection circleMap

/-- `f` is an sc-Fredholm section functor. -/
theorem isScFredholmSectionFunctor_circleSection :
    (epSEP 2 1).E.IsScFredholmSectionFunctor circleSection :=
  graphSection_mem_fredholmSectionFunctors_epBundle contDiff_circleMap

/-- **`|S_f|` is compact** (Definition 12.4.1 (1)): `S_f` is the unit circle. -/
theorem hasCompactSolutionSetEp_circleSection :
    (epSEP 2 1).E.HasCompactSolutionSetEp circleSection := by
  have hK : IsCompact (solutionSet (epSEP 2 1).P circleSection) := by
    have h : solutionSet (epSEP 2 1).P circleSection = circleMap ⁻¹' {0} := by
      ext x
      exact isZeroAt_graphSection_iff (n := 2) (k := 1) (φ := circleMap) (x := x)
    rw [h]
    exact isCompact_circleMap_zero
  exact hK.image (epSEP 2 1).X.continuous_π

/-- **The index of `f` is `1 = 2 − 1`** at every point. -/
theorem isIndexAt_circleSection (x : (epSEP 2 1).Obj) :
    (epSEP 2 1).B.IsIndexAt circleSection x ((0 + 1 : ℕ) : ℤ) := by
  have h := isIndexAt_graphSection_epSEP contDiff_circleMap x
  norm_num at h
  exact_mod_cast h

/-- **`f` is orientable** (Definitions 6.6.14–6.6.16): the path category of `ℝ²` has at most one
morphism between two points. -/
theorem exists_isSectionOrientation_circleSection :
    haveI := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 2 1).B
    ∃ o : ∀ a (hs : a ∈ (epSEP 2 1).X.PObj.smoothSet),
        Orx (B := (epSEP 2 1).B) circleSection isScFredholmSectionFunctor_circleSection.2 a hs,
      IsSectionOrientation (B := (epSEP 2 1).B) circleSection
        isScFredholmSectionFunctor_circleSection.2 o := by
  have := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
  have := paracompactSpace_rn_pullback (epSEP 2 1).B
  have := paracompactSpace_rn_rn_prod (epSEP 2 1).X.PObj
  have := paracompactSpace_rn_rn_pullback (epSEP 2 1).B
  exact (exists_isSectionOrientation_iff (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
    (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
    (hasScPlusSectionsThrough_epSEP 2 1)).2 fun _ _ a b =>
      congrArg (fun c => orFunctorMap (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
        (isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap)
        (hasScPlusSectionsThrough_epSEP 2 1) c) (PathCat.hom_eq_rn (n := 2) a b)

/-- **An orientation of the circle section** (Definition 6.6.16; one of the two is chosen). -/
def circleSectionOrientation : ∀ a (hs : a ∈ (epSEP 2 1).X.PObj.smoothSet),
    Orx (B := (epSEP 2 1).B) circleSection isScFredholmSectionFunctor_circleSection.2 a hs :=
  exists_isSectionOrientation_circleSection.choose

theorem isSectionOrientation_circleSectionOrientation :
    haveI := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 2 1).B
    IsSectionOrientation (B := (epSEP 2 1).B) circleSection
      isScFredholmSectionFunctor_circleSection.2 circleSectionOrientation :=
  exists_isSectionOrientation_circleSection.choose_spec

/-- `circleSectionOrientation` is invariant under the morphisms (Definition 12.5.4): they are
units. -/
theorem isOrInvariant_circleSectionOrientation :
    (epSEP 2 1).E.IsOrInvariant isScFredholmSectionFunctor_circleSection
      (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation :=
  isOrInvariant_of_forall_unit _ _ _ fun _ => rfl

/-! ### Corollary 15.4.4 -/

/-- Sc⁺-sections through smooth fibre points over `[0, 1] × ℝ²`. -/
theorem hasScPlusSectionsThrough_cubeSEP_epSEP (n k : ℕ) :
    ((epSEP n k).cubeSEP 1).B.HasScPlusSectionsThrough := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (epSEP n k).X.PObj
  have hb : ((epSEP n k).cubeSEP 1).X.PObj.AdmitsBumpFunctions :=
    admitsBumpFunctions_prod_cube (admitsBumpFunctions_epSEP n k)
  exact MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hb

/-- **All hypotheses of Corollary 15.4.4 (`corollary_15_4_4_oriented`, `m = 0`) hold for the
circle section**, with non-zero fibres and a non-empty solution set: `d_X ≡ 0`, `|X|` is
paracompact, `X` and `[0, 1] × X` have sc-smooth partitions of unity, `f` is an sc-Fredholm
section functor with tame germ data, `|S_f|` is compact, `circleSectionOrientation` is an
orientation of `f` (Definition 6.6.16) invariant under the morphisms (Definition 12.5.4), and `f`
has index `1` at every point. -/
theorem corollary_15_4_4_hypotheses_circleSection :
    (∀ y : (epSEP 2 1).Obj, Nontrivial ((epSEP 2 1).P ⁻¹' {y})) ∧
    (solutionSet (epSEP 2 1).P circleSection).Nonempty ∧
    (∀ x, (epSEP 2 1).X.PObj.degIndex x = 0) ∧
    (epSEP 2 1).X.HasParacompactOrbitSpace ∧ (epSEP 2 1).X.HasScPartitionsOfUnity ∧
    ((epSEP 2 1).cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    (epSEP 2 1).E.IsScFredholmSectionFunctor circleSection ∧
    (epSEP 2 1).B.IsScFredholmSectionTame circleSection ∧
    (epSEP 2 1).E.HasCompactSolutionSetEp circleSection ∧
    (haveI := paracompactSpace_rn_prod (epSEP 2 1).X.PObj
     haveI := paracompactSpace_rn_pullback (epSEP 2 1).B
     IsSectionOrientation (B := (epSEP 2 1).B) circleSection
       isScFredholmSectionFunctor_circleSection.2 circleSectionOrientation) ∧
    (epSEP 2 1).E.IsOrInvariant isScFredholmSectionFunctor_circleSection
      (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation ∧
    ∀ x ∈ (epSEP 2 1).X.PObj.smoothSet,
      (epSEP 2 1).B.IsIndexAt circleSection x ((0 + 1 : ℕ) : ℤ) :=
  ⟨fun y => (fibEquiv (n := 2) (k := 1) y).nontrivial,
    ⟨fun i => if i = 0 then 1 else 0,
      (isZeroAt_graphSection_iff (n := 2) (k := 1) (φ := circleMap)).2
        ((circleMap_eq_zero_iff _).2 (by norm_num))⟩,
    fun x => MPolyfold.degIndex_rn x, EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold 2),
    hasScPartitionsOfUnity_trivial_rn_of_theorem_7_5_7 2, admitsScPartitionsOfUnity_cube_rn 2,
    isScFredholmSectionFunctor_circleSection,
    isScFredholmSectionTame_graphSection_epSEP contDiff_circleMap,
    hasCompactSolutionSetEp_circleSection, isSectionOrientation_circleSectionOrientation,
    isOrInvariant_circleSectionOrientation, fun x _ => isIndexAt_circleSection x⟩

/-- **Corollary 15.4.4 (2021 p. 703) for the circle section over `ℝ²`**
(`corollary_15_4_4_oriented` applied to the instance of
`corollary_15_4_4_hypotheses_circleSection`): exact `1`-forms integrate to `0` over every
regular perturbation of `f` with the canonical orientation of `(f, o)`, and a closed `1`-form
has the same integral over any two of them; the sheets have dimension `1`. -/
theorem corollary_15_4_4_circleSection :
    corollary_15_4_4_statement (epSEP 2 1) circleSection 0
      (IsCanonicalPerturbation isScFredholmSectionFunctor_circleSection.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation) := by
  obtain ⟨-, -, hd, hpara, hPU, hPUC, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_circleSection
  exact corollary_15_4_4_oriented hd hF hft (hasScPlusSectionsThrough_epSEP 2 1)
    (hasScPlusSectionsThrough_cubeSEP_epSEP 2 1) circleSectionOrientation ho hinv hidx hpara hPU
    hPUC hS

/-! ### A canonically oriented regular perturbation -/

/-- `Dφ(x)` is onto `ℝ` at the zeros of `φ(x) = x₀² + x₁² − 1`. -/
theorem surjective_fderiv_circleMap {x : Fin 2 → ℝ} (h0 : circleMap x = 0) :
    Surjective (fderiv ℝ circleMap x) := by
  have hd : HasFDerivAt circleMap
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
          (2 * x 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x := by
    refine hasFDerivAt_pi.2 fun _ => ?_
    have h0' : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x := hasFDerivAt_apply 0 x
    have h1' : HasFDerivAt (fun y : Fin 2 → ℝ => y 1)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x := hasFDerivAt_apply 1 x
    exact (((h0'.pow 2).add (h1'.pow 2)).sub_const (1 : ℝ)).congr_fderiv (by simp)
  rw [hd.fderiv]
  have hx := (circleMap_eq_zero_iff x).1 h0
  have hne : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by rw [hx]; exact one_ne_zero
  intro w
  refine ⟨fun i => w 0 * x i / (2 * (x 0 ^ 2 + x 1 ^ 2)), ?_⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp
  field_simp

/-- **`(f, Λ₀)` is transversal** (Definition 15.2.1). -/
theorem isTransversal_circleSection :
    IsTransversal circleSection (zeroMultisection (epSEP 2 1)) :=
  isTransversal_graphSection_epSEP contDiff_circleMap fun _ h => surjective_fderiv_circleMap h

/-- **`Λ₀` is a regular perturbation of the circle section** (Corollary 15.3.10): for an
auxiliary norm `N` and a saturated open `U` with `(N, U)` controlling compactness, `Λ₀` is
structurable, `dom-supp(Λ₀) = ∅ ⊆ U`, `N(Λ₀) ≡ 0 < 1` and `(f, Λ₀)` is transversal. -/
theorem exists_isRegularPerturbation_circleSection :
    ∃ (N : (epSEP 2 1).B.One → ℝ) (U : Set (epSEP 2 1).Obj),
      IsRegularPerturbation (epSEP 2 1) circleSection N U (zeroMultisection (epSEP 2 1)) := by
  have hpara : (epSEP 2 1).X.HasParacompactOrbitSpace :=
    EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold 2)
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (epSEP 2 1).E hpara
  obtain ⟨U, hcc⟩ := exists_controlsCompactness isScFredholmSectionFunctor_circleSection
    hasCompactSolutionSetEp_circleSection hN
  have hN0 := pointwiseNorm_zeroMultisection (A := epSEP 2 1) hcc.1.isAuxNorm
  exact ⟨N, U, hcc, isStructurable_zeroMultisection hpara,
    by rw [domSupp_zeroMultisection]; exact empty_subset _,
    fun x => by rw [hN0]; exact one_pos, isTransversal_circleSection⟩

/-- **A canonically oriented regular perturbation of the circle section** (Definition 15.4.2,
Corollary 15.4.4): there is an oriented regular perturbation `P` of `f` of dimension `0 + 1`
with `P.Λ = Λ₀` satisfying `IsCanonicalPerturbation` for the orientation `circleSectionOrientation`,
and the support of `Λ₀ ∘ f` (the unit circle) is not empty.  So the perturbations over which
`corollary_15_4_4_circleSection` quantifies exist. -/
theorem exists_isCanonicalPerturbation_circleSection :
    ∃ P : OrientedRegularPerturbation (epSEP 2 1) circleSection 0,
      P.Λ = zeroMultisection (epSEP 2 1) ∧
      IsCanonicalPerturbation isScFredholmSectionFunctor_circleSection.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation P ∧
      (EpGroupoid.supp (fun z => (P.Λ (circleSection z) : ℚ))).Nonempty := by
  obtain ⟨-, -, hd, -, -, -, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_circleSection
  obtain ⟨N, U, hreg⟩ := exists_isRegularPerturbation_circleSection
  have hbd : ∀ x : (epSEP 2 1).Obj, x ∉ (epSEP 2 1).X.PObj.boundary := fun x hx => by
    have h : (0 : ℕ) < (epSEP 2 1).X.PObj.degIndex x := hx
    rw [hd x] at h
    exact lt_irrefl _ h
  have hgood : ∀ x ∈ (epSEP 2 1).X.PObj.boundary,
      0 < zeroMultisection (epSEP 2 1) (circleSection x) →
      SBLocalization.IsGoodPositionAt circleSection (zeroMultisection (epSEP 2 1)) x :=
    fun x hx _ => absurd hx (hbd x)
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => (zeroMultisection (epSEP 2 1) (circleSection z) : ℚ)),
      (epSEP 2 1).B.IsIndexAt circleSection x ((0 + 1 : ℕ) : ℤ) := fun x _ =>
    isIndexAt_circleSection x
  refine ⟨OrientedRegularPerturbation.canonical (m := 0) (isTame_epSEP 2 1)
      (admitsBumpFunctions_epSEP 2 1) hF hft (hasScPlusSectionsThrough_epSEP 2 1) _ hinv ho hreg
      hgood hidx', rfl,
    isCanonicalPerturbation_canonical (m := 0) (isTame_epSEP 2 1) (admitsBumpFunctions_epSEP 2 1)
      hF hft (hasScPlusSectionsThrough_epSEP 2 1) _ hinv ho hreg hgood hidx',
    ⟨fun i => if i = 0 then 1 else 0, ?_⟩⟩
  change (0 : ℚ) < _
  exact_mod_cast (zeroMultisection_graphSection_epSEP_pos_iff (φ := circleMap) _).2
    ((circleMap_eq_zero_iff _).2 (by norm_num))

end TrivialBundle

end Polyfold
