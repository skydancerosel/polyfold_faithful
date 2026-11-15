import Polyfold.Chapter16.IndexZeroCylinder
import Polyfold.Chapter16.CircleSectionCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) for Fredholm index `0`, on an example.

# Two signed points: the section `x ↦ (x, x² − 1)` over `ℝ`

The strong bundle `ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ`, with the section
`f(x) = (x, x² − 1)`: the fibres are not zero, `f` has Fredholm index `0`, and the solution set
is `{−1, 1}`, two transversally cut-out points.

## What is formalized (namespace `Polyfold.TrivialBundle`)

* `twoPointMap`, `twoPointSection`, `twoPointSectionOrientation`.
* **`corollary_15_4_4_index_zero_hypotheses_twoPointSection`**: all hypotheses of
  `corollary_15_4_4_index_zero_oriented` hold, with non-zero fibres and `S_f = {−1, 1}`.
* **`exists_isCanonical_twoPointSection`**: a regular perturbation of dimension `0` with the
  canonical orientation, with support `{−1, 1}`.
* **`corollary_15_4_4_index_zero_twoPointSection`**: the conclusion of the corollary;
  `hasOrientedCobordism_twoPointSection`: the cobordism of the cylinder.
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

/-- `φ(x) = x² − 1`. -/
def twoPointMap : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x _ => x 0 ^ 2 - 1

theorem contDiff_twoPointMap : ContDiff ℝ ∞ twoPointMap :=
  contDiff_pi.2 fun _ => ((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2).sub contDiff_const

/-- `φ(x) = 0` iff `x² = 1`. -/
theorem twoPointMap_eq_zero_iff (x : Fin 1 → ℝ) : twoPointMap x = 0 ↔ x 0 ^ 2 = 1 := by
  constructor
  · intro h
    have := congrFun h 0
    simp only [twoPointMap, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [twoPointMap, Pi.zero_apply]
    linarith

/-- The zero set of `φ` (the points `±1`) is compact. -/
theorem isCompact_twoPointMap_zero : IsCompact (twoPointMap ⁻¹' {0}) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_singleton.preimage contDiff_twoPointMap.continuous) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 1 → ℝ)) (r := 1)).subset fun p hp => ?_
  have h := (twoPointMap_eq_zero_iff p).1 hp
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one, Subsingleton.elim i 0, h]

/-- The section `f(x) = (x, x² − 1)` of `ℝ × ℝ → ℝ`. -/
abbrev twoPointSection : (epSEP 1 1).Obj → (epSEP 1 1).W := graphSection twoPointMap

/-- `f` is an sc-Fredholm section functor. -/
theorem isScFredholmSectionFunctor_twoPointSection :
    (epSEP 1 1).E.IsScFredholmSectionFunctor twoPointSection :=
  graphSection_mem_fredholmSectionFunctors_epBundle contDiff_twoPointMap

/-- **`|S_f|` is compact** (Definition 12.4.1 (1)): `S_f = {−1, 1}`. -/
theorem hasCompactSolutionSetEp_twoPointSection :
    (epSEP 1 1).E.HasCompactSolutionSetEp twoPointSection := by
  have hK : IsCompact (solutionSet (epSEP 1 1).P twoPointSection) := by
    have h : solutionSet (epSEP 1 1).P twoPointSection = twoPointMap ⁻¹' {0} := by
      ext x
      exact isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := twoPointMap) (x := x)
    rw [h]
    exact isCompact_twoPointMap_zero
  exact hK.image (epSEP 1 1).X.continuous_π

/-- **The index of `f` is `0 = 1 − 1`** at every point. -/
theorem isIndexAt_twoPointSection (x : (epSEP 1 1).Obj) :
    (epSEP 1 1).B.IsIndexAt twoPointSection x 0 := by
  have h := isIndexAt_graphSection_epSEP contDiff_twoPointMap x
  norm_num at h
  exact_mod_cast h

/-- **`f` is orientable** (Definitions 6.6.14–6.6.16): the path category of `ℝ` has at most one
morphism between two points. -/
theorem exists_isSectionOrientation_twoPointSection :
    haveI := paracompactSpace_rn_prod (epSEP 1 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 1 1).B
    ∃ o : ∀ a (hs : a ∈ (epSEP 1 1).X.PObj.smoothSet),
        Orx (B := (epSEP 1 1).B) twoPointSection isScFredholmSectionFunctor_twoPointSection.2 a hs,
      IsSectionOrientation (B := (epSEP 1 1).B) twoPointSection
        isScFredholmSectionFunctor_twoPointSection.2 o := by
  have := paracompactSpace_rn_prod (epSEP 1 1).X.PObj
  have := paracompactSpace_rn_pullback (epSEP 1 1).B
  have := paracompactSpace_rn_rn_prod (epSEP 1 1).X.PObj
  have := paracompactSpace_rn_rn_pullback (epSEP 1 1).B
  exact (exists_isSectionOrientation_iff (isTame_epSEP 1 1) (admitsBumpFunctions_epSEP 1 1)
    (isScFredholmSectionTame_graphSection_epSEP contDiff_twoPointMap)
    (hasScPlusSectionsThrough_epSEP 1 1)).2 fun _ _ a b =>
      congrArg (fun c => orFunctorMap (isTame_epSEP 1 1) (admitsBumpFunctions_epSEP 1 1)
        (isScFredholmSectionTame_graphSection_epSEP contDiff_twoPointMap)
        (hasScPlusSectionsThrough_epSEP 1 1) c) (PathCat.hom_eq_rn (n := 1) a b)

/-- **An orientation of `f`** (Definition 6.6.16; one of the two is chosen). -/
def twoPointSectionOrientation : ∀ a (hs : a ∈ (epSEP 1 1).X.PObj.smoothSet),
    Orx (B := (epSEP 1 1).B) twoPointSection isScFredholmSectionFunctor_twoPointSection.2 a hs :=
  exists_isSectionOrientation_twoPointSection.choose

theorem isSectionOrientation_twoPointSectionOrientation :
    haveI := paracompactSpace_rn_prod (epSEP 1 1).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP 1 1).B
    IsSectionOrientation (B := (epSEP 1 1).B) twoPointSection
      isScFredholmSectionFunctor_twoPointSection.2 twoPointSectionOrientation :=
  exists_isSectionOrientation_twoPointSection.choose_spec

/-- `twoPointSectionOrientation` is invariant under the morphisms (Definition 12.5.4): they are
units. -/
theorem isOrInvariant_twoPointSectionOrientation :
    (epSEP 1 1).E.IsOrInvariant isScFredholmSectionFunctor_twoPointSection
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation :=
  isOrInvariant_of_forall_unit _ _ _ fun _ => rfl

/-- **All hypotheses of Corollary 15.4.4 for index `0`
(`corollary_15_4_4_index_zero_oriented`) hold for `f(x) = (x, x² − 1)`**, with non-zero fibres
and the solution set `{−1, 1}`: `d_X ≡ 0`, `|X|` is paracompact, `X` and `[0, 1] × X` have
sc-smooth partitions of unity, `f` is an sc-Fredholm section functor with tame germ data,
`|S_f|` is compact, `twoPointSectionOrientation` is an orientation of `f` (Definition 6.6.16)
invariant under the morphisms (Definition 12.5.4), and `f` has index `0` at every point. -/
theorem corollary_15_4_4_index_zero_hypotheses_twoPointSection :
    (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
    (fun _ => (1 : ℝ)) ∈ solutionSet (epSEP 1 1).P twoPointSection ∧
    (fun _ => (-1 : ℝ)) ∈ solutionSet (epSEP 1 1).P twoPointSection ∧
    (∀ x, (epSEP 1 1).X.PObj.degIndex x = 0) ∧
    (epSEP 1 1).X.HasParacompactOrbitSpace ∧ (epSEP 1 1).X.HasScPartitionsOfUnity ∧
    ((epSEP 1 1).cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    (epSEP 1 1).E.IsScFredholmSectionFunctor twoPointSection ∧
    (epSEP 1 1).B.IsScFredholmSectionTame twoPointSection ∧
    (epSEP 1 1).E.HasCompactSolutionSetEp twoPointSection ∧
    (haveI := paracompactSpace_rn_prod (epSEP 1 1).X.PObj
     haveI := paracompactSpace_rn_pullback (epSEP 1 1).B
     IsSectionOrientation (B := (epSEP 1 1).B) twoPointSection
       isScFredholmSectionFunctor_twoPointSection.2 twoPointSectionOrientation) ∧
    (epSEP 1 1).E.IsOrInvariant isScFredholmSectionFunctor_twoPointSection
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation ∧
    ∀ x ∈ (epSEP 1 1).X.PObj.smoothSet, (epSEP 1 1).B.IsIndexAt twoPointSection x 0 :=
  ⟨fun y => (fibEquiv (n := 1) (k := 1) y).nontrivial,
    (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := twoPointMap)).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num)),
    (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := twoPointMap)).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num)),
    fun x => MPolyfold.degIndex_rn x, EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold 1),
    hasScPartitionsOfUnity_trivial_rn_of_theorem_7_5_7 1, admitsScPartitionsOfUnity_cube_rn 1,
    isScFredholmSectionFunctor_twoPointSection,
    isScFredholmSectionTame_graphSection_epSEP contDiff_twoPointMap,
    hasCompactSolutionSetEp_twoPointSection, isSectionOrientation_twoPointSectionOrientation,
    isOrInvariant_twoPointSectionOrientation, fun x _ => isIndexAt_twoPointSection x⟩

/-- `Dφ(x)` is onto `ℝ` at the zeros of `φ(x) = x² − 1`. -/
theorem surjective_fderiv_twoPointMap {x : Fin 1 → ℝ} (h0 : twoPointMap x = 0) :
    Surjective (fderiv ℝ twoPointMap x) := by
  have hd : HasFDerivAt twoPointMap
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := by
    refine hasFDerivAt_pi.2 fun _ => ?_
    have h0' : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := hasFDerivAt_apply 0 x
    exact ((h0'.pow 2).sub_const (1 : ℝ)).congr_fderiv (by simp)
  rw [hd.fderiv]
  have hx := (twoPointMap_eq_zero_iff x).1 h0
  have hne : x 0 ≠ 0 := fun h => by
    rw [h] at hx
    norm_num at hx
  intro w
  refine ⟨fun _ => w 0 / (2 * x 0), ?_⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp
  field_simp

/-- **`(f, Λ₀)` is transversal** (Definition 15.2.1). -/
theorem isTransversal_twoPointSection :
    IsTransversal twoPointSection (zeroMultisection (epSEP 1 1)) :=
  isTransversal_graphSection_epSEP contDiff_twoPointMap fun _ h => surjective_fderiv_twoPointMap h

/-- **`Λ₀` is a regular perturbation of `f`** (Corollary 15.3.10). -/
theorem exists_isRegularPerturbation_twoPointSection :
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj),
      IsRegularPerturbation (epSEP 1 1) twoPointSection N U (zeroMultisection (epSEP 1 1)) := by
  have hpara : (epSEP 1 1).X.HasParacompactOrbitSpace :=
    EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold 1)
  obtain ⟨N, hN⟩ := EpStrongBundle.theorem_12_2_2 (epSEP 1 1).E hpara
  obtain ⟨U, hcc⟩ := exists_controlsCompactness isScFredholmSectionFunctor_twoPointSection
    hasCompactSolutionSetEp_twoPointSection hN
  have hN0 := pointwiseNorm_zeroMultisection (A := epSEP 1 1) hcc.1.isAuxNorm
  exact ⟨N, U, hcc, isStructurable_zeroMultisection hpara,
    by rw [domSupp_zeroMultisection]; exact empty_subset _,
    fun x => by rw [hN0]; exact one_pos, isTransversal_twoPointSection⟩

/-- **A canonically oriented regular perturbation of dimension `0` of `f(x) = (x, x² − 1)`**
(Definition 15.4.2, Corollary 15.4.4 for index `0`): there is a regular perturbation `P` of `f`
of dimension `0` with `P.Λ = Λ₀` and the canonical orientation of `(f, o)`, and both points
`±1` lie in the support of `Λ₀ ∘ f`.  So the perturbations over which
`corollary_15_4_4_index_zero_twoPointSection` quantifies exist, with a support that is not empty. -/
theorem exists_isCanonical_twoPointSection :
    ∃ P : PointPerturbation (epSEP 1 1) twoPointSection,
      P.Λ = zeroMultisection (epSEP 1 1) ∧
      P.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
        (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation ∧
      (fun _ => (1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (twoPointSection z) : ℚ)) ∧
      (fun _ => (-1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (twoPointSection z) : ℚ)) := by
  obtain ⟨-, -, -, hd, -, -, -, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_twoPointSection
  obtain ⟨N, U, hreg⟩ := exists_isRegularPerturbation_twoPointSection
  have hbd : ∀ x : (epSEP 1 1).Obj, x ∉ (epSEP 1 1).X.PObj.boundary := fun x hx => by
    have h : (0 : ℕ) < (epSEP 1 1).X.PObj.degIndex x := hx
    rw [hd x] at h
    exact lt_irrefl _ h
  have hgood : ∀ x ∈ (epSEP 1 1).X.PObj.boundary,
      0 < zeroMultisection (epSEP 1 1) (twoPointSection x) →
      SBLocalization.IsGoodPositionAt twoPointSection (zeroMultisection (epSEP 1 1)) x :=
    fun x hx _ => absurd hx (hbd x)
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => (zeroMultisection (epSEP 1 1) (twoPointSection z) : ℚ)),
      (epSEP 1 1).B.IsIndexAt twoPointSection x (0 : ℕ) := fun x _ => by
    exact_mod_cast isIndexAt_twoPointSection x
  refine ⟨PointPerturbation.canonical (isTame_epSEP 1 1) (admitsBumpFunctions_epSEP 1 1) hF hft
      (hasScPlusSectionsThrough_epSEP 1 1) _ hinv ho hreg hgood hidx', rfl,
    PointPerturbation.isCanonical_canonical (isTame_epSEP 1 1) (admitsBumpFunctions_epSEP 1 1)
      hF hft (hasScPlusSectionsThrough_epSEP 1 1) _ hinv ho hreg hgood hidx', ?_, ?_⟩
  · change (0 : ℚ) < _
    exact_mod_cast (zeroMultisection_graphSection_epSEP_pos_iff (φ := twoPointMap) _).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num))
  · change (0 : ℚ) < _
    exact_mod_cast (zeroMultisection_graphSection_epSEP_pos_iff (φ := twoPointMap) _).2
      ((twoPointMap_eq_zero_iff _).2 (by norm_num))

/-- **Corollary 15.4.4 (2021 p. 703) for Fredholm index `0`, for `f(x) = (x, x² − 1)` over `ℝ`**
(`corollary_15_4_4_index_zero_oriented` applied to the instance of
`corollary_15_4_4_index_zero_hypotheses_twoPointSection`): a closed `0`-form has the same weighted
signed count over any two regular perturbations of `f` of dimension `0` with the canonical
orientation of `(f, o)`. -/
theorem corollary_15_4_4_index_zero_twoPointSection
    (P₀ P₁ : PointPerturbation (epSEP 1 1) twoPointSection)
    (h₀ : P₀.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation)
    (h₁ : P₁.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation)
    (τ : (epSEP 1 1).baseEP.epFormsInfty 0) (hτ : (epSEP 1 1).baseEP.epFormsInftyD 0 τ = 0) :
    P₀.count τ = P₁.count τ ∧
      ∀ hLUC : (epSEP 1 1).X.IsLUC, P₀.countEff hLUC τ = P₁.countEff hLUC τ := by
  obtain ⟨-, -, -, hd, hpara, hPU, hPUC, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_twoPointSection
  exact corollary_15_4_4_index_zero_oriented hd hF hft (hasScPlusSectionsThrough_epSEP 1 1)
    twoPointSectionOrientation ho hidx hinv hpara hPU hPUC hS P₀ P₁ h₀ h₁ τ hτ

/-- **The cobordism of the cylinder for `f(x) = (x, x² − 1)`**: any two canonically oriented
regular perturbations of dimension `0` are joined by an oriented compact cobordism of dimension
`1` over `[0, 1] × ℝ` (`hasOrientedCobordism_of_isCanonical`). -/
theorem hasOrientedCobordism_twoPointSection (P₀ P₁ : PointPerturbation (epSEP 1 1) twoPointSection)
    (h₀ : P₀.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation)
    (h₁ : P₁.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation) :
    P₀.HasOrientedCobordism P₁ := by
  obtain ⟨-, -, -, hd, hpara, hPU, hPUC, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_twoPointSection
  exact (hasOrientedCobordism_of_isCanonical hd hF hft (hasScPlusSectionsThrough_epSEP 1 1)
    twoPointSectionOrientation ho hidx hinv hpara hPU hPUC hS P₀ P₁ h₀ h₁).1

end TrivialBundle

end Polyfold
