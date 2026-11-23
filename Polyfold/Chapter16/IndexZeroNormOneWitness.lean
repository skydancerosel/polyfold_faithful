import Polyfold.Chapter16.IndexZeroAllAdmissible
import Polyfold.Chapter16.IndexZeroShiftedPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.3** and **Corollary 15.4.4** (2017: Theorem 15.7, Corollary 15.2), Fredholm index
`0`, on an example with `N(Λ) = 1`.

# A transversal perturbation with `N(Λ) = 1`

The strong bundle `ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ`, the section
`f(x) = (x, x² − 1)` and the auxiliary norm `N(x, v) = |v|` of
`Chapter16/IndexZeroShiftedPerturbation` (`(N, ℝ)` controls compactness).  The multisection
`Λ_u` of the constant section `u(x) = (x, 1)` has `N(Λ_u) ≡ 1`; `f(x) = u(x)` iff `x² = 2`, where
`(f − u)'(x) = 2x ≠ 0`.  So `(N, ℝ, Λ_u)` satisfies the hypotheses of Theorem 15.4.3 and is not a
regular perturbation for `(N, ℝ)` in the sense of Corollary 15.3.10 (1) (`N(Λ) < 1`).

## What is formalized (namespace `Polyfold.TrivialBundle`)

* `unitMap`, `unitSection`, `unitMulti = Λ_u`; `unitMulti_twoPointSection_pos_iff`.
* `pointwiseNorm_unitMulti` (`N(Λ_u) ≡ 1`), `isTransversal_unitMulti`,
  **`isTransversalPerturbation_unitMulti`**, `not_isRegularPerturbation_unitMulti`.
* **`corollary_15_4_4_index_zero_norm_one`**: a point solution set `P₀` with `P₀.Λ = Λ_u`,
  `N(P₀.Λ) ≡ 1`, the canonical orientation and `√2` in its support, and a canonically oriented
  regular perturbation `P₁` (with `Λ_s`, `N = 3/4`), such that every closed `0`-form has the same
  weighted signed count and effective count over both
  (`pointCount_eq_of_isTransversalPerturbation`).
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

/-- `ψ(x) = 1`. -/
def unitMap : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun _ _ => 1

/-- The constant section `u(x) = (x, 1)`. -/
abbrev unitSection : (epSEP 1 1).Obj → (epSEP 1 1).W := graphSection unitMap

theorem isScPlusSection_unitSection : (epSEP 1 1).B.IsScPlusSection unitSection :=
  isScPlusSection_graphSection contDiff_const

/-- **The multisection `Λ_u` of the constant section** `u(x) = (x, 1)`. -/
abbrev unitMulti : (epSEP 1 1).W → ℚ≥0 := sectionMulti unitSection

/-- `f(x) = u(x)` iff `x² = 2`. -/
theorem twoPointSection_eq_unitSection_iff (x : (epSEP 1 1).Obj) :
    twoPointSection x = unitSection x ↔ x 0 ^ 2 = 2 := by
  constructor
  · intro h
    have h2 := congrFun (congrArg Prod.snd h) 0
    change x 0 ^ 2 - 1 = 1 at h2
    linarith
  · intro h
    refine Prod.ext rfl (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    change x 0 ^ 2 - 1 = 1
    linarith

theorem unitMulti_twoPointSection_pos_iff (x : (epSEP 1 1).Obj) :
    0 < unitMulti (twoPointSection x) ↔ x 0 ^ 2 = 2 :=
  (sectionMulti_pos_iff _ _).trans (twoPointSection_eq_unitSection_iff x)


/-- `D(φ − ψ)(x) = 2x` is onto `ℝ` where `x² = 2`. -/
theorem surjective_fderiv_twoPointMap_sub_unitMap {x : Fin 1 → ℝ} (hx : x 0 ^ 2 = 2) :
    Surjective (fderiv ℝ (twoPointMap - unitMap) x) := by
  have hd₁ : HasFDerivAt twoPointMap
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := by
    refine hasFDerivAt_pi.2 fun _ => ?_
    have h0' : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := hasFDerivAt_apply 0 x
    exact ((h0'.pow 2).sub_const (1 : ℝ)).congr_fderiv (by simp)
  have hd : HasFDerivAt (twoPointMap - unitMap)
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    (hd₁.sub (hasFDerivAt_const (fun _ : Fin 1 => (1 : ℝ)) x)).congr_fderiv (sub_zero _)
  rw [hd.fderiv]
  have hne : x 0 ≠ 0 := fun h => by
    rw [h] at hx
    norm_num at hx
  intro w
  refine ⟨fun _ => w 0 / (2 * x 0), ?_⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp
  field_simp

/-- **`(f, Λ_u)` is transversal** (Definition 15.2.1): at `x₀ = ±√2`, in the chart centred at
`x₀`, `(f − u)'(x₀) = D(φ − ψ)(x₀)` is onto `ℝ`. -/
theorem isTransversal_unitMulti : IsTransversal twoPointSection unitMulti := by
  classical
  have hf := isScFredholmSectionFunctor_twoPointSection
  intro x₀ hpos
  have h0 : x₀ 0 ^ 2 = 2 := (unitMulti_twoPointSection_pos_iff x₀).1 hpos
  have hx1 : x₀ ∈ (epSEP 1 1).X.PObj.levelSet 1 := by
    have h : (x₀ : Fin 1 → ℝ) ∈ (rnPolyfold 1).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hpos, hx1, ?_⟩
  set x := (epSEP 1 1).X.PObj.levelMk 1 x₀ hx1 with hxdef
  intro L hL
  have hxv : (epSEP 1 1).X.PObj.levelVal 1 x = x₀ := (epSEP 1 1).X.PObj.levelVal_levelMk _ _ _
  let c : StrongBundleChart (epSEP 1 1).X.PObj (epSEP 1 1).P := chart (k := 1) x₀
  have hc : (epSEP 1 1).B.IsChart c := isChart_chart x₀
  have hx : (epSEP 1 1).X.PObj.levelVal 1 x ∈ c.φ.source := mem_univ _
  have hxs : twoPointSection ((epSEP 1 1).X.PObj.levelVal 1 x) =
      unitSection ((epSEP 1 1).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (twoPointSection_eq_unitSection_iff x₀).2 h0
  rw [← (mem_support_linearization_sectionMulti_iff isScPlusSection_unitSection hf hc hx hxs
    L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (IsScPlusSectionOn.of_isScPlusSection
    isScPlusSection_unitSection isOpen_univ) hc (subset_univ _) hx hxs).2 ?_
  set z := levelLift c.φ 1 ((epSEP 1 1).X.PObj.levelVal 1 x) with hzdef
  have hz : z = 0 := by
    have h1 : c.φ.model.E.toBase 1 z = c.φ ((epSEP 1 1).X.PObj.levelVal 1 x) :=
      (epSEP 1 1).X.PObj.toBase_levelLift c.isChart hx ((epSEP 1 1).X.PObj.levelVal_mem x)
    rw [hxv] at h1
    have h2 : c.φ x₀ = (0 : Fin 1 → ℝ) := sub_self (show Fin 1 → ℝ from x₀)
    exact h1.trans h2
  have he : ((fun y => c.principal twoPointSection y - c.principal unitSection y) ∘ r c.R) =
      loc (twoPointMap - unitMap) x₀ := by
    funext u
    rfl
  intro w _
  obtain ⟨v, hv⟩ := surjective_fderiv_twoPointMap_sub_unitMap h0 w
  refine ⟨v, ⟨v, ?_⟩, ?_⟩
  · rw [hz]
    exact congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T v) (scDeriv_r (k := 1) x₀)
  · change scDeriv c.U ((fun y => c.principal twoPointSection y -
      c.principal unitSection y) ∘ r c.R) z v = w
    rw [he, hz]
    exact (congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T v)
      (scDeriv_loc (contDiff_twoPointMap.sub contDiff_const) x₀)).trans hv

/-! ### The norm -/

theorem isScPlusMultisection_unitMulti : IsScPlusMultisection (epSEP 1 1) unitMulti :=
  (isStructurable_sectionMulti tgt_eq_src_epSEP μ_epSEP isScPlusSection_unitSection
    (EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold 1))).1

/-- **`N(Λ_u)(x) = 1`** for every `x`. -/
theorem pointwiseNorm_unitMulti (x : (epSEP 1 1).Obj) :
    pointwiseNorm (fibNorm (n := 1) (k := 1)) unitMulti x = 1 := by
  have hmem := (IsScPlusSectionOn.of_isScPlusSection isScPlusSection_unitSection
    isOpen_univ).mem_oneSet (mem_univ x)
  refine ((pointwiseNorm_sectionMulti _ isScPlusSection_unitSection.1 x).trans
    ((normW_of_mem _ hmem).trans (fibNorm_oneMk _ hmem))).trans ?_
  change ‖unitMap x‖ = 1
  have h : unitMap x = fun _ : Fin 1 => (1 : ℝ) := rfl
  rw [h, pi_norm_const, norm_one]

/-- **`(N, ℝ, Λ_u)` is a transversal perturbation of `f`** (the hypotheses of Theorem 15.4.3):
`(N, ℝ)` controls compactness, `Λ_u` is an sc⁺-multisection with `N(Λ_u) = 1 ≤ 1`, and
`(f, Λ_u)` is transversal. -/
theorem isTransversalPerturbation_unitMulti :
    IsTransversalPerturbation (epSEP 1 1) twoPointSection (fibNorm (n := 1) (k := 1)) univ
      unitMulti :=
  ⟨controlsCompactness_twoPointSection_univ, isScPlusMultisection_unitMulti, subset_univ _,
    fun x => (pointwiseNorm_unitMulti x).le, isTransversal_unitMulti⟩

/-- `(N, ℝ, Λ_u)` is not a regular perturbation in the sense of Corollary 15.3.10 (1): the bound
`N(Λ) < 1` does not hold. -/
theorem not_isRegularPerturbation_unitMulti :
    ¬ IsRegularPerturbation (epSEP 1 1) twoPointSection (fibNorm (n := 1) (k := 1)) univ
      unitMulti := fun h => by
  have h1 := h.2.2.2.1 (fun _ => (0 : ℝ))
  have h2 := pointwiseNorm_unitMulti (fun _ => (0 : ℝ))
  linarith

/-! ### The counts -/

/-- **Corollary 15.4.4 for index `0` with a perturbation of norm `1`**: for `f(x) = (x, x² − 1)`
over `ℝ` there are a point solution set `P₀` with `P₀.Λ = Λ_u`, `N(Λ_u) ≡ 1`, the canonical
orientation and `√2` in its support, and a canonically oriented regular perturbation `P₁` (with
`Λ_s`), such that every closed `0`-form has the same weighted signed count, and the same
effective count, over both. -/
theorem corollary_15_4_4_index_zero_norm_one :
    ∃ (P₀ : PointSolution (epSEP 1 1) twoPointSection)
      (P₁ : PointPerturbation (epSEP 1 1) twoPointSection),
      P₀.Λ = unitMulti ∧
      (∀ x, pointwiseNorm (fibNorm (n := 1) (k := 1)) P₀.Λ x = 1) ∧
      IsTransversalPerturbation (epSEP 1 1) twoPointSection (fibNorm (n := 1) (k := 1)) univ
        P₀.Λ ∧
      IsCanonicalFor P₀.Λ isScFredholmSectionFunctor_twoPointSection.2
        (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation 0 P₀.T ∧
      (fun _ => Real.sqrt 2) ∈ EpGroupoid.supp (fun z => (P₀.Λ (twoPointSection z) : ℚ)) ∧
      P₁.Λ = shiftMulti ∧
      ∀ τ : (epSEP 1 1).baseEP.epFormsInfty 0, (epSEP 1 1).baseEP.epFormsInftyD 0 τ = 0 →
        P₀.count τ = P₁.count τ ∧
          ∀ hLUC : (epSEP 1 1).X.IsLUC, P₀.countEff hLUC τ = P₁.countEff hLUC τ := by
  obtain ⟨-, -, -, hd, hpara, -, -, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_index_zero_hypotheses_twoPointSection
  obtain ⟨P₁, hΛ₁, hcan₁, -⟩ := exists_isCanonical_shiftMulti
  have hbd : ∀ x : (epSEP 1 1).Obj, x ∉ (epSEP 1 1).X.PObj.boundary := fun x hx => by
    have h : (0 : ℕ) < (epSEP 1 1).X.PObj.degIndex x := hx
    rw [hd x] at h
    exact lt_irrefl _ h
  have hgood : ∀ x ∈ (epSEP 1 1).X.PObj.boundary, 0 < unitMulti (twoPointSection x) →
      SBLocalization.IsGoodPositionAt twoPointSection unitMulti x :=
    fun x hx _ => absurd hx (hbd x)
  have hidx' : ∀ x ∈ EpGroupoid.supp (fun z => (unitMulti (twoPointSection z) : ℚ)),
      (epSEP 1 1).B.IsIndexAt twoPointSection x (0 : ℕ) := fun x _ => by
    exact_mod_cast isIndexAt_twoPointSection x
  have hr := isTransversalPerturbation_unitMulti
  have hcan := theorem_15_4_1 (isTame_epSEP 1 1) (admitsBumpFunctions_epSEP 1 1) hF hft hr.2.1
    (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation hinv ho
    (isGoodPositionAt_of_transversal hF hft hr.2.1 hr.2.2.2.2 hgood) hidx'
  have hb := theorem_15_4_3_isBranched_hyp hF hft hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
    hgood
  let P₀ : PointSolution (epSEP 1 1) twoPointSection :=
    ⟨unitMulti, hr.2.1, _, hb.1, hb.2, hcan.1, EpGroupoid.isPointTame_iff.2 hcan.loc⟩
  refine ⟨P₀, P₁, rfl, pointwiseNorm_unitMulti, hr, hcan, ?_, hΛ₁, fun τ hτ => ?_⟩
  · change (0 : ℚ) < _
    exact_mod_cast (unitMulti_twoPointSection_pos_iff (fun _ => Real.sqrt 2)).2
      (Real.sq_sqrt (by norm_num))
  · exact pointCount_eq_of_isTransversalPerturbation hd hF hft
      (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation ho hidx hinv hpara
      (admitsBumpFunctions_epSEP 1 1) (P₀ := P₀) (P₁ := PointSolution.ofRegular P₁) hr
      P₁.isRegular.isTransversalPerturbation hcan hcan₁ τ hτ

end TrivialBundle

end Polyfold
