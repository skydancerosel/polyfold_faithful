import Polyfold.Chapter16.IndexZeroCylinderWitness
import Polyfold.Chapter15.SingleSectionMultisection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) for Fredholm index `0`, with two different
perturbations.

# Two canonical perturbations of `x ↦ (x, x² − 1)` with different solution sets

The strong bundle `ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ` and the section
`f(x) = (x, x² − 1)` of `IndexZeroCylinderWitness`.  Besides `Λ₀` (perturbed solutions `±1`),
the multisection `Λ_s` of the constant section `s(x) = (x, −3/4)` is a regular perturbation:
`f(x) = s(x)` iff `x = ±1/2`, where `(f − s)'(x) = 2x ≠ 0`, and `N(s(x)) = 3/4 < 1` for the
auxiliary norm `N(x, v) = |v|`, for which `(N, ℝ)` controls compactness (`|x² − 1| ≤ 1` forces
`|x| ≤ 2`).  So the cobordism identity of the corollary is exercised on two perturbations with
different supports.

## What is formalized (namespace `Polyfold.TrivialBundle`)

* `shiftMap`, `shiftSection`, `shiftMulti = Λ_s`; `shiftMulti_twoPointSection_pos_iff`
  (`Λ_s(f(x)) > 0 ⇔ x² = 1/4`).
* `isAuxNorm_fibNorm_epSEP`: `N(x, v) = |v|` is an auxiliary norm for the ep-groupoid bundle;
  `controlsCompactness_twoPointSection_univ`: `(N, ℝ)` controls compactness of `f`.
* `isTransversal_shiftMulti`, **`isRegularPerturbation_shiftMulti`** (Definition 15.3.8).
* `exists_isCanonical_shiftMulti`: a regular perturbation of dimension `0` with `P.Λ = Λ_s` and
  the canonical orientation, with `±1/2` in its support and `1` not.
* **`corollary_15_4_4_index_zero_two_perturbations`**: two canonically oriented regular
  perturbations `P₀` (`Λ₀`) and `P₁` (`Λ_s`) with `P₀ ≠ P₁` and different supports; they are
  joined by an oriented cobordism, and the weighted signed counts of every closed `0`-form agree.
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

/-- `ψ(x) = −3/4`. -/
def shiftMap : (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun _ _ => -(3 / 4)

/-- The constant section `s(x) = (x, −3/4)`. -/
abbrev shiftSection : (epSEP 1 1).Obj → (epSEP 1 1).W := graphSection shiftMap

theorem isScPlusSection_shiftSection : (epSEP 1 1).B.IsScPlusSection shiftSection :=
  isScPlusSection_graphSection contDiff_const

theorem tgt_eq_src_epSEP (φ : (epSEP 1 1).Mor) : (epSEP 1 1).X.tgt φ = (epSEP 1 1).X.src φ :=
  rfl

theorem μ_epSEP (q : pullbackSpace (epSEP 1 1).P (epSEP 1 1).X.src) :
    (epSEP 1 1).E.μ q = (q : (epSEP 1 1).Mor × (epSEP 1 1).W).2 :=
  rfl

/-- **The multisection `Λ_s` of the constant section** `s(x) = (x, −3/4)`. -/
abbrev shiftMulti : (epSEP 1 1).W → ℚ≥0 := sectionMulti shiftSection

/-- `f(x) = s(x)` iff `x² = 1/4`. -/
theorem twoPointSection_eq_shiftSection_iff (x : (epSEP 1 1).Obj) :
    twoPointSection x = shiftSection x ↔ x 0 ^ 2 = 1 / 4 := by
  constructor
  · intro h
    have h2 := congrFun (congrArg Prod.snd h) 0
    change x 0 ^ 2 - 1 = -(3 / 4) at h2
    linarith
  · intro h
    refine Prod.ext rfl (funext fun i => ?_)
    rw [Subsingleton.elim i 0]
    change x 0 ^ 2 - 1 = -(3 / 4)
    linarith

theorem shiftMulti_twoPointSection_pos_iff (x : (epSEP 1 1).Obj) :
    0 < shiftMulti (twoPointSection x) ↔ x 0 ^ 2 = 1 / 4 :=
  (sectionMulti_pos_iff _ _).trans (twoPointSection_eq_shiftSection_iff x)

/-! ### The auxiliary norm `N(x, v) = |v|` and the controlling pair `(N, ℝ)` -/

/-- **`N(x, v) = |v|` is an auxiliary norm** for the ep-groupoid bundle (the morphisms are
units and act trivially). -/
theorem isAuxNorm_fibNorm_epSEP : (epSEP 1 1).E.IsAuxNorm (fibNorm (n := 1) (k := 1)) :=
  ⟨isAuxNorm_fibNorm, fun h k _ _ e => by
    rw [(bundle 1 1).oneVal_injective (e.trans (μ_epSEP _))]⟩

theorem fibNorm_oneMk (w : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (hw : w ∈ (bundle 1 1).oneSet) :
    fibNorm (n := 1) (k := 1) ((bundle 1 1).oneMk w hw) = ‖w.2‖ := by
  unfold fibNorm
  rw [oneVal_oneMk]

/-- **`(N, ℝ)` controls the compactness of `f`** (Definition 15.3.1): `N(f(x)) ≤ 1` means
`|x² − 1| ≤ 1`, so `|x| ≤ 2`. -/
theorem controlsCompactness_twoPointSection_univ :
    ControlsCompactness (epSEP 1 1) twoPointSection (fibNorm (n := 1) (k := 1)) univ := by
  refine ⟨isAuxNorm_fibNorm_epSEP, isOpen_univ, GroupoidStr.isSaturated_univ _,
    subset_univ _, ?_⟩
  let K : Set (Fin 1 → ℝ) := Metric.closedBall 0 2
  have hK : IsCompact K := isCompact_closedBall 0 2
  have hsub : {x ∈ (univ : Set (epSEP 1 1).Obj) |
      (epSEP 1 1).B.AuxLe (fibNorm (n := 1) (k := 1)) (twoPointSection x) 1} ⊆
      (K : Set (epSEP 1 1).Obj) := by
    rintro (x : Fin 1 → ℝ) ⟨-, hw, hle⟩
    have hle' : ‖twoPointMap x‖ ≤ 1 := (fibNorm_oneMk _ hw).symm.trans_le hle
    have h1 : ‖twoPointMap x 0‖ ≤ 1 := (norm_le_pi_norm (twoPointMap x) 0).trans hle'
    change ‖x 0 ^ 2 - 1‖ ≤ 1 at h1
    rw [Real.norm_eq_abs, abs_le] at h1
    change x ∈ Metric.closedBall (0 : Fin 1 → ℝ) 2
    rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    rw [Subsingleton.elim i 0, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [h1.2, sq_nonneg (x 0 - 2), sq_nonneg (x 0 + 2)]
  exact (hK.image (epSEP 1 1).X.continuous_π).closure_of_subset (image_mono hsub)

/-- `N(Λ_s)(x) = 3/4 < 1`. -/
theorem pointwiseNorm_shiftMulti_lt (x : (epSEP 1 1).Obj) :
    pointwiseNorm (fibNorm (n := 1) (k := 1)) shiftMulti x < 1 := by
  have hmem := (IsScPlusSectionOn.of_isScPlusSection isScPlusSection_shiftSection
    isOpen_univ).mem_oneSet (mem_univ x)
  refine ((pointwiseNorm_sectionMulti _ isScPlusSection_shiftSection.1 x).trans
    ((normW_of_mem _ hmem).trans (fibNorm_oneMk _ hmem))).trans_lt ?_
  have h : ‖shiftMap x‖ ≤ 3 / 4 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    intro i
    change ‖(-(3 / 4) : ℝ)‖ ≤ 3 / 4
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  change ‖shiftMap x‖ < 1
  linarith

/-! ### Transversality -/

/-- `D(φ − ψ)(x) = 2x` is onto `ℝ` where `x² = 1/4`. -/
theorem surjective_fderiv_twoPointMap_sub_shiftMap {x : Fin 1 → ℝ} (hx : x 0 ^ 2 = 1 / 4) :
    Surjective (fderiv ℝ (twoPointMap - shiftMap) x) := by
  have hd₁ : HasFDerivAt twoPointMap
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := by
    refine hasFDerivAt_pi.2 fun _ => ?_
    have h0' : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x := hasFDerivAt_apply 0 x
    exact ((h0'.pow 2).sub_const (1 : ℝ)).congr_fderiv (by simp)
  have hd : HasFDerivAt (twoPointMap - shiftMap)
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (2 * x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    (hd₁.sub (hasFDerivAt_const (fun _ : Fin 1 => (-(3 / 4) : ℝ)) x)).congr_fderiv (sub_zero _)
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

/-- **`(f, Λ_s)` is transversal** (Definition 15.2.1): at `x₀ = ±1/2`, in the chart centred at
`x₀`, `(f − s)'(x₀) = D(φ − ψ)(x₀)` is onto `ℝ`. -/
theorem isTransversal_shiftMulti : IsTransversal twoPointSection shiftMulti := by
  classical
  have hf := isScFredholmSectionFunctor_twoPointSection
  intro x₀ hpos
  have h0 : x₀ 0 ^ 2 = 1 / 4 := (shiftMulti_twoPointSection_pos_iff x₀).1 hpos
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
      shiftSection ((epSEP 1 1).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (twoPointSection_eq_shiftSection_iff x₀).2 h0
  rw [← (mem_support_linearization_sectionMulti_iff isScPlusSection_shiftSection hf hc hx hxs
    L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (IsScPlusSectionOn.of_isScPlusSection
    isScPlusSection_shiftSection isOpen_univ) hc (subset_univ _) hx hxs).2 ?_
  set z := levelLift c.φ 1 ((epSEP 1 1).X.PObj.levelVal 1 x) with hzdef
  have hz : z = 0 := by
    have h1 : c.φ.model.E.toBase 1 z = c.φ ((epSEP 1 1).X.PObj.levelVal 1 x) :=
      (epSEP 1 1).X.PObj.toBase_levelLift c.isChart hx ((epSEP 1 1).X.PObj.levelVal_mem x)
    rw [hxv] at h1
    have h2 : c.φ x₀ = (0 : Fin 1 → ℝ) := sub_self (show Fin 1 → ℝ from x₀)
    exact h1.trans h2
  have he : ((fun y => c.principal twoPointSection y - c.principal shiftSection y) ∘ r c.R) =
      loc (twoPointMap - shiftMap) x₀ := by
    funext u
    rfl
  intro w _
  obtain ⟨v, hv⟩ := surjective_fderiv_twoPointMap_sub_shiftMap h0 w
  refine ⟨v, ⟨v, ?_⟩, ?_⟩
  · rw [hz]
    exact congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T v) (scDeriv_r (k := 1) x₀)
  · change scDeriv c.U ((fun y => c.principal twoPointSection y -
      c.principal shiftSection y) ∘ r c.R) z v = w
    rw [he, hz]
    exact (congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T v)
      (scDeriv_loc (contDiff_twoPointMap.sub contDiff_const) x₀)).trans hv

/-- **`Λ_s` is a regular perturbation of `f`** (Definition 15.3.8) for `(N, ℝ)`, `N(x, v) = |v|`:
`(N, ℝ)` controls compactness, `Λ_s` is structurable, `dom-supp(Λ_s) ⊆ ℝ`, `N(Λ_s) = 3/4 < 1`,
and `(f, Λ_s)` is transversal. -/
theorem isRegularPerturbation_shiftMulti :
    IsRegularPerturbation (epSEP 1 1) twoPointSection (fibNorm (n := 1) (k := 1)) univ
      shiftMulti :=
  ⟨controlsCompactness_twoPointSection_univ,
    isStructurable_sectionMulti tgt_eq_src_epSEP μ_epSEP isScPlusSection_shiftSection
      (EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold 1)),
    subset_univ _, pointwiseNorm_shiftMulti_lt, isTransversal_shiftMulti⟩

/-! ### The second canonical perturbation -/

/-- **A second canonically oriented regular perturbation of dimension `0`** of
`f(x) = (x, x² − 1)` (Definition 15.4.2): `P.Λ = Λ_s`, with `±1/2` in the support of `Λ_s ∘ f`
and `1` not in it. -/
theorem exists_isCanonical_shiftMulti :
    ∃ P : PointPerturbation (epSEP 1 1) twoPointSection,
      P.Λ = shiftMulti ∧
      P.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
        (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation ∧
      (fun _ => (1 / 2 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (twoPointSection z) : ℚ)) ∧
      (fun _ => (-1 / 2 : ℝ)) ∈ EpGroupoid.supp (fun z => (P.Λ (twoPointSection z) : ℚ)) ∧
      (fun _ => (1 : ℝ)) ∉ EpGroupoid.supp (fun z => (P.Λ (twoPointSection z) : ℚ)) := by
  obtain ⟨-, -, -, hd, -, -, -, hF, hft, -, ho, hinv, -⟩ :=
    corollary_15_4_4_index_zero_hypotheses_twoPointSection
  have hbd : ∀ x : (epSEP 1 1).Obj, x ∉ (epSEP 1 1).X.PObj.boundary := fun x hx => by
    have h : (0 : ℕ) < (epSEP 1 1).X.PObj.degIndex x := hx
    rw [hd x] at h
    exact lt_irrefl _ h
  have hgood : ∀ x ∈ (epSEP 1 1).X.PObj.boundary, 0 < shiftMulti (twoPointSection x) →
      SBLocalization.IsGoodPositionAt twoPointSection shiftMulti x :=
    fun x hx _ => absurd hx (hbd x)
  have hidx' : ∀ x ∈ EpGroupoid.supp (fun z => (shiftMulti (twoPointSection z) : ℚ)),
      (epSEP 1 1).B.IsIndexAt twoPointSection x (0 : ℕ) := fun x _ => by
    exact_mod_cast isIndexAt_twoPointSection x
  refine ⟨PointPerturbation.canonical (isTame_epSEP 1 1) (admitsBumpFunctions_epSEP 1 1) hF hft
      (hasScPlusSectionsThrough_epSEP 1 1) _ hinv ho isRegularPerturbation_shiftMulti hgood hidx',
    rfl, PointPerturbation.isCanonical_canonical (isTame_epSEP 1 1)
      (admitsBumpFunctions_epSEP 1 1) hF hft (hasScPlusSectionsThrough_epSEP 1 1) _ hinv ho
      isRegularPerturbation_shiftMulti hgood hidx', ?_, ?_, ?_⟩
  · change (0 : ℚ) < _
    exact_mod_cast (shiftMulti_twoPointSection_pos_iff (fun _ => (1 / 2 : ℝ))).2 (by norm_num)
  · change (0 : ℚ) < _
    exact_mod_cast (shiftMulti_twoPointSection_pos_iff (fun _ => (-1 / 2 : ℝ))).2 (by norm_num)
  · intro h
    change (0 : ℚ) < _ at h
    have h' := (shiftMulti_twoPointSection_pos_iff (fun _ => (1 : ℝ))).1 (by exact_mod_cast h)
    norm_num at h'

/-- **Corollary 15.4.4 for index `0` on two different perturbations**: for `f(x) = (x, x² − 1)`
over `ℝ` there are canonically oriented regular perturbations `P₀` (with `Λ₀`, perturbed
solutions `±1`) and `P₁` (with `Λ_s`, perturbed solutions `±1/2`), `P₀ ≠ P₁` and with different
supports; they are joined by an oriented compact cobordism over `[0, 1] × ℝ`, and every closed
`0`-form has the same weighted signed count, and the same effective count, over both. -/
theorem corollary_15_4_4_index_zero_two_perturbations :
    ∃ P₀ P₁ : PointPerturbation (epSEP 1 1) twoPointSection,
      P₀.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
        (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation ∧
      P₁.IsCanonical isScFredholmSectionFunctor_twoPointSection.2
        (hasScPlusSectionsThrough_epSEP 1 1) twoPointSectionOrientation ∧
      P₀ ≠ P₁ ∧ P₀.Λ ≠ P₁.Λ ∧
      (fun _ => (1 : ℝ)) ∈ EpGroupoid.supp (fun z => (P₀.Λ (twoPointSection z) : ℚ)) ∧
      (fun _ => (1 : ℝ)) ∉ EpGroupoid.supp (fun z => (P₁.Λ (twoPointSection z) : ℚ)) ∧
      (fun _ => (1 / 2 : ℝ)) ∈ EpGroupoid.supp (fun z => (P₁.Λ (twoPointSection z) : ℚ)) ∧
      (fun _ => (1 / 2 : ℝ)) ∉ EpGroupoid.supp (fun z => (P₀.Λ (twoPointSection z) : ℚ)) ∧
      P₀.HasOrientedCobordism P₁ ∧
      ∀ (τ : (epSEP 1 1).baseEP.epFormsInfty 0), (epSEP 1 1).baseEP.epFormsInftyD 0 τ = 0 →
        P₀.count τ = P₁.count τ ∧
          ∀ hLUC : (epSEP 1 1).X.IsLUC, P₀.countEff hLUC τ = P₁.countEff hLUC τ := by
  obtain ⟨P₀, hΛ₀, h₀, h₀1, -⟩ := exists_isCanonical_twoPointSection
  obtain ⟨P₁, -, h₁, h₁h, -, h₁1⟩ := exists_isCanonical_shiftMulti
  have h₀h : (fun _ => (1 / 2 : ℝ)) ∉
      EpGroupoid.supp (fun z => (P₀.Λ (twoPointSection z) : ℚ)) := by
    intro h
    change (0 : ℚ) < _ at h
    rw [hΛ₀] at h
    have h' := (zeroMultisection_graphSection_epSEP_pos_iff (φ := twoPointMap)
      (fun _ => (1 / 2 : ℝ))).1 (by exact_mod_cast h)
    have h'' := (twoPointMap_eq_zero_iff _).1 h'
    norm_num at h''
  have hΛ : P₀.Λ ≠ P₁.Λ := fun e => h₁1 (by
    change (0 : ℚ) < _
    rw [← e]
    exact h₀1)
  exact ⟨P₀, P₁, h₀, h₁, fun e => hΛ (by rw [e]), hΛ, h₀1, h₁1, h₁h, h₀h,
    hasOrientedCobordism_twoPointSection P₀ P₁ h₀ h₁,
    fun τ hτ => corollary_15_4_4_index_zero_twoPointSection P₀ P₁ h₀ h₁ τ hτ⟩

end TrivialBundle

end Polyfold
