import Polyfold.Chapter9.SheetIntegrationConcrete
import Polyfold.Chapter9.BranchedIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": **(9.22)**, p. 441 (gap G.107).  Numbers and
pages are the 2021 text's.

# (9.22): `dμ_τ = f̄ · dμ_ω` for `τ = f · ω`

## The text, paraphrased

(p. 441) For the local measures `μ_ω^{U(x)}`, `μ_ω^{eff,U(x)}` of (9.21): if `τ = f · ω`, then
`dμ_τ = f̄ dμ_ω` on `|U(x)|`, with `f̄ ∘ π = f`.

## What is formalized

For the concrete integration `F.sheetIntegration` of `SheetIntegrationConcrete.lean`
(`F : X.FormEval n Ω` an evaluation of forms):

* `F.IsMul τ ω f`: "`τ = f · ω`" read through the evaluation, `τ(α) = f(y) ω(α)` for the frames
  `α` of the tangent spaces `T_yN` of the submanifolds; no product on `Ω` is used.
* `integ_eq_setIntegral_mul`: in the graph chart of a sheet, `∫_A τ|(N, o)` is the integral of
  the density of `ω` multiplied by `f`.
* `localMeasure_eq_sum_setIntegral_mul` (**(9.22)**, exact form): `μ_τ^{U(x)}(K)` is the
  expression (9.21) for `μ_ω^{U(x)}(K)` with `f = f̄ ∘ π` inserted in the integrands over the
  sheets; the same for `μ^{eff,U(x)}` (`localMeasureEff_eq_sum_setIntegral_mul`).
* `abs_localMeasure_sub_le` (**(9.22)**, as an estimate on measurable sets): if
  `|f̄ − a| ≤ ε` on `K`, then `|μ_τ^{U(x)}(K) − a μ_ω^{U(x)}(K)| ≤ ε · M_ω(K)`, where
  `M_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} |ω|` (`absSheetSum`); `localMeasure_eq_mul_of_eqOn`: if `f̄ = a`
  on `K` then `μ_τ^{U(x)}(K) = a μ_ω^{U(x)}(K)`.  The same for the measures of Theorem 9.5.4
  (`abs_branchedMeasure_sub_le`, `branchedMeasure_eq_mul_of_eqOn`).

## The choices made

Mathlib has no integral of a function against a signed measure; `dμ_τ = f̄ dμ_ω` is stated
(i) exactly, through the integrals over the sheets, and (ii) through the estimate above, which
determines `μ_τ` from `μ_ω` and `f̄` (Riemann–Stieltjes sums over partitions of `K` into
measurable pieces on which `f̄` varies by at most `ε`).  The form with the Jordan decomposition of
`μ_ω` is not written.  (2026-11-13) The global form, with Mathlib's integral against a vector
measure (`VectorMeasure.integral`) and its Jordan form, is in `SignedMeasureIntegrals.lean` and
`DensitySignedMeasure.lean` (`branchedMeasure_eq_setIntegral_mul`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

variable {N : Set Obj}

/-- **`τ = f · ω`**, read through the evaluation of the forms on the frames of the tangent
spaces of the submanifolds: `τ(α) = f(y) ω(α)` for `α₁, …, αₙ ∈ T_yN`. -/
def IsMul (τ ω : Ω) (f : Obj → ℝ) : Prop :=
  ∀ N : Set Obj, X.PObj.IsSmoothSubmanifold N → ∀ y ∈ N, ∀ α : Fin n → X.PObj.TangentSpace,
    (∀ i, α i ∈ X.PObj.submanifoldTangent N y) → F.ev τ α = f y * F.ev ω α

variable {F}

theorem IsMul.add_smul {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) (a : ℝ) :
    F.IsMul (τ + a • ω) ω fun y => f y + a := fun N hN y hy α hα => by
  rw [F.ev_add, F.ev_smul, h N hN y hy α hα]; ring

theorem isMul_smul (a : ℝ) (ω : Ω) : F.IsMul (a • ω) ω fun _ => a := fun _ _ _ _ α _ =>
  F.ev_smul a ω α

theorem IsMul.density_eq {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f)
    (hN : X.PObj.IsSmoothSubmanifold N) (c : X.PObj.GraphChart n N)
    (g : Obj → X.PObj.OrTangent) {y : Obj} (hy : y ∈ N) :
    F.density c τ g y = f y * F.density c ω g y := by
  simp only [density, h N hN y hy _ (c.tvec_mem hy)]; ring

/-- **(9.22) in a graph chart**: `∫_A (f ω)|(N, o)` is the integral of the density of `ω`
multiplied by `f`. -/
theorem integ_eq_setIntegral_mul (hN : N ∈ F.sheets) (o : X.PObj.SubmanifoldOrientation N n)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) {A : Set Obj}
    (hA : F.sheetNull.IsMeasIn N A) :
    F.integ τ N o.tangent A = ∫ u in (chart hN).coord '' (A ∩ N),
      f ((chart hN).q u) * F.density (chart hN) ω o.tangent ((chart hN).q u) := by
  rw [integ_eq hN o]
  unfold chartInteg
  refine setIntegral_congr_ae₀ (nullMeasurableSet_coord_image _ hA) (Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  rw [(chart hN).q_coord' hy.2]
  exact h.density_eq hN.1.1 _ _ hy.2

variable (F) in
/-- `∫_A |ω|` over the sheet `N`: the integral of `|ω(∂₁, …, ∂ₙ)|` in the graph chart. -/
def absInteg (hN : N ∈ F.sheets) (ω : Ω) (A : Set Obj) : ℝ :=
  ∫ u in (chart hN).coord '' (A ∩ N), |F.ev ω ((chart hN).tvec ((chart hN).q u))|

theorem absInteg_nonneg (hN : N ∈ F.sheets) (ω : Ω) (A : Set Obj) : 0 ≤ F.absInteg hN ω A :=
  integral_nonneg fun _ => abs_nonneg _

open Classical in
theorem abs_density (c : X.PObj.GraphChart n N) (ω : Ω) (g : Obj → X.PObj.OrTangent)
    (y : Obj) : |F.density c ω g y| = |F.ev ω (c.tvec y)| := by
  unfold density MPolyfold.GraphChart.frameSgn
  split_ifs <;> simp

/-- If `|f| ≤ ε` on `A ∩ N`, then `|∫_A (f ω)|(N, o)| ≤ ε ∫_A |ω|`. -/
theorem abs_integ_le (hN : N ∈ F.sheets) (o : X.PObj.SubmanifoldOrientation N n) {τ ω : Ω}
    {f : Obj → ℝ} (h : F.IsMul τ ω f) {A : Set Obj} (hA : F.sheetNull.IsMeasIn N A) {ε : ℝ}
    (hf : ∀ y ∈ A ∩ N, |f y| ≤ ε) :
    |F.integ τ N o.tangent A| ≤ ε * F.absInteg hN ω A := by
  rw [integ_eq_setIntegral_mul hN o h hA, absInteg, ← integral_const_mul, ← Real.norm_eq_abs]
  have hint : IntegrableOn (fun u => ε * |F.ev ω ((chart hN).tvec ((chart hN).q u))|)
      ((chart hN).coord '' (A ∩ N)) volume :=
    IntegrableOn.mono_set (((integrableOn_chart hN ω).abs).const_mul ε)
      (image_mono inter_subset_right)
  refine norm_integral_le_of_norm_le hint ?_
  refine (ae_restrict_iff'₀ (nullMeasurableSet_coord_image _ hA)).2 (Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  rw [(chart hN).q_coord' hy.2, Real.norm_eq_abs, abs_mul, abs_density]
  exact mul_le_mul_of_nonneg_right (hf y hy) (abs_nonneg _)

/-- **(9.22) on a sheet, as an estimate**: if `|f − a| ≤ ε` on `A ∩ N`, then
`|∫_A (f ω)|(N, o) − a ∫_A ω|(N, o)| ≤ ε ∫_A |ω|`. -/
theorem abs_integ_sub_le (hn : 0 < n) (hN : N ∈ F.sheets)
    (o : X.PObj.SubmanifoldOrientation N n) {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f)
    {A : Set Obj} (hA : F.sheetNull.IsMeasIn N A) {a ε : ℝ}
    (hf : ∀ y ∈ A ∩ N, |f y - a| ≤ ε) :
    |F.integ τ N o.tangent A - a * F.integ ω N o.tangent A| ≤ ε * F.absInteg hN ω A := by
  have h1 := abs_integ_le hN o (h.add_smul (-a)) hA (ε := ε) fun y hy => by
    simpa [sub_eq_add_neg] using hf y hy
  have h2 : F.integ (τ + -a • ω) N o.tangent A =
      F.integ τ N o.tangent A - a * F.integ ω N o.tangent A := by
    have e1 := (F.sheetIntegration hn).integ_add τ (-a • ω) N o.tangent A
    have e2 := (F.sheetIntegration hn).integ_smul (-a) ω N o.tangent A
    rw [sheetIntegration_integ] at e1 e2
    rw [e1, e2]; ring
  rwa [h2] at h1

end FormEval

/-! ### The local measures and the measures of Theorem 9.5.4 -/

namespace OrientedTameStructure

variable {F} {Θ : Obj → ℚ} {x : Obj} (C : X.OrientedTameStructure n Θ x)

variable (F) in
/-- `∑ σᵢ ∫_{A ∩ Mᵢ} |ω|`: the sum (9.20) for the absolute value of the densities. -/
def absSheetSum (hS : ∀ i, C.M i ∈ F.sheets) (ω : Ω) (A : Set Obj) : ℝ :=
  ∑ i, (C.σ i : ℝ) * F.absInteg (hS i) ω (A ∩ C.M i)

theorem absSheetSum_nonneg (hS : ∀ i, C.M i ∈ F.sheets) (ω : Ω) (A : Set Obj) :
    0 ≤ C.absSheetSum F hS ω A :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast (C.σ_pos i).le)
    (FormEval.absInteg_nonneg _ ω _)

/-- **(9.22), exact form for the sum over the sheets.** -/
theorem sheetSum_eq_sum_setIntegral_mul (hn : 0 < n) (hS : ∀ i, C.M i ∈ F.sheets) {τ ω : Ω}
    {f : Obj → ℝ} (h : F.IsMul τ ω f) {A : Set Obj} (hA : C.IsMeas F.sheetNull A) :
    C.sheetSum (F.sheetIntegration hn) τ A =
      ∑ i, (C.σ i : ℝ) * ∫ u in (FormEval.chart (hS i)).coord '' (A ∩ C.M i),
        f ((FormEval.chart (hS i)).q u) *
          F.density (FormEval.chart (hS i)) ω (C.orient i).tangent
            ((FormEval.chart (hS i)).q u) := by
  unfold sheetSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FormEval.sheetIntegration_integ,
    FormEval.integ_eq_setIntegral_mul (hS i) (C.orient i) h
      ((hA i).inter (SheetNullSets.isMeasIn_self _)), inter_assoc, inter_self]

/-- **(9.22) for the sum over the sheets, as an estimate.** -/
theorem abs_sheetSum_sub_le (hn : 0 < n) (hS : ∀ i, C.M i ∈ F.sheets) {τ ω : Ω} {f : Obj → ℝ}
    (h : F.IsMul τ ω f) {A : Set Obj} (hA : C.IsMeas F.sheetNull A) {a ε : ℝ}
    (hf : ∀ y ∈ A, |f y - a| ≤ ε) :
    |C.sheetSum (F.sheetIntegration hn) τ A - a * C.sheetSum (F.sheetIntegration hn) ω A| ≤
      ε * C.absSheetSum F hS ω A := by
  unfold sheetSum absSheetSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hσ : (0 : ℝ) ≤ C.σ i := by exact_mod_cast (C.σ_pos i).le
  have h1 := FormEval.abs_integ_sub_le hn (hS i) (C.orient i) h
    ((hA i).inter (SheetNullSets.isMeasIn_self _)) (a := a) (ε := ε)
    fun y hy => hf y hy.1.1
  rw [FormEval.sheetIntegration_integ]
  calc |(C.σ i : ℝ) * F.integ τ (C.M i) (C.orient i).tangent (A ∩ C.M i) -
        a * ((C.σ i : ℝ) * F.integ ω (C.M i) (C.orient i).tangent (A ∩ C.M i))|
      = (C.σ i : ℝ) * |F.integ τ (C.M i) (C.orient i).tangent (A ∩ C.M i) -
        a * F.integ ω (C.M i) (C.orient i).tangent (A ∩ C.M i)| := by
        rw [← mul_left_comm, ← mul_sub, abs_mul, abs_of_nonneg hσ]
    _ ≤ (C.σ i : ℝ) * (ε * F.absInteg (hS i) ω (A ∩ C.M i)) :=
        mul_le_mul_of_nonneg_left h1 hσ
    _ = ε * ((C.σ i : ℝ) * F.absInteg (hS i) ω (A ∩ C.M i)) := by ring

/-- **(9.22), 2021 p. 441, exact form**: `μ_τ^{U(x)}(K)` for `τ = f · ω` is the expression
(9.21) of `μ_ω^{U(x)}(K)` with `f` inserted in the integrals over the sheets. -/
theorem localMeasure_eq_sum_setIntegral_mul (hn : 0 < n) (hS : ∀ i, C.M i ∈ F.sheets)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) {K : Set X.OrbitSpace}
    (hK : C.IsMeas F.sheetNull (X.π ⁻¹' K)) :
    C.localMeasure (F.sheetIntegration hn) τ K = (Nat.card (X.Isotropy x) : ℝ)⁻¹ *
      ∑ i, (C.σ i : ℝ) * ∫ u in (FormEval.chart (hS i)).coord '' (X.π ⁻¹' K ∩ C.M i),
        f ((FormEval.chart (hS i)).q u) *
          F.density (FormEval.chart (hS i)) ω (C.orient i).tangent
            ((FormEval.chart (hS i)).q u) := by
  unfold localMeasure
  rw [C.sheetSum_eq_sum_setIntegral_mul hn hS h hK]

/-- **(9.22), 2021 p. 441, exact form, for the effective local measure.** -/
theorem localMeasureEff_eq_sum_setIntegral_mul (hn : 0 < n) (hS : ∀ i, C.M i ∈ F.sheets)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) {K : Set X.OrbitSpace}
    (hK : C.IsMeas F.sheetNull (X.π ⁻¹' K)) :
    C.localMeasureEff (F.sheetIntegration hn) τ K = (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ *
      ∑ i, (C.σ i : ℝ) * ∫ u in (FormEval.chart (hS i)).coord '' (X.π ⁻¹' K ∩ C.M i),
        f ((FormEval.chart (hS i)).q u) *
          F.density (FormEval.chart (hS i)) ω (C.orient i).tangent
            ((FormEval.chart (hS i)).q u) := by
  unfold localMeasureEff
  rw [C.sheetSum_eq_sum_setIntegral_mul hn hS h hK]

/-- **(9.22), 2021 p. 441, as an estimate**: if `|f̄ − a| ≤ ε` on `K` (`f = f̄ ∘ π`), then
`|μ_τ^{U(x)}(K) − a μ_ω^{U(x)}(K)| ≤ ε · (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} |ω|`. -/
theorem abs_localMeasure_sub_le (hn : 0 < n) (hS : ∀ i, C.M i ∈ F.sheets) {τ ω : Ω}
    {f : Obj → ℝ} (h : F.IsMul τ ω f) {K : Set X.OrbitSpace}
    (hK : C.IsMeas F.sheetNull (X.π ⁻¹' K)) {a ε : ℝ} (hf : ∀ y, X.π y ∈ K → |f y - a| ≤ ε) :
    |C.localMeasure (F.sheetIntegration hn) τ K -
        a * C.localMeasure (F.sheetIntegration hn) ω K| ≤
      ε * ((Nat.card (X.Isotropy x) : ℝ)⁻¹ * C.absSheetSum F hS ω (X.π ⁻¹' K)) := by
  unfold localMeasure
  have hc : (0 : ℝ) ≤ (Nat.card (X.Isotropy x) : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have h1 := C.abs_sheetSum_sub_le hn hS h hK (a := a) (ε := ε) fun y hy => hf y hy
  calc _ = (Nat.card (X.Isotropy x) : ℝ)⁻¹ *
        |C.sheetSum (F.sheetIntegration hn) τ (X.π ⁻¹' K) -
          a * C.sheetSum (F.sheetIntegration hn) ω (X.π ⁻¹' K)| := by
        rw [← mul_left_comm, ← mul_sub, abs_mul, abs_of_nonneg hc]
    _ ≤ (Nat.card (X.Isotropy x) : ℝ)⁻¹ * (ε * C.absSheetSum F hS ω (X.π ⁻¹' K)) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = _ := by ring

/-- **(9.22) where `f̄` is constant**: if `f̄ = a` on `K`, then
`μ_τ^{U(x)}(K) = a μ_ω^{U(x)}(K)`. -/
theorem localMeasure_eq_mul_of_eqOn (hn : 0 < n) (hS : ∀ i, C.M i ∈ F.sheets) {τ ω : Ω}
    {f : Obj → ℝ} (h : F.IsMul τ ω f) {K : Set X.OrbitSpace}
    (hK : C.IsMeas F.sheetNull (X.π ⁻¹' K)) {a : ℝ} (hf : ∀ y, X.π y ∈ K → f y = a) :
    C.localMeasure (F.sheetIntegration hn) τ K =
      a * C.localMeasure (F.sheetIntegration hn) ω K := by
  have h1 := C.abs_localMeasure_sub_le hn hS h hK (a := a) (ε := 0) fun y hy => by
    rw [hf y hy, sub_self, abs_zero]
  rw [zero_mul] at h1
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm h1 (abs_nonneg _)))

end OrientedTameStructure

section Global

variable {F} {Θ : Obj → ℚ}

/-- **(9.22) for the measure of Theorem 9.5.4, as an estimate**: for a measurable
`K ⊆ |U(x)|` on which `|f̄ − a| ≤ ε`,
`|μ_τ^Θ̂(K) − a μ_ω^Θ̂(K)| ≤ ε · (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} |ω|`. -/
theorem abs_branchedMeasure_sub_le (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (hS : ∀ i, C.M i ∈ F.sheets) (hCT : C.Represents T)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K)
    (hKU : Subtype.val '' K ⊆ X.π '' C.U) {a ε : ℝ}
    (hf : ∀ y, X.π y ∈ Subtype.val '' K → |f y - a| ≤ ε) :
    |branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov τ K -
        a * branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov ω K| ≤
      ε * ((Nat.card (X.Isotropy x) : ℝ)⁻¹ *
        C.absSheetSum F hS ω (X.π ⁻¹' (Subtype.val '' K))) := by
  have hTS : X.HasTameSheetsIn F.sheets Θ := fun x hx => by
    obtain ⟨C', hC', -⟩ := hcov x hx
    exact ⟨C'.toTameBranchingStructure, hC'⟩
  rw [branchedMeasure_apply (F.sheetIntegration hn) hΘ hcpt hT hcov τ C hS hCT hK hKU,
    branchedMeasure_apply (F.sheetIntegration hn) hΘ hcpt hT hcov ω C hS hCT hK hKU]
  exact C.abs_localMeasure_sub_le hn hS h (C.isMeas_preimage hTS hS hK) hf

/-- **(9.22) for the measure of Theorem 9.5.4, where `f̄` is constant**: for a measurable
`K ⊆ |U(x)|` on which `f̄ = a`, `μ_τ^Θ̂(K) = a μ_ω^Θ̂(K)`. -/
theorem branchedMeasure_eq_mul_of_eqOn (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T)
    {τ ω : Ω} {f : Obj → ℝ} (h : F.IsMul τ ω f) {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (hS : ∀ i, C.M i ∈ F.sheets) (hCT : C.Represents T)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K)
    (hKU : Subtype.val '' K ⊆ X.π '' C.U) {a : ℝ}
    (hf : ∀ y, X.π y ∈ Subtype.val '' K → f y = a) :
    branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov τ K =
      a * branchedMeasure (F.sheetIntegration hn) hΘ hcpt hT hcov ω K := by
  have hTS : X.HasTameSheetsIn F.sheets Θ := fun x hx => by
    obtain ⟨C', hC', -⟩ := hcov x hx
    exact ⟨C'.toTameBranchingStructure, hC'⟩
  rw [branchedMeasure_apply (F.sheetIntegration hn) hΘ hcpt hT hcov τ C hS hCT hK hKU,
    branchedMeasure_apply (F.sheetIntegration hn) hΘ hcpt hT hcov ω C hS hCT hK hKU]
  exact C.localMeasure_eq_mul_of_eqOn hn hS h (C.isMeas_preimage hTS hS hK) hf

end Global

end EpGroupoid

end Polyfold
