import Polyfold.Chapter1.CylinderCompactInclusions

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 7: integration by parts

For `F` smooth and `1`-periodic in `t` (`SmPer F`) and a test function `φ`,
`∫ F ∂_s φ = -∫ (∂_s F) φ` and `∫ F ∂_t φ = -∫ (∂_t F) φ` on `ℝ × S¹`. Hence the classical
derivatives of `F` are its weak derivatives (`SmPer.hasWeakDeriv`), and every test function
lies in every space `H^{m,δ}(ℝ × S¹)` (`IsTest.mem_Hsub`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-- `F` is smooth and `1`-periodic in `t`. -/
structure SmPer (F : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ F
  periodic : ∀ s t, F (s, t + 1) = F (s, t)

lemma IsTest.smPer {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : SmPer φ := ⟨h.smooth, h.periodic⟩

lemma SmPer.ds {F : ℝ × ℝ → ℝ} (h : SmPer F) : SmPer (Ds F) :=
  ⟨contDiff_Ds h.smooth, fun s t => by
    simp only [Ds]
    have := periodic_fderiv h.periodic (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [this]⟩

lemma SmPer.dt {F : ℝ × ℝ → ℝ} (h : SmPer F) : SmPer (Dt F) :=
  ⟨contDiff_Dt h.smooth, fun s t => by
    simp only [Dt]
    have := periodic_fderiv h.periodic (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [this]⟩

lemma SmPer.iterate_dt {F : ℝ × ℝ → ℝ} (h : SmPer F) : ∀ b, SmPer (Dt^[b] F)
  | 0 => h
  | b + 1 => by rw [Function.iterate_succ_apply']; exact (h.iterate_dt b).dt

lemma SmPer.pDer {F : ℝ × ℝ → ℝ} (h : SmPer F) : ∀ a b, SmPer (pD a b F)
  | 0, b => by simpa [GapP1Sobolev.pD] using h.iterate_dt b
  | a + 1, b => by
    simp only [GapP1Sobolev.pD] at *
    rw [Function.iterate_succ_apply']; exact (h.pDer a b).ds

/-- The product of a test function with a smooth `t`-periodic function is a test function. -/
lemma IsTest.mul_smPer {φ F : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hF : SmPer F) :
    IsTest (fun x => F x * φ x) where
  smooth := hF.smooth.mul hφ.smooth
  periodic s t := by simp only [hF.periodic, hφ.periodic]
  bddSupp := by
    obtain ⟨R, hR⟩ := hφ.bddSupp
    exact ⟨R, fun s t h => by simp [hR s t h]⟩

/-- `∫ ∂_s ψ = 0` for a test function `ψ`. -/
lemma IsTest.integral_ds {ψ : ℝ × ℝ → ℝ} (h : IsTest ψ) : ∫ x, Ds ψ x ∂cyl = 0 := by
  have hint : Integrable (Ds ψ) cyl := memLp_one_iff_integrable.1 (h.ds.memLp 1)
  rw [cyl, integral_prod_symm _ hint]
  have hd : Differentiable ℝ ψ := h.smooth.differentiable (by simp)
  obtain ⟨R, hR⟩ := h.bddSupp
  have inner : ∀ t, ∫ s, Ds ψ (s, t) = 0 := by
    intro t
    have hcs : ∀ (f : ℝ × ℝ → ℝ), IsTest f → HasCompactSupport (fun s => f (s, t)) := by
      intro f hf
      obtain ⟨R', hR'⟩ := hf.bddSupp
      refine HasCompactSupport.intro (isCompact_Icc (a := -R') (b := R')) fun s hs => hR' s t ?_
      simp only [mem_Icc, not_and_or, not_le] at hs
      rw [lt_abs]
      rcases hs with hs | hs
      · right; linarith
      · left; exact hs
    refine integral_eq_zero_of_hasDerivAt_of_integrable (fun s => hasDerivAt_s hd s t) ?_ ?_
    · exact (h.ds.smooth.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport
        (hcs _ h.ds)
    · exact (h.smooth.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport (hcs _ h)
  simp [inner]

/-- `∫ ∂_t ψ = 0` for a test function `ψ` (periodicity in `t`). -/
lemma IsTest.integral_dt {ψ : ℝ × ℝ → ℝ} (h : IsTest ψ) : ∫ x, Dt ψ x ∂cyl = 0 := by
  have hint : Integrable (Dt ψ) cyl := memLp_one_iff_integrable.1 (h.dt.memLp 1)
  rw [cyl, integral_prod _ hint]
  have hd : Differentiable ℝ ψ := h.smooth.differentiable (by simp)
  have inner : ∀ s, ∫ t in Ioc (0 : ℝ) 1, Dt ψ (s, t) = 0 := by
    intro s
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_t hd s t)
        ((h.dt.smooth.continuous.comp (by fun_prop)).intervalIntegrable _ _)]
    have := h.periodic s 0
    rw [zero_add] at this
    rw [this, sub_self]
  simp [inner]

lemma Ds_mul {F G : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : ℝ × ℝ) :
    Ds (fun y => F y * G y) x = Ds F x * G x + F x * Ds G x := by
  simp only [Ds]
  rw [show (fun y => F y * G y) = F * G from rfl, ((hF x).hasFDerivAt.mul (hG x).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma Dt_mul {F G : ℝ × ℝ → ℝ} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : ℝ × ℝ) :
    Dt (fun y => F y * G y) x = Dt F x * G x + F x * Dt G x := by
  simp only [Dt]
  rw [show (fun y => F y * G y) = F * G from rfl, ((hF x).hasFDerivAt.mul (hG x).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Integration by parts in `s`. -/
lemma SmPer.integral_mul_ds {F φ : ℝ × ℝ → ℝ} (hF : SmPer F) (hφ : IsTest φ) :
    ∫ x, F x * Ds φ x ∂cyl = -∫ x, Ds F x * φ x ∂cyl := by
  have hFd : Differentiable ℝ F := hF.smooth.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have h0 := (hφ.mul_smPer hF).integral_ds
  have e : Ds (fun x => F x * φ x) = fun x => Ds F x * φ x + F x * Ds φ x :=
    funext (Ds_mul hFd hφd)
  rw [e, integral_add (memLp_one_iff_integrable.1 ((hφ.mul_smPer hF.ds).memLp 1))
    (memLp_one_iff_integrable.1 ((hφ.ds.mul_smPer hF).memLp 1))] at h0
  linarith

/-- Integration by parts in `t`. -/
lemma SmPer.integral_mul_dt {F φ : ℝ × ℝ → ℝ} (hF : SmPer F) (hφ : IsTest φ) :
    ∫ x, F x * Dt φ x ∂cyl = -∫ x, Dt F x * φ x ∂cyl := by
  have hFd : Differentiable ℝ F := hF.smooth.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have h0 := (hφ.mul_smPer hF).integral_dt
  have e : Dt (fun x => F x * φ x) = fun x => Dt F x * φ x + F x * Dt φ x :=
    funext (Dt_mul hFd hφd)
  rw [e, integral_add (memLp_one_iff_integrable.1 ((hφ.mul_smPer hF.dt).memLp 1))
    (memLp_one_iff_integrable.1 ((hφ.dt.mul_smPer hF).memLp 1))] at h0
  linarith

lemma SmPer.hasWeakDeriv_s {F : ℝ × ℝ → ℝ} (hF : SmPer F) : HasWeakDeriv 1 0 F (Ds F) :=
  fun φ hφ => by
    simp only [GapP1Sobolev.pD, Function.iterate_one, Function.iterate_zero, id]
    rw [hF.integral_mul_ds hφ]; ring

lemma SmPer.hasWeakDeriv_t {F : ℝ × ℝ → ℝ} (hF : SmPer F) : HasWeakDeriv 0 1 F (Dt F) :=
  fun φ hφ => by
    simp only [GapP1Sobolev.pD, Function.iterate_one, Function.iterate_zero, id]
    rw [hF.integral_mul_dt hφ]; ring

/-- The classical derivatives of a smooth `t`-periodic function are its weak derivatives. -/
theorem SmPer.hasWeakDeriv {F : ℝ × ℝ → ℝ} (hF : SmPer F) :
    ∀ a b, HasWeakDeriv a b F (pD a b F)
  | 0, 0 => by simpa [pD] using hasWeakDeriv_zero F
  | 0, b + 1 => by
    have h := hF.hasWeakDeriv 0 b
    have e : pD 0 (b + 1) F = Dt (pD 0 b F) := by
      simp only [pD, Function.iterate_zero, id]; rw [Function.iterate_succ_apply']
    rw [e]; exact h.succ_t (hF.pDer 0 b).hasWeakDeriv_t
  | a + 1, b => by
    have h := hF.hasWeakDeriv a b
    have e : pD (a + 1) b F = Ds (pD a b F) := by
      simp only [pD]; rw [Function.iterate_succ_apply']
    rw [e]; exact h.succ_s (hF.pDer a b).hasWeakDeriv_s

/-- A test function, weighted by `e^{δ|s|}`, is in `L²`. -/
lemma IsTest.memLp_wt {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (δ : ℝ) :
    MemLp (fun x => wt δ x * φ x) 2 cyl := by
  obtain ⟨R, hR⟩ := h.bddSupp
  refine (h.memLp 2).of_le_mul (c := Real.exp (|δ| * |R|))
    ((continuous_wt δ).aestronglyMeasurable.mul (h.memLp 2).1) (ae_of_all _ fun x => ?_)
  obtain ⟨s, t⟩ := x
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos δ _)]
  by_cases hs : R < |s|
  · simp [hR s t hs]
  · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [wt, Real.exp_le_exp]
    push Not at hs
    calc δ * |s| ≤ |δ| * |s| := mul_le_mul_of_nonneg_right (le_abs_self δ) (abs_nonneg _)
      _ ≤ |δ| * |R| := mul_le_mul_of_nonneg_left (hs.trans (le_abs_self R)) (abs_nonneg _)

/-- Every test function lies in `H^{m,δ}(ℝ × S¹)`. -/
theorem IsTest.mem_Hsub {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (h.memLp 2).toLp φ ∈ Hsub m hδ := fun a b _ =>
  ⟨GapP1Sobolev.pD a b φ, (h.smPer.hasWeakDeriv a b).congr_ae (h.memLp 2).coeFn_toLp.symm (ae_eq_refl _),
    (h.pD a b).memLp_wt δ⟩

end Polyfold.GapP1Sobolev
