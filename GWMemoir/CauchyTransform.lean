import Mathlib

/-!
# The Cauchy transform solves `∂̄ξ = η` for smooth compactly supported `η`

The classical input of the vanishing of the cokernel of `∂̄` on the Riemann sphere
(`H^{0,1}(P¹, ℂⁿ) = 0`, used in HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248,
no. 1179, §4 at the constant maps).  The target is a real Banach space `E` with a complex
structure `J₀`, `J₀² = -1`, so `ℂ` acts on `E` by `cmulL J₀ (a + bi) = a + b J₀`.

* `dbar J₀ F z = ½ (dF(z) 1 + J₀ dF(z) i)`, the `(0,1)`-part of `dF(z)`.
* `cauchyKer w = 1/(π w)`, locally integrable on `ℂ` (`locallyIntegrable_cauchyKer`).
* `cauchyT J₀ g z = ∫ (1/(π t)) g(z - t) dA(t) = (1/π) ∫ g(w)/(z - w) dA(w)`, the convolution
  with `cauchyKer`.
* **`contDiff_cauchyT`**: for `g` smooth with compact support, `cauchyT g` is smooth.
* **`pompeiu`**: `∫ (1/(π t)) ∂̄g(z - t) dA(t) = g(z)` for `g` of class `C¹` with compact support
  (polar coordinates around `z`: the radial part integrates to `-g(z)`, the angular part to `0`).
* **`dbar_cauchyT`**: `∂̄ (cauchyT g) = g`.
-/

open scoped Topology ContDiff Real Convolution

set_option linter.unusedSectionVars false
open Set Filter MeasureTheory Metric

noncomputable section

namespace GWMemoir

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (J₀ : E →L[ℝ] E)

/-! ## 1. The action of `ℂ` through `J₀` -/

/-- `c ↦ (v ↦ (Re c) v + (Im c) J₀ v)`. -/
def cmulL : ℂ →L[ℝ] E →L[ℝ] E :=
  Complex.reCLM.smulRight (ContinuousLinearMap.id ℝ E) + Complex.imCLM.smulRight J₀

lemma cmulL_apply (c : ℂ) (v : E) : cmulL J₀ c v = c.re • v + c.im • J₀ v := by
  simp [cmulL]

lemma cmulL_J (c : ℂ) (v : E) : J₀ (cmulL J₀ c v) = cmulL J₀ c (J₀ v) := by
  simp [cmulL_apply, map_add, map_smul]

lemma cmulL_ofReal (a : ℝ) (v : E) : cmulL J₀ (a : ℂ) v = a • v := by
  simp [cmulL_apply]

/-- The `(0,1)`-part of `dF(z)`: `∂̄F(z) = ½ (dF(z) 1 + J₀ dF(z) i)`. -/
def dbar (F : ℂ → E) (z : ℂ) : E :=
  (1 / 2 : ℝ) • (fderiv ℝ F z 1 + J₀ (fderiv ℝ F z Complex.I))

/-! ## 2. The kernel -/

/-- The Cauchy kernel `1/(π w)`. -/
def cauchyKer (w : ℂ) : ℂ := ((π : ℂ) * w)⁻¹

lemma cauchyKer_neg (w : ℂ) : cauchyKer (-w) = -cauchyKer w := by
  simp [cauchyKer, mul_neg, inv_neg]

lemma measurable_cauchyKer : Measurable cauchyKer :=
  (measurable_const.mul measurable_id).inv

lemma norm_cauchyKer (w : ℂ) : ‖cauchyKer w‖ = π⁻¹ * ‖w‖ ^ (-1 : ℝ) := by
  rw [cauchyKer, norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Real.rpow_neg_one, mul_inv]

/-- **`1/(π w)` is locally integrable on `ℂ`.** -/
theorem locallyIntegrable_cauchyKer : LocallyIntegrable cauchyKer volume := by
  refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (C := π⁻¹) (α := 1) (by simp) (by simp)
    (Eventually.of_forall fun w => (norm_cauchyKer w).le)
    measurable_cauchyKer.aestronglyMeasurable

/-! ## 3. The Cauchy transform -/

/-- **The Cauchy transform** `(Tg)(z) = ∫ (1/(π t)) g(z - t) dA(t)`. -/
def cauchyT (g : ℂ → E) : ℂ → E := cauchyKer ⋆[cmulL J₀, volume] g

lemma cauchyT_apply (g : ℂ → E) (z : ℂ) :
    cauchyT J₀ g z = ∫ t, cmulL J₀ (cauchyKer t) (g (z - t)) := rfl

variable {J₀}

/-- **The Cauchy transform of a smooth compactly supported function is smooth.** -/
theorem contDiff_cauchyT {g : ℂ → E} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyT J₀ g) :=
  hc.contDiff_convolution_right (cmulL J₀) locallyIntegrable_cauchyKer hg

lemma hasFDerivAt_cauchyT {g : ℂ → E} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (z : ℂ) :
    HasFDerivAt (cauchyT J₀ g)
      ((cauchyKer ⋆[(cmulL J₀).precompR ℂ, volume] fderiv ℝ g) z) z :=
  hc.hasFDerivAt_convolution_right (cmulL J₀) locallyIntegrable_cauchyKer hg z

lemma fderiv_cauchyT_apply {g : ℂ → E} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (z v : ℂ) :
    fderiv ℝ (cauchyT J₀ g) z v = ∫ t, cmulL J₀ (cauchyKer t) (fderiv ℝ g (z - t) v) := by
  rw [(hasFDerivAt_cauchyT hg hc z).fderiv]
  exact convolution_precompR_apply (cmulL J₀) locallyIntegrable_cauchyKer (hc.fderiv ℝ)
    (hg.continuous_fderiv one_ne_zero) z v

lemma integrable_cauchy {g : ℂ → E} (hg : Continuous g) (hc : HasCompactSupport g) (z : ℂ) :
    Integrable fun t => cmulL J₀ (cauchyKer t) (g (z - t)) :=
  hc.convolutionExists_right (cmulL J₀) locallyIntegrable_cauchyKer hg z

/-- `∂̄ (Tg)(z) = ∫ (1/(π t)) ∂̄g(z - t) dA(t)`. -/
lemma dbar_cauchyT_eq {g : ℂ → E} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (z : ℂ) :
    dbar J₀ (cauchyT J₀ g) z = ∫ t, cmulL J₀ (cauchyKer t) (dbar J₀ g (z - t)) := by
  have hd : ∀ v : ℂ, Continuous fun x => fderiv ℝ g x v := fun v =>
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcd : ∀ v : ℂ, HasCompactSupport fun x => fderiv ℝ g x v := fun v =>
    (HasCompactSupport.fderiv (𝕜 := ℝ) hc).comp_left (g := fun L : ℂ →L[ℝ] E => L v) rfl
  have i1 := integrable_cauchy (J₀ := J₀) (hd 1) (hcd 1) z
  have i2 := integrable_cauchy (J₀ := J₀) (hd Complex.I) (hcd Complex.I) z
  rw [dbar, fderiv_cauchyT_apply hg hc, fderiv_cauchyT_apply hg hc,
    ← J₀.integral_comp_comm i2, ← integral_add i1 (J₀.integrable_comp i2),
    ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [dbar, map_smul, map_add, cmulL_J]

/-! ## 4. Pompeiu's formula -/

/-- `e(θ) = cos θ + i sin θ`. -/
def eAng (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

lemma eAng_eq (θ : ℝ) : eAng θ = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • Complex.I := by
  simp [eAng, Complex.real_smul]

lemma I_mul_eAng (θ : ℝ) :
    Complex.I * eAng θ = (-Real.sin θ : ℝ) • (1 : ℂ) + (Real.cos θ : ℝ) • Complex.I := by
  apply Complex.ext <;> simp [eAng]

lemma eAng_mul_conj (θ : ℝ) : eAng θ * (Real.cos θ - Real.sin θ * Complex.I) = 1 := by
  apply Complex.ext <;> simp only [eAng, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

lemma hasDerivAt_eAng (θ : ℝ) : HasDerivAt eAng (Complex.I * eAng θ) θ := by
  have h1 := (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I
  refine (h1.add h2).congr_deriv ?_
  simp only [eAng]; push_cast; ring_nf; rw [Complex.I_sq]; ring

variable (J₀) in
/-- In the direction `e(θ)`: `e(θ)⁻¹ ∂̄L = ½ (L e(θ) + J₀ L (i e(θ)))`. -/
lemma dbar_rotate (hJ : ∀ v, J₀ (J₀ v) = -v) (L : ℂ →L[ℝ] E) (θ : ℝ) :
    cmulL J₀ (Real.cos θ - Real.sin θ * Complex.I) ((1 / 2 : ℝ) • (L 1 + J₀ (L Complex.I))) =
      (1 / 2 : ℝ) • (L (eAng θ) + J₀ (L (Complex.I * eAng θ))) := by
  rw [I_mul_eAng, eAng_eq]
  simp only [map_add, map_smul, cmulL_apply, hJ, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im,
    Complex.mul_im]
  module

lemma norm_eAng (θ : ℝ) : ‖eAng θ‖ = 1 := by
  rw [eAng, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I,
    Complex.norm_exp_ofReal_mul_I]

lemma continuous_eAng : Continuous eAng := by unfold eAng; fun_prop

lemma eAng_ne_zero (θ : ℝ) : eAng θ ≠ 0 := fun h => by simpa [h] using norm_eAng θ

lemma smul_cmulL (a : ℝ) (c : ℂ) (v : E) : a • cmulL J₀ c v = cmulL J₀ (a * c) v := by
  rw [← Complex.real_smul, map_smul, smul_apply]

variable {g : ℂ → E}

lemma exists_radius (hc : HasCompactSupport g) (z : ℂ) :
    ∃ R₀ : ℝ, ∀ r θ : ℝ, R₀ < |r| →
      g (z + (r : ℂ) * eAng θ) = 0 ∧ fderiv ℝ g (z + (r : ℂ) * eAng θ) = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R + ‖z‖, fun r θ hr => ?_⟩
  have hx : z + (r : ℂ) * eAng θ ∉ tsupport g := fun h => by
    have h1 := mem_closedBall_zero_iff.1 (hR h)
    have h2 : ‖(r : ℂ) * eAng θ‖ = |r| := by
      rw [norm_mul, norm_eAng, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_sub_norm_le ((r : ℂ) * eAng θ) (-z)
    rw [sub_neg_eq_add, add_comm, norm_neg, h2] at h3
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx⟩

lemma integrableOn_target {F : ℝ × ℝ → E} (hF : Continuous F) {R₀ : ℝ}
    (h : ∀ p : ℝ × ℝ, R₀ < |p.1| → F p = 0) : IntegrableOn F (Ioi 0 ×ˢ Ioo (-π) π) := by
  refine (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-R₀) R₀ ×ˢ Icc (-π) π))).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => h p ?_
  obtain ⟨⟨-, hθ⟩, hn⟩ := hp
  by_contra hle
  exact hn ⟨abs_le.1 (not_lt.1 hle), Ioo_subset_Icc_self hθ⟩

lemma integrableOn_target_swap {F : ℝ × ℝ → E} (hF : Continuous F) {R₀ : ℝ}
    (h : ∀ p : ℝ × ℝ, R₀ < |p.2| → F p = 0) : IntegrableOn F (Ioo (-π) π ×ˢ Ioi 0) := by
  refine (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-π) π ×ˢ Icc (-R₀) R₀))).of_forall_sdiff_eq_zero
    (measurableSet_Ioo.prod measurableSet_Ioi) fun p hp => h p ?_
  obtain ⟨⟨hθ, -⟩, hn⟩ := hp
  by_contra hle
  exact hn ⟨Ioo_subset_Icc_self hθ, abs_le.1 (not_lt.1 hle)⟩

lemma hasDerivAt_ray (z : ℂ) (θ r : ℝ) :
    HasDerivAt (fun r : ℝ => z + (r : ℂ) * eAng θ) (eAng θ) r := by
  simpa using ((hasDerivAt_id r).ofReal_comp.mul_const (eAng θ)).const_add z

lemma hasDerivAt_circ (z : ℂ) (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => z + (r : ℂ) * eAng θ) ((r : ℂ) * (Complex.I * eAng θ)) θ :=
  ((hasDerivAt_eAng θ).const_mul (r : ℂ)).const_add z

/-- The radial part: `∫_0^∞ ∂_r g(z + r e(θ)) dr = -g(z)`. -/
lemma integral_radial (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (z : ℂ) (θ : ℝ) :
    ∫ r : ℝ in Ioi 0, fderiv ℝ g (z + (r : ℂ) * eAng θ) (eAng θ) = -g z := by
  obtain ⟨R₀, hR₀⟩ := exists_radius hc z
  set f : ℝ → E := fun r => g (z + (r : ℂ) * eAng θ)
  have hf : ContDiff ℝ 1 f :=
    hg.comp (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const))
  have hcf : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R₀) R₀))
      fun r hr => (hR₀ r θ (by
        by_contra hle; exact hr (abs_le.1 (not_lt.1 hle)))).1
  have hd : ∀ r : ℝ, deriv f r = fderiv ℝ g (z + (r : ℂ) * eAng θ) (eAng θ) := fun r =>
    (((hg.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_ray z θ r)).deriv
  simp_rw [← hd]
  rw [hcf.integral_Ioi_deriv_eq hf 0]
  simp [f]

/-- The angular part: `∫_{-π}^{π} ∂_θ g(z + r e(θ)) dθ = 0`. -/
lemma integral_angular (hg : ContDiff ℝ 1 g) (z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    ∫ θ in Ioo (-π) π, fderiv ℝ g (z + (r : ℂ) * eAng θ) (Complex.I * eAng θ) = 0 := by
  have hφ : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => g (z + (r : ℂ) * eAng θ))
      (fderiv ℝ g (z + (r : ℂ) * eAng θ) ((r : ℂ) * (Complex.I * eAng θ))) θ := fun θ =>
    ((hg.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circ z r θ)
  have hcont : Continuous fun θ : ℝ =>
      fderiv ℝ g (z + (r : ℂ) * eAng θ) ((r : ℂ) * (Complex.I * eAng θ)) :=
    ((hg.continuous_fderiv one_ne_zero).comp (continuous_const.add
      (continuous_const.mul continuous_eAng))).clm_apply
      (continuous_const.mul (continuous_const.mul continuous_eAng))
  have e : ∀ θ : ℝ, fderiv ℝ g (z + (r : ℂ) * eAng θ) (Complex.I * eAng θ) =
      r⁻¹ • fderiv ℝ g (z + (r : ℂ) * eAng θ) ((r : ℂ) * (Complex.I * eAng θ)) := fun θ => by
    rw [show (r : ℂ) * (Complex.I * eAng θ) = r • (Complex.I * eAng θ) from
      (Complex.real_smul ..).symm, map_smul, smul_smul, inv_mul_cancel₀ hr, one_smul]
  simp_rw [e]
  rw [integral_smul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hφ θ)
      (hcont.intervalIntegrable _ _)]
  simp [eAng]

/-- **Pompeiu's formula** for `g` of class `C¹` with compact support:
`∫ (1/(π t)) ∂̄g(z - t) dA(t) = g(z)`. -/
theorem pompeiu (hJ : ∀ v, J₀ (J₀ v) = -v) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (z : ℂ) : ∫ t, cmulL J₀ (cauchyKer t) (dbar J₀ g (z - t)) = g z := by
  obtain ⟨R₀, hR₀⟩ := exists_radius hc z
  set A : ℝ × ℝ → E := fun p => fderiv ℝ g (z + (p.1 : ℂ) * eAng p.2) (eAng p.2) with hA
  set B : ℝ × ℝ → E := fun p =>
    fderiv ℝ g (z + (p.1 : ℂ) * eAng p.2) (Complex.I * eAng p.2) with hB
  have hpc : Continuous fun p : ℝ × ℝ => fderiv ℝ g (z + (p.1 : ℂ) * eAng p.2) :=
    (hg.continuous_fderiv one_ne_zero).comp (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_fst).mul (continuous_eAng.comp continuous_snd)))
  have hAc : Continuous A := hpc.clm_apply (continuous_eAng.comp continuous_snd)
  have hBc : Continuous B :=
    hpc.clm_apply (continuous_const.mul (continuous_eAng.comp continuous_snd))
  have hAi : IntegrableOn A polarCoord.target := integrableOn_target hAc (R₀ := R₀) fun p hp => by
    simp only [hA, (hR₀ p.1 p.2 hp).2, zero_apply]
  have hBi : IntegrableOn B polarCoord.target := integrableOn_target hBc (R₀ := R₀) fun p hp => by
    simp only [hB, (hR₀ p.1 p.2 hp).2, zero_apply]
  have hAis := integrableOn_target_swap (hAc.comp continuous_swap) (R₀ := R₀) fun p hp => by
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, hA, (hR₀ p.2 p.1 hp).2,
      zero_apply]
  -- `t ↦ -t`
  have e1 : ∫ t, cmulL J₀ (cauchyKer t) (dbar J₀ g (z - t)) =
      -∫ w, cmulL J₀ (cauchyKer w) (dbar J₀ g (z + w)) := by
    rw [← integral_neg_eq_self, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [cauchyKer_neg, map_neg, sub_neg_eq_add, neg_apply]
  -- polar coordinates
  have e2 : ∫ w, cmulL J₀ (cauchyKer w) (dbar J₀ g (z + w)) =
      ∫ p in polarCoord.target, (π⁻¹ * (1 / 2 : ℝ)) • (A p + J₀ (B p)) := by
    rw [← Complex.integral_comp_polarCoord_symm]
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    have hr : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hp.1)
    rw [Complex.polarCoord_symm_apply]
    change p.1 • cmulL J₀ (cauchyKer ((p.1 : ℂ) * eAng p.2))
      (dbar J₀ g (z + (p.1 : ℂ) * eAng p.2)) = _
    have hk : (p.1 : ℂ) * cauchyKer ((p.1 : ℂ) * eAng p.2) =
        ((π⁻¹ : ℝ) : ℂ) * (Real.cos p.2 - Real.sin p.2 * Complex.I) := by
      have hinv : (eAng p.2)⁻¹ = Real.cos p.2 - Real.sin p.2 * Complex.I :=
        inv_eq_of_mul_eq_one_right (eAng_mul_conj p.2)
      rw [cauchyKer, ← hinv]
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
      have he := eAng_ne_zero p.2
      push_cast
      field_simp
    rw [smul_cmulL, hk, ← smul_cmulL, dbar, dbar_rotate J₀ hJ, smul_smul]
  rw [e1, e2, integral_smul, integral_add hAi (J₀.integrable_comp hBi),
    J₀.integral_comp_comm hBi]
  -- the radial part
  have hAint : ∫ p in polarCoord.target, A p = -((2 * π : ℝ) • g z) := by
    rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl, Measure.volume_eq_prod,
      ← setIntegral_prod_swap, setIntegral_prod (fun q => A q.swap) hAis]
    have : ∀ θ, ∫ r in Ioi (0 : ℝ), A (θ, r).swap = -g z := fun θ => integral_radial hg hc z θ
    simp_rw [this]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_neg]
    congr 2; ring
  -- the angular part
  have hBint : ∫ p in polarCoord.target, B p = 0 := by
    rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl, Measure.volume_eq_prod,
      setIntegral_prod _ hBi]
    rw [setIntegral_congr_fun measurableSet_Ioi fun r hr =>
      integral_angular hg z (ne_of_gt (mem_Ioi.1 hr)), integral_zero]
  rw [hAint, hBint, map_zero, add_zero, smul_neg, neg_neg, smul_smul]
  convert one_smul ℝ (g z) using 2
  field_simp

/-- **The Cauchy transform solves `∂̄ξ = g`** for `g` of class `C¹` with compact support. -/
theorem dbar_cauchyT (hJ : ∀ v, J₀ (J₀ v) = -v) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (z : ℂ) : dbar J₀ (cauchyT J₀ g) z = g z := by
  rw [dbar_cauchyT_eq hg hc]; exact pompeiu hJ hg hc z

/-! ## 5. The chain rule for `∂̄` under `z ↦ a z` and `z ↦ 1/z` -/

variable (J₀) in
/-- `∂̄` of a real-linear map: `½ (L 1 + J₀ L i)`. -/
def dbarL (L : ℂ →L[ℝ] E) : E := (1 / 2 : ℝ) • (L 1 + J₀ (L Complex.I))

lemma dbar_eq_dbarL (F : ℂ → E) (z : ℂ) : dbar J₀ F z = dbarL J₀ (fderiv ℝ F z) := rfl

lemma cmulL_mul (hJ : ∀ v, J₀ (J₀ v) = -v) (a b : ℂ) (v : E) :
    cmulL J₀ (a * b) v = cmulL J₀ a (cmulL J₀ b v) := by
  simp only [cmulL_apply, Complex.mul_re, Complex.mul_im, map_add, map_smul, hJ]
  module

/-- `∂̄ (L ∘ (a ·)) = ā ∂̄L`. -/
lemma dbarL_comp_mul (hJ : ∀ v, J₀ (J₀ v) = -v) (L : ℂ →L[ℝ] E) (a : ℂ) :
    dbarL J₀ (L.comp ((ContinuousLinearMap.mul ℝ ℂ) a)) =
      cmulL J₀ ((starRingEnd ℂ) a) (dbarL J₀ L) := by
  have h1 : a = a.re • (1 : ℂ) + a.im • Complex.I := by apply Complex.ext <;> simp
  have h2 : a * Complex.I = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp
  have e1 : L a = a.re • L 1 + a.im • L Complex.I := by
    conv_lhs => rw [h1]
    rw [map_add, map_smul, map_smul]
  have e2 : L (a * Complex.I) = (-a.im) • L 1 + a.re • L Complex.I := by
    rw [h2, map_add, map_smul, map_smul]
  simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_one, e1,
    e2, map_add, map_smul, cmulL_apply, Complex.conj_re, Complex.conj_im, hJ]
  module

lemma hasFDerivAt_inv_real {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => z⁻¹) ((ContinuousLinearMap.mul ℝ ℂ) (-(w ^ 2)⁻¹)) w := by
  refine ((hasDerivAt_inv hw).hasFDerivAt.restrictScalars ℝ).congr_fderiv ?_
  exact ContinuousLinearMap.ext fun v => by simp [mul_comm]

/-- **`∂̄ (F ∘ (1/·))(w) = conj(-1/w²) ∂̄F(1/w)`.** -/
lemma dbar_comp_inv (hJ : ∀ v, J₀ (J₀ v) = -v) {F : ℂ → E} {w : ℂ} (hw : w ≠ 0)
    (hF : DifferentiableAt ℝ F w⁻¹) :
    dbar J₀ (fun z => F z⁻¹) w =
      cmulL J₀ ((starRingEnd ℂ) (-(w ^ 2)⁻¹)) (dbar J₀ F w⁻¹) := by
  have h := hF.hasFDerivAt.comp w (hasFDerivAt_inv_real hw)
  rw [dbar_eq_dbarL, show (fun z => F z⁻¹) = F ∘ fun z : ℂ => z⁻¹ from rfl, h.fderiv,
    dbarL_comp_mul hJ]
  rfl

/-! ## 6. The Cauchy transform at infinity -/

variable (J₀) in
/-- `w ↦ (Tg)(1/w)`, `0` at `w = 0` (the transform read in the chart at `∞`). -/
def cauchyTInv (g : ℂ → E) (w : ℂ) : E := if w = 0 then 0 else cauchyT J₀ g w⁻¹

lemma cauchyTInv_of_ne {w : ℂ} (hw : w ≠ 0) : cauchyTInv J₀ g w = cauchyT J₀ g w⁻¹ := if_neg hw

/-- The integrand of `cauchyTInv` as a parametric integral: `w / (π (1 - w s)) · g(s)`. -/
def invKer (w s : ℂ) : ℂ := w * ((π : ℂ) * (1 - w * s))⁻¹

lemma cauchyKer_inv_sub {w : ℂ} (hw : w ≠ 0) (s : ℂ) : cauchyKer (w⁻¹ - s) = invKer w s := by
  rw [cauchyKer, invKer, show w⁻¹ - s = (1 - w * s) * w⁻¹ by field_simp, ← mul_assoc,
    mul_inv, inv_inv, mul_comm]

/-- `cauchyTInv g w = ∫ (w / (π (1 - w s))) g(s) dA(s)`, for every `w`. -/
lemma cauchyTInv_eq_integral (w : ℂ) :
    cauchyTInv J₀ g w = ∫ s, cmulL J₀ (invKer w s) (g s) := by
  by_cases hw : w = 0
  · simp [cauchyTInv, hw, invKer]
  rw [cauchyTInv_of_ne hw, cauchyT_apply, ← integral_sub_left_eq_self _ volume w⁻¹]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [sub_sub_cancel, cauchyKer_inv_sub hw]

/-- **The Cauchy transform is smooth at `∞`**: for `g` smooth with compact support,
`w ↦ (Tg)(1/w)` (with the value `0` at `w = 0`) is smooth on `ℂ`. -/
theorem contDiff_cauchyTInv (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyTInv J₀ g) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hR' : tsupport g ⊆ closedBall 0 (max R 1) :=
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))
  set R₁ := max R 1
  have hR₁ : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [contDiff_iff_contDiffAt]
  intro w₀
  by_cases hw₀ : w₀ = 0
  swap
  · -- away from `0`: the composite with `z ↦ 1/z`
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => cauchyT J₀ g w⁻¹) w₀ :=
      (contDiff_cauchyT hg hc).contDiffAt.comp w₀
        ((contDiffAt_inv ℂ hw₀).restrict_scalars ℝ)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hw₀] with w hw
    exact cauchyTInv_of_ne hw
  -- near `0`: a parametric integral with compactly supported smooth integrand
  subst hw₀
  set G : ℂ → ℂ → E := fun p x => cmulL J₀ (invKer p (-x)) (g (-x))
  have hgs : ∀ p x, p ∈ ball (0 : ℂ) R₁⁻¹ → x ∉ closedBall (0 : ℂ) R₁ → G p x = 0 := by
    intro p x _ hx
    have : -x ∉ tsupport g := fun h => hx (by simpa using hR' h)
    simp [G, image_eq_zero_of_notMem_tsupport this]
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) (ball (0 : ℂ) R₁⁻¹ ×ˢ univ) := by
    rintro ⟨p, x⟩ ⟨hp, -⟩
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hx : -x ∈ tsupport g
    · have hxn : ‖x‖ ≤ R₁ := by simpa using hR' hx
      have hpn : ‖p‖ < R₁⁻¹ := by simpa using hp
      have hne : (π : ℂ) * (1 - p * -x) ≠ 0 := by
        refine mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_pos.ne') fun h => ?_
        have h1 : p * x = -1 := by linear_combination h
        have h2 : ‖p * x‖ < 1 := by
          rw [norm_mul]
          calc ‖p‖ * ‖x‖ ≤ ‖p‖ * R₁ := mul_le_mul_of_nonneg_left hxn (norm_nonneg _)
            _ < R₁⁻¹ * R₁ := mul_lt_mul_of_pos_right hpn hR₁
            _ = 1 := inv_mul_cancel₀ hR₁.ne'
        rw [h1] at h2; simp at h2
      have hk : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => invKer q.1 (-q.2)) (p, x) := by
        unfold invKer
        refine contDiffAt_fst.mul (ContDiffAt.inv ?_ hne)
        exact contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_fst.mul contDiffAt_snd.neg))
      exact (((cmulL J₀).contDiff.contDiffAt.comp _ hk)).clm_apply
        (hg.contDiffAt.comp _ contDiffAt_snd.neg)
    · have hopen : IsOpen {q : ℂ × ℂ | -q.2 ∉ tsupport g} :=
        (isClosed_tsupport g).isOpen_compl.preimage (continuous_snd.neg)
      refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hx] with q hq
      change cmulL J₀ (invKer q.1 (-q.2)) (g (-q.2)) = 0
      rw [image_eq_zero_of_notMem_tsupport hq, map_zero]
  have hconv := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) (v := fun _ : ℂ => (0 : ℂ))
    contDiffOn_const (f := fun _ : ℂ => (1 : ℝ)) isOpen_ball (isCompact_closedBall 0 R₁) hgs
    (locallyIntegrable_const 1) hG
  refine (hconv.contDiffAt (isOpen_ball.mem_nhds (by simpa using hR₁))).congr_of_eventuallyEq
    (Eventually.of_forall fun w => ?_)
  rw [cauchyTInv_eq_integral]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, one_smul, zero_sub, neg_neg, G]

/-! ## 7. The two charts of the Riemann sphere -/

lemma smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  have h := Real.smoothTransition.pos_denom x
  simp only [Real.smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x)), ← add_div, div_self h.ne']

/-- A cut-off on `ℂ`, `1` near `0`, `0` for `|z|² ≥ 3`, with `χ(z) + χ(1/z) = 1`:
`χ(z) = τ(½ - (|z|² - 1)/(|z|² + 1))`, `τ` the smooth transition. -/
def cutS (z : ℂ) : ℝ := Real.smoothTransition (1 / 2 - (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1))

lemma contDiff_cutS : ContDiff ℝ ∞ cutS := by
  unfold cutS
  refine Real.smoothTransition.contDiff.comp (contDiff_const.sub ?_)
  exact ((contDiff_norm_sq ℝ).sub contDiff_const).div ((contDiff_norm_sq ℝ).add contDiff_const)
    fun z => by positivity

lemma hasCompactSupport_cutS : HasCompactSupport cutS := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2) fun z hz => ?_
  have hz2 : 2 < ‖z‖ := by simpa using hz
  have h4 : 4 < ‖z‖ ^ 2 := by nlinarith
  refine Real.smoothTransition.zero_of_nonpos ?_
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  linarith

lemma cutS_add_inv {z : ℂ} (hz : z ≠ 0) : cutS z + cutS z⁻¹ = 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have e : 1 / 2 - (‖z⁻¹‖ ^ 2 - 1) / (‖z⁻¹‖ ^ 2 + 1) =
      1 - (1 / 2 - (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)) := by
    rw [norm_inv]
    field_simp
    ring
  rw [cutS, cutS, e, smoothTransition_add_one_sub]

lemma dbar_congr {F G : ℂ → E} {z : ℂ} (h : F =ᶠ[𝓝 z] G) : dbar J₀ F z = dbar J₀ G z := by
  simp only [dbar, h.fderiv_eq]

lemma dbar_add {F G : ℂ → E} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) :
    dbar J₀ (fun w => F w + G w) z = dbar J₀ F z + dbar J₀ G z := by
  have e : fderiv ℝ (fun w => F w + G w) z = fderiv ℝ F z + fderiv ℝ G z :=
    (hF.hasFDerivAt.fun_add hG.hasFDerivAt).fderiv
  simp only [dbar, e, add_apply, map_add]
  module

lemma continuous_dbar {F : ℂ → E} (hF : ContDiff ℝ ∞ F) : Continuous (dbar J₀ F) := by
  have h := hF.continuous_fderiv (by simp)
  exact continuous_const.smul ((h.clm_apply continuous_const).add
    (J₀.continuous.comp (h.clm_apply continuous_const)))

lemma contDiff_cut_smul {g : ℂ → E} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun z => cutS z • g z := contDiff_cutS.smul hg

lemma contDiff_one_cut_smul {g : ℂ → E} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ 1 fun z => cutS z • g z := (contDiff_cut_smul hg).of_le (by simp)

lemma hasCompactSupport_cut_smul (g : ℂ → E) : HasCompactSupport fun z => cutS z • g z :=
  hasCompactSupport_cutS.smul_right

/-- The glued solution in one chart: `∂̄ (T(χg) + T(χh)(1/·)) = g`, when `g` and `h` are the
coefficients of one anti-linear form in the charts `z` and `w = 1/z`. -/
theorem dbar_glue (hJ : ∀ v, J₀ (J₀ v) = -v) {g h : ℂ → E} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h)
    (hgh : ∀ z ≠ 0, g z = cmulL J₀ (-((starRingEnd ℂ) z ^ 2)⁻¹) (h z⁻¹)) (z : ℂ) :
    dbar J₀ (fun z => cauchyT J₀ (fun w => cutS w • g w) z +
      cauchyTInv J₀ (fun w => cutS w • h w) z) z = g z := by
  have h1 := contDiff_cauchyT (J₀ := J₀) (contDiff_cut_smul hg) (hasCompactSupport_cut_smul g)
  have h2 := contDiff_cauchyTInv (J₀ := J₀) (contDiff_cut_smul hh) (hasCompactSupport_cut_smul h)
  have h3 := contDiff_cauchyT (J₀ := J₀) (contDiff_cut_smul hh) (hasCompactSupport_cut_smul h)
  refine congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (continuous_dbar (h1.add h2)) hg.continuous fun z hz => ?_) z
  have hz : z ≠ 0 := hz
  have d1 := (h1.differentiable (by simp)) z
  have d2 := (h2.differentiable (by simp)) z
  rw [dbar_add d1 d2, dbar_cauchyT hJ (contDiff_one_cut_smul hg)
    (hasCompactSupport_cut_smul g) z]
  have ev : cauchyTInv J₀ (fun w => cutS w • h w) =ᶠ[𝓝 z]
      fun w => cauchyT J₀ (fun w => cutS w • h w) w⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact cauchyTInv_of_ne hw
  rw [dbar_congr ev, dbar_comp_inv hJ hz ((h3.differentiable (by simp)) _),
    dbar_cauchyT hJ (contDiff_one_cut_smul hh) (hasCompactSupport_cut_smul h),
    map_smul, map_neg, map_inv₀, map_pow, ← hgh z hz, ← add_smul, cutS_add_inv hz, one_smul]

lemma cmulL_one (v : E) : cmulL J₀ 1 v = v := by simp [cmulL_apply]

/-- **`∂̄ ξ = η` on the Riemann sphere, in its two charts.**  Let `g, h : ℂ → E` be smooth, the
coefficients of an anti-linear form in the charts `z` and `w = 1/z`:
`h(w) = -(w̄²)⁻¹ g(1/w)` for `w ≠ 0`.  Then there are smooth `F, F' : ℂ → E` with `∂̄F = g`,
`∂̄F' = h` and `F'(w) = F(1/w)`: a smooth section of the trivial bundle with `∂̄ξ = η`. -/
theorem exists_dbar_sphere (hJ : ∀ v, J₀ (J₀ v) = -v) {g h : ℂ → E} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h)
    (hhg : ∀ w ≠ 0, h w = cmulL J₀ (-((starRingEnd ℂ) w ^ 2)⁻¹) (g w⁻¹)) :
    ∃ F F' : ℂ → E, ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ F' ∧ (∀ z, dbar J₀ F z = g z) ∧
      (∀ w, dbar J₀ F' w = h w) ∧ ∀ w ≠ 0, F' w = F w⁻¹ := by
  have hgh : ∀ z ≠ 0, g z = cmulL J₀ (-((starRingEnd ℂ) z ^ 2)⁻¹) (h z⁻¹) := by
    intro z hz
    have hc : (starRingEnd ℂ) z ≠ 0 := (map_ne_zero _).2 hz
    rw [hhg z⁻¹ (inv_ne_zero hz), inv_inv, ← cmulL_mul hJ, map_inv₀]
    rw [show -((starRingEnd ℂ) z ^ 2)⁻¹ * -(((starRingEnd ℂ) z)⁻¹ ^ 2)⁻¹ = 1 by
      field_simp, cmulL_one]
  refine ⟨fun z => cauchyT J₀ (fun w => cutS w • g w) z + cauchyTInv J₀ (fun w => cutS w • h w) z,
    fun z => cauchyT J₀ (fun w => cutS w • h w) z + cauchyTInv J₀ (fun w => cutS w • g w) z,
    (contDiff_cauchyT (contDiff_cut_smul hg) (hasCompactSupport_cut_smul g)).add
      (contDiff_cauchyTInv (contDiff_cut_smul hh) (hasCompactSupport_cut_smul h)),
    (contDiff_cauchyT (contDiff_cut_smul hh) (hasCompactSupport_cut_smul h)).add
      (contDiff_cauchyTInv (contDiff_cut_smul hg) (hasCompactSupport_cut_smul g)),
    dbar_glue hJ hg hh hgh, dbar_glue hJ hh hg hhg, fun w hw => ?_⟩
  simp only [cauchyTInv_of_ne hw, cauchyTInv_of_ne (inv_ne_zero hw), inv_inv]
  exact add_comm _ _

end GWMemoir
