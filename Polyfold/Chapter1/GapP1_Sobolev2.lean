import Polyfold.Chapter1.GapP1_Sobolev1

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 2: Fourier series on boxes

For the compact embeddings and the density in Example 1.1.3 we use Fourier series on a box
`(a, a+T] × (0,1]` of the cylinder, viewed as the torus `ℝ/Tℤ × ℝ/ℤ`.

* `bc a T F j k = T⁻¹ ∫_box e^{-iθ} F`, `θ = 2π (j s / T + k t)`: the Fourier coefficients.
* `hasSum_bc`: Parseval's identity `∑ |bc|² = T⁻¹ ∫_box |F|²`, from the one-variable identity
  `hasSum_sq_fourierCoeffOn` in each variable and Fubini.
* `exists_cutoff`: smooth cut-off functions of `s`.
* `bc_ds`, `bc_dt`: for `f` supported in `[c,d] × S¹ ⊂ (a, a+T) × S¹`, the coefficients of the weak
  derivatives are `2πij/T · bc f` and `2πik · bc f`.
* `ae_eq_zero_of_forall_test`: a function in `L²` which integrates to `0` against every test
  function vanishes almost everywhere; hence weak derivatives are unique
  (`HasWeakDeriv.ae_eq`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-! ### Boxes -/

/-- The box `(a, a+T] × (0,1]` of the cylinder. -/
def box (a T : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc a (a + T))).prod (volume.restrict (Ioc (0 : ℝ) 1))

lemma box_eq (a T : ℝ) : box a T = cyl.restrict (Ioc a (a + T) ×ˢ (univ : Set ℝ)) := by
  rw [box, cyl, ← Measure.prod_restrict, Measure.restrict_univ]

instance (a T : ℝ) : IsFiniteMeasure (volume.restrict (Ioc a (a + T))) :=
  isFiniteMeasure_restrict.2 (by simp)

instance (a T : ℝ) : IsFiniteMeasure (box a T) := by unfold box; infer_instance

/-- The phase `θ = 2π (j s / T + k t)`. -/
def phase (T : ℝ) (j k : ℤ) (x : ℝ × ℝ) : ℝ := 2 * Real.pi * (j * x.1 / T + k * x.2)

/-- `e^{-iθ}`. -/
def ecoef (T : ℝ) (j k : ℤ) (x : ℝ × ℝ) : ℂ := Complex.exp (((-phase T j k x : ℝ) : ℂ) * I)

lemma norm_ecoef (T : ℝ) (j k : ℤ) (x : ℝ × ℝ) : ‖ecoef T j k x‖ = 1 := by
  rw [ecoef, Complex.norm_exp_ofReal_mul_I]

lemma continuous_phase (T : ℝ) (j k : ℤ) : Continuous (phase T j k) := by
  unfold phase; fun_prop

lemma continuous_ecoef (T : ℝ) (j k : ℤ) : Continuous (ecoef T j k) := by
  unfold ecoef
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_phase T j k).neg).mul continuous_const)

lemma ecoef_eq_exp (T : ℝ) (j k : ℤ) (x : ℝ × ℝ) :
    ecoef T j k x = Complex.exp (2 * Real.pi * I * ((-j : ℤ) : ℂ) * x.1 / T) *
      Complex.exp (2 * Real.pi * I * ((-k : ℤ) : ℂ) * x.2) := by
  rw [ecoef, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Fourier coefficients on the box `(a, a+T] × (0,1]`. -/
def bc (a T : ℝ) (F : ℝ × ℝ → ℂ) (j k : ℤ) : ℂ :=
  (T⁻¹ : ℂ) * ∫ x, ecoef T j k x * F x ∂box a T

/-- The `t`-Fourier coefficient of `F(s, ·)`. -/
def tc (F : ℝ × ℝ → ℂ) (k : ℤ) (s : ℝ) : ℂ := fourierCoeffOn zero_lt_one (fun t => F (s, t)) k

lemma tc_eq (F : ℝ × ℝ → ℂ) (k : ℤ) (s : ℝ) :
    tc F k s = ∫ t, Complex.exp (2 * Real.pi * I * ((-k : ℤ) : ℂ) * t) * F (s, t)
      ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [tc, fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le zero_le_one]
  simp only [fourier_coe_apply, sub_zero, div_one, one_smul, smul_eq_mul, Complex.ofReal_one]

lemma bc_eq_fourierCoeffOn {a T : ℝ} (hT : 0 < T) {F : ℝ × ℝ → ℂ}
    (hF : Integrable F (box a T)) (j k : ℤ) :
    bc a T F j k = fourierCoeffOn (lt_add_of_pos_right a hT) (tc F k) j := by
  rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le (lt_add_of_pos_right a hT).le,
    bc, box, integral_prod]
  · simp only [fourier_coe_apply, add_sub_cancel_left, one_div, Complex.real_smul,
      Complex.ofReal_inv, smul_eq_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only
    rw [tc_eq, ← integral_const_mul]
    congr 1; funext t
    rw [ecoef_eq_exp]; ring
  · have : Integrable (fun x => ecoef T j k x * F x) (box a T) := by
      refine hF.bdd_mul (c := 1) (continuous_ecoef T j k).aestronglyMeasurable
        (ae_of_all _ fun x => (norm_ecoef T j k x).le)
    exact this

/-- Combining iterated sums of nonnegative terms. -/
lemma hasSum_prod_of_nonneg {f : ℤ × ℤ → ℝ} (hf : 0 ≤ f) {g : ℤ → ℝ} {S : ℝ}
    (h1 : ∀ k, HasSum (fun j => f (j, k)) (g k)) (h2 : HasSum g S) : HasSum f S := by
  set f' : ℤ × ℤ → ℝ := fun p => f (p.2, p.1)
  have hf' : 0 ≤ f' := fun p => hf (p.2, p.1)
  have hs : Summable f' := (summable_prod_of_nonneg hf').2
    ⟨fun k => (h1 k).summable, by
      convert h2.summable using 1; funext k; exact (h1 k).tsum_eq⟩
  have hS : HasSum f' S := by
    have := hs.hasSum
    convert this using 1
    rw [hs.tsum_prod]
    exact (h2.tsum_eq.symm.trans (tsum_congr fun k => ((h1 k).tsum_eq).symm))
  have := (Equiv.prodComm ℤ ℤ).hasSum_iff.2 hS
  convert this using 1
  funext p; simp [f']

/-- **Parseval's identity on a box.** -/
theorem hasSum_bc {a T : ℝ} (hT : 0 < T) {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (box a T)) :
    HasSum (fun p : ℤ × ℤ => ‖bc a T F p.1 p.2‖ ^ 2) (T⁻¹ * ∫ x, ‖F x‖ ^ 2 ∂box a T) := by
  set μW : Measure ℝ := volume.restrict (Ioc a (a + T)) with hμW
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hF2 : Integrable (fun x => ‖F x‖ ^ 2) (box a T) :=
    (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  have hF1 : Integrable F (box a T) := hF.integrable one_le_two
  -- slices
  have hslice : ∀ᵐ s ∂μW, MemLp (fun t => F (s, t)) 2 ν := by
    have h1 := hF.1.prodMk_left
    have h2 := hF2.prod_right_ae
    filter_upwards [h1, h2] with s hs1 hs2
    exact (memLp_two_iff_integrable_sq_norm hs1).2 hs2
  set G : ℝ → ℝ := fun s => ∫ t, ‖F (s, t)‖ ^ 2 ∂ν with hG
  have hGi : Integrable G μW := hF2.integral_prod_left
  -- Parseval in `t`
  have hPt : ∀ᵐ s ∂μW, HasSum (fun k => ‖tc F k s‖ ^ 2) (G s) := by
    filter_upwards [hslice] with s hs
    have := hasSum_sq_fourierCoeffOn zero_lt_one hs
    simp only [sub_zero, inv_one, one_smul,
      intervalIntegral.integral_of_le zero_le_one] at this
    exact this
  -- measurability of `tc`
  have htc_meas : ∀ k, AEStronglyMeasurable (tc F k) μW := by
    intro k
    have hm : AEStronglyMeasurable
        (fun x : ℝ × ℝ => Complex.exp (2 * Real.pi * I * ((-k : ℤ) : ℂ) * x.2) * F x)
        (μW.prod ν) :=
      (Continuous.cexp (by fun_prop)).aestronglyMeasurable.mul hF.1
    have := hm.integral_prod_right'
    refine this.congr (ae_of_all _ fun s => ?_)
    simp only
    rw [tc_eq]
  have htc_L2 : ∀ k, MemLp (tc F k) 2 μW := by
    intro k
    refine (memLp_two_iff_integrable_sq_norm (htc_meas k)).2 ?_
    refine hGi.mono' ((htc_meas k).norm.pow 2) ?_
    filter_upwards [hPt] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_hasSum hs k (fun _ _ => sq_nonneg _)
  -- Parseval in `s`
  have hPs : ∀ k, HasSum (fun j => ‖bc a T F j k‖ ^ 2) (T⁻¹ * ∫ s, ‖tc F k s‖ ^ 2 ∂μW) := by
    intro k
    have := hasSum_sq_fourierCoeffOn hab (htc_L2 k)
    simp only [add_sub_cancel_left, smul_eq_mul,
      intervalIntegral.integral_of_le hab.le] at this
    convert this using 2 with j
    rw [bc_eq_fourierCoeffOn hT hF1]
  -- sum over `k`
  have hk : HasSum (fun k => ∫ s, ‖tc F k s‖ ^ 2 ∂μW) (∫ s, G s ∂μW) := by
    refine hasSum_integral_of_dominated_convergence (fun k s => ‖tc F k s‖ ^ 2)
      (fun k => (htc_meas k).norm.pow 2) (fun k => ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]) ?_ ?_ hPt
    · filter_upwards [hPt] with s hs using hs.summable
    · refine hGi.congr ?_
      filter_upwards [hPt] with s hs using hs.tsum_eq.symm
  have hGF : ∫ s, G s ∂μW = ∫ x, ‖F x‖ ^ 2 ∂box a T := by
    rw [box, integral_prod _ hF2]
  rw [← hGF]
  refine hasSum_prod_of_nonneg (fun _ => sq_nonneg _) (fun k => hPs k) ?_
  exact hk.mul_left _

/-! ### Cut-off functions -/

/-- A smooth cut-off: `χ = 1` near `[c,d]`, `χ = 0` outside `(a,b)`, `0 ≤ χ ≤ 1`. -/
lemma exists_cutoff {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ s, s ≤ a ∨ b ≤ s → χ s = 0) ∧
      (∀ s ∈ Icc c d, χ s = 1 ∧ deriv χ s = 0) ∧ (∀ s, 0 ≤ χ s ∧ χ s ≤ 1) := by
  set m := (c + d) / 2
  set r := (d - c) / 2
  set ε := min (c - a) (b - d) / 2
  have hε : 0 < ε := by
    have : 0 < min (c - a) (b - d) := lt_min (by linarith) (by linarith)
    positivity
  have hr : 0 ≤ r := by simp only [r]; linarith
  let f : ContDiffBump m := ⟨r + ε / 2, r + ε, by linarith, by linarith⟩
  refine ⟨f, f.contDiff, ?_, ?_, fun s => ⟨f.nonneg, f.le_one⟩⟩
  · intro s hs
    apply f.zero_of_le_dist
    show r + ε ≤ dist s m
    rw [Real.dist_eq]
    have h1 : ε ≤ (c - a) / 2 := by
      simp only [ε]; linarith [min_le_left (c - a) (b - d)]
    have h2 : ε ≤ (b - d) / 2 := by
      simp only [ε]; linarith [min_le_right (c - a) (b - d)]
    rcases hs with hs | hs
    · rw [abs_of_neg (by simp only [m]; linarith)]; simp only [m, r]; linarith
    · rw [abs_of_pos (by simp only [m]; linarith)]; simp only [m, r]; linarith
  · intro s hs
    have hball : s ∈ Metric.ball m (r + ε / 2) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      obtain ⟨h1, h2⟩ := hs
      constructor <;> simp only [m, r] <;> linarith
    have hev := f.eventuallyEq_one_of_mem_ball hball
    refine ⟨hev.eq_of_nhds, ?_⟩
    rw [hev.deriv_eq]; simp

lemma cutoff_bddSupp {χ : ℝ → ℝ} {a b : ℝ} (h : ∀ s, s ≤ a ∨ b ≤ s → χ s = 0) :
    ∃ R, ∀ s, R < |s| → χ s = 0 := by
  refine ⟨max |a| |b|, fun s hs => h s ?_⟩
  rcases lt_abs.1 ((le_max_left _ _).trans_lt hs), lt_abs.1 ((le_max_right _ _).trans_lt hs)
    with ⟨h1 | h1, h2 | h2⟩ <;>
  first
  | (right; linarith [le_abs_self b, abs_nonneg a, abs_nonneg b, neg_abs_le a])
  | (left; linarith [le_abs_self b, abs_nonneg a, abs_nonneg b, neg_abs_le a])

/-! ### The trigonometric test functions -/

/-- `χ(s) cos θ`. -/
def tcos (T : ℝ) (j k : ℤ) (χ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := χ x.1 * Real.cos (phase T j k x)

/-- `χ(s) sin θ`. -/
def tsin (T : ℝ) (j k : ℤ) (χ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := χ x.1 * Real.sin (phase T j k x)

lemma contDiff_phase (T : ℝ) (j k : ℤ) : ContDiff ℝ ∞ (phase T j k) := by
  unfold phase; fun_prop

lemma phase_periodic (T : ℝ) (j k : ℤ) (s t : ℝ) :
    phase T j k (s, t + 1) = phase T j k (s, t) + k * (2 * Real.pi) := by
  simp only [phase]; ring

lemma isTest_tcos (T : ℝ) (j k : ℤ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hR : ∃ R, ∀ s, R < |s| → χ s = 0) : IsTest (tcos T j k χ) where
  smooth := (hχ.comp contDiff_fst).mul (Real.contDiff_cos.comp (contDiff_phase T j k))
  periodic s t := by
    simp only [tcos, phase_periodic]
    rw [Real.cos_add_int_mul_two_pi]
  bddSupp := by
    obtain ⟨R, hR⟩ := hR
    exact ⟨R, fun s t hs => by simp [tcos, hR s hs]⟩

lemma isTest_tsin (T : ℝ) (j k : ℤ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hR : ∃ R, ∀ s, R < |s| → χ s = 0) : IsTest (tsin T j k χ) where
  smooth := (hχ.comp contDiff_fst).mul (Real.contDiff_sin.comp (contDiff_phase T j k))
  periodic s t := by
    simp only [tsin, phase_periodic]
    rw [Real.sin_add_int_mul_two_pi]
  bddSupp := by
    obtain ⟨R, hR⟩ := hR
    exact ⟨R, fun s t hs => by simp [tsin, hR s hs]⟩

lemma Ds_cos_phase (T : ℝ) (j k : ℤ) :
    Ds (fun x => Real.cos (phase T j k x)) =
      fun x => -Real.sin (phase T j k x) * (2 * Real.pi * j / T) := by
  funext x
  obtain ⟨s, t⟩ := x
  have hd : Differentiable ℝ (fun x => Real.cos (phase T j k x)) :=
    (Real.contDiff_cos.comp (contDiff_phase T j k)).differentiable (by simp)
  refine (hasDerivAt_s hd s t).unique ?_
  have h1 : HasDerivAt (fun s' => phase T j k (s', t)) (2 * Real.pi * j / T) s := by
    have h0 : HasDerivAt (fun s' : ℝ => 2 * Real.pi * ((j : ℝ) * s' / T + k * t))
        (2 * Real.pi * ((j : ℝ) * 1 / T)) s :=
      (((hasDerivAt_id s).const_mul (j : ℝ)).div_const T |>.add_const _).const_mul _
    exact h0.congr_deriv (by ring)
  exact h1.cos

lemma Ds_sin_phase (T : ℝ) (j k : ℤ) :
    Ds (fun x => Real.sin (phase T j k x)) =
      fun x => Real.cos (phase T j k x) * (2 * Real.pi * j / T) := by
  funext x
  obtain ⟨s, t⟩ := x
  have hd : Differentiable ℝ (fun x => Real.sin (phase T j k x)) :=
    (Real.contDiff_sin.comp (contDiff_phase T j k)).differentiable (by simp)
  refine (hasDerivAt_s hd s t).unique ?_
  have h1 : HasDerivAt (fun s' => phase T j k (s', t)) (2 * Real.pi * j / T) s := by
    have h0 : HasDerivAt (fun s' : ℝ => 2 * Real.pi * ((j : ℝ) * s' / T + k * t))
        (2 * Real.pi * ((j : ℝ) * 1 / T)) s :=
      (((hasDerivAt_id s).const_mul (j : ℝ)).div_const T |>.add_const _).const_mul _
    exact h0.congr_deriv (by ring)
  exact h1.sin

lemma Dt_cos_phase (T : ℝ) (j k : ℤ) :
    Dt (fun x => Real.cos (phase T j k x)) =
      fun x => -Real.sin (phase T j k x) * (2 * Real.pi * k) := by
  funext x
  obtain ⟨s, t⟩ := x
  have hd : Differentiable ℝ (fun x => Real.cos (phase T j k x)) :=
    (Real.contDiff_cos.comp (contDiff_phase T j k)).differentiable (by simp)
  refine (hasDerivAt_t hd s t).unique ?_
  have h1 : HasDerivAt (fun t' => phase T j k (s, t')) (2 * Real.pi * k) t := by
    have h0 : HasDerivAt (fun t' : ℝ => 2 * Real.pi * ((j : ℝ) * s / T + k * t'))
        (2 * Real.pi * ((k : ℝ) * 1)) t :=
      (((hasDerivAt_id t).const_mul (k : ℝ)).const_add _).const_mul _
    exact h0.congr_deriv (by ring)
  exact h1.cos

lemma Dt_sin_phase (T : ℝ) (j k : ℤ) :
    Dt (fun x => Real.sin (phase T j k x)) =
      fun x => Real.cos (phase T j k x) * (2 * Real.pi * k) := by
  funext x
  obtain ⟨s, t⟩ := x
  have hd : Differentiable ℝ (fun x => Real.sin (phase T j k x)) :=
    (Real.contDiff_sin.comp (contDiff_phase T j k)).differentiable (by simp)
  refine (hasDerivAt_t hd s t).unique ?_
  have h1 : HasDerivAt (fun t' => phase T j k (s, t')) (2 * Real.pi * k) t := by
    have h0 : HasDerivAt (fun t' : ℝ => 2 * Real.pi * ((j : ℝ) * s / T + k * t'))
        (2 * Real.pi * ((k : ℝ) * 1)) t :=
      (((hasDerivAt_id t).const_mul (k : ℝ)).const_add _).const_mul _
    exact h0.congr_deriv (by ring)
  exact h1.sin

/-! ### Coefficients as real integrals -/

lemma ecoef_re (T : ℝ) (j k : ℤ) (x : ℝ × ℝ) :
    (ecoef T j k x).re = Real.cos (phase T j k x) := by
  rw [ecoef, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

lemma ecoef_im (T : ℝ) (j k : ℤ) (x : ℝ × ℝ) :
    (ecoef T j k x).im = -Real.sin (phase T j k x) := by
  rw [ecoef, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

/-- For a real function supported where `χ = 1`, the coefficient integral splits into the
pairings with the test functions `χ cos θ` and `χ sin θ`. -/
lemma integral_ecoef_eq {T : ℝ} {j k : ℤ} {χ : ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 cyl) (hχ : ContDiff ℝ ∞ χ) (hR : ∃ R, ∀ s, R < |s| → χ s = 0)
    (hsupp : ∀ᵐ x ∂cyl, f x ≠ 0 → χ x.1 = 1) :
    ∫ x, ecoef T j k x * (f x : ℂ) ∂cyl =
      ((∫ x, f x * tcos T j k χ x ∂cyl : ℝ) : ℂ) - ((∫ x, f x * tsin T j k χ x ∂cyl : ℝ) : ℂ) * I := by
  have ic := (isTest_tcos T j k hχ hR).integrable_mul hf
  have is := (isTest_tsin T j k hχ hR).integrable_mul hf
  have e : (fun x => ecoef T j k x * (f x : ℂ)) =ᵐ[cyl]
      fun x => ((f x * tcos T j k χ x : ℝ) : ℂ) - ((f x * tsin T j k χ x : ℝ) : ℂ) * I := by
    filter_upwards [hsupp] with x hx
    by_cases h0 : f x = 0
    · simp [h0]
    · have h1 := hx h0
      apply Complex.ext
      · rw [Complex.re_mul_ofReal, ecoef_re]; simp [tcos, h1, Complex.cos_ofReal_re]; ring
      · rw [Complex.im_mul_ofReal, ecoef_im]; simp [tsin, h1, Complex.sin_ofReal_re]; ring
  have ic' : Integrable (fun x => ((f x * tcos T j k χ x : ℝ) : ℂ)) cyl := ic.ofReal
  have is' : Integrable (fun x => ((f x * tsin T j k χ x : ℝ) : ℂ) * I) cyl :=
    is.ofReal.mul_const I
  rw [integral_congr_ae e, integral_sub ic' is', integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]

/-- The box coefficient of a function supported in the box is the coefficient over the cylinder. -/
lemma bc_eq_cyl {a T : ℝ} {F : ℝ × ℝ → ℂ}
    (hsupp : ∀ᵐ x ∂cyl, F x ≠ 0 → x.1 ∈ Ioc a (a + T)) (j k : ℤ) :
    bc a T F j k = (T⁻¹ : ℂ) * ∫ x, ecoef T j k x * F x ∂cyl := by
  rw [bc, box_eq, setIntegral_eq_integral_of_ae_compl_eq_zero]
  filter_upwards [hsupp] with x hx hxS
  by_contra h
  have h' : F x ≠ 0 := by
    intro h0; apply h; simp [h0]
  exact hxS ⟨hx h', mem_univ _⟩

/-! ### Coefficients of weak derivatives -/

/-- `∂_s` multiplies the box coefficients by `2πij/T`. -/
theorem bc_ds {a T c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < a + T)
    {f g : ℝ × ℝ → ℝ} (hf : MemLp f 2 cyl) (hg : MemLp g 2 cyl) (hfg : HasWeakDeriv 1 0 f g)
    (hsf : ∀ᵐ x ∂cyl, f x ≠ 0 → x.1 ∈ Icc c d) (hsg : ∀ᵐ x ∂cyl, g x ≠ 0 → x.1 ∈ Icc c d)
    (j k : ℤ) :
    bc a T (fun x => (g x : ℂ)) j k = (2 * Real.pi * I * j / T) * bc a T (fun x => (f x : ℂ)) j k := by
  obtain ⟨χ, hχ, hχ0, hχ1, -⟩ := exists_cutoff hac hcd hdb
  have hR := cutoff_bddSupp hχ0
  have hin : ∀ s ∈ Icc c d, s ∈ Ioc a (a + T) := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have sF : ∀ᵐ x ∂cyl, (f x : ℂ) ≠ 0 → x.1 ∈ Ioc a (a + T) := by
    filter_upwards [hsf] with x hx h0 using hin _ (hx (by exact_mod_cast h0))
  have sG : ∀ᵐ x ∂cyl, (g x : ℂ) ≠ 0 → x.1 ∈ Ioc a (a + T) := by
    filter_upwards [hsg] with x hx h0 using hin _ (hx (by exact_mod_cast h0))
  have cf : ∀ᵐ x ∂cyl, f x ≠ 0 → χ x.1 = 1 := by
    filter_upwards [hsf] with x hx h0 using (hχ1 _ (hx h0)).1
  have cg : ∀ᵐ x ∂cyl, g x ≠ 0 → χ x.1 = 1 := by
    filter_upwards [hsg] with x hx h0 using (hχ1 _ (hx h0)).1
  rw [bc_eq_cyl sF, bc_eq_cyl sG, integral_ecoef_eq hf hχ hR cf, integral_ecoef_eq hg hχ hR cg]
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  set w0 : ℝ := 2 * Real.pi * j / T
  -- the two test functions
  have tc' := isTest_tcos T j k hχ hR
  have ts' := isTest_tsin T j k hχ hR
  have e1 := hfg _ tc'
  have e2 := hfg _ ts'
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at e1 e2
  have dc : Ds (tcos T j k χ) = fun x => deriv χ x.1 * Real.cos (phase T j k x)
      + χ x.1 * (-Real.sin (phase T j k x) * w0) := by
    have := Ds_mul_s (φ := fun x => Real.cos (phase T j k x))
      ((Real.contDiff_cos.comp (contDiff_phase T j k)).differentiable (by simp)) hχd
    rw [Ds_cos_phase] at this; exact this
  have ds : Ds (tsin T j k χ) = fun x => deriv χ x.1 * Real.sin (phase T j k x)
      + χ x.1 * (Real.cos (phase T j k x) * w0) := by
    have := Ds_mul_s (φ := fun x => Real.sin (phase T j k x))
      ((Real.contDiff_sin.comp (contDiff_phase T j k)).differentiable (by simp)) hχd
    rw [Ds_sin_phase] at this; exact this
  have a1 : ∫ x, f x * Ds (tcos T j k χ) x ∂cyl = -w0 * ∫ x, f x * tsin T j k χ x ∂cyl := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hsf] with x hx
    by_cases h0 : f x = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hχ1 _ (hx h0)
      rw [dc]; simp only [tsin, h1, h2]; ring
  have a2 : ∫ x, f x * Ds (tsin T j k χ) x ∂cyl = w0 * ∫ x, f x * tcos T j k χ x ∂cyl := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hsf] with x hx
    by_cases h0 : f x = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hχ1 _ (hx h0)
      rw [ds]; simp only [tcos, h1, h2]; ring
  rw [a1] at e1
  rw [a2] at e2
  norm_num at e1 e2
  set A := ∫ x, f x * tcos T j k χ x ∂cyl
  set B := ∫ x, f x * tsin T j k χ x ∂cyl
  set Ag := ∫ x, g x * tcos T j k χ x ∂cyl
  set Bg := ∫ x, g x * tsin T j k χ x ∂cyl
  have hAg : Ag = w0 * B := by linarith
  have hBg : Bg = -w0 * A := by linarith
  rw [hAg, hBg]
  simp only [w0]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `∂_t` multiplies the box coefficients by `2πik`. -/
theorem bc_dt {a T c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < a + T)
    {f g : ℝ × ℝ → ℝ} (hf : MemLp f 2 cyl) (hg : MemLp g 2 cyl) (hfg : HasWeakDeriv 0 1 f g)
    (hsf : ∀ᵐ x ∂cyl, f x ≠ 0 → x.1 ∈ Icc c d) (hsg : ∀ᵐ x ∂cyl, g x ≠ 0 → x.1 ∈ Icc c d)
    (j k : ℤ) :
    bc a T (fun x => (g x : ℂ)) j k = (2 * Real.pi * I * k) * bc a T (fun x => (f x : ℂ)) j k := by
  obtain ⟨χ, hχ, hχ0, hχ1, -⟩ := exists_cutoff hac hcd hdb
  have hR := cutoff_bddSupp hχ0
  have hin : ∀ s ∈ Icc c d, s ∈ Ioc a (a + T) := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have sF : ∀ᵐ x ∂cyl, (f x : ℂ) ≠ 0 → x.1 ∈ Ioc a (a + T) := by
    filter_upwards [hsf] with x hx h0 using hin _ (hx (by exact_mod_cast h0))
  have sG : ∀ᵐ x ∂cyl, (g x : ℂ) ≠ 0 → x.1 ∈ Ioc a (a + T) := by
    filter_upwards [hsg] with x hx h0 using hin _ (hx (by exact_mod_cast h0))
  have cf : ∀ᵐ x ∂cyl, f x ≠ 0 → χ x.1 = 1 := by
    filter_upwards [hsf] with x hx h0 using (hχ1 _ (hx h0)).1
  have cg : ∀ᵐ x ∂cyl, g x ≠ 0 → χ x.1 = 1 := by
    filter_upwards [hsg] with x hx h0 using (hχ1 _ (hx h0)).1
  rw [bc_eq_cyl sF, bc_eq_cyl sG, integral_ecoef_eq hf hχ hR cf, integral_ecoef_eq hg hχ hR cg]
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  set w0 : ℝ := 2 * Real.pi * k
  have tc' := isTest_tcos T j k hχ hR
  have ts' := isTest_tsin T j k hχ hR
  have e1 := hfg _ tc'
  have e2 := hfg _ ts'
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at e1 e2
  have dc : Dt (tcos T j k χ) = fun x => χ x.1 * (-Real.sin (phase T j k x) * w0) := by
    have := Dt_mul_s (φ := fun x => Real.cos (phase T j k x))
      ((Real.contDiff_cos.comp (contDiff_phase T j k)).differentiable (by simp)) hχd
    rw [Dt_cos_phase] at this; exact this
  have ds : Dt (tsin T j k χ) = fun x => χ x.1 * (Real.cos (phase T j k x) * w0) := by
    have := Dt_mul_s (φ := fun x => Real.sin (phase T j k x))
      ((Real.contDiff_sin.comp (contDiff_phase T j k)).differentiable (by simp)) hχd
    rw [Dt_sin_phase] at this; exact this
  have a1 : ∫ x, f x * Dt (tcos T j k χ) x ∂cyl = -w0 * ∫ x, f x * tsin T j k χ x ∂cyl := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [dc]; simp only [tsin]; ring
  have a2 : ∫ x, f x * Dt (tsin T j k χ) x ∂cyl = w0 * ∫ x, f x * tcos T j k χ x ∂cyl := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [ds]; simp only [tcos]; ring
  rw [a1] at e1
  rw [a2] at e2
  norm_num at e1 e2
  set A := ∫ x, f x * tcos T j k χ x ∂cyl
  set B := ∫ x, f x * tsin T j k χ x ∂cyl
  set Ag := ∫ x, g x * tcos T j k χ x ∂cyl
  set Bg := ∫ x, g x * tsin T j k χ x ∂cyl
  have hAg : Ag = w0 * B := by linarith
  have hBg : Bg = -w0 * A := by linarith
  rw [hAg, hBg]
  simp only [w0]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Uniqueness of weak derivatives -/

lemma memLp_cutoff_mul {χ : ℝ → ℝ} (hχ : Continuous χ) (hb : ∀ s, |χ s| ≤ 1)
    {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 cyl) : MemLp (fun x => χ x.1 * f x) 2 cyl :=
  hf.of_le ((hχ.comp continuous_fst).aestronglyMeasurable.mul hf.1)
    (ae_of_all _ fun x => by
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hb _))

/-- A function in `L²(ℝ × S¹)` orthogonal to every test function vanishes almost everywhere. -/
theorem ae_eq_zero_of_forall_test {h : ℝ × ℝ → ℝ} (hh : MemLp h 2 cyl)
    (H : ∀ φ, IsTest φ → ∫ x, h x * φ x ∂cyl = 0) : h =ᵐ[cyl] 0 := by
  have key : ∀ n : ℕ, ∀ᵐ x ∂cyl, x.1 ∈ Icc (-(n : ℝ)) n → h x = 0 := by
    intro n
    set a : ℝ := -(n : ℝ) - 1 with ha
    set T : ℝ := 2 * n + 3 with hTdef
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hT : 0 < T := by positivity
    obtain ⟨χ, hχ, hχ0, hχ1, hχb⟩ :=
      exists_cutoff (a := a) (b := a + T) (c := -(n : ℝ)) (d := n) (by linarith) (by linarith)
        (by linarith)
    have hR := cutoff_bddSupp hχ0
    have hχab : ∀ s, |χ s| ≤ 1 := fun s => abs_le.2 ⟨by linarith [(hχb s).1], (hχb s).2⟩
    set F : ℝ × ℝ → ℂ := fun x => ((χ x.1 * h x : ℝ) : ℂ) with hF
    have hχh := memLp_cutoff_mul hχ.continuous hχab hh
    have sF : ∀ᵐ x ∂cyl, F x ≠ 0 → x.1 ∈ Ioc a (a + T) := by
      refine ae_of_all _ fun x hx => ?_
      have h1 : χ x.1 ≠ 0 := by
        intro h0; apply hx; simp [F, h0]
      by_contra hc
      apply h1; apply hχ0
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hc
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr hc.le
    have hz : ∀ j k, bc a T F j k = 0 := by
      intro j k
      rw [bc_eq_cyl sF]
      have e : ∫ x, ecoef T j k x * F x ∂cyl =
          ((∫ x, h x * tcos T j k χ x ∂cyl : ℝ) : ℂ)
            - ((∫ x, h x * tsin T j k χ x ∂cyl : ℝ) : ℂ) * I := by
        have ic := (isTest_tcos T j k hχ hR).integrable_mul hh
        have is := (isTest_tsin T j k hχ hR).integrable_mul hh
        have e0 : (fun x => ecoef T j k x * F x) =
            fun x => ((h x * tcos T j k χ x : ℝ) : ℂ) - ((h x * tsin T j k χ x : ℝ) : ℂ) * I := by
          funext x
          apply Complex.ext
          · rw [Complex.re_mul_ofReal, ecoef_re]; simp [tcos, Complex.cos_ofReal_re]; ring
          · rw [Complex.im_mul_ofReal, ecoef_im]; simp [tsin, Complex.sin_ofReal_re]; ring
        have ic' : Integrable (fun x => ((h x * tcos T j k χ x : ℝ) : ℂ)) cyl := ic.ofReal
        have is' : Integrable (fun x => ((h x * tsin T j k χ x : ℝ) : ℂ) * I) cyl :=
          is.ofReal.mul_const I
        rw [e0, integral_sub ic' is', integral_mul_const,
          integral_complex_ofReal, integral_complex_ofReal]
      rw [e, H _ (isTest_tcos T j k hχ hR), H _ (isTest_tsin T j k hχ hR)]
      simp
    have hFL2 : MemLp F 2 (box a T) := by
      rw [box_eq]; exact hχh.ofReal.restrict _
    have hP := hasSum_bc hT hFL2
    have h0 : (fun p : ℤ × ℤ => ‖bc a T F p.1 p.2‖ ^ 2) = 0 := by
      funext p; simp [hz]
    rw [h0] at hP
    have hI : ∫ x, ‖F x‖ ^ 2 ∂box a T = 0 := by
      have := hasSum_zero.unique hP
      rcases mul_eq_zero.1 this.symm with h1 | h1
      · exact absurd h1 (inv_ne_zero hT.ne')
      · exact h1
    have hF2 : Integrable (fun x => ‖F x‖ ^ 2) (box a T) :=
      (memLp_two_iff_integrable_sq_norm hFL2.1).1 hFL2
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖F x‖) hF2).1 hI
    rw [box_eq, EventuallyEq, ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)] at hae
    filter_upwards [hae] with x hx hxn
    have hmem : x ∈ Ioc a (a + T) ×ˢ (univ : Set ℝ) :=
      ⟨⟨by linarith [hxn.1], by linarith [hxn.2]⟩, mem_univ _⟩
    have h1 := hx hmem
    simp only [Pi.zero_apply, F, (hχ1 _ hxn).1, one_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_eq_zero_iff, abs_eq_zero] at h1
    exact h1
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_nat_ge |x.1|
  exact hx n (abs_le.1 hn)

/-- **Weak derivatives are unique** (as elements of `L²`). -/
theorem HasWeakDeriv.ae_eq {a b : ℕ} {u g g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g)
    (h' : HasWeakDeriv a b u g') (hg : MemLp g 2 cyl) (hg' : MemLp g' 2 cyl) : g =ᵐ[cyl] g' := by
  have hz := ae_eq_zero_of_forall_test (hg.sub hg') fun φ hφ => by
    have e1 := h φ hφ
    have e2 := h' φ hφ
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub (hφ.integrable_mul hg) (hφ.integrable_mul hg')]
    have hne : ((-1 : ℝ) ^ (a + b)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have : ∫ x, g x * φ x ∂cyl = ∫ x, g' x * φ x ∂cyl := by
      apply mul_left_cancel₀ hne; rw [← e1, ← e2]
    rw [this, sub_self]
  filter_upwards [hz] with x hx
  simpa [sub_eq_zero] using hx

end Polyfold.GapP1Sobolev
