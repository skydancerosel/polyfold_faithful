import Polyfold.Chapter1.GapP1_Sobolev10

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 11: trigonometric polynomials

On the box `(a, a+T] × (0,1]`, the partial Fourier sums
`trig T c N = Re ∑_{|j|,|k| ≤ N} c_{jk} e^{2πi(js/T + kt)}` are smooth and `1`-periodic in `t`,
their classical derivatives multiply the coefficients by `2πij/T` and `2πik` (`pD_trig`),
the exponentials are orthonormal (`bc_eexp`), and for `f ∈ L²` the partial sums with the
Fourier coefficients of `f` converge to `f` in `L²` of the box (`tendsto_box_sq`).
-/

open MeasureTheory Set Filter Topology Finset
open Complex (I)
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-- `Re(c e^{iθ})`, `θ = 2π(js/T + kt)`. -/
def term (T : ℝ) (c : ℂ) (q : ℤ × ℤ) (x : ℝ × ℝ) : ℝ :=
  c.re * Real.cos (phase T q.1 q.2 x) - c.im * Real.sin (phase T q.1 q.2 x)

/-- `e^{iθ}`. -/
def eexp (T : ℝ) (q : ℤ × ℤ) (x : ℝ × ℝ) : ℂ := Complex.exp ((phase T q.1 q.2 x : ℂ) * I)

lemma term_eq (T : ℝ) (c : ℂ) (q : ℤ × ℤ) (x : ℝ × ℝ) : term T c q x = (c * eexp T q x).re := by
  simp only [term, eexp, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

lemma contDiff_term (T : ℝ) (c : ℂ) (q : ℤ × ℤ) : ContDiff ℝ ∞ (term T c q) :=
  (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_phase T _ _))).sub
    (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_phase T _ _)))

lemma term_periodic (T : ℝ) (c : ℂ) (q : ℤ × ℤ) (s t : ℝ) :
    term T c q (s, t + 1) = term T c q (s, t) := by
  simp only [term, phase_periodic, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma Ds_lin {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (α β : ℝ) :
    Ds (fun x => α * f x - β * g x) = fun x => α * Ds f x - β * Ds g x := by
  funext x
  have h : HasFDerivAt (fun x => α * f x - β * g x) (α • fderiv ℝ f x - β • fderiv ℝ g x) x :=
    ((hf x).hasFDerivAt.const_mul α).sub ((hg x).hasFDerivAt.const_mul β)
  simp only [Ds]; rw [h.fderiv]; simp

lemma Dt_lin {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (α β : ℝ) :
    Dt (fun x => α * f x - β * g x) = fun x => α * Dt f x - β * Dt g x := by
  funext x
  have h : HasFDerivAt (fun x => α * f x - β * g x) (α • fderiv ℝ f x - β • fderiv ℝ g x) x :=
    ((hf x).hasFDerivAt.const_mul α).sub ((hg x).hasFDerivAt.const_mul β)
  simp only [Dt]; rw [h.fderiv]; simp

lemma Ds_fsum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) :
    Ds (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, Ds (f i) x := by
  funext x; simp only [Ds]; rw [fderiv_fun_sum (fun i _ => hf i x)]; simp

lemma Dt_fsum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) :
    Dt (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, Dt (f i) x := by
  funext x; simp only [Dt]; rw [fderiv_fun_sum (fun i _ => hf i x)]; simp

/-- The `s`-multiplier `2πij/T`. -/
def mS (T : ℝ) (q : ℤ × ℤ) : ℂ := 2 * Real.pi * I * q.1 / T

/-- The `t`-multiplier `2πik`. -/
def mT (q : ℤ × ℤ) : ℂ := 2 * Real.pi * I * q.2

lemma Ds_term (T : ℝ) (c : ℂ) (q : ℤ × ℤ) : Ds (term T c q) = term T (mS T q * c) q := by
  have hc : Differentiable ℝ (fun x => Real.cos (phase T q.1 q.2 x)) :=
    (Real.contDiff_cos.comp (contDiff_phase T _ _)).differentiable (by simp)
  have hs : Differentiable ℝ (fun x => Real.sin (phase T q.1 q.2 x)) :=
    (Real.contDiff_sin.comp (contDiff_phase T _ _)).differentiable (by simp)
  have e : mS T q = ((2 * Real.pi * q.1 / T : ℝ) : ℂ) * I := by simp only [mS]; push_cast; ring
  change Ds (fun x => c.re * Real.cos (phase T q.1 q.2 x) - c.im * Real.sin (phase T q.1 q.2 x)) = _
  rw [Ds_lin hc hs, Ds_cos_phase, Ds_sin_phase]
  funext x
  simp only [term, e, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma Dt_term (T : ℝ) (c : ℂ) (q : ℤ × ℤ) : Dt (term T c q) = term T (mT q * c) q := by
  have hc : Differentiable ℝ (fun x => Real.cos (phase T q.1 q.2 x)) :=
    (Real.contDiff_cos.comp (contDiff_phase T _ _)).differentiable (by simp)
  have hs : Differentiable ℝ (fun x => Real.sin (phase T q.1 q.2 x)) :=
    (Real.contDiff_sin.comp (contDiff_phase T _ _)).differentiable (by simp)
  have e : mT q = ((2 * Real.pi * q.2 : ℝ) : ℂ) * I := by simp only [mT]; push_cast; ring
  change Dt (fun x => c.re * Real.cos (phase T q.1 q.2 x) - c.im * Real.sin (phase T q.1 q.2 x)) = _
  rw [Dt_lin hc hs, Dt_cos_phase, Dt_sin_phase]
  funext x
  simp only [term, e, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- The real partial Fourier sum `Re ∑_{q ∈ sqN N} c_q e^{iθ_q}`. -/
def trig (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) (x : ℝ × ℝ) : ℝ := ∑ q ∈ sqN N, term T (c q) q x

lemma trig_eq_re (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) (x : ℝ × ℝ) :
    trig T c N x = (∑ q ∈ sqN N, c q * eexp T q x).re := by
  simp only [trig, term_eq, Complex.re_sum]

lemma smPer_trig (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) : SmPer (trig T c N) :=
  ⟨ContDiff.sum fun q _ => contDiff_term T (c q) q, fun s t => by simp only [trig, term_periodic]⟩

lemma Ds_trig (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) :
    Ds (trig T c N) = trig T (fun q => mS T q * c q) N := by
  change Ds (fun x => ∑ q ∈ sqN N, term T (c q) q x) = _
  rw [Ds_fsum _ _ fun q => (contDiff_term T (c q) q).differentiable (by simp)]
  simp_rw [Ds_term]; rfl

lemma Dt_trig (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) :
    Dt (trig T c N) = trig T (fun q => mT q * c q) N := by
  change Dt (fun x => ∑ q ∈ sqN N, term T (c q) q x) = _
  rw [Dt_fsum _ _ fun q => (contDiff_term T (c q) q).differentiable (by simp)]
  simp_rw [Dt_term]; rfl

lemma iterate_Dt_trig (T : ℝ) (N : ℕ) : ∀ (b : ℕ) (c : ℤ × ℤ → ℂ),
    Dt^[b] (trig T c N) = trig T (fun q => mT q ^ b * c q) N
  | 0, c => by simp
  | b + 1, c => by
    rw [Function.iterate_succ_apply', iterate_Dt_trig T N b c, Dt_trig]
    congr 1; funext q; ring

lemma iterate_Ds_trig (T : ℝ) (N : ℕ) : ∀ (a : ℕ) (c : ℤ × ℤ → ℂ),
    Ds^[a] (trig T c N) = trig T (fun q => mS T q ^ a * c q) N
  | 0, c => by simp
  | a + 1, c => by
    rw [Function.iterate_succ_apply', iterate_Ds_trig T N a c, Ds_trig]
    congr 1; funext q; ring

lemma pD_trig (T : ℝ) (c : ℤ × ℤ → ℂ) (N a b : ℕ) :
    pD a b (trig T c N) = trig T (fun q => mS T q ^ a * mT q ^ b * c q) N := by
  rw [pD, iterate_Dt_trig, iterate_Ds_trig]; congr 1; funext q; ring

/-! ### Orthonormality on the box -/

lemma integral_exp_Ioc (a b T : ℝ) (hb : b = a + T) (hT : 0 < T) (j : ℤ) :
    ∫ s in Ioc a b, Complex.exp (((2 * Real.pi * j / T * s : ℝ) : ℂ) * I) =
      if j = 0 then (T : ℂ) else 0 := by
  subst hb
  split_ifs with hj
  · subst hj
    simp [Measure.real, Real.volume_Ioc, hT.le]
  · rw [← intervalIntegral.integral_of_le (by linarith)]
    set c : ℂ := ((2 * Real.pi * j / T : ℝ) : ℂ) * I with hc
    have e : ∀ s : ℝ, (((2 * Real.pi * j / T * s : ℝ) : ℂ) * I) = c * s := fun s => by
      simp only [hc]; push_cast; ring
    simp_rw [e]
    have hc0 : c ≠ 0 := by
      refine mul_ne_zero (Complex.ofReal_ne_zero.2 ?_) Complex.I_ne_zero
      have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      have := Real.pi_pos
      positivity
    rw [integral_exp_mul_complex hc0]
    have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
    have h1 : c * ((a + T : ℝ) : ℂ) = c * a + j * (2 * Real.pi * I) := by
      simp only [hc]; push_cast; rw [mul_add]; congr 1; field_simp
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]; simp

lemma continuous_eexp (T : ℝ) (q : ℤ × ℤ) : Continuous (eexp T q) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_phase T _ _)).mul
    continuous_const)

lemma norm_eexp (T : ℝ) (q : ℤ × ℤ) (x : ℝ × ℝ) : ‖eexp T q x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma bc_eexp {a T : ℝ} (hT : 0 < T) (p q : ℤ × ℤ) :
    bc a T (eexp T p) q.1 q.2 = if q = p then 1 else 0 := by
  have e : ∀ x : ℝ × ℝ, ecoef T q.1 q.2 x * eexp T p x =
      Complex.exp (((2 * Real.pi * (p.1 - q.1 : ℤ) / T * x.1 : ℝ) : ℂ) * I) *
      Complex.exp (((2 * Real.pi * (p.2 - q.2 : ℤ) / 1 * x.2 : ℝ) : ℂ) * I) := by
    intro x
    rw [ecoef, eexp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; simp only [phase]; push_cast; ring
  simp only [bc]
  simp_rw [e]
  rw [box, integral_prod_mul (fun s => Complex.exp (((2 * Real.pi * (p.1 - q.1 : ℤ) / T * s : ℝ) : ℂ) * I))
    (fun t => Complex.exp (((2 * Real.pi * (p.2 - q.2 : ℤ) / 1 * t : ℝ) : ℂ) * I)),
    integral_exp_Ioc a (a + T) T rfl hT, integral_exp_Ioc 0 1 1 (by ring) one_pos]
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
  by_cases h1 : p.1 - q.1 = 0 <;> by_cases h2 : p.2 - q.2 = 0
  · have : q = p := Prod.ext (by omega) (by omega)
    simp [h1, hT', this]
  · have : q ≠ p := fun h => h2 (by rw [h]; ring)
    simp [h2, this]
  · have : q ≠ p := fun h => h1 (by rw [h]; ring)
    simp [h1, this]
  · have : q ≠ p := fun h => h1 (by rw [h]; ring)
    simp [h1, this]

/-- The complex partial sum. -/
def Pc (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) (x : ℝ × ℝ) : ℂ := ∑ q ∈ sqN N, c q * eexp T q x

lemma continuous_Pc (T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) : Continuous (Pc T c N) :=
  continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_eexp T q)

lemma memLp_Pc (a T : ℝ) (c : ℤ × ℤ → ℂ) (N : ℕ) (p : ℝ≥0∞) : MemLp (Pc T c N) p (box a T) :=
  MemLp.of_bound (continuous_Pc T c N).aestronglyMeasurable (∑ q ∈ sqN N, ‖c q‖)
    (ae_of_all _ fun x => (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => by
      rw [norm_mul, norm_eexp, mul_one]))

lemma bc_Pc {a T : ℝ} (hT : 0 < T) (c : ℤ × ℤ → ℂ) (N : ℕ) (q : ℤ × ℤ) :
    bc a T (Pc T c N) q.1 q.2 = if q ∈ sqN N then c q else 0 := by
  have hi : ∀ p ∈ sqN N, Integrable (fun x => c p * (ecoef T q.1 q.2 x * eexp T p x)) (box a T) :=
    fun p _ => Integrable.of_bound
      ((continuous_const.mul ((continuous_ecoef T _ _).mul (continuous_eexp T p))).aestronglyMeasurable)
      ‖c p‖ (ae_of_all _ fun x => by rw [norm_mul, norm_mul, norm_ecoef, norm_eexp]; simp)
  have e : ∀ x, ecoef T q.1 q.2 x * Pc T c N x =
      ∑ p ∈ sqN N, c p * (ecoef T q.1 q.2 x * eexp T p x) := fun x => by
    rw [Pc, Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  simp only [bc]
  simp_rw [e]
  rw [integral_finsetSum _ hi, Finset.mul_sum]
  have e2 : ∀ p ∈ sqN N, (T⁻¹ : ℂ) * ∫ x, c p * (ecoef T q.1 q.2 x * eexp T p x) ∂box a T =
      c p * (if q = p then 1 else 0) := fun p _ => by
    rw [integral_const_mul, ← bc_eexp hT p q, bc]; ring
  rw [Finset.sum_congr rfl e2]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- The Fourier coefficients of a real function on the box. -/
def cf (a T : ℝ) (f : ℝ × ℝ → ℝ) (q : ℤ × ℤ) : ℂ := bc a T (fun x => (f x : ℂ)) q.1 q.2

lemma eventually_mem_sqN (q : ℤ × ℤ) : ∀ᶠ N in atTop, q ∈ sqN N := by
  filter_upwards [eventually_ge_atTop (q.1.natAbs + q.2.natAbs)] with N hN
  simp only [sqN, Finset.mem_product, Finset.mem_Icc]
  omega

/-- The partial Fourier sums of `f ∈ L²` converge to `f` in `L²` of the box. -/
theorem tendsto_box_sq {a T : ℝ} (hT : 0 < T) {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 cyl) :
    Tendsto (fun N : ℕ => ∫ x, (trig T (cf a T f) N x - f x) ^ 2 ∂box a T) atTop (𝓝 0) := by
  set F : ℝ × ℝ → ℂ := fun x => (f x : ℂ)
  have hF : MemLp F 2 (box a T) := memLp_box hf
  have hsum := hasSum_bc hT hF
  -- the error `D_N = F - P_N F`
  have hD : ∀ N : ℕ, MemLp (F - Pc T (cf a T f) N) 2 (box a T) := fun N =>
    hF.sub (memLp_Pc a T _ N 2)
  have hbcD : ∀ (N : ℕ) (q : ℤ × ℤ), ‖bc a T (F - Pc T (cf a T f) N) q.1 q.2‖ ^ 2 =
      if q ∈ sqN N then 0 else ‖cf a T f q‖ ^ 2 := by
    intro N q
    rw [bc_sub (hF.integrable one_le_two) ((memLp_Pc a T _ N 2).integrable one_le_two), bc_Pc hT]
    split_ifs <;> simp [cf, F]
  have hI : ∀ N : ℕ, ∫ x, ‖(F - Pc T (cf a T f) N) x‖ ^ 2 ∂box a T =
      T * ∑' q, (if q ∈ sqN N then 0 else ‖cf a T f q‖ ^ 2) := by
    intro N
    have h := (hasSum_bc hT (hD N)).tsum_eq
    simp_rw [hbcD] at h
    rw [h]; field_simp
  have htail : Tendsto (fun N : ℕ => ∑' q, (if q ∈ sqN N then 0 else ‖cf a T f q‖ ^ 2))
      atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : ℤ × ℤ => (0 : ℝ))
      (f := fun (N : ℕ) q => if q ∈ sqN N then 0 else ‖cf a T f q‖ ^ 2)
      (bound := fun q => ‖cf a T f q‖ ^ 2) hsum.summable
      (fun q => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_mem_sqN q] with N hN; simp [hN]))
      (Eventually.of_forall fun N q => by
        split_ifs <;> simp)
    simpa using this
  refine squeeze_zero (fun N => integral_nonneg fun x => sq_nonneg _) (fun N => ?_)
    (by simpa using htail.const_mul T)
  rw [← hI N]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
    ((memLp_two_iff_integrable_sq_norm (hD N).1).1 (hD N)) (ae_of_all _ fun x => ?_)
  have e : trig T (cf a T f) N x - f x = ((Pc T (cf a T f) N - F) x).re := by
    simp [trig_eq_re, Pc, F]
  have hn : ‖(F - Pc T (cf a T f) N) x‖ = ‖(Pc T (cf a T f) N - F) x‖ := by
    simp only [Pi.sub_apply]; exact norm_sub_rev _ _
  simp only
  rw [e, hn, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

end Polyfold.GapP1Sobolev
