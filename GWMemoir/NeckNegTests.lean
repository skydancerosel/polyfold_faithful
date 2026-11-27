import GWMemoir.NeckModels

/-!
# The model with growth on `ℝ × S¹`: the estimate for test tuples

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Proposition 4.16 (p. 110)
after the translation by `R/2` of p. 170. On the spaces `H^{k,-δ}` (growth `e^{δ|s|}` allowed)
the operator `∂_s + J ∂_t` is studied through `v = e^{-δ h(s)} u` with `h(s) ≈ |s|`, where it
becomes `L v = (∂_s + J ∂_t) v + a(s) v` on the unweighted spaces, `a = δ h'`, `a ≥ 0` for
`s ≥ 0`, `a ≤ 0` for `s ≤ 0`, `|a| ≤ δ`, and `|a| = δ` for `|s| ≥ 1`. This file proves, for test
tuples and `0 < δ < π`,
`∑_k ‖v_k‖²_{H¹} ≤ C (∑_k ‖(L v)_k‖²_{L²} + ∑_k [v_k]_0²)`, `[φ]_0 = ∫_0^1 φ(0, t) dt`.

* `cmean`: the circle mean `[φ](s)`; it is smooth (`contDiff_cmean`), commutes with `∂_s` and
  kills `∂_t`. `perp φ = φ - [φ]`.
* `circle_gap0`, `slice_gap0`: the gap on the circle without the mode `0`, with `a` depending on
  `s`: `(2π - δ)² ∫ |h|² ≤ ∫ |h' - i a h|²` when `∫ h = 0`.
* `pair_perp`, `pair_perp_H1`: for mean-zero pairs, `X + Z + 2∫ a (f ∂_s f + g ∂_s g)` with
  `|2 a f p| ≤ (δ/d) p² + δ d f²`; this closes for `δ < d = 2π - δ`, i.e. `δ < π`.
* The mode `0` and the assembly for tuples are in `NeckNegTuple`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped ContDiff Topology Real
open Set Function Filter MeasureTheory Complex
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir.NeckNeg

/-! ## 1. The circle mean -/

section Mean

/-- The circle mean `[φ](s) = ∫₀¹ φ(s, t) dt`. -/
def cmean (φ : ℝ × ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, φ (s, t)

variable {φ ψ : ℝ × ℝ → ℝ}

lemma intervalIntegrable_slice (hφ : IsTest φ) (s : ℝ) :
    IntervalIntegrable (fun t => φ (s, t)) volume 0 1 :=
  (hφ.smooth.continuous.comp (by fun_prop : Continuous fun t : ℝ => (s, t))).intervalIntegrable _ _

lemma hasDerivAt_cmean (hφ : IsTest φ) (s : ℝ) :
    HasDerivAt (cmean φ) (cmean (Ds φ) s) s := by
  obtain ⟨C, hC⟩ := hφ.ds.bounded
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hc : Continuous φ := hφ.smooth.continuous
  have hc' : Continuous (Ds φ) := hφ.ds.smooth.continuous
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s' t => φ (s', t)) (F' := fun s' t => Ds φ (s', t)) (x₀ := s) (s := univ)
    (bound := fun _ => C) Filter.univ_mem
    (Eventually.of_forall fun s' =>
      (hc.comp (by fun_prop : Continuous fun t : ℝ => (s', t))).aestronglyMeasurable)
    ((hc.comp (by fun_prop : Continuous fun t : ℝ => (s, t))).intervalIntegrable _ _)
    ((hc'.comp (by fun_prop : Continuous fun t : ℝ => (s, t))).aestronglyMeasurable)
    (ae_of_all _ fun t _ x _ => by rw [Real.norm_eq_abs]; exact hC _)
    intervalIntegrable_const
    (ae_of_all _ fun t _ x _ => hasDerivAt_s hd x t)).2

lemma deriv_cmean (hφ : IsTest φ) : deriv (cmean φ) = cmean (Ds φ) :=
  funext fun s => (hasDerivAt_cmean hφ s).deriv

lemma iteratedDeriv_cmean : ∀ (k : ℕ) {φ : ℝ × ℝ → ℝ}, IsTest φ →
    iteratedDeriv k (cmean φ) = cmean (Ds^[k] φ)
  | 0, _, _ => by simp
  | k + 1, φ, hφ => by
    rw [iteratedDeriv_succ', deriv_cmean hφ, iteratedDeriv_cmean k hφ.ds]; rfl

lemma contDiff_cmean (hφ : IsTest φ) : ContDiff ℝ ∞ (cmean φ) := by
  refine contDiff_of_differentiable_iteratedDeriv fun k _ => ?_
  rw [iteratedDeriv_cmean k hφ]
  exact fun s => (hasDerivAt_cmean (hφ.iterate_ds k) s).differentiableAt

lemma cmean_eq_zero (hφ : IsTest φ) : ∃ R, ∀ s, R < |s| → cmean φ s = 0 := by
  obtain ⟨R, hR⟩ := hφ.bddSupp
  refine ⟨R, fun s hs => ?_⟩
  simp only [cmean]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t _ => hR s t hs]
  simp

lemma isTest_cmean (hφ : IsTest φ) : IsTest fun x : ℝ × ℝ => cmean φ x.1 where
  smooth := (contDiff_cmean hφ).comp contDiff_fst
  periodic _ _ := rfl
  bddSupp := by
    obtain ⟨R, hR⟩ := cmean_eq_zero hφ
    exact ⟨R, fun s _ hs => hR s hs⟩

lemma cmean_Dt (hφ : IsTest φ) (s : ℝ) : cmean (Dt φ) s = 0 := by
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  simp only [cmean]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_t hd s t)
    (intervalIntegrable_slice hφ.dt s)]
  have := hφ.periodic s 0
  rw [zero_add] at this
  rw [this, sub_self]

lemma cmean_add (hφ : IsTest φ) (hψ : IsTest ψ) (s : ℝ) :
    cmean (fun x => φ x + ψ x) s = cmean φ s + cmean ψ s :=
  intervalIntegral.integral_add (intervalIntegrable_slice hφ s) (intervalIntegrable_slice hψ s)

lemma cmean_mul_s (c : ℝ → ℝ) (s : ℝ) : cmean (fun x => c x.1 * φ x) s = c s * cmean φ s := by
  simp only [cmean]; exact intervalIntegral.integral_const_mul _ _

lemma cmean_jv {n : ℕ} (J : Fin n → Fin n → ℝ) {r : Fin n → ℝ × ℝ → ℝ}
    (hr : ∀ k, IsTest (r k)) (k : Fin n) (s : ℝ) :
    cmean (jv J r k) s = ∑ l, J k l * cmean (r l) s := by
  simp only [cmean, jv]
  rw [intervalIntegral.integral_finsetSum fun l _ => (intervalIntegrable_slice (hr l) s).const_mul _]
  simp only [intervalIntegral.integral_const_mul]

lemma isTest_sub' (hφ : IsTest φ) (hψ : IsTest ψ) : IsTest fun x => φ x - ψ x := by
  have := hφ.add (hψ.const_mul (-1))
  convert this using 1
  funext x; simp [sub_eq_add_neg]

/-- `φ - [φ]`. -/
def perp (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun x => φ x - cmean φ x.1

lemma isTest_perp (hφ : IsTest φ) : IsTest (perp φ) := isTest_sub' hφ (isTest_cmean hφ)

lemma cmean_perp (hφ : IsTest φ) (s : ℝ) : cmean (perp φ) s = 0 := by
  have e := intervalIntegral.integral_sub (intervalIntegrable_slice hφ s)
    (intervalIntegrable_const (c := cmean φ s) (μ := volume) (a := 0) (b := 1))
  simp only [cmean, perp] at e ⊢
  rw [e]; simp

lemma Ds_perp (hφ : IsTest φ) : Ds (perp φ) = fun x => Ds φ x - cmean (Ds φ) x.1 := by
  have e : perp φ = φ - fun x => cmean φ x.1 := rfl
  rw [e, Ds_sub_fun (hφ.smooth.differentiable (by simp))
    ((isTest_cmean hφ).smooth.differentiable (by simp)),
    Ds_fun_s ((contDiff_cmean hφ).differentiable (by simp)), deriv_cmean hφ]
  rfl

lemma Dt_perp (hφ : IsTest φ) : Dt (perp φ) = Dt φ := by
  have e : perp φ = φ - fun x => cmean φ x.1 := rfl
  rw [e, Dt_sub_fun (hφ.smooth.differentiable (by simp))
    ((isTest_cmean hφ).smooth.differentiable (by simp)),
    Dt_fun_s ((contDiff_cmean hφ).differentiable (by simp))]
  funext x; simp

/-- Integrals over the cylinder compared slice by slice. -/
lemma integral_cyl_le {F G : ℝ × ℝ → ℝ} (hF : Integrable F cyl) (hG : Integrable G cyl)
    (h : ∀ s, ∫ t in (0 : ℝ)..1, F (s, t) ≤ ∫ t in (0 : ℝ)..1, G (s, t)) :
    ∫ x, F x ∂cyl ≤ ∫ x, G x ∂cyl := by
  rw [cyl, integral_prod _ hF, integral_prod _ hG]
  refine integral_mono hF.integral_prod_left hG.integral_prod_left fun s => ?_
  have := h s
  rwa [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    at this

lemma sq_cmean_le (hφ : IsTest φ) (s : ℝ) :
    cmean φ s ^ 2 ≤ ∫ t in (0 : ℝ)..1, φ (s, t) ^ 2 := by
  have hc : Continuous fun t : ℝ => φ (s, t) :=
    hφ.smooth.continuous.comp (by fun_prop : Continuous fun t : ℝ => (s, t))
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (φ (s, t) - cmean φ s) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have e : (fun t => (φ (s, t) - cmean φ s) ^ 2) =
      fun t => (φ (s, t) ^ 2 - (2 * cmean φ s) * φ (s, t)) + cmean φ s ^ 2 := by
    funext t; ring
  have := hφ.smooth.continuous
  have c1 : Continuous fun t => φ (s, t) ^ 2 - 2 * cmean φ s * φ (s, t) := by fun_prop
  have c2 : Continuous fun t => φ (s, t) ^ 2 := by fun_prop
  have c3 : Continuous fun t => 2 * cmean φ s * φ (s, t) := by fun_prop
  rw [e, intervalIntegral.integral_add (c1.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_sub (c2.intervalIntegrable _ _) (c3.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at h0
  have : ∫ t in (0 : ℝ)..1, φ (s, t) = cmean φ s := rfl
  rw [this] at h0
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h0
  nlinarith

lemma integral_sq_cmean_le (hφ : IsTest φ) :
    ∫ x, cmean φ x.1 ^ 2 ∂cyl ≤ ∫ x, φ x ^ 2 ∂cyl :=
  integral_cyl_le (tInt_sq (isTest_cmean hφ)) (tInt_sq hφ) fun s => by
    have := sq_cmean_le hφ s
    simpa using this

lemma integral_cyl_fst (f : ℝ → ℝ) : ∫ x, f x.1 ∂cyl = ∫ s, f s := by
  rw [cyl, integral_fun_fst]; simp [Measure.real]

end Mean

/-! ## 2. The gap without the mode `0` -/

section Gap

/-- **The gap on the circle without the mode `0`**: for a `1`-periodic `C¹` function
`h : ℝ → ℂ` with `∫₀¹ h = 0` and `d ≤ |2πn - a|` for `n ≠ 0`, `d² ∫₀¹ |h|² ≤ ∫₀¹ |h' - i a h|²`. -/
theorem circle_gap0 {h h' : ℝ → ℂ} (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h')
    (hp : h 1 = h 0) (hz : ∫ t in (0 : ℝ)..1, h t = 0) {a d : ℝ}
    (had : ∀ n : ℤ, n ≠ 0 → d ^ 2 ≤ (2 * π * n - a) ^ 2) :
    d ^ 2 * ∫ t in (0 : ℝ)..1, ‖h t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖h' t - (a * I) * h t‖ ^ 2 := by
  have hcont : Continuous h := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hgc : Continuous fun t => h' t - (a * I) * h t := by fun_prop
  have P1 := hasSum_sq_fourierCoeffOn zero_lt_one (memLp_Ioc_of_continuous hcont)
  have P2 := hasSum_sq_fourierCoeffOn zero_lt_one (memLp_Ioc_of_continuous hgc)
  simp only [sub_zero, inv_one, one_smul] at P1 P2
  have hcoef : ∀ n : ℤ, ‖fourierCoeffOn zero_lt_one (fun t => h' t - (a * I) * h t) n‖ ^ 2 =
      (2 * π * n - a) ^ 2 * ‖fourierCoeffOn zero_lt_one h n‖ ^ 2 := by
    intro n
    rw [fc_sub (g := fun t => (a * I) * h t) hc (continuous_const.mul hcont),
      fourierCoeffOn.const_mul h (a * I) n zero_lt_one, fc_deriv hd hc hp]
    have e : 2 * ↑π * I * ↑n * fourierCoeffOn zero_lt_one h n -
        ↑a * I * fourierCoeffOn zero_lt_one h n =
        (((2 * π * n - a : ℝ)) : ℂ) * I * fourierCoeffOn zero_lt_one h n := by
      push_cast; ring
    rw [e, norm_mul, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  refine hasSum_le (fun n => ?_) (P1.mul_left (d ^ 2)) P2
  rw [hcoef]
  by_cases hn : n = 0
  · subst hn
    have h0 : fourierCoeffOn zero_lt_one h 0 = 0 := by
      rw [fourierCoeffOn_eq_integral]
      simp only [neg_zero, fourier_zero, one_smul]
      rw [hz, smul_zero]
    rw [h0]; simp
  · exact mul_le_mul_of_nonneg_right (had n hn) (sq_nonneg _)

/-- **The gap on the slices without the mode `0`**, `a` depending on `s`. -/
theorem slice_gap0 {f g : ℝ × ℝ → ℝ} (hf : IsTest f) (hg : IsTest g)
    (hf0 : ∀ s, cmean f s = 0) (hg0 : ∀ s, cmean g s = 0) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    {d : ℝ} (had : ∀ s, ∀ n : ℤ, n ≠ 0 → d ^ 2 ≤ (2 * π * n - a s) ^ 2) :
    d ^ 2 * ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl ≤
      ∫ x, ((Dt g x - a x.1 * f x) ^ 2 + (Dt f x + a x.1 * g x) ^ 2) ∂cyl := by
  have i1 : Integrable (fun x => f x ^ 2 + g x ^ 2) cyl := (tInt_sq hf).add (tInt_sq hg)
  have i2 : Integrable (fun x => (Dt g x - a x.1 * f x) ^ 2 + (Dt f x + a x.1 * g x) ^ 2) cyl :=
    ((tInt_sq (hg.dt.add ((hf.mul_s ha).const_mul (-1)))).congr
      (ae_of_all _ fun x => by simp; ring)).add
      ((tInt_sq (hf.dt.add (hg.mul_s ha))).congr (ae_of_all _ fun x => by simp))
  rw [cyl, ← integral_const_mul, integral_prod _ (i1.const_mul _), integral_prod _ i2]
  refine integral_mono (i1.const_mul _).integral_prod_left i2.integral_prod_left fun s => ?_
  have hfd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.smooth.differentiable (by simp)
  set h : ℝ → ℂ := fun t => (g (s, t) : ℂ) - I * f (s, t)
  set h' : ℝ → ℂ := fun t => (Dt g (s, t) : ℂ) - I * Dt f (s, t)
  have hd : ∀ t, HasDerivAt h (h' t) t := fun t =>
    ((hasDerivAt_t hgd s t).ofReal_comp).sub (((hasDerivAt_t hfd s t).ofReal_comp).const_mul I)
  have hc : Continuous h' := by
    have := hg.dt.smooth.continuous; have := hf.dt.smooth.continuous
    fun_prop
  have hp : h 1 = h 0 := by
    simp only [h]; rw [← zero_add (1 : ℝ), hf.periodic, hg.periodic]
  have hz : ∫ t in (0 : ℝ)..1, h t = 0 := by
    have cf : Continuous fun t : ℝ => ((f (s, t) : ℝ) : ℂ) := by
      have := hf.smooth.continuous; fun_prop
    have cg : Continuous fun t : ℝ => ((g (s, t) : ℝ) : ℂ) := by
      have := hg.smooth.continuous; fun_prop
    simp only [h]
    have cf' : Continuous fun t : ℝ => I * ((f (s, t) : ℝ) : ℂ) := by fun_prop
    rw [intervalIntegral.integral_sub (cg.intervalIntegrable _ _) (cf'.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    have e1 := hf0 s; have e2 := hg0 s
    simp only [cmean] at e1 e2
    rw [e1, e2]; simp
  have key := circle_gap0 hd hc hp hz (had s)
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    at key
  have e1 : ∀ t, ‖h t‖ ^ 2 = f (s, t) ^ 2 + g (s, t) ^ 2 := fun t => by
    rw [norm_sq_sub_I]; ring
  have e2 : ∀ t, ‖h' t - (a s * I) * h t‖ ^ 2 =
      (Dt g (s, t) - a s * f (s, t)) ^ 2 + (Dt f (s, t) + a s * g (s, t)) ^ 2 := fun t => by
    have : h' t - (a s * I) * h t =
        ((Dt g (s, t) - a s * f (s, t) : ℝ) : ℂ) -
          I * ((Dt f (s, t) + a s * g (s, t) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h, h']; ring
    rw [this, norm_sq_sub_I]
  simp only [e1, e2] at key
  simpa only [integral_const_mul] using key

end Gap

/-! ## 3. Mean-zero pairs -/

section Pair

lemma amgm_cross {a δ d f p : ℝ} (hδ : 0 < δ) (hd : 0 < d) (ha : |a| ≤ δ) :
    -(δ / d * p ^ 2 + δ * d * f ^ 2) ≤ 2 * a * (f * p) := by
  have h1 : a ^ 2 ≤ δ ^ 2 := sq_le_sq' (abs_le.1 ha).1 (abs_le.1 ha).2
  have key : 0 ≤ δ * (δ * p ^ 2 + δ * d ^ 2 * f ^ 2 + 2 * a * d * f * p) := by
    have e : δ * (δ * p ^ 2 + δ * d ^ 2 * f ^ 2 + 2 * a * d * f * p) =
        (δ * p + a * d * f) ^ 2 + (δ ^ 2 - a ^ 2) * d ^ 2 * f ^ 2 := by ring
    rw [e]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sq_nonneg d)) (sq_nonneg f))
  have k2 := (mul_nonneg_iff_of_pos_left hδ).1 key
  have e : δ / d * p ^ 2 + δ * d * f ^ 2 + 2 * a * (f * p) =
      (δ * p ^ 2 + δ * d ^ 2 * f ^ 2 + 2 * a * d * f * p) / d := by
    field_simp
  have : 0 ≤ δ / d * p ^ 2 + δ * d * f ^ 2 + 2 * a * (f * p) := by
    rw [e]; exact div_nonneg k2 hd.le
  linarith

variable {f g : ℝ × ℝ → ℝ} {a : ℝ → ℝ} {δ : ℝ}

/-- **The identity for mean-zero pairs**: with `d = 2π - δ`, `0 < δ < π`, `|a| ≤ δ`,
`(1 - δ/d)(∫ (∂_s f)² + (∂_s g)² + d² ∫ f² + g²) ≤
∫ (∂_s f + ∂_t g + a f)² + (∂_s g - ∂_t f + a g)²`. -/
theorem pair_perp (hf : IsTest f) (hg : IsTest g) (hf0 : ∀ s, cmean f s = 0)
    (hg0 : ∀ s, cmean g s = 0) (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hπ : δ < π)
    (hab : ∀ s, |a s| ≤ δ) :
    (1 - δ / (2 * π - δ)) * (∫ x, (Ds f x ^ 2 + Ds g x ^ 2) ∂cyl +
        (2 * π - δ) ^ 2 * ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl) ≤
      ∫ x, ((Ds f x + Dt g x + a x.1 * f x) ^ 2 + (Ds g x - Dt f x + a x.1 * g x) ^ 2) ∂cyl := by
  set d := 2 * π - δ with hdd
  have hpi := Real.pi_pos
  have hd : 0 < d := by linarith
  have had : ∀ s, ∀ n : ℤ, n ≠ 0 → d ^ 2 ≤ (2 * π * n - (fun s => -a s) s) ^ 2 := by
    intro s n hn
    have h1 := abs_le.1 (hab s)
    simp only
    rcases lt_or_gt_of_ne hn with hn | hn
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hn
      have : 2 * π * n - -a s ≤ -d := by nlinarith
      nlinarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : d ≤ 2 * π * n - -a s := by nlinarith
      nlinarith
  have hS := slice_gap0 hf hg hf0 hg0 ha.neg had
  have iA : Integrable (fun x => Ds f x ^ 2 + Ds g x ^ 2) cyl := (tInt_sq hf.ds).add (tInt_sq hg.ds)
  have iY : Integrable (fun x => f x ^ 2 + g x ^ 2) cyl := (tInt_sq hf).add (tInt_sq hg)
  have iZ : Integrable (fun x => (Dt g x + a x.1 * f x) ^ 2 + (Dt f x - a x.1 * g x) ^ 2) cyl :=
    ((tInt_sq (hg.dt.add (hf.mul_s ha))).congr (ae_of_all _ fun x => by simp)).add
      ((tInt_sq (hf.dt.add ((hg.mul_s ha).const_mul (-1)))).congr
        (ae_of_all _ fun x => by simp; ring))
  have i1 : Integrable (fun x => Ds f x * Dt g x) cyl := tInt (test_mul hf.ds hg.dt)
  have i2 : Integrable (fun x => Dt f x * Ds g x) cyl := tInt (test_mul hf.dt hg.ds)
  have iC : Integrable (fun x => 2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x)) cyl :=
    (i1.const_mul 2).sub (i2.const_mul 2)
  have iE : Integrable (fun x => 2 * a x.1 * (f x * Ds f x + g x * Ds g x)) cyl := by
    have := tInt (((test_mul hf hf.ds).add (test_mul hg hg.ds)).mul_s (contDiff_const.mul ha)
      (χ := fun s => 2 * a s))
    exact this.congr (ae_of_all _ fun x => by simp)
  have e : (fun x => (Ds f x + Dt g x + a x.1 * f x) ^ 2 + (Ds g x - Dt f x + a x.1 * g x) ^ 2) =
      fun x => (Ds f x ^ 2 + Ds g x ^ 2) +
        ((Dt g x + a x.1 * f x) ^ 2 + (Dt f x - a x.1 * g x) ^ 2) +
        (2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x)) +
        2 * a x.1 * (f x * Ds f x + g x * Ds g x) := by
    funext x; ring
  have j1 : Integrable (fun x => (Ds f x ^ 2 + Ds g x ^ 2) +
      ((Dt g x + a x.1 * f x) ^ 2 + (Dt f x - a x.1 * g x) ^ 2)) cyl := iA.add iZ
  have j2 : Integrable (fun x => (Ds f x ^ 2 + Ds g x ^ 2) +
      ((Dt g x + a x.1 * f x) ^ 2 + (Dt f x - a x.1 * g x) ^ 2) +
      (2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x))) cyl := j1.add iC
  rw [e, integral_add j2 iE, integral_add j1 iC, integral_add iA iZ,
    integral_sub (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul,
    ibp_cross hf hg, sub_self, add_zero]
  have eZ : ∫ x, ((Dt g x - -a x.1 * f x) ^ 2 + (Dt f x + -a x.1 * g x) ^ 2) ∂cyl =
      ∫ x, ((Dt g x + a x.1 * f x) ^ 2 + (Dt f x - a x.1 * g x) ^ 2) ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [eZ] at hS
  have hE : -(δ / d * ∫ x, (Ds f x ^ 2 + Ds g x ^ 2) ∂cyl +
      δ * d * ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl) ≤
      ∫ x, 2 * a x.1 * (f x * Ds f x + g x * Ds g x) ∂cyl := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iA.const_mul _) (iY.const_mul _), ← integral_neg]
    refine integral_mono ((iA.const_mul _).add (iY.const_mul _)).neg iE fun x => ?_
    have h1 := amgm_cross (f := f x) (p := Ds f x) hδ hd (hab x.1)
    have h2 := amgm_cross (f := g x) (p := Ds g x) hδ hd (hab x.1)
    simp only
    linear_combination h1 + h2
  set X := ∫ x, (Ds f x ^ 2 + Ds g x ^ 2) ∂cyl
  set Y := ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl
  have eq : (1 - δ / d) * (X + d ^ 2 * Y) = X + d ^ 2 * Y - (δ / d * X + δ * d * Y) := by
    field_simp
  rw [eq]
  linarith

/-- The constant of `pair_perp_H1`. -/
def perpC (δ : ℝ) : ℝ :=
  3 + (4 + (1 + 3 * δ ^ 2) / (2 * π - δ) ^ 2) / (1 - δ / (2 * π - δ))

lemma perpC_nonneg {δ : ℝ} (hδ : 0 < δ) (hπ : δ < π) : 0 ≤ perpC δ := by
  have hpi := Real.pi_pos
  have hd : 0 < 2 * π - δ := by linarith
  have hθ : 0 < 1 - δ / (2 * π - δ) := by
    rw [sub_pos, div_lt_one hd]; linarith
  unfold perpC; positivity

/-- **The `H¹` bound for mean-zero pairs**:
`∫ f² + (∂_s f)² + (∂_t f)² ≤ perpC δ ∫ (∂_s f + ∂_t g + a f)² + (∂_s g - ∂_t f + a g)²`. -/
theorem pair_perp_H1 (hf : IsTest f) (hg : IsTest g) (hf0 : ∀ s, cmean f s = 0)
    (hg0 : ∀ s, cmean g s = 0) (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hπ : δ < π)
    (hab : ∀ s, |a s| ≤ δ) :
    ∫ x, (f x ^ 2 + Ds f x ^ 2 + Dt f x ^ 2) ∂cyl ≤ perpC δ *
      ∫ x, ((Ds f x + Dt g x + a x.1 * f x) ^ 2 + (Ds g x - Dt f x + a x.1 * g x) ^ 2) ∂cyl := by
  have hP := pair_perp hf hg hf0 hg0 ha hδ hπ hab
  have hpi := Real.pi_pos
  set d := 2 * π - δ with hdd
  have hd : 0 < d := by linarith
  set θ := 1 - δ / d with hθd
  have hθ : 0 < θ := by rw [hθd, sub_pos, div_lt_one hd]; linarith
  have iA : Integrable (fun x => Ds f x ^ 2 + Ds g x ^ 2) cyl := (tInt_sq hf.ds).add (tInt_sq hg.ds)
  have iY : Integrable (fun x => f x ^ 2 + g x ^ 2) cyl := (tInt_sq hf).add (tInt_sq hg)
  have iP : Integrable (fun x => Ds f x + Dt g x + a x.1 * f x) cyl :=
    tInt ((hf.ds.add hg.dt).add (hf.mul_s ha))
  have iW : Integrable (fun x => (Ds f x + Dt g x + a x.1 * f x) ^ 2 +
      (Ds g x - Dt f x + a x.1 * g x) ^ 2) cyl :=
    (tInt_sq ((hf.ds.add hg.dt).add (hf.mul_s ha))).add
      ((tInt_sq ((isTest_sub' hg.ds hf.dt).add (hg.mul_s ha))).congr (ae_of_all _ fun x => by simp))
  have iL : Integrable (fun x => f x ^ 2 + Ds f x ^ 2 + Dt f x ^ 2) cyl :=
    ((tInt_sq hf).add (tInt_sq hf.ds)).add (tInt_sq hf.dt)
  set X := ∫ x, (Ds f x ^ 2 + Ds g x ^ 2) ∂cyl
  set Y := ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl
  set W := ∫ x, ((Ds f x + Dt g x + a x.1 * f x) ^ 2 + (Ds g x - Dt f x + a x.1 * g x) ^ 2) ∂cyl
  have hX : 0 ≤ X := integral_nonneg fun x => by positivity
  have hY : 0 ≤ Y := integral_nonneg fun x => by positivity
  have hmono : ∫ x, (f x ^ 2 + Ds f x ^ 2 + Dt f x ^ 2) ∂cyl ≤
      4 * X + (1 + 3 * δ ^ 2) * Y + 3 * W := by
    have k1 : Integrable (fun x => 4 * (Ds f x ^ 2 + Ds g x ^ 2) +
        (1 + 3 * δ ^ 2) * (f x ^ 2 + g x ^ 2)) cyl :=
      (iA.const_mul 4).add (iY.const_mul (1 + 3 * δ ^ 2))
    have k2 : Integrable (fun x => 4 * (Ds f x ^ 2 + Ds g x ^ 2) +
        (1 + 3 * δ ^ 2) * (f x ^ 2 + g x ^ 2) + 3 * ((Ds f x + Dt g x + a x.1 * f x) ^ 2 +
        (Ds g x - Dt f x + a x.1 * g x) ^ 2)) cyl := k1.add (iW.const_mul 3)
    refine (integral_mono iL k2 fun x => ?_).trans (le_of_eq ?_)
    swap
    · rw [integral_add k1 (iW.const_mul 3), integral_add (iA.const_mul 4)
        (iY.const_mul (1 + 3 * δ ^ 2)), integral_const_mul, integral_const_mul, integral_const_mul]
    simp only
    have ha2 : a x.1 ^ 2 ≤ δ ^ 2 := sq_le_sq' (abs_le.1 (hab x.1)).1 (abs_le.1 (hab x.1)).2
    have hDt : Dt f x = Ds g x + a x.1 * g x - (Ds g x - Dt f x + a x.1 * g x) := by ring
    set Q := Ds g x - Dt f x + a x.1 * g x
    rw [hDt]
    nlinarith [sq_nonneg (Ds g x - a x.1 * g x), sq_nonneg (Ds g x + Q), sq_nonneg (a x.1 * g x + Q),
      sq_nonneg (Ds f x + Dt g x + a x.1 * f x), mul_le_mul_of_nonneg_right ha2 (sq_nonneg (g x)),
      sq_nonneg (Ds g x - Q), sq_nonneg (a x.1 * g x - Q), sq_nonneg (Ds g x - a x.1 * g x)]
  have hXY : X + d ^ 2 * Y ≤ W / θ := by rw [le_div_iff₀ hθ]; linarith
  have h4 : 4 * X + (1 + 3 * δ ^ 2) * Y ≤ (4 + (1 + 3 * δ ^ 2) / d ^ 2) * (X + d ^ 2 * Y) := by
    have hd2 : 0 < d ^ 2 := by positivity
    have : (4 + (1 + 3 * δ ^ 2) / d ^ 2) * (X + d ^ 2 * Y) =
        4 * X + (1 + 3 * δ ^ 2) * Y + (4 * d ^ 2 * Y + (1 + 3 * δ ^ 2) / d ^ 2 * X) := by
      field_simp; ring
    rw [this]
    have : 0 ≤ 4 * d ^ 2 * Y + (1 + 3 * δ ^ 2) / d ^ 2 * X := by positivity
    linarith
  have hK : 0 ≤ 4 + (1 + 3 * δ ^ 2) / d ^ 2 := by positivity
  calc _ ≤ 4 * X + (1 + 3 * δ ^ 2) * Y + 3 * W := hmono
    _ ≤ (4 + (1 + 3 * δ ^ 2) / d ^ 2) * (W / θ) + 3 * W := by
        have := mul_le_mul_of_nonneg_left hXY hK
        linarith
    _ = perpC δ * W := by simp only [perpC, ← hdd, ← hθd]; field_simp; ring

end Pair

end GWMemoir.NeckNeg
