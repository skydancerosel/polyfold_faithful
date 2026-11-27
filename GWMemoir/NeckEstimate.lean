import GWMemoir.EllipticEstimate

/-!
# The neck estimate for `∂_s + J ∂_t` on weighted cylinder spaces

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.3: the weighted estimate
on `ℝ × S¹` behind Proposition 4.15 (p. 109), on the functions with asymptotic constant `0`, at
the weights `0 < δ < 2π` fixed on p. 104. For `0 < δ < 2π` and a matrix `J` with `J² = -1`,
`‖r‖_{H^{m+1,δ}} ≤ C ‖(∂_s + J ∂_t) r‖_{H^{m,δ}}` on `(H^{m+1,δ}(ℝ × S¹))ⁿ`, with no lower-order
term (compare `cyl_estimate`, `δ = 0`).

* `circle_gap`: `d² ∫₀¹ |h|² ≤ ∫₀¹ |h' - i a h|²` for `1`-periodic `h`, when `d ≤ |2πn - a|` for
  all `n ∈ ℤ` (Parseval, `hasSum_sq_fourierCoeffOn`); `gap_le`: `d = min δ (2π - δ)` works for
  `a = ±δ`.
* `slice_gap`: the same on each circle `{s} × S¹`, integrated in `s`.
* `pair_estimate`: for test functions `f, g`, `∫ (∂_s f)² + (∂_s g)² + d² ∫ f² + g² ≤
  ∫ (∂_s f + ∂_t g - a f)² + (∂_s g - ∂_t f - a g)²`; the cross terms vanish by `ibp_cross` and
  `∫ f ∂_s f = 0`. With `g = (J r)_k` this is the identity of the design with the adapted inner
  product `⟨x, y⟩ + ⟨J x, J y⟩`, for which `J` is orthogonal.
* `pair_estimate_ew`, `one_weight`: the same for `w = e^{as} r`, `a = ±δ`, which is smooth;
  `test_estimate`: since `e^{2δ|s|} ≤ e^{2δs} + e^{-2δs}`, the weighted `H¹` estimate for test
  tuples with the explicit constant `gapConst J δ = 2 (8 + (1 + 5δ²)/d²)(1 + ∑ J_{kl}²)`.
* `crOpW`: `∂_s + J ∂_t : (H^{m+1,δ})ⁿ → (H^{m,δ})ⁿ`; `low_estimate`: the level-`0` estimate
  on `(H^{m+1,δ})ⁿ`, by density (`dense_test`).
* **`neck_estimate_sq`**, **`neck_estimate`**: all levels, by induction (`∂_s`, `∂_t` commute with
  `∂_s + J ∂_t`, `crOpW_dsH`, `crOpW_dtH`).
* **`neck_estimate_half`**: tuples vanishing for `s ≤ 0` (the half-cylinder with weight `e^{δs}`).
* `neck_hyps_witness`, `neck_estimate_pi`: `δ = π`, `J₀ = [[0, -1], [1, 0]]` and a nonzero pair
  vanishing for `s ≤ 0`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology InnerProductSpace Real
open Set Function Filter MeasureTheory Complex
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The gap on the circle -/

section Circle

lemma memLp_Ioc_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => hC t (Ioc_subset_Icc_self ht))

lemma intervalIntegrable_fourier_mul {f : ℝ → ℂ} (hf : Continuous f) (n : ℤ) :
    IntervalIntegrable (fun x : ℝ => fourier (-n) (x : AddCircle ((1 : ℝ) - 0)) • f x) volume 0 1 :=
  (((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).smul hf).intervalIntegrable _ _

lemma fc_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn zero_lt_one (fun t => f t - g t) n =
      fourierCoeffOn zero_lt_one f n - fourierCoeffOn zero_lt_one g n := by
  simp only [fourierCoeffOn_eq_integral, smul_sub]
  rw [← smul_sub, ← intervalIntegral.integral_sub (intervalIntegrable_fourier_mul hf n)
    (intervalIntegrable_fourier_mul hg n)]

lemma fc_deriv {h h' : ℝ → ℂ} (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h')
    (hp : h 1 = h 0) (n : ℤ) :
    fourierCoeffOn zero_lt_one h' n = 2 * π * I * n * fourierCoeffOn zero_lt_one h n := by
  by_cases hn : n = 0
  · subst hn
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Int.cast_zero, mul_zero, zero_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable _ _),
      hp, sub_self, smul_zero]
  · have := fourierCoeffOn_of_hasDerivAt zero_lt_one hn (fun x _ => hd x)
      (hc.intervalIntegrable _ _)
    rw [this, hp, sub_self, mul_zero, zero_sub]
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
    push_cast
    ring

/-- **The gap on the circle**: for a `1`-periodic `C¹` function `h : ℝ → ℂ` and `d` with
`d ≤ |2πn - a|` for all `n ∈ ℤ`, `d² ∫₀¹ |h|² ≤ ∫₀¹ |h' - i a h|²` (Parseval). -/
theorem circle_gap {h h' : ℝ → ℂ} (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h')
    (hp : h 1 = h 0) {a d : ℝ} (had : ∀ n : ℤ, d ^ 2 ≤ (2 * π * n - a) ^ 2) :
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
  exact mul_le_mul_of_nonneg_right (had n) (sq_nonneg _)

/-- For `0 < δ < 2π` the gap `min δ (2π - δ)` bounds `|2πn ∓ δ|`. -/
lemma gap_le {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 2 * π) {a : ℝ} (ha : a = δ ∨ a = -δ) (n : ℤ) :
    min δ (2 * π - δ) ^ 2 ≤ (2 * π * n - a) ^ 2 := by
  set d := min δ (2 * π - δ)
  have hd0 : 0 ≤ d := le_min h0.le (by linarith)
  have hd1 : d ≤ δ := min_le_left _ _
  have hd2 : d ≤ 2 * π - δ := min_le_right _ _
  have hpi := Real.pi_pos
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 hn
    have : 2 * π * n - a ≤ -d := by rcases ha with rfl | rfl <;> nlinarith
    nlinarith
  · subst hn; simp only [Int.cast_zero, mul_zero, zero_sub, neg_sq]
    rcases ha with rfl | rfl
    · nlinarith
    · nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : d ≤ 2 * π * n - a := by rcases ha with rfl | rfl <;> nlinarith
    nlinarith

end Circle

/-! ## 2. Test functions: linear combinations, weights, slices -/

section Tests

lemma test_mul {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) :
    IsTest (fun x => φ x * ψ x) := hψ.mul_smPer hφ.smPer

lemma isTest_zero : IsTest (fun _ : ℝ × ℝ => (0 : ℝ)) :=
  ⟨contDiff_const, fun _ _ => rfl, ⟨0, fun _ _ _ => rfl⟩⟩

lemma isTest_finsum {ι : Type*} (s : Finset ι) {φ : ι → ℝ × ℝ → ℝ} (h : ∀ i, IsTest (φ i))
    (c : ι → ℝ) : IsTest (fun x => ∑ i ∈ s, c i * φ i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTest_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact ((h i).const_mul (c i)).add ih

lemma isTest_lin {n : ℕ} {φ : Fin n → ℝ × ℝ → ℝ} (h : ∀ i, IsTest (φ i)) (c : Fin n → ℝ) :
    IsTest (fun x => ∑ i, c i * φ i x) := isTest_finsum _ h c

lemma tInt {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : Integrable φ cyl :=
  memLp_one_iff_integrable.1 (h.memLp 1)

lemma tInt_sq {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : Integrable (fun x => φ x ^ 2) cyl :=
  (h.memLp 2).integrable_sq

lemma Ds_lin {n : ℕ} {φ : Fin n → ℝ × ℝ → ℝ} (h : ∀ i, Differentiable ℝ (φ i)) (c : Fin n → ℝ) :
    Ds (fun x => ∑ i, c i * φ i x) = fun x => ∑ i, c i * Ds (φ i) x := by
  funext x
  obtain ⟨s, t⟩ := x
  have h1 : HasDerivAt (fun s' => ∑ i, c i * φ i (s', t)) (∑ i, c i * Ds (φ i) (s, t)) s :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_s (h i) s t).const_mul (c i)
  have hd : Differentiable ℝ (fun x => ∑ i, c i * φ i x) := by
    have := fun i => (h i).const_mul (c i)
    fun_prop
  exact (hasDerivAt_s hd s t).unique h1

lemma Dt_lin {n : ℕ} {φ : Fin n → ℝ × ℝ → ℝ} (h : ∀ i, Differentiable ℝ (φ i)) (c : Fin n → ℝ) :
    Dt (fun x => ∑ i, c i * φ i x) = fun x => ∑ i, c i * Dt (φ i) x := by
  funext x
  obtain ⟨s, t⟩ := x
  have h1 : HasDerivAt (fun t' => ∑ i, c i * φ i (s, t')) (∑ i, c i * Dt (φ i) (s, t)) t :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_t (h i) s t).const_mul (c i)
  have hd : Differentiable ℝ (fun x => ∑ i, c i * φ i x) := by
    have := fun i => (h i).const_mul (c i)
    fun_prop
  exact (hasDerivAt_t hd s t).unique h1

/-- The weight `e^{a s}`. -/
def ew (a : ℝ) (s : ℝ) : ℝ := Real.exp (a * s)

lemma contDiff_ew (a : ℝ) : ContDiff ℝ ∞ (ew a) := by unfold ew; fun_prop

lemma deriv_ew (a s : ℝ) : deriv (ew a) s = a * ew a s := by
  have := ((hasDerivAt_id s).const_mul a).exp
  simp only [id, mul_one] at this
  unfold ew; rw [this.deriv]; ring

lemma Ds_ew {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (a : ℝ) (x : ℝ × ℝ) :
    Ds (fun y => ew a y.1 * φ y) x = ew a x.1 * (Ds φ x + a * φ x) := by
  rw [Ds_mul_s hφ ((contDiff_ew a).differentiable (by simp))]; simp only [deriv_ew]; ring

lemma Dt_ew {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (a : ℝ) (x : ℝ × ℝ) :
    Dt (fun y => ew a y.1 * φ y) x = ew a x.1 * Dt φ x := by
  rw [Dt_mul_s hφ ((contDiff_ew a).differentiable (by simp))]

lemma norm_sq_sub_I (x y : ℝ) : ‖(x : ℂ) - I * y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- **The gap on the slices**: for test functions `f, g` and `d ≤ |2πn - a|` (`n ∈ ℤ`),
`d² ∫ (f² + g²) ≤ ∫ (∂_t g - a f)² + (∂_t f + a g)²`: on each circle `{s} × S¹` this is
`circle_gap` for `h = g - i f`. -/
theorem slice_gap {f g : ℝ × ℝ → ℝ} (hf : IsTest f) (hg : IsTest g) {a d : ℝ}
    (had : ∀ n : ℤ, d ^ 2 ≤ (2 * π * n - a) ^ 2) :
    d ^ 2 * ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl ≤
      ∫ x, ((Dt g x - a * f x) ^ 2 + (Dt f x + a * g x) ^ 2) ∂cyl := by
  have i1 : Integrable (fun x => f x ^ 2 + g x ^ 2) cyl := (tInt_sq hf).add (tInt_sq hg)
  have i2 : Integrable (fun x => (Dt g x - a * f x) ^ 2 + (Dt f x + a * g x) ^ 2) cyl :=
    ((tInt_sq (hg.dt.add (hf.const_mul (-a)))).congr (ae_of_all _ fun x => by simp; ring)).add
      ((tInt_sq (hf.dt.add (hg.const_mul a))).congr (ae_of_all _ fun x => by simp))
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
  have key := circle_gap hd hc hp had
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    at key
  have e1 : ∀ t, ‖h t‖ ^ 2 = f (s, t) ^ 2 + g (s, t) ^ 2 := fun t => by
    rw [norm_sq_sub_I]; ring
  have e2 : ∀ t, ‖h' t - (a * I) * h t‖ ^ 2 =
      (Dt g (s, t) - a * f (s, t)) ^ 2 + (Dt f (s, t) + a * g (s, t)) ^ 2 := fun t => by
    have : h' t - (a * I) * h t =
        ((Dt g (s, t) - a * f (s, t) : ℝ) : ℂ) - I * ((Dt f (s, t) + a * g (s, t) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h, h']; ring
    rw [this, norm_sq_sub_I]
  simp only [e1, e2] at key
  simpa only [integral_const_mul] using key

end Tests

/-! ## 3. The identity for `∂_s + J ∂_t - a` -/

section Pair

lemma integral_ds_mul_self {f : ℝ × ℝ → ℝ} (hf : IsTest f) : ∫ x, Ds f x * f x ∂cyl = 0 := by
  have h := hf.smPer.integral_mul_ds hf
  have e : ∫ x, f x * Ds f x ∂cyl = ∫ x, Ds f x * f x ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  linarith

/-- **The identity, unweighted**: for test functions `f, g` (the pair `(r_k, (J r)_k)`) and
`d ≤ |2πn - a|`, `∫ (∂_s f)² + (∂_s g)² + d² ∫ f² + g² ≤ ∫ (∂_s f + ∂_t g - a f)² +
(∂_s g - ∂_t f - a g)²`. The cross terms vanish: `∫ ∂_s f ∂_t g = ∫ ∂_t f ∂_s g` (`ibp_cross`)
and `∫ f ∂_s f = 0`. -/
theorem pair_estimate {f g : ℝ × ℝ → ℝ} (hf : IsTest f) (hg : IsTest g) {a d : ℝ}
    (had : ∀ n : ℤ, d ^ 2 ≤ (2 * π * n - a) ^ 2) :
    ∫ x, (Ds f x ^ 2 + Ds g x ^ 2) ∂cyl + d ^ 2 * ∫ x, (f x ^ 2 + g x ^ 2) ∂cyl ≤
      ∫ x, ((Ds f x + Dt g x - a * f x) ^ 2 + (Ds g x - Dt f x - a * g x) ^ 2) ∂cyl := by
  have hS := slice_gap hf hg had
  have iA : Integrable (fun x => Ds f x ^ 2 + Ds g x ^ 2) cyl :=
    (tInt_sq hf.ds).add (tInt_sq hg.ds)
  have iB : Integrable (fun x => (Dt g x - a * f x) ^ 2 + (Dt f x + a * g x) ^ 2) cyl :=
    ((tInt_sq (hg.dt.add (hf.const_mul (-a)))).congr (ae_of_all _ fun x => by simp; ring)).add
      ((tInt_sq (hf.dt.add (hg.const_mul a))).congr (ae_of_all _ fun x => by simp))
  have i1 : Integrable (fun x => Ds f x * Dt g x) cyl := tInt (test_mul hf.ds hg.dt)
  have i2 : Integrable (fun x => Dt f x * Ds g x) cyl := tInt (test_mul hf.dt hg.ds)
  have i3 : Integrable (fun x => Ds f x * f x) cyl := tInt (test_mul hf.ds hf)
  have i4 : Integrable (fun x => Ds g x * g x) cyl := tInt (test_mul hg.ds hg)
  have e : (fun x => (Ds f x + Dt g x - a * f x) ^ 2 + (Ds g x - Dt f x - a * g x) ^ 2) =
      fun x => (Ds f x ^ 2 + Ds g x ^ 2) + ((Dt g x - a * f x) ^ 2 + (Dt f x + a * g x) ^ 2) +
        (2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x) - (2 * a) * (Ds f x * f x) -
          (2 * a) * (Ds g x * g x)) := by
    funext x; ring
  have jAB : Integrable (fun x => (Ds f x ^ 2 + Ds g x ^ 2) +
      ((Dt g x - a * f x) ^ 2 + (Dt f x + a * g x) ^ 2)) cyl := iA.add iB
  have jC1 : Integrable (fun x => 2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x)) cyl :=
    (i1.const_mul 2).sub (i2.const_mul 2)
  have jC2 : Integrable (fun x => 2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x) -
      (2 * a) * (Ds f x * f x)) cyl := jC1.sub (i3.const_mul _)
  have jC3 : Integrable (fun x => 2 * (Ds f x * Dt g x) - 2 * (Dt f x * Ds g x) -
      (2 * a) * (Ds f x * f x) - (2 * a) * (Ds g x * g x)) cyl := jC2.sub (i4.const_mul _)
  rw [e, integral_add jAB jC3, integral_add iA iB, integral_sub jC2 (i4.const_mul _),
    integral_sub jC1 (i3.const_mul _), integral_sub (i1.const_mul 2) (i2.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    ibp_cross hf hg, integral_ds_mul_self hf, integral_ds_mul_self hg]
  linarith

/-- **The identity with the weight `e^{a s}`**: for test functions `f, g`,
`∫ e^{2as}((∂_s f + a f)² + (∂_s g + a g)²) + d² ∫ e^{2as}(f² + g²) ≤
∫ e^{2as}((∂_s f + ∂_t g)² + (∂_s g - ∂_t f)²)`; this is `pair_estimate` for `e^{as} f`,
`e^{as} g`. -/
theorem pair_estimate_ew {f g : ℝ × ℝ → ℝ} (hf : IsTest f) (hg : IsTest g) {a d : ℝ}
    (had : ∀ n : ℤ, d ^ 2 ≤ (2 * π * n - a) ^ 2) :
    ∫ x, ew a x.1 ^ 2 * ((Ds f x + a * f x) ^ 2 + (Ds g x + a * g x) ^ 2) ∂cyl +
        d ^ 2 * ∫ x, ew a x.1 ^ 2 * (f x ^ 2 + g x ^ 2) ∂cyl ≤
      ∫ x, ew a x.1 ^ 2 * ((Ds f x + Dt g x) ^ 2 + (Ds g x - Dt f x) ^ 2) ∂cyl := by
  have hF := hf.mul_s (contDiff_ew a)
  have hG := hg.mul_s (contDiff_ew a)
  have hfd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.smooth.differentiable (by simp)
  have h := pair_estimate hF hG had
  simp only [Ds_ew hfd, Ds_ew hgd, Dt_ew hfd, Dt_ew hgd] at h
  have e1 : ∫ x, ((ew a x.1 * (Ds f x + a * f x)) ^ 2 + (ew a x.1 * (Ds g x + a * g x)) ^ 2) ∂cyl
      = ∫ x, ew a x.1 ^ 2 * ((Ds f x + a * f x) ^ 2 + (Ds g x + a * g x) ^ 2) ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e2 : ∫ x, ((ew a x.1 * f x) ^ 2 + (ew a x.1 * g x) ^ 2) ∂cyl
      = ∫ x, ew a x.1 ^ 2 * (f x ^ 2 + g x ^ 2) ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  have e3 : ∫ x, ((ew a x.1 * (Ds f x + a * f x) + ew a x.1 * Dt g x - a * (ew a x.1 * f x)) ^ 2
      + (ew a x.1 * (Ds g x + a * g x) - ew a x.1 * Dt f x - a * (ew a x.1 * g x)) ^ 2) ∂cyl
      = ∫ x, ew a x.1 ^ 2 * ((Ds f x + Dt g x) ^ 2 + (Ds g x - Dt f x) ^ 2) ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  rwa [e1, e2, e3] at h

end Pair

/-! ## 4. Tuples: the estimate for test functions -/

section Tuple

variable {n : ℕ} (J : Fin n → Fin n → ℝ)

/-- `(J r)_k = ∑_l J_{kl} r_l`. -/
def jv (r : Fin n → ℝ × ℝ → ℝ) (k : Fin n) : ℝ × ℝ → ℝ := fun x => ∑ l, J k l * r l x

/-- `((∂_s + J ∂_t) r)_k = ∂_s r_k + ∑_l J_{kl} ∂_t r_l`. -/
def dbarCyl (r : Fin n → ℝ × ℝ → ℝ) (k : Fin n) : ℝ × ℝ → ℝ :=
  fun x => Ds (r k) x + ∑ l, J k l * Dt (r l) x

variable {J} {r : Fin n → ℝ × ℝ → ℝ}

lemma isTest_jv (hr : ∀ k, IsTest (r k)) (k : Fin n) : IsTest (jv J r k) := isTest_lin hr (J k)

lemma isTest_dbar (hr : ∀ k, IsTest (r k)) (k : Fin n) : IsTest (dbarCyl J r k) :=
  (hr k).ds.add (isTest_lin (fun l => (hr l).dt) (J k))

lemma diff_of_test (hr : ∀ k, IsTest (r k)) (k : Fin n) : Differentiable ℝ (r k) :=
  (hr k).smooth.differentiable (by simp)

lemma dbar_eq (hr : ∀ k, IsTest (r k)) (k : Fin n) (x : ℝ × ℝ) :
    Ds (r k) x + Dt (jv J r k) x = dbarCyl J r k x := by
  have h : Dt (jv J r k) = fun x => ∑ l, J k l * Dt (r l) x := Dt_lin (diff_of_test hr) (J k)
  rw [h]; rfl

lemma jdbar_eq (hJ : IsCxMat J) (hr : ∀ k, IsTest (r k)) (k : Fin n) (x : ℝ × ℝ) :
    Ds (jv J r k) x - Dt (r k) x = jv J (dbarCyl J r) k x := by
  have h : Ds (jv J r k) = fun x => ∑ l, J k l * Ds (r l) x := Ds_lin (diff_of_test hr) (J k)
  rw [h]
  simp only [jv, dbarCyl, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have : ∑ l, ∑ j, J k l * (J l j * Dt (r j) x) = - Dt (r k) x := by
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, hJ k]
    simp
  rw [this]; ring

/-- The identity for a tuple, componentwise: with `v = J r`,
`∫ e^{2as}((∂_s r_k + a r_k)² + (∂_s v_k + a v_k)²) + d² ∫ e^{2as}(r_k² + v_k²) ≤
∫ e^{2as}(((∂_s + J∂_t) r)_k² + (J (∂_s + J∂_t) r)_k²)`. -/
theorem tuple_core (hJ : IsCxMat J) (hr : ∀ k, IsTest (r k)) {a d : ℝ}
    (had : ∀ n : ℤ, d ^ 2 ≤ (2 * π * n - a) ^ 2) (k : Fin n) :
    ∫ x, ew a x.1 ^ 2 * ((Ds (r k) x + a * r k x) ^ 2 +
        (Ds (jv J r k) x + a * jv J r k x) ^ 2) ∂cyl +
      d ^ 2 * ∫ x, ew a x.1 ^ 2 * (r k x ^ 2 + jv J r k x ^ 2) ∂cyl ≤
      ∫ x, ew a x.1 ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl := by
  have h := pair_estimate_ew (hr k) (isTest_jv (J := J) hr k) had
  simp only [dbar_eq hr, jdbar_eq hJ hr] at h
  exact h

lemma tInt_ew_sq {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (a : ℝ) :
    Integrable (fun x => ew a x.1 ^ 2 * φ x ^ 2) cyl :=
  (tInt_sq (h.mul_s (contDiff_ew a))).congr (ae_of_all _ fun x => by dsimp only; ring)

lemma pointwise_split (r X Y v Q P a : ℝ) (hDt : 0 ≤ P) :
    r ^ 2 + (X - a * r) ^ 2 + (Y - a * v - Q) ^ 2 ≤
      5 * (X ^ 2 + Y ^ 2) + (1 + 5 * a ^ 2) * (r ^ 2 + v ^ 2) + 3 * (P + Q ^ 2) := by
  nlinarith [sq_nonneg (X + a * r), sq_nonneg (Y + a * v), sq_nonneg (Y + Q),
    sq_nonneg (a * v - Q), sq_nonneg (a * v), sq_nonneg r]

/-- For one weight `e^{as}` and one component, with `d > 0`:
`∫ e^{2as}(r_k² + (∂_s r_k)² + (∂_t r_k)²) ≤ K ∫ e^{2as}(((∂̄ r)_k)² + ((J∂̄ r)_k)²)`. -/
theorem one_weight (hJ : IsCxMat J) (hr : ∀ k, IsTest (r k)) {a d : ℝ} (hd : 0 < d)
    (had : ∀ n : ℤ, d ^ 2 ≤ (2 * π * n - a) ^ 2) (k : Fin n) :
    ∫ x, ew a x.1 ^ 2 * (r k x ^ 2 + Ds (r k) x ^ 2 + Dt (r k) x ^ 2) ∂cyl ≤
      (8 + (1 + 5 * a ^ 2) / d ^ 2) *
        ∫ x, ew a x.1 ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl := by
  have core := tuple_core hJ hr had k
  set c := 1 + 5 * a ^ 2 with hc
  have hX : IsTest (fun x => Ds (r k) x + a * r k x) := (hr k).ds.add ((hr k).const_mul a)
  have hY : IsTest (fun x => Ds (jv J r k) x + a * jv J r k x) :=
    (isTest_jv hr k).ds.add ((isTest_jv hr k).const_mul a)
  have iP : Integrable (fun x => ew a x.1 ^ 2 * ((Ds (r k) x + a * r k x) ^ 2 +
      (Ds (jv J r k) x + a * jv J r k x) ^ 2)) cyl :=
    ((tInt_ew_sq hX a).add (tInt_ew_sq hY a)).congr (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
  have iZ : Integrable (fun x => ew a x.1 ^ 2 * (r k x ^ 2 + jv J r k x ^ 2)) cyl :=
    ((tInt_ew_sq (hr k) a).add (tInt_ew_sq (isTest_jv hr k) a)).congr
      (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
  have iR : Integrable (fun x => ew a x.1 ^ 2 * (dbarCyl J r k x ^ 2 +
      jv J (dbarCyl J r) k x ^ 2)) cyl :=
    ((tInt_ew_sq (isTest_dbar hr k) a).add (tInt_ew_sq (isTest_jv (isTest_dbar hr) k) a)).congr
      (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
  have iL : Integrable (fun x => ew a x.1 ^ 2 * (r k x ^ 2 + Ds (r k) x ^ 2 +
      Dt (r k) x ^ 2)) cyl :=
    (((tInt_ew_sq (hr k) a).add (tInt_ew_sq (hr k).ds a)).add (tInt_ew_sq (hr k).dt a)).congr
      (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
  set P := ∫ x, ew a x.1 ^ 2 * ((Ds (r k) x + a * r k x) ^ 2 +
      (Ds (jv J r k) x + a * jv J r k x) ^ 2) ∂cyl
  set Z := ∫ x, ew a x.1 ^ 2 * (r k x ^ 2 + jv J r k x ^ 2) ∂cyl
  set R := ∫ x, ew a x.1 ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl
  have hP : 0 ≤ P := integral_nonneg fun x => by positivity
  have hZ : 0 ≤ Z := integral_nonneg fun x => by positivity
  have hmono : ∫ x, ew a x.1 ^ 2 * (r k x ^ 2 + Ds (r k) x ^ 2 + Dt (r k) x ^ 2) ∂cyl ≤
      5 * P + c * Z + 3 * R := by
    have i3 : Integrable (fun x => 5 * (ew a x.1 ^ 2 * ((Ds (r k) x + a * r k x) ^ 2 +
        (Ds (jv J r k) x + a * jv J r k x) ^ 2)) + c * (ew a x.1 ^ 2 * (r k x ^ 2 +
        jv J r k x ^ 2))) cyl := (iP.const_mul 5).add (iZ.const_mul c)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iP.const_mul 5) (iZ.const_mul c), ← integral_add i3 (iR.const_mul 3)]
    refine integral_mono iL (i3.add (iR.const_mul 3)) fun x => ?_
    have hDt : Dt (r k) x = (Ds (jv J r k) x + a * jv J r k x) - a * jv J r k x -
        jv J (dbarCyl J r) k x := by
      rw [← jdbar_eq hJ hr k x]; ring
    have hDs : Ds (r k) x = (Ds (r k) x + a * r k x) - a * r k x := by ring
    have hw : 0 ≤ ew a x.1 ^ 2 := sq_nonneg _
    have key := pointwise_split (r k x) (Ds (r k) x + a * r k x)
      (Ds (jv J r k) x + a * jv J r k x) (jv J r k x) (jv J (dbarCyl J r) k x)
      (dbarCyl J r k x ^ 2) a (sq_nonneg _)
    rw [← hDs, ← hDt] at key
    dsimp only
    nlinarith [mul_le_mul_of_nonneg_left key hw]
  have hZR : Z ≤ R / d ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hPR : P ≤ R := by nlinarith [mul_nonneg (sq_nonneg d) hZ]
  calc _ ≤ 5 * P + c * Z + 3 * R := hmono
    _ ≤ 5 * R + c * (R / d ^ 2) + 3 * R := by
        have hc0 : 0 ≤ c := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hZR hc0]
    _ = (8 + c / d ^ 2) * R := by ring

end Tuple

/-! ## 5. The weight `e^{δ|s|}` -/

section Assembly

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {r : Fin n → ℝ × ℝ → ℝ}

lemma wt_eq_ew (δ : ℝ) (x : ℝ × ℝ) : wt δ x = ew δ x.1 ∨ wt δ x = ew (-δ) x.1 := by
  unfold wt ew
  rcases abs_choice x.1 with h | h <;> rw [h]
  · left; rfl
  · right; congr 1; ring

lemma wt_sq_le (δ : ℝ) (x : ℝ × ℝ) : wt δ x ^ 2 ≤ ew δ x.1 ^ 2 + ew (-δ) x.1 ^ 2 := by
  rcases wt_eq_ew δ x with h | h <;> rw [h]
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · exact le_add_of_nonneg_left (sq_nonneg _)

lemma ew_sq_le {δ a : ℝ} (hδ : 0 ≤ δ) (ha : a = δ ∨ a = -δ) (x : ℝ × ℝ) :
    ew a x.1 ^ 2 ≤ wt δ x ^ 2 := by
  have : ew a x.1 ≤ wt δ x := by
    unfold ew wt; apply Real.exp_le_exp.2
    rcases ha with rfl | rfl
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) hδ
    · rw [neg_mul, ← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) hδ
  exact pow_le_pow_left₀ (Real.exp_pos _).le this 2

lemma sum_jv_sq_le (y : Fin n → ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    ∑ k, jv J y k x ^ 2 ≤ (∑ k, ∑ l, J k l ^ 2) * ∑ l, y l x ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma sum_weight_le (w : ℝ) (y : Fin n → ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    ∑ k, w ^ 2 * (y k x ^ 2 + jv J y k x ^ 2) ≤
      (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, (w * y k x) ^ 2 := by
  have cs := sum_jv_sq_le (J := J) y x
  have e1 : ∑ k, w ^ 2 * (y k x ^ 2 + jv J y k x ^ 2) =
      w ^ 2 * ∑ k, y k x ^ 2 + w ^ 2 * ∑ k, jv J y k x ^ 2 := by
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
  have e2 : ∑ k, (w * y k x) ^ 2 = w ^ 2 * ∑ k, y k x ^ 2 := by
    rw [Finset.mul_sum]; simp only [mul_pow]
  rw [e1, e2]
  have hw := sq_nonneg w
  have hS : 0 ≤ ∑ k, y k x ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left cs hw]

/-- **The neck estimate for test functions**, `0 < δ < 2π`, with `d = min δ (2π - δ)`:
`∑_k ‖e^{δ|s|} r_k‖² + ‖e^{δ|s|} ∂_s r_k‖² + ‖e^{δ|s|} ∂_t r_k‖² ≤
C ∑_k ‖e^{δ|s|} ((∂_s + J ∂_t) r)_k‖²`, `C = 2 (8 + (1 + 5δ²)/d²)(1 + ∑ J_{kl}²)`. The weight
`e^{δ|s|}` is compared with `e^{δs}` and `e^{-δs}`, for which `one_weight` applies. -/
theorem test_estimate (hJ : IsCxMat J) (hr : ∀ k, IsTest (r k)) {δ : ℝ} (h0 : 0 < δ)
    (h1 : δ < 2 * π) :
    ∑ k, ∫ x, ((wt δ x * r k x) ^ 2 + (wt δ x * Ds (r k) x) ^ 2 +
        (wt δ x * Dt (r k) x) ^ 2) ∂cyl ≤
      (2 * (8 + (1 + 5 * δ ^ 2) / min δ (2 * π - δ) ^ 2) * (1 + ∑ k, ∑ l, J k l ^ 2)) *
        ∑ k, ∫ x, (wt δ x * dbarCyl J r k x) ^ 2 ∂cyl := by
  set d := min δ (2 * π - δ) with hd
  have hd0 : 0 < d := lt_min h0 (by linarith)
  set K := 8 + (1 + 5 * δ ^ 2) / d ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have wP := one_weight hJ hr hd0 (gap_le h0 h1 (Or.inl rfl))
  have wM := one_weight hJ hr hd0 (gap_le h0 h1 (Or.inr rfl))
  simp only [neg_sq] at wM
  have iR : ∀ k, Integrable (fun x => wt δ x ^ 2 * (dbarCyl J r k x ^ 2 +
      jv J (dbarCyl J r) k x ^ 2)) cyl := fun k =>
    ((((isTest_dbar hr k).memLp_wt δ).integrable_sq.add
      ((isTest_jv (isTest_dbar hr) k).memLp_wt δ).integrable_sq)).congr
      (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
  have hk : ∀ k, ∫ x, ((wt δ x * r k x) ^ 2 + (wt δ x * Ds (r k) x) ^ 2 +
      (wt δ x * Dt (r k) x) ^ 2) ∂cyl ≤
      2 * K * ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl := by
    intro k
    have iW : Integrable (fun x => (wt δ x * r k x) ^ 2 + (wt δ x * Ds (r k) x) ^ 2 +
        (wt δ x * Dt (r k) x) ^ 2) cyl :=
      (((hr k).memLp_wt δ).integrable_sq.add ((hr k).ds.memLp_wt δ).integrable_sq).add
        ((hr k).dt.memLp_wt δ).integrable_sq
    have iL : ∀ a, Integrable (fun x => ew a x.1 ^ 2 * (r k x ^ 2 + Ds (r k) x ^ 2 +
        Dt (r k) x ^ 2)) cyl := fun a =>
      (((tInt_ew_sq (hr k) a).add (tInt_ew_sq (hr k).ds a)).add (tInt_ew_sq (hr k).dt a)).congr
        (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
    have iRa : ∀ a, Integrable (fun x => ew a x.1 ^ 2 * (dbarCyl J r k x ^ 2 +
        jv J (dbarCyl J r) k x ^ 2)) cyl := fun a =>
      ((tInt_ew_sq (isTest_dbar hr k) a).add (tInt_ew_sq (isTest_jv (isTest_dbar hr) k) a)).congr
        (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)
    have s1 : ∫ x, ((wt δ x * r k x) ^ 2 + (wt δ x * Ds (r k) x) ^ 2 +
        (wt δ x * Dt (r k) x) ^ 2) ∂cyl ≤
        ∫ x, ew δ x.1 ^ 2 * (r k x ^ 2 + Ds (r k) x ^ 2 + Dt (r k) x ^ 2) ∂cyl +
          ∫ x, ew (-δ) x.1 ^ 2 * (r k x ^ 2 + Ds (r k) x ^ 2 + Dt (r k) x ^ 2) ∂cyl := by
      rw [← integral_add (iL δ) (iL (-δ))]
      refine integral_mono iW ((iL δ).add (iL (-δ))) fun x => ?_
      dsimp only
      have := wt_sq_le δ x
      have hL : 0 ≤ r k x ^ 2 + Ds (r k) x ^ 2 + Dt (r k) x ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hL]
    have s2 : ∀ a, (a = δ ∨ a = -δ) →
        ∫ x, ew a x.1 ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl ≤
          ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl :=
      fun a ha => integral_mono (iRa a) (iR k) fun x =>
        mul_le_mul_of_nonneg_right (ew_sq_le h0.le ha x) (by positivity)
    calc _ ≤ _ := s1
      _ ≤ K * ∫ x, ew δ x.1 ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl +
          K * ∫ x, ew (-δ) x.1 ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl :=
          add_le_add (wP k) (wM k)
      _ ≤ K * ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl +
          K * ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl :=
          add_le_add (mul_le_mul_of_nonneg_left (s2 δ (Or.inl rfl)) hK0)
            (mul_le_mul_of_nonneg_left (s2 (-δ) (Or.inr rfl)) hK0)
      _ = _ := by ring
  have iD : ∀ k, Integrable (fun x => (wt δ x * dbarCyl J r k x) ^ 2) cyl := fun k =>
    ((isTest_dbar hr k).memLp_wt δ).integrable_sq
  have hsum : ∑ k, ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl ≤
      (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ∫ x, (wt δ x * dbarCyl J r k x) ^ 2 ∂cyl := by
    rw [← integral_finsetSum _ (fun k _ => iR k), ← integral_finsetSum _ (fun k _ => iD k),
      ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun k _ => iR k)
      ((integrable_finsetSum _ fun k _ => iD k).const_mul _) fun x =>
        sum_weight_le (wt δ x) (dbarCyl J r) x
  calc _ ≤ ∑ k, 2 * K * ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl :=
        Finset.sum_le_sum fun k _ => hk k
    _ = 2 * K * ∑ k, ∫ x, wt δ x ^ 2 * (dbarCyl J r k x ^ 2 + jv J (dbarCyl J r) k x ^ 2) ∂cyl := by
        rw [Finset.mul_sum]
    _ ≤ 2 * K * ((1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ∫ x, (wt δ x * dbarCyl J r k x) ^ 2 ∂cyl) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Assembly

/-! ## 6. The weighted spaces `H^{m,δ}` -/

section Spaces

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- **`∂_s + J ∂_t : (H^{m+1,δ})ⁿ → (H^{m,δ})ⁿ`**, `(g_k) ↦ ∂_s g_k + ∑_l J_{kl} ∂_t g_l`. For
`δ = 0` this is `crOp`. -/
def crOpW {n : ℕ} {δ : ℝ} (m : ℕ) (hδ : 0 ≤ δ) (J : Fin n → Fin n → ℝ)
    (g : Fin n → H (m + 1) hδ) (k : Fin n) : H m hδ :=
  dsH m hδ (g k) + ∑ l, J k l • dtH m hδ (g l)

lemma crOpW_zero (m : ℕ) (g : Fin n → H (m + 1) (le_refl (0 : ℝ))) :
    crOpW m (le_refl (0 : ℝ)) J g = crOp m J g := rfl

lemma continuous_crOpW (m : ℕ) (k : Fin n) :
    Continuous fun g : Fin n → H (m + 1) hδ => crOpW m hδ J g k := by
  unfold crOpW; fun_prop

lemma toH_congr {m : ℕ} {φ ψ : ℝ × ℝ → ℝ} (h : φ = ψ) (hφ : IsTest φ) (hψ : IsTest ψ) :
    toH m hδ hφ = toH m hδ hψ := by subst h; rfl

lemma crOpW_toH {m : ℕ} {r : Fin n → ℝ × ℝ → ℝ} (hr : ∀ k, IsTest (r k)) (k : Fin n) :
    crOpW m hδ J (fun l => toH (m + 1) hδ (hr l)) k = toH m hδ (isTest_dbar (J := J) hr k) := by
  apply valCLM_injective (m := m) (hδ := hδ)
  simp only [crOpW, map_add, map_sum, map_smul, dsH_toH, dtH_toH]
  refine Lp.ext ?_
  have hs : ∀ l, (valCLM m hδ (toH m hδ (hr l).dt) : ℝ × ℝ → ℝ) =ᵐ[cyl] Dt (r l) := fun l =>
    val_toH (m := m) (hδ := hδ) (hr l).dt
  filter_upwards [Lp.coeFn_add (valCLM m hδ (toH m hδ (hr k).ds))
      (∑ l, J k l • valCLM m hδ (toH m hδ (hr l).dt)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun l => J k l • valCLM m hδ (toH m hδ (hr l).dt)),
    ae_all_iff.2 fun l => Lp.coeFn_smul (J k l) (valCLM m hδ (toH m hδ (hr l).dt)),
    ae_all_iff.2 hs, val_toH (m := m) (hδ := hδ) (hr k).ds,
    val_toH (m := m) (hδ := hδ) (isTest_dbar (J := J) hr k)] with x h1 h2 h3 h4 h5 h6
  change _ = (H.val (toH m hδ (isTest_dbar (J := J) hr k)) : ℝ × ℝ → ℝ) x
  rw [h1, Pi.add_apply, h2, h6]
  change _ = Ds (r k) x + ∑ l, J k l * Dt (r l) x
  rw [show (valCLM m hδ (toH m hδ (hr k).ds) : ℝ × ℝ → ℝ) x = Ds (r k) x from h5]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h3 l, Pi.smul_apply, smul_eq_mul, h4 l]

lemma nsq_toH (m : ℕ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    ‖wdv (H.toSub (toH m hδ hφ)) (CylinderSobolev.idx0 m)‖ ^ 2 =
      ∫ x, (wt δ x * φ x) ^ 2 ∂cyl := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_wdv (H.toSub (toH m hδ hφ)) (CylinderSobolev.idx0 m),
    dv_idx0 (H.toSub (toH m hδ hφ)), val_toH (m := m) (hδ := hδ) hφ] with x h1 h2 h3
  rw [h1, h2]; change (wt δ x * (H.val (toH m hδ hφ) : ℝ × ℝ → ℝ) x) ^ 2 = _; rw [h3]

/-- The constant of the estimate at level `0`. -/
def gapConst (J : Fin n → Fin n → ℝ) (δ : ℝ) : ℝ :=
  2 * (8 + (1 + 5 * δ ^ 2) / min δ (2 * π - δ) ^ 2) * (1 + ∑ k, ∑ l, J k l ^ 2)

lemma gapConst_nonneg (J : Fin n → Fin n → ℝ) {δ : ℝ} : 0 ≤ gapConst J δ := by
  unfold gapConst; positivity

/-- **The estimate at level `0`**, on `(H^{m+1,δ})ⁿ` for every `m`:
`∑_k ‖e^{δ|s|} g_k‖² + ‖e^{δ|s|} ∂_s g_k‖² + ‖e^{δ|s|} ∂_t g_k‖² ≤
C ∑_k ‖e^{δ|s|} ((∂_s + J ∂_t) g)_k‖²_{L²}`, by density of the test functions. -/
theorem low_estimate (hJ : IsCxMat J) (h0 : 0 < δ) (h1 : δ < 2 * π) (m : ℕ)
    (g : Fin n → H (m + 1) hδ) :
    ∑ k, (‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 (m + 1))‖ ^ 2 +
        ‖wdv (H.toSub (dsH m hδ (g k))) (CylinderSobolev.idx0 m)‖ ^ 2 +
        ‖wdv (H.toSub (dtH m hδ (g k))) (CylinderSobolev.idx0 m)‖ ^ 2) ≤
      gapConst J δ * ∑ k, ‖wdv (H.toSub (crOpW m hδ J g k)) (CylinderSobolev.idx0 m)‖ ^ 2 := by
  set T : Set (H (m + 1) hδ) := {u | ∃ φ, ∃ hφ : IsTest φ, u = toH (m + 1) hδ hφ}
  have hD : Dense (Set.pi Set.univ fun _ : Fin n => T) :=
    dense_pi Set.univ fun k _ => dense_test (m + 1) hδ
  have hC : IsClosed {g : Fin n → H (m + 1) hδ |
      ∑ k, (‖wdvCLM (m + 1) hδ (CylinderSobolev.idx0 (m + 1)) (g k)‖ ^ 2 +
        ‖wdvCLM m hδ (CylinderSobolev.idx0 m) (dsH m hδ (g k))‖ ^ 2 +
        ‖wdvCLM m hδ (CylinderSobolev.idx0 m) (dtH m hδ (g k))‖ ^ 2) ≤
      gapConst J δ * ∑ k, ‖wdvCLM m hδ (CylinderSobolev.idx0 m) (crOpW m hδ J g k)‖ ^ 2} := by
    refine isClosed_le (by fun_prop) ?_
    have := fun k => continuous_crOpW (hδ := hδ) (J := J) m k
    fun_prop
  have hsub := closure_minimal (s := Set.pi Set.univ fun _ : Fin n => T) ?_ hC
  · rw [hD.closure_eq] at hsub
    exact hsub (Set.mem_univ g)
  intro g hg
  simp only [Set.mem_pi, Set.mem_univ, true_implies, T, Set.mem_ofPred_eq] at hg
  choose r hr hgr using hg
  have hg' : g = fun l => toH (m + 1) hδ (hr l) := funext hgr
  subst hg'
  change ∑ k, (‖wdv (H.toSub (toH (m + 1) hδ (hr k))) (CylinderSobolev.idx0 (m + 1))‖ ^ 2 +
        ‖wdv (H.toSub (dsH m hδ (toH (m + 1) hδ (hr k)))) (CylinderSobolev.idx0 m)‖ ^ 2 +
        ‖wdv (H.toSub (dtH m hδ (toH (m + 1) hδ (hr k)))) (CylinderSobolev.idx0 m)‖ ^ 2) ≤
      gapConst J δ * ∑ k, ‖wdv (H.toSub (crOpW m hδ J (fun l => toH (m + 1) hδ (hr l)) k))
        (CylinderSobolev.idx0 m)‖ ^ 2
  simp only [dsH_toH, dtH_toH, crOpW_toH hr, nsq_toH]
  have h := test_estimate hJ hr h0 h1
  rw [← gapConst] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_add, integral_add]
  · exact ((hr k).memLp_wt δ).integrable_sq
  · exact ((hr k).ds.memLp_wt δ).integrable_sq
  · exact ((hr k).memLp_wt δ).integrable_sq.add ((hr k).ds.memLp_wt δ).integrable_sq
  · exact ((hr k).dt.memLp_wt δ).integrable_sq

end Spaces

/-! ## 7. All levels -/

section Levels

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma norm_sq_H0 (v : H 0 hδ) :
    ‖v‖ ^ 2 = ‖wdv (H.toSub v) (CylinderSobolev.idx0 0)‖ ^ 2 := by
  rw [norm_sq_H, Fintype.sum_eq_single (CylinderSobolev.idx0 0) fun p hp => absurd (Subtype.ext (by
    have := mem_idx.1 p.2
    exact Prod.ext (by change p.1.1 = 0; omega) (by change p.1.2 = 0; omega))) hp]

/-- `‖u‖²_{m+1} ≤ ‖e^{δ|s|} u‖²_{L²} + ‖∂_s u‖²_m + ‖∂_t u‖²_m`. -/
lemma norm_sq_le_split {m : ℕ} (u : H (m + 1) hδ) :
    ‖u‖ ^ 2 ≤ ‖wdv (H.toSub u) (CylinderSobolev.idx0 (m + 1))‖ ^ 2 + ‖dsH m hδ u‖ ^ 2 +
      ‖dtH m hδ u‖ ^ 2 := by
  have h := norm_sq_le_shift u
  rw [norm_sq_H (dsH m hδ u), norm_sq_H (dtH m hδ u), add_assoc, ← Finset.sum_add_distrib]
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← wdv_dsH u p, ← wdv_dtH u p]; rfl

lemma dtH_dsH {m : ℕ} (u : H (m + 2) hδ) :
    dtH m hδ (dsH (m + 1) hδ u) = dsH m hδ (dtH (m + 1) hδ u) := by
  have h := Continuous.ext_on (dense_test (m + 2) hδ)
    ((dtH m hδ).comp (dsH (m + 1) hδ)).continuous ((dsH m hδ).comp (dtH (m + 1) hδ)).continuous
    (f := fun u => dtH m hδ (dsH (m + 1) hδ u)) (g := fun u => dsH m hδ (dtH (m + 1) hδ u))
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [dsH_toH, dtH_toH]
      exact toH_congr (Ds_Dt hφ.smooth).symm _ _)
  exact congrFun h u

lemma crOpW_dsH {m : ℕ} (g : Fin n → H (m + 2) hδ) (k : Fin n) :
    crOpW m hδ J (fun l => dsH (m + 1) hδ (g l)) k = dsH m hδ (crOpW (m + 1) hδ J g k) := by
  simp only [crOpW, map_add, map_sum, map_smul, dtH_dsH]

lemma crOpW_dtH {m : ℕ} (g : Fin n → H (m + 2) hδ) (k : Fin n) :
    crOpW m hδ J (fun l => dtH (m + 1) hδ (g l)) k = dtH m hδ (crOpW (m + 1) hδ J g k) := by
  simp only [crOpW, map_add, map_sum, map_smul, dtH_dsH]

lemma sum_sq_wdv_le {m : ℕ} (g : Fin n → H m hδ) :
    ∑ k, ‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 m)‖ ^ 2 ≤ ∑ k, ‖g k‖ ^ 2 :=
  Finset.sum_le_sum fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_wdv_le (g k) (CylinderSobolev.idx0 m)) 2

/-- **The neck estimate, squared form**: for `0 < δ < 2π` and `J² = -1`, every level `m` has a
constant `C` with `∑_k ‖g_k‖²_{H^{m+1,δ}} ≤ C ∑_k ‖((∂_s + J ∂_t) g)_k‖²_{H^{m,δ}}` on
`(H^{m+1,δ}(ℝ × S¹))ⁿ`. There is no lower-order term. -/
theorem neck_estimate_sq (hJ : IsCxMat J) (h0 : 0 < δ) (h1 : δ < 2 * π) :
    ∀ m : ℕ, ∃ C, 0 ≤ C ∧ ∀ g : Fin n → H (m + 1) hδ,
      ∑ k, ‖g k‖ ^ 2 ≤ C * ∑ k, ‖crOpW m hδ J g k‖ ^ 2 := by
  have hC0 := gapConst_nonneg (δ := δ) J
  intro m
  induction m with
  | zero =>
    refine ⟨gapConst J δ, hC0, fun g => ?_⟩
    have hL := low_estimate (hδ := hδ) hJ h0 h1 0 g
    simp only [← norm_sq_H0] at hL
    calc ∑ k, ‖g k‖ ^ 2 ≤ ∑ k, (‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 (0 + 1))‖ ^ 2 +
          ‖dsH 0 hδ (g k)‖ ^ 2 + ‖dtH 0 hδ (g k)‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => norm_sq_le_split (g k)
      _ ≤ _ := hL
      _ = _ := by simp only [norm_sq_H0]
  | succ m ih =>
    obtain ⟨C, hC, hCg⟩ := ih
    refine ⟨gapConst J δ + 2 * C, by positivity, fun g => ?_⟩
    have hL := low_estimate (hδ := hδ) hJ h0 h1 (m + 1) g
    have hA : ∑ k, ‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 (m + 1 + 1))‖ ^ 2 ≤
        gapConst J δ * ∑ k, ‖crOpW (m + 1) hδ J g k‖ ^ 2 := by
      refine le_trans ?_ ((mul_le_mul_of_nonneg_left (sum_sq_wdv_le _) hC0))
      refine le_trans (Finset.sum_le_sum fun k _ => ?_) hL
      have := sq_nonneg ‖wdv (H.toSub (dsH (m + 1) hδ (g k))) (CylinderSobolev.idx0 (m + 1))‖
      have := sq_nonneg ‖wdv (H.toSub (dtH (m + 1) hδ (g k))) (CylinderSobolev.idx0 (m + 1))‖
      linarith
    have hS : ∑ k, ‖dsH (m + 1) hδ (g k)‖ ^ 2 ≤ C * ∑ k, ‖crOpW (m + 1) hδ J g k‖ ^ 2 := by
      refine (hCg fun l => dsH (m + 1) hδ (g l)).trans (mul_le_mul_of_nonneg_left ?_ hC)
      refine Finset.sum_le_sum fun k _ => ?_
      rw [crOpW_dsH]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_dsH_le _) 2
    have hT : ∑ k, ‖dtH (m + 1) hδ (g k)‖ ^ 2 ≤ C * ∑ k, ‖crOpW (m + 1) hδ J g k‖ ^ 2 := by
      refine (hCg fun l => dtH (m + 1) hδ (g l)).trans (mul_le_mul_of_nonneg_left ?_ hC)
      refine Finset.sum_le_sum fun k _ => ?_
      rw [crOpW_dtH]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_dtH_le _) 2
    calc ∑ k, ‖g k‖ ^ 2 ≤ ∑ k, (‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 (m + 1 + 1))‖ ^ 2 +
          ‖dsH (m + 1) hδ (g k)‖ ^ 2 + ‖dtH (m + 1) hδ (g k)‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => norm_sq_le_split (g k)
      _ = ∑ k, ‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 (m + 1 + 1))‖ ^ 2 +
          ∑ k, ‖dsH (m + 1) hδ (g k)‖ ^ 2 + ∑ k, ‖dtH (m + 1) hδ (g k)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ _ := by linarith

/-- **The neck estimate** (design §3a): for `0 < δ < 2π`, a matrix `J` with `J² = -1` and every
level `m`, there is `C` with `‖g_k‖_{H^{m+1,δ}} ≤ C ∑_l ‖((∂_s + J ∂_t) g)_l‖_{H^{m,δ}}` for all
`g ∈ (H^{m+1,δ}(ℝ × S¹))ⁿ`, without a lower-order term. Compare `cyl_estimate` (`δ = 0`), which
needs `‖g‖_{L²}` on the right. -/
theorem neck_estimate (hJ : IsCxMat J) (h0 : 0 < δ) (h1 : δ < 2 * π) (m : ℕ) :
    ∃ C, ∀ (g : Fin n → H (m + 1) hδ) (k : Fin n), ‖g k‖ ≤ C * ∑ l, ‖crOpW m hδ J g l‖ := by
  obtain ⟨C0, hC0, hC⟩ := neck_estimate_sq (hδ := hδ) hJ h0 h1 m
  refine ⟨1 + C0, fun g k => ?_⟩
  set S := ∑ l, ‖crOpW m hδ J g l‖
  have hS : 0 ≤ S := by positivity
  have hb : ∑ l, ‖crOpW m hδ J g l‖ ^ 2 ≤ S ^ 2 :=
    sum_sq_le_sq_sum _ fun _ _ => norm_nonneg _
  have hk : ‖g k‖ ^ 2 ≤ ∑ l, ‖g l‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖g l‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
  have h2 : ‖g k‖ ^ 2 ≤ ((1 + C0) * S) ^ 2 := by
    have := hC g
    nlinarith [mul_le_mul_of_nonneg_left hb hC0, sq_nonneg S, mul_nonneg hC0 (sq_nonneg S)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end Levels

/-! ## 8. The half-cylinder, and the hypotheses are satisfiable -/

section Witness

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- **The half-cylinder case.** For tuples vanishing for `s ≤ 0` the weight `e^{δ|s|}` is
`e^{δs}`, so this is the estimate on `[0, ∞) × S¹` with weight `e^{δs}`, for the `H`-part `r`
of a neck block `(c, r)`; the asymptotic constant `c` has `(∂_s + J ∂_t) c = 0`. It is
`neck_estimate` restricted to these tuples. -/
theorem neck_estimate_half (hJ : IsCxMat J) (h0 : 0 < δ) (h1 : δ < 2 * π) (m : ℕ) :
    ∃ C, ∀ g : Fin n → H (m + 1) hδ,
      (∀ k, ∀ᵐ x ∂cyl, x.1 ≤ 0 → (H.val (g k) : ℝ × ℝ → ℝ) x = 0) →
        ∀ k, ‖g k‖ ≤ C * ∑ l, ‖crOpW m hδ J g l‖ := by
  obtain ⟨C, hC⟩ := neck_estimate (hδ := hδ) hJ h0 h1 m
  exact ⟨C, fun g _ k => hC g k⟩

/-- The standard complex structure `J₀ = [[0, -1], [1, 0]]` on `ℝ²`. -/
def Jstd : Fin 2 → Fin 2 → ℝ := ![![0, -1], ![1, 0]]

lemma isCxMat_Jstd : IsCxMat Jstd := by
  intro k l
  fin_cases k <;> fin_cases l <;> simp [Jstd, Fin.sum_univ_two]

/-- A test function of `s` alone, supported in `(0, 3)` and equal to `1` on `[1, 2]`. -/
lemma exists_test_bump : ∃ φ : ℝ × ℝ → ℝ, IsTest φ ∧ (∀ x : ℝ × ℝ, x.1 ≤ 0 → φ x = 0) ∧
    ∀ x : ℝ × ℝ, x.1 ∈ Icc (1 : ℝ) 2 → φ x = 1 := by
  obtain ⟨χ, hχ, h0, h1, -⟩ := exists_cutoff (a := 0) (c := 1) (d := 2) (b := 3)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨R, hR⟩ := cutoff_bddSupp h0
  refine ⟨fun x => χ x.1, ⟨hχ.comp contDiff_fst, fun _ _ => rfl, ⟨R, fun s _ hs => hR s hs⟩⟩,
    fun x hx => h0 x.1 (Or.inl hx), fun x hx => (h1 x.1 hx).1⟩

lemma toH_ne_zero (m : ℕ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ)
    (h1 : ∀ x : ℝ × ℝ, x.1 ∈ Icc (1 : ℝ) 2 → φ x = 1) : toH m hδ hφ ≠ 0 := by
  intro h
  have hae : φ =ᵐ[cyl] 0 := by
    refine (val_toH (m := m) (hδ := hδ) hφ).symm.trans ?_
    rw [h]; exact Lp.coeFn_zero ℝ 2 cyl
  have hsub : Icc (1 : ℝ) 2 ×ˢ (univ : Set ℝ) ⊆ {x | ¬ φ x = (0 : ℝ × ℝ → ℝ) x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, h1 x hx.1]
    exact one_ne_zero
  have h0 := measure_mono_null hsub (ae_iff.1 hae)
  rw [cyl_slab] at h0
  norm_num at h0

/-- **The hypotheses are satisfiable**: `δ = π` lies in `(0, 2π)`, `J₀` has `J₀² = -1`, and there
is a nonzero pair in `(H^{m+1,π})²` vanishing for `s ≤ 0`. -/
theorem neck_hyps_witness (m : ℕ) :
    IsCxMat Jstd ∧ 0 < π ∧ π < 2 * π ∧ ∃ g : Fin 2 → H (m + 1) Real.pi_pos.le, g ≠ 0 ∧
      ∀ k, ∀ᵐ x ∂cyl, x.1 ≤ 0 → (H.val (g k) : ℝ × ℝ → ℝ) x = 0 := by
  obtain ⟨φ, hφ, hneg, hone⟩ := exists_test_bump
  refine ⟨isCxMat_Jstd, Real.pi_pos, by linarith [Real.pi_pos],
    fun _ => toH (m + 1) Real.pi_pos.le hφ, fun h => ?_, fun _ => ?_⟩
  · exact toH_ne_zero (m + 1) hφ hone (congrFun h 0)
  · filter_upwards [val_toH (m := m + 1) (hδ := Real.pi_pos.le) hφ] with x hx hx0
    rw [hx, hneg x hx0]

/-- **The instance `δ = π`, `J = J₀`** of `neck_estimate_half` (hence of `neck_estimate`). -/
theorem neck_estimate_pi (m : ℕ) :
    ∃ C, ∀ g : Fin 2 → H (m + 1) Real.pi_pos.le,
      (∀ k, ∀ᵐ x ∂cyl, x.1 ≤ 0 → (H.val (g k) : ℝ × ℝ → ℝ) x = 0) →
        ∀ k, ‖g k‖ ≤ C * ∑ l, ‖crOpW m Real.pi_pos.le Jstd g l‖ :=
  neck_estimate_half isCxMat_Jstd Real.pi_pos (by linarith [Real.pi_pos]) m

end Witness

end GWMemoir
