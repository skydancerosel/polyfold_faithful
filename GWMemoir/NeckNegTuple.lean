import GWMemoir.NeckNegTests

/-!
# The model with growth on `ℝ × S¹`: the mode `0` and test tuples

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Proposition 4.16 (p. 110).
Continuation of `NeckNegTests`, with `L v = (∂_s + J ∂_t) v + a(s) v`.

* `mode0_bound`: the mode `0`, a one-dimensional estimate
  `∫ F² + F'² ≤ C₁ F(0)² + C₂ ∫ (F' + a F)²`, from `(F²)' = 2 F G - 2 a F²` on each half-line.
* `tuple_perp`: mean-zero tuples.
* **`exists_test_estimate_neg`**: `∑_k ‖v_k‖²_{H¹} ≤ C (∑_k ‖(L v)_k‖² + ∑_k [v_k]_0²)` for test
  tuples and `0 < δ < π`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped ContDiff Topology Real
open Set Function Filter MeasureTheory Complex
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir.NeckNeg

/-! ## 4. The mode `0` -/

section Mode0

/-- The constants of `mode0_bound`. -/
def m0C1 (δ : ℝ) : ℝ := (1 + 2 * δ ^ 2) * (2 * (1 / δ + 2))

/-- The constants of `mode0_bound`. -/
def m0C2 (δ : ℝ) : ℝ := (1 + 2 * δ ^ 2) * (4 * (1 / (2 * δ) + 2) ^ 2) + 2

lemma m0C1_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ m0C1 δ := by unfold m0C1; positivity

lemma m0C2_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ m0C2 δ := by unfold m0C2; positivity

lemma iint_eq_int {f : ℝ → ℝ} {R T : ℝ} (hRT : R < T) (hf : ∀ s, R < |s| → f s = 0) :
    ∫ s in (-T)..T, f s = ∫ s, f s := by
  refine intervalIntegral.integral_eq_integral_of_support_subset fun s hs => ?_
  by_contra h
  apply hs
  refine hf s ?_
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at h
  rcases h with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs s)
  · exact lt_of_lt_of_le (by linarith) (le_abs_self s)

lemma integrable_of_vanish {f : ℝ → ℝ} {R : ℝ} (hf : Continuous f)
    (hz : ∀ s, R < |s| → f s = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
    fun s hs => hz s (by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs s)
      · exact lt_of_lt_of_le h (le_abs_self s)))

/-- **The mode `0`**: for `F` vanishing for `|s| > R`, `G = F' + a F`, with `a ≥ 0` on `s ≥ 0`,
`a ≤ 0` on `s ≤ 0`, `|a| ≤ δ` and `|a| ≥ δ` for `|s| ≥ 1`,
`∫ F² + F'² ≤ C₁ F(0)² + C₂ ∫ G²`. From `(F²)' = 2FG - 2aF²`: on each half-line
`F(s)² ≤ F(0)² + ∫ (ηF² + G²/η)`, and `∫ 2|a| F² ≤ 2F(0)² + ∫ (ηF² + G²/η)`. -/
theorem mode0_bound {a : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (ha : Continuous a)
    (hpos : ∀ s, 0 ≤ s → 0 ≤ a s) (hneg : ∀ s, s ≤ 0 → a s ≤ 0) (hle : ∀ s, |a s| ≤ δ)
    (hge : ∀ s, 1 ≤ |s| → δ ≤ |a s|) {F F' : ℝ → ℝ} {R : ℝ} (hF : ∀ s, HasDerivAt F (F' s) s)
    (hF' : Continuous F') (hFz : ∀ s, R < |s| → F s = 0) (hF'z : ∀ s, R < |s| → F' s = 0) :
    ∫ s, (F s ^ 2 + F' s ^ 2) ≤ m0C1 δ * F 0 ^ 2 + m0C2 δ * ∫ s, (F' s + a s * F s) ^ 2 := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun s => (hF s).continuousAt
  set G : ℝ → ℝ := fun s => F' s + a s * F s with hG
  have hGc : Continuous G := by fun_prop
  have hGz : ∀ s, R < |s| → G s = 0 := fun s h => by simp only [G, hFz s h, hF'z s h]; ring
  set c := 1 / (2 * δ) + 2 with hc
  have hc0 : 0 < c := by positivity
  set η := 1 / (2 * c) with hη
  have hη0 : 0 < η := by positivity
  set X : ℝ → ℝ := fun s => η * F s ^ 2 + G s ^ 2 / η with hX
  have hX0 : ∀ s, 0 ≤ X s := fun s => by positivity
  have hXc : Continuous X := by fun_prop
  have hXz : ∀ s, R < |s| → X s = 0 := fun s h => by simp only [X, hFz s h, hGz s h]; ring
  have iX : Integrable X := integrable_of_vanish hXc hXz
  set N := ∫ s, X s with hN
  set T := max R 1 + 1 with hT
  have hRT : R < T := by have := le_max_left R 1; linarith
  have h1T : 1 < T := by have := le_max_right R 1; linarith
  have hFT : F T = 0 := hFz T (by rw [abs_of_pos (by linarith)]; exact hRT)
  have hFmT : F (-T) = 0 := hFz (-T) (by rw [abs_neg, abs_of_pos (by linarith)]; exact hRT)
  have hderiv : ∀ s, HasDerivAt (fun s => F s * F s) (2 * F s * F' s) s := fun s =>
    ((hF s).mul (hF s)).congr_deriv (by ring)
  have hpt : ∀ s, 2 * F s * F' s = 2 * F s * G s - 2 * a s * (F s * F s) := fun s => by
    simp only [G]; ring
  have hup : ∀ s, 2 * F s * G s ≤ X s := fun s => by
    have e : η * (X s - 2 * F s * G s) = (η * F s - G s) ^ 2 := by
      simp only [X]; field_simp; ring
    have h2 : 0 ≤ X s - 2 * F s * G s :=
      (mul_nonneg_iff_of_pos_left hη0).1 (e ▸ sq_nonneg _)
    linarith
  have hlo : ∀ s, -X s ≤ 2 * F s * G s := fun s => by
    have e : η * (X s + 2 * F s * G s) = (η * F s + G s) ^ 2 := by
      simp only [X]; field_simp; ring
    have h2 : 0 ≤ X s + 2 * F s * G s :=
      (mul_nonneg_iff_of_pos_left hη0).1 (e ▸ sq_nonneg _)
    linarith
  have cD : Continuous fun s => 2 * F s * F' s := by fun_prop
  have cXn : Continuous fun s => -X s := by fun_prop
  have cFG : Continuous fun s => 2 * F s * G s := by fun_prop
  have cAF : Continuous fun s => 2 * a s * (F s * F s) := by fun_prop
  have hXle : ∀ u v, u ≤ v → ∫ s in u..v, X s ≤ N := fun u v huv => by
    rw [intervalIntegral.integral_of_le huv]; exact setIntegral_le_integral iX (ae_of_all volume hX0)
  -- the sup bound
  have hsup : ∀ s, F s ^ 2 ≤ F 0 ^ 2 + N := by
    intro s
    rcases le_total 0 s with hs | hs
    · have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
        (cD.intervalIntegrable (μ := volume) 0 s)
      have m := intervalIntegral.integral_mono_on hs (cD.intervalIntegrable (μ := volume) 0 s)
        (hXc.intervalIntegrable (μ := volume) 0 s) fun x hx => by
          rw [hpt]
          have := hpos x hx.1
          have := mul_nonneg (mul_nonneg zero_le_two this) (mul_self_nonneg (F x))
          linarith [hup x]
      have := hXle 0 s hs
      rw [sq, sq]; linarith
    · have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
        (cD.intervalIntegrable (μ := volume) s 0)
      have m := intervalIntegral.integral_mono_on hs (cXn.intervalIntegrable (μ := volume) s 0)
        (cD.intervalIntegrable (μ := volume) s 0) fun x hx => by
          rw [hpt]
          have := hneg x hx.2
          nlinarith [hlo x, mul_self_nonneg (F x)]
      rw [intervalIntegral.integral_neg] at m
      have := hXle s 0 hs
      rw [sq, sq]; linarith
  -- the weighted identity
  have cQ : Continuous fun s => 2 * |a s| * (F s * F s) := by fun_prop
  have hQ : ∫ s, 2 * |a s| * (F s * F s) ≤ 2 * F 0 ^ 2 + N := by
    rw [← iint_eq_int hRT (fun s h => by simp [hFz s h]),
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (cQ.intervalIntegrable (μ := volume) _ _)
        (cQ.intervalIntegrable (μ := volume) _ _)]
    have eP : ∫ s in (0 : ℝ)..T, 2 * |a s| * (F s * F s) =
        ∫ s in (0 : ℝ)..T, 2 * a s * (F s * F s) :=
      intervalIntegral.integral_congr fun s hs => by
        rw [uIcc_of_le (by linarith)] at hs
        rw [abs_of_nonneg (hpos s hs.1)]
    have eN : ∫ s in (-T)..0, 2 * |a s| * (F s * F s) =
        -∫ s in (-T)..0, 2 * a s * (F s * F s) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun s hs => by
        rw [uIcc_of_le (by linarith)] at hs
        rw [abs_of_nonpos (hneg s hs.2)]; ring
    have fP := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (cD.intervalIntegrable (μ := volume) 0 T)
    have fN := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (cD.intervalIntegrable (μ := volume) (-T) 0)
    simp only [hFT, hFmT] at fP fN
    have sP : ∫ s in (0 : ℝ)..T, 2 * F s * F' s = (∫ s in (0 : ℝ)..T, 2 * F s * G s) -
        ∫ s in (0 : ℝ)..T, 2 * a s * (F s * F s) := by
      exact (intervalIntegral.integral_congr fun s _ => hpt s).trans
        (intervalIntegral.integral_sub (cFG.intervalIntegrable (μ := volume) 0 T)
          (cAF.intervalIntegrable (μ := volume) 0 T))
    have sN : ∫ s in (-T)..0, 2 * F s * F' s = (∫ s in (-T)..0, 2 * F s * G s) -
        ∫ s in (-T)..0, 2 * a s * (F s * F s) := by
      exact (intervalIntegral.integral_congr fun s _ => hpt s).trans
        (intervalIntegral.integral_sub (cFG.intervalIntegrable (μ := volume) (-T) 0)
          (cAF.intervalIntegrable (μ := volume) (-T) 0))
    have mP : ∫ s in (0 : ℝ)..T, 2 * F s * G s ≤ ∫ s in (0 : ℝ)..T, X s :=
      intervalIntegral.integral_mono_on (by linarith) (cFG.intervalIntegrable (μ := volume) _ _)
        (hXc.intervalIntegrable (μ := volume) _ _) fun s _ => hup s
    have mN : ∫ s in (-T)..0, -X s ≤ ∫ s in (-T)..0, 2 * F s * G s :=
      intervalIntegral.integral_mono_on (by linarith) (cXn.intervalIntegrable (μ := volume) _ _)
        (cFG.intervalIntegrable (μ := volume) _ _) fun s _ => hlo s
    rw [intervalIntegral.integral_neg] at mN
    have hsum : (∫ s in (-T)..0, X s) + ∫ s in (0 : ℝ)..T, X s = N := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hXc.intervalIntegrable (μ := volume) _ _) (hXc.intervalIntegrable (μ := volume) _ _)).trans
        (iint_eq_int hRT hXz)
    rw [eP, eN, sq]
    linarith
  -- the integral of `F²`
  have cF2 : Continuous fun s => F s ^ 2 := by fun_prop
  have iF2 : Integrable fun s => F s ^ 2 := integrable_of_vanish (R := R) cF2 (fun s h => by simp [hFz s h])
  have iQ : Integrable fun s => 2 * |a s| * (F s * F s) :=
    integrable_of_vanish (R := R) cQ (fun s h => by simp [hFz s h])
  set M := F 0 ^ 2 + N with hM
  have iI : Integrable ((Icc (-1 : ℝ) 1).indicator fun _ => M) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hI : ∫ s, (Icc (-1 : ℝ) 1).indicator (fun _ => M) s = 2 * M := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp [Measure.real, Real.volume_Icc]; norm_num
  have hA : δ * ∫ s, F s ^ 2 ≤ (1 / 2) * (∫ s, 2 * |a s| * (F s * F s)) + δ * (2 * M) := by
    have k : Integrable fun s => 1 / 2 * (2 * |a s| * (F s * F s)) +
        δ * (Icc (-1 : ℝ) 1).indicator (fun _ => M) s := (iQ.const_mul _).add (iI.const_mul _)
    have := integral_mono (iF2.const_mul δ) k fun s => by
      simp only
      by_cases hs : s ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hs]
        have := hsup s
        have : 0 ≤ 1 / 2 * (2 * |a s| * (F s * F s)) := mul_nonneg (by norm_num)
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg _)) (mul_self_nonneg _))
        nlinarith
      · rw [indicator_of_notMem hs]
        have h1 : 1 ≤ |s| := by
          simp only [mem_Icc, not_and_or, not_le] at hs
          rcases hs with h | h
          · exact le_trans (by linarith) (neg_le_abs s)
          · exact le_trans h.le (le_abs_self s)
        have := hge s h1
        nlinarith [sq_nonneg (F s), mul_self_nonneg (F s)]
    rw [integral_add (iQ.const_mul _) (iI.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, hI] at this
    exact this
  have cG2 : Continuous fun s => G s ^ 2 := by fun_prop
  have iG2 : Integrable fun s => G s ^ 2 := integrable_of_vanish (R := R) cG2 (fun s h => by simp [hGz s h])
  have hNe : N = η * (∫ s, F s ^ 2) + (∫ s, G s ^ 2) / η := by
    rw [hN]
    simp only [X]
    rw [integral_add (iF2.const_mul η) (iG2.div_const η), integral_const_mul, integral_div]
  set A := ∫ s, F s ^ 2 with hAd
  set B := ∫ s, G s ^ 2 with hBd
  set Q := ∫ s, 2 * |a s| * (F s * F s) with hQd
  have hA2 : δ * A ≤ δ * ((1 / δ + 2) * F 0 ^ 2 + c * N) := by
    have e : δ * ((1 / δ + 2) * F 0 ^ 2 + c * N) =
        F 0 ^ 2 + 2 * δ * F 0 ^ 2 + N / 2 + 2 * δ * N := by
      rw [hc]; field_simp; ring
    rw [e]; linarith
  have hA3 : A ≤ (1 / δ + 2) * F 0 ^ 2 + c * N := le_of_mul_le_mul_left hA2 hδ
  have hcN : c * N = A / 2 + 2 * c ^ 2 * B := by
    rw [hNe, hη]; field_simp
  have hA4 : A ≤ 2 * (1 / δ + 2) * F 0 ^ 2 + 4 * c ^ 2 * B := by linarith
  -- the derivative
  have cF'2 : Continuous fun s => F' s ^ 2 := by fun_prop
  have iF'2 : Integrable fun s => F' s ^ 2 :=
    integrable_of_vanish (R := R) cF'2 (fun s h => by simp [hF'z s h])
  have hD : ∫ s, F' s ^ 2 ≤ 2 * B + 2 * δ ^ 2 * A := by
    have k : Integrable fun s => 2 * G s ^ 2 + 2 * δ ^ 2 * F s ^ 2 :=
      (iG2.const_mul 2).add (iF2.const_mul _)
    have := integral_mono iF'2 k fun s => by
      simp only
      have ha2 : a s ^ 2 ≤ δ ^ 2 := sq_le_sq' (abs_le.1 (hle s)).1 (abs_le.1 (hle s)).2
      have e : F' s = G s - a s * F s := by simp only [G]; ring
      rw [e]
      nlinarith [sq_nonneg (G s + a s * F s), mul_le_mul_of_nonneg_right ha2 (sq_nonneg (F s))]
    rw [integral_add (iG2.const_mul 2) (iF2.const_mul _), integral_const_mul,
      integral_const_mul] at this
    exact this
  rw [integral_add iF2 iF'2]
  have hm : 0 ≤ 1 + 2 * δ ^ 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hA4 hm
  have hc' : 1 / (2 * δ) + 2 = c := hc.symm
  simp only [m0C1, m0C2, hc']
  linear_combination h5 + hD

end Mode0

/-! ## 5. Test tuples -/

section Assembly

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {a : ℝ → ℝ} {δ : ℝ}

/-- `L r = (∂_s + J ∂_t) r + a(s) r`. -/
def negL (J : Fin n → Fin n → ℝ) (a : ℝ → ℝ) (r : Fin n → ℝ × ℝ → ℝ) (k : Fin n) :
    ℝ × ℝ → ℝ :=
  fun x => dbarCyl J r k x + a x.1 * r k x

lemma isTest_negL (ha : ContDiff ℝ ∞ a) {r : Fin n → ℝ × ℝ → ℝ} (hr : ∀ k, IsTest (r k))
    (k : Fin n) : IsTest (negL J a r k) :=
  (isTest_dbar hr k).add ((hr k).mul_s ha)

lemma jv_negL (r : Fin n → ℝ × ℝ → ℝ) (k : Fin n) (x : ℝ × ℝ) :
    jv J (negL J a r) k x = jv J (dbarCyl J r) k x + a x.1 * jv J r k x := by
  simp only [jv, negL, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

lemma cmean_negL (ha : ContDiff ℝ ∞ a) {r : Fin n → ℝ × ℝ → ℝ} (hr : ∀ k, IsTest (r k))
    (k : Fin n) (s : ℝ) :
    cmean (negL J a r k) s = cmean (Ds (r k)) s + a s * cmean (r k) s := by
  have h1 : IsTest fun x => Ds (r k) x + jv J (fun l => Dt (r l)) k x :=
    (hr k).ds.add (isTest_jv (fun l => (hr l).dt) k)
  have e : negL J a r k = fun x => (Ds (r k) x + jv J (fun l => Dt (r l)) k x) + a x.1 * r k x :=
    rfl
  rw [e, cmean_add (φ := fun x => Ds (r k) x + jv J (fun l => Dt (r l)) k x)
      (ψ := fun x => a x.1 * r k x) h1 ((hr k).mul_s ha),
    cmean_add (φ := Ds (r k)) (ψ := jv J (fun l => Dt (r l)) k) (hr k).ds
      (isTest_jv (fun l => (hr l).dt) k),
    cmean_jv J (fun l => (hr l).dt), cmean_mul_s]
  simp [cmean_Dt (hr _)]

lemma negL_perp (ha : ContDiff ℝ ∞ a) {v : Fin n → ℝ × ℝ → ℝ} (hv : ∀ k, IsTest (v k))
    (k : Fin n) (x : ℝ × ℝ) :
    negL J a (fun l => perp (v l)) k x = negL J a v k x - cmean (negL J a v k) x.1 := by
  rw [cmean_negL ha hv]
  have hs : ∑ l, J k l * Dt (perp (v l)) x = ∑ l, J k l * Dt (v l) x :=
    Finset.sum_congr rfl fun l _ => by rw [Dt_perp (hv l)]
  simp only [negL, dbarCyl]
  rw [hs, Ds_perp (hv k)]
  simp only [perp]; ring

/-- **Mean-zero tuples**: `∑_k ‖w_k‖²_{H¹} ≤ perpC δ (1 + ∑ J_{kl}²) ∑_k ‖(L w)_k‖²`. -/
theorem tuple_perp (hJ : IsCxMat J) (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ) (hπ : δ < π)
    (hab : ∀ s, |a s| ≤ δ) {w : Fin n → ℝ × ℝ → ℝ} (hw : ∀ k, IsTest (w k))
    (hw0 : ∀ k s, cmean (w k) s = 0) :
    ∑ k, ∫ x, (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) ∂cyl ≤
      perpC δ * (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ∫ x, negL J a w k x ^ 2 ∂cyl := by
  have hk : ∀ k, ∫ x, (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) ∂cyl ≤
      perpC δ * ∫ x, (negL J a w k x ^ 2 + jv J (negL J a w) k x ^ 2) ∂cyl := by
    intro k
    have hg0 : ∀ s, cmean (jv J w k) s = 0 := fun s => by
      rw [cmean_jv J hw]; simp [hw0]
    have h := pair_perp_H1 (hw k) (isTest_jv (J := J) hw k) (hw0 k) hg0 ha hδ hπ hab
    refine h.trans (le_of_eq ?_)
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [dbar_eq hw k x, jdbar_eq hJ hw k x, jv_negL]
    rfl
  have iN : ∀ k, Integrable (fun x => negL J a w k x ^ 2 + jv J (negL J a w) k x ^ 2) cyl :=
    fun k => (tInt_sq (isTest_negL ha hw k)).add (tInt_sq (isTest_jv (isTest_negL ha hw) k))
  have iD : ∀ k, Integrable (fun x => negL J a w k x ^ 2) cyl := fun k =>
    tInt_sq (isTest_negL ha hw k)
  have hsum : ∑ k, ∫ x, (negL J a w k x ^ 2 + jv J (negL J a w) k x ^ 2) ∂cyl ≤
      (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ∫ x, negL J a w k x ^ 2 ∂cyl := by
    rw [← integral_finsetSum _ (fun k _ => iN k), ← integral_finsetSum _ (fun k _ => iD k),
      ← integral_const_mul]
    refine integral_mono (integrable_finsetSum _ fun k _ => iN k)
      ((integrable_finsetSum _ fun k _ => iD k).const_mul _) fun x => ?_
    have := sum_weight_le (J := J) 1 (negL J a w) x
    simpa using this
  have hP := perpC_nonneg hδ hπ
  calc _ ≤ ∑ k, perpC δ * ∫ x, (negL J a w k x ^ 2 + jv J (negL J a w) k x ^ 2) ∂cyl :=
        Finset.sum_le_sum fun k _ => hk k
    _ = perpC δ * ∑ k, ∫ x, (negL J a w k x ^ 2 + jv J (negL J a w) k x ^ 2) ∂cyl := by
        rw [Finset.mul_sum]
    _ ≤ perpC δ * ((1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ∫ x, negL J a w k x ^ 2 ∂cyl) :=
        mul_le_mul_of_nonneg_left hsum hP
    _ = _ := by ring

/-- **The estimate for test tuples**, `0 < δ < π`:
`∑_k ‖v_k‖²_{H¹} ≤ C (∑_k ‖(L v)_k‖² + ∑_k [v_k]_0²)`. The tuple splits into its circle mean
`[v](s)` (`mode0_bound`) and `v - [v]` (`tuple_perp`); `L` commutes with the splitting. -/
theorem exists_test_estimate_neg (hJ : IsCxMat J) (ha : ContDiff ℝ ∞ a) (hδ : 0 < δ)
    (hπ : δ < π) (hpos : ∀ s, 0 ≤ s → 0 ≤ a s) (hneg : ∀ s, s ≤ 0 → a s ≤ 0)
    (hle : ∀ s, |a s| ≤ δ) (hge : ∀ s, 1 ≤ |s| → δ ≤ |a s|) :
    ∃ C, 0 ≤ C ∧ ∀ v : Fin n → ℝ × ℝ → ℝ, (∀ k, IsTest (v k)) →
      ∑ k, ∫ x, (v k x ^ 2 + Ds (v k) x ^ 2 + Dt (v k) x ^ 2) ∂cyl ≤
        C * (∑ k, ∫ x, negL J a v k x ^ 2 ∂cyl + ∑ k, cmean (v k) 0 ^ 2) := by
  have hP := perpC_nonneg hδ hπ
  have hJ0 : 0 ≤ 1 + ∑ k, ∑ l, J k l ^ 2 := by positivity
  refine ⟨8 * (perpC δ * (1 + ∑ k, ∑ l, J k l ^ 2)) + 2 * m0C1 δ + 2 * m0C2 δ,
    by have := m0C1_nonneg hδ; have := m0C2_nonneg hδ; positivity, fun v hv => ?_⟩
  set w : Fin n → ℝ × ℝ → ℝ := fun l => perp (v l) with hwd
  have hw : ∀ k, IsTest (w k) := fun k => isTest_perp (hv k)
  have hw0 : ∀ k s, cmean (w k) s = 0 := fun k s => cmean_perp (hv k) s
  set Nk : Fin n → ℝ := fun k => ∫ x, negL J a v k x ^ 2 ∂cyl with hNk
  -- the mean-zero part
  have hL : ∀ k, ∫ x, negL J a w k x ^ 2 ∂cyl ≤ 4 * Nk k := by
    intro k
    have iv := tInt_sq (isTest_negL (J := J) ha hv k)
    have im := tInt_sq (isTest_cmean (isTest_negL (J := J) ha hv k))
    have hc := integral_sq_cmean_le (isTest_negL (J := J) ha hv k)
    have k2 : Integrable (fun x => 2 * negL J a v k x ^ 2 + 2 * cmean (negL J a v k) x.1 ^ 2) cyl :=
      (iv.const_mul 2).add (im.const_mul 2)
    have := integral_mono (tInt_sq (isTest_negL (J := J) ha hw k)) k2 fun x => by
        simp only
        rw [negL_perp ha hv k x]
        nlinarith [sq_nonneg (negL J a v k x + cmean (negL J a v k) x.1)]
    rw [integral_add (iv.const_mul 2) (im.const_mul 2), integral_const_mul,
      integral_const_mul] at this
    simp only [Nk]
    linarith
  have hPsum := tuple_perp hJ ha hδ hπ hle hw hw0
  have hPsum' : ∑ k, ∫ x, (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) ∂cyl ≤
      perpC δ * (1 + ∑ k, ∑ l, J k l ^ 2) * (4 * ∑ k, Nk k) := by
    refine hPsum.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hP hJ0))
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hL k
  -- the mode `0`
  have hM : ∀ k, ∫ x, (cmean (v k) x.1 ^ 2 + cmean (Ds (v k)) x.1 ^ 2) ∂cyl ≤
      m0C1 δ * cmean (v k) 0 ^ 2 + m0C2 δ * Nk k := by
    intro k
    obtain ⟨R1, hR1⟩ := cmean_eq_zero (hv k)
    obtain ⟨R2, hR2⟩ := cmean_eq_zero (hv k).ds
    have hb := mode0_bound hδ ha.continuous hpos hneg hle hge (F := cmean (v k))
      (F' := cmean (Ds (v k))) (R := max R1 R2) (hasDerivAt_cmean (hv k))
      (contDiff_cmean (hv k).ds).continuous
      (fun s h => hR1 s (lt_of_le_of_lt (le_max_left _ _) h))
      (fun s h => hR2 s (lt_of_le_of_lt (le_max_right _ _) h))
    rw [integral_cyl_fst (fun s => cmean (v k) s ^ 2 + cmean (Ds (v k)) s ^ 2)]
    refine hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (m0C2_nonneg hδ)))
    have e : ∫ s, (cmean (Ds (v k)) s + a s * cmean (v k) s) ^ 2 =
        ∫ x, cmean (negL J a v k) x.1 ^ 2 ∂cyl := by
      rw [integral_cyl_fst (fun s => cmean (negL J a v k) s ^ 2)]
      exact integral_congr_ae (ae_of_all _ fun s => by simp only [cmean_negL ha hv])
    rw [e]
    exact integral_sq_cmean_le (isTest_negL ha hv k)
  -- the splitting
  have hsplit : ∀ k, ∫ x, (v k x ^ 2 + Ds (v k) x ^ 2 + Dt (v k) x ^ 2) ∂cyl ≤
      2 * ∫ x, (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) ∂cyl +
        2 * ∫ x, (cmean (v k) x.1 ^ 2 + cmean (Ds (v k)) x.1 ^ 2) ∂cyl := by
    intro k
    have iL : Integrable (fun x => v k x ^ 2 + Ds (v k) x ^ 2 + Dt (v k) x ^ 2) cyl :=
      ((tInt_sq (hv k)).add (tInt_sq (hv k).ds)).add (tInt_sq (hv k).dt)
    have iW : Integrable (fun x => w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) cyl :=
      ((tInt_sq (hw k)).add (tInt_sq (hw k).ds)).add (tInt_sq (hw k).dt)
    have iF : Integrable (fun x => cmean (v k) x.1 ^ 2 + cmean (Ds (v k)) x.1 ^ 2) cyl :=
      (tInt_sq (isTest_cmean (hv k))).add (tInt_sq (isTest_cmean (hv k).ds))
    have k2 : Integrable (fun x => 2 * (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) +
        2 * (cmean (v k) x.1 ^ 2 + cmean (Ds (v k)) x.1 ^ 2)) cyl :=
      (iW.const_mul 2).add (iF.const_mul 2)
    have := integral_mono iL k2 fun x => by
      simp only [w, Ds_perp (hv k), Dt_perp (hv k), perp]
      nlinarith [sq_nonneg (v k x - 2 * cmean (v k) x.1),
        sq_nonneg (Ds (v k) x - 2 * cmean (Ds (v k)) x.1)]
    rwa [integral_add (iW.const_mul 2) (iF.const_mul 2), integral_const_mul,
      integral_const_mul] at this
  have hm1 := m0C1_nonneg hδ
  have hm2 := m0C2_nonneg hδ
  calc ∑ k, ∫ x, (v k x ^ 2 + Ds (v k) x ^ 2 + Dt (v k) x ^ 2) ∂cyl
      ≤ ∑ k, (2 * ∫ x, (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) ∂cyl +
          2 * (m0C1 δ * cmean (v k) 0 ^ 2 + m0C2 δ * Nk k)) :=
        Finset.sum_le_sum fun k _ => (hsplit k).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hM k) zero_le_two))
    _ = 2 * ∑ k, ∫ x, (w k x ^ 2 + Ds (w k) x ^ 2 + Dt (w k) x ^ 2) ∂cyl +
          2 * m0C1 δ * ∑ k, cmean (v k) 0 ^ 2 + 2 * m0C2 δ * ∑ k, Nk k := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 2 * (perpC δ * (1 + ∑ k, ∑ l, J k l ^ 2) * (4 * ∑ k, Nk k)) +
          2 * m0C1 δ * ∑ k, cmean (v k) 0 ^ 2 + 2 * m0C2 δ * ∑ k, Nk k := by
        linarith
    _ ≤ _ := by
        have hN0 : 0 ≤ ∑ k, Nk k := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
        have hF0 : 0 ≤ ∑ k, cmean (v k) 0 ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
        simp only [Nk] at hN0 ⊢
        nlinarith [mul_nonneg (mul_nonneg hP hJ0) hF0, mul_nonneg hm1 hN0, mul_nonneg hm2 hF0]

end Assembly

end GWMemoir.NeckNeg
