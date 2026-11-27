import GWMemoir.NeckNegTuple

/-!
# The model with growth on `ℝ × S¹`: the functions of `s`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Proposition 4.16 (p. 110).
For a cut-off `β` (`IsCutoff`) and `δ > 0`:

* `negA δ β = δ (1 - 2β)`: `|a| ≤ δ`, `a = ±δ` for `±s ≥ 1`, `a ≥ 0` for `s ≥ 0`, `a ≤ 0` for
  `s ≤ 0` (`β` is antitone, `cut_antitone`), `a(0) = 0`;
* `negH β = ∫₀^s (1 - 2β)`, so `h(s) = |s| + const` for `|s| ≥ 1`;
* `negPsi δ β = e^{-δ h}`: `ψ' = -a ψ`, `ψ(0) = 1`, and `|ψ^{(i)}(s)| ≤ M_i e^{-δ|s|}`, so `ψ`
  and `ψ'` are multipliers and `ψ(s)` lies in `H^m(ℝ × S¹)` for every `m`.

`u = e^{δh} v` identifies the spaces `H^{m,-δ}` with `H^m`, `e^{-δ|s|}` and `e^{-δh}` being
comparable.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped ContDiff Topology Real
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev GWMemoir.Neck

noncomputable section

namespace GWMemoir.NeckNeg

variable {β : ℝ → ℝ} {δ : ℝ}

/-! ## 1. The cut-off is antitone -/

lemma cut_deriv_nonpos (hβ : IsCutoff β) (s : ℝ) : deriv β s ≤ 0 := by
  by_cases h : s ∈ Ioo (-1 : ℝ) 1
  · exact (hβ.deriv_neg s h).le
  · simp only [mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · have hm : IsLocalMax β s := Eventually.of_forall fun y => by
        rw [hβ.one_of_le s h]; exact (hβ.mem y).2
      rw [hm.deriv_eq_zero]
    · have hm : IsLocalMin β s := Eventually.of_forall fun y => by
        rw [hβ.zero_of_ge h]; exact (hβ.mem y).1
      rw [hm.deriv_eq_zero]

lemma cut_antitone (hβ : IsCutoff β) : Antitone β :=
  antitone_of_deriv_nonpos (hβ.smooth.differentiable (by simp)) (cut_deriv_nonpos hβ)

lemma cut_le_half (hβ : IsCutoff β) {s : ℝ} (hs : 0 ≤ s) : β s ≤ 1 / 2 := by
  have := cut_antitone hβ hs; rwa [hβ.half] at this

lemma half_le_cut (hβ : IsCutoff β) {s : ℝ} (hs : s ≤ 0) : 1 / 2 ≤ β s := by
  have := cut_antitone hβ hs; rwa [hβ.half] at this

/-! ## 2. Multipliers vanishing for large `|s|` -/

lemma deriv_eq_zero_of_vanish {χ : ℝ → ℝ} {R : ℝ} (hz : ∀ s, R < |s| → χ s = 0) {s : ℝ}
    (hs : R < |s|) : deriv χ s = 0 := by
  have hO : IsOpen {y : ℝ | R < |y|} := isOpen_lt continuous_const continuous_abs
  have : χ =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [hO.mem_nhds hs] with y hy using hz y hy
  rw [this.deriv_eq, deriv_const]

lemma mult_of_vanish {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {R : ℝ}
    (hz : ∀ s, R < |s| → χ s = 0) (m : ℕ) : Mult m χ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hχ.continuous.continuousOn
  have nm : ∀ s, s ∉ Icc (-R) R → R < |s| := fun s hs => by
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with h | h
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs s)
    · exact lt_of_lt_of_le h (le_abs_self s)
  refine mult_of_deriv hχ (C := max C 0) (fun s => ?_) ?_ m
  · by_cases hs : s ∈ Icc (-R) R
    · have := hC s hs; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    · rw [hz s (nm s hs), abs_zero]; exact le_max_right _ _
  · exact HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs =>
      deriv_eq_zero_of_vanish hz (nm s hs)

lemma contDiff_deriv_cut (hβ : IsCutoff β) : ContDiff ℝ ∞ (deriv β) :=
  (contDiff_infty_iff_deriv.1 hβ.smooth).2

lemma mult_cut (hβ : IsCutoff β) (m : ℕ) : Mult m β :=
  mult_of_deriv hβ.smooth (C := 1) (fun s => by
    rw [abs_of_nonneg (hβ.mem s).1]; exact (hβ.mem s).2)
    (HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun s hs =>
      deriv_cut_eq_zero hβ (by
        simp only [mem_Icc, not_and_or, not_le] at hs
        rcases hs with h | h
        · exact le_trans (by linarith) (neg_le_abs s)
        · exact le_trans h.le (le_abs_self s))) m

lemma mult_deriv_cut (hβ : IsCutoff β) (m : ℕ) : Mult m (deriv β) :=
  mult_of_vanish (contDiff_deriv_cut hβ) (R := 2)
    (fun s hs => deriv_cut_eq_zero hβ hs.le) m

/-! ## 3. The weight `a = δ (1 - 2β)` -/

/-- `a(s) = δ (1 - 2β(s))`. -/
def negA (δ : ℝ) (β : ℝ → ℝ) (s : ℝ) : ℝ := δ * (1 - 2 * β s)

lemma contDiff_negA (hβ : IsCutoff β) : ContDiff ℝ ∞ (negA δ β) :=
  contDiff_const.mul (contDiff_const.sub (contDiff_const.mul hβ.smooth))

lemma negA_nonneg (hβ : IsCutoff β) (hδ : 0 ≤ δ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ negA δ β s :=
  mul_nonneg hδ (by linarith [cut_le_half hβ hs])

lemma negA_nonpos (hβ : IsCutoff β) (hδ : 0 ≤ δ) {s : ℝ} (hs : s ≤ 0) : negA δ β s ≤ 0 := by
  unfold negA; nlinarith [half_le_cut hβ hs]

lemma abs_negA_le (hβ : IsCutoff β) (hδ : 0 ≤ δ) (s : ℝ) : |negA δ β s| ≤ δ := by
  have h1 := hβ.mem s
  unfold negA
  rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2]

lemma le_abs_negA (hβ : IsCutoff β) (hδ : 0 ≤ δ) {s : ℝ} (hs : 1 ≤ |s|) : δ ≤ |negA δ β s| := by
  rcases le_abs'.1 hs with h | h
  · rw [negA, hβ.one_of_le s h, show δ * (1 - 2 * 1) = -δ by ring, abs_neg]
    exact le_abs_self δ
  · rw [negA, hβ.zero_of_ge h, show δ * (1 - 2 * 0) = δ by ring]
    exact le_abs_self δ

lemma negA_zero (hβ : IsCutoff β) : negA δ β 0 = 0 := by
  rw [negA, hβ.half]; ring

lemma hasDerivAt_negA (hβ : IsCutoff β) (s : ℝ) :
    HasDerivAt (negA δ β) (-(2 * δ) * deriv β s) s := by
  have hd : HasDerivAt β (deriv β s) s :=
    ((hβ.smooth.differentiable (by simp)) s).hasDerivAt
  exact (((hasDerivAt_const s (1 : ℝ)).sub (hd.const_mul 2)).const_mul δ).congr_deriv (by ring)

lemma deriv_negA (hβ : IsCutoff β) : deriv (negA δ β) = fun s => -(2 * δ) * deriv β s :=
  funext fun s => (hasDerivAt_negA hβ s).deriv

lemma mult_negA (hβ : IsCutoff β) (hδ : 0 ≤ δ) (m : ℕ) : Mult m (negA δ β) :=
  mult_of_deriv (contDiff_negA hβ) (abs_negA_le hβ hδ) (by
    rw [deriv_negA hβ]
    exact HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun s hs => by
      rw [deriv_cut_eq_zero hβ (by
        simp only [mem_Icc, not_and_or, not_le] at hs
        rcases hs with h | h
        · exact le_trans (by linarith) (neg_le_abs s)
        · exact le_trans h.le (le_abs_self s)), mul_zero]) m

/-! ## 4. `h = ∫₀^s (1 - 2β)` and `ψ = e^{-δ h}` -/

/-- `h(s) = ∫₀^s (1 - 2β)`. -/
def negH (β : ℝ → ℝ) (s : ℝ) : ℝ := ∫ τ in (0 : ℝ)..s, (1 - 2 * β τ)

lemma continuous_one_sub (hβ : IsCutoff β) : Continuous fun τ => 1 - 2 * β τ :=
  continuous_const.sub (continuous_const.mul hβ.smooth.continuous)

lemma hasDerivAt_negH (hβ : IsCutoff β) (s : ℝ) : HasDerivAt (negH β) (1 - 2 * β s) s :=
  ((continuous_one_sub hβ).integral_hasStrictDerivAt 0 s).hasDerivAt

lemma contDiff_negH (hβ : IsCutoff β) : ContDiff ℝ ∞ (negH β) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun s => (hasDerivAt_negH hβ s).differentiableAt, ?_⟩
  have : deriv (negH β) = fun s => 1 - 2 * β s := funext fun s => (hasDerivAt_negH hβ s).deriv
  rw [this]
  exact contDiff_const.sub (contDiff_const.mul hβ.smooth)

lemma negH_zero : negH β 0 = 0 := by simp [negH]

lemma negH_of_ge (hβ : IsCutoff β) {s : ℝ} (hs : 1 ≤ s) : negH β s = negH β 1 + (s - 1) := by
  unfold negH
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    ((continuous_one_sub hβ).intervalIntegrable _ _) ((continuous_one_sub hβ).intervalIntegrable _ _)]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun τ hτ => by
    rw [uIcc_of_le hs] at hτ
    rw [hβ.zero_of_ge hτ.1]; ring]
  simp

lemma negH_of_le (hβ : IsCutoff β) {s : ℝ} (hs : s ≤ -1) :
    negH β s = negH β (-1) - (s + 1) := by
  unfold negH
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := -1)
    ((continuous_one_sub hβ).intervalIntegrable _ _) ((continuous_one_sub hβ).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := -1) (b := s) (g := fun _ => (-1 : ℝ)) fun τ hτ => by
    rw [uIcc_of_ge hs] at hτ
    rw [hβ.one_of_le τ hτ.2]; ring]
  simp; ring

/-- `ψ(s) = e^{-δ h(s)}`. -/
def negPsi (δ : ℝ) (β : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-(δ * negH β s))

lemma contDiff_negPsi (hβ : IsCutoff β) : ContDiff ℝ ∞ (negPsi δ β) :=
  Real.contDiff_exp.comp ((contDiff_const.mul (contDiff_negH hβ)).neg)

lemma negPsi_zero : negPsi δ β 0 = 1 := by simp [negPsi, negH_zero]

lemma negPsi_pos (s : ℝ) : 0 < negPsi δ β s := Real.exp_pos _

lemma hasDerivAt_negPsi (hβ : IsCutoff β) (s : ℝ) :
    HasDerivAt (negPsi δ β) (-(negA δ β s) * negPsi δ β s) s :=
  (((hasDerivAt_negH hβ s).const_mul δ).neg.exp).congr_deriv (by simp only [negA, negPsi, Pi.neg_apply]; ring)

lemma deriv_negPsi (hβ : IsCutoff β) :
    deriv (negPsi δ β) = fun s => -(negA δ β s) * negPsi δ β s :=
  funext fun s => (hasDerivAt_negPsi hβ s).deriv

/-- The tails of `ψ`: `ψ = K₊ e^{-δs}` for `s ≥ 1`, `ψ = K₋ e^{δs}` for `s ≤ -1`. -/
lemma negPsi_of_ge (hβ : IsCutoff β) {s : ℝ} (hs : 1 ≤ s) :
    negPsi δ β s = Real.exp (-(δ * (negH β 1 - 1))) * Real.exp (-δ * s) := by
  rw [negPsi, negH_of_ge hβ hs, ← Real.exp_add]; ring_nf

lemma negPsi_of_le (hβ : IsCutoff β) {s : ℝ} (hs : s ≤ -1) :
    negPsi δ β s = Real.exp (-(δ * (negH β (-1) - 1))) * Real.exp (δ * s) := by
  rw [negPsi, negH_of_le hβ hs, ← Real.exp_add]; ring_nf

/-- **The derivatives of `ψ` decay like `e^{-δ|s|}`.** -/
theorem negPsi_deriv_bound (hβ : IsCutoff β) (hδ : 0 ≤ δ) (i : ℕ) :
    ∃ M, 0 ≤ M ∧ ∀ s, |iteratedDeriv i (negPsi δ β) s| ≤ M * Real.exp (-δ * |s|) := by
  have hc := (contDiff_negPsi (δ := δ) hβ).continuous_iteratedDeriv i (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  set Kp := Real.exp (-(δ * (negH β 1 - 1)))
  set Km := Real.exp (-(δ * (negH β (-1) - 1)))
  refine ⟨Kp * δ ^ i + Km * δ ^ i + max B 0 * Real.exp δ, by positivity, fun s => ?_⟩
  have hE : 0 ≤ Real.exp (-δ * |s|) := (Real.exp_pos _).le
  have hKp : 0 ≤ Kp * δ ^ i := by positivity
  have hKm : 0 ≤ Km * δ ^ i := by positivity
  have hBe : 0 ≤ max B 0 * Real.exp δ * Real.exp (-δ * |s|) := by positivity
  rcases lt_or_ge 1 s with h1 | h1
  · have hev : negPsi δ β =ᶠ[𝓝 s] Kp • fun y => Real.exp (-δ * y) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      rw [negPsi_of_ge hβ (le_of_lt hy)]; rfl
    rw [(hev.iteratedDeriv i).eq_of_nhds, iteratedDeriv_const_smul_field,
      iteratedDeriv_exp_const_mul, smul_eq_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
    have : |Kp * ((-δ) ^ i * Real.exp (-δ * s))| = Kp * δ ^ i * Real.exp (-δ * s) := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hδ, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _)]; ring
    rw [this]
    have h3 : 0 ≤ (Km * δ ^ i + max B 0 * Real.exp δ) * Real.exp (-δ * s) := by positivity
    linear_combination h3
  rcases lt_or_ge s (-1) with h2 | h2
  · have hev : negPsi δ β =ᶠ[𝓝 s] Km • fun y => Real.exp (δ * y) := by
      filter_upwards [Iio_mem_nhds h2] with y hy
      rw [negPsi_of_le hβ (le_of_lt hy)]; rfl
    rw [(hev.iteratedDeriv i).eq_of_nhds, iteratedDeriv_const_smul_field,
      iteratedDeriv_exp_const_mul, smul_eq_mul, abs_of_neg (by linarith : s < 0)]
    have : |Km * (δ ^ i * Real.exp (δ * s))| = Km * δ ^ i * Real.exp (-δ * -s) := by
      rw [show -δ * -s = δ * s by ring, abs_mul, abs_mul, abs_pow, abs_of_nonneg hδ,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]; ring
    rw [this]
    have h3 : 0 ≤ (Kp * δ ^ i + max B 0 * Real.exp δ) * Real.exp (-δ * -s) := by positivity
    linear_combination h3
  · have hs : s ∈ Icc (-1 : ℝ) 1 := ⟨h2, h1⟩
    have hb := hB s hs
    rw [Real.norm_eq_abs] at hb
    have hs1 : |s| ≤ 1 := abs_le.2 ⟨h2, h1⟩
    have : 1 ≤ Real.exp δ * Real.exp (-δ * |s|) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have hB0 : |iteratedDeriv i (negPsi δ β) s| ≤ max B 0 * Real.exp δ * Real.exp (-δ * |s|) := by
      calc _ ≤ max B 0 := hb.trans (le_max_left _ _)
        _ = max B 0 * 1 := (mul_one _).symm
        _ ≤ max B 0 * (Real.exp δ * Real.exp (-δ * |s|)) :=
            mul_le_mul_of_nonneg_left this (le_max_right _ _)
        _ = _ := by ring
    linear_combination hB0 + mul_nonneg hKp hE + mul_nonneg hKm hE

lemma exp_neg_abs_le_one (hδ : 0 ≤ δ) (s : ℝ) : Real.exp (-δ * |s|) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg s])

lemma mult_of_bounds {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ i, ∃ M, 0 ≤ M ∧ ∀ s, |iteratedDeriv i χ s| ≤ M) (m : ℕ) : Mult m χ := by
  choose M hM0 hM using hb
  refine ⟨hχ, ∑ i ∈ Finset.range (m + 1), M i, fun i hi s => (hM i s).trans ?_⟩
  exact Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.2 (by omega))

lemma mult_negPsi (hβ : IsCutoff β) (hδ : 0 ≤ δ) (m : ℕ) : Mult m (negPsi δ β) :=
  mult_of_bounds (contDiff_negPsi hβ) (fun i => by
    obtain ⟨M, hM0, hM⟩ := negPsi_deriv_bound hβ hδ i
    exact ⟨M, hM0, fun s => (hM s).trans (by
      nlinarith [exp_neg_abs_le_one hδ s, Real.exp_pos (-δ * |s|)])⟩) m

lemma mult_deriv_negPsi (hβ : IsCutoff β) (hδ : 0 ≤ δ) (m : ℕ) :
    Mult m (deriv (negPsi δ β)) :=
  mult_of_bounds (contDiff_infty_iff_deriv.1 (contDiff_negPsi hβ)).2 (fun i => by
    obtain ⟨M, hM0, hM⟩ := negPsi_deriv_bound hβ hδ (i + 1)
    refine ⟨M, hM0, fun s => ?_⟩
    rw [← iteratedDeriv_succ']
    exact (hM s).trans (by nlinarith [exp_neg_abs_le_one hδ s, Real.exp_pos (-δ * |s|)])) m

/-! ## 5. `ψ(s)` in `H^m(ℝ × S¹)` -/

lemma iterate_Ds_fun_s {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ∀ a : ℕ, Ds^[a] (fun x : ℝ × ℝ => χ x.1) = fun x => iteratedDeriv a χ x.1
  | 0 => by simp
  | a + 1 => by
    rw [Function.iterate_succ_apply', iterate_Ds_fun_s hχ a,
      Ds_fun_s (hχ.differentiable_iteratedDeriv a (by exact_mod_cast WithTop.coe_lt_top _)), iteratedDeriv_succ]

lemma iterate_zero_fun (D : (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ) (hD : D (fun _ => 0) = fun _ => 0) :
    ∀ a : ℕ, D^[a] (fun _ => 0) = fun _ => 0
  | 0 => rfl
  | a + 1 => by rw [Function.iterate_succ_apply', iterate_zero_fun D hD a, hD]

lemma Ds_zero_fun : Ds (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by funext x; simp [Ds]

lemma Dt_zero_fun : Dt (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by funext x; simp [Dt]

lemma pD_fun_s {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (a b : ℕ) :
    pD a b (fun x : ℝ × ℝ => χ x.1) =
      if b = 0 then (fun x => iteratedDeriv a χ x.1) else fun _ => 0 := by
  rcases b with _ | b
  · simp only [pD, Function.iterate_zero, id]; exact iterate_Ds_fun_s hχ a
  · simp only [pD, Nat.succ_ne_zero, if_false]
    rw [Function.iterate_succ_apply, Dt_fun_s (hχ.differentiable (by simp)),
      iterate_zero_fun Dt Dt_zero_fun, iterate_zero_fun Ds Ds_zero_fun]

/-- A function of `s` whose derivatives decay like `e^{-δ|s|}` lies in every `H^m`. -/
lemma smoothW_fun_s {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hδ : 0 < δ)
    (hb : ∀ i, ∃ M, 0 ≤ M ∧ ∀ s, |iteratedDeriv i χ s| ≤ M * Real.exp (-δ * |s|)) :
    SmoothW 0 (fun x : ℝ × ℝ => χ x.1) where
  smPer := ⟨hχ.comp contDiff_fst, fun _ _ => rfl⟩
  memLp a b := by
    rw [pD_fun_s hχ]
    split_ifs with h
    · obtain ⟨M, hM0, hM⟩ := hb a
      have hc : Continuous fun x : ℝ × ℝ => wt 0 x * iteratedDeriv a χ x.1 :=
        Continuous.mul (by unfold wt; fun_prop)
          ((hχ.continuous_iteratedDeriv a (by exact_mod_cast le_top)).comp continuous_fst)
      refine ((memLp_wt_neg hδ).const_mul M).of_le hc.aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      simp only [wt, zero_mul, Real.exp_zero, one_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg hM0 (Real.exp_pos _).le)]
      have := hM x.1
      rwa [neg_mul] at this ⊢
    · convert (MemLp.zero : MemLp (0 : ℝ × ℝ → ℝ) 2 cyl) using 1
      funext x; simp

lemma smoothW_negPsi (hβ : IsCutoff β) (hδ : 0 < δ) :
    SmoothW 0 (fun x : ℝ × ℝ => negPsi δ β x.1) :=
  smoothW_fun_s (contDiff_negPsi hβ) hδ (negPsi_deriv_bound hβ hδ.le)

end GWMemoir.NeckNeg
