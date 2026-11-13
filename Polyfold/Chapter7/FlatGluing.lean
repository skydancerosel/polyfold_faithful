import Mathlib

/-!
# Flat gluing at `t = 0` (for Subsection 1.4.4 and Appendix 7.6.3)

The moving projections `π_t` of 2021 Subsection 1.4.4 are `0` for `t ≤ 0` and `Q(e^{1/t})` for
`t > 0`, where `Q(c)` (the projection onto `β(· + c)`) has all derivatives decaying like `e^{-εc}`
in the operator norm with one level of loss.  This file proves the calculus fact behind the smoothness
of `t ↦ π_t` at `t = 0`:

* `contDiff_of_flat`: a map `g : ℝ → X`, zero on `t ≤ 0`, `C^∞` on `t > 0`, all of whose
  derivatives tend to `0` as `t → 0⁺`, is `C^∞` on `ℝ`.
* `contDiff_flat_comp`: if `Q : ℝ → X` is `C^∞` with `‖D^n Q(c)‖ ≤ K_n e^{-εc}` for large `c`
  (a fixed `ε > 0`), then `t ↦ Q(e^{1/t})` (`t > 0`), `0` (`t ≤ 0`) is `C^∞` on `ℝ`.  The bound
  on the derivatives of `Q ∘ e^{1/·}` is Faà di Bruno's (`norm_iteratedFDerivWithin_comp_le`).
-/

open Set Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace Polyfold.ZhouFlat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section Glue

variable {g : ℝ → X}

/-- The candidate `n`-th derivative: `g^{(n)}` on `t > 0`, `0` on `t ≤ 0`. -/
def D (g : ℝ → X) (n : ℕ) (t : ℝ) : X := if 0 < t then iteratedDeriv n g t else 0

lemma hasDerivAt_iteratedDeriv_pos (hpos : ContDiffOn ℝ ∞ g (Ioi 0)) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g t) t := by
  have hev : iteratedDerivWithin n g (Ioi 0) =ᶠ[𝓝 t] iteratedDeriv n g :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht) (iteratedDerivWithin_of_isOpen isOpen_Ioi)
  have hd : DifferentiableAt ℝ (iteratedDerivWithin n g (Ioi 0)) t :=
    ((hpos.differentiableOn_iteratedDerivWithin (by exact_mod_cast WithTop.coe_lt_top _)
      (uniqueDiffOn_Ioi 0)) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)
  have h1 := (hd.congr_of_eventuallyEq hev.symm).hasDerivAt
  rwa [iteratedDeriv_succ]

lemma eventually_D_eq_pos {n : ℕ} {t : ℝ} (ht : 0 < t) : D g n =ᶠ[𝓝 t] iteratedDeriv n g :=
  Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun _ hx => if_pos hx

lemma hasDerivAt_D_pos (hpos : ContDiffOn ℝ ∞ g (Ioi 0)) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (D g n) (D g (n + 1) t) t := by
  rw [show D g (n + 1) t = iteratedDeriv (n + 1) g t from if_pos ht]
  exact (hasDerivAt_iteratedDeriv_pos hpos n ht).congr_of_eventuallyEq (eventually_D_eq_pos ht)

lemma norm_D_le (hpos : ContDiffOn ℝ ∞ g (Ioi 0))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n g) (𝓝[>] 0) (𝓝 0)) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h in 𝓝 (0 : ℝ), ‖D g n h‖ ≤ η * ‖h‖ := by
  obtain ⟨δ0, hδ0, hb⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 ((hlim (n + 1)).norm.eventually (gt_mem_nhds (by rw [norm_zero]; exact hη))))
  filter_upwards [Metric.ball_mem_nhds 0 hδ0] with h hh
  rcases le_or_gt h 0 with h0 | h0
  · simp only [D, if_neg (not_lt.2 h0), norm_zero]; positivity
  · rw [Real.norm_eq_abs, abs_of_pos h0]
    have hbound : ∀ x ∈ Ioo 0 δ0, ‖D g (n + 1) x‖ ≤ η := fun x hx => by
      rw [D, if_pos hx.1]
      refine (hb ?_ hx.1).le
      rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; exact hx.2
    have hh' : h < δ0 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos h0] at hh; exact hh
    have hmvt : ∀ ε ∈ Ioo 0 h, ‖D g n h - D g n ε‖ ≤ η * (h - ε) := fun ε hε =>
      norm_image_sub_le_of_norm_deriv_le_segment'
        (fun x hx => (hasDerivAt_D_pos hpos n (hε.1.trans_le hx.1)).hasDerivWithinAt)
        (fun x hx => hbound x ⟨hε.1.trans_le hx.1, hx.2.trans hh'⟩) h ⟨hε.2.le, le_rfl⟩
    have hlimε : Tendsto (fun ε => ‖D g n h - D g n ε‖) (𝓝[>] 0) (𝓝 ‖D g n h - 0‖) := by
      refine (tendsto_const_nhds.sub ?_).norm
      refine (hlim n).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (if_pos hε).symm
    rw [sub_zero] at hlimε
    refine le_of_tendsto hlimε ?_
    filter_upwards [Ioo_mem_nhdsGT h0] with ε hε
    exact (hmvt ε hε).trans (mul_le_mul_of_nonneg_left (by linarith [hε.1]) hη.le)

lemma hasDerivAt_D (hpos : ContDiffOn ℝ ∞ g (Ioi 0))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n g) (𝓝[>] 0) (𝓝 0)) (n : ℕ) (t : ℝ) :
    HasDerivAt (D g n) (D g (n + 1) t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hev : D g n =ᶠ[𝓝 t] fun _ => 0 :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds ht) fun x hx => if_neg (not_lt.2 (le_of_lt hx))
    rw [show D g (n + 1) t = 0 from if_neg (not_lt.2 ht.le)]
    exact (hasDerivAt_const t (0 : X)).congr_of_eventuallyEq hev
  · rw [show D g (n + 1) 0 = 0 from if_neg (lt_irrefl 0), hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.isLittleO_iff.2 fun η hη => ?_
    filter_upwards [norm_D_le hpos hlim n hη] with h hh
    simpa [D] using hh
  · exact hasDerivAt_D_pos hpos n ht

/-- **Flat gluing**: `g = 0` on `t ≤ 0`, `C^∞` on `t > 0`, every derivative `→ 0` at `0⁺`
⇒ `g` is `C^∞`. -/
theorem contDiff_of_flat (h0 : ∀ t ≤ 0, g t = 0) (hpos : ContDiffOn ℝ ∞ g (Ioi 0))
    (hlim : ∀ n : ℕ, Tendsto (iteratedDeriv n g) (𝓝[>] 0) (𝓝 0)) : ContDiff ℝ ∞ g := by
  have hD : ∀ n, iteratedDeriv n g = D g n := by
    intro n
    induction n with
    | zero =>
      funext t
      rw [iteratedDeriv_zero, D]
      split_ifs with ht
      · rfl
      · exact h0 t (not_lt.1 ht)
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hasDerivAt_D hpos hlim n t).deriv
  exact contDiff_of_differentiable_iteratedDeriv fun m _ => by
    rw [hD]; exact fun t => (hasDerivAt_D hpos hlim m t).differentiableAt

end Glue

section Comp

/-- `e(t) = e^{1/t}`. -/
def eInv (t : ℝ) : ℝ := Real.exp t⁻¹

lemma contDiffOn_inv_Ioi : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi 0) :=
  contDiffOn_id.inv fun _ hx => ne_of_gt hx

lemma contDiffOn_eInv : ContDiffOn ℝ ∞ eInv (Ioi 0) :=
  Real.contDiff_exp.comp_contDiffOn contDiffOn_inv_Ioi

lemma norm_iteratedFDerivWithin_inv (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedFDerivWithin ℝ j (fun x : ℝ => x⁻¹) (Ioi 0) t‖ = j ! * t⁻¹ ^ (j + 1) := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen isOpen_Ioi ht, iteratedDeriv_eq_iterate]
  have e : (fun x : ℝ => x⁻¹) = Inv.inv := rfl
  rw [e, iter_deriv_inv, show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
    zpow_natCast, inv_pow, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma norm_iteratedFDerivWithin_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDerivWithin ℝ i Real.exp univ y‖ = Real.exp y := by
  rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma one_le_inv_of_le_one {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ t⁻¹ :=
  (one_le_inv₀ ht).2 ht1

/-- `‖D^i e(t)‖ ≤ (n! e^{1/t} n! t⁻²)^i` for `1 ≤ i ≤ n`, `0 < t ≤ 1`. -/
lemma norm_iteratedFDerivWithin_eInv_le {n i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖iteratedFDerivWithin ℝ i eInv (Ioi 0) t‖ ≤
      ((n ! : ℝ) * Real.exp t⁻¹ * ((n ! : ℝ) * t⁻¹ ^ 2)) ^ i := by
  have hinv1 := one_le_inv_of_le_one ht ht1
  have hn1 : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  have hfac : ∀ k, k ≤ n → ((k ! : ℕ) : ℝ) ≤ n ! := fun k hk => by
    exact_mod_cast Nat.factorial_le hk
  have hD : ∀ k, 1 ≤ k → k ≤ i →
      ‖iteratedFDerivWithin ℝ k (fun x : ℝ => x⁻¹) (Ioi 0) t‖ ≤ ((n ! : ℝ) * t⁻¹ ^ 2) ^ k := by
    intro k hk1 hki
    rw [norm_iteratedFDerivWithin_inv k ht, mul_pow, ← pow_mul]
    have hk0 : k ≠ 0 := by omega
    refine mul_le_mul ((hfac k (hki.trans hin)).trans (le_self_pow₀ hn1 hk0)) ?_
      (by positivity) (by positivity)
    exact pow_le_pow_right₀ hinv1 (by omega)
  have hC : ∀ k, k ≤ i → ‖iteratedFDerivWithin ℝ k Real.exp univ ((fun x : ℝ => x⁻¹) t)‖ ≤
      Real.exp t⁻¹ := fun k _ => (norm_iteratedFDerivWithin_exp k _).le
  have h := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := fun x : ℝ => x⁻¹) (N := ∞)
    Real.contDiff_exp.contDiffOn contDiffOn_inv_Ioi (by exact_mod_cast le_top) uniqueDiffOn_univ
    (uniqueDiffOn_Ioi 0) (mapsTo_univ _ _) ht hC hD
  refine h.trans ?_
  have he1 : 1 ≤ Real.exp t⁻¹ := Real.one_le_exp (by positivity)
  have hi0 : i ≠ 0 := by omega
  have e : ((n ! : ℝ) * Real.exp t⁻¹ * ((n ! : ℝ) * t⁻¹ ^ 2)) ^ i =
      ((n ! : ℝ) ^ i * Real.exp t⁻¹ ^ i) * ((n ! : ℝ) * t⁻¹ ^ 2) ^ i := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (mul_le_mul ((hfac i hin).trans (le_self_pow₀ hn1 hi0))
    (le_self_pow₀ he1 hi0) (by positivity) (by positivity)) (by positivity)

/-- The decay bounds hold uniformly for the first `n` derivatives. -/
lemma uniform_decay {Q : ℝ → X} {ε : ℝ}
    (hdec : ∀ n : ℕ, ∃ K c0 : ℝ, ∀ c, c0 ≤ c → ‖iteratedFDeriv ℝ n Q c‖ ≤ K * Real.exp (-(ε * c)))
    (n : ℕ) : ∃ K c0 : ℝ, 0 ≤ K ∧ ∀ i ≤ n, ∀ c, c0 ≤ c →
      ‖iteratedFDeriv ℝ i Q c‖ ≤ K * Real.exp (-(ε * c)) := by
  induction n with
  | zero =>
    obtain ⟨K, c0, h⟩ := hdec 0
    refine ⟨max K 0, c0, le_max_right _ _, fun i hi c hc => ?_⟩
    obtain rfl : i = 0 := by omega
    exact (h c hc).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  | succ n ih =>
    obtain ⟨K, c0, hK, h⟩ := ih
    obtain ⟨K', c0', h'⟩ := hdec (n + 1)
    refine ⟨max K K', max c0 c0', hK.trans (le_max_left _ _), fun i hi c hc => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
    · exact (h i (by omega) c ((le_max_left _ _).trans hc)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · obtain rfl : i = n + 1 := by omega
      exact (h' c ((le_max_right _ _).trans hc)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

lemma tendsto_pow_mul_exp_neg_mul {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    Tendsto (fun y : ℝ => y ^ k * Real.exp (-(ε * y))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_id.const_mul_atTop hε)
  have h2 := h.const_mul (ε⁻¹ ^ k)
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]

/-- **Flat composition**: if `Q` is `C^∞` and all its derivatives decay like `e^{-εc}`, then
`t ↦ Q(e^{1/t})` for `t > 0`, `0` for `t ≤ 0`, is `C^∞` on `ℝ`. -/
theorem contDiff_flat_comp {Q : ℝ → X} (hQ : ContDiff ℝ ∞ Q) {ε : ℝ} (hε : 0 < ε)
    (hdec : ∀ n : ℕ, ∃ K c0 : ℝ, ∀ c, c0 ≤ c → ‖iteratedFDeriv ℝ n Q c‖ ≤ K * Real.exp (-(ε * c))) :
    ContDiff ℝ ∞ (fun t => if 0 < t then Q (Real.exp t⁻¹) else 0) := by
  set g : ℝ → X := fun t => if 0 < t then Q (Real.exp t⁻¹) else 0
  have hEq : EqOn g (Q ∘ eInv) (Ioi 0) := fun t ht => if_pos ht
  have hpos : ContDiffOn ℝ ∞ g (Ioi 0) := (hQ.comp_contDiffOn contDiffOn_eInv).congr hEq
  refine contDiff_of_flat (fun t ht => if_neg (not_lt.2 ht)) hpos fun n => ?_
  obtain ⟨K, c0, hK, hdecn⟩ := uniform_decay hdec n
  have hy : Tendsto eInv (𝓝[>] 0) atTop := Real.tendsto_exp_atTop.comp tendsto_inv_nhdsGT_zero
  set A : ℝ := (n ! : ℝ) * K * ((n ! : ℝ) * (n ! : ℝ)) ^ n
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖iteratedDeriv n g t‖ ≤ A * ((eInv t) ^ (3 * n) * Real.exp (-(ε * eInv t))) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ),
      hy.eventually (eventually_ge_atTop c0)] with t ht ht1 hc
    have ht' : (0 : ℝ) < t := ht
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      ← iteratedFDerivWithin_of_isOpen n isOpen_Ioi ht, iteratedFDerivWithin_congr hEq ht]
    have hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i Q univ (eInv t)‖ ≤
        K * Real.exp (-(ε * eInv t)) := fun i hi => by
      rw [iteratedFDerivWithin_univ]; exact hdecn i hi _ hc
    have h := norm_iteratedFDerivWithin_comp_le (N := ∞) hQ.contDiffOn contDiffOn_eInv (by exact_mod_cast le_top)
      uniqueDiffOn_univ (uniqueDiffOn_Ioi 0) (mapsTo_univ _ _) ht hC
      (fun i hi1 hin => norm_iteratedFDerivWithin_eInv_le hi1 hin ht' ht1.2.le)
    refine h.trans ?_
    have hy0 : 0 ≤ t⁻¹ := by positivity
    have hty : t⁻¹ ≤ eInv t := by
      have := Real.add_one_le_exp t⁻¹; unfold eInv; linarith
    have hD : (n ! : ℝ) * Real.exp t⁻¹ * ((n ! : ℝ) * t⁻¹ ^ 2) ≤
        ((n ! : ℝ) * (n ! : ℝ)) * eInv t ^ 3 := by
      have h2 : t⁻¹ ^ 2 ≤ eInv t ^ 2 := pow_le_pow_left₀ hy0 hty 2
      calc (n ! : ℝ) * Real.exp t⁻¹ * ((n ! : ℝ) * t⁻¹ ^ 2)
          = ((n ! : ℝ) * (n ! : ℝ)) * (eInv t * t⁻¹ ^ 2) := by unfold eInv; ring
        _ ≤ ((n ! : ℝ) * (n ! : ℝ)) * (eInv t * eInv t ^ 2) := by gcongr; exact (Real.exp_pos _).le
        _ = ((n ! : ℝ) * (n ! : ℝ)) * eInv t ^ 3 := by ring
    calc (n ! : ℝ) * (K * Real.exp (-(ε * eInv t))) *
          ((n ! : ℝ) * Real.exp t⁻¹ * ((n ! : ℝ) * t⁻¹ ^ 2)) ^ n
        ≤ (n ! : ℝ) * (K * Real.exp (-(ε * eInv t))) *
          (((n ! : ℝ) * (n ! : ℝ)) * eInv t ^ 3) ^ n := by
          gcongr
      _ = A * ((eInv t) ^ (3 * n) * Real.exp (-(ε * eInv t))) := by
          simp only [A]; rw [mul_pow, ← pow_mul]; ring
  have hlim0 : Tendsto (fun t => A * ((eInv t) ^ (3 * n) * Real.exp (-(ε * eInv t))))
      (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_pow_mul_exp_neg_mul hε (3 * n)).comp hy).const_mul A
    rwa [mul_zero] at this
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim0)

end Comp

end Polyfold.ZhouFlat
