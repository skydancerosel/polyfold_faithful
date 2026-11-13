import Polyfold.Chapter1.GapP1_Sobolev9

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 10: cutting off

With `ρ` a smooth cut-off equal to `1` on `[-1,1]` and `0` outside `(-2,2)`, put
`χₙ(s) = ρ(s/(n+1))`. For `u ∈ H^{m,δ}(ℝ × S¹)`, `χₙ u → u` in `H^{m,δ}` (`tendsto_cut`):
the derivatives of `χₙ` are bounded uniformly in `n` and the error is supported in
`|s| > n`, where the tails of `e^{δ|s|} ∂^α u` tend to `0` in `L²`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- The tails of an `L²` function tend to `0`. -/
lemma tendsto_tail (f : Lp ℝ 2 cyl) :
    Tendsto (fun n : ℕ => ‖f - cutR n f‖) atTop (𝓝 0) := by
  have hf2 : Integrable (fun x => f x ^ 2) cyl :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)).congr
      (ae_of_all _ fun x => by simp [Real.norm_eq_abs, sq_abs])
  have e : ∀ n : ℕ, ‖f - cutR n f‖ ^ 2 = ∫ x, ((1 - indR n x) * f x) ^ 2 ∂cyl := by
    intro n
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f (cutR n f), coeFn_mulOp (indR n) (aesm_indR n) 1
      (abs_indR_le n) f] with x h1 h2
    rw [h1, Pi.sub_apply, cutR, h2]; ring
  have hlim : Tendsto (fun n : ℕ => ∫ x, ((1 - indR n x) * f x) ^ 2 ∂cyl) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
      (F := fun (n : ℕ) x => ((1 - indR n x) * f x) ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => ((aestronglyMeasurable_const.sub (aesm_indR n)).mul (Lp.aestronglyMeasurable f)).pow 2) hf2
      (fun n => ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, mul_pow]
        rw [abs_of_nonneg (by positivity)]
        refine mul_le_of_le_one_left (sq_nonneg _) ?_
        simp only [indR, indicator]; split_ifs <;> norm_num)
      (ae_of_all _ fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (Nat.ceil |x.1|)] with n hn
        have : |x.1| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        simp [indR, indicator, this])
    simpa using this
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (‖f - cutR n f‖ ^ 2)) atTop (𝓝 0) := by
    simp_rw [e]
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  simpa [Real.sqrt_sq (norm_nonneg _)] using h2

/-! ### Smooth compactly supported functions have bounded derivatives -/

lemma hasCompactSupport_iteratedDeriv {ρ : ℝ → ℝ} (h : HasCompactSupport ρ) :
    ∀ i, HasCompactSupport (iteratedDeriv i ρ)
  | 0 => by simpa using h
  | i + 1 => by rw [iteratedDeriv_succ]; exact (hasCompactSupport_iteratedDeriv h i).deriv

lemma bdd_iteratedDeriv {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (h : HasCompactSupport ρ) (m : ℕ) :
    ∃ K, ∀ i ≤ m, ∀ s, |iteratedDeriv i ρ s| ≤ K := by
  have hb : ∀ i, ∃ C, ∀ s, ‖iteratedDeriv i ρ s‖ ≤ C := fun i =>
    (contDiff_iteratedDeriv hρ i).continuous.bounded_above_of_compact_support
      (hasCompactSupport_iteratedDeriv h i)
  choose C hC using hb
  refine ⟨∑ i ∈ range (m + 1), |C i|, fun i hi s => ?_⟩
  calc |iteratedDeriv i ρ s| ≤ |C i| := (hC i s).trans (le_abs_self _)
    _ ≤ _ := Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))

lemma iteratedDeriv_eq_zero_of_eqOn {ρ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {c : ℝ}
    (h : EqOn ρ (fun _ => c) U) {i : ℕ} (hi : 1 ≤ i) {s : ℝ} (hs : s ∈ U) :
    iteratedDeriv i ρ s = 0 := by
  rw [h.iteratedDeriv_of_isOpen hU i hs]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [iteratedDeriv_succ']; simp

/-! ### The cut-off family -/

/-- A fixed cut-off: `1` on `[-1,1]`, `0` outside `(-2,2)`, values in `[0,1]`. -/
lemma exists_rho : ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ s, 2 ≤ |s| → ρ s = 0) ∧
    (∀ s, |s| ≤ 1 → ρ s = 1) ∧ (∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1) := by
  obtain ⟨ρ, hρ, h0, h1, hb⟩ := exists_cutoff (a := -2) (c := -1) (d := 1) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ρ, hρ, fun s hs => h0 s ?_, fun s hs => (h1 s (abs_le.1 hs)).1, hb⟩
  rcases le_abs'.1 hs with h | h
  · left; linarith
  · right; exact h

/-- The chosen cut-off `ρ`. -/
def rho : ℝ → ℝ := exists_rho.choose

lemma rho_smooth : ContDiff ℝ ∞ rho := exists_rho.choose_spec.1
lemma rho_zero {s : ℝ} (hs : 2 ≤ |s|) : rho s = 0 := exists_rho.choose_spec.2.1 s hs
lemma rho_one {s : ℝ} (hs : |s| ≤ 1) : rho s = 1 := exists_rho.choose_spec.2.2.1 s hs
lemma rho_mem (s : ℝ) : 0 ≤ rho s ∧ rho s ≤ 1 := exists_rho.choose_spec.2.2.2 s

lemma rho_hasCompactSupport : HasCompactSupport rho :=
  HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun s hs => rho_zero (by
    simp only [Set.mem_Icc, not_and_or, not_le] at hs
    rcases hs with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)

lemma rho_deriv_zero {i : ℕ} (hi : 1 ≤ i) {s : ℝ} (hs : |s| < 1) : iteratedDeriv i rho s = 0 :=
  iteratedDeriv_eq_zero_of_eqOn (U := {s | |s| < 1}) (isOpen_lt continuous_abs continuous_const)
    (fun _ hs => rho_one (le_of_lt hs)) hi hs

lemma rho_deriv_zero_out (i : ℕ) {s : ℝ} (hs : 2 < |s|) : iteratedDeriv i rho s = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using rho_zero hs.le
  · exact iteratedDeriv_eq_zero_of_eqOn (U := {s | 2 < |s|})
      (isOpen_lt continuous_const continuous_abs) (fun _ hs => rho_zero (le_of_lt hs)) hi hs

/-- `χₙ(s) = ρ(s/(n+1))`. -/
def chi (n : ℕ) (s : ℝ) : ℝ := rho (((n : ℝ) + 1)⁻¹ * s)

lemma chi_smooth (n : ℕ) : ContDiff ℝ ∞ (chi n) :=
  rho_smooth.comp (contDiff_const.mul contDiff_id)

lemma iteratedDeriv_chi (n i : ℕ) (s : ℝ) :
    iteratedDeriv i (chi n) s = (((n : ℝ) + 1)⁻¹) ^ i * iteratedDeriv i rho (((n : ℝ) + 1)⁻¹ * s) := by
  have := iteratedDeriv_comp_const_mul (n := i) (rho_smooth.of_le (mod_cast le_top))
    (((n : ℝ) + 1)⁻¹)
  exact congrFun this s

lemma chi_bdd (m : ℕ) : ∃ K, 0 ≤ K ∧ ∀ n i, i ≤ m → ∀ s, |iteratedDeriv i (chi n) s| ≤ K := by
  obtain ⟨K, hK⟩ := bdd_iteratedDeriv rho_smooth rho_hasCompactSupport m
  refine ⟨|K|, abs_nonneg _, fun n i hi s => ?_⟩
  rw [iteratedDeriv_chi, abs_mul]
  have hc : |(((n : ℝ) + 1)⁻¹) ^ i| ≤ 1 := by
    rw [abs_pow, abs_inv]
    refine pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ ?_)
    rw [abs_of_pos (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  calc _ ≤ 1 * |K| := mul_le_mul hc ((hK i hi _).trans (le_abs_self _)) (abs_nonneg _) zero_le_one
    _ = |K| := one_mul _

lemma chi_mult (m n : ℕ) : Mult m (chi n) :=
  ⟨chi_smooth n, let ⟨K, _, hK⟩ := chi_bdd m; ⟨K, fun i hi s => hK n i hi s⟩⟩

lemma chi_mem (n : ℕ) (s : ℝ) : 0 ≤ chi n s ∧ chi n s ≤ 1 := rho_mem _

lemma inv_mul_abs_lt {n : ℕ} {s : ℝ} (hs : |s| ≤ n) : |((n : ℝ) + 1)⁻¹ * s| < 1 := by
  rw [abs_mul, abs_inv, abs_of_pos (by positivity), inv_mul_lt_iff₀ (by positivity), mul_one]
  linarith

lemma chi_one {n : ℕ} {s : ℝ} (hs : |s| ≤ n) : chi n s = 1 := rho_one (inv_mul_abs_lt hs).le

lemma chi_deriv_zero {n i : ℕ} (hi : 1 ≤ i) {s : ℝ} (hs : |s| ≤ n) : iteratedDeriv i (chi n) s = 0 := by
  rw [iteratedDeriv_chi, rho_deriv_zero hi (inv_mul_abs_lt hs), mul_zero]

lemma chi_deriv_zero_out (n i : ℕ) {s : ℝ} (hs : 2 * ((n : ℝ) + 1) < |s|) :
    iteratedDeriv i (chi n) s = 0 := by
  rw [iteratedDeriv_chi, rho_deriv_zero_out i, mul_zero]
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < n + 1), lt_inv_mul_iff₀ (by positivity)]
  linarith

/-! ### Convergence -/

/-- The Leibniz error: `leib χ G a b - G a b = ∑ C(a,j) (χ^{(j)} - [j = 0]) G (a-j) b`. -/
lemma leib_sub (χ : ℝ → ℝ) (G : ℕ → ℕ → ℝ × ℝ → ℝ) (a b : ℕ) (x : ℝ × ℝ) :
    leib χ G a b x - G a b x = ∑ j ∈ range (a + 1), (a.choose j : ℝ) *
      ((iteratedDeriv j χ x.1 - if j = 0 then 1 else 0) * G (a - j) b x) := by
  simp only [leib, sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (range (a + 1)) 0]; simp

lemma norm_wdv_cut_sub_le (u : H m hδ) (n : ℕ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ i, i ≤ m → ∀ s, |iteratedDeriv i (chi n) s| ≤ K) (p : idx m) :
    ‖wdvCLM m hδ p (mulH (chi n) (chi_mult m n) u - u)‖ ≤
      ∑ j ∈ range (p.1.1 + 1), ‖((p.1.1.choose j : ℝ) * (K + 1)) •
        ((Gu_wt (H.toSub u) (p.1.1 - j) p.1.2).toLp _ -
          cutR n ((Gu_wt (H.toSub u) (p.1.1 - j) p.1.2).toLp _))‖ := by
  obtain ⟨⟨a, b⟩, hpm⟩ := p
  have hab : a + b ≤ m := mem_idx.1 hpm
  dsimp only
  rw [map_sub]
  apply norm_le_sum_of_ae
  have h1 := coeFn_wdv (H.toSub (mulH (chi n) (chi_mult m n) u)) ⟨(a, b), hpm⟩
  have h2 := coeFn_wdv (H.toSub u) ⟨(a, b), hpm⟩
  have h3 := dv_mulH (chi_mult m n) u ⟨(a, b), hpm⟩
  have hG : dv (H.toSub u) ⟨(a, b), hpm⟩ = Gu (H.toSub u) a b := (Gu_of _ hab).symm
  have hF : ∀ j ∈ range (a + 1), ∀ᵐ x ∂cyl,
      (((a.choose j : ℝ) * (K + 1)) • ((Gu_wt (H.toSub u) (a - j) b).toLp _ -
        cutR n ((Gu_wt (H.toSub u) (a - j) b).toLp _))) x
        = (a.choose j : ℝ) * (K + 1) * ((1 - indR n x) * (wt δ x * Gu (H.toSub u) (a - j) b x)) := by
    intro j _
    set f := (Gu_wt (H.toSub u) (a - j) b).toLp _
    filter_upwards [Lp.coeFn_smul ((a.choose j : ℝ) * (K + 1)) (f - cutR n f),
      Lp.coeFn_sub f (cutR n f), coeFn_mulOp (indR n) (aesm_indR n) 1 (abs_indR_le n) f,
      MemLp.coeFn_toLp (Gu_wt (H.toSub u) (a - j) b)] with x e1 e2 e3 e4
    rw [e1, Pi.smul_apply, e2, Pi.sub_apply, smul_eq_mul, cutR, e3]
    simp only [f] at e4 ⊢; rw [e4]; ring
  rw [← Finset.eventually_all] at hF
  have hwt := Lp.coeFn_sub (wdv (H.toSub (mulH (chi n) (chi_mult m n) u)) ⟨(a, b), hpm⟩)
    (wdv (H.toSub u) ⟨(a, b), hpm⟩)
  filter_upwards [h1, h2, h3, hF, hwt] with x e1 e2 e3 e4 e5
  change |(wdv (H.toSub (mulH (chi n) (chi_mult m n) u)) ⟨(a, b), hpm⟩ -
    wdv (H.toSub u) ⟨(a, b), hpm⟩ : Lp ℝ 2 cyl) x| ≤ _
  rw [e5, Pi.sub_apply, e1, e2, e3, hG, ← mul_sub, leib_sub, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [e4 j hj, Real.norm_eq_abs]
  have hj' : j ≤ m := by have := Finset.mem_range.1 hj; omega
  have hc : |iteratedDeriv j (chi n) x.1 - (if j = 0 then 1 else 0)| ≤ (K + 1) * (1 - indR n x) := by
    by_cases hx : |x.1| ≤ n
    · have : iteratedDeriv j (chi n) x.1 - (if j = 0 then 1 else 0) = 0 := by
        rcases Nat.eq_zero_or_pos j with rfl | hjp
        · simp [chi_one hx]
        · simp [chi_deriv_zero hjp hx, hjp.ne']
      rw [this, abs_zero]
      have : indR n x = 1 := by simp [indR, indicator, hx]
      rw [this]; simp
    · have : indR n x = 0 := by simp [indR, indicator, hx]
      rw [this, sub_zero, mul_one]
      refine (abs_sub _ _).trans (add_le_add (hK j hj' _) ?_)
      split_ifs <;> norm_num
  have hind : 0 ≤ 1 - indR n x := by
    have := abs_indR_le n x; linarith [le_abs_self (indR n x)]
  simp only [abs_mul, Nat.abs_cast, abs_of_nonneg hind,
    abs_of_nonneg (show (0 : ℝ) ≤ K + 1 by linarith)]
  calc |wt δ x| * ((a.choose j : ℝ) * (|iteratedDeriv j (chi n) x.1 - (if j = 0 then 1 else 0)| *
          |Gu (H.toSub u) (a - j) b x|))
      ≤ |wt δ x| * ((a.choose j : ℝ) * ((K + 1) * (1 - indR n x) *
          |Gu (H.toSub u) (a - j) b x|)) := by gcongr
    _ = _ := by ring

/-- `χₙ u → u` in `H^{m,δ}(ℝ × S¹)`. -/
theorem tendsto_cut (u : H m hδ) :
    Tendsto (fun n : ℕ => mulH (chi n) (chi_mult m n) u) atTop (𝓝 u) := by
  obtain ⟨K, hK0, hK⟩ := chi_bdd m
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set B : ℕ → ℝ := fun n => ∑ p : idx m, ∑ j ∈ range (p.1.1 + 1),
    ‖((p.1.1.choose j : ℝ) * (K + 1)) •
        ((Gu_wt (H.toSub u) (p.1.1 - j) p.1.2).toLp _ -
          cutR n ((Gu_wt (H.toSub u) (p.1.1 - j) p.1.2).toLp _))‖
  have hB : Tendsto B atTop (𝓝 0) := by
    have : (0 : ℝ) = ∑ p : idx m, ∑ j ∈ range (p.1.1 + 1), 0 := by simp
    rw [this]
    refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun j _ => ?_
    simp_rw [norm_smul]
    simpa using (tendsto_tail _).const_mul ‖(p.1.1.choose j : ℝ) * (K + 1)‖
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hB
  refine (norm_H_le_sum _).trans (Finset.sum_le_sum fun p _ => ?_)
  exact norm_wdv_cut_sub_le u n hK0 (hK n) p

end Polyfold.GapP1Sobolev
