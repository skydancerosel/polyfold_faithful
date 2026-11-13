import Polyfold.Chapter1.CylinderTrigPolynomials

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 12: density of test functions

* `approx_supp`: an element `v ∈ H^{m,δ}(ℝ × S¹)` whose weak derivatives vanish for `|s| > ρ`
  is approximated by `χ(s) · Re S_N v`, where `S_N v` is the partial Fourier sum of `v` on a
  box containing `[-ρ,ρ] × S¹` and `χ` a cut-off equal to `1` on `[-ρ,ρ]`.
* `dense_test`: the test functions (smooth, compactly supported in `s`, periodic in `t`) are
  dense in `H^{m,δ}(ℝ × S¹)`: first cut off (`tendsto_cut`), then approximate.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- The element of `H^{m,δ}` given by a test function. -/
def toH (m : ℕ) (hδ : 0 ≤ δ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) : H m hδ :=
  (⟨(hφ.memLp 2).toLp φ, hφ.mem_Hsub m hδ⟩ : Hsub m hδ)

lemma isTest_of_s {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {R : ℝ} (hR : ∀ s, R ≤ |s| → χ s = 0) :
    IsTest (fun x => χ x.1) :=
  ⟨hχ.comp contDiff_fst, fun _ _ => rfl, ⟨R, fun s _ h => hR s h.le⟩⟩

lemma isTest_mul_smPer {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {R : ℝ}
    (hR : ∀ s, R ≤ |s| → χ s = 0) {F : ℝ × ℝ → ℝ} (hF : SmPer F) :
    IsTest (fun x => χ x.1 * F x) := by
  have h := (isTest_of_s hχ hR).mul_smPer hF
  have e : (fun x => F x * χ x.1) = fun x => χ x.1 * F x := funext fun x => mul_comm _ _
  rw [e] at h; exact h

/-- A cut-off for the window `[-ρ, ρ]`. -/
lemma exists_win {ρ : ℝ} (hρ : 0 ≤ ρ) : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
    (∀ s, ρ + 2 ≤ |s| → χ s = 0) ∧ (∀ s ∈ Icc (-ρ) ρ, χ s = 1) := by
  obtain ⟨χ, hχ, h0, h1, -⟩ := exists_cutoff (a := -ρ - 2) (c := -ρ) (d := ρ) (b := ρ + 2)
    (by linarith) (by linarith) (by linarith)
  refine ⟨χ, hχ, fun s hs => h0 s ?_, fun s hs => (h1 s hs).1⟩
  rcases le_abs'.1 hs with h | h
  · left; linarith
  · right; exact h

lemma win_deriv_zero {χ : ℝ → ℝ} {R : ℝ} (h0 : ∀ s, R ≤ |s| → χ s = 0) (i : ℕ) {s : ℝ}
    (hs : R < |s|) : iteratedDeriv i χ s = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using h0 s hs.le
  · exact iteratedDeriv_eq_zero_of_eqOn (U := {s | R < |s|})
      (isOpen_lt continuous_const continuous_abs) (fun _ hs => h0 _ (le_of_lt hs)) hi hs

lemma win_hasCompactSupport {χ : ℝ → ℝ} {R : ℝ} (h0 : ∀ s, R ≤ |s| → χ s = 0) :
    HasCompactSupport χ :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs => h0 s (by
    simp only [Set.mem_Icc, not_and_or, not_le] at hs
    rcases hs with h | h
    · rw [le_abs']; left; linarith
    · rw [le_abs']; right; linarith)

lemma win_mult {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {R : ℝ} (h0 : ∀ s, R ≤ |s| → χ s = 0)
    (m : ℕ) : Mult m χ :=
  ⟨hχ, bdd_iteratedDeriv hχ (win_hasCompactSupport h0) m⟩

/-- `‖1_B f‖² = ∫_B f²` for the box `B`. -/
lemma norm_sq_indicator_box {a T : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : MemLp ((Ioc a (a + T) ×ˢ (univ : Set ℝ)).indicator f) 2 cyl) :
    ‖hf.toLp _‖ ^ 2 = ∫ x, f x ^ 2 ∂box a T := by
  have hS : MeasurableSet (Ioc a (a + T) ×ˢ (univ : Set ℝ)) := measurableSet_Ioc.prod MeasurableSet.univ
  rw [norm_sq_eq_integral]
  have h1 : ∫ x, (hf.toLp _ : ℝ × ℝ → ℝ) x ^ 2 ∂cyl =
      ∫ x, ((Ioc a (a + T) ×ˢ (univ : Set ℝ)).indicator f x) ^ 2 ∂cyl :=
    integral_congr_ae (by filter_upwards [hf.coeFn_toLp] with x hx; rw [hx])
  have e : (fun x => ((Ioc a (a + T) ×ˢ (univ : Set ℝ)).indicator f x) ^ 2) =
      (Ioc a (a + T) ×ˢ (univ : Set ℝ)).indicator (fun x => f x ^ 2) := by
    funext x; by_cases hx : x ∈ Ioc a (a + T) ×ˢ (univ : Set ℝ) <;> simp [hx]
  rw [h1, e, integral_indicator hS, box_eq]

theorem approx_supp (v : H m hδ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsupp : ∀ a b, a + b ≤ m → ∀ᵐ x ∂cyl, Gu (H.toSub v) a b x ≠ 0 → x.1 ∈ Icc (-ρ) ρ)
    {ε : ℝ} (hε : 0 < ε) : ∃ φ, ∃ hφ : IsTest φ, ‖toH m hδ hφ - v‖ < ε := by
  obtain ⟨χ, hχ, hχ0, hχ1⟩ := exists_win hρ
  have hχM : Mult m χ := win_mult hχ hχ0 m
  obtain ⟨K, hK⟩ := hχM.bdd
  set a0 : ℝ := -ρ - 3
  set T : ℝ := 2 * ρ + 6
  have hT : 0 < T := by positivity
  have hac : a0 < -ρ := by linarith
  have hdb : ρ < a0 + T := by linarith
  -- Fourier coefficients of the derivatives
  have hcoef : ∀ a b, a + b ≤ m →
      cf a0 T ((Gu (H.toSub v)) a b) = fun q => mS T q ^ a * mT q ^ b * cf a0 T ((Gu (H.toSub v)) 0 0) q := by
    intro a
    induction a with
    | zero =>
      intro b
      induction b with
      | zero => intro _; funext q; simp
      | succ b ih =>
        intro hb
        funext q
        have h := bc_dt hac (by linarith) hdb (Gu_memLp _ 0 b) (Gu_memLp _ 0 (b + 1))
          (Gu_t _ (by omega)) (hsupp 0 b (by omega)) (hsupp 0 (b + 1) hb) q.1 q.2
        have hq := congrFun (ih (by omega)) q
        simp only [cf] at hq h ⊢
        rw [h, hq, mT]; ring
    | succ a ih =>
      intro b hab
      funext q
      have h := bc_ds hac (by linarith) hdb (Gu_memLp _ a b) (Gu_memLp _ (a + 1) b)
        (Gu_s _ hab) (hsupp a b (by omega)) (hsupp (a + 1) b hab) q.1 q.2
      have hq := congrFun (ih b (by omega)) q
      simp only [cf] at hq h ⊢
      rw [h, hq, mS]; ring
  set FN : ℕ → ℝ × ℝ → ℝ := fun N => trig T (cf a0 T ((Gu (H.toSub v)) 0 0)) N
  have hpD : ∀ N a b, a + b ≤ m → pD a b (FN N) = trig T (cf a0 T ((Gu (H.toSub v)) a b)) N := by
    intro N a b hab
    simp only [FN]; rw [pD_trig, hcoef a b hab]
  have hFN : ∀ N, SmPer (FN N) := fun N => smPer_trig _ _ _
  set ψ : ℕ → ℝ × ℝ → ℝ := fun N x => χ x.1 * FN N x
  have hψ : ∀ N, IsTest (ψ N) := fun N => isTest_mul_smPer hχ hχ0 (hFN N)
  -- weak derivatives of `v`
  have hv : mulH χ hχM v = v := by
    change (⟨mulχ χ hχM (H.toSub v), _⟩ : Hsub m hδ) = H.toSub v
    refine Subtype.ext (Lp.ext ?_)
    have h00 := hsupp 0 0 (by omega)
    filter_upwards [coeFn_mulχ χ hχM (H.toSub v), Gu_zero (H.toSub v), h00] with x e1 e2 e3
    rw [e1, ← e2]
    by_cases hx : (Gu (H.toSub v)) 0 0 x = 0
    · simp [hx]
    · rw [hχ1 _ (e3 hx), one_mul]
  have hdvv : ∀ p : idx m, dv (H.toSub v) p =ᵐ[cyl] leib χ (Gu (H.toSub v)) p.1.1 p.1.2 := by
    intro p; have h := dv_mulH hχM v p; rw [hv] at h; exact h
  -- weak derivatives of the approximants
  have hlocF : ∀ N a b, LocL (pD a b (FN N)) := fun N a b => ((hFN N).pDer a b).locL
  have hleibF : ∀ N a b, a + b ≤ m →
      HasWeakDeriv a b (fun x => χ x.1 * pD 0 0 (FN N) x) (leib χ (fun a b => pD a b (FN N)) a b) :=
    fun N => leibniz hχ (fun a b _ => hlocF N a b)
      (fun a b _ => by
        have e : pD (a + 1) b (FN N) = Ds (pD a b (FN N)) := by
          simp only [pD]; rw [Function.iterate_succ_apply']
        rw [e]; exact ((hFN N).pDer a b).hasWeakDeriv_s)
      (fun b _ => by
        have e : pD 0 (b + 1) (FN N) = Dt (pD 0 b (FN N)) := by
          simp only [pD, Function.iterate_zero, id]; rw [Function.iterate_succ_apply']
        rw [e]; exact ((hFN N).pDer 0 b).hasWeakDeriv_t)
  have hmemF : ∀ N a b, MemLp (leib χ (fun a b => pD a b (FN N)) a b) 2 cyl := by
    intro N a b
    refine memLp_finsetSum _ fun i _ => ?_
    have ht := isTest_mul_smPer (contDiff_iteratedDeriv hχ i) (R := ρ + 3)
      (fun s hs => win_deriv_zero hχ0 i (by linarith)) ((hFN N).pDer (a - i) b)
    exact (ht.memLp 2).const_mul _
  have hdvψ : ∀ N (p : idx m), dv (H.toSub (toH m hδ (hψ N))) p =ᵐ[cyl]
      leib χ (fun a b => pD a b (FN N)) p.1.1 p.1.2 := by
    intro N p
    refine dv_unique _ p ((hleibF N _ _ (mem_idx.1 p.2)).congr_ae ?_ (ae_eq_refl _))
      (hmemF N _ _)
    filter_upwards [(hψ N).memLp 2 |>.coeFn_toLp] with x hx
    change _ = ((((hψ N).memLp 2).toLp (ψ N) : Lp ℝ 2 cyl) : ℝ × ℝ → ℝ) x
    rw [hx]; simp [ψ, pD]
  -- the error terms on the box
  set B : Set (ℝ × ℝ) := Ioc a0 (a0 + T) ×ˢ (univ : Set ℝ)
  have hB : MeasurableSet B := measurableSet_Ioc.prod MeasurableSet.univ
  have htrig_bdd : ∀ (c : ℤ × ℤ → ℂ) N x, ‖trig T c N x‖ ≤ ∑ q ∈ sqN N, ‖c q‖ := by
    intro c N x
    rw [trig_eq_re, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun q _ => ?_))
    rw [norm_mul, norm_eexp, mul_one]
  have hE : ∀ N a' b', MemLp (B.indicator
      (fun x => trig T (cf a0 T ((Gu (H.toSub v)) a' b')) N x - (Gu (H.toSub v)) a' b' x)) 2 cyl := by
    intro N a' b'
    have hBb : cyl.restrict B = box a0 T := (box_eq a0 T).symm
    rw [memLp_indicator_iff_restrict hB, hBb]
    refine MemLp.sub ?_ ?_
    · exact MemLp.of_bound ((smPer_trig T _ N).smooth.continuous.aestronglyMeasurable) _
        (ae_of_all _ fun x => htrig_bdd _ N x)
    · rw [← hBb]; exact (Gu_memLp _ a' b').restrict _
  have hEt : ∀ a' b', Tendsto (fun N => ‖(hE N a' b').toLp _‖) atTop (𝓝 0) := by
    intro a' b'
    have h1 := tendsto_box_sq (a := a0) hT (Gu_memLp (H.toSub v) a' b')
    have h2 : Tendsto (fun N => Real.sqrt (‖(hE N a' b').toLp _‖ ^ 2)) atTop (𝓝 0) := by
      have e : ∀ N, ‖(hE N a' b').toLp _‖ ^ 2 =
          ∫ x, (trig T (cf a0 T ((Gu (H.toSub v)) a' b')) N x - (Gu (H.toSub v)) a' b' x) ^ 2
            ∂box a0 T := fun N => norm_sq_indicator_box (hE N a' b')
      simp_rw [e]
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this; exact this
    simpa [Real.sqrt_sq (norm_nonneg _)] using h2
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (Nat.zero_le _) 0)
  set Kw : ℝ := Real.exp (δ * (ρ + 2)) * K
  have hKw : 0 ≤ Kw := by positivity
  -- the pointwise estimate
  have hpt : ∀ N (p : idx m), ‖wdvCLM m hδ p (toH m hδ (hψ N) - v)‖ ≤
      ∑ i ∈ range (p.1.1 + 1), ‖((p.1.1.choose i : ℝ) * Kw) • (hE N (p.1.1 - i) p.1.2).toLp _‖ := by
    intro N p
    obtain ⟨⟨a, b⟩, hpm⟩ := p
    have hab : a + b ≤ m := mem_idx.1 hpm
    dsimp only
    rw [map_sub]
    apply norm_le_sum_of_ae
    have hF : ∀ i ∈ range (a + 1), ∀ᵐ x ∂cyl,
        (((a.choose i : ℝ) * Kw) • (hE N (a - i) b).toLp _) x =
          (a.choose i : ℝ) * Kw * B.indicator
            (fun x => trig T (cf a0 T ((Gu (H.toSub v)) (a - i) b)) N x - (Gu (H.toSub v)) (a - i) b x) x := by
      intro i _
      filter_upwards [Lp.coeFn_smul ((a.choose i : ℝ) * Kw) ((hE N (a - i) b).toLp _),
        (hE N (a - i) b).coeFn_toLp] with x e1 e2
      rw [e1, Pi.smul_apply, e2, smul_eq_mul]
    rw [← Finset.eventually_all] at hF
    filter_upwards [coeFn_wdv (H.toSub (toH m hδ (hψ N))) ⟨(a, b), hpm⟩,
      coeFn_wdv (H.toSub v) ⟨(a, b), hpm⟩, hdvψ N ⟨(a, b), hpm⟩, hdvv ⟨(a, b), hpm⟩, hF,
      Lp.coeFn_sub (wdv (H.toSub (toH m hδ (hψ N))) ⟨(a, b), hpm⟩) (wdv (H.toSub v) ⟨(a, b), hpm⟩)]
      with x e1 e2 e3 e4 e5 e6
    change |(wdv (H.toSub (toH m hδ (hψ N))) ⟨(a, b), hpm⟩ -
      wdv (H.toSub v) ⟨(a, b), hpm⟩ : Lp ℝ 2 cyl) x| ≤ _
    rw [e6, Pi.sub_apply, e1, e2, e3, e4]
    have hsplit : wt δ x * leib χ (fun a b => pD a b (FN N)) a b x - wt δ x * leib χ (Gu (H.toSub v)) a b x =
        ∑ i ∈ range (a + 1), (a.choose i : ℝ) * (wt δ x * iteratedDeriv i χ x.1 *
          (trig T (cf a0 T ((Gu (H.toSub v)) (a - i) b)) N x - (Gu (H.toSub v)) (a - i) b x)) := by
      simp only [leib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [hpD N (a - i) b (by omega)]; ring
    rw [hsplit]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i ≤ m := by have := Finset.mem_range.1 hi; omega
    rw [e5 i hi, Real.norm_eq_abs]
    by_cases hx : ρ + 2 < |x.1|
    · rw [win_deriv_zero hχ0 i hx]; simp only [mul_zero, zero_mul, abs_zero]
      exact abs_nonneg _
    · push Not at hx
      have hxB : x ∈ B := by
        refine ⟨⟨?_, ?_⟩, mem_univ _⟩
        · linarith [neg_abs_le x.1]
        · linarith [le_abs_self x.1]
      rw [indicator_of_mem hxB]
      have hw : |wt δ x * iteratedDeriv i χ x.1| ≤ Kw := by
        rw [abs_mul, abs_of_pos (wt_pos _ _)]
        refine mul_le_mul ?_ (hK i hi' _) (abs_nonneg _) (Real.exp_pos _).le
        rw [wt, Real.exp_le_exp]; exact mul_le_mul_of_nonneg_left hx hδ
      simp only [abs_mul, Nat.abs_cast, abs_of_nonneg hKw]
      rw [mul_assoc (a.choose i : ℝ) Kw]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by rw [← abs_mul]; exact hw)
        (abs_nonneg _)) (Nat.cast_nonneg _)
  -- conclusion
  set Bd : ℕ → ℝ := fun N => ∑ p : idx m, ∑ i ∈ range (p.1.1 + 1),
    ‖((p.1.1.choose i : ℝ) * Kw) • (hE N (p.1.1 - i) p.1.2).toLp _‖
  have hBd : Tendsto Bd atTop (𝓝 0) := by
    have : (0 : ℝ) = ∑ p : idx m, ∑ i ∈ range (p.1.1 + 1), 0 := by simp
    rw [this]
    refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun i _ => ?_
    simp_rw [norm_smul]
    simpa using (hEt _ _).const_mul ‖(p.1.1.choose i : ℝ) * Kw‖
  obtain ⟨N, hN⟩ := (hBd.eventually (gt_mem_nhds hε)).exists
  refine ⟨ψ N, hψ N, ?_⟩
  calc ‖toH m hδ (hψ N) - v‖ ≤ ∑ p : idx m, ‖wdvCLM m hδ p (toH m hδ (hψ N) - v)‖ :=
        norm_H_le_sum _
    _ ≤ Bd N := Finset.sum_le_sum fun p _ => hpt N p
    _ < ε := hN

/-- The weak derivatives of `χₙ u` vanish for `|s| > 2(n+1)`. -/
lemma supp_mulH_chi (u : H m hδ) (n a b : ℕ) (hab : a + b ≤ m) :
    ∀ᵐ x ∂cyl, Gu (H.toSub (mulH (chi n) (chi_mult m n) u)) a b x ≠ 0 →
      x.1 ∈ Icc (-(2 * ((n : ℝ) + 1))) (2 * ((n : ℝ) + 1)) := by
  have h := dv_mulH (chi_mult m n) u ⟨(a, b), mem_idx.2 hab⟩
  rw [← Gu_of _ hab] at h
  filter_upwards [h] with x hx hne
  rw [hx] at hne
  by_contra hc
  apply hne
  have : 2 * ((n : ℝ) + 1) < |x.1| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; exact h
  simp [leib, chi_deriv_zero_out n _ this]

/-- The test functions are dense in `H^{m,δ}(ℝ × S¹)`. -/
theorem dense_test (m : ℕ) (hδ : 0 ≤ δ) :
    Dense {u : H m hδ | ∃ φ, ∃ hφ : IsTest φ, u = toH m hδ hφ} := by
  rw [Metric.dense_iff]
  intro u ε hε
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 (tendsto_cut u) (ε / 2) (by positivity)).imp
    fun n h => h n le_rfl
  obtain ⟨φ, hφ, hlt⟩ := approx_supp (mulH (chi n) (chi_mult m n) u)
    (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1)) (supp_mulH_chi u n) (by positivity : 0 < ε / 2)
  refine ⟨toH m hδ hφ, ?_, φ, hφ, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖toH m hδ hφ - u‖
      ≤ ‖toH m hδ hφ - mulH (chi n) (chi_mult m n) u‖ + ‖mulH (chi n) (chi_mult m n) u - u‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hlt (by rw [← dist_eq_norm]; exact hn)
    _ = ε := by ring

end Polyfold.GapP1Sobolev
