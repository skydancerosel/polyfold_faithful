import Polyfold.Chapter1.GapP1_Sobolev4

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 5: Rellich's theorem on a bounded
cylinder

The compactness in Example 1.1.3 rests on "Sobolev's compact embedding theorem for bounded
domains". We prove the case needed, by Fourier series on a box:

* `rellich`: for `R > 0` and `C`, the set of the restrictions `1_{|s| ≤ R} v` of the
  `v ∈ L²(ℝ × S¹)` with `‖v‖, ‖∂_s v‖, ‖∂_t v‖ ≤ C` (weak derivatives) is totally bounded in
  `L²(ℝ × S¹)`.

Proof: with a cut-off `χ = 1` on `[-R, R]`, `w = χ v` lives in a box of length `T`; its box Fourier
coefficients satisfy `∑ (j² + k²) |ŵ_{jk}|² ≤ M` (Parseval for `∂_s w`, `∂_t w`, and `bc_ds`, `bc_dt`),
so the coefficients with `|j|, |k| ≤ N` determine `w`, hence `1_{|s|≤R} v`, up to `O(1/N)`
(`totallyBounded_image_of_coords`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-! ### Totally bounded sets -/

/-- A set which is approximated to within every `ε` by totally bounded sets is totally bounded. -/
lemma totallyBounded_of_approx {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (h : ∀ ε > 0, ∃ S' : Set X, TotallyBounded S' ∧ ∀ x ∈ S, ∃ y ∈ S', dist x y < ε) :
    TotallyBounded S := by
  refine Metric.totallyBounded_iff.2 fun ε hε => ?_
  obtain ⟨S', hS', hS⟩ := h (ε / 2) (by positivity)
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hS' (ε / 2) (by positivity)
  refine ⟨t, ht, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hS x hx
  have := hcov hy
  simp only [mem_iUnion, Metric.mem_ball] at this ⊢
  obtain ⟨z, hz, hyz⟩ := this
  exact ⟨z, hz, by linarith [dist_triangle x y z]⟩

/-- The image `f '' A` is totally bounded if, for every `ε`, finitely many coordinates
(a map `P` into a proper space, bounded on `A`) determine `f` on `A` up to `ε`. -/
lemma totallyBounded_image_of_coords {α X : Type*} [PseudoMetricSpace X] {A : Set α} (f : α → X)
    (h : ∀ ε > 0, ∃ (E : Type) (_ : PseudoMetricSpace E) (_ : ProperSpace E) (P : α → E) (η : ℝ),
      0 < η ∧ Bornology.IsBounded (P '' A) ∧
        ∀ a ∈ A, ∀ b ∈ A, dist (P a) (P b) < η → dist (f a) (f b) < ε) :
    TotallyBounded (f '' A) := by
  refine Metric.totallyBounded_iff.2 fun ε hε => ?_
  obtain ⟨E, _, _, P, η, hη, hb, hP⟩ := h ε hε
  have htb : TotallyBounded (P '' A) := hb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨t, htA, ht, hcov⟩ := Metric.finite_approx_of_totallyBounded htb η hη
  have hchoose : ∀ y : t, ∃ a ∈ A, P a = y := fun y => htA y.2
  choose g hgA hgP using hchoose
  have : Finite t := ht.to_subtype
  refine ⟨Set.range (fun y : t => f (g y)), Set.finite_range _, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have := hcov ⟨a, ha, rfl⟩
  rw [Set.mem_iUnion₂] at this
  obtain ⟨y, hy, hay⟩ := this
  rw [Set.mem_iUnion₂]
  refine ⟨f (g ⟨y, hy⟩), ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  rw [Metric.mem_ball] at hay ⊢
  refine hP a ha _ (hgA _) ?_
  rwa [hgP]

/-! ### `L²` norms as integrals -/

lemma norm_sq_eq_integral (f : Lp ℝ 2 cyl) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂cyl := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1; funext x
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma integral_sq_box_le {a T : ℝ} {w : ℝ × ℝ → ℝ} (hw : MemLp w 2 cyl) :
    ∫ x, ‖((w x : ℝ) : ℂ)‖ ^ 2 ∂box a T ≤ ∫ x, w x ^ 2 ∂cyl := by
  have e : ∀ x, ‖((w x : ℝ) : ℂ)‖ ^ 2 = w x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [box_eq]
  exact setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm hw.1).1 hw |>.congr
    (ae_of_all _ fun x => by simp [Real.norm_eq_abs, sq_abs])) (ae_of_all _ fun x => sq_nonneg _)

lemma memLp_box {a T : ℝ} {w : ℝ × ℝ → ℝ} (hw : MemLp w 2 cyl) :
    MemLp (fun x => ((w x : ℝ) : ℂ)) 2 (box a T) := by
  rw [box_eq]; exact hw.ofReal.restrict _

/-! ### Cut-offs with bounded derivative -/

lemma exists_cutoff' {a b c d : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ s, s ≤ a ∨ b ≤ s → χ s = 0) ∧
      (∀ s ∈ Icc c d, χ s = 1 ∧ deriv χ s = 0) ∧ (∀ s, |χ s| ≤ 1) ∧
      ∃ C', ∀ s, |deriv χ s| ≤ C' := by
  obtain ⟨χ, hχ, h0, h1, hb⟩ := exists_cutoff hac hcd hdb
  refine ⟨χ, hχ, h0, h1, fun s => abs_le.2 ⟨by linarith [(hb s).1], (hb s).2⟩, ?_⟩
  have hc : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc a b))
  refine ⟨max C 0, fun s => ?_⟩
  by_cases hs : s ∈ Icc a b
  · exact (Real.norm_eq_abs _ ▸ hC s hs).trans (le_max_left _ _)
  · have hev : χ =ᶠ[𝓝 s] fun _ => 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · filter_upwards [Iio_mem_nhds hs] with y hy using h0 y (Or.inl hy.le)
      · filter_upwards [Ioi_mem_nhds hs] with y hy using h0 y (Or.inr hy.le)
    rw [hev.deriv_eq]; simp

/-! ### Box coefficients with frequency weights -/

lemma bc_sub {a T : ℝ} {F G : ℝ × ℝ → ℂ} (hF : Integrable F (box a T))
    (hG : Integrable G (box a T)) (j k : ℤ) :
    bc a T (F - G) j k = bc a T F j k - bc a T G j k := by
  have hb : ∀ {H : ℝ × ℝ → ℂ}, Integrable H (box a T) →
      Integrable (fun x => ecoef T j k x * H x) (box a T) := fun hH =>
    hH.bdd_mul (c := 1) (continuous_ecoef T j k).aestronglyMeasurable
      (ae_of_all _ fun x => (norm_ecoef T j k x).le)
  simp only [bc, Pi.sub_apply, mul_sub]
  rw [integral_sub (hb hF) (hb hG), mul_sub]

/-- **Frequency-weighted Parseval bound.** For `w` supported in `[c,d] × S¹ ⊂ (a, a+T) × S¹`
with weak derivatives `w_s`, `w_t` in `L²`: `∑ (j² + k²) |ŵ_{jk}|² ≤ T (‖w_s‖² + ‖w_t‖²)`. -/
theorem summable_freq_bc {a T c d : ℝ} (hT : 1 ≤ T) (hac : a < c) (hcd : c ≤ d)
    (hdb : d < a + T) {w ws wt : ℝ × ℝ → ℝ} (hw : MemLp w 2 cyl) (hws : MemLp ws 2 cyl)
    (hwt : MemLp wt 2 cyl) (h1 : HasWeakDeriv 1 0 w ws) (h2 : HasWeakDeriv 0 1 w wt)
    (sw : ∀ᵐ x ∂cyl, w x ≠ 0 → x.1 ∈ Icc c d) (sws : ∀ᵐ x ∂cyl, ws x ≠ 0 → x.1 ∈ Icc c d)
    (swt : ∀ᵐ x ∂cyl, wt x ≠ 0 → x.1 ∈ Icc c d) :
    Summable (fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) *
        ‖bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2) ∧
      ∑' p : ℤ × ℤ, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * ‖bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2
        ≤ T * (∫ x, ws x ^ 2 ∂cyl + ∫ x, wt x ^ 2 ∂cyl) := by
  have hT0 : 0 < T := by linarith
  have Ps := hasSum_bc hT0 (memLp_box (a := a) (T := T) hws)
  have Pt := hasSum_bc hT0 (memLp_box (a := a) (T := T) hwt)
  have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have key : ∀ p : ℤ × ℤ, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * ‖bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2
      ≤ T ^ 2 * (‖bc a T (fun x => (ws x : ℂ)) p.1 p.2‖ ^ 2 +
        ‖bc a T (fun x => (wt x : ℂ)) p.1 p.2‖ ^ 2) := by
    intro p
    rw [bc_ds hac hcd hdb hw hws h1 sw sws, bc_dt hac hcd hdb hw hwt h2 sw swt]
    set B := ‖bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2
    have hB : 0 ≤ B := sq_nonneg _
    have e1 : ‖(2 * Real.pi * I * p.1 / T : ℂ) * bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2
        = 4 * Real.pi ^ 2 * (p.1 : ℝ) ^ 2 / T ^ 2 * B := by
      rw [norm_mul, mul_pow]
      congr 1
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hT0]
      rw [div_pow, mul_pow, mul_pow, mul_pow, sq_abs]; ring
    have e2 : ‖(2 * Real.pi * I * p.2 : ℂ) * bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2
        = 4 * Real.pi ^ 2 * (p.2 : ℝ) ^ 2 * B := by
      rw [norm_mul, mul_pow]
      congr 1
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
        Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
    rw [e1, e2]
    have hT2 : T ^ 2 * (4 * Real.pi ^ 2 * (p.1 : ℝ) ^ 2 / T ^ 2 * B)
        = 4 * Real.pi ^ 2 * (p.1 : ℝ) ^ 2 * B := by
      field_simp
    have hj : (p.1 : ℝ) ^ 2 * B ≤ 4 * Real.pi ^ 2 * (p.1 : ℝ) ^ 2 * B := by
      have := mul_le_mul_of_nonneg_right hpi (mul_nonneg (sq_nonneg (p.1 : ℝ)) hB)
      nlinarith
    have hk : (p.2 : ℝ) ^ 2 * B ≤ T ^ 2 * (4 * Real.pi ^ 2 * (p.2 : ℝ) ^ 2 * B) := by
      have h0 : 0 ≤ 4 * Real.pi ^ 2 * (p.2 : ℝ) ^ 2 * B := by positivity
      have hT1 : 1 ≤ T ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right hpi (mul_nonneg (sq_nonneg (p.2 : ℝ)) hB)
      nlinarith
    rw [mul_add, hT2]
    nlinarith
  have hsum : Summable (fun p : ℤ × ℤ => T ^ 2 * (‖bc a T (fun x => (ws x : ℂ)) p.1 p.2‖ ^ 2 +
      ‖bc a T (fun x => (wt x : ℂ)) p.1 p.2‖ ^ 2)) :=
    (Ps.summable.add Pt.summable).mul_left _
  have hnn : ∀ p : ℤ × ℤ, 0 ≤ ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) *
      ‖bc a T (fun x => (w x : ℂ)) p.1 p.2‖ ^ 2 := fun p => by positivity
  have hS := Summable.of_nonneg_of_le hnn key hsum
  refine ⟨hS, ?_⟩
  calc _ ≤ ∑' p : ℤ × ℤ, T ^ 2 * (‖bc a T (fun x => (ws x : ℂ)) p.1 p.2‖ ^ 2 +
        ‖bc a T (fun x => (wt x : ℂ)) p.1 p.2‖ ^ 2) := hS.tsum_le_tsum key hsum
    _ = T ^ 2 * (T⁻¹ * ∫ x, ‖((ws x : ℝ) : ℂ)‖ ^ 2 ∂box a T +
          T⁻¹ * ∫ x, ‖((wt x : ℝ) : ℂ)‖ ^ 2 ∂box a T) := by
        rw [tsum_mul_left, (Ps.add Pt).tsum_eq]
    _ = T * (∫ x, ‖((ws x : ℝ) : ℂ)‖ ^ 2 ∂box a T + ∫ x, ‖((wt x : ℝ) : ℂ)‖ ^ 2 ∂box a T) := by
        field_simp
    _ ≤ T * (∫ x, ws x ^ 2 ∂cyl + ∫ x, wt x ^ 2 ∂cyl) := by
        gcongr
        · exact integral_sq_box_le hws
        · exact integral_sq_box_le hwt

/-! ### Rellich's theorem on a bounded cylinder -/

/-- The indicator of `{|s| ≤ R}`. -/
def indR (R : ℝ) (x : ℝ × ℝ) : ℝ := {y : ℝ × ℝ | |y.1| ≤ R}.indicator (fun _ => (1 : ℝ)) x

lemma measurableSet_absLe (R : ℝ) : MeasurableSet {y : ℝ × ℝ | |y.1| ≤ R} :=
  measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const

lemma abs_indR_le (R : ℝ) (x : ℝ × ℝ) : |indR R x| ≤ 1 := by
  unfold indR; by_cases h : x ∈ {y : ℝ × ℝ | |y.1| ≤ R} <;> simp [h]

lemma aesm_indR (R : ℝ) : AEStronglyMeasurable (indR R) cyl :=
  (measurable_const.indicator (measurableSet_absLe R)).aestronglyMeasurable

/-- Restriction to the bounded cylinder `[-R, R] × S¹`. -/
def cutR (R : ℝ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl := mulOp (indR R) (aesm_indR R) 1 (abs_indR_le R)

/-- The `H¹`-bounded set of radius `C`. -/
def H1ball (C : ℝ) : Set (Lp ℝ 2 cyl) :=
  {v | ∃ gs gt : Lp ℝ 2 cyl, HasWeakDeriv 1 0 v gs ∧ HasWeakDeriv 0 1 v gt ∧ ‖v‖ ≤ C ∧
    ‖gs‖ ≤ C ∧ ‖gt‖ ≤ C}

/-- `‖1_{|s| ≤ R} v‖² ≤ ∫_box |χ v|²` when `χ = 1` on `[-R, R]` and `[-R,R] ⊂ (a, a+T]`. -/
lemma norm_cutR_sq_le {R a T : ℝ} (ha : a < -R) (hb : R ≤ a + T) {χ : ℝ → ℝ}
    (hχ1 : ∀ s ∈ Icc (-R) R, χ s = 1) (hχc : AEStronglyMeasurable (fun x : ℝ × ℝ => χ x.1) cyl)
    (hχb : ∀ x : ℝ × ℝ, |χ x.1| ≤ 1) (v : Lp ℝ 2 cyl) :
    ‖cutR R v‖ ^ 2 ≤
      ∫ x, ‖(((mulOp (fun x => χ x.1) hχc 1 hχb v) x : ℝ) : ℂ)‖ ^ 2 ∂box a T := by
  set w := mulOp (fun x => χ x.1) hχc 1 hχb v
  have hint : Integrable (fun x => ‖((w x : ℝ) : ℂ)‖ ^ 2) cyl :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp w).ofReal.1).1 (Lp.memLp w).ofReal
  have hS : MeasurableSet (Ioc a (a + T) ×ˢ (univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  rw [norm_sq_eq_integral, box_eq, ← integral_indicator hS]
  refine integral_mono_ae ?_ (hint.indicator hS) ?_
  · have := (memLp_two_iff_integrable_sq_norm (Lp.memLp (cutR R v)).1).1 (Lp.memLp (cutR R v))
    exact this.congr (ae_of_all _ fun x => by simp only [Real.norm_eq_abs, sq_abs])
  · filter_upwards [coeFn_mulOp (indR R) (aesm_indR R) 1 (abs_indR_le R) v,
      coeFn_mulOp (fun x => χ x.1) hχc 1 hχb v] with x h1 h2
    change (cutR R v) x ^ 2 ≤ _
    rw [cutR, h1]
    by_cases hx : |x.1| ≤ R
    · have hmem : x ∈ Ioc a (a + T) ×ˢ (univ : Set ℝ) := by
        refine ⟨⟨?_, ?_⟩, mem_univ _⟩
        · linarith [(abs_le.1 hx).1]
        · linarith [(abs_le.1 hx).2]
      rw [indicator_of_mem hmem]
      simp only [indR, indicator_of_mem (show x ∈ {y : ℝ × ℝ | |y.1| ≤ R} from hx), one_mul]
      change v x ^ 2 ≤ ‖((w x : ℝ) : ℂ)‖ ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, h2, (hχ1 _ (abs_le.1 hx)), one_mul]
    · simp only [indR, indicator_of_notMem (show x ∉ {y : ℝ × ℝ | |y.1| ≤ R} from hx),
        zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact indicator_nonneg (fun _ _ => sq_nonneg _) _

/-- The square `[-N, N]²` of frequencies. -/
def sqN (N : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N

lemma le_freq_of_not_mem_sqN {N : ℕ} {p : ℤ × ℤ} (hp : p ∉ sqN N) :
    (N : ℝ) ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  simp only [sqN, Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hp
  have h1 : (N : ℝ) ^ 2 ≤ (p.1 : ℝ) ^ 2 ∨ (N : ℝ) ^ 2 ≤ (p.2 : ℝ) ^ 2 := by
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    rcases hp with (h | h) | (h | h)
    · left; have : (p.1 : ℝ) < -(N : ℝ) := by exact_mod_cast h
      nlinarith
    · left; have : (N : ℝ) < (p.1 : ℝ) := by exact_mod_cast h
      nlinarith
    · right; have : (p.2 : ℝ) < -(N : ℝ) := by exact_mod_cast h
      nlinarith
    · right; have : (N : ℝ) < (p.2 : ℝ) := by exact_mod_cast h
      nlinarith
  rcases h1 with h1 | h1
  · linarith [sq_nonneg (p.2 : ℝ)]
  · linarith [sq_nonneg (p.1 : ℝ)]

/-- The tail estimate for coefficient sequences with bounded frequency moments. -/
lemma tsum_sub_le {b₁ b₂ : ℤ × ℤ → ℂ} {M η : ℝ} {N : ℕ} (hN : 0 < N)
    (hS₁ : Summable (fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * ‖b₁ p‖ ^ 2))
    (hM₁ : ∑' p : ℤ × ℤ, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * ‖b₁ p‖ ^ 2 ≤ M)
    (hS₂ : Summable (fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * ‖b₂ p‖ ^ 2))
    (hM₂ : ∑' p : ℤ × ℤ, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * ‖b₂ p‖ ^ 2 ≤ M)
    (hs₁ : Summable (fun p => ‖b₁ p‖ ^ 2)) (hs₂ : Summable (fun p => ‖b₂ p‖ ^ 2))
    (hcoord : ∀ p ∈ sqN N, ‖b₁ p - b₂ p‖ < η) :
    ∑' p, ‖b₁ p - b₂ p‖ ^ 2 ≤ (sqN N).card * η ^ 2 + 2 / (N : ℝ) ^ 2 * (M + M) := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  set W : ℤ × ℤ → ℝ := fun p => (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2
  have hsq : ∀ p, ‖b₁ p - b₂ p‖ ^ 2 ≤ 2 * (‖b₁ p‖ ^ 2 + ‖b₂ p‖ ^ 2) := by
    intro p
    have h := norm_sub_le (b₁ p) (b₂ p)
    have h0 := norm_nonneg (b₁ p - b₂ p)
    nlinarith [sq_nonneg (‖b₁ p‖ - ‖b₂ p‖)]
  have hbound : ∀ p, ‖b₁ p - b₂ p‖ ^ 2 ≤ (if p ∈ sqN N then η ^ 2 else 0) +
      2 / (N : ℝ) ^ 2 * (W p * ‖b₁ p‖ ^ 2 + W p * ‖b₂ p‖ ^ 2) := by
    intro p
    have hW : 0 ≤ W p := by positivity
    have h0 : 0 ≤ 2 / (N : ℝ) ^ 2 * (W p * ‖b₁ p‖ ^ 2 + W p * ‖b₂ p‖ ^ 2) := by positivity
    by_cases hp : p ∈ sqN N
    · rw [if_pos hp]
      have h1 := hcoord p hp
      have h2 : ‖b₁ p - b₂ p‖ ^ 2 ≤ η ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1.le 2
      linarith
    · rw [if_neg hp, zero_add]
      have h2 : (N : ℝ) ^ 2 ≤ W p := le_freq_of_not_mem_sqN hp
      have h3 : 2 * (‖b₁ p‖ ^ 2 + ‖b₂ p‖ ^ 2) ≤
          2 / (N : ℝ) ^ 2 * (W p * ‖b₁ p‖ ^ 2 + W p * ‖b₂ p‖ ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hN2]
        have := mul_le_mul_of_nonneg_left h2
          (by positivity : (0 : ℝ) ≤ 2 * (‖b₁ p‖ ^ 2 + ‖b₂ p‖ ^ 2))
        nlinarith
      exact (hsq p).trans h3
  have hsumD : Summable (fun p => ‖b₁ p - b₂ p‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsq ((hs₁.add hs₂).mul_left 2)
  have hfin : Summable (fun p : ℤ × ℤ => if p ∈ sqN N then η ^ 2 else 0) :=
    summable_of_ne_finset_zero (s := sqN N) fun p hp => if_neg hp
  have hsumR := hfin.add ((hS₁.add hS₂).mul_left (2 / (N : ℝ) ^ 2))
  refine (hsumD.tsum_le_tsum hbound hsumR).trans ?_
  rw [hfin.tsum_add ((hS₁.add hS₂).mul_left _), tsum_mul_left, hS₁.tsum_add hS₂,
    tsum_eq_sum (s := sqN N) (fun p hp => if_neg hp), Finset.sum_ite_mem, Finset.inter_self,
    Finset.sum_const, nsmul_eq_mul]
  gcongr

/-- The choice of `N` and `η`. -/
lemma exists_N_eta {T M ε : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ η : ℝ, 0 < η ∧
      T * ((sqN N).card * η ^ 2 + 2 / (N : ℝ) ^ 2 * (M + M)) < ε ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * T * M / ε ^ 2 + 1)
  have hN1 : (1 : ℝ) < N := by
    have : 0 ≤ 8 * T * M / ε ^ 2 := by positivity
    linarith
  have hN0 : 0 < N := by exact_mod_cast (zero_lt_one.trans hN1)
  refine ⟨N, hN0, ?_⟩
  set K : ℝ := T * (sqN N).card
  have hK : 0 ≤ K := by positivity
  refine ⟨ε / (2 * (K + 1)), by positivity, ?_⟩
  have e1 : T * ((sqN N).card * (ε / (2 * (K + 1))) ^ 2) ≤ ε ^ 2 / 4 := by
    have : T * ((sqN N).card * (ε / (2 * (K + 1))) ^ 2) = K * ε ^ 2 / (4 * (K + 1) ^ 2) := by
      simp only [K]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ε, sq_nonneg K]
  have e2 : T * (2 / (N : ℝ) ^ 2 * (M + M)) < ε ^ 2 / 2 := by
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hN' : 8 * T * M / ε ^ 2 < N := by linarith
    rw [div_lt_iff₀ (by positivity)] at hN'
    have : T * (2 / (N : ℝ) ^ 2 * (M + M)) = 4 * T * M / (N : ℝ) ^ 2 := by
      field_simp; ring
    rw [this, div_lt_iff₀ (by positivity)]
    have h4 : 0 ≤ 4 * T * M := by positivity
    nlinarith
  nlinarith

/-- **Rellich's theorem on `[-R, R] × S¹`.** -/
theorem rellich {R : ℝ} (hR : 0 < R) (C : ℝ) : TotallyBounded (cutR R '' H1ball C) := by
  have hT : (1 : ℝ) ≤ 2 * R + 4 := by linarith
  have hT0 : (0 : ℝ) < 2 * R + 4 := by linarith
  obtain ⟨χ, hχ, hχ0, hχ1, hχb, C', hC'⟩ :=
    exists_cutoff' (a := -R - 1) (b := R + 1) (c := -R) (d := R) (by linarith) (by linarith)
      (by linarith)
  have hC'0 : 0 ≤ C' := (abs_nonneg _).trans (hC' 0)
  have hχc : Continuous χ := hχ.continuous
  have hχm : AEStronglyMeasurable (fun x : ℝ × ℝ => χ x.1) cyl :=
    (hχc.comp continuous_fst).aestronglyMeasurable
  have hχm' : AEStronglyMeasurable (fun x : ℝ × ℝ => deriv χ x.1) cyl :=
    ((hχ.continuous_deriv (by simp)).comp continuous_fst).aestronglyMeasurable
  have hχb' : ∀ x : ℝ × ℝ, |χ x.1| ≤ 1 := fun x => hχb x.1
  have hC'' : ∀ x : ℝ × ℝ, |deriv χ x.1| ≤ C' := fun x => hC' x.1
  -- support of the cut-off
  have hχout : ∀ s, s ∉ Icc (-R - 1) (R + 1) → χ s = 0 ∧ deriv χ s = 0 := by
    intro s hs
    simp only [mem_Icc, not_and_or, not_le] at hs
    have hev : χ =ᶠ[𝓝 s] fun _ => 0 := by
      rcases hs with hs | hs
      · filter_upwards [Iio_mem_nhds hs] with y hy using hχ0 y (Or.inl hy.le)
      · filter_upwards [Ioi_mem_nhds hs] with y hy using hχ0 y (Or.inr hy.le)
    exact ⟨hev.eq_of_nhds, by rw [hev.deriv_eq]; simp⟩
  have hmulb : ∀ f : Lp ℝ 2 cyl, ‖mulOp (fun x => χ x.1) hχm 1 hχb' f‖ ≤ ‖f‖ := fun f => by
    have := (ContinuousLinearMap.le_opNorm (mulOp (fun x => χ x.1) hχm 1 hχb') f).trans
      (mul_le_mul_of_nonneg_right (norm_mulOp_le zero_le_one) (norm_nonneg _))
    simpa using this
  -- the frequency bound
  have hM : ∀ v ∈ H1ball C,
      Summable (fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) *
        ‖bc (-R - 2) (2 * R + 4)
          (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v) x : ℂ)) p.1 p.2‖ ^ 2) ∧
      ∑' p : ℤ × ℤ, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) *
        ‖bc (-R - 2) (2 * R + 4)
          (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v) x : ℂ)) p.1 p.2‖ ^ 2
        ≤ (2 * R + 4) * (((C' + 1) * C) ^ 2 + C ^ 2) := by
    rintro v ⟨gs, gt, hs, ht, hv, hgs, hgt⟩
    have cv : mulOp (fun x => χ x.1) hχm 1 hχb' v =ᵐ[cyl] fun x => χ x.1 * v x :=
      coeFn_mulOp _ _ _ _ v
    have cs1 : mulOp (fun x => deriv χ x.1) hχm' C' hC'' v =ᵐ[cyl] fun x => deriv χ x.1 * v x :=
      coeFn_mulOp _ _ _ _ v
    have cs2 : mulOp (fun x => χ x.1) hχm 1 hχb' gs =ᵐ[cyl] fun x => χ x.1 * gs x :=
      coeFn_mulOp _ _ _ _ gs
    have ct : mulOp (fun x => χ x.1) hχm 1 hχb' gt =ᵐ[cyl] fun x => χ x.1 * gt x :=
      coeFn_mulOp _ _ _ _ gt
    set ws := mulOp (fun x => deriv χ x.1) hχm' C' hC'' v + mulOp (fun x => χ x.1) hχm 1 hχb' gs
    set wt := mulOp (fun x => χ x.1) hχm 1 hχb' gt
    have cws := Lp.coeFn_add (mulOp (fun x => deriv χ x.1) hχm' C' hC'' v)
      (mulOp (fun x => χ x.1) hχm 1 hχb' gs)
    have h1 : HasWeakDeriv 1 0 (mulOp (fun x => χ x.1) hχm 1 hχb' v) ws := by
      refine (hs.mul_s (Lp.memLp v) (Lp.memLp gs) hχ).congr_ae cv.symm ?_
      filter_upwards [cws, cs1, cs2] with x e1 e2 e3
      rw [e1, Pi.add_apply, e2, e3]
    have h2 : HasWeakDeriv 0 1 (mulOp (fun x => χ x.1) hχm 1 hχb' v) wt :=
      (ht.mul_s_t hχ).congr_ae cv.symm ct.symm
    have s1 : ∀ᵐ x ∂cyl, (mulOp (fun x => χ x.1) hχm 1 hχb' v) x ≠ 0 →
        x.1 ∈ Icc (-R - 1) (R + 1) := by
      filter_upwards [cv] with x hx hne
      by_contra hc
      apply hne; rw [hx, (hχout _ hc).1, zero_mul]
    have s2 : ∀ᵐ x ∂cyl, ws x ≠ 0 → x.1 ∈ Icc (-R - 1) (R + 1) := by
      filter_upwards [cws, cs1, cs2] with x e1 e2 e3 hne
      by_contra hc
      apply hne; rw [e1, Pi.add_apply, e2, e3, (hχout _ hc).1, (hχout _ hc).2]; ring
    have s3 : ∀ᵐ x ∂cyl, wt x ≠ 0 → x.1 ∈ Icc (-R - 1) (R + 1) := by
      filter_upwards [ct] with x hx hne
      by_contra hc
      apply hne; rw [hx, (hχout _ hc).1, zero_mul]
    obtain ⟨hS, hle⟩ := summable_freq_bc (a := -R - 2) (T := 2 * R + 4) hT (by linarith)
      (by linarith) (by linarith) (Lp.memLp _) (Lp.memLp ws) (Lp.memLp wt) h1 h2 s1 s2 s3
    refine ⟨hS, hle.trans ?_⟩
    rw [← norm_sq_eq_integral, ← norm_sq_eq_integral]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hgt
    have n1 : ‖ws‖ ≤ (C' + 1) * C := by
      calc ‖ws‖ ≤ ‖mulOp (fun x => deriv χ x.1) hχm' C' hC'' v‖ +
            ‖mulOp (fun x => χ x.1) hχm 1 hχb' gs‖ := norm_add_le _ _
        _ ≤ C' * ‖v‖ + ‖gs‖ := by
            gcongr
            · exact (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mulOp_le hC'0) (norm_nonneg _))
            · exact hmulb gs
        _ ≤ C' * C + C := by gcongr
        _ = (C' + 1) * C := by ring
    have n2 : ‖wt‖ ≤ C := (hmulb gt).trans hgt
    gcongr
  -- Parseval for the cut-off functions
  have hPar : ∀ v : Lp ℝ 2 cyl, HasSum (fun p : ℤ × ℤ =>
      ‖bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v) x : ℂ))
        p.1 p.2‖ ^ 2)
      ((2 * R + 4)⁻¹ * ∫ x, ‖(((mulOp (fun x => χ x.1) hχm 1 hχb' v) x : ℝ) : ℂ)‖ ^ 2
        ∂box (-R - 2) (2 * R + 4)) :=
    fun v => hasSum_bc hT0 (memLp_box (Lp.memLp _))
  -- linearity of the coefficients
  have hlin : ∀ (v₁ v₂ : Lp ℝ 2 cyl) (p : ℤ × ℤ),
      bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' (v₁ - v₂)) x : ℂ))
        p.1 p.2 =
      bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v₁) x : ℂ)) p.1 p.2 -
      bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v₂) x : ℂ))
        p.1 p.2 := by
    intro v₁ v₂ p
    rw [← bc_sub ((memLp_box (Lp.memLp _)).integrable one_le_two)
      ((memLp_box (Lp.memLp _)).integrable one_le_two)]
    unfold bc
    congr 1
    refine integral_congr_ae ?_
    rw [box_eq]
    refine ae_restrict_of_ae ?_
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (mulOp (fun x => χ x.1) hχm 1 hχb' v₁)
      (mulOp (fun x => χ x.1) hχm 1 hχb' v₂)] with x hx
    simp only [hx, Pi.sub_apply, Complex.ofReal_sub]
  -- apply the coordinate criterion
  refine totallyBounded_image_of_coords (cutR R) fun ε hε => ?_
  have hM0 : 0 ≤ (2 * R + 4) * (((C' + 1) * C) ^ 2 + C ^ 2) := by
    by_cases hC : 0 ≤ C
    · positivity
    · positivity
  obtain ⟨N, hN, η, hη, hlt⟩ := exists_N_eta hT0 hM0 hε
  refine ⟨sqN N → ℂ, inferInstance, inferInstance,
    fun v p => bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v) x : ℂ))
      p.1.1 p.1.2, η, hη, ?_, ?_⟩
  · -- boundedness of the coordinates
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.sqrt ((2 * R + 4)⁻¹ * C ^ 2), ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun p => ?_
    obtain ⟨gs, gt, -, -, hvC, -, -⟩ := hv
    refine Real.le_sqrt_of_sq_le ?_
    have h1 := le_hasSum (hPar v) p.1 (fun _ _ => sq_nonneg _)
    refine h1.trans ?_
    gcongr
    calc ∫ x, ‖(((mulOp (fun x => χ x.1) hχm 1 hχb' v) x : ℝ) : ℂ)‖ ^ 2
          ∂box (-R - 2) (2 * R + 4)
        ≤ ∫ x, (mulOp (fun x => χ x.1) hχm 1 hχb' v) x ^ 2 ∂cyl := integral_sq_box_le (Lp.memLp _)
      _ = ‖mulOp (fun x => χ x.1) hχm 1 hχb' v‖ ^ 2 := (norm_sq_eq_integral _).symm
      _ ≤ C ^ 2 := by
          gcongr
          exact (hmulb v).trans hvC
  · -- the estimate
    intro v₁ hv₁ v₂ hv₂ hd
    obtain ⟨hS₁, hM₁⟩ := hM v₁ hv₁
    obtain ⟨hS₂, hM₂⟩ := hM v₂ hv₂
    have hcoord : ∀ p ∈ sqN N,
        ‖bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v₁) x : ℂ)) p.1 p.2 -
          bc (-R - 2) (2 * R + 4) (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' v₂) x : ℂ))
            p.1 p.2‖ < η := by
      intro p hp
      rw [dist_eq_norm] at hd
      have := (norm_le_pi_norm _ ⟨p, hp⟩).trans_lt hd
      simpa using this
    have htail := tsum_sub_le hN hS₁ hM₁ hS₂ hM₂ (hPar v₁).summable (hPar v₂).summable hcoord
    have hP12 := hPar (v₁ - v₂)
    have hcut' : ‖cutR R v₁ - cutR R v₂‖ ^ 2 ≤ (2 * R + 4) *
        ∑' p : ℤ × ℤ, ‖bc (-R - 2) (2 * R + 4)
          (fun x => ((mulOp (fun x => χ x.1) hχm 1 hχb' (v₁ - v₂)) x : ℂ)) p.1 p.2‖ ^ 2 := by
      rw [← map_sub, hP12.tsum_eq, ← mul_assoc, mul_inv_cancel₀ hT0.ne', one_mul]
      exact norm_cutR_sq_le (by linarith) (by linarith) (fun s hs => (hχ1 s hs).1) hχm hχb' _
    simp_rw [hlin] at hcut'
    have hfin := hcut'.trans (mul_le_mul_of_nonneg_left htail hT0.le)
    rw [dist_eq_norm]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 (hfin.trans_lt hlt)

end Polyfold.GapP1Sobolev
