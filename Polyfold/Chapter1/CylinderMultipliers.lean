import Polyfold.Chapter1.CylinderLeibniz

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 9: smooth multipliers

Multiplication by a smooth function `χ(s)` whose derivatives up to order `m` are bounded
(`Mult m χ`) maps `H^{m,δ}(ℝ × S¹)` into itself (`mulH`), and the weak derivatives of `χ u`
are given by the Leibniz rule (`dv_mulH`). Also two norm estimates used for density.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- A pointwise bound by a finite sum of `L²` functions bounds the norm. -/
lemma norm_le_sum_of_ae {ι : Type*} (e : Lp ℝ 2 cyl) (s : Finset ι) (F : ι → Lp ℝ 2 cyl)
    (h : ∀ᵐ x ∂cyl, |e x| ≤ ∑ j ∈ s, ‖F j x‖) : ‖e‖ ≤ ∑ j ∈ s, ‖F j‖ := by
  rw [Lp.norm_def]
  have h1 : eLpNorm e 2 cyl ≤ eLpNorm (∑ j ∈ s, fun x => ‖F j x‖) 2 cyl := by
    apply eLpNorm_mono_ae
    filter_upwards [h] with x hx
    simp only [Real.norm_eq_abs, Finset.sum_apply]
    exact (by simpa only [Real.norm_eq_abs] using hx : |e x| ≤ ∑ j ∈ s, |F j x|).trans
      (le_abs_self _)
  have h2 := eLpNorm_sum_le (μ := cyl) (p := 2) (s := s) (f := fun j x => ‖F j x‖)
    (fun j _ => (Lp.aestronglyMeasurable (F j)).norm) (by norm_num)
  simp only [eLpNorm_norm] at h2
  have hne : ∀ j ∈ s, eLpNorm (F j) 2 cyl ≠ ⊤ := fun j _ => Lp.eLpNorm_ne_top _
  calc (eLpNorm e 2 cyl).toReal
      ≤ (∑ j ∈ s, eLpNorm (F j) 2 cyl).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne) (h1.trans h2)
    _ = ∑ j ∈ s, ‖F j‖ := by
        rw [ENNReal.toReal_sum hne]; rfl

/-- `‖u‖_{m,δ} ≤ ∑_p ‖e^{δ|s|} ∂^p u‖`. -/
lemma norm_H_le_sum (v : H m hδ) : ‖v‖ ≤ ∑ p : idx m, ‖wdv (H.toSub v) p‖ := by
  have hS : 0 ≤ ∑ p : idx m, ‖wdv (H.toSub v) p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hS two_ne_zero).1 ?_
  rw [norm_sq_H, sq]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun p => ‖wdv (H.toSub v) p‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ p)) (norm_nonneg _)

/-! ### The family of weak derivatives of an element -/

/-- `∂_s^a ∂_t^b u` for `a + b ≤ m`, and `0` otherwise. -/
def Gu (u : Hsub m hδ) (a b : ℕ) : ℝ × ℝ → ℝ :=
  if h : a + b ≤ m then dv u ⟨(a, b), mem_idx.2 h⟩ else 0

lemma Gu_of (u : Hsub m hδ) {a b : ℕ} (h : a + b ≤ m) :
    Gu u a b = dv u ⟨(a, b), mem_idx.2 h⟩ := dif_pos h

lemma Gu_hwd (u : Hsub m hδ) {a b : ℕ} (h : a + b ≤ m) :
    HasWeakDeriv a b (u : Lp ℝ 2 cyl) (Gu u a b) := by
  rw [Gu_of u h]; exact (dv_spec u ⟨(a, b), mem_idx.2 h⟩).1

lemma Gu_wt (u : Hsub m hδ) (a b : ℕ) : MemLp (fun x => wt δ x * Gu u a b x) 2 cyl := by
  by_cases h : a + b ≤ m
  · rw [Gu_of u h]; exact (dv_spec u _).2
  · simp only [Gu, h, dite_false, Pi.zero_apply, mul_zero]; exact MemLp.zero

lemma Gu_memLp (u : Hsub m hδ) (a b : ℕ) : MemLp (Gu u a b) 2 cyl :=
  memLp_of_weighted hδ (Gu_wt u a b)

lemma Gu_s (u : Hsub m hδ) {a b : ℕ} (h : a + 1 + b ≤ m) :
    HasWeakDeriv 1 0 (Gu u a b) (Gu u (a + 1) b) :=
  (Gu_hwd u (by omega)).of_succ_s (Gu_hwd u h)

lemma Gu_t (u : Hsub m hδ) {b : ℕ} (h : b + 1 ≤ m) :
    HasWeakDeriv 0 1 (Gu u 0 b) (Gu u 0 (b + 1)) :=
  (Gu_hwd u (by omega)).of_succ_t (Gu_hwd u (by omega))

lemma Gu_zero (u : Hsub m hδ) : Gu u 0 0 =ᵐ[cyl] (u : Lp ℝ 2 cyl) := by
  rw [Gu_of u (by omega)]; exact dv_idx0 u

/-! ### Multipliers -/

/-- `χ` is smooth with derivatives up to order `m` bounded by `C`. -/
structure Mult (m : ℕ) (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  bdd : ∃ C, ∀ i ≤ m, ∀ s, |iteratedDeriv i χ s| ≤ C

lemma Mult.bound {χ : ℝ → ℝ} (h : Mult m χ) : ∃ C, ∀ s, |χ s| ≤ C := by
  obtain ⟨C, hC⟩ := h.bdd
  exact ⟨C, fun s => by simpa using hC 0 (Nat.zero_le _) s⟩

/-- Multiplication by `χ(s)` on `L²`. -/
def mulχ (χ : ℝ → ℝ) (h : Mult m χ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  mulOp (fun x => χ x.1) ((h.smooth.continuous.comp continuous_fst).aestronglyMeasurable)
    h.bound.choose (fun x => h.bound.choose_spec x.1)

lemma coeFn_mulχ (χ : ℝ → ℝ) (h : Mult m χ) (f : Lp ℝ 2 cyl) :
    mulχ χ h f =ᵐ[cyl] fun x => χ x.1 * f x := coeFn_mulOp _ _ _ _ f

lemma Mult.memLp_wt_leib {χ : ℝ → ℝ} (h : Mult m χ) {G : ℕ → ℕ → ℝ × ℝ → ℝ}
    (hG : ∀ a b, MemLp (fun x => wt δ x * G a b x) 2 cyl) {a b : ℕ} (hab : a ≤ m) :
    MemLp (fun x => wt δ x * leib χ G a b x) 2 cyl := by
  obtain ⟨C, hC⟩ := h.bdd
  have e : (fun x => wt δ x * leib χ G a b x) = fun x => ∑ i ∈ range (a + 1),
      (a.choose i : ℝ) * (iteratedDeriv i χ x.1 * (wt δ x * G (a - i) b x)) := by
    funext x; simp only [leib, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine memLp_finsetSum _ fun i hi => ?_
  have hi' : i ≤ m := by have := Finset.mem_range.1 hi; omega
  exact (memLp_mul (((contDiff_iteratedDeriv h.smooth i).continuous.comp
    continuous_fst).aestronglyMeasurable) (fun x => hC i hi' x.1) (hG _ _)).const_mul _

lemma mulχ_hwd {χ : ℝ → ℝ} (h : Mult m χ) (u : Hsub m hδ) {a b : ℕ} (hab : a + b ≤ m) :
    HasWeakDeriv a b (mulχ χ h u) (leib χ (Gu u) a b) := by
  have hl := leibniz h.smooth (fun a b _ => locL_of_memLp (Gu_memLp u a b)) (fun a b h => Gu_s u h)
    (fun b h => Gu_t u h) a b hab
  refine hl.congr_ae ?_ (ae_eq_refl _)
  filter_upwards [Gu_zero u, coeFn_mulχ χ h u] with x h1 h2
  rw [h2, h1]

lemma mulχ_mem {χ : ℝ → ℝ} (h : Mult m χ) (u : Hsub m hδ) : mulχ χ h u ∈ Hsub m hδ :=
  fun a b hab => ⟨_, mulχ_hwd h u hab, h.memLp_wt_leib (Gu_wt u) (by omega)⟩

/-- `χ u ∈ H^{m,δ}` for `u ∈ H^{m,δ}`. -/
def mulH (χ : ℝ → ℝ) (h : Mult m χ) (u : H m hδ) : H m hδ :=
  (⟨mulχ χ h (H.toSub u), mulχ_mem h (H.toSub u)⟩ : Hsub m hδ)

lemma dv_mulH {χ : ℝ → ℝ} (h : Mult m χ) (u : H m hδ) (p : idx m) :
    dv (H.toSub (mulH χ h u)) p =ᵐ[cyl] leib χ (Gu (H.toSub u)) p.1.1 p.1.2 :=
  dv_unique _ p (mulχ_hwd h (H.toSub u) (mem_idx.1 p.2))
    (memLp_of_weighted hδ (h.memLp_wt_leib (Gu_wt _) (by have := mem_idx.1 p.2; omega)))

end Polyfold.GapP1Sobolev
