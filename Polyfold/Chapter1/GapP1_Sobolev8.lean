import Polyfold.Chapter1.GapP1_Sobolev7

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 8: the Leibniz rule

For a smooth function `χ` of `s` and a family `G a b` of weak derivatives `∂_s^a ∂_t^b`
of `G 0 0`, the product `χ G 0 0` has the weak derivatives
`∂_s^a ∂_t^b (χ G₀₀) = ∑_{i ≤ a} C(a,i) χ^{(i)} G (a-i) b` (`leibniz`).
Integrability is only needed against test functions (`LocL`), so the rule applies both to
elements of `H^{m,δ}` and to smooth `t`-periodic functions.
-/

open MeasureTheory Set Filter Topology Finset
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-- `g φ` is integrable for every test function `φ`. -/
def LocL (g : ℝ × ℝ → ℝ) : Prop := ∀ φ, IsTest φ → Integrable (fun x => g x * φ x) cyl

lemma locL_of_memLp {g : ℝ × ℝ → ℝ} (h : MemLp g 2 cyl) : LocL g := fun _ hφ => hφ.integrable_mul h

lemma SmPer.locL {F : ℝ × ℝ → ℝ} (h : SmPer F) : LocL F := fun _ hφ =>
  memLp_one_iff_integrable.1 ((hφ.mul_smPer h).memLp 1)

lemma LocL.add {g g' : ℝ × ℝ → ℝ} (h : LocL g) (h' : LocL g') : LocL (fun x => g x + g' x) :=
  fun φ hφ => ((h φ hφ).add (h' φ hφ)).congr (ae_of_all _ fun x => by simp only [Pi.add_apply]; ring)

lemma LocL.const_mul {g : ℝ × ℝ → ℝ} (h : LocL g) (c : ℝ) : LocL (fun x => c * g x) :=
  fun φ hφ => ((h φ hφ).const_mul c).congr (ae_of_all _ fun x => by simp only; ring)

lemma LocL.mul_s {g : ℝ × ℝ → ℝ} (h : LocL g) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    LocL (fun x => χ x.1 * g x) :=
  fun φ hφ => (h _ (hφ.mul_s hχ)).congr (ae_of_all _ fun x => by simp only; ring)

lemma LocL.zero : LocL (fun _ => 0) := fun φ _ => by simp

lemma LocL.sum {ι : Type*} (s : Finset ι) {g : ι → ℝ × ℝ → ℝ} (h : ∀ i ∈ s, LocL (g i)) :
    LocL (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocL.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))

lemma HasWeakDeriv.add' {a b : ℕ} {u g u' g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g)
    (h' : HasWeakDeriv a b u' g') (hu : LocL u) (hu' : LocL u') (hg : LocL g) (hg' : LocL g') :
    HasWeakDeriv a b (fun x => u x + u' x) (fun x => g x + g' x) := fun φ hφ => by
  have e1 : ∀ x, (u x + u' x) * pD a b φ x = u x * pD a b φ x + u' x * pD a b φ x :=
    fun x => by ring
  have e2 : ∀ x, (g x + g' x) * φ x = g x * φ x + g' x * φ x := fun x => by ring
  simp_rw [e1, e2]
  rw [integral_add (hu _ (hφ.pD a b)) (hu' _ (hφ.pD a b)), integral_add (hg _ hφ) (hg' _ hφ),
    h φ hφ, h' φ hφ]
  ring

lemma HasWeakDeriv.sum {a b : ℕ} {ι : Type*} (s : Finset ι) {u g : ι → ℝ × ℝ → ℝ}
    (h : ∀ i ∈ s, HasWeakDeriv a b (u i) (g i)) (hu : ∀ i ∈ s, LocL (u i))
    (hg : ∀ i ∈ s, LocL (g i)) :
    HasWeakDeriv a b (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun φ _ => by simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (mem_insert_self _ _)).add'
      (ih (fun i hi => h i (mem_insert_of_mem hi)) (fun i hi => hu i (mem_insert_of_mem hi))
        (fun i hi => hg i (mem_insert_of_mem hi)))
      (hu j (mem_insert_self _ _)) (LocL.sum s fun i hi => hu i (mem_insert_of_mem hi))
      (hg j (mem_insert_self _ _)) (LocL.sum s fun i hi => hg i (mem_insert_of_mem hi))

lemma HasWeakDeriv.congr_fun {a b : ℕ} {u g g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g)
    (e : ∀ x, g x = g' x) : HasWeakDeriv a b u g' :=
  h.congr_ae (ae_eq_refl _) (ae_of_all _ e)

/-- Product rule in `s` under local integrability. -/
lemma HasWeakDeriv.mul_s' {g h : ℝ × ℝ → ℝ} (hh : HasWeakDeriv 1 0 g h) (hg : LocL g)
    (hh2 : LocL h) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    HasWeakDeriv 1 0 (fun x => χ x.1 * g x) (fun x => deriv χ x.1 * g x + χ x.1 * h x) :=
  fun φ hφ => by
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at hh ⊢
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hDs := Ds_mul_s hφd hχd
  have e1 : ∀ x, χ x.1 * g x * Ds φ x
      = g x * Ds (fun y => χ y.1 * φ y) x - g x * (deriv χ x.1 * φ x) := by
    intro x; rw [hDs]; ring
  have hχ' : ContDiff ℝ ∞ (deriv χ) := hχ.iterate_deriv 1
  have i1 : Integrable (fun x => g x * Ds (fun y => χ y.1 * φ y) x) cyl :=
    hg _ (hφ.mul_s hχ).ds
  have i2 : Integrable (fun x => g x * (deriv χ x.1 * φ x)) cyl := hg _ (hφ.mul_s hχ')
  have hh' := hh _ (hφ.mul_s hχ)
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at hh'
  simp_rw [e1]
  rw [integral_sub i1 i2, hh']
  have e2 : ∀ x, (deriv χ x.1 * g x + χ x.1 * h x) * φ x
      = g x * (deriv χ x.1 * φ x) + h x * (χ x.1 * φ x) := by intro x; ring
  simp_rw [e2]
  rw [integral_add i2 (hh2 _ (hφ.mul_s hχ))]
  ring

lemma contDiff_iteratedDeriv {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (i : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv i χ) := by
  rw [iteratedDeriv_eq_iterate]; exact hχ.iterate_deriv i

/-- The Leibniz expression `∑_{i ≤ a} C(a,i) χ^{(i)}(s) G (a-i) b`. -/
def leib (χ : ℝ → ℝ) (G : ℕ → ℕ → ℝ × ℝ → ℝ) (a b : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ i ∈ range (a + 1), (a.choose i : ℝ) * (iteratedDeriv i χ x.1 * G (a - i) b x)

lemma leib_zero (χ : ℝ → ℝ) (G : ℕ → ℕ → ℝ × ℝ → ℝ) (b : ℕ) (x : ℝ × ℝ) :
    leib χ G 0 b x = χ x.1 * G 0 b x := by
  simp [leib]

lemma leib_succ (χ : ℝ → ℝ) (G : ℕ → ℕ → ℝ × ℝ → ℝ) (a b : ℕ) (x : ℝ × ℝ) :
    leib χ G (a + 1) b x = ∑ i ∈ range (a + 1), (a.choose i : ℝ) *
      (iteratedDeriv (i + 1) χ x.1 * G (a - i) b x + iteratedDeriv i χ x.1 * G (a - i + 1) b x) := by
  have := Finset.sum_choose_succ_mul (R := ℝ) (fun i j => iteratedDeriv i χ x.1 * G j b x) a
  simp only [leib]
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [show a + 1 - i = a - i + 1 by omega]
  ring

lemma LocL.leib {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {G : ℕ → ℕ → ℝ × ℝ → ℝ} {m : ℕ}
    (hL : ∀ a b, a + b ≤ m → LocL (G a b)) {a b : ℕ} (hab : a + b ≤ m) : LocL (leib χ G a b) :=
  LocL.sum _ fun i hi => ((hL _ _ (by have := Finset.mem_range.1 hi; omega)).mul_s
    (contDiff_iteratedDeriv hχ i)).const_mul _

/-- Leibniz rule for weak derivatives and a smooth function of `s`. -/
theorem leibniz {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {G : ℕ → ℕ → ℝ × ℝ → ℝ} {m : ℕ}
    (hL : ∀ a b, a + b ≤ m → LocL (G a b))
    (hs : ∀ a b, a + 1 + b ≤ m → HasWeakDeriv 1 0 (G a b) (G (a + 1) b))
    (ht : ∀ b, b + 1 ≤ m → HasWeakDeriv 0 1 (G 0 b) (G 0 (b + 1))) :
    ∀ a b, a + b ≤ m → HasWeakDeriv a b (fun x => χ x.1 * G 0 0 x) (leib χ G a b) := by
  have base : ∀ b, b ≤ m → HasWeakDeriv 0 b (fun x => χ x.1 * G 0 0 x) (leib χ G 0 b) := by
    intro b
    induction b with
    | zero => intro _; exact (hasWeakDeriv_zero _).congr_fun fun x => (leib_zero _ _ _ x).symm
    | succ b ih =>
      intro hb
      have h1 := (ht b (by omega)).mul_s_t hχ
      exact ((ih (by omega)).congr_fun (leib_zero χ G b)).succ_t h1 |>.congr_fun
        fun x => (leib_zero _ _ _ x).symm
  intro a
  induction a with
  | zero => intro b hb; exact base b (by omega)
  | succ a ih =>
    intro b hab
    have h0 := ih b (by omega)
    refine h0.succ_s ?_ |>.congr_fun fun x => (leib_succ χ G a b x).symm
    refine HasWeakDeriv.sum (range (a + 1)) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · have hi' : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hm := (hs (a - i) b (by omega)).mul_s' (hL _ _ (by omega)) (hL _ _ (by omega))
        (contDiff_iteratedDeriv hχ i)
      refine (hm.const_mul (a.choose i : ℝ)).congr_fun fun x => ?_
      rw [← iteratedDeriv_succ]
    · have hi' : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      exact ((hL _ _ (by omega)).mul_s (contDiff_iteratedDeriv hχ i)).const_mul _
    · have hi' : i ≤ a := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      exact (((hL _ _ (by omega)).mul_s (contDiff_iteratedDeriv hχ (i + 1))).add
        ((hL _ _ (by omega)).mul_s (contDiff_iteratedDeriv hχ i))).const_mul _

end Polyfold.GapP1Sobolev
