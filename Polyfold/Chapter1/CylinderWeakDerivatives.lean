import Mathlib

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 1: the cylinder, test functions and
weak derivatives

Example 1.1.3 (2021) equips `E = L²(ℝ × S¹)` with the scale `E_m = H^{m,δ_m}(ℝ × S¹)`: the
elements of `E` whose weak partial derivatives up to order `m`, weighted by `e^{δ_m |s|}`, belong
to `E`, for a strictly increasing sequence `0 = δ_0 < δ_1 < ⋯`.

This file sets up the objects in that sentence.

* `S¹ = ℝ/ℤ`, and the cylinder `ℝ × S¹` with its Lebesgue measure is realised on the strip
  `ℝ × (0,1]`: `cyl` is the product of Lebesgue measure on `ℝ` and Lebesgue measure on `(0,1]`.
  A function on the cylinder is a function of `(s,t) ∈ ℝ × ℝ`, of which only the values on the
  strip enter the integrals.
* The test functions `C_c^∞(ℝ × S¹)` are the smooth functions of `(s,t)` which are `1`-periodic in
  `t` and vanish for large `|s|` (`IsTest`).
* `Ds`, `Dt` are the partial derivatives `∂_s`, `∂_t`, and `pD a b = ∂_s^a ∂_t^b`.
* `HasWeakDeriv a b u g`: `g` is the weak derivative `∂_s^a ∂_t^b u`, i.e.
  `∫ u · ∂_s^a ∂_t^b φ = (-1)^{a+b} ∫ g · φ` for every test function `φ`.

We prove the first-order calculus: test functions are bounded and in every `Lᵖ`, the operations
`∂_s`, `∂_t` and multiplication by a smooth function of `s` preserve test functions, `∂_s` and `∂_t`
commute, weak derivatives compose (`HasWeakDeriv.succ_s`, `HasWeakDeriv.succ_t`), and the product
rule for multiplication by a smooth function of `s` (`HasWeakDeriv.mul_s`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-! ### The cylinder -/

/-- Lebesgue measure on the cylinder `ℝ × S¹` (`S¹ = ℝ/ℤ`), realised on the strip `ℝ × (0,1]`. -/
def cyl : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume.restrict (Ioc (0 : ℝ) 1))

instance : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.2 (by simp)

instance : SFinite cyl := by unfold cyl; infer_instance

lemma cyl_slab (a b : ℝ) : cyl (Icc a b ×ˢ (univ : Set ℝ)) = ENNReal.ofReal (b - a) := by
  rw [cyl, Measure.prod_prod]; simp

instance (a b : ℝ) : IsFiniteMeasure (cyl.restrict (Icc a b ×ˢ (univ : Set ℝ))) :=
  ⟨by rw [Measure.restrict_apply_univ, cyl_slab]; exact ENNReal.ofReal_lt_top⟩

/-! ### Partial derivatives -/

/-- `∂_s φ`. -/
def Ds (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun x => fderiv ℝ φ x (1, 0)

/-- `∂_t φ`. -/
def Dt (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun x => fderiv ℝ φ x (0, 1)

/-- `∂_s^a ∂_t^b φ`. -/
def pD (a b : ℕ) (φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := Ds^[a] (Dt^[b] φ)

lemma contDiff_Ds {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Ds φ) :=
  (h.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_Dt {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Dt φ) :=
  (h.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_iterate_Ds {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) : ∀ a, ContDiff ℝ ∞ (Ds^[a] φ)
  | 0 => h
  | a + 1 => by
    rw [Function.iterate_succ_apply']; exact contDiff_Ds (contDiff_iterate_Ds h a)

lemma contDiff_iterate_Dt {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) : ∀ b, ContDiff ℝ ∞ (Dt^[b] φ)
  | 0 => h
  | b + 1 => by
    rw [Function.iterate_succ_apply']; exact contDiff_Dt (contDiff_iterate_Dt h b)

lemma contDiff_pD {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) (a b : ℕ) : ContDiff ℝ ∞ (pD a b φ) :=
  contDiff_iterate_Ds (contDiff_iterate_Dt h b) a

/-- `∂_s φ (s,t)` is the derivative of `s ↦ φ(s,t)`. -/
lemma hasDerivAt_s {φ : ℝ × ℝ → ℝ} (h : Differentiable ℝ φ) (s t : ℝ) :
    HasDerivAt (fun s' => φ (s', t)) (Ds φ (s, t)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => ((s', t) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact (h (s, t)).hasFDerivAt.comp_hasDerivAt s h1

/-- `∂_t φ (s,t)` is the derivative of `t ↦ φ(s,t)`. -/
lemma hasDerivAt_t {φ : ℝ × ℝ → ℝ} (h : Differentiable ℝ φ) (s t : ℝ) :
    HasDerivAt (fun t' => φ (s, t')) (Dt φ (s, t)) t := by
  have h1 : HasDerivAt (fun t' : ℝ => ((s, t') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact (h (s, t)).hasFDerivAt.comp_hasDerivAt t h1

/-- `∂_s ∂_t φ = ∂_t ∂_s φ` (Schwarz). -/
lemma Ds_Dt {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) : Ds (Dt φ) = Dt (Ds φ) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (h.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have key : ∀ v w : ℝ × ℝ,
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v = fderiv ℝ (fderiv ℝ φ) x v w := by
    intro v w
    rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  have hsymm : IsSymmSndFDerivAt ℝ φ x :=
    (h.contDiffAt).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  show fderiv ℝ (fun y => fderiv ℝ φ y (0, 1)) x (1, 0)
    = fderiv ℝ (fun y => fderiv ℝ φ y (1, 0)) x (0, 1)
  rw [key, key]
  exact hsymm _ _

lemma Ds_iterate_Dt {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) :
    ∀ b, Ds (Dt^[b] φ) = Dt^[b] (Ds φ)
  | 0 => rfl
  | b + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Ds_Dt (contDiff_iterate_Dt h b), Ds_iterate_Dt h b]

lemma pD_succ_s {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) (a b : ℕ) :
    pD (a + 1) b φ = pD a b (Ds φ) := by
  simp only [pD]
  rw [Function.iterate_succ_apply, Ds_iterate_Dt h b]

lemma pD_succ_t (φ : ℝ × ℝ → ℝ) (a b : ℕ) : pD a (b + 1) φ = pD a b (Dt φ) := by
  simp only [pD, Function.iterate_succ_apply]

@[simp] lemma pD_zero (φ : ℝ × ℝ → ℝ) : pD 0 0 φ = φ := rfl

/-! ### Test functions -/

/-- The test functions `C_c^∞(ℝ × S¹)`: smooth, `1`-periodic in `t`, vanishing for large `|s|`. -/
structure IsTest (φ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ s t, φ (s, t + 1) = φ (s, t)
  bddSupp : ∃ R, ∀ s t, R < |s| → φ (s, t) = 0

lemma periodic_fderiv {φ : ℝ × ℝ → ℝ} (hp : ∀ s t, φ (s, t + 1) = φ (s, t)) (x : ℝ × ℝ) :
    fderiv ℝ φ (x + (0, 1)) = fderiv ℝ φ x := by
  have : (fun y => φ (y + ((0 : ℝ), (1 : ℝ)))) = φ := by
    funext y; obtain ⟨s, t⟩ := y; simpa using hp s t
  rw [← fderiv_comp_add_right, this]

lemma fderiv_eq_zero_of_bdd {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ s t, R < |s| → φ (s, t) = 0)
    {x : ℝ × ℝ} (hx : R < |x.1|) : fderiv ℝ φ x = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | R < |y.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have : φ =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    obtain ⟨s, t⟩ := y; exact hR s t hy
  rw [this.fderiv_eq]; simp

lemma IsTest.ds {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : IsTest (Ds φ) where
  smooth := contDiff_Ds h.smooth
  periodic s t := by
    simp only [Ds]
    have := periodic_fderiv h.periodic (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [this]
  bddSupp := by
    obtain ⟨R, hR⟩ := h.bddSupp
    exact ⟨R, fun s t hs => by simp [Ds, fderiv_eq_zero_of_bdd hR (x := (s, t)) hs]⟩

lemma IsTest.dt {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : IsTest (Dt φ) where
  smooth := contDiff_Dt h.smooth
  periodic s t := by
    simp only [Dt]
    have := periodic_fderiv h.periodic (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    rw [this]
  bddSupp := by
    obtain ⟨R, hR⟩ := h.bddSupp
    exact ⟨R, fun s t hs => by simp [Dt, fderiv_eq_zero_of_bdd hR (x := (s, t)) hs]⟩

lemma IsTest.iterate_ds {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : ∀ a, IsTest (Ds^[a] φ)
  | 0 => h
  | a + 1 => by rw [Function.iterate_succ_apply']; exact (h.iterate_ds a).ds

lemma IsTest.iterate_dt {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : ∀ b, IsTest (Dt^[b] φ)
  | 0 => h
  | b + 1 => by rw [Function.iterate_succ_apply']; exact (h.iterate_dt b).dt

lemma IsTest.pD {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (a b : ℕ) : IsTest (pD a b φ) :=
  (h.iterate_dt b).iterate_ds a

lemma IsTest.periodic_int {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (s t : ℝ) :
    φ (s, Int.fract t) = φ (s, t) := by
  have hp : Function.Periodic (fun t => φ (s, t)) 1 := fun t => h.periodic s t
  have := hp.sub_int_mul_eq (x := t) (⌊t⌋)
  have e : Int.fract t = t - ⌊t⌋ * 1 := by rw [mul_one]; rfl
  rw [e]; exact this

lemma IsTest.bounded {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : ∃ C, ∀ x, |φ x| ≤ C := by
  obtain ⟨R, hR⟩ := h.bddSupp
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-R) R ×ˢ Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    h.smooth.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  obtain ⟨s, t⟩ := x
  by_cases hs : R < |s|
  · rw [hR s t hs]; simp
  · rw [← h.periodic_int]
    have hm : ((s, Int.fract t) : ℝ × ℝ) ∈ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
      refine ⟨?_, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
      exact abs_le.1 (not_lt.1 hs)
    exact (hC _ hm).trans (le_max_left _ _)

lemma IsTest.eq_indicator {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    φ = (Icc (-R) R ×ˢ (univ : Set ℝ)).indicator φ := by
  funext x
  by_cases hx : x ∈ Icc (-R) R ×ˢ (univ : Set ℝ)
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    obtain ⟨s, t⟩ := x
    apply hR
    simp only [mem_prod, mem_Icc, mem_univ, and_true] at hx
    rw [lt_abs]
    by_contra hc
    push Not at hc
    exact hx ⟨by linarith [hc.2], hc.1⟩

lemma IsTest.memLp {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (p : ℝ≥0∞) : MemLp φ p cyl := by
  obtain ⟨R, hR⟩ := h.bddSupp
  obtain ⟨C, hC⟩ := h.bounded
  have hS : MeasurableSet (Icc (-R) R ×ˢ (univ : Set ℝ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  rw [IsTest.eq_indicator hR, memLp_indicator_iff_restrict hS]
  exact MemLp.of_bound h.smooth.continuous.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

lemma IsTest.integrable_mul {φ u : ℝ × ℝ → ℝ} (h : IsTest φ) (hu : MemLp u 2 cyl) :
    Integrable (fun x => u x * φ x) cyl :=
  hu.integrable_mul (h.memLp 2)

lemma IsTest.add {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) : IsTest (φ + ψ) where
  smooth := hφ.smooth.add hψ.smooth
  periodic s t := by simp [hφ.periodic, hψ.periodic]
  bddSupp := by
    obtain ⟨R, hR⟩ := hφ.bddSupp
    obtain ⟨R', hR'⟩ := hψ.bddSupp
    exact ⟨max R R', fun s t hs => by
      simp [hR s t ((le_max_left _ _).trans_lt hs), hR' s t ((le_max_right _ _).trans_lt hs)]⟩

lemma IsTest.const_mul {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (c : ℝ) : IsTest (fun x => c * φ x) where
  smooth := contDiff_const.mul hφ.smooth
  periodic s t := by simp [hφ.periodic]
  bddSupp := by
    obtain ⟨R, hR⟩ := hφ.bddSupp
    exact ⟨R, fun s t hs => by simp [hR s t hs]⟩

/-- Multiplying a test function by a smooth function of `s` gives a test function. -/
lemma IsTest.mul_s {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    IsTest (fun x => χ x.1 * φ x) where
  smooth := (hχ.comp contDiff_fst).mul hφ.smooth
  periodic s t := by simp [hφ.periodic]
  bddSupp := by
    obtain ⟨R, hR⟩ := hφ.bddSupp
    exact ⟨R, fun s t hs => by simp [hR s t hs]⟩

lemma Ds_mul_s {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) {χ : ℝ → ℝ}
    (hχ : Differentiable ℝ χ) :
    Ds (fun x => χ x.1 * φ x) = fun x => deriv χ x.1 * φ x + χ x.1 * Ds φ x := by
  funext x
  obtain ⟨s, t⟩ := x
  have h1 : HasDerivAt (fun s' => χ s' * φ (s', t)) (deriv χ s * φ (s, t) + χ s * Ds φ (s, t)) s :=
    (hχ s).hasDerivAt.mul (hasDerivAt_s hφ s t)
  have h2 := hasDerivAt_s (φ := fun x => χ x.1 * φ x)
    ((hχ.comp differentiable_fst).mul hφ) s t
  exact h2.unique h1

lemma Dt_mul_s {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) {χ : ℝ → ℝ}
    (hχ : Differentiable ℝ χ) :
    Dt (fun x => χ x.1 * φ x) = fun x => χ x.1 * Dt φ x := by
  funext x
  obtain ⟨s, t⟩ := x
  have h1 : HasDerivAt (fun t' => χ s * φ (s, t')) (χ s * Dt φ (s, t)) t :=
    (hasDerivAt_t hφ s t).const_mul (χ s)
  have h2 := hasDerivAt_t (φ := fun x => χ x.1 * φ x)
    ((hχ.comp differentiable_fst).mul hφ) s t
  exact h2.unique h1

/-! ### Weak derivatives -/

/-- `g` is the weak derivative `∂_s^a ∂_t^b u` on the cylinder:
`∫ u · ∂_s^a ∂_t^b φ = (-1)^{a+b} ∫ g · φ` for every test function `φ`. -/
def HasWeakDeriv (a b : ℕ) (u g : ℝ × ℝ → ℝ) : Prop :=
  ∀ φ, IsTest φ → ∫ x, u x * pD a b φ x ∂cyl = (-1) ^ (a + b) * ∫ x, g x * φ x ∂cyl

lemma hasWeakDeriv_zero (u : ℝ × ℝ → ℝ) : HasWeakDeriv 0 0 u u := fun φ _ => by simp

lemma HasWeakDeriv.congr_ae {a b : ℕ} {u g u' g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g)
    (hu : u =ᵐ[cyl] u') (hg : g =ᵐ[cyl] g') : HasWeakDeriv a b u' g' := fun φ hφ => by
  have e1 : (fun x => u x * pD a b φ x) =ᵐ[cyl] fun x => u' x * pD a b φ x :=
    hu.mono fun x hx => by dsimp only; rw [hx]
  have e2 : (fun x => g x * φ x) =ᵐ[cyl] fun x => g' x * φ x :=
    hg.mono fun x hx => by dsimp only; rw [hx]
  rw [← integral_congr_ae e1, h φ hφ, integral_congr_ae e2]

lemma HasWeakDeriv.add {a b : ℕ} {u g u' g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g)
    (h' : HasWeakDeriv a b u' g') (hu : MemLp u 2 cyl) (hu' : MemLp u' 2 cyl)
    (hg : MemLp g 2 cyl) (hg' : MemLp g' 2 cyl) :
    HasWeakDeriv a b (u + u') (g + g') := fun φ hφ => by
  simp only [Pi.add_apply, add_mul]
  rw [integral_add ((hφ.pD a b).integrable_mul hu) ((hφ.pD a b).integrable_mul hu'),
    integral_add (hφ.integrable_mul hg) (hφ.integrable_mul hg'), h φ hφ, h' φ hφ, mul_add]

lemma HasWeakDeriv.const_mul {a b : ℕ} {u g : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g) (c : ℝ) :
    HasWeakDeriv a b (fun x => c * u x) (fun x => c * g x) := fun φ hφ => by
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ hφ]; ring

lemma HasWeakDeriv.neg {a b : ℕ} {u g : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g) :
    HasWeakDeriv a b (-u) (-g) := fun φ hφ => by
  have := h.const_mul (-1) φ hφ
  simpa [neg_one_mul] using this

lemma HasWeakDeriv.sub {a b : ℕ} {u g u' g' : ℝ × ℝ → ℝ} (h : HasWeakDeriv a b u g)
    (h' : HasWeakDeriv a b u' g') (hu : MemLp u 2 cyl) (hu' : MemLp u' 2 cyl)
    (hg : MemLp g 2 cyl) (hg' : MemLp g' 2 cyl) :
    HasWeakDeriv a b (u - u') (g - g') := by
  simpa [sub_eq_add_neg] using h.add h'.neg hu hu'.neg hg hg'.neg

lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp

/-- Weak derivatives compose in `s`: if `g = ∂_s^a ∂_t^b u` and `h = ∂_s g`, then
`h = ∂_s^{a+1} ∂_t^b u`. -/
lemma HasWeakDeriv.succ_s {a b : ℕ} {u g h : ℝ × ℝ → ℝ} (hg : HasWeakDeriv a b u g)
    (hh : HasWeakDeriv 1 0 g h) : HasWeakDeriv (a + 1) b u h := fun φ hφ => by
  rw [pD_succ_s hφ.smooth, hg _ hφ.ds]
  have := hh φ hφ
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at this
  rw [this]; ring

/-- Conversely, `∂_s` of `∂_s^a ∂_t^b u` is `∂_s^{a+1} ∂_t^b u`. -/
lemma HasWeakDeriv.of_succ_s {a b : ℕ} {u g h : ℝ × ℝ → ℝ} (hg : HasWeakDeriv a b u g)
    (hh : HasWeakDeriv (a + 1) b u h) : HasWeakDeriv 1 0 g h := fun φ hφ => by
  have h1 := hh φ hφ
  rw [pD_succ_s hφ.smooth, hg _ hφ.ds] at h1
  simp only [pD, Function.iterate_one, Function.iterate_zero, id]
  have h2 : ∫ x, g x * Ds φ x ∂cyl = (-1) ^ (a + b) * (-1) ^ (a + b) * ∫ x, g x * Ds φ x ∂cyl := by
    rw [neg_one_pow_mul_self, one_mul]
  rw [h2, mul_assoc, h1]
  have : ((-1 : ℝ) ^ (a + b)) * (-1) ^ (a + 1 + b) = (-1) ^ (1 + 0) * ((-1) ^ (a + b) * (-1) ^ (a + b)) := by
    ring
  rw [← mul_assoc, this, neg_one_pow_mul_self, mul_one]

lemma HasWeakDeriv.succ_t {a b : ℕ} {u g h : ℝ × ℝ → ℝ} (hg : HasWeakDeriv a b u g)
    (hh : HasWeakDeriv 0 1 g h) : HasWeakDeriv a (b + 1) u h := fun φ hφ => by
  rw [pD_succ_t, hg _ hφ.dt]
  have := hh φ hφ
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at this
  rw [this]; ring

lemma HasWeakDeriv.of_succ_t {a b : ℕ} {u g h : ℝ × ℝ → ℝ} (hg : HasWeakDeriv a b u g)
    (hh : HasWeakDeriv a (b + 1) u h) : HasWeakDeriv 0 1 g h := fun φ hφ => by
  have h1 := hh φ hφ
  rw [pD_succ_t, hg _ hφ.dt] at h1
  simp only [pD, Function.iterate_one, Function.iterate_zero, id]
  have h2 : ∫ x, g x * Dt φ x ∂cyl = (-1) ^ (a + b) * (-1) ^ (a + b) * ∫ x, g x * Dt φ x ∂cyl := by
    rw [neg_one_pow_mul_self, one_mul]
  rw [h2, mul_assoc, h1]
  have : ((-1 : ℝ) ^ (a + b)) * (-1) ^ (a + (b + 1)) = (-1) ^ (0 + 1) * ((-1) ^ (a + b) * (-1) ^ (a + b)) := by
    ring
  rw [← mul_assoc, this, neg_one_pow_mul_self, mul_one]

/-- Product rule for `∂_s` and a smooth function `χ` of `s`:
`∂_s (χ g) = χ' g + χ ∂_s g`. -/
lemma HasWeakDeriv.mul_s {g h : ℝ × ℝ → ℝ} (hh : HasWeakDeriv 1 0 g h) (hg : MemLp g 2 cyl)
    (hh2 : MemLp h 2 cyl) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
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
    (hφ.mul_s hχ).ds.integrable_mul hg
  have i2 : Integrable (fun x => g x * (deriv χ x.1 * φ x)) cyl :=
    (hφ.mul_s hχ').integrable_mul hg
  have hh' := hh _ (hφ.mul_s hχ)
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at hh'
  simp_rw [e1]
  rw [integral_sub i1 i2, hh']
  have e2 : ∀ x, (deriv χ x.1 * g x + χ x.1 * h x) * φ x
      = g x * (deriv χ x.1 * φ x) + h x * (χ x.1 * φ x) := by intro x; ring
  simp_rw [e2]
  rw [integral_add i2 ((hφ.mul_s hχ).integrable_mul hh2)]
  ring

/-- `∂_t (χ g) = χ ∂_t g` for a smooth function `χ` of `s`. -/
lemma HasWeakDeriv.mul_s_t {g h : ℝ × ℝ → ℝ} (hh : HasWeakDeriv 0 1 g h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    HasWeakDeriv 0 1 (fun x => χ x.1 * g x) (fun x => χ x.1 * h x) := fun φ hφ => by
  simp only [pD, Function.iterate_one, Function.iterate_zero, id] at hh ⊢
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have e1 : ∀ x, χ x.1 * g x * Dt φ x = g x * Dt (fun y => χ y.1 * φ y) x := by
    intro x; rw [Dt_mul_s hφd hχd]; ring
  have e2 : ∀ x, χ x.1 * h x * φ x = h x * (χ x.1 * φ x) := by intro x; ring
  simp_rw [e1, e2]
  exact hh _ (hφ.mul_s hχ)

end Polyfold.GapP1Sobolev
