import Polyfold.Chapter1.CylinderScBanach

/-!
# Subsection 1.4.4 (2021, p. 17): the sc-Hilbert space `L²(ℝ)` with `E_m = H^{m,δ_m}(ℝ)`

2021 Subsection 1.4.4, p. 18, and Appendix 7.6.3, p. 348: for a strictly increasing sequence
`0 = δ₀ < δ₁ < ⋯`, the Hilbert space `E = L²(ℝ)` carries the sc-structure `E_m = H^{m,δ_m}(ℝ)`,
the maps with weak derivatives up to order `m` which, weighted by `e^{δ_m |s|}`, are in `L²(ℝ)`.

We build it from Example 1.1.3 (`GapP1_Sobolev*`, the cylinder `ℝ × S¹`), through the isometry
`f ↦ f ∘ pr₁ : L²(ℝ) → L²(ℝ × S¹)` (`liftC`):

* `Hsub1 m hδ` is the space of `f ∈ L²(ℝ)` whose lift lies in `H^{m,δ}(ℝ × S¹)`, normed by the
  norm of the lift (`H1`, `liftH` an isometry).  A function of `s` alone has `∂_t`-derivatives `0`,
  so this is the norm `∑_{a ≤ m} ‖e^{δ|s|} ∂_s^a f‖²` of `H^{m,δ}(ℝ)`.
* the averaging operator `𝒜 = liftC ∘ liftC*` (the adjoint is the average over `t ∈ (0,1]`) maps
  `H^{m,δ}(ℝ × S¹)` to itself with norm `≤ 1` (`avgH`), and sends test functions of the cylinder to
  lifts of test functions of the line (`avgC_toLp`, `isTest_avgFun`).
* `H1` is complete (`completeSpace_H1`), the inclusions `H1 (m+1) δ' → H1 m δ` (`δ < δ'`) are
  compact (`isCompactOperator_incl1`), and lifts of averaged test functions are dense in every level
  (`dense_smooth1`); `lineSc δ h0 hmono` is the sc-Hilbert space of Subsection 1.4.4.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal InnerProductSpace

noncomputable section

namespace Polyfold.ZhouLine

open Polyfold.GapP1Sobolev

/-! ### The lift `L²(ℝ) → L²(ℝ × S¹)` -/

/-- Lebesgue measure on `(0,1]`, the circle factor of `cyl`. -/
abbrev νS : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure νS := ⟨by simp [Real.volume_Ioc]⟩

lemma measurePreserving_fst_cyl : MeasurePreserving Prod.fst cyl (volume : Measure ℝ) :=
  measurePreserving_fst

/-- `f ↦ f ∘ pr₁`, `L²(ℝ) → L²(ℝ × S¹)`, a linear isometry. -/
def liftI : Lp ℝ 2 (volume : Measure ℝ) →ₗᵢ[ℝ] Lp ℝ 2 cyl :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst_cyl

/-- The lift as a continuous linear map. -/
def liftC : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 cyl := liftI.toContinuousLinearMap

lemma coeFn_liftC (f : Lp ℝ 2 (volume : Measure ℝ)) : liftC f =ᵐ[cyl] fun x => f x.1 :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_fst_cyl

lemma norm_liftC (f : Lp ℝ 2 (volume : Measure ℝ)) : ‖liftC f‖ = ‖f‖ := liftI.norm_map f

lemma inner_liftC (f g : Lp ℝ 2 (volume : Measure ℝ)) : ⟪liftC f, liftC g⟫_ℝ = ⟪f, g⟫_ℝ :=
  liftI.inner_map_map f g

lemma liftC_injective : Function.Injective liftC := liftI.injective

/-- The average over the circle, `liftC*`. -/
def avgC : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) := ContinuousLinearMap.adjoint liftC

lemma inner_avgC (u : Lp ℝ 2 cyl) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ⟪avgC u, f⟫_ℝ = ⟪u, liftC f⟫_ℝ := ContinuousLinearMap.adjoint_inner_left _ _ _

lemma avgC_liftC (f : Lp ℝ 2 (volume : Measure ℝ)) : avgC (liftC f) = f :=
  ext_inner_right ℝ fun g => by rw [inner_avgC, inner_liftC]

lemma norm_avgC_le : ‖avgC‖ ≤ 1 := by
  rw [avgC, LinearIsometryEquiv.norm_map]
  exact liftI.norm_toContinuousLinearMap_le

/-- `𝒜 = liftC ∘ avgC`, the orthogonal projection onto the functions of `s` alone. -/
def avgL : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl := liftC.comp avgC

lemma avgL_liftC (f : Lp ℝ 2 (volume : Measure ℝ)) : avgL (liftC f) = liftC f := by
  rw [avgL, ContinuousLinearMap.comp_apply, avgC_liftC]

lemma inner_avgL (u v : Lp ℝ 2 cyl) : ⟪avgL u, v⟫_ℝ = ⟪u, avgL v⟫_ℝ := by
  rw [avgL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, real_inner_comm,
    ← inner_avgC, real_inner_comm, inner_avgC]

lemma norm_avgL_le : ‖avgL‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_one₀ liftI.norm_toContinuousLinearMap_le (norm_nonneg _) norm_avgC_le)

/-! ### Averages of functions over the circle -/

/-- The average `s ↦ ∫_{(0,1]} φ(s,t) dt`. -/
def avgFun (φ : ℝ × ℝ → ℝ) (s : ℝ) : ℝ := ∫ t, φ (s, t) ∂νS

/-- A function of `s`, viewed on the cylinder. -/
def liftFun (g : ℝ → ℝ) : ℝ × ℝ → ℝ := fun x => g x.1

lemma cyl_eq : cyl = (volume : Measure ℝ).prod νS := rfl

lemma continuous_slice {φ : ℝ × ℝ → ℝ} (h : Continuous φ) (s : ℝ) :
    Continuous fun t => φ (s, t) :=
  h.comp (continuous_const.prodMk continuous_id)

lemma integrable_slice {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (s : ℝ) :
    Integrable (fun t => φ (s, t)) νS := by
  obtain ⟨C, hC⟩ := h.bounded
  exact Integrable.of_bound (continuous_slice h.smooth.continuous s).aestronglyMeasurable C
    (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hC (s, t))

lemma hasDerivAt_avgFun {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (s : ℝ) :
    HasDerivAt (avgFun φ) (avgFun (Ds φ) s) s := by
  obtain ⟨C, hC⟩ := h.ds.bounded
  have hd : Differentiable ℝ φ := h.smooth.differentiable (by simp)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := νS) (F := fun s t => φ (s, t))
    (F' := fun s t => Ds φ (s, t)) (bound := fun _ => C) (x₀ := s) Filter.univ_mem
    (Eventually.of_forall fun x => (continuous_slice h.smooth.continuous x).aestronglyMeasurable)
    (integrable_slice h s) (continuous_slice h.ds.smooth.continuous s).aestronglyMeasurable
    (ae_of_all _ fun t x _ => by simpa [Real.norm_eq_abs] using hC (x, t))
    (integrable_const C) (ae_of_all _ fun t x _ => hasDerivAt_s hd x t)).2

lemma deriv_avgFun {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : deriv (avgFun φ) = avgFun (Ds φ) :=
  funext fun s => (hasDerivAt_avgFun h s).deriv

lemma differentiable_avgFun {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : Differentiable ℝ (avgFun φ) :=
  fun s => (hasDerivAt_avgFun h s).differentiableAt

lemma contDiff_avgFun_nat : ∀ (n : ℕ) {φ : ℝ × ℝ → ℝ}, IsTest φ → ContDiff ℝ n (avgFun φ)
  | 0, φ, h => contDiff_zero.2 (differentiable_avgFun h).continuous
  | n + 1, φ, h => by
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by push_cast; rfl, contDiff_succ_iff_deriv]
    refine ⟨differentiable_avgFun h, fun h' => absurd h' (by simp), ?_⟩
    rw [deriv_avgFun h]
    exact contDiff_avgFun_nat n h.ds

lemma contDiff_avgFun {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : ContDiff ℝ ∞ (avgFun φ) :=
  contDiff_infty.2 fun n => contDiff_avgFun_nat n h

lemma avgFun_eq_zero {φ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ s t, R < |s| → φ (s, t) = 0) {s : ℝ}
    (hs : R < |s|) : avgFun φ s = 0 := by
  simp [avgFun, hR s _ hs]

/-- The average of `∂_t χ` vanishes (periodicity). -/
lemma avgFun_Dt {χ : ℝ × ℝ → ℝ} (h : IsTest χ) : avgFun (Dt χ) = 0 := by
  funext s
  have hd : Differentiable ℝ χ := h.smooth.differentiable (by simp)
  rw [avgFun, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => χ (s, t))
      (fun t _ => hasDerivAt_t hd s t)
      ((continuous_slice h.dt.smooth.continuous s).intervalIntegrable 0 1)]
  have := h.periodic s 0
  rw [zero_add] at this
  simp [this]

lemma hasFDerivAt_liftFun {g : ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    HasFDerivAt (liftFun g) ((fderiv ℝ g x.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
  (hg x.1).hasFDerivAt.comp x hasFDerivAt_fst

lemma Ds_liftFun {g : ℝ → ℝ} (hg : Differentiable ℝ g) : Ds (liftFun g) = liftFun (deriv g) := by
  funext x
  simp [Ds, (hasFDerivAt_liftFun hg x).fderiv, liftFun]

lemma Dt_liftFun {g : ℝ → ℝ} (hg : Differentiable ℝ g) : Dt (liftFun g) = 0 := by
  funext x
  simp [Dt, (hasFDerivAt_liftFun hg x).fderiv]

lemma isTest_liftFun {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : ∀ s, R < |s| → g s = 0) :
    IsTest (liftFun g) :=
  ⟨hg.comp contDiff_fst, fun _ _ => rfl, ⟨R, fun s _ hs => hR s hs⟩⟩

lemma isTest_liftAvg {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : IsTest (liftFun (avgFun φ)) := by
  obtain ⟨R, hR⟩ := h.bddSupp
  exact isTest_liftFun (contDiff_avgFun h) fun s hs => avgFun_eq_zero hR hs

lemma iterate_Ds_liftAvg : ∀ (a : ℕ) {ψ : ℝ × ℝ → ℝ}, IsTest ψ →
    Ds^[a] (liftFun (avgFun ψ)) = liftFun (avgFun (Ds^[a] ψ))
  | 0, _, _ => rfl
  | a + 1, ψ, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_Ds_liftAvg a h,
      Ds_liftFun (differentiable_avgFun (h.iterate_ds a)), deriv_avgFun (h.iterate_ds a)]

lemma iterate_Dt_liftAvg : ∀ (b : ℕ) {φ : ℝ × ℝ → ℝ}, IsTest φ →
    Dt^[b] (liftFun (avgFun φ)) = liftFun (avgFun (Dt^[b] φ))
  | 0, _, _ => rfl
  | b + 1, φ, h => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_Dt_liftAvg b h,
      Dt_liftFun (differentiable_avgFun (h.iterate_dt b)), avgFun_Dt (h.iterate_dt b)]
    rfl

/-- `∂_s^a ∂_t^b` of the averaged lift is the lift of the average of `∂_s^a ∂_t^b φ`. -/
lemma pD_liftAvg {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (a b : ℕ) :
    pD a b (liftFun (avgFun φ)) = liftFun (avgFun (pD a b φ)) := by
  rw [pD, iterate_Dt_liftAvg b h, iterate_Ds_liftAvg a (h.iterate_dt b)]
  rfl

lemma avgFun_pD_succ_t {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (a b : ℕ) :
    avgFun (pD a (b + 1) φ) = 0 := by
  have e : pD a (b + 1) (liftFun (avgFun φ)) = 0 := by
    rw [pD, Function.iterate_succ_apply', iterate_Dt_liftAvg b h,
      Dt_liftFun (differentiable_avgFun (h.iterate_dt b))]
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x; simp [Ds]
  rw [pD_liftAvg h] at e
  funext s
  exact congrFun e (s, 0)

/-! ### `avgC` on test functions -/

lemma inner_toLp_left {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℝ}
    (hφ : MemLp φ 2 μ) (f : Lp ℝ 2 μ) : ⟪hφ.toLp φ, f⟫_ℝ = ∫ x, f x * φ x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hφ] with x hx
  rw [hx, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

lemma memLp_avgFun {φ : ℝ × ℝ → ℝ} (h : IsTest φ) : MemLp (avgFun φ) 2 volume := by
  obtain ⟨R, hR⟩ := h.bddSupp
  refine (differentiable_avgFun h).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs => ?_)
  refine avgFun_eq_zero hR ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with hs | hs
  · rw [lt_abs]; right; linarith
  · rw [lt_abs]; left; exact hs

/-- The average over the circle of a test function `φ` is `s ↦ ∫ φ(s,t) dt`. -/
theorem avgC_toLp {φ : ℝ × ℝ → ℝ} (h : IsTest φ) :
    avgC ((h.memLp 2).toLp φ) = (memLp_avgFun h).toLp (avgFun φ) := by
  refine ext_inner_right ℝ fun k => ?_
  rw [inner_avgC, inner_toLp_left, inner_toLp_left]
  have hint : Integrable (fun x : ℝ × ℝ => k x.1 * φ x) cyl := by
    have := (Lp.memLp (liftC k)).integrable_mul (h.memLp 2)
    exact this.congr (by filter_upwards [coeFn_liftC k] with x hx; simp only [Pi.mul_apply, hx])
  calc ∫ x, liftC k x * φ x ∂cyl = ∫ x, k x.1 * φ x ∂cyl :=
        integral_congr_ae (by filter_upwards [coeFn_liftC k] with x hx; rw [hx])
    _ = ∫ s, ∫ t, k s * φ (s, t) ∂νS ∂volume := by
        rw [cyl_eq] at hint ⊢; exact integral_prod _ hint
    _ = ∫ s, k s * avgFun φ s := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only [avgFun]; exact integral_const_mul _ _

lemma liftC_toLp {g : ℝ → ℝ} (hg : MemLp g 2 volume) (hg' : MemLp (liftFun g) 2 cyl) :
    liftC (hg.toLp g) = hg'.toLp (liftFun g) := by
  refine Lp.ext ?_
  have h1 := coeFn_liftC (hg.toLp g)
  have h2 : (fun x : ℝ × ℝ => (hg.toLp g) x.1) =ᵐ[cyl] liftFun g :=
    measurePreserving_fst_cyl.quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hg)
  filter_upwards [h1, h2, MemLp.coeFn_toLp hg'] with x e1 e2 e3
  rw [e1, e2, e3]

/-- `𝒜` on a test function `φ` of the cylinder is the lift of its average, again a test function. -/
theorem avgL_toLp {φ : ℝ × ℝ → ℝ} (h : IsTest φ) :
    avgL ((h.memLp 2).toLp φ) = ((isTest_liftAvg h).memLp 2).toLp (liftFun (avgFun φ)) := by
  rw [avgL, ContinuousLinearMap.comp_apply, avgC_toLp h, liftC_toLp]

/-! ### Multiplication by `e^{-δ|s|}` commutes with the average -/

section MulOp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_mulG {c : α → ℝ} (hc : AEStronglyMeasurable c μ) {C : ℝ}
    (hb : ∀ x, |c x| ≤ C) {f : α → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun x => c x * f x) 2 μ :=
  hf.of_le_mul (hc.mul hf.1) (ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _))

/-- Multiplication by a bounded measurable function on `L²(μ)`. -/
def mulG (c : α → ℝ) (hc : AEStronglyMeasurable c μ) (C : ℝ) (hb : ∀ x, |c x| ≤ C) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mulG hc hb (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add (memLp_mulG hc hb (Lp.memLp f)) (memLp_mulG hc hb (Lp.memLp g))]
        apply (MemLp.toLp_eq_toLp_iff _ _).2
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := fun r f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul r (memLp_mulG hc hb (Lp.memLp f))]
        apply (MemLp.toLp_eq_toLp_iff _ _).2
        filter_upwards [Lp.coeFn_smul r f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul]; ring }
    C (fun f => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (memLp_mulG hc hb (Lp.memLp f))] with x hx
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _))

lemma coeFn_mulG (c : α → ℝ) (hc : AEStronglyMeasurable c μ) (C : ℝ) (hb : ∀ x, |c x| ≤ C)
    (f : Lp ℝ 2 μ) : mulG c hc C hb f =ᵐ[μ] fun x => c x * f x :=
  MemLp.coeFn_toLp (memLp_mulG hc hb (Lp.memLp f))

lemma inner_mulG (c : α → ℝ) (hc : AEStronglyMeasurable c μ) (C : ℝ) (hb : ∀ x, |c x| ≤ C)
    (f g : Lp ℝ 2 μ) : ⟪mulG c hc C hb f, g⟫_ℝ = ⟪f, mulG c hc C hb g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulG c hc C hb f, coeFn_mulG c hc C hb g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end MulOp

/-- `e^{-δ|s|}` on the line. -/
def wt1 (δ : ℝ) (s : ℝ) : ℝ := Real.exp (δ * |s|)

lemma continuous_wt1 (δ : ℝ) : Continuous (wt1 δ) := by unfold wt1; fun_prop

lemma abs_wt1_neg_le {δ : ℝ} (h : 0 ≤ δ) (s : ℝ) : |wt1 (-δ) s| ≤ 1 := by
  rw [wt1, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [abs_nonneg s]

/-- `e^{-δ|s|}·` on `L²(ℝ × S¹)`. -/
abbrev Mc {δ : ℝ} (hδ : 0 ≤ δ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  mulG (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)

/-- `e^{-δ|s|}·` on `L²(ℝ)`. -/
abbrev Mc1 {δ : ℝ} (hδ : 0 ≤ δ) : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  mulG (wt1 (-δ)) (continuous_wt1 _).aestronglyMeasurable 1 (abs_wt1_neg_le hδ)

lemma Mc_liftC {δ : ℝ} (hδ : 0 ≤ δ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Mc hδ (liftC f) = liftC (Mc1 hδ f) := by
  refine Lp.ext ?_
  have h2 : (fun x : ℝ × ℝ => (Mc1 hδ f) x.1) =ᵐ[cyl] fun x => wt1 (-δ) x.1 * f x.1 :=
    measurePreserving_fst_cyl.quasiMeasurePreserving.ae_eq_comp (coeFn_mulG _ _ _ _ f)
  filter_upwards [coeFn_mulG (μ := cyl) _ _ _ _ (liftC f), coeFn_liftC f, coeFn_liftC (Mc1 hδ f),
    h2] with x e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  rfl

lemma avgC_Mc {δ : ℝ} (hδ : 0 ≤ δ) (v : Lp ℝ 2 cyl) : avgC (Mc hδ v) = Mc1 hδ (avgC v) :=
  ext_inner_right ℝ fun g => by
    rw [inner_avgC, inner_mulG, Mc_liftC hδ, ← inner_avgC, inner_mulG]

lemma avgL_Mc {δ : ℝ} (hδ : 0 ≤ δ) (v : Lp ℝ 2 cyl) : avgL (Mc hδ v) = Mc hδ (avgL v) := by
  simp only [avgL, ContinuousLinearMap.comp_apply]
  rw [avgC_Mc, Mc_liftC]

/-- If `e^{δ|s|} G = W ∈ L²`, then `e^{δ|s|} 𝒜G = 𝒜W`. -/
lemma wt_mul_avgL {δ : ℝ} (hδ : 0 ≤ δ) {G W : Lp ℝ 2 cyl}
    (hGW : (fun x => wt δ x * G x) =ᵐ[cyl] W) :
    (fun x => wt δ x * avgL G x) =ᵐ[cyl] avgL W := by
  have hG : G = Mc hδ W := by
    refine Lp.ext ?_
    filter_upwards [coeFn_mulG (μ := cyl) _ _ _ _ W, hGW] with x e1 e2
    rw [e1, ← e2, ← mul_assoc, wt_neg_mul, one_mul]
  rw [hG, avgL_Mc]
  filter_upwards [coeFn_mulG (μ := cyl) _ _ _ _ (avgL W)] with x e1
  rw [e1, ← mul_assoc, mul_comm (wt δ x), wt_neg_mul, one_mul]

/-! ### `𝒜` on `H^{m,δ}(ℝ × S¹)` -/

/-- Moving `𝒜` onto a test function. -/
lemma integral_avgL_mul {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (v : Lp ℝ 2 cyl) :
    ∫ x, avgL v x * φ x ∂cyl = ∫ x, v x * liftFun (avgFun φ) x ∂cyl := by
  rw [← inner_toLp_left (h.memLp 2), ← inner_toLp_left ((isTest_liftAvg h).memLp 2),
    real_inner_comm, inner_avgL, avgL_toLp h, real_inner_comm]

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma hasWeakDeriv_avgL_zero (u : Hsub m hδ) (p : idx m) (hp : p.1.2 = 0) :
    HasWeakDeriv p.1.1 0 (avgL (u : Lp ℝ 2 cyl))
      (avgL ((dv_memLp u p).toLp (dv u p)) : ℝ × ℝ → ℝ) := by
  intro φ hφ
  have hΨ := isTest_liftAvg hφ
  rw [integral_avgL_mul (hφ.pD _ _), ← pD_liftAvg hφ, integral_avgL_mul hφ]
  have e := (dv_spec u p).1 _ hΨ
  rw [hp] at e
  rw [e]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (dv_memLp u p)] with x hx
  rw [hx]

lemma hasWeakDeriv_avgL_succ (u : Hsub m hδ) (a b : ℕ) :
    HasWeakDeriv a (b + 1) (avgL (u : Lp ℝ 2 cyl)) 0 := by
  intro φ hφ
  rw [integral_avgL_mul (hφ.pD _ _), avgFun_pD_succ_t hφ]
  simp [liftFun]

/-- `𝒜` maps `H^{m,δ}(ℝ × S¹)` into itself. -/
theorem avgL_mem_Hsub (u : Hsub m hδ) : avgL (u : Lp ℝ 2 cyl) ∈ Hsub m hδ := by
  intro a b hab
  rcases b with _ | b
  · set p : idx m := ⟨(a, 0), mem_idx.2 hab⟩
    refine ⟨_, hasWeakDeriv_avgL_zero u p rfl, ?_⟩
    refine (Lp.memLp (avgL (wdv u p))).ae_eq (wt_mul_avgL hδ ?_).symm
    filter_upwards [MemLp.coeFn_toLp (dv_memLp u p), coeFn_wdv u p] with x e1 e2
    rw [e1, e2]
  · exact ⟨0, hasWeakDeriv_avgL_succ u a b, by simp⟩

/-- `‖e^{δ|s|} ∂^p 𝒜u‖ ≤ ‖e^{δ|s|} ∂^p u‖`. -/
lemma norm_wdv_avgL_le (u : Hsub m hδ) (p : idx m) :
    ‖wdv (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) p‖ ≤ ‖wdv u p‖ := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  rcases b with _ | b
  · have hd := dv_unique (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) ⟨(a, 0), hp⟩
      (hasWeakDeriv_avgL_zero u ⟨(a, 0), hp⟩ rfl) (Lp.memLp _)
    have hw := wt_mul_avgL hδ (G := (dv_memLp u ⟨(a, 0), hp⟩).toLp _) (W := wdv u ⟨(a, 0), hp⟩)
      (by filter_upwards [MemLp.coeFn_toLp (dv_memLp u ⟨(a, 0), hp⟩),
            coeFn_wdv u ⟨(a, 0), hp⟩] with x e1 e2; rw [e1, e2])
    have he : wdv (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) ⟨(a, 0), hp⟩ = avgL (wdv u ⟨(a, 0), hp⟩) := by
      refine Lp.ext ?_
      filter_upwards [coeFn_wdv (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) ⟨(a, 0), hp⟩, hd, hw]
        with x e1 e2 e3
      rw [e1, e2, e3]
    rw [he]
    exact (avgL.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) norm_avgL_le)
  · have hd := dv_unique (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) ⟨(a, b + 1), hp⟩
      (hasWeakDeriv_avgL_succ u a b) MemLp.zero
    have he : wdv (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) ⟨(a, b + 1), hp⟩ = 0 := by
      refine Lp.ext ?_
      filter_upwards [coeFn_wdv (⟨_, avgL_mem_Hsub u⟩ : Hsub m hδ) ⟨(a, b + 1), hp⟩, hd,
        Lp.coeFn_zero ℝ 2 cyl] with x e1 e2 e3
      rw [e1, e2, e3]; simp
    rw [he, norm_zero]; exact norm_nonneg _

/-- `𝒜` on `H^{m,δ}(ℝ × S¹)`, of norm `≤ 1`. -/
def avgH (m : ℕ) (hδ : 0 ≤ δ) : H m hδ →L[ℝ] H m hδ :=
  LinearMap.mkContinuous
    { toFun := fun u => Hsub.toH ⟨_, avgL_mem_Hsub (H.toSub u)⟩
      map_add' := fun u v => Subtype.ext (map_add avgL _ _)
      map_smul' := fun c u => Subtype.ext (map_smul avgL c _) } 1
    (fun u => by
      rw [one_mul]
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      rw [norm_sq_H, norm_sq_H]
      exact Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _)
        (norm_wdv_avgL_le (H.toSub u) p) 2)

lemma valCLM_avgH (u : H m hδ) : valCLM m hδ (avgH m hδ u) = avgL (valCLM m hδ u) := rfl

/-! ### The spaces `H^{m,δ}(ℝ)` -/

/-- `H^{m,δ}(ℝ)` inside `L²(ℝ)`: the `f` whose lift `f ∘ pr₁` lies in `H^{m,δ}(ℝ × S¹)`.  A function
of `s` has weak derivatives `∂_t = 0`, so this is the space of the `f ∈ L²(ℝ)` with weak
derivatives `∂_s^a f`, `a ≤ m`, in `L²(ℝ)` after weighting by `e^{δ|s|}`. -/
def Hsub1 (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  (Hsub m hδ).comap (liftC : Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 cyl)

/-- `H^{m,δ}(ℝ)`, normed by `‖f‖ = ‖f ∘ pr₁‖_{H^{m,δ}(ℝ × S¹)}`, i.e.
`‖f‖² = ∑_{a ≤ m} ‖e^{δ|s|} ∂_s^a f‖²_{L²(ℝ)}`. -/
def H1 (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : Type := Hsub1 m hδ

instance : AddCommGroup (H1 m hδ) := inferInstanceAs (AddCommGroup (Hsub1 m hδ))

instance : Module ℝ (H1 m hδ) := inferInstanceAs (Module ℝ (Hsub1 m hδ))

/-- The element of `Hsub1` underlying `f : H1`. -/
def H1.toSub (f : H1 m hδ) : Hsub1 m hδ := f

/-- The underlying element of `L²(ℝ)`. -/
def H1.val (f : H1 m hδ) : Lp ℝ 2 (volume : Measure ℝ) := (H1.toSub f : Lp ℝ 2 volume)

/-- The lift `H^{m,δ}(ℝ) → H^{m,δ}(ℝ × S¹)` as a linear map. -/
def liftL (m : ℕ) (hδ : 0 ≤ δ) : H1 m hδ →ₗ[ℝ] H m hδ where
  toFun f := Hsub.toH ⟨liftC (H1.val f), (H1.toSub f).2⟩
  map_add' f g := Subtype.ext (map_add liftC (H1.val f) (H1.val g))
  map_smul' c f := Subtype.ext (map_smul liftC c (H1.val f))

lemma liftL_injective : Function.Injective (liftL m hδ) := fun f g h => by
  have h' : liftC (H1.val f) = liftC (H1.val g) := congrArg (fun u : H m hδ => valCLM m hδ u) h
  exact Subtype.ext (liftC_injective h')

instance : NormedAddCommGroup (H1 m hδ) :=
  NormedAddCommGroup.induced (H1 m hδ) (H m hδ) (liftL m hδ) liftL_injective

instance : NormedSpace ℝ (H1 m hδ) := NormedSpace.induced ℝ (H1 m hδ) (H m hδ) (liftL m hδ)

/-- The lift `H^{m,δ}(ℝ) → H^{m,δ}(ℝ × S¹)`, an isometry. -/
def liftH (m : ℕ) (hδ : 0 ≤ δ) : H1 m hδ →L[ℝ] H m hδ :=
  LinearMap.mkContinuous (liftL m hδ) 1 fun f => by rw [one_mul]; rfl

lemma norm_liftH (f : H1 m hδ) : ‖liftH m hδ f‖ = ‖f‖ := rfl

lemma isometry_liftH : Isometry (liftH m hδ) :=
  AddMonoidHomClass.isometry_of_norm _ norm_liftH

lemma valCLM_liftH (f : H1 m hδ) : valCLM m hδ (liftH m hδ f) = liftC (H1.val f) := rfl

lemma H1.val_injective : Function.Injective (H1.val (m := m) (hδ := hδ)) := fun _ _ h =>
  Subtype.ext h

lemma isClosed_range_liftC : IsClosed (range liftC) :=
  (liftI.isometry.isClosedEmbedding).isClosed_range

lemma range_liftH : range (liftH m hδ) = valCLM m hδ ⁻¹' range liftC := by
  ext u
  constructor
  · rintro ⟨f, rfl⟩; exact ⟨H1.val f, rfl⟩
  · rintro ⟨f, hf⟩
    have hf' : f ∈ Hsub1 m hδ := by
      change liftC f ∈ Hsub m hδ
      rw [hf]; exact (H.toSub u).2
    refine ⟨((⟨f, hf'⟩ : Hsub1 m hδ) : H1 m hδ), valCLM_injective ?_⟩
    exact hf

/-- **`H^{m,δ}(ℝ)` is a Hilbert space** (complete). -/
instance completeSpace_H1 : CompleteSpace (H1 m hδ) := by
  rw [completeSpace_iff_isComplete_range isometry_liftH.isUniformInducing, range_liftH]
  exact (isClosed_range_liftC.preimage (valCLM m hδ).continuous).isComplete

lemma isClosedEmbedding_liftH : Topology.IsClosedEmbedding (liftH m hδ) :=
  isometry_liftH.isClosedEmbedding

/-! ### Inclusions -/

lemma Hsub1_mono {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') : Hsub1 m' hδ' ≤ Hsub1 m hδ := fun _ hf => Hsub_mono hδ hδ' hm hδδ hf

/-- The inclusion `H^{m',δ'}(ℝ) → H^{m,δ}(ℝ)` for `m ≤ m'`, `δ ≤ δ'`. -/
def incl1 {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m') (hδδ : δ ≤ δ') :
    H1 m' hδ' →L[ℝ] H1 m hδ :=
  LinearMap.mkContinuous (Submodule.inclusion (Hsub1_mono hδ hδ' hm hδδ)) 1 fun f => by
    rw [one_mul]
    exact norm_inclL_le hδ hδ' hm hδδ (liftH m' hδ' f)

lemma val_incl1 {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m') (hδδ : δ ≤ δ')
    (f : H1 m' hδ') : H1.val (incl1 hδ hδ' hm hδδ f) = H1.val f := rfl

lemma liftH_incl1 {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') (f : H1 m' hδ') :
    liftH m hδ (incl1 hδ hδ' hm hδδ f) = inclH hδ hδ' hm hδδ (liftH m' hδ' f) := rfl

lemma incl1_injective {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m ≤ m')
    (hδδ : δ ≤ δ') : Function.Injective (incl1 hδ hδ' hm hδδ) := fun f g h =>
  H1.val_injective (by rw [← val_incl1 hδ hδ' hm hδδ f, h, val_incl1])

/-- **The inclusions `H^{m+1,δ'}(ℝ) → H^{m,δ}(ℝ)`, `δ < δ'`, are compact.** -/
theorem isCompactOperator_incl1 {m : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hlt : δ < δ') :
    IsCompactOperator (incl1 hδ hδ' (Nat.le_succ m) hlt.le) := by
  obtain ⟨K, hK, hK0⟩ := isCompactOperator_inclH (m := m) hδ hδ' hlt
  refine ⟨liftH m hδ ⁻¹' K, isClosedEmbedding_liftH.isCompact_preimage hK, ?_⟩
  have : incl1 hδ hδ' (Nat.le_succ m) hlt.le ⁻¹' (liftH m hδ ⁻¹' K) =
      liftH (m + 1) hδ' ⁻¹' (inclH hδ hδ' (Nat.le_succ m) hlt.le ⁻¹' K) := rfl
  rw [this]
  exact (liftH (m + 1) hδ').continuous.continuousAt.preimage_mem_nhds (by simpa using hK0)

/-! ### Density of test functions -/

/-- The element of `H^{m,δ}(ℝ)` given by a function `g` of `s` whose lift is a test function. -/
def ofTest1 (m : ℕ) (hδ : 0 ≤ δ) {g : ℝ → ℝ} (hg : IsTest (liftFun g)) (hg1 : MemLp g 2 volume) :
    H1 m hδ :=
  ((⟨hg1.toLp g, show liftC _ ∈ Hsub m hδ by
    rw [liftC_toLp hg1 (hg.memLp 2)]; exact hg.mem_Hsub m hδ⟩ : Hsub1 m hδ) : H1 m hδ)

lemma val_ofTest1 {g : ℝ → ℝ} (hg : IsTest (liftFun g)) (hg1 : MemLp g 2 volume) :
    H1.val (ofTest1 m hδ hg hg1) = hg1.toLp g := rfl

lemma liftH_ofTest1 {g : ℝ → ℝ} (hg : IsTest (liftFun g)) (hg1 : MemLp g 2 volume) :
    liftH m hδ (ofTest1 m hδ hg hg1) = toH m hδ hg :=
  valCLM_injective (liftC_toLp hg1 (hg.memLp 2))

lemma avgH_liftH (f : H1 m hδ) : avgH m hδ (liftH m hδ f) = liftH m hδ f :=
  valCLM_injective (avgL_liftC (H1.val f))

lemma avgH_toH {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    avgH m hδ (toH m hδ hφ) = liftH m hδ (ofTest1 m hδ (isTest_liftAvg hφ) (memLp_avgFun hφ)) :=
  valCLM_injective ((avgL_toLp hφ).trans (liftC_toLp (memLp_avgFun hφ) _).symm)

/-- **The functions of `s` alone whose lifts are test functions are dense in `H^{m,δ}(ℝ)`**:
average the test functions of the cylinder approximating the lift (`dense_test`, `avgH`). -/
theorem dense_ofTest1 (m : ℕ) (hδ : 0 ≤ δ) :
    Dense {f : H1 m hδ | ∃ (g : ℝ → ℝ) (hg : IsTest (liftFun g)) (hg1 : MemLp g 2 volume),
      f = ofTest1 m hδ hg hg1} := by
  rw [Metric.dense_iff]
  intro f ε hε
  obtain ⟨_, hu, ⟨φ, hφ, rfl⟩⟩ := Metric.dense_iff.1 (dense_test m hδ) (liftH m hδ f) ε hε
  refine ⟨ofTest1 m hδ (isTest_liftAvg hφ) (memLp_avgFun hφ), ?_, _, _, _, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm, ← norm_liftH, map_sub, ← avgH_toH hφ, ← avgH_liftH f,
    ← map_sub]
  rw [Metric.mem_ball, dist_eq_norm] at hu
  exact ((avgH m hδ).le_opNorm _).trans_lt
    (lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (LinearMap.mkContinuous_norm_le _
      zero_le_one _)) hu)

/-! ### The sc-structure of Subsection 1.4.4 -/

/-- The scale `E_m = H^{m,δ_m}(ℝ)`. -/
def lineScale (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) : ScScale where
  lvl m := H1 m (nonneg_of_strictMono h0 hmono m)
  incl m := incl1 (nonneg_of_strictMono h0 hmono m) (nonneg_of_strictMono h0 hmono (m + 1))
    (Nat.le_succ m) (hmono (Nat.lt_succ_self m)).le
  incl_injective _ := incl1_injective _ _ _ _
  incl_isCompactOperator m := isCompactOperator_incl1 _ _ (hmono (Nat.lt_succ_self m))

lemma val_toBase (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) :
    ∀ (m : ℕ) (f : lineScale δ h0 hmono m),
      H1.val ((lineScale δ h0 hmono).toBase m f) = H1.val (show H1 m _ from f)
  | 0, _ => rfl
  | m + 1, _ => val_toBase δ h0 hmono m _

lemma toBase_ofTest1 (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) (m : ℕ) {g : ℝ → ℝ}
    (hg : IsTest (liftFun g)) (hg1 : MemLp g 2 volume) :
    (lineScale δ h0 hmono).toBase m (ofTest1 m (nonneg_of_strictMono h0 hmono m) hg hg1) =
      ofTest1 0 (nonneg_of_strictMono h0 hmono 0) hg hg1 :=
  H1.val_injective (val_toBase δ h0 hmono m _)

/-- **Subsection 1.4.4 (2021, p. 18)**: for `δ₀ = 0 < δ₁ < δ₂ < ⋯`, the filtration
`E_m = H^{m,δ_m}(ℝ)` is an sc-structure on `E = L²(ℝ)` (level `0` is `L²(ℝ)`: `level0_line`).
Each level is a Hilbert space, the inclusions are compact, and the smooth points are dense. -/
def lineSc (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) : ScBanach where
  toScScale := lineScale δ h0 hmono
  dense_smooth m := by
    refine (dense_ofTest1 m (nonneg_of_strictMono h0 hmono m)).mono ?_
    rintro _ ⟨g, hg, hg1, rfl⟩
    refine (lineScale δ h0 hmono).mem_smoothLvl_iff.2 fun j =>
      ⟨ofTest1 j (nonneg_of_strictMono h0 hmono j) hg hg1, ?_⟩
    rw [toBase_ofTest1, toBase_ofTest1]

lemma lineSc_lvl (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) (m : ℕ) :
    (lineSc δ h0 hmono).lvl m = H1 m (nonneg_of_strictMono h0 hmono m) := rfl

/-- **Level `0` of `lineSc` is `L²(ℝ)`**: for `δ = 0`, `f ↦ f` is an isometry of `H^{0,0}(ℝ)` onto
`L²(ℝ)`. -/
theorem level0_line {δ : ℝ} (hδ : 0 ≤ δ) (h : δ = 0) :
    Isometry (H1.val (m := 0) (hδ := hδ)) ∧ Function.Surjective (H1.val (m := 0) (hδ := hδ)) := by
  refine ⟨AddMonoidHomClass.isometry_of_norm
    ({ toFun := H1.val, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      H1 0 hδ →+ Lp ℝ 2 (volume : Measure ℝ)) fun f => ?_, fun g => ?_⟩
  · change ‖H1.val f‖ = ‖f‖
    rw [← norm_liftH, ← (level0_isometry hδ h).norm_map_of_map_zero (map_zero _), valCLM_liftH,
      norm_liftC]
  · obtain ⟨u, hu⟩ := level0_surjective hδ h (liftC g)
    have hg : g ∈ Hsub1 0 hδ := by
      change liftC g ∈ Hsub 0 hδ
      rw [← hu]; exact (H.toSub u).2
    exact ⟨((⟨g, hg⟩ : Hsub1 0 hδ) : H1 0 hδ), rfl⟩

end Polyfold.ZhouLine
