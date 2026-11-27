import GWMemoir.LevelsNodesFredholm

/-!
# The reflection `u ↦ u(c - s, ϑ - t)` on `H^{m,δ}(ℝ × S¹)`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, p. 45 and p. 13.

At a nodal pair `{x, y}` the memoir writes the polar coordinates at `y` as `(s', t') ∈ ℝ⁻ × S¹`
and glues by `s' = s - R`, `t' = t - ϑ` (p. 45).  The neck blocks of the section and fibre spaces
use polar coordinates `(s, t) ∈ ℝ⁺ × S¹` at both points of the pair, so the half-cylinder at `y` is
read through the reflection `(s', t') ↦ (-s', -t')`, and the shift `τ` of the gluing becomes
`u ↦ u(R - s, ϑ - t)`.  This file provides that operator.

* `rfT c ϑ x = (c - s, ϑ - t)` in the strip coordinates `t ∈ (0, 1]`; it preserves the measure
  (`measurePreserving_rfT`) and is an involution (`rfT_rfT`).
* `HasWeakDeriv.comp_rfT`: the weak derivative `∂_s^a ∂_t^b` of `u ∘ rfT` is
  `(-1)^{a+b} (∂_s^a ∂_t^b u) ∘ rfT`.
* **`reflH c ϑ`**: `u ↦ u(c - s, ϑ - t)` on `H^{m,δ}(ℝ × S¹)`, an involution (`reflH_reflH`).
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-! ## 1. The reflection of the strip -/

/-- `(s, t) ↦ (c - s, ϑ - t)` in the strip coordinates of `ℝ × S¹`, `t ∈ (0, 1]`. -/
def rfT (c ϑ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (c - x.1, rot x.2 ϑ)

lemma measurePreserving_negRot (ϑ : ℝ) :
    MeasurePreserving (fun t => rot t ϑ) (volume.restrict (Ioc (0 : ℝ) 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h1 := AddCircle.measurePreserving_mk (1 : ℝ) 0
  have h2 := Measure.measurePreserving_sub_left (volume : Measure UnitAddCircle) (ϑ : UnitAddCircle)
  have h3 := AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0)
  have h4 := measurePreserving_subtype_coe (μa := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) (0 + 1))
    measurableSet_Ioc
  have := h4.comp (h3.comp (h2.comp h1))
  simp only [zero_add] at this
  exact this

lemma measurePreserving_rfT (c ϑ : ℝ) : MeasurePreserving (rfT c ϑ) cyl cyl :=
  (Measure.measurePreserving_sub_left (volume : Measure ℝ) c).prod (measurePreserving_negRot ϑ)

lemma rot_negRot {t : ℝ} (ϑ : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : rot (rot t ϑ) ϑ = t := by
  have h : ((rot (rot t ϑ) ϑ : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := by
    rw [rot_coe, rot_coe]; abel
  have h' := rot_coe 0 t
  rw [AddCircle.coe_zero, sub_zero, ← rot_of_mem ht] at h'
  have hm := rot_mem (rot t ϑ) ϑ
  have ht' : t ∈ Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  have hm' : rot (rot t ϑ) ϑ ∈ Ioc (0 : ℝ) (0 + 1) := by simpa using hm
  have := (AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) hm').symm
  rw [this, h, AddCircle.equivIoc_coe_of_mem ht']

lemma rfT_rfT {c ϑ : ℝ} {x : ℝ × ℝ} (hx : x.2 ∈ Ioc (0 : ℝ) 1) : rfT c ϑ (rfT c ϑ x) = x := by
  simp only [rfT, sub_sub_cancel, rot_negRot ϑ hx]

lemma integral_comp_rfT (c ϑ : ℝ) {F : ℝ × ℝ → ℝ} (hF : AEStronglyMeasurable F cyl) :
    ∫ x, F (rfT c ϑ x) ∂cyl = ∫ x, F x ∂cyl := by
  have hT := measurePreserving_rfT c ϑ
  rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hF), hT.map_eq]

/-! ## 2. Reflected test functions -/

lemma rot_int' (ϑ t : ℝ) : ∃ k : ℤ, rot t ϑ = ϑ - t + k := rot_int t ϑ

lemma hasFDerivAt_comp_csub {φ : ℝ × ℝ → ℝ} (c : ℝ × ℝ) {x : ℝ × ℝ}
    (hφ : DifferentiableAt ℝ φ (c - x)) :
    HasFDerivAt (fun y => φ (c - y)) (-(fderiv ℝ φ (c - x))) x := by
  have h := hφ.hasFDerivAt.comp x ((hasFDerivAt_id x).const_sub c)
  refine h.congr_fderiv ?_
  ext <;> simp

lemma Ds_csub {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ × ℝ) :
    Ds (fun y => φ (c - y)) = -fun y => Ds φ (c - y) := by
  funext y
  simp only [Ds, Pi.neg_apply]
  rw [(hasFDerivAt_comp_csub c ((hφ.differentiable (by simp)) _)).fderiv]
  rfl

lemma Dt_csub {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ × ℝ) :
    Dt (fun y => φ (c - y)) = -fun y => Dt φ (c - y) := by
  funext y
  simp only [Dt, Pi.neg_apply]
  rw [(hasFDerivAt_comp_csub c ((hφ.differentiable (by simp)) _)).fderiv]
  rfl

lemma Ds_smul' (r : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : Ds (r • f) = r • Ds f := by
  funext y
  simp only [Ds]
  rw [fderiv_const_smul ((hf.differentiable (by simp)) _)]
  rfl

lemma Dt_smul' (r : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : Dt (r • f) = r • Dt f := by
  funext y
  simp only [Dt]
  rw [fderiv_const_smul ((hf.differentiable (by simp)) _)]
  rfl

lemma contDiff_Dt' {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Dt φ) :=
  (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_Ds' {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Ds φ) :=
  (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_iterate_Dt {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (b : ℕ) :
    ContDiff ℝ ∞ (Dt^[b] φ) := by
  induction b with
  | zero => exact hφ
  | succ b ih => rw [Function.iterate_succ_apply']; exact contDiff_Dt' ih

lemma contDiff_iterate_Ds {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : ℕ) :
    ContDiff ℝ ∞ (Ds^[a] φ) := by
  induction a with
  | zero => exact hφ
  | succ a ih => rw [Function.iterate_succ_apply']; exact contDiff_Ds' ih

lemma contDiff_csub {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ × ℝ) :
    ContDiff ℝ ∞ fun y => φ (c - y) :=
  hφ.comp (contDiff_const.sub contDiff_id)

lemma iterate_Dt_csub {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ × ℝ) (b : ℕ) :
    Dt^[b] (fun y => φ (c - y)) = (-1 : ℝ) ^ b • fun y => Dt^[b] φ (c - y) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Function.iterate_succ_apply', ih,
      Dt_smul' _ (contDiff_csub (contDiff_iterate_Dt hφ b) c),
      Dt_csub (contDiff_iterate_Dt hφ b) c, ← Function.iterate_succ_apply' Dt b φ, pow_succ]
    funext y
    simp

lemma iterate_Ds_csub {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ × ℝ) (a : ℕ) :
    Ds^[a] (fun y => φ (c - y)) = (-1 : ℝ) ^ a • fun y => Ds^[a] φ (c - y) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih,
      Ds_smul' _ (contDiff_csub (contDiff_iterate_Ds hφ a) c),
      Ds_csub (contDiff_iterate_Ds hφ a) c, ← Function.iterate_succ_apply' Ds a φ, pow_succ]
    funext y
    simp

lemma iterate_Ds_smul (r : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℕ) :
    Ds^[a] (r • f) = r • Ds^[a] f := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, Ds_smul' _ (contDiff_iterate_Ds hf a),
      Function.iterate_succ_apply']

lemma pD_csub {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : ℝ × ℝ) (a b : ℕ) :
    pD a b (fun y => φ (c - y)) = fun y => (-1) ^ (a + b) * pD a b φ (c - y) := by
  simp only [pD]
  rw [iterate_Dt_csub hφ c b, iterate_Ds_smul _ (contDiff_csub (contDiff_iterate_Dt hφ b) c),
    iterate_Ds_csub (contDiff_iterate_Dt hφ b) c a]
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, pow_add]
  ring

lemma _root_.Polyfold.CylinderSobolev.IsTest.csub {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (c : ℝ × ℝ) :
    IsTest fun y => φ (c - y) where
  smooth := h.smooth.comp (contDiff_const.sub contDiff_id)
  periodic s t := by
    show φ (c.1 - s, c.2 - (t + 1)) = φ (c.1 - s, c.2 - t)
    rw [show c.2 - (t + 1) = (c.2 - t) + ((-1 : ℤ) : ℝ) by push_cast; ring, h.periodic_intAdd]
  bddSupp := by
    obtain ⟨R, hR⟩ := h.bddSupp
    refine ⟨R + |c.1|, fun s t hs => ?_⟩
    show φ (c.1 - s, c.2 - t) = 0
    refine hR _ _ ?_
    have := abs_sub_abs_le_abs_sub s c.1
    rw [abs_sub_comm s c.1] at this
    linarith

lemma _root_.Polyfold.CylinderSobolev.IsTest.eq_rfT {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (c ϑ : ℝ)
    (x : ℝ × ℝ) : φ x = φ ((c, ϑ) - rfT c ϑ x) := by
  obtain ⟨k, hk⟩ := rot_int' ϑ x.2
  simp only [rfT, Prod.mk_sub_mk, sub_sub_cancel, hk]
  rw [show ϑ - (ϑ - x.2 + k) = x.2 + ((-k : ℤ) : ℝ) by push_cast; ring, h.periodic_intAdd]

/-! ## 3. Weak derivatives and weights -/

theorem _root_.Polyfold.CylinderSobolev.HasWeakDeriv.comp_rfT {a b : ℕ} {u g : ℝ × ℝ → ℝ}
    (hu : AEStronglyMeasurable u cyl) (hg : AEStronglyMeasurable g cyl) (h : HasWeakDeriv a b u g)
    (c ϑ : ℝ) :
    HasWeakDeriv a b (fun x => u (rfT c ϑ x)) (fun x => (-1) ^ (a + b) * g (rfT c ϑ x)) :=
  fun φ hφ => by
  set ψ : ℝ × ℝ → ℝ := fun y => φ ((c, ϑ) - y)
  have hψ : IsTest ψ := hφ.csub _
  have hp : pD a b ψ = fun y => (-1) ^ (a + b) * pD a b φ ((c, ϑ) - y) := pD_csub hφ.smooth _ a b
  have hs : ((-1 : ℝ) ^ (a + b)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have L : (fun x => u (rfT c ϑ x) * pD a b φ x) =
      fun x => (-1) ^ (a + b) * (fun y => u y * pD a b ψ y) (rfT c ϑ x) := by
    funext x
    rw [hp, (hφ.pD a b).eq_rfT c ϑ x]
    linear_combination (-(u (rfT c ϑ x) * pD a b φ ((c, ϑ) - rfT c ϑ x))) * hs
  have M : (fun x => (-1) ^ (a + b) * g (rfT c ϑ x) * φ x) =
      fun x => (-1) ^ (a + b) * (fun y => g y * ψ y) (rfT c ϑ x) := by
    funext x; rw [hφ.eq_rfT c ϑ x]; ring
  rw [L, M, integral_const_mul, integral_const_mul,
    integral_comp_rfT c ϑ (F := fun y => u y * pD a b ψ y)
      (hu.mul (hψ.pD a b).smooth.continuous.aestronglyMeasurable),
    integral_comp_rfT c ϑ (F := fun y => g y * ψ y)
      (hg.mul hψ.smooth.continuous.aestronglyMeasurable), h ψ hψ]

lemma wt_le_rfT (hδ : 0 ≤ δ) (c ϑ : ℝ) (x : ℝ × ℝ) :
    wt δ x ≤ Real.exp (δ * |c|) * wt δ (rfT c ϑ x) := by
  simp only [wt, rfT, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : |x.1| ≤ |c - x.1| + |c| := by
    have := abs_sub_abs_le_abs_sub c x.1
    have h2 := abs_sub_comm x.1 c
    linarith [abs_sub_abs_le_abs_sub x.1 c, abs_sub_comm c x.1]
  nlinarith

lemma memLp_wt_comp_rfT (hδ : 0 ≤ δ) {g : ℝ × ℝ → ℝ} (hw : MemLp (fun x => wt δ x * g x) 2 cyl)
    (c ϑ : ℝ) (σ : ℝ) : MemLp (fun x => wt δ x * (σ * g (rfT c ϑ x))) 2 cyl := by
  have hT := measurePreserving_rfT c ϑ
  have hG := ((hw.comp_measurePreserving hT).const_mul (Real.exp (δ * |c|))).const_mul |σ|
  have hg := (memLp_of_weighted hδ hw).1
  refine hG.of_le ((continuous_wt δ).aestronglyMeasurable.mul
    (aestronglyMeasurable_const.mul (hg.comp_measurePreserving hT))) (ae_of_all _ fun x => ?_)
  simp only [Function.comp, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos δ _),
    abs_of_pos (Real.exp_pos _), abs_abs]
  have := mul_le_mul_of_nonneg_right (wt_le_rfT hδ c ϑ x) (abs_nonneg (g (rfT c ϑ x)))
  nlinarith [abs_nonneg σ, abs_nonneg (g (rfT c ϑ x)), wt_pos δ x]

/-! ## 4. The operator -/

/-- The reflection on `L²(ℝ × S¹)`. -/
def rfLp (c ϑ : ℝ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  (Lp.compMeasurePreservingₗᵢ ℝ (rfT c ϑ) (measurePreserving_rfT c ϑ)).toContinuousLinearMap

lemma coeFn_rfLp (c ϑ : ℝ) (f : Lp ℝ 2 cyl) :
    rfLp c ϑ f =ᵐ[cyl] fun x => f (rfT c ϑ x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_rfT c ϑ)

lemma rfLp_mem (c ϑ : ℝ) {f : Lp ℝ 2 cyl} (hf : f ∈ Hsub m hδ) : rfLp c ϑ f ∈ Hsub m hδ := by
  intro a b hab
  obtain ⟨g, hg, hgw⟩ := hf a b hab
  exact ⟨fun x => (-1) ^ (a + b) * g (rfT c ϑ x),
    (hg.comp_rfT (Lp.aestronglyMeasurable f) (memLp_of_weighted hδ hgw).1 c ϑ).congr_ae
      (coeFn_rfLp c ϑ f).symm (ae_eq_refl _), memLp_wt_comp_rfT hδ hgw c ϑ _⟩

lemma rfLp_rfLp (c ϑ : ℝ) (f : Lp ℝ 2 cyl) : rfLp c ϑ (rfLp c ϑ f) = f := by
  apply Lp.ext
  have hq := (measurePreserving_rfT c ϑ).quasiMeasurePreserving
  filter_upwards [coeFn_rfLp c ϑ (rfLp c ϑ f), hq.ae_eq_comp (coeFn_rfLp c ϑ f), ae_snd_mem]
    with x h1 h2 h3
  rw [h1]
  simp only [Function.comp] at h2
  rw [h2, rfT_rfT h3]

/-- **The reflection `u ↦ u(c - s, ϑ - t)`** on `H^{m,δ}(ℝ × S¹)`. -/
def reflH (c ϑ : ℝ) : H m hδ →L[ℝ] H m hδ :=
  liftVal (rfLp c ϑ) fun u => rfLp_mem c ϑ (H.toSub u).2

lemma val_reflH (c ϑ : ℝ) (u : H m hδ) :
    valCLM m hδ (reflH c ϑ u) =ᵐ[cyl] fun x => valCLM m hδ u (rfT c ϑ x) :=
  coeFn_rfLp c ϑ _

lemma valCLM_reflH (c ϑ : ℝ) (u : H m hδ) :
    valCLM m hδ (reflH c ϑ u) = rfLp c ϑ (valCLM m hδ u) := rfl

/-- `reflH c ϑ` is an involution. -/
theorem reflH_reflH (c ϑ : ℝ) (u : H m hδ) : reflH c ϑ (reflH c ϑ u) = u :=
  valCLM_injective (rfLp_rfLp c ϑ _)

end GWMemoir.Neck

namespace GWMemoir

lemma valEq_reflH {k l : ℕ} {d e : ℝ} {hd : 0 ≤ d} {he : 0 ≤ e} (c ϑ : ℝ) :
    ValEq (Neck.reflH c ϑ : H k hd →L[ℝ] H k hd) (Neck.reflH c ϑ : H l he →L[ℝ] H l he) :=
  fun _ _ h => by rw [Neck.valCLM_reflH, Neck.valCLM_reflH, h]

end GWMemoir
