import Polyfold.Chapter1.GapP1_Sobolev2

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2), part 3: the spaces `H^{m,δ}(ℝ × S¹)`

`H^{m,δ}(ℝ × S¹)` consists of the `u ∈ L²(ℝ × S¹)` having weak partial derivatives
`∂_s^a ∂_t^b u`, `a + b ≤ m`, which weighted by `e^{δ|s|}` belong to `L²(ℝ × S¹)` (`MemH`,
`Hsub`). Its norm is `‖u‖² = ∑_{a+b ≤ m} ‖e^{δ|s|} ∂_s^a ∂_t^b u‖²_{L²}`, given by the
embedding `Φ` into a finite product of copies of `L²`; `H m hδ` is this normed space.

* `completeSpace_H`: `H^{m,δ}` is a Banach space (the image of `Φ` is closed).
* `inclH`: for `δ ≤ δ'`, `H^{m+1,δ'} ⊂ H^{m,δ}` as subspaces of `L²`, with `‖u‖_{m,δ} ≤
  ‖u‖_{m+1,δ'}`; the inclusion is injective.

All weights `δ` are `≥ 0` (in Example 1.1.3, `δ_m ≥ δ_0 = 0`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

/-! ### The weight -/

/-- The weight `e^{δ|s|}`. -/
def wt (δ : ℝ) (x : ℝ × ℝ) : ℝ := Real.exp (δ * |x.1|)

lemma wt_pos (δ : ℝ) (x : ℝ × ℝ) : 0 < wt δ x := Real.exp_pos _

lemma continuous_wt (δ : ℝ) : Continuous (wt δ) := by unfold wt; fun_prop

lemma wt_neg_mul (δ : ℝ) (x : ℝ × ℝ) : wt (-δ) x * wt δ x = 1 := by
  rw [wt, wt, ← Real.exp_add]; simp

lemma wt_mono {δ δ' : ℝ} (h : δ ≤ δ') (x : ℝ × ℝ) : wt δ x ≤ wt δ' x :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (abs_nonneg _))

lemma one_le_wt {δ : ℝ} (h : 0 ≤ δ) (x : ℝ × ℝ) : 1 ≤ wt δ x :=
  Real.one_le_exp (mul_nonneg h (abs_nonneg _))

lemma abs_wt_neg_le {δ : ℝ} (h : 0 ≤ δ) (x : ℝ × ℝ) : |wt (-δ) x| ≤ 1 := by
  rw [abs_of_pos (wt_pos _ _), wt, Real.exp_le_one_iff]
  nlinarith [abs_nonneg x.1]

/-! ### Multiplication operators and pairings on `L²` -/

lemma memLp_mul {c : ℝ × ℝ → ℝ} (hc : AEStronglyMeasurable c cyl) {C : ℝ}
    (hb : ∀ x, |c x| ≤ C) {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 cyl) :
    MemLp (fun x => c x * f x) 2 cyl :=
  hf.of_le_mul (hc.mul hf.1) (ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _))

/-- Multiplication by a bounded measurable function, as an operator on `L²(ℝ × S¹)`. -/
def mulOp (c : ℝ × ℝ → ℝ) (hc : AEStronglyMeasurable c cyl) (C : ℝ) (hb : ∀ x, |c x| ≤ C) :
    Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul hc hb (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add (memLp_mul hc hb (Lp.memLp f)) (memLp_mul hc hb (Lp.memLp g))]
        apply (MemLp.toLp_eq_toLp_iff _ _).2
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := fun r f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul r (memLp_mul hc hb (Lp.memLp f))]
        apply (MemLp.toLp_eq_toLp_iff _ _).2
        filter_upwards [Lp.coeFn_smul r f] with x hx
        simp only [hx, Pi.smul_apply, smul_eq_mul]; ring }
    C (fun f => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (memLp_mul hc hb (Lp.memLp f))] with x hx
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at hx ⊢
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _))

lemma coeFn_mulOp (c : ℝ × ℝ → ℝ) (hc : AEStronglyMeasurable c cyl) (C : ℝ)
    (hb : ∀ x, |c x| ≤ C) (f : Lp ℝ 2 cyl) :
    mulOp c hc C hb f =ᵐ[cyl] fun x => c x * f x :=
  MemLp.coeFn_toLp (memLp_mul hc hb (Lp.memLp f))

/-- The pairing `f ↦ ∫ f φ` with a function `φ ∈ L²`, as a continuous linear functional. -/
def pairing (φ : ℝ × ℝ → ℝ) (hφ : MemLp φ 2 cyl) : Lp ℝ 2 cyl →L[ℝ] ℝ :=
  innerSL ℝ (hφ.toLp φ)

lemma pairing_apply (φ : ℝ × ℝ → ℝ) (hφ : MemLp φ 2 cyl) (f : Lp ℝ 2 cyl) :
    pairing φ hφ f = ∫ x, f x * φ x ∂cyl := by
  rw [pairing, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hφ] with x hx
  rw [hx, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-! ### The spaces `H^{m,δ}` -/

/-- The multi-indices `(a,b)` with `a + b ≤ m`. -/
def idx (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => p.1 + p.2 ≤ m)

lemma mem_idx {m : ℕ} {p : ℕ × ℕ} : p ∈ idx m ↔ p.1 + p.2 ≤ m := by
  simp only [idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega

/-- The multi-index `(0,0)`. -/
def idx0 (m : ℕ) : idx m := ⟨(0, 0), mem_idx.2 (by simp)⟩

/-- `u` has weak partial derivatives up to order `m` which, weighted by `e^{δ|s|}`, are in `L²`. -/
def MemH (m : ℕ) (δ : ℝ) (u : ℝ × ℝ → ℝ) : Prop :=
  ∀ a b, a + b ≤ m → ∃ g, HasWeakDeriv a b u g ∧ MemLp (fun x => wt δ x * g x) 2 cyl

lemma memLp_of_weighted {δ : ℝ} (hδ : 0 ≤ δ) {g : ℝ × ℝ → ℝ}
    (hg : MemLp (fun x => wt δ x * g x) 2 cyl) : MemLp g 2 cyl := by
  have hm : AEStronglyMeasurable g cyl := by
    have := (continuous_wt (-δ)).aestronglyMeasurable.mul hg.1
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    rw [← mul_assoc, wt_neg_mul, one_mul]
  refine hg.of_le hm (ae_of_all _ fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos δ x)]
  exact le_mul_of_one_le_left (abs_nonneg _) (one_le_wt hδ x)

/-- `H^{m,δ}(ℝ × S¹)` as a subspace of `L²(ℝ × S¹)`. -/
def Hsub (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : Submodule ℝ (Lp ℝ 2 cyl) where
  carrier := {u | MemH m δ u}
  add_mem' := by
    intro u v hu hv a b hab
    obtain ⟨g, hg, hgw⟩ := hu a b hab
    obtain ⟨g', hg', hgw'⟩ := hv a b hab
    refine ⟨g + g', ?_, ?_⟩
    · refine (hg.add hg' (Lp.memLp u) (Lp.memLp v) (memLp_of_weighted hδ hgw)
        (memLp_of_weighted hδ hgw')).congr_ae ?_ (ae_eq_refl _)
      filter_upwards [Lp.coeFn_add u v] with x hx using hx.symm
    · have := hgw.add hgw'
      convert this using 1
      funext x; simp [mul_add]
  zero_mem' := by
    intro a b _
    refine ⟨0, ?_, by simp⟩
    have h0 : HasWeakDeriv a b (0 : ℝ × ℝ → ℝ) 0 := fun φ _ => by simp
    exact h0.congr_ae (Lp.coeFn_zero ℝ 2 cyl).symm (ae_eq_refl _)
  smul_mem' := by
    intro c u hu a b hab
    obtain ⟨g, hg, hgw⟩ := hu a b hab
    refine ⟨fun x => c * g x, ?_, ?_⟩
    · refine (hg.const_mul c).congr_ae ?_ (ae_eq_refl _)
      filter_upwards [Lp.coeFn_smul c u] with x hx
      simp [hx]
    · exact MemLp.ae_eq (ae_of_all _ fun x => by simp only; ring) (hgw.const_mul c)

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma mem_Hsub {u : Lp ℝ 2 cyl} : u ∈ Hsub m hδ ↔ MemH m δ u := Iff.rfl

/-- The chosen weak derivative `∂^p u`. -/
def dv (u : Hsub m hδ) (p : idx m) : ℝ × ℝ → ℝ :=
  Classical.choose ((show MemH m δ (u : Lp ℝ 2 cyl) from u.2) p.1.1 p.1.2 (mem_idx.1 p.2))

lemma dv_spec (u : Hsub m hδ) (p : idx m) :
    HasWeakDeriv p.1.1 p.1.2 (u : Lp ℝ 2 cyl) (dv u p) ∧
      MemLp (fun x => wt δ x * dv u p x) 2 cyl :=
  Classical.choose_spec ((show MemH m δ (u : Lp ℝ 2 cyl) from u.2) p.1.1 p.1.2 (mem_idx.1 p.2))

lemma dv_memLp (u : Hsub m hδ) (p : idx m) : MemLp (dv u p) 2 cyl :=
  memLp_of_weighted hδ (dv_spec u p).2

lemma dv_unique (u : Hsub m hδ) (p : idx m) {g : ℝ × ℝ → ℝ}
    (hg : HasWeakDeriv p.1.1 p.1.2 (u : Lp ℝ 2 cyl) g) (hg2 : MemLp g 2 cyl) :
    dv u p =ᵐ[cyl] g :=
  (dv_spec u p).1.ae_eq hg (dv_memLp u p) hg2

lemma dv_idx0 (u : Hsub m hδ) : dv u (idx0 m) =ᵐ[cyl] (u : Lp ℝ 2 cyl) :=
  dv_unique u (idx0 m) (hasWeakDeriv_zero _) (Lp.memLp _)

/-- The weighted derivative `e^{δ|s|} ∂^p u ∈ L²`. -/
def wdv (u : Hsub m hδ) (p : idx m) : Lp ℝ 2 cyl := (dv_spec u p).2.toLp _

lemma coeFn_wdv (u : Hsub m hδ) (p : idx m) :
    wdv u p =ᵐ[cyl] fun x => wt δ x * dv u p x := MemLp.coeFn_toLp _

lemma dv_add (u v : Hsub m hδ) (p : idx m) : dv (u + v) p =ᵐ[cyl] dv u p + dv v p := by
  refine dv_unique (u + v) p ?_ ((dv_memLp u p).add (dv_memLp v p))
  refine ((dv_spec u p).1.add (dv_spec v p).1 (Lp.memLp _) (Lp.memLp _) (dv_memLp u p)
    (dv_memLp v p)).congr_ae ?_ (ae_eq_refl _)
  filter_upwards [Lp.coeFn_add (u : Lp ℝ 2 cyl) v] with x hx
  exact hx.symm

lemma dv_smul (c : ℝ) (u : Hsub m hδ) (p : idx m) :
    dv (c • u) p =ᵐ[cyl] fun x => c * dv u p x := by
  refine dv_unique (c • u) p ?_ ((dv_memLp u p).const_mul c)
  refine ((dv_spec u p).1.const_mul c).congr_ae ?_ (ae_eq_refl _)
  filter_upwards [Lp.coeFn_smul c (u : Lp ℝ 2 cyl)] with x hx
  simp [hx]

lemma wdv_add (u v : Hsub m hδ) (p : idx m) : wdv (u + v) p = wdv u p + wdv v p := by
  rw [wdv, wdv, wdv, ← MemLp.toLp_add]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [dv_add u v p] with x hx
  simp [hx, mul_add]

lemma wdv_smul (c : ℝ) (u : Hsub m hδ) (p : idx m) : wdv (c • u) p = c • wdv u p := by
  rw [wdv, wdv, ← MemLp.toLp_const_smul]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards [dv_smul c u p] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul]; ring

/-- The embedding `u ↦ (e^{δ|s|} ∂^p u)_{p}` into a finite product of copies of `L²`. -/
def Φ (m : ℕ) (hδ : 0 ≤ δ) : Hsub m hδ →ₗ[ℝ] PiLp 2 (fun _ : idx m => Lp ℝ 2 cyl) where
  toFun u := WithLp.toLp 2 (fun p => wdv u p)
  map_add' u v := by
    rw [← WithLp.toLp_add]; congr 1; funext p; exact wdv_add u v p
  map_smul' c u := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]; congr 1; funext p; exact wdv_smul c u p

lemma Φ_apply (u : Hsub m hδ) (p : idx m) : Φ m hδ u p = wdv u p := rfl

lemma Φ_injective : Function.Injective (Φ m hδ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h0 : wdv u (idx0 m) = 0 := by
    have := congrArg (fun G : PiLp 2 (fun _ : idx m => Lp ℝ 2 cyl) => G (idx0 m)) hu
    simpa [Φ_apply] using this
  have h1 : (fun x => wt δ x * dv u (idx0 m) x) =ᵐ[cyl] 0 := by
    have := coeFn_wdv u (idx0 m)
    rw [h0] at this
    exact this.symm.trans (Lp.coeFn_zero ℝ 2 cyl)
  apply Subtype.ext
  rw [Submodule.coe_zero, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [h1, dv_idx0 u] with x hx hx'
  rw [← hx']
  simpa [(wt_pos δ x).ne'] using hx

/-- `H^{m,δ}(ℝ × S¹)` with its norm `‖u‖² = ∑_{a+b ≤ m} ‖e^{δ|s|} ∂_s^a ∂_t^b u‖²_{L²}`. -/
def H (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : Type := Hsub m hδ

instance : AddCommGroup (H m hδ) := inferInstanceAs (AddCommGroup (Hsub m hδ))

/-- The element of `Hsub` underlying `u : H`. -/
def H.toSub (u : H m hδ) : Hsub m hδ := u

instance : Module ℝ (H m hδ) := inferInstanceAs (Module ℝ (Hsub m hδ))

/-- `Φ` on `H`. -/
def ΦH (m : ℕ) (hδ : 0 ≤ δ) : H m hδ →ₗ[ℝ] PiLp 2 (fun _ : idx m => Lp ℝ 2 cyl) := Φ m hδ

instance : NormedAddCommGroup (H m hδ) :=
  NormedAddCommGroup.induced (H m hδ) (PiLp 2 (fun _ : idx m => Lp ℝ 2 cyl)) (ΦH m hδ)
    Φ_injective

instance : NormedSpace ℝ (H m hδ) :=
  NormedSpace.induced ℝ (H m hδ) (PiLp 2 (fun _ : idx m => Lp ℝ 2 cyl)) (ΦH m hδ)

/-- The underlying element of `L²`. -/
def H.val (u : H m hδ) : Lp ℝ 2 cyl := (H.toSub u : Lp ℝ 2 cyl)

lemma norm_H (u : H m hδ) : ‖u‖ = ‖ΦH m hδ u‖ := rfl

lemma norm_sq_H (u : H m hδ) : ‖u‖ ^ 2 = ∑ p : idx m, ‖wdv (H.toSub u) p‖ ^ 2 := by
  rw [norm_H, PiLp.norm_sq_eq_of_L2]; rfl

lemma norm_wdv_le (u : H m hδ) (p : idx m) : ‖wdv (H.toSub u) p‖ ≤ ‖u‖ := by
  rw [norm_H]
  exact PiLp.norm_apply_le (ΦH m hδ u) p

lemma isometry_ΦH : Isometry (ΦH m hδ) := by
  refine AddMonoidHomClass.isometry_of_norm (ΦH m hδ) fun u => ?_
  rfl

/-- The weighted derivative as a continuous linear map on `H^{m,δ}`. -/
def wdvCLM (m : ℕ) (hδ : 0 ≤ δ) (p : idx m) : H m hδ →L[ℝ] Lp ℝ 2 cyl :=
  LinearMap.mkContinuous
    { toFun := fun u => wdv (H.toSub u) p
      map_add' := fun u v => wdv_add (H.toSub u) (H.toSub v) p
      map_smul' := fun c u => wdv_smul c (H.toSub u) p } 1
    (fun u => by rw [one_mul]; exact norm_wdv_le u p)

/-- The weak derivative `∂^p u ∈ L²` as a continuous linear map on `H^{m,δ}`. -/
def dvCLM (m : ℕ) (hδ : 0 ≤ δ) (p : idx m) : H m hδ →L[ℝ] Lp ℝ 2 cyl :=
  (mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)).comp
    (wdvCLM m hδ p)

lemma coeFn_dvCLM (p : idx m) (u : H m hδ) :
    dvCLM m hδ p u =ᵐ[cyl] dv (H.toSub u) p := by
  filter_upwards [coeFn_mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1
    (abs_wt_neg_le hδ) (wdvCLM m hδ p u), coeFn_wdv (H.toSub u) p] with x h1 h2
  rw [dvCLM, ContinuousLinearMap.comp_apply, h1]
  change wt (-δ) x * (wdv (H.toSub u) p) x = _
  rw [h2, ← mul_assoc, wt_neg_mul, one_mul]

lemma norm_mulOp_le {c : ℝ × ℝ → ℝ} {hc : AEStronglyMeasurable c cyl} {C : ℝ}
    {hb : ∀ x, |c x| ≤ C} (hC : 0 ≤ C) : ‖mulOp c hc C hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

lemma val_eq_dvCLM (u : H m hδ) :
    (H.toSub u : Lp ℝ 2 cyl) = dvCLM m hδ (idx0 m) u := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dvCLM (idx0 m) u, dv_idx0 (H.toSub u)] with x h1 h2
  rw [h1, h2]

/-- The inclusion `H^{m,δ} → L²`. -/
def valCLM (m : ℕ) (hδ : 0 ≤ δ) : H m hδ →L[ℝ] Lp ℝ 2 cyl :=
  LinearMap.mkContinuous ((Hsub m hδ).subtype : H m hδ →ₗ[ℝ] Lp ℝ 2 cyl) 1 (fun u => by
    rw [one_mul]
    change ‖(H.toSub u : Lp ℝ 2 cyl)‖ ≤ ‖u‖
    rw [val_eq_dvCLM]
    calc ‖dvCLM m hδ (idx0 m) u‖
        ≤ ‖mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)‖ *
            ‖wdvCLM m hδ (idx0 m) u‖ :=
          ContinuousLinearMap.le_opNorm
            (mulOp (wt (-δ)) (continuous_wt _).aestronglyMeasurable 1 (abs_wt_neg_le hδ)) _
      _ ≤ 1 * ‖u‖ := mul_le_mul (norm_mulOp_le zero_le_one) (norm_wdv_le u _) (norm_nonneg _)
            zero_le_one
      _ = ‖u‖ := one_mul _)

lemma valCLM_apply (u : H m hδ) : valCLM m hδ u = (H.toSub u : Lp ℝ 2 cyl) := rfl

lemma valCLM_injective : Function.Injective (valCLM m hδ) := fun _ _ h => Subtype.ext h

end Polyfold.GapP1Sobolev
