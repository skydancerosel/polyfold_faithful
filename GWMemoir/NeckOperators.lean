import GWMemoir.HalfCylinders

/-!
# Memoir §2.4: the operators on `H^{m,δ}(ℝ × S¹)` used by the gluing at a fixed parameter

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, pp. 49–50.

The total glued map `Φ_a` at the Sobolev levels is built from three kinds of operators on the
project's weighted spaces `H m hδ = H^{m,δ}(ℝ × S¹)` (`Polyfold.CylinderSobolev`):

* `mulHL χ`: multiplication by a function `χ(s)` with bounded derivatives (the cut-offs `β_a`,
  `1 - β_a`, `β_a/γ_a`, `(1 - β_a)/γ_a`); `mult_of_deriv` gives the hypothesis for smooth bounded
  `χ` with compactly supported derivative.
* `shH R ϑ`: `u ↦ u(s - R, t - ϑ)`, the identification `s' = s - R`, `t' = t - ϑ` of the two
  half-cylinders (Memoir p. 45), with inverse `shH (-R) (-ϑ)` (`shH_shH`).
* `trH σ`: the circle average `[u]_σ = ∫_{S¹} u(σ, t) dt` (Memoir p. 46), a continuous functional
  on `H^{m+1,δ}`, given by `∫_{s ≤ σ} ∂_s(ρ_σ u)` for a cut-off `ρ_σ`; `trH_toH` computes it on
  test functions, and `trH_mulHL`, `trH_shH`, `trH_eq_zero_of_vanish` are its properties.

All three are first defined on `L²` and lifted to `H^{m,δ}` by `liftVal`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-! ## 1. Lifting `L²` operators to `H^{m,δ}` -/

/-- An operator on `L²` that preserves `H^{m,δ}` is continuous on `H^{m,δ}` (closed graph). -/
def liftVal (A : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl) (hA : ∀ u : H m hδ, A (valCLM m hδ u) ∈ Hsub m hδ) :
    H m hδ →L[ℝ] H m hδ :=
  let L : H m hδ →ₗ[ℝ] H m hδ :=
    { toFun := fun u => (⟨A (valCLM m hδ u), hA u⟩ : Hsub m hδ)
      map_add' := fun u v => valCLM_injective (by
        change A (valCLM m hδ (u + v)) = A (valCLM m hδ u) + A (valCLM m hδ v)
        rw [map_add, map_add])
      map_smul' := fun c u => valCLM_injective (by
        change A (valCLM m hδ (c • u)) = c • A (valCLM m hδ u)
        rw [map_smul, map_smul]) }
  ⟨L, L.continuous_of_seq_closed_graph fun u x y hu hy => by
    apply valCLM_injective
    have h1 := ((valCLM m hδ).continuous.tendsto y).comp hy
    have h2 := ((A.comp (valCLM m hδ)).continuous.tendsto x).comp hu
    exact tendsto_nhds_unique h1 h2⟩

lemma val_liftVal (A : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl)
    (hA : ∀ u : H m hδ, A (valCLM m hδ u) ∈ Hsub m hδ) (u : H m hδ) :
    valCLM m hδ (liftVal A hA u) = A (valCLM m hδ u) := rfl

/-! ## 2. Multipliers -/

/-- A smooth bounded `χ` with compactly supported derivative has bounded derivatives. -/
lemma mult_of_deriv {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {C : ℝ} (hb : ∀ s, |χ s| ≤ C)
    (hc : HasCompactSupport (deriv χ)) (m : ℕ) : Mult m χ := by
  refine ⟨hχ, ?_⟩
  obtain ⟨K, hK⟩ := bdd_iteratedDeriv (contDiff_infty_iff_deriv.1 hχ).2 hc m
  refine ⟨max C K, fun i hi s => ?_⟩
  rcases i with _ | j
  · simpa using (hb s).trans (le_max_left _ _)
  · rw [iteratedDeriv_succ']
    exact (hK j (by omega) s).trans (le_max_right _ _)

/-- Multiplication by `χ(s)` on `H^{m,δ}`. -/
def mulHL (χ : ℝ → ℝ) (h : Mult m χ) : H m hδ →L[ℝ] H m hδ :=
  liftVal (mulχ χ h) fun u => mulχ_mem h (H.toSub u)

lemma val_mulHL (χ : ℝ → ℝ) (h : Mult m χ) (u : H m hδ) :
    valCLM m hδ (mulHL χ h u) =ᵐ[cyl] fun x => χ x.1 * valCLM m hδ u x :=
  coeFn_mulχ χ h _

/-! ## 3. The shift-rotation `u ↦ u(s - R, t - ϑ)` -/

/-- `t ↦ t - ϑ` on `S¹ = ℝ/ℤ`, in the coordinate `t ∈ (0,1]`. -/
def rot (ϑ t : ℝ) : ℝ :=
  (AddCircle.equivIoc (1 : ℝ) 0 ((t : UnitAddCircle) - (ϑ : UnitAddCircle)) : ℝ)

lemma rot_mem (ϑ t : ℝ) : rot ϑ t ∈ Ioc (0 : ℝ) 1 := by
  have := (AddCircle.equivIoc (1 : ℝ) 0 ((t : UnitAddCircle) - (ϑ : UnitAddCircle))).2
  simp only [rot]; simpa using this

lemma rot_coe (ϑ t : ℝ) : ((rot ϑ t : ℝ) : UnitAddCircle) = (t : UnitAddCircle) - ϑ :=
  AddCircle.coe_equivIoc

lemma rot_int (ϑ t : ℝ) : ∃ k : ℤ, rot ϑ t = t - ϑ + k := by
  have h := rot_coe ϑ t
  rw [← AddCircle.coe_sub] at h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq_iff_sub_mem.1 h)
  refine ⟨k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  linarith

lemma rot_of_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : rot 0 t = t := by
  have ht' : t ∈ Ioc (0 : ℝ) (0 + 1) := by simpa using ht
  simp only [rot, AddCircle.coe_zero, sub_zero]
  exact AddCircle.equivIoc_coe_of_mem ht'

lemma rot_rot (ϑ ϑ' t : ℝ) : rot ϑ' (rot ϑ t) = rot (ϑ + ϑ') t := by
  simp only [rot]
  rw [AddCircle.coe_equivIoc]
  congr 2
  rw [AddCircle.coe_add]; abel

lemma measurePreserving_rot (ϑ : ℝ) :
    MeasurePreserving (rot ϑ) (volume.restrict (Ioc (0 : ℝ) 1)) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h1 := AddCircle.measurePreserving_mk (1 : ℝ) 0
  have h2 := measurePreserving_sub_right (volume : Measure UnitAddCircle) (ϑ : UnitAddCircle)
  have h3 := AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0)
  have h4 := measurePreserving_subtype_coe (μa := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) (0 + 1))
    measurableSet_Ioc
  have := h4.comp (h3.comp (h2.comp h1))
  simp only [zero_add] at this
  exact this

/-- `(s, t) ↦ (s - R, t - ϑ)` in the strip coordinates of `ℝ × S¹`. -/
def shT (R ϑ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 - R, rot ϑ x.2)

lemma measurePreserving_shT (R ϑ : ℝ) : MeasurePreserving (shT R ϑ) cyl cyl :=
  (measurePreserving_sub_right (volume : Measure ℝ) R).prod (measurePreserving_rot ϑ)

lemma ae_snd_mem : ∀ᵐ x ∂cyl, x.2 ∈ Ioc (0 : ℝ) 1 :=
  Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)

lemma shT_shT {R ϑ : ℝ} {x : ℝ × ℝ} (hx : x.2 ∈ Ioc (0 : ℝ) 1) :
    shT (-R) (-ϑ) (shT R ϑ x) = x := by
  simp only [shT, rot_rot, add_neg_cancel, rot_of_mem hx, sub_neg_eq_add, sub_add_cancel]

lemma shT_shT' {R ϑ : ℝ} {x : ℝ × ℝ} (hx : x.2 ∈ Ioc (0 : ℝ) 1) :
    shT R ϑ (shT (-R) (-ϑ) x) = x := by
  have := shT_shT (R := -R) (ϑ := -ϑ) hx
  rwa [neg_neg, neg_neg] at this

lemma integral_comp_shT (R ϑ : ℝ) {F : ℝ × ℝ → ℝ} (hF : AEStronglyMeasurable F cyl) :
    ∫ x, F (shT R ϑ x) ∂cyl = ∫ x, F x ∂cyl := by
  have hT := measurePreserving_shT R ϑ
  rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hF), hT.map_eq]

/-! ### Translated test functions -/

lemma Ds_add (φ : ℝ × ℝ → ℝ) (c : ℝ × ℝ) :
    Ds (fun y => φ (y + c)) = fun y => Ds φ (y + c) := by
  funext y; simp only [Ds]; rw [fderiv_comp_add_right]

lemma Dt_add (φ : ℝ × ℝ → ℝ) (c : ℝ × ℝ) :
    Dt (fun y => φ (y + c)) = fun y => Dt φ (y + c) := by
  funext y; simp only [Dt]; rw [fderiv_comp_add_right]

lemma pD_add (φ : ℝ × ℝ → ℝ) (c : ℝ × ℝ) (a b : ℕ) :
    pD a b (fun y => φ (y + c)) = fun y => pD a b φ (y + c) := by
  have ht : ∀ b (φ : ℝ × ℝ → ℝ), Dt^[b] (fun y => φ (y + c)) = fun y => Dt^[b] φ (y + c) := by
    intro b; induction b with
    | zero => intro φ; rfl
    | succ b ih => intro φ; rw [Function.iterate_succ_apply, Dt_add, ih, Function.iterate_succ_apply]
  have hs : ∀ a (φ : ℝ × ℝ → ℝ), Ds^[a] (fun y => φ (y + c)) = fun y => Ds^[a] φ (y + c) := by
    intro a; induction a with
    | zero => intro φ; rfl
    | succ a ih => intro φ; rw [Function.iterate_succ_apply, Ds_add, ih, Function.iterate_succ_apply]
  simp only [pD]; rw [ht, hs]

lemma _root_.Polyfold.CylinderSobolev.IsTest.add_const {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (c : ℝ × ℝ) :
    IsTest fun y => φ (y + c) where
  smooth := h.smooth.comp (contDiff_id.add contDiff_const)
  periodic s t := by
    show φ (s + c.1, t + 1 + c.2) = φ (s + c.1, t + c.2)
    rw [show t + 1 + c.2 = (t + c.2) + 1 by ring, h.periodic]
  bddSupp := by
    obtain ⟨R, hR⟩ := h.bddSupp
    refine ⟨R + |c.1|, fun s t hs => ?_⟩
    show φ (s + c.1, t + c.2) = 0
    refine hR _ _ ?_
    have := abs_sub_abs_le_abs_sub s (-c.1)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith

lemma _root_.Polyfold.CylinderSobolev.IsTest.periodic_intAdd {φ : ℝ × ℝ → ℝ} (h : IsTest φ)
    (s t : ℝ) (k : ℤ) :
    φ (s, t + k) = φ (s, t) := by
  rw [← h.periodic_int s (t + k), Int.fract_add_intCast, h.periodic_int]

lemma _root_.Polyfold.CylinderSobolev.IsTest.eq_shT {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (R ϑ : ℝ) (x : ℝ × ℝ) :
    φ x = φ (shT R ϑ x + (R, ϑ)) := by
  obtain ⟨k, hk⟩ := rot_int ϑ x.2
  simp only [shT, Prod.mk_add_mk, sub_add_cancel, hk]
  rw [show x.2 - ϑ + k + ϑ = x.2 + k by ring, h.periodic_intAdd]

lemma _root_.Polyfold.CylinderSobolev.IsTest.eq_shT_sub {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (R ϑ : ℝ) (x : ℝ × ℝ) :
    φ (shT R ϑ x) = φ (x + (-R, -ϑ)) := by
  obtain ⟨k, hk⟩ := rot_int ϑ x.2
  simp only [shT, hk]
  rw [show x.2 - ϑ + k = (x.2 + -ϑ) + k by ring, h.periodic_intAdd, sub_eq_add_neg]
  rfl

/-! ### Weak derivatives and weights -/

theorem _root_.Polyfold.CylinderSobolev.HasWeakDeriv.comp_shT {a b : ℕ} {u g : ℝ × ℝ → ℝ}
    (hu : AEStronglyMeasurable u cyl)
    (hg : AEStronglyMeasurable g cyl) (h : HasWeakDeriv a b u g) (R ϑ : ℝ) :
    HasWeakDeriv a b (fun x => u (shT R ϑ x)) (fun x => g (shT R ϑ x)) := fun φ hφ => by
  set ψ : ℝ × ℝ → ℝ := fun y => φ (y + (R, ϑ))
  have hψ : IsTest ψ := hφ.add_const _
  have L : (fun x => u (shT R ϑ x) * pD a b φ x) =
      fun x => (fun y => u y * pD a b ψ y) (shT R ϑ x) := by
    funext x; rw [pD_add, (hφ.pD a b).eq_shT R ϑ x]
  have M : (fun x => g (shT R ϑ x) * φ x) = fun x => (fun y => g y * ψ y) (shT R ϑ x) := by
    funext x; rw [hφ.eq_shT R ϑ x]
  rw [L, M, integral_comp_shT R ϑ (F := fun y => u y * pD a b ψ y)
      (hu.mul (hψ.pD a b).smooth.continuous.aestronglyMeasurable),
    integral_comp_shT R ϑ (F := fun y => g y * ψ y)
      (hg.mul hψ.smooth.continuous.aestronglyMeasurable)]
  exact h ψ hψ

lemma wt_le_shT (hδ : 0 ≤ δ) (R ϑ : ℝ) (x : ℝ × ℝ) :
    wt δ x ≤ Real.exp (δ * |R|) * wt δ (shT R ϑ x) := by
  simp only [wt, shT, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : |x.1| ≤ |x.1 - R| + |R| := by
    have := abs_add_le (x.1 - R) R; rwa [sub_add_cancel] at this
  nlinarith

lemma memLp_wt_comp_shT (hδ : 0 ≤ δ) {g : ℝ × ℝ → ℝ} (hw : MemLp (fun x => wt δ x * g x) 2 cyl)
    (R ϑ : ℝ) : MemLp (fun x => wt δ x * g (shT R ϑ x)) 2 cyl := by
  have hT := measurePreserving_shT R ϑ
  have hG := (hw.comp_measurePreserving hT).const_mul (Real.exp (δ * |R|))
  have hg := (memLp_of_weighted hδ hw).1
  refine hG.of_le ((continuous_wt δ).aestronglyMeasurable.mul (hg.comp_measurePreserving hT))
    (ae_of_all _ fun x => ?_)
  simp only [Function.comp, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos δ _),
    abs_of_pos (Real.exp_pos _)]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (wt_le_shT hδ R ϑ x) (abs_nonneg _)

/-- The shift-rotation on `L²(ℝ × S¹)`. -/
def shLp (R ϑ : ℝ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  (Lp.compMeasurePreservingₗᵢ ℝ (shT R ϑ) (measurePreserving_shT R ϑ)).toContinuousLinearMap

lemma coeFn_shLp (R ϑ : ℝ) (f : Lp ℝ 2 cyl) :
    shLp R ϑ f =ᵐ[cyl] fun x => f (shT R ϑ x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_shT R ϑ)

lemma shLp_mem (R ϑ : ℝ) {f : Lp ℝ 2 cyl} (hf : f ∈ Hsub m hδ) : shLp R ϑ f ∈ Hsub m hδ := by
  intro a b hab
  obtain ⟨g, hg, hgw⟩ := hf a b hab
  exact ⟨fun x => g (shT R ϑ x),
    (hg.comp_shT (Lp.aestronglyMeasurable f) (memLp_of_weighted hδ hgw).1 R ϑ).congr_ae
      (coeFn_shLp R ϑ f).symm (ae_eq_refl _), memLp_wt_comp_shT hδ hgw R ϑ⟩

lemma shLp_shLp (R ϑ : ℝ) (f : Lp ℝ 2 cyl) : shLp (-R) (-ϑ) (shLp R ϑ f) = f := by
  apply Lp.ext
  have hq := (measurePreserving_shT (-R) (-ϑ)).quasiMeasurePreserving
  filter_upwards [coeFn_shLp (-R) (-ϑ) (shLp R ϑ f), hq.ae_eq_comp (coeFn_shLp R ϑ f), ae_snd_mem]
    with x h1 h2 h3
  rw [h1]
  simp only [Function.comp] at h2
  rw [h2, shT_shT' h3]

/-- The shift-rotation `u ↦ u(s - R, t - ϑ)` on `H^{m,δ}(ℝ × S¹)`. -/
def shH (R ϑ : ℝ) : H m hδ →L[ℝ] H m hδ :=
  liftVal (shLp R ϑ) fun u => shLp_mem R ϑ (H.toSub u).2

lemma val_shH (R ϑ : ℝ) (u : H m hδ) :
    valCLM m hδ (shH R ϑ u) =ᵐ[cyl] fun x => valCLM m hδ u (shT R ϑ x) :=
  coeFn_shLp R ϑ _

theorem shH_shH (R ϑ : ℝ) (u : H m hδ) : shH (-R) (-ϑ) (shH R ϑ u) = u :=
  valCLM_injective (shLp_shLp R ϑ _)

theorem shH_shH' (R ϑ : ℝ) (u : H m hδ) : shH R ϑ (shH (-R) (-ϑ) u) = u := by
  have := shH_shH (-R) (-ϑ) u
  rwa [neg_neg, neg_neg] at this

/-! ## 4. The circle average `[u]_σ = ∫_{S¹} u(σ, t) dt` -/

/-- The cut-off `ρ` of the trace formula: `ρ = 0` on `(-∞,-1]`, `ρ = 1` on `[-1/2, ∞)`. -/
def trCut (s : ℝ) : ℝ := Real.smoothTransition (2 * s + 2)

lemma contDiff_trCut : ContDiff ℝ ∞ trCut :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

lemma continuous_deriv_trCut : Continuous (deriv trCut) :=
  contDiff_trCut.continuous_deriv (by simp)

lemma trCut_zero : trCut 0 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)

lemma trCut_neg_one : trCut (-1) = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)

/-- `f(s)` on the slab `[σ - 1, σ] × S¹`, `0` elsewhere. -/
def trK (σ : ℝ) (f : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := (Icc (σ - 1) σ).indicator f x.1

lemma memLp_trK (σ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) : MemLp (trK σ f) 2 cyl := by
  have hS : MeasurableSet (Icc (σ - 1) σ ×ˢ (univ : Set ℝ)) := measurableSet_Icc.prod MeasurableSet.univ
  have e : trK σ f = (Icc (σ - 1) σ ×ˢ (univ : Set ℝ)).indicator fun x => f x.1 := by
    funext x
    by_cases h : x.1 ∈ Icc (σ - 1) σ <;> simp [trK, h, Set.indicator, Set.mem_prod]
  rw [e, memLp_indicator_iff_restrict hS]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := σ - 1) (b := σ)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound (hf.comp continuous_fst).aestronglyMeasurable C ?_
  exact (ae_restrict_iff' hS).2 (ae_of_all _ fun x hx => hC x.1 hx.1)

/-- The index `∂_s` in `idx m`. -/
def p10 (hm : 1 ≤ m) : idx m := ⟨(1, 0), mem_idx.2 (by omega)⟩

/-- The circle average `[u]_σ` on `H^{m+1,δ}(ℝ × S¹)`:
`[u]_σ = ∫_{[σ-1,σ] × S¹} (ρ(s - σ) ∂_s u + ρ'(s - σ) u)`, i.e. `∫_{s ≤ σ} ∂_s(ρ(s - σ) u)`. -/
def trH (hm : 1 ≤ m) (σ : ℝ) : H m hδ →L[ℝ] ℝ :=
  (pairing (trK σ fun s => trCut (s - σ))
      (memLp_trK σ (contDiff_trCut.continuous.comp (continuous_sub_right σ)))).comp
      (dvCLM m hδ (p10 hm)) +
    (pairing (trK σ fun s => deriv trCut (s - σ))
      (memLp_trK σ (continuous_deriv_trCut.comp (continuous_sub_right σ)))).comp
      (valCLM m hδ)

lemma val_toH {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) : valCLM m hδ (toH m hδ hφ) =ᵐ[cyl] φ :=
  (hφ.memLp 2).coeFn_toLp

/-- On test functions, `[φ]_σ = ∫_0^1 φ(σ, t) dt`. -/
theorem trH_toH (hm : 1 ≤ m) (σ : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    trH hm σ (toH m hδ hφ) = ∫ t in Ioc (0 : ℝ) 1, φ (σ, t) := by
  have hv := val_toH (m := m) (hδ := hδ) hφ
  have hd : dvCLM m hδ (p10 hm) (toH m hδ hφ) =ᵐ[cyl] Ds φ :=
    (coeFn_dvCLM _ _).trans (dv_unique _ _ ((hφ.smPer.hasWeakDeriv 1 0).congr_ae hv.symm
      (ae_eq_refl _)) (hφ.ds.memLp 2))
  simp only [trH, add_apply, ContinuousLinearMap.comp_apply, pairing_apply]
  set k1 := trK σ fun s => trCut (s - σ)
  set k2 := trK σ fun s => deriv trCut (s - σ)
  have hk1 : MemLp k1 2 cyl := memLp_trK σ (contDiff_trCut.continuous.comp (continuous_sub_right σ))
  have hk2 : MemLp k2 2 cyl := memLp_trK σ (continuous_deriv_trCut.comp (continuous_sub_right σ))
  have e1 : ∫ x, (dvCLM m hδ (p10 hm) (toH m hδ hφ) : ℝ × ℝ → ℝ) x * k1 x ∂cyl =
      ∫ x, Ds φ x * k1 x ∂cyl := integral_congr_ae (hd.mono fun x hx => by simp only [hx])
  have e2 : ∫ x, (valCLM m hδ (toH m hδ hφ) : ℝ × ℝ → ℝ) x * k2 x ∂cyl =
      ∫ x, φ x * k2 x ∂cyl := integral_congr_ae (hv.mono fun x hx => by simp only [hx])
  rw [e1, e2]
  have i1 : Integrable (fun x => Ds φ x * k1 x) cyl :=
    (hφ.ds.integrable_mul hk1).congr (ae_of_all _ fun x => mul_comm _ _)
  have i2 : Integrable (fun x => φ x * k2 x) cyl :=
    (hφ.integrable_mul hk2).congr (ae_of_all _ fun x => mul_comm _ _)
  set G' : ℝ → ℝ → ℝ := fun t s => deriv trCut (s - σ) * φ (s, t) + trCut (s - σ) * Ds φ (s, t)
  have e3 : (fun x => Ds φ x * k1 x + φ x * k2 x) =
      fun x => (Icc (σ - 1) σ).indicator (G' x.2) x.1 := by
    funext x
    by_cases h : x.1 ∈ Icc (σ - 1) σ <;> simp [k1, k2, trK, h, G']
    ring
  rw [← integral_add i1 i2, e3]
  have hi : Integrable (fun x : ℝ × ℝ => (Icc (σ - 1) σ).indicator (G' x.2) x.1) cyl := by
    rw [← e3]; exact i1.add i2
  rw [cyl, integral_prod_symm _ hi]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hder : ∀ s, HasDerivAt (fun s => trCut (s - σ) * φ (s, t)) (G' t s) s := fun s =>
    (HasDerivAt.comp_sub_const s σ ((contDiff_trCut.differentiable (by simp) _).hasDerivAt)).mul
      (hasDerivAt_s hφd s t)
  have hcont : Continuous (G' t) := by
    have h1 : Continuous fun s : ℝ => φ (s, t) := hφ.smooth.continuous.comp (by fun_prop)
    have h2 : Continuous fun s : ℝ => Ds φ (s, t) :=
      (contDiff_Ds hφ.smooth).continuous.comp (by fun_prop)
    exact ((continuous_deriv_trCut.comp (continuous_sub_right σ)).mul h1).add
      ((contDiff_trCut.continuous.comp (continuous_sub_right σ)).mul h2)
  simp only
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
      (hcont.intervalIntegrable _ _)]
  simp [trCut_zero, trCut_neg_one]

/-! ### Properties of the circle average -/

lemma mulHL_toH {χ : ℝ → ℝ} (hχ : Mult m χ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    mulHL χ hχ (toH m hδ hφ) = toH m hδ (hφ.mul_s hχ.smooth) := by
  apply valCLM_injective
  apply Lp.ext
  filter_upwards [val_mulHL (hδ := hδ) χ hχ (toH m hδ hφ), val_toH (m := m) (hδ := hδ) hφ,
    val_toH (m := m) (hδ := hδ) (hφ.mul_s hχ.smooth)] with x h1 h2 h3
  rw [h1, h2, h3]

lemma shH_toH (R ϑ : ℝ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    shH R ϑ (toH m hδ hφ) = toH m hδ (hφ.add_const (-R, -ϑ)) := by
  apply valCLM_injective
  apply Lp.ext
  have hq := (measurePreserving_shT R ϑ).quasiMeasurePreserving
  filter_upwards [val_shH (hδ := hδ) R ϑ (toH m hδ hφ),
    hq.ae_eq_comp (val_toH (m := m) (hδ := hδ) hφ),
    val_toH (m := m) (hδ := hδ) (hφ.add_const (-R, -ϑ))] with x h1 h2 h3
  simp only [Function.comp] at h2
  rw [h1, h2, h3, hφ.eq_shT_sub]

/-- `[χ u]_σ = χ(σ) [u]_σ`. -/
theorem trH_mulHL (hm : 1 ≤ m) (σ : ℝ) {χ : ℝ → ℝ} (hχ : Mult m χ) (u : H m hδ) :
    trH hm σ (mulHL χ hχ u) = χ σ * trH hm σ u := by
  have := Continuous.ext_on (dense_test m hδ)
    ((trH hm σ).comp (mulHL χ hχ)).continuous ((χ σ) • trH (hδ := hδ) hm σ).continuous
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
      rw [mulHL_toH, trH_toH, trH_toH, ← integral_const_mul])
  exact congrFun this u

/-- `[u(· - R, · - ϑ)]_σ = [u]_{σ - R}`. -/
theorem trH_shH (hm : 1 ≤ m) (σ R ϑ : ℝ) (u : H m hδ) :
    trH hm σ (shH R ϑ u) = trH hm (σ - R) u := by
  have := Continuous.ext_on (dense_test m hδ)
    ((trH hm σ).comp (shH R ϑ)).continuous (trH (hδ := hδ) hm (σ - R)).continuous
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [ContinuousLinearMap.comp_apply]
      rw [shH_toH, trH_toH, trH_toH]
      have hp : Function.Periodic (fun t => φ (σ - R, t)) 1 := fun t => hφ.periodic _ t
      rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
      simp only [Prod.mk_add_mk, ← sub_eq_add_neg]
      rw [intervalIntegral.integral_comp_sub_right (fun t => φ (σ - R, t)) ϑ]
      have := hp.intervalIntegral_add_eq (-ϑ) 0
      rw [zero_add, neg_add_eq_sub] at this
      rw [zero_sub, this])
  exact congrFun this u

/-- `[χ]_σ = χ(σ)` for a test function `χ(s)`. -/
theorem trH_toH_s (hm : 1 ≤ m) (σ : ℝ) {χ : ℝ → ℝ} (hχ : IsTest fun x : ℝ × ℝ => χ x.1) :
    trH hm σ (toH m hδ hχ) = χ σ := by
  rw [trH_toH]; simp

/-- If `u` vanishes on `I × S¹` and `η` is a multiplier vanishing off `I` with `η(σ) = 1`,
then `[u]_σ = 0`. -/
theorem trH_eq_zero_of_vanish (hm : 1 ≤ m) (σ : ℝ) {I : Set ℝ} {η : ℝ → ℝ} (hη : Mult m η)
    (hηI : ∀ s ∉ I, η s = 0) (hησ : η σ = 1) {u : H m hδ}
    (hu : ∀ᵐ x ∂cyl, x.1 ∈ I → valCLM m hδ u x = 0) : trH hm σ u = 0 := by
  have h0 : mulHL η hη u = 0 := by
    apply valCLM_injective
    apply Lp.ext
    filter_upwards [val_mulHL (hδ := hδ) η hη u, hu,
      (valCLM m hδ).map_zero ▸ Lp.coeFn_zero ℝ 2 cyl] with x h1 h2 h3
    rw [h1, h3, Pi.zero_apply]
    by_cases hx : x.1 ∈ I
    · rw [h2 hx, mul_zero]
    · rw [hηI _ hx, zero_mul]
  have := trH_mulHL hm σ hη u
  rwa [h0, map_zero, hησ, one_mul, eq_comm] at this

/-- The circle average does not depend on the level: it only sees the `L²` class. -/
theorem trH_eq_of_val {m' : ℕ} {δ' : ℝ} {hδ' : 0 ≤ δ'} (hm : 1 ≤ m) (hm' : 1 ≤ m') (σ : ℝ)
    {u : H m hδ} {u' : H m' hδ'} (h : valCLM m hδ u = valCLM m' hδ' u') :
    trH hm σ u = trH hm' σ u' := by
  simp only [trH, add_apply, ContinuousLinearMap.comp_apply, pairing_apply]
  rw [h]
  congr 1
  have hd : (dvCLM m hδ (p10 hm) u : ℝ × ℝ → ℝ) =ᵐ[cyl] dvCLM m' hδ' (p10 hm') u' := by
    refine (coeFn_dvCLM _ u).trans ((dv_unique _ _ ?_ (dv_memLp (H.toSub u') (p10 hm'))).trans
      (coeFn_dvCLM _ u').symm)
    have := (dv_spec (H.toSub u') (p10 hm')).1
    have e : ((H.toSub u : Lp ℝ 2 cyl) : ℝ × ℝ → ℝ) = ((H.toSub u' : Lp ℝ 2 cyl)) :=
      congrArg (fun f : Lp ℝ 2 cyl => (f : ℝ × ℝ → ℝ)) h
    rw [e]; exact this
  refine integral_congr_ae ?_
  filter_upwards [hd] with x hx
  rw [hx]

end GWMemoir.Neck
