import GWMemoir.LinearCRNodesOp
import GWMemoir.CokernelNodesNeck

/-!
# The linearized Cauchy–Riemann operator at a constant map, with nodes: representatives and kernel

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), continuing `GWMemoir.LinearCRNodesOp`.

* `neckRowN_rep`: on a neck, `σ` is holomorphic, so the neck row of `linOpN` represents the form
  `½ (dη + J(q) ∘ dη ∘ j)` read in the polar chart (`formInPolar_projF`).
* **`isFormRep_linOpN`**: `linOpN v` represents `projF J(q) (dη)` for every representative `v`
  of a continuous section `η`; **`linOpN_mem`**, **`linCRN`**: `D` as a bounded operator
  `H^{3,δ₀}_c(S, u*TQ) → H^{2,δ₀}`.
* **`linCRN_ker_equiv`**: on two spheres joined at a node (`twoSpheres`), `E ≃ ker D`, the
  constant sections (`kerN_eq_range`, `IsFormRep.unique`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The neck rows on representatives -/

section NeckRep

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (G : GlueDataN A)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

lemma ae_fst_ne (s₀ : ℝ) : ∀ᵐ x ∂cyl, x.1 ≠ s₀ :=
  Measure.quasiMeasurePreserving_fst.ae (compl_mem_ae_iff.2 (measure_singleton s₀))

/-- The shift `u ↦ u(s - R, t)` on representatives. -/
lemma ae_comp_shT {f g : ℝ × ℝ → ℝ} (h : f =ᵐ[cyl] g) (R : ℝ) :
    (fun x => f (Neck.shT R 0 x)) =ᵐ[cyl] fun x => g (x.1 - R, x.2) := by
  filter_upwards [(Neck.measurePreserving_shT R 0).quasiMeasurePreserving.ae_eq_comp h,
    Neck.ae_snd_mem] with x h1 h2
  simp only [Function.comp_apply] at h1
  rw [h1]
  simp only [Neck.shT, Neck.rot_of_mem h2]

lemma coeFn_shH_s {k : ℕ} {d : ℝ} {hd : 0 ≤ d} (u : H k hd) {g : ℝ × ℝ → ℝ}
    (hg : (H.val u : ℝ × ℝ → ℝ) =ᵐ[cyl] g) (R : ℝ) :
    (H.val (Neck.shH R 0 u) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => g (x.1 - R, x.2) :=
  (Neck.val_shH R 0 u).trans (ae_comp_shT hg R)

variable {η : Section E X} {v : (blocks A δ h0 hmono) 0}

/-- The disc pieces of the neck row `(j, k)`, on a representative:
`∑_i β'(s - s₀) ρ_i(σ) η_k(σ)`. -/
lemma neckD_rep (hr : IsRep η v) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    (H.val (∑ i, ∑ a, (Neck.shH 0 (G.θ a)) ((G.Dd j i a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (G.cD_smooth j i a) (G.cD_supp j i a) (Neck.δ_nonneg δ h0 hmono 0)
        (incl32 δ h0 hmono (secProj δ h0 hmono (i, k) v)))) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
      ∑ i, dTr (x.1 - A.s0 j) * G.ρ i (X.polar (A.hol j) x) *
        crd k (η (X.polar (A.hol j) x)) := by
  have h1 : ∀ i a, (H.val ((Neck.shH 0 (G.θ a)) ((G.Dd j i a).op 2 (Neck.δ_nonneg δ h0 hmono 0)
      (G.cD_smooth j i a) (G.cD_supp j i a) (Neck.δ_nonneg δ h0 hmono 0)
        (incl32 δ h0 hmono (secProj δ h0 hmono (i, k) v)))) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
      G.cD j i a (Neck.shT 0 (G.θ a) x) *
        discRep A i k η ((G.Dd j i a).ψ (Neck.shT 0 (G.θ a) x)) := by
    intro i a
    have h2 := (ChartChange.coeFn_op (G.cD_smooth j i a) (G.cD_supp j i a)
      (Neck.δ_nonneg δ h0 hmono 0) (incl32 δ h0 hmono (secProj δ h0 hmono (i, k) v))).trans
        ((G.Dd j i a).comp_congr (G.cD_supp j i a) (hr.1 i k))
    exact (Neck.val_shH 0 (G.θ a) _).trans
      ((Neck.measurePreserving_shT 0 (G.θ a)).quasiMeasurePreserving.ae_eq_comp h2)
  filter_upwards [coeFn_sumH _ _, ae_all_iff.2 fun i => coeFn_sumH (k := 2)
      (hd := Neck.δ_nonneg δ h0 hmono 0) Finset.univ fun a => (Neck.shH 0 (G.θ a))
        ((G.Dd j i a).op 2 (Neck.δ_nonneg δ h0 hmono 0) (G.cD_smooth j i a) (G.cD_supp j i a)
          (Neck.δ_nonneg δ h0 hmono 0) (incl32 δ h0 hmono (secProj δ h0 hmono (i, k) v))),
    ae_all_iff.2 fun i => ae_all_iff.2 (h1 i)] with x e1 e2 e3
  rw [e1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e2 i, Finset.sum_congr rfl fun a _ => e3 i a]
  have e : ∀ a, G.cD j i a (Neck.shT 0 (G.θ a) x) *
      discRep A i k η ((G.Dd j i a).ψ (Neck.shT 0 (G.θ a) x)) =
      G.cD j i a (Neck.shT 0 (G.θ a) x) *
        discCut ((G.Dd j i a).ψ (Neck.shT 0 (G.θ a) x)) * crd k (η (X.polar (A.hol j) x)) := by
    intro a
    rw [discRep_const (fun _ => rfl)]
    by_cases hK : Neck.shT 0 (G.θ a) x ∈ (G.Dd j i a).K
    · rw [G.Dd_pt j i a _ hK]
      obtain ⟨n, hn⟩ := Neck.rot_int (G.θ a) x.2
      have hx : ((Neck.shT 0 (G.θ a) x).1, (Neck.shT 0 (G.θ a) x).2 + G.θ a) =
          (x.1, x.2 + (n : ℝ)) := by
        simp only [Neck.shT, sub_zero, hn]; congr 1; ring
      rw [hx, polar_add_int]
      ring
    · rw [(G.Dd j i a).eq_zero_off (G.cD_supp j i a) hK]; ring
  rw [Finset.sum_congr rfl fun a _ => e a, ← Finset.sum_mul, G.cD_sum]

omit G in
/-- A continuous representative of a neck block vanishes on `s < 0`, with its derivatives. -/
lemma neck_rep_zero (hr : IsRep η v) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E))
    {g gs gt : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hwg : (H.val (neckBlock v j k).2 : ℝ × ℝ → ℝ) =ᵐ[cyl] g)
    (hder : ∀ x ∈ openStrip, HasFDerivAt g
      (gs x • ContinuousLinearMap.fst ℝ ℝ ℝ + gt x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    {x : ℝ × ℝ} (hx : x ∈ Iio (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) : g x = 0 ∧ gs x = 0 ∧ gt x = 0 := by
  set V : Set (ℝ × ℝ) := Iio (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1
  have hV : IsOpen V := isOpen_Iio.prod isOpen_Ioo
  have hF0 : ∀ y ∈ V, neckRep A j k η y = 0 := fun y hy => by
    simp only [neckRep, Real.smoothTransition.zero_of_nonpos (le_of_lt hy.1), zero_mul]
  have hae : g =ᵐ[cyl] neckRep A j k η := hwg.symm.trans (hr.2 j k).2
  rw [cyl_eq_vol_restrict] at hae
  have hsub : V ⊆ univ ×ˢ Ioc 0 1 := prod_mono (subset_univ _) Ioo_subset_Ioc_self
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hsub hae) hV
    hg.continuousOn (continuousOn_const.congr fun y hy => hF0 y hy)
  have hz : ∀ y ∈ V, g y = 0 := fun y hy => (heq hy).trans (hF0 y hy)
  refine ⟨hz x hx, ?_⟩
  have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] g := by
    filter_upwards [hV.mem_nhds hx] with y hy using (hz y hy).symm
  have h1 := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq hev.symm
  have h2 := (hder x ⟨mem_univ _, hx.2⟩).unique h1
  have e1 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) h2
  have e2 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (0, 1)) h2
  exact ⟨by simpa using e1, by simpa using e2⟩

omit G in
/-- A continuous representative of a neck block is the neck representative on `s > 0`. -/
lemma neck_rep_eq (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) (j : Fin A.nn)
    (k : Fin (Module.finrank ℝ E)) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hwg : (H.val (neckBlock v j k).2 : ℝ × ℝ → ℝ) =ᵐ[cyl] g) :
    EqOn g (neckRep A j k η) (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) := by
  have hV : IsOpen (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) := isOpen_Ioi.prod isOpen_Ioo
  have hae : g =ᵐ[cyl] neckRep A j k η := hwg.symm.trans (hr.2 j k).2
  rw [cyl_eq_vol_restrict] at hae
  have hsub : Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ univ ×ˢ Ioc 0 1 :=
    prod_mono (subset_univ _) Ioo_subset_Ioc_self
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hsub hae) hV
    hg.continuousOn ((continuousOn_neckRep A continuous_const hc j k).mono
      (prod_mono subset_rfl (subset_univ _)))

omit G in
/-- **The partial derivatives of `v⁺` from the neck block**: on `s > s₀`, `0 < t < 1`,
`β ∂_s v⁺_k = ∂_s v_k(s - s₀, t) - β'(v⁺_k - c_k)` and `β ∂_t v⁺_k = ∂_t v_k(s - s₀, t)`. -/
lemma neck_partials (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) (j : Fin A.nn)
    (k : Fin (Module.finrank ℝ E)) {g gs gt : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hwg : (H.val (neckBlock v j k).2 : ℝ × ℝ → ℝ) =ᵐ[cyl] g)
    (hder : ∀ x ∈ openStrip, HasFDerivAt g
      (gs x • ContinuousLinearMap.fst ℝ ℝ ℝ + gt x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    {Vs Vt : ℝ × ℝ → E}
    (hV : ∀ x ∈ neckU A j 0, HasFDerivAt (vPolar A j η)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Vs x) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Vt x)) x)
    {x : ℝ × ℝ} (hx : x ∈ neckU A j 0) :
    Real.smoothTransition (x.1 - A.s0 j) * crd k (Vs x) =
        gs (x.1 - A.s0 j, x.2) - dTr (x.1 - A.s0 j) *
          (crd k (vPolar A j η x) - neckConst A j k η) ∧
      Real.smoothTransition (x.1 - A.s0 j) * crd k (Vt x) = gt (x.1 - A.s0 j, x.2) := by
  set T : ℝ × ℝ → ℝ × ℝ := fun y => (y.1 - A.s0 j, y.2)
  have hTU : ∀ y ∈ neckU A j 0, T y ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 := fun y hy => by
    obtain ⟨h1, h2, h3⟩ := hy
    refine ⟨?_, ?_, ?_⟩ <;> simp [T] <;> linarith
  have heq := neck_rep_eq hc hr j k hg hwg
  set F : ℝ × ℝ → ℝ := fun y => Real.smoothTransition (y.1 - A.s0 j) *
    (crd k (vPolar A j η y) - neckConst A j k η)
  have hFg : ∀ y ∈ neckU A j 0, F y = g (T y) := fun y hy => by
    rw [heq (hTU y hy), neckRep_const]
    simp only [F, T, sub_add_cancel]
    rfl
  have hev : F =ᶠ[𝓝 x] fun y => g (T y) := by
    filter_upwards [(isOpen_neckU j 0).mem_nhds hx] with y hy using hFg y hy
  have hT' : HasFDerivAt T (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x := by
    have : T = fun y => y - (A.s0 j, 0) := by funext y; ext <;> simp [T]
    rw [this]; exact (hasFDerivAt_id x).sub_const _
  have hGT := (hder (T x) ⟨mem_univ _, (hTU x hx).2⟩).comp x hT'
  have hβ : HasFDerivAt (fun y : ℝ × ℝ => Real.smoothTransition (y.1 - A.s0 j))
      (dTr (x.1 - A.s0 j) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
    have h1 : HasDerivAt (fun s => Real.smoothTransition (s - A.s0 j))
        (dTr (x.1 - A.s0 j)) x.1 := by
      have := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
        (x.1 - A.s0 j)).hasDerivAt.comp_sub_const x.1 (A.s0 j)
      exact this
    have := h1.comp_hasFDerivAt x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
    refine this.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
    simp [mul_comm]
  have hv : HasFDerivAt (fun y => crd k (vPolar A j η y) - neckConst A j k η)
      ((crdL k).comp ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Vs x) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Vt x))) x :=
    ((crdL k).hasFDerivAt.comp x (hV x hx)).sub_const _
  have hF := hβ.mul hv
  have hu := hF.unique (hGT.congr_of_eventuallyEq hev)
  have e1 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) hu
  have e2 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (0, 1)) hu
  simp [crdL_apply, T] at e1 e2 ⊢
  constructor
  · linarith
  · linarith

/-- On the support of `β'(s - s₀)`, the partition reads `∑ ρ_i(σ) + χ(s) = 1`. -/
lemma GlueDataN.sum_neck (j : Fin A.nn) {x : ℝ × ℝ} (h1 : A.s0 j ≤ x.1) (h2 : x.1 ≤ A.s0 j + 1) :
    ∑ i, G.ρ i (X.polar (A.hol j) x) + G.χ j x.1 = 1 := by
  have h := G.sum_one (X.polar (A.hol j) x)
  rw [Finset.sum_congr rfl fun j' _ => G.χS_polar j j' x h1 h2, Finset.sum_ite_eq'] at h
  simpa using h

omit G in
lemma crd_J (J₀ : E →L[ℝ] E) (k : Fin (Module.finrank ℝ E)) (w : E) :
    crd k (J₀ w) = ∑ l, Jm J₀ k l * crd l w := by
  conv_lhs => rw [← crd_basis_sum w]
  simp only [map_sum, map_smul, smul_eq_mul, Jm]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **The neck rows of `linOpN` are the representatives of `½ (dη + J₀ ∘ dη ∘ j)`.** -/
theorem neckRowN_rep (hsm : NeckSmooth A) (hc : IsContSection (fun _ => q) η) (hr : IsRep η v)
    (J₀ : E →L[ℝ] E) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    (H.val (neckRowN G δ h0 hmono J₀ (j, k) v) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      formNeckRep A j k (projF J₀ (dForm η)) := by
  choose g gs gt hg hgs hgt hwg hwgs hwgt hder using
    fun l => exists_C1_rep (neckBlock v j l).2
  obtain ⟨Vs, Vt, -, -, hV⟩ := neck_C1 hc hr j 0
  set hδ := Neck.δ_nonneg δ h0 hmono 0
  set X1 := Neck.shH (A.s0 j) 0 (dsH 2 hδ (neckW δ h0 hmono (j, k) v))
  set X2 := fun l => Neck.shH (A.s0 j) 0 (dtH 2 hδ (neckW δ h0 hmono (j, l) v))
  set Y1 := ∑ i, ∑ a, (Neck.shH 0 (G.θ a)) ((G.Dd j i a).op 2 hδ (G.cD_smooth j i a)
    (G.cD_supp j i a) hδ (incl32 δ h0 hmono (secProj δ h0 hmono (i, k) v)))
  set Y2 := Neck.mulHL (mulN (A.s0 j) (G.χ j)) (mult_mulN (G.χ_smooth j) (G.χ_zero j) 2)
    (Neck.shH (A.s0 j) 0 (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v)))
  set Y3 := neckC δ h0 hmono (j, k) v • toH 2 hδ (isTest_cstN (s₀ := A.s0 j) (G.χ_smooth j))
  have e : neckRowN G δ h0 hmono J₀ (j, k) v =
      (1 / 2 : ℝ) • (X1 + ∑ l, Jm J₀ k l • X2 l) - (1 / 2 : ℝ) • (Y1 + Y2 - Y3) := by
    simp only [neckRowN, sub_apply, smul_apply, add_apply, sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, X1, X2, Y1, Y2, Y3]
  rw [e]
  have r1 : (H.val X1 : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => gs k (x.1 - A.s0 j, x.2) :=
    coeFn_shH_s _ (hwgs k) (A.s0 j)
  have r2 : ∀ l, (H.val (X2 l) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => gt l (x.1 - A.s0 j, x.2) :=
    fun l => coeFn_shH_s _ (hwgt l) (A.s0 j)
  have r4 : (H.val Y2 : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => mulN (A.s0 j) (G.χ j) x.1 * g k (x.1 - A.s0 j, x.2) :=
    (Neck.val_mulHL _ (mult_mulN (G.χ_smooth j) (G.χ_zero j) 2) _).trans (by
      filter_upwards [coeFn_shH_s (incl32 δ h0 hmono (neckW δ h0 hmono (j, k) v)) (hwg k) (A.s0 j)]
        with x hx
      exact congrArg (mulN (A.s0 j) (G.χ j) x.1 * ·) hx)
  have r5 : (H.val Y3 : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x =>
      neckConst A j k η * cstN (A.s0 j) (G.χ j) x := by
    filter_upwards [val_smul_ae (neckC δ h0 hmono (j, k) v) (toH 2 hδ
      (isTest_cstN (s₀ := A.s0 j) (G.χ_smooth j))), val_toH (m := 2) (hδ := hδ)
        (isTest_cstN (s₀ := A.s0 j) (G.χ_smooth j))] with x h1 h2
    rw [h1, h2, neckC_apply, (hr.2 j k).1, smul_eq_mul]
  filter_upwards [val_sub_ae (k := 2) _ _, val_smul_ae (k := 2) (1 / 2 : ℝ) _,
    val_smul_ae (k := 2) (1 / 2 : ℝ) _, val_add_ae (k := 2) _ _, val_sub_ae (k := 2) _ _,
    val_add_ae (k := 2) _ _, coeFn_sumH _ _, ae_all_iff.2 fun l => val_smul_ae (k := 2)
      (hd := hδ) (Jm J₀ k l) (X2 l), r1, ae_all_iff.2 r2, neckD_rep G hr j k, r4, r5,
    ae_fst_ne (A.s0 j), ae_openStrip] with x e1 e2 e3 e4 e5 e6 e7 e8 f1 f2 f3 f4 f5 hx1 hxS
  rw [e1, e2, e3, e4, e5, e6, e7, Finset.sum_congr rfl fun l _ => e8 l, f1,
    Finset.sum_congr rfl fun l _ => by rw [smul_eq_mul, f2 l], f3, f4, f5]
  simp only [smul_eq_mul]
  have hx2 : x.2 ∈ Ioo (0 : ℝ) 1 := hxS.2
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · -- `s < A.s0 j`: everything vanishes
    have hT : (x.1 - A.s0 j, x.2) ∈ Iio (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 := ⟨by simp; linarith, hx2⟩
    have hz := fun l => neck_rep_zero hr j l (hg l) (hwg l) (hder l) hT
    have hd0 : dTr (x.1 - A.s0 j) = 0 := dTr_eq_zero_of_neg (by linarith)
    have hm0 : mulN (A.s0 j) (G.χ j) x.1 = 0 := by
      rw [mulN, hd0, zero_mul, zero_div]
    have hc0 : cstN (A.s0 j) (G.χ j) x = 0 := by rw [cstN, hd0, zero_mul]
    rw [formNeckRep, Real.smoothTransition.zero_of_nonpos (by linarith), (hz k).2.1, hm0, hc0]
    simp only [hd0, zero_mul, Finset.sum_const_zero, (hz _).2.2, mul_zero]
    ring
  · -- `s > A.s0 j`
    have hxU : x ∈ neckU A j 0 := ⟨hgt, by simpa using hx2.1, by simpa using hx2.2⟩
    have hp := (A.neck_chart j x hgt.le).1
    have hd := (mdifferentiableAt_of_polar (A.isHol j) hp (hV x hxU).differentiableAt).1
    have hform := formInPolar_projF (q := q) (A.isHol j) hp (hsm j _ hp) hd J₀
    have hfd : fderiv ℝ (fun q => η (X.polar (A.hol j) q)) x = _ := (hV x hxU).fderiv
    rw [hfd] at hform
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', one_smul, zero_smul,
      add_zero, zero_add] at hform
    have hP := fun l => neck_partials hc hr j l (hg l) (hwg l) (hder l) hV hxU
    have hβ : 0 < Real.smoothTransition (x.1 - A.s0 j) :=
      Real.smoothTransition.pos_of_pos (by linarith)
    have hgk : g k (x.1 - A.s0 j, x.2) = Real.smoothTransition (x.1 - A.s0 j) *
        (crd k (vPolar A j η x) - neckConst A j k η) := by
      have hT : (x.1 - A.s0 j, x.2) ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 := ⟨by simp; linarith, hx2⟩
      rw [neck_rep_eq hc hr j k (hg k) (hwg k) hT, neckRep_const, sub_add_cancel]
      rfl
    -- the zeroth-order bracket
    have hbr : ∑ i, dTr (x.1 - A.s0 j) * G.ρ i (X.polar (A.hol j) x) *
          crd k (η (X.polar (A.hol j) x)) + mulN (A.s0 j) (G.χ j) x.1 * g k (x.1 - A.s0 j, x.2) -
          neckConst A j k η * cstN (A.s0 j) (G.χ j) x =
        dTr (x.1 - A.s0 j) * (crd k (vPolar A j η x) - neckConst A j k η) := by
      rcases le_or_gt x.1 (A.s0 j + 1) with hle | hgt1
      · have hs := G.sum_neck j hgt.le hle
        rw [hgk, mulN, cstN]
        have e3 : ∑ i, dTr (x.1 - A.s0 j) * G.ρ i (X.polar (A.hol j) x) *
            crd k (η (X.polar (A.hol j) x)) = dTr (x.1 - A.s0 j) * (1 - G.χ j x.1) *
              crd k (vPolar A j η x) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, ← hs]
          simp only [add_sub_cancel_right]
          rfl
        rw [e3]
        field_simp
        ring
      · have hd0 : dTr (x.1 - A.s0 j) = 0 := dTr_eq_zero_of_one_lt (by linarith)
        simp only [mulN, cstN, hd0, zero_mul, zero_div, Finset.sum_const_zero, mul_zero,
          sub_zero, add_zero]
    rw [hbr, formNeckRep, hform, map_smul, map_add, crd_J, smul_eq_mul]
    have hk := (hP k).1
    have hl := fun l => (hP l).2
    have e9 : ∑ l, Jm J₀ k l * (Real.smoothTransition (x.1 - A.s0 j) * crd l (Vt x)) =
        Real.smoothTransition (x.1 - A.s0 j) * ∑ l, Jm J₀ k l * crd l (Vt x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    have hsum : ∑ l, Jm J₀ k l * gt l (x.1 - A.s0 j, x.2) =
        Real.smoothTransition (x.1 - A.s0 j) * ∑ l, Jm J₀ k l * crd l (Vt x) := by
      rw [← e9]; exact Finset.sum_congr rfl fun l _ => by rw [hl l]
    rw [hsum]
    linear_combination (-1 / 2 : ℝ) * hk

end NeckRep

/-! ## 2. `D` as an operator between the section space and the fibre -/

section Operator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

include hsm in
/-- **`D v` is the representative of `½ (dη + J₀ ∘ dη ∘ j)`** (Memoir Prop 4.23, p. 118, `a = 0`)
for the representative `v` of a continuous section `η`; on the necks, `σ` is holomorphic, so the
form read along `∂_s σ` is `½ (∂_s v⁺ + J₀ ∂_t v⁺)` (`formInPolar_projF`). -/
theorem isFormRep_linOpN {η : Section E X} {v : (blocks A δ h0 hmono) 0}
    (hc : IsContSection (fun _ => q) η) (hr : IsRep η v) (J₀ : E →L[ℝ] E) :
    IsFormRep (projF J₀ (dForm η)) (linOpN hT G δ h0 hmono J₀ v) :=
  ⟨fun i d k => linOpN_disc_rep hT G hc hr J₀ i d k,
    fun j k => neckRowN_rep G hsm hc hr J₀ j k⟩

include hsm in
/-- `D` maps `H^{3,δ₀}_c(S, u*TQ)` into the fibre `H^{2,δ₀}` of `W` over `u`. -/
theorem linOpN_mem (J : AlmostComplexStructure E Q) {w : (blocks A δ h0 hmono) 0}
    (hw : w ∈ sectionSpace A δ h0 hmono) :
    linOpN hT G δ h0 hmono (J.J q) w ∈ fibreSpace J A δ h0 hmono := by
  rw [sectionSpace_eq_sectionsSub continuous_const A δ h0 hmono] at hw
  obtain ⟨η, hc, -, hr⟩ := hw
  exact formsSub_le J A δ h0 hmono ⟨projF (J.J q) (dForm η), fun x _ => projF_mem J q _ x,
    isFormRep_linOpN hT hsm G hc hr _⟩

variable (δ h0 hmono) in
include hsm in
/-- **The linearization of `∂̄_J` at the constant map `u ≡ q`, with nodes** (Memoir Prop 4.23,
p. 118, level `0`, `a = 0`; the spaces of p. 66 and p. 7), as a bounded operator
`H^{3,δ₀}_c(S, u*TQ) → H^{2,δ₀}`. -/
def linCRN (J : AlmostComplexStructure E Q) :
    sectionSpace A δ h0 hmono →L[ℝ] fibreSpace J A δ h0 hmono :=
  ((linOpN hT G δ h0 hmono (J.J q)).comp (sectionSpace A δ h0 hmono).subtypeL).codRestrict _
    fun w => linOpN_mem hT hsm G J w.2

lemma linCRN_apply (J : AlmostComplexStructure E Q) (w : sectionSpace A δ h0 hmono) :
    (linCRN hT hsm G δ h0 hmono J w : (fibreBlocks A δ h0 hmono) 0) =
      linOpN hT G δ h0 hmono (J.J q) w := rfl

end Operator

/-! ## 3. The kernel on two spheres joined at a node -/

section Kernel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

lemma constBlocksN_mem (e : E) : constBlocksN A δ h0 hmono e ∈ sectionSpace A δ h0 hmono :=
  Submodule.le_topologicalClosure _ ⟨fun _ => e,
    isContSection_of_const (fun _ => rfl) continuous_const, fun _ _ _ => rfl,
    isRep_constBlocks A e⟩

include hsm in
/-- **The kernel of `D` is the constants** (Memoir Prop 4.23, `a = 0`, two spheres joined at a
node): for `v ∈ H^{3,δ₀}_c`, `D v = 0` iff `v` represents a constant section. -/
theorem linOpN_eq_zero_iff {v : (blocks A δ h0 hmono) 0} (hv : v ∈ sectionSpace A δ h0 hmono) :
    linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v = 0 ↔
      v ∈ LinearMap.range (constBlocksN A δ h0 hmono) := by
  rw [← SetLike.mem_coe, ← kerN_eq_range J hsm]
  constructor
  · intro h
    rw [sectionSpace_eq_sectionsSub continuous_const A δ h0 hmono] at hv
    obtain ⟨η, hc, hm, hr⟩ := hv
    have h1 := isFormRep_linOpN twoSpheres_chartsOnto hsm G hc hr (J.J q)
    rw [h] at h1
    exact ⟨η, hc, hm, hr, h1⟩
  · rintro ⟨η, hc, -, hr, hD⟩
    exact (isFormRep_linOpN twoSpheres_chartsOnto hsm G hc hr (J.J q)).unique hD

/-- The constants as elements of the kernel of `linCRN`. -/
def constKerN : E →ₗ[ℝ] (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J).ker where
  toFun e := ⟨⟨constBlocksN A δ h0 hmono e, constBlocksN_mem δ h0 hmono e⟩, by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact (linOpN_eq_zero_iff J hsm G δ h0 hmono (constBlocksN_mem δ h0 hmono e)).2
      ⟨e, rfl⟩⟩
  map_add' e e' := by
    apply Subtype.ext; apply Subtype.ext
    exact map_add (constBlocksN A δ h0 hmono) e e'
  map_smul' c e := by
    apply Subtype.ext; apply Subtype.ext
    exact map_smul (constBlocksN A δ h0 hmono) c e

/-- **`E ≃ ker D`** (Memoir Prop 4.23, `a = 0`, two spheres joined at a node): the kernel of the
linearization on `H^{3,δ₀}_c(S, u*TQ)` is a copy of `E = T_qQ`, the constant sections. -/
def linCRN_ker_equiv : E ≃ₗ[ℝ] (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J).ker :=
  LinearEquiv.ofBijective (constKerN J hsm G δ h0 hmono) ⟨fun e e' h =>
    constBlocksN_injective (A := A) (δ := δ) (h0 := h0) (hmono := hmono)
      (congrArg (fun w : (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J).ker =>
        ((w : sectionSpace A δ h0 hmono) : (blocks A δ h0 hmono) 0)) h), fun w => by
    obtain ⟨⟨v, hv⟩, hw⟩ := w
    rw [LinearMap.mem_ker] at hw
    have h0' : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v = 0 := by
      exact congrArg Subtype.val hw
    obtain ⟨e, he⟩ := (linOpN_eq_zero_iff J hsm G δ h0 hmono hv).1 h0'
    exact ⟨e, by subst he; rfl⟩⟩

theorem finrank_linCRN_ker :
    Module.finrank ℝ ((linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J).ker) =
      Module.finrank ℝ E :=
  (linCRN_ker_equiv J hsm G δ h0 hmono).finrank_eq.symm

end Kernel

/-! ## 4. The neck charts of `IsStdNeck` -/

section StdNeck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- The neck charts `σ₋₁` of `IsStdNeck` (the atlas of `exists_stdNeck_atlas`) have
differentiable inverses, so `NeckSmooth` holds for them. -/
theorem neckSmooth_of_isStdNeck {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
    (hA : IsStdNeck A) : NeckSmooth A := fun j ζ _ => by
  rw [hA j]
  generalize A.node j = y
  rcases y with y | y
  · exact mdifferentiableAt_holChartInl_symm ζ
  · exact mdifferentiableAt_holChartInr_symm ζ

/-- **Witness**: for every `q`, `twoSpheres` has an atlas satisfying both `IsStdNeck` and
`NeckSmooth`. -/
theorem exists_stdNeck_neckSmooth (q : Q) :
    ∃ A : SectionAtlas (E := E) twoSpheres (fun _ => q), IsStdNeck A ∧ NeckSmooth A := by
  obtain ⟨A, hA⟩ := exists_stdNeck_atlas (E := E) q
  exact ⟨A, hA, neckSmooth_of_isStdNeck hA⟩

end StdNeck

end GWMemoir
