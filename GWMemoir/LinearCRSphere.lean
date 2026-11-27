import GWMemoir.LinearCRKernel
import GWMemoir.SphereStability

/-!
# The kernel of the linearized Cauchy–Riemann operator on the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Props 4.7, 4.23, 4.25
near the constant maps).  For the constant map `u ≡ q` from `sphere3` and the operator
`D = linOp` of `GWMemoir.LinearCR` (`linCR` of `GWMemoir.LinearCRKernel`):

* **`const_of_CR`** (Liouville): a bounded map `f : ℂ → E` with `df(iv) = J₀ df(v)`, `J₀² = -1`,
  is constant (each `ℓ ∘ f - i ℓ ∘ J₀ ∘ f` is entire and bounded);
* **`eq_const_of_holo_sphere3`**: a continuous differentiable `η : S² → E` with
  `dη ∘ j = J₀ ∘ dη` is constant (Liouville in the stereographic chart `σ₁`, and continuity at
  `e₂`);
* **`linCR_ker_sphere3`**: `D v = 0` for `v ∈ H^{3,δ₀}_c(S², u*TQ)` iff `v` represents a
  constant section `η ≡ e`; `constBlocks_injective`: the kernel is a copy of `E`;
* **`linCR_ker_uSpace`**: on `E_u` the kernel is `{e | e ∈ H_{u(z)} for z ∈ Σ}`;
  **`linCR_ker_three_points`**: with `H = 0` at `e₀, e₁, e₂` it is `0`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Liouville for `J₀`-holomorphic maps -/

section Liouville

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Liouville**: a bounded `f : ℂ → E` with `df(i v) = J₀ df(v)` is constant. -/
theorem const_of_CR {f : ℂ → E} (hf : Differentiable ℝ f) (J₀ : E →L[ℝ] E)
    (hJ : ∀ w, J₀ (J₀ w) = -w)
    (hCR : ∀ z v, fderiv ℝ f z (Complex.I * v) = J₀ (fderiv ℝ f z v))
    (hb : Bornology.IsBounded (range f)) (z : ℂ) : f z = f 0 := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  set Φ : E →L[ℝ] ℂ := ℓ.smulRight (1 : ℂ) + (ℓ.comp J₀).smulRight (-Complex.I)
  have hΦ : ∀ w, Φ w = (ℓ w : ℂ) - Complex.I * (ℓ (J₀ w) : ℂ) := by
    intro w
    simp only [Φ, _root_.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, Complex.real_smul, mul_one, mul_neg]
    ring
  have hg : Differentiable ℂ (Φ ∘ f) := by
    intro x
    have hd : HasFDerivAt (Φ ∘ f) (Φ.comp (fderiv ℝ f x)) x :=
      Φ.hasFDerivAt.comp x (hf x).hasFDerivAt
    set M := Φ.comp (fderiv ℝ f x)
    have hI : M Complex.I = Complex.I * M 1 := by
      have h1 := hCR x 1
      rw [mul_one] at h1
      simp only [M, ContinuousLinearMap.comp_apply, h1, hΦ, hJ, map_neg, Complex.ofReal_neg]
      linear_combination (ℓ (J₀ (fderiv ℝ f x 1)) : ℂ) * Complex.I_sq
    refine (hasFDerivAt_of_restrictScalars ℝ hd
      (f' := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (M 1)) ?_).differentiableAt
    refine ContinuousLinearMap.ext fun v => ?_
    change v • M 1 = M v
    have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
      apply Complex.ext <;> simp
    conv_rhs => rw [hv]
    rw [map_add, map_smul, map_smul, hI]
    simp only [smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im v]
    ring
  have hbg : Bornology.IsBounded (range (Φ ∘ f)) := by
    rw [range_comp]; exact Φ.lipschitz.isBounded_image hb
  have := congrArg Complex.re (hg.apply_eq_apply_of_bounded hbg z 0)
  simpa [hΦ] using this

end Liouville

/-! ## 2. Holomorphic maps `S² → E` are constant -/

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A continuous differentiable `η : S² → E` with `dη ∘ j = J₀ ∘ dη` is constant.** -/
theorem eq_const_of_holo_sphere3 {η : S2 → E} (hc : Continuous η)
    (hmd : MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E) η) (J₀ : E →L[ℝ] E) (hJ : ∀ w, J₀ (J₀ w) = -w)
    (hh : ∀ y w, mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y (jStdMap y w) =
      J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y w)) (y : S2) :
    η y = η (sig.symm 0) := by
  set f : ℂ → E := fun z => η (sig.symm z)
  have hτ := fun z => mdifferentiable_holChart_symm 1 (by norm_num) z
  have hfm : ∀ z, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z := fun z => (hmd _).comp z (hτ z)
  have hf : Differentiable ℝ f := fun z => mdifferentiableAt_iff_differentiableAt.1 (hfm z)
  have hmf : ∀ z v, fderiv ℝ f z v = mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (sig.symm z) (Dtau z v) := by
    intro z v
    have h : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z = (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (sig.symm z)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) sig.symm z) := mfderiv_comp z (hmd _) (hτ z)
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun T => T v) h
  have hCR : ∀ z v, fderiv ℝ f z (Complex.I * v) = J₀ (fderiv ℝ f z v) := by
    intro z v; rw [hmf, hmf, Dtau_I]; exact hh _ _
  have hb : Bornology.IsBounded (range f) :=
    (isCompact_range hc).isBounded.subset (range_comp_subset_range _ _)
  have hsig : ∀ y, y ≠ pt 2 → η y = f 0 := by
    intro y hy
    rw [← sig.left_inv ((mem_sig_source_iff y).2 hy)]
    exact const_of_CR hf J₀ hJ hCR hb (sig y)
  by_cases h2 : y = pt 2
  swap
  · exact hsig y h2
  subst h2
  set τ' := (holChart (-1) (by norm_num)).symm
  have hτ'c : ContinuousAt (fun w => η (τ' w)) 0 :=
    hc.continuousAt.comp (mdifferentiable_holChart_symm (-1) (by norm_num) 0).continuousAt
  have h1 : Tendsto (fun w => η (τ' w)) (𝓝[≠] 0) (𝓝 (η (pt 2))) := by
    rw [← holChart_neg_symm_zero]; exact hτ'c.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun w => η (τ' w)) (𝓝[≠] 0) (𝓝 (f 0)) := by
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    have e : τ' w = sig.symm w⁻¹ := by
      rw [← holChart_neg_symm_inv w⁻¹ (inv_ne_zero hw), inv_inv]
    change f 0 = η (τ' w)
    rw [e]
    exact (hsig _ ((mem_sig_source_iff _).1 (sig_symm_mem _))).symm
  exact tendsto_nhds_unique h1 h2

end Sphere

/-! ## 3. Representatives -/

section Reps

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hX : X.nodes = ∅) {q : Q}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

include hX in
/-- On a surface without nodes a tuple of blocks represents at most one section's blocks. -/
lemma isRep_unique {u : X.S → Q} {A : SectionAtlas (E := E) X u} {η : Section E X}
    {v w : (blocks A δ h0 hmono) 0} (h : IsRep η v) (h' : IsRep η w) : v = w := by
  have hnn := isEmpty_neck_of_nodes_empty hX A
  exact Prod.ext (funext fun ik => H_ext_ae ((h.1 ik.1 ik.2).trans (h'.1 ik.1 ik.2).symm))
    (funext fun jk => (hnn.false jk.1).elim)

/-- `constBlocks e` represents the constant section `η ≡ e`. -/
lemma isRep_constBlocks (A : SectionAtlas (E := E) X (fun _ => q)) (e : E) :
    IsRep (fun _ => e) (constBlocks A δ h0 hmono e) := by
  have hT : ∀ v : E, tangentCoordChange 𝓘(ℝ, E) q q q v = v := fun v =>
    tangentCoordChange_self (mem_extChartAt_source q)
  refine ⟨fun i k => ?_, fun j k => ⟨rfl, ?_⟩⟩
  · have h1 : (H.val (discBlock (constBlocks A δ h0 hmono e) i k) : ℝ × ℝ → ℝ) =ᵐ[cyl]
        bumpPer (crd k e) := MemLp.coeFn_toLp ((isTest_bumpPer _).memLp 2)
    filter_upwards [h1, bumpPer_ae_eq (crd k e)] with p hp1 hp2
    rw [hp1, hp2, discRep, hT]; rfl
  · rw [show (neckBlock (constBlocks A δ h0 hmono e) j k).2 = 0 from rfl]
    filter_upwards [val_zero_ae (k := 3) (hd := Neck.δ_nonneg δ h0 hmono 0)] with p hp
    rw [hp, neckRep, hT, neckConst, sub_self, mul_zero]; rfl

include hX in
/-- **Two continuous sections with the same representative are equal** (constant `u`, no
nodes). -/
lemma eq_of_isRep {u : X.S → Q} (hu : ∀ x, u x = q) {A : SectionAtlas (E := E) X u}
    {η η' : Section E X} {v : (blocks A δ h0 hmono) 0} (hc : IsContSection u η)
    (hc' : IsContSection u η') (h : IsRep η v) (h' : IsRep η' v) : η = η' := by
  have hnn := isEmpty_neck_of_nodes_empty hX A
  funext y
  rcases A.cover y with ⟨i, p₀, hp₀, rfl⟩ | ⟨j, -⟩
  swap
  · exact (hnn.false j).elim
  have hp₀D : p₀ ∈ discD := mem_discD_of_core hp₀
  have hp2 : 1 / 4 ≤ p₀.2 ∧ p₀.2 ≤ 3 / 4 := by
    constructor <;> nlinarith [sq_nonneg p₀.1, sq_nonneg (p₀.2 - 1 / 4),
      sq_nonneg (p₀.2 - 3 / 4)]
  refine (Module.finBasis ℝ E).ext_elem fun k => ?_
  have hca := ((continuousOn_discRep A (continuous_u hu) hc i k).continuousAt
    (isOpen_discD.mem_nhds hp₀D)).sub ((continuousOn_discRep A (continuous_u hu) hc' i k
      ).continuousAt (isOpen_discD.mem_nhds hp₀D))
  have hae : (fun p => discRep A i k η p - discRep A i k η' p) =ᵐ[cyl] 0 := by
    filter_upwards [h.1 i k, h'.1 i k] with p h1 h2
    rw [← h1, ← h2, sub_self]; rfl
  have := eq_zero_of_ae_of_continuousAt (by linarith) (by linarith) hca hae
  rw [Pi.sub_apply, discRep_const hu, discRep_const hu, discCut_eq_one hp₀, one_mul, one_mul,
    sub_eq_zero] at this
  exact this

lemma dForm_const (e : E) : dForm (fun _ : X.S => e) = 0 :=
  funext fun _ => mfderiv_const

lemma projF_zero (J₀ : E →L[ℝ] E) : projF J₀ (0 : Form E X) = 0 := by
  funext y; ext w; simp [projF, twist]

end Reps

/-! ## 4. The kernel on `sphere3` -/

section Kernel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **The kernel of `D` on `H^{3,δ₀}_c(S², u*TQ)` is the constants** (Memoir §4, Liouville on
`S²`): `D v = 0` iff `v` represents a constant section `η ≡ e`. -/
theorem linCR_ker_sphere3 {v : (blocks A δ h0 hmono) 0} (hv : v ∈ sectionSpace A δ h0 hmono) :
    linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v = 0 ↔
      ∃ e : E, v = constBlocks A δ h0 hmono e := by
  have hu : ∀ x, (fun _ : sphere3.S => q) x = q := fun _ => rfl
  constructor
  · intro h
    rw [sectionSpace_eq_of_nodes_empty continuous_const rfl A δ h0 hmono] at hv
    obtain ⟨η, hc, -, hr⟩ := hv
    obtain ⟨hmd, hP⟩ := projF_eq_zero_of_linOp rfl sphere3_chartsOnto hu G hc hr (J.J q) h
    have hηc : Continuous η := continuous_of_isContSection hu hc
    have hconst : η = fun _ => η (sig.symm 0) :=
      funext (eq_const_of_holo_sphere3 hηc hmd (J.J q) (J.J_J q) fun y w =>
        holo_of_projF (J := J) (congrFun hP y) w)
    refine ⟨η (sig.symm 0), isRep_unique rfl (hconst ▸ hr) (isRep_constBlocks A _)⟩
  · rintro ⟨e, rfl⟩
    have h1 := isFormRep_linOp rfl sphere3_chartsOnto hu G
      (isContSection_of_const hu continuous_const)
      (isRep_constBlocks (δ := δ) (h0 := h0) (hmono := hmono) A e) (J.J q)
    rw [dForm_const, projF_zero] at h1
    exact h1.unique isFormRep_zero

/-- The same statement for the bounded operator `linCR`. -/
theorem linCR_ker_sphere3' (w : sectionSpace A δ h0 hmono) :
    linCR rfl sphere3_chartsOnto (fun _ => rfl) G J w = 0 ↔
      ∃ e : E, (w : (blocks A δ h0 hmono) 0) = constBlocks A δ h0 hmono e := by
  rw [← linCR_ker_sphere3 J G δ h0 hmono w.2, ← linCR_apply rfl sphere3_chartsOnto
    (fun _ => rfl) G J w, Submodule.coe_eq_zero]

/-- The constant sections are distinct: the kernel is a copy of `E`, of dimension
`dim E = 2n`. -/
theorem constBlocks_injective : Injective (constBlocks A δ h0 hmono) := by
  intro e e' h
  have hc := fun e : E => isContSection_of_const (u := fun _ : sphere3.S => q)
    (fun _ => rfl) (η := fun _ => e) continuous_const
  have h1 := isRep_constBlocks (δ := δ) (h0 := h0) (hmono := hmono) A e'
  rw [← h] at h1
  exact congrFun (eq_of_isRep rfl (fun _ => rfl) (hc e) (hc e') (isRep_constBlocks A e) h1)
    (pt 0)

/-- **The kernel of `D` on `E_u`** (Memoir p. 68): the constants `e ∈ ⋂_{z ∈ Σ} H_{u(z)}`. -/
theorem linCR_ker_uSpace (C : LinearConstraints sphere3 E) {v : (blocks A δ h0 hmono) 0}
    (hv : v ∈ uSpace A δ h0 hmono C) :
    linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v = 0 ↔
      ∃ e : E, (∀ l, e ∈ C.H l) ∧ v = constBlocks A δ h0 hmono e := by
  have hvS := uSpace_le A δ h0 hmono C hv
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := (linCR_ker_sphere3 J G δ h0 hmono hvS).1 h
    rw [uSpace_eq A δ h0 hmono C (constraintsClosed_of_nodes_empty continuous_const rfl A δ h0
      hmono C)] at hv
    obtain ⟨η, hc, -, hr, hH⟩ := hv
    have he : η = fun _ => e := eq_of_isRep rfl (fun _ => rfl) hc
      (isContSection_of_const (fun _ => rfl) continuous_const) hr (isRep_constBlocks A e)
    exact ⟨e, fun l => by simpa [he] using hH l, rfl⟩
  · rintro ⟨e, -, rfl⟩
    exact (linCR_ker_sphere3 J G δ h0 hmono hvS).2 ⟨e, rfl⟩

/-- The three constraints `H = 0` at the marked points `e₀, e₁, e₂`. -/
def threePoints : LinearConstraints sphere3 E := ⟨3, pt, fun _ => ⊥⟩

/-- **With the three point constraints the kernel of `D` on `E_u` is `0`.** -/
theorem linCR_ker_three_points {v : (blocks A δ h0 hmono) 0}
    (hv : v ∈ uSpace A δ h0 hmono threePoints) :
    linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v = 0 ↔ v = 0 := by
  rw [linCR_ker_uSpace J G δ h0 hmono threePoints hv]
  constructor
  · rintro ⟨e, he, rfl⟩
    have he0 : e = 0 := (Submodule.mem_bot ℝ).1 (he (0 : Fin 3))
    subst he0
    exact isRep_unique rfl (isRep_constBlocks A 0) isRep_zero
  · rintro rfl
    refine ⟨0, fun l => (threePoints (E := E)).H l |>.zero_mem, ?_⟩
    exact isRep_unique rfl isRep_zero (isRep_constBlocks A 0)

end Kernel

end GWMemoir
