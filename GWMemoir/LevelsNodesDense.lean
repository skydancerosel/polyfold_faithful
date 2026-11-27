import GWMemoir.LevelsNodesOp

/-!
# The range of `D` with nodes is dense on every level

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Propositions 4.7,
4.23): at a constant map from two spheres joined at a node (`twoSpheres`), the argument of
`GWMemoir.LinearCRNodesDense` on level `M`, for weights with `δ_m < 2π` for all `m`.

* `smoothBlocks2L`: the level-`M` blocks of a smooth section, for `δ_M < 2π`
  (`memH_neckRep`); `toBase_smoothBlocks2L`: they lie over the level-`0` blocks, so a smooth
  section with matching values at the node is a smooth point of the section blocks
  (`smoothBlocks2L_mem_smoothLvl`).
* `discOutNL`, `neckOutNL`, `glueNL`, `phiNL`: the operator `Φ` of
  `GWMemoir.LinearCRNodesDenseOp` on level `M`; `toBase_phiNL`.
* `phiN_testTuple_rep`: `Φ` maps a tuple of test functions to the representative of a form
  anti-linear and smooth on both spheres (the neck test forms, `neckTestForms_of_glueCharts`).
* **`denseNL`**: every form of class `(2+M, δ_M)` in the fibre is a limit, in `H^{2+M,δ_M}`, of
  `D w` with `w` a smooth point of the section space.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Smooth sections on every level -/

section Smooth

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  {ξ : Section E twoSpheres} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) (hA : IsStdNeck A)

/-- The neck block `β (v⁺ - c) ∈ H^{3+M,δ_M}` of a smooth section, for `δ_M < 2π`. -/
def neckHL (M : ℕ) (hδ : δ M < 2 * Real.pi) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    H (3 + M) (Neck.δ_nonneg δ h0 hmono M) :=
  (⟨(memLp_neckRep hξ hA j k).toLp _,
    mem_Hsub_toLp _ (memLp_neckRep hξ hA j k) (memH_neckRep hξ hA j k (3 + M) hδ)⟩ : Hsub _ _)

/-- The level-`M` blocks of a smooth section of `twoSpheres`, for `δ_M < 2π`. -/
def smoothBlocks2L (M : ℕ) (hδ : δ M < 2 * Real.pi) : (blocks A δ h0 hmono) M :=
  (fun ik => toHdisc (contDiff_secDisc2 hξ ik.1 ik.2) (tsupport_secDisc2 ik.1 ik.2) (3 + M)
      (Neck.δ_nonneg δ h0 hmono M),
    fun jk => (crd jk.2 (ξ (A.node jk.1)), neckHL δ h0 hmono hξ hA M hδ jk.1 jk.2))

lemma toBase_smoothBlocks2L (M : ℕ) (hδ : δ M < 2 * Real.pi) (hδ0 : δ 0 < 2 * Real.pi) :
    (blocks A δ h0 hmono).toBase M (smoothBlocks2L δ h0 hmono hξ hA M hδ) =
      smoothBlocks2 δ h0 hmono hξ hA hδ0 := by
  refine Prod.ext (funext fun ik => ?_) (funext fun jk => ?_)
  · apply valCLM_injective (m := 3) (hδ := Neck.δ_nonneg δ h0 hmono 0)
    exact (val_blocks_toBase M _ ik).trans (val_toHdisc_eq (k := 3 + M)
      (hd := Neck.δ_nonneg δ h0 hmono M) (l := 3 + 0) (he := Neck.δ_nonneg δ h0 hmono 0)
        (contDiff_secDisc2 hξ ik.1 ik.2) (tsupport_secDisc2 ik.1 ik.2))
  · rw [neck_blocks_toBase]
    refine Prod.ext rfl (valCLM_injective ?_)
    exact Neck.val_toBase δ h0 hmono M _

/-- **A smooth section is a smooth point of the section blocks** when `δ_m < 2π` for all `m`. -/
lemma smoothBlocks2L_mem_smoothLvl (hδ : ∀ m, δ m < 2 * Real.pi) (M : ℕ) :
    smoothBlocks2L δ h0 hmono hξ hA M (hδ M) ∈ (blocks A δ h0 hmono).smoothLvl M :=
  (blocks A δ h0 hmono).mem_smoothLvl_iff.2 fun k => ⟨smoothBlocks2L δ h0 hmono hξ hA k (hδ k), by
    rw [toBase_smoothBlocks2L δ h0 hmono hξ hA k (hδ k) (hδ 0),
      toBase_smoothBlocks2L δ h0 hmono hξ hA M (hδ M) (hδ 0)]⟩

end Smooth

/-! ## 2. The operator `Φ` on level `M` -/

section Operator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q}
  {A : SectionAtlas (E := E) X (fun _ => q)} (hG : GlueCharts A) (F : FormGlueN A)
  (J₀ : E →L[ℝ] E) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-- The disc block `o` of the glued form on level `M`. -/
def discOutNL (o : Ix A) :
    (fibreBlocks A δ h0 hmono) M →L[ℝ] H (2 + M) (Neck.δ_nonneg δ h0 hmono M) :=
  fBlock δ h0 hmono (fun o t => F.D o.1 t.1) (aG A (fun j => F.ρ j)) (F.hcG hT) (F.hsG hT)
      (srcG A) M o +
    ∑ j, ∑ a, ∑ l, ((F.Dn o.1 j a).op (2 + M) (Neck.δ_nonneg δ h0 hmono M)
      (contDiff_cFN hG hT J₀ o.1 j a o.2.1 o.2.2 l) (F.hsN hT hG J₀ o.1 j a o.2.1 o.2.2 l)
      (Neck.δ_nonneg δ h0 hmono M)).comp
        ((Neck.shH (-A.s0 j) (thetaN a)).comp
          ((ContinuousLinearMap.proj (j, l)).comp (ContinuousLinearMap.snd ℝ _ _)))

/-- The neck block `(j, k)` of the glued form on level `M`. -/
def neckOutNL (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) M →L[ℝ] H (2 + M) (Neck.δ_nonneg δ h0 hmono M) :=
  (Neck.mulHL (chiN (A.s0 jk.1)) (mult_chiN _ (2 + M))).comp
      ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _)) +
    ∑ i, ∑ a, ∑ d, ∑ l, (Neck.shH 0 (thetaN a)).comp
      (((F.Dd jk.1 i a).op (2 + M) (Neck.δ_nonneg δ h0 hmono M)
        (contDiff_cDN hG hT J₀ jk.1 i a (F.ρ i) (F.hρ i) (F.hρn i jk.1) d jk.2 l)
        (F.hsD hT hG J₀ jk.1 i a d jk.2 l) (Neck.δ_nonneg δ h0 hmono M)).comp
          ((ContinuousLinearMap.proj (i, d, l)).comp (ContinuousLinearMap.fst ℝ _ _)))

/-- The glued form on level `M`. -/
def glueNL : (fibreBlocks A δ h0 hmono) M →L[ℝ] (fibreBlocks A δ h0 hmono) M :=
  (ContinuousLinearMap.pi fun o => discOutNL hT hG F J₀ δ h0 hmono M o).prod
    (ContinuousLinearMap.pi fun jk => neckOutNL hT hG F J₀ δ h0 hmono M jk)

/-- **The operator `Φ` on level `M`**. -/
def phiNL : (fibreBlocks A δ h0 hmono) M →L[ℝ] (fibreBlocks A δ h0 hmono) M :=
  ((ContinuousLinearMap.fst ℝ _ _).comp ((1 / 2 : ℝ) • (glueNL hT hG F J₀ δ h0 hmono M +
      (fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _)
        (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) M).comp
          (glueNL hT hG F J₀ δ h0 hmono M)))).prod
    ((ContinuousLinearMap.snd ℝ _ _).comp (glueNL hT hG F J₀ δ h0 hmono M))

lemma valEqF_projFst (o : Ix A) :
    ValEqF M ((ContinuousLinearMap.proj o).comp (ContinuousLinearMap.fst ℝ _ _) :
      (fibreBlocks A δ h0 hmono) M →L[ℝ] H (2 + M) (Neck.δ_nonneg δ h0 hmono M))
      ((ContinuousLinearMap.proj o).comp (ContinuousLinearMap.fst ℝ _ _) :
        (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0)) :=
  fun v => (val_fibre_toBase M v o).symm

lemma valEqF_projSnd (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ValEqF M ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _) :
      (fibreBlocks A δ h0 hmono) M →L[ℝ] H (2 + M) (Neck.δ_nonneg δ h0 hmono M))
      ((ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _) :
        (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0)) :=
  fun v => (val_fibreNeck_toBase δ h0 hmono M v jk).symm

lemma valEqF_discOutNL (o : Ix A) :
    ValEqF M (discOutNL hT hG F J₀ δ h0 hmono M o) (discOutN hT hG F J₀ δ h0 hmono o) :=
  (ValEqF.sum _ fun _ => (valEq_op _ _ _).compF (valEqF_projFst δ h0 hmono M _)).add
    (ValEqF.sum _ fun _ => ValEqF.sum _ fun _ => ValEqF.sum _ fun _ =>
      (valEq_op _ _ _).compF ((valEq_shH _ _).compF (valEqF_projSnd δ h0 hmono M _)))

lemma valEqF_neckOutNL (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ValEqF M (neckOutNL hT hG F J₀ δ h0 hmono M jk) (neckOutN hT hG F J₀ δ h0 hmono jk) :=
  ((valEq_mulHL _ _).compF (valEqF_projSnd δ h0 hmono M jk)).add
    (ValEqF.sum _ fun _ => ValEqF.sum _ fun _ => ValEqF.sum _ fun _ => ValEqF.sum _ fun _ =>
      (valEq_shH _ _).compF ((valEq_op _ _ _).compF (valEqF_projFst δ h0 hmono M _)))

lemma toBase_glueNL (y : (fibreBlocks A δ h0 hmono) M) :
    (fibreBlocks A δ h0 hmono).toBase M (glueNL hT hG F J₀ δ h0 hmono M y) =
      glueN hT hG F J₀ δ h0 hmono ((fibreBlocks A δ h0 hmono).toBase M y) :=
  fibre_ext_val δ h0 hmono (fun o => by
      rw [val_fibre_toBase]; exact valEqF_discOutNL hT hG F J₀ δ h0 hmono M o y)
    (fun jk => by
      rw [val_fibreNeck_toBase]; exact valEqF_neckOutNL hT hG F J₀ δ h0 hmono M jk y)

/-- **`Φ` on level `M` agrees with `Φ` on level `0` along the inclusions.** -/
theorem toBase_phiNL (y : (fibreBlocks A δ h0 hmono) M) :
    (fibreBlocks A δ h0 hmono).toBase M (phiNL hT hG F J₀ δ h0 hmono M y) =
      phiN hT hG F J₀ δ h0 hmono ((fibreBlocks A δ h0 hmono).toBase M y) := by
  set g := glueNL hT hG F J₀ δ h0 hmono M y
  set Z : (fibreBlocks A δ h0 hmono) M := (1 / 2 : ℝ) • (g + fOp δ h0 hmono (fun _ _ => idCC)
    (aPI A J₀) (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _)
    (srcP A) M g)
  have hZ : (fibreBlocks A δ h0 hmono).toBase M Z = (1 / 2 : ℝ) •
      (glueN hT hG F J₀ δ h0 hmono ((fibreBlocks A δ h0 hmono).toBase M y) +
        projPN hT J₀ δ h0 hmono (glueN hT hG F J₀ δ h0 hmono
          ((fibreBlocks A δ h0 hmono).toBase M y))) := by
    have h1 := toBase_fOpN δ h0 hmono M (D := fun _ _ => idCC) (a := aPI A J₀)
      (fun _ _ => contDiff_aP hT J₀ _ _ _ _ _ _) (fun _ _ => tsupport_aP J₀ _ _ _ _ _ _) (srcP A) g
    rw [map_smul, map_add, h1, toBase_glueNL]
    rfl
  refine fibre_ext_val δ h0 hmono (fun o => ?_) (fun jk => ?_)
  · rw [val_fibre_toBase]
    have h := congrArg (fun w : (fibreBlocks A δ h0 hmono) 0 => H.val (w.1 o)) hZ
    rw [val_fibre_toBase] at h
    exact h
  · rw [val_fibreNeck_toBase]
    have h := congrArg (fun w : (fibreBlocks A δ h0 hmono) 0 => H.val (w.2 jk))
      (toBase_glueNL hT hG F J₀ δ h0 hmono M y)
    rw [val_fibreNeck_toBase] at h
    exact h

end Operator

/-! ## 3. Density on level `M` -/

section Dense

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **`Φ` maps a tuple of test functions to the representative of a smooth anti-linear form**
(the neck test forms, `neckTestForms_of_glueCharts`). -/
theorem phiN_testTuple_rep (hG : GlueCharts A) (F : FormGlueN A) {w : (fibreBlocks A δ h0 hmono) 0}
    (hw : w ∈ testTuplesN δ h0 hmono (A := A)) : ∃ η : Form E twoSpheres,
      IsAntiJ (J.J q) (fun z => η (Sum.inl z)) ∧ IsAntiJ (J.J q) (fun z => η (Sum.inr z)) ∧
      IsSphereSmooth (fun z => η (Sum.inl z)) ∧ IsSphereSmooth (fun z => η (Sum.inr z)) ∧
      IsFormRep η (phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono w) := by
  choose φ hφ hwφ using fun o => hw.1 o (mem_univ _)
  choose γ hγ hwγ using fun jk => hw.2 jk (mem_univ _)
  obtain ⟨ξN, h1, h2, h3, h4⟩ := neckTestForms_of_glueCharts J hG F φ hφ γ hγ
  have hg : IsGlueRep J w (testForm A φ) ξN :=
    ⟨fun i d k => ⟨φ (i, d, k), by rw [hwφ (i, d, k)]; exact MemLp.coeFn_toLp ((hφ _).memLp 2),
        fun p hp => (formDiscRep_testForm twoSpheres_chartsOnto (fun _ => rfl) A φ i d k hp).symm⟩,
      fun j k => ⟨γ (j, k), by rw [hwγ (j, k)]; exact MemLp.coeFn_toLp ((hγ _).memLp 2),
        h1 j k⟩, h2⟩
  have hrep : IsFormRep (projF (J.J q) (glueForm F (testForm A φ) ξN))
      (phiN twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono w) :=
    isFormRep_phiN twoSpheres_chartsOnto hG F J hg
  have ha1 : IsAntiJ (J.J q)
      fun z => projF (J.J q) (glueForm F (testForm A φ) ξN) (Sum.inl z) := by
    intro y v
    have := (NodalSurface.mem_antiLinearForms J twoSpheres).1
      (projF_mem J q (glueForm F (testForm A φ) ξN) (Sum.inl y)) v
    rw [twoSpheres_j_inl] at this
    exact this
  have ha2 : IsAntiJ (J.J q)
      fun z => projF (J.J q) (glueForm F (testForm A φ) ξN) (Sum.inr z) := by
    intro y v
    have := (NodalSurface.mem_antiLinearForms J twoSpheres).1
      (projF_mem J q (glueForm F (testForm A φ) ξN) (Sum.inr y)) v
    rw [twoSpheres_j_inr] at this
    exact this
  exact ⟨_, ha1, ha2, h3, h4, hrep⟩

variable (hsm : NeckSmooth A) (G : GlueDataN A)

include hsm in
/-- **The range of `D` is dense on level `M`**, with smooth sections: a form of class
`(2+M, δ_M)` in the fibre over a constant map from `twoSpheres` is a limit in `H^{2+M,δ_M}` of
`D w`, `w` a smooth point of the section space (`δ_m < 2π` for all `m`). -/
theorem denseNL (hA : IsStdNeck A) (hG : GlueCharts A) (hδ : ∀ m, δ m < 2 * Real.pi) (M : ℕ)
    (y : (fibreBlocks A δ h0 hmono) M)
    (hy : (fibreBlocks A δ h0 hmono).toBase M y ∈ fibreSpace J A δ h0 hmono) :
    y ∈ closure {z | ∃ w : (blocks A δ h0 hmono) M, w ∈ (blocks A δ h0 hmono).smoothLvl M ∧
      (blocks A δ h0 hmono).toBase M w ∈ sectionSpace A δ h0 hmono ∧
        linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) w = z} := by
  obtain ⟨F⟩ := nonempty_formGlueN hG twoSpheres_chartsOnto
  set ΦM := phiNL twoSpheres_chartsOnto hG F (J.J q) δ h0 hmono M
  have hyfix : ΦM y = y := (fibreBlocks A δ h0 hmono).toBase_injective M (by
    rw [toBase_phiNL]
    exact phiN_eq_self_fibre twoSpheres_chartsOnto hG F J (twoSpheres_polar_offNode hA hG) hy)
  let T : Set ((fibreBlocks A δ h0 hmono) M) :=
    (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) M |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + M) (Neck.δ_nonneg δ h0 hmono M) hφ}) ×ˢ
    (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) M |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + M) (Neck.δ_nonneg δ h0 hmono M) hφ})
  have hd : Dense T :=
    (dense_pi univ fun _ _ => dense_test (2 + M) (Neck.δ_nonneg δ h0 hmono M)).prod
      (dense_pi univ fun _ _ => dense_test (2 + M) (Neck.δ_nonneg δ h0 hmono M))
  have htest : ∀ w ∈ T, ΦM w ∈ {z | ∃ w : (blocks A δ h0 hmono) M,
      w ∈ (blocks A δ h0 hmono).smoothLvl M ∧
      (blocks A δ h0 hmono).toBase M w ∈ sectionSpace A δ h0 hmono ∧
        linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) w = z} := by
    rintro w ⟨hw1, hw2⟩
    have hw0 : (fibreBlocks A δ h0 hmono).toBase M w ∈ testTuplesN δ h0 hmono (A := A) := by
      refine ⟨fun o _ => ?_, fun jk _ => ?_⟩
      · obtain ⟨φ, hφ, e⟩ := hw1 o (mem_univ _)
        refine ⟨φ, hφ, valCLM_injective ?_⟩
        refine (val_fibre_toBase M w o).trans ?_
        rw [e]
        exact val_toH_eq (k := 2 + M) (hd := Neck.δ_nonneg δ h0 hmono M) hφ
      · obtain ⟨φ, hφ, e⟩ := hw2 jk (mem_univ _)
        refine ⟨φ, hφ, valCLM_injective ?_⟩
        refine (val_fibreNeck_toBase δ h0 hmono M w jk).trans ?_
        rw [e]
        exact val_toH_eq (k := 2 + M) (hd := Neck.δ_nonneg δ h0 hmono M) hφ
    obtain ⟨η, hη₁, hη₂, hs₁, hs₂, hrep⟩ := phiN_testTuple_rep J δ h0 hmono hG F hw0
    obtain ⟨ξ, hξ, hm, hsol⟩ := exists_twoSpheres_smooth_solution (acs_sq J q) hη₁ hη₂ hs₁ hs₂
    have hc : IsContSection (fun _ => q) ξ := isContSection_of_const (fun _ => rfl) hξ.continuous
    have hr := isRep_smoothBlocks2 δ h0 hmono hξ hA (hδ 0)
    have hD := isFormRep_linOpN twoSpheres_chartsOnto hsm G hc hr (J.J q)
    have he : projF (X := twoSpheres) (J.J q) (dForm (X := twoSpheres) ξ) = η := funext hsol
    rw [he] at hD
    have hlin := hD.unique hrep
    refine ⟨smoothBlocks2L δ h0 hmono hξ hA M (hδ M),
      smoothBlocks2L_mem_smoothLvl δ h0 hmono hξ hA hδ M, ?_, ?_⟩
    · rw [toBase_smoothBlocks2L δ h0 hmono hξ hA M (hδ M) (hδ 0)]
      exact smoothNeckRep_mem δ h0 hmono hξ hA (hδ 0) hm
    · apply (fibreBlocks A δ h0 hmono).toBase_injective M
      rw [toBase_linOpNL, toBase_smoothBlocks2L δ h0 hmono hξ hA M (hδ M) (hδ 0), hlin,
        toBase_phiNL]
  have hsub : ΦM '' T ⊆ {z | ∃ w : (blocks A δ h0 hmono) M,
      w ∈ (blocks A δ h0 hmono).smoothLvl M ∧
      (blocks A δ h0 hmono).toBase M w ∈ sectionSpace A δ h0 hmono ∧
        linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) w = z} := by
    rintro _ ⟨w, hw, rfl⟩
    exact htest w hw
  rw [← hyfix]
  exact closure_mono hsub (image_closure_subset_closure_image ΦM.continuous ⟨y, hd y, rfl⟩)

end Dense

end GWMemoir
