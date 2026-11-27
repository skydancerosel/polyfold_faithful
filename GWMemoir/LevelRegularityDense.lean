import GWMemoir.LinearModelFredholm

/-!
# The range of `D` is dense on every level, at a constant map from the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.  The argument of
`GWMemoir.CokernelSphereDense` on level `M` of the sc-structure.

* `smoothBlocksL`, `constBlocksL`: the blocks of a smooth section and of a constant section on
  level `M`; `toBase_smoothBlocksL`, `toBase_constBlocksL`: they lie over the level-`0` blocks.
* **`denseL`**: every form of class `(2+M, δ_M)` in the fibre is a limit, in `H^{2+M,δ_M}`, of
  `D w` with `w` of class `(3+M, δ_M)`.  The operator `Φ = ½ (G + P G)` of
  `smoothFormsDense_sphere3`, on level `M`, is the identity on the fibre and maps the tuples of
  test functions, a dense set on level `M`, to representatives of smooth anti-linear forms; these are `D w` for a
  smooth section `w` (`exists_sphere_solution`), whose blocks lie on every level.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section Blocks

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} (A : SectionAtlas (E := E) sphere3 (fun _ => q))
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-- The level-`M` blocks of a smooth section. -/
def smoothBlocksL {ξ : S2 → E} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) :
    (blocks A δ h0 hmono) M :=
  (fun ik => toHdisc (contDiff_secDisc A hξ ik.1 ik.2) (tsupport_secDisc A ik.1 ik.2) (3 + M)
      (Neck.δ_nonneg δ h0 hmono M),
    fun jk => (isEmpty_neck_of_nodes_empty rfl A).elim jk.1)

lemma toBase_smoothBlocksL {ξ : S2 → E} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) :
    (blocks A δ h0 hmono).toBase M (smoothBlocksL A δ h0 hmono M hξ) =
      smoothBlocks A δ h0 hmono hξ := by
  refine Prod.ext (funext fun ik => ?_)
    (funext fun jk => (isEmpty_neck_of_nodes_empty rfl A).elim jk.1)
  apply valCLM_injective (m := 3) (hδ := Neck.δ_nonneg δ h0 hmono 0)
  exact val_blocks_toBase M _ ik

/-- The level-`M` blocks of the constant section `e`. -/
def constBlocksL (e : E) : (blocks A δ h0 hmono) M :=
  (fun ik => toH (3 + M) (Neck.δ_nonneg δ h0 hmono M) (isTest_bumpPer (crd ik.2 e)),
    fun jk => (isEmpty_neck_of_nodes_empty rfl A).elim jk.1)

lemma toBase_constBlocksL (e : E) :
    (blocks A δ h0 hmono).toBase M (constBlocksL A δ h0 hmono M e) =
      constBlocks A δ h0 hmono e := by
  refine Prod.ext (funext fun ik => ?_)
    (funext fun jk => (isEmpty_neck_of_nodes_empty rfl A).elim jk.1)
  apply valCLM_injective (m := 3) (hδ := Neck.δ_nonneg δ h0 hmono 0)
  exact val_blocks_toBase M _ ik

end Blocks

section Dense

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-- **The range of `D` is dense on level `M`**: a form of class `(2+M, δ_M)` in the fibre over a
constant map from `sphere3` is a limit in `H^{2+M,δ_M}` of `D w`, `w` of class `(3+M, δ_M)`. -/
theorem denseL (y : (fibreBlocks A δ h0 hmono) M)
    (hy : (fibreBlocks A δ h0 hmono).toBase M y ∈ fibreSpace J A δ h0 hmono) :
    y ∈ closure {z | ∃ w : (blocks A δ h0 hmono) M,
      (blocks A δ h0 hmono).toBase M w ∈ sectionSpace A δ h0 hmono ∧
        linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) w = z} := by
  have hX : sphere3.nodes = ∅ := rfl
  have hT := sphere3_chartsOnto
  have hu : ∀ x : sphere3.S, (fun _ => q) x = q := fun _ => rfl
  obtain ⟨ρ, hρ⟩ := exists_partition hX hT A
  have hρ' : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j) := hρ
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (z := A.center i) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ' j)
  have hcG : ∀ o t, ContDiff ℝ ∞ (aG A (fun j => ρ j) o t) :=
    fun o t => contDiff_coef hT (ρ t.1) _ _ _ _ (hρ' t.1) _ _
  have hsG : ∀ o t, tsupport (aG A (fun j => ρ j) o t) ⊆ (D o.1 t.1).K :=
    fun o t => by
      rw [hDK o.1 t.1]
      exact tsupport_coef_sub hT _ _ _ _ _ _ _
  have hcP : ∀ o t, ContDiff ℝ ∞ (aPI A (J.J q) o t) := fun o t => contDiff_aP hT _ _ _ _ _ _ _
  have hsP : ∀ o t, tsupport (aPI A (J.J q) o t) ⊆ ((fun _ _ => idCC) o t : ChartChange).K :=
    fun o t => tsupport_aP _ _ _ _ _ _ _
  have hnn := isEmpty_neck_of_nodes_empty hX A
  set Gf := fOp δ h0 hmono (fun o t => D o.1 t.1) (aG A (fun j => ρ j)) hcG hsG (srcG A) with hG
  set P := fOp δ h0 hmono (fun _ _ => idCC) (aPI A (J.J q)) hcP hsP (srcP A) with hP
  set Φ : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
    (1 / 2 : ℝ) • (Gf 0 + (P 0).comp (Gf 0)) with hΦ
  set ΦM : (fibreBlocks A δ h0 hmono) M →L[ℝ] (fibreBlocks A δ h0 hmono) M :=
    (1 / 2 : ℝ) • (Gf M + (P M).comp (Gf M)) with hΦM
  have hΦtoBase : ∀ z, (fibreBlocks A δ h0 hmono).toBase M (ΦM z) =
      Φ ((fibreBlocks A δ h0 hmono).toBase M z) := by
    intro z
    simp only [hΦM, hΦ, smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_smul, map_add]
    rw [hP, hG, toBase_fOp _ _ hcP hsP _ hnn, toBase_fOp _ _ hcG hsG _ hnn]
  have hGrep : ∀ ξ v, IsFormRep ξ v → IsFormRep ξ (Gf 0 v) := by
    intro ξ v hv
    refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
    refine (G_ae hT hu hρ' hDK hDψ hcG hsG (fun _ => ξ)
      (fun o t => ChartChange.comp_congr (hsG o t) (hv.1 t.1 t.2 o.2.2)) (i, d, k)).trans
      (Eventually.of_forall fun x => ?_)
    change ∑ j, ρ j _ * _ = _
    rw [← Finset.sum_mul]
    have h := ρ.sum_eq_one (x := sphere3.discPt (A.center i) (A.ε i) x) (mem_univ _)
    rw [finsum_eq_sum_of_fintype] at h
    rw [h, one_mul]
  have hrep : ∀ ξ v, IsFormRep ξ (Gf 0 v) → IsFormRep (projF (J.J q) ξ) (Φ v) := fun ξ v hv =>
    (hv.add (P_rep hT hu hnn (J.J q) hcP hsP hv)).smul (1 / 2 : ℝ)
  have hfix : ∀ v ∈ formsSub J A δ h0 hmono, Φ v = v := by
    rintro v ⟨ξ, ha, hv⟩
    have hp : projF (J.J q) ξ = ξ := funext fun y => projF_of_mem (ha y (by rw [hX]; simp))
    have h := hrep ξ v (hGrep ξ v hv)
    rw [hp] at h
    exact h.unique hv
  have hfixF : ∀ v ∈ (fibreSpace J A δ h0 hmono : Set ((fibreBlocks A δ h0 hmono) 0)),
      Φ v = v := by
    intro v hv
    rw [fibreSpace, Submodule.topologicalClosure_coe] at hv
    exact (show EqOn Φ id (formsSub J A δ h0 hmono : Set _) from fun v hv => hfix v hv).closure
      Φ.continuous continuous_id hv
  have hyfix : ΦM y = y :=
    (fibreBlocks A δ h0 hmono).toBase_injective M (by rw [hΦtoBase, hfixF _ hy])
  -- the image of a tuple of test functions on level `M`
  let T : Set ((fibreBlocks A δ h0 hmono) M) :=
    (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) M |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + M) (Neck.δ_nonneg δ h0 hmono M) hφ}) ×ˢ univ
  have hd : Dense T :=
    (dense_pi univ fun _ _ => dense_test (2 + M) (Neck.δ_nonneg δ h0 hmono M)).prod dense_univ
  have htest : ∀ w ∈ T, ΦM w ∈ {z | ∃ w : (blocks A δ h0 hmono) M,
      (blocks A δ h0 hmono).toBase M w ∈ sectionSpace A δ h0 hmono ∧
        linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) w = z} := by
    rintro w ⟨hw, -⟩
    choose φ hφ hwφ using fun o => hw o (mem_univ o)
    set w0 := (fibreBlocks A δ h0 hmono).toBase M w with hw0def
    have hw0 : ∀ o, w0.1 o = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) (hφ o) := fun o =>
      valCLM_injective ((val_fibre_toBase M w o).trans (by rw [hwφ o]; rfl))
    have hG' : IsFormRep (fun y => ∑ j, ρ j y • testForm A φ j y) (Gf 0 w0) := by
      refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
      refine (G_ae hT hu hρ' hDK hDψ hcG hsG (fun j => testForm A φ j) (fun o t => ?_)
        (i, d, k)).trans (Eventually.of_forall fun x =>
          (formDiscRep_sum hu A (fun j => ρ j) _ i d k x).symm)
      refine (ChartChange.comp_congr (hsG o t) (f' := φ (srcG A o t)) (by
        rw [hw0 (srcG A o t)]; exact MemLp.coeFn_toLp ((hφ _).memLp 2))).trans
        (Eventually.of_forall fun x => ?_)
      change aG A (fun j => ρ j) o t x * φ (srcG A o t) ((D o.1 t.1).ψ x) =
        aG A (fun j => ρ j) o t x * formDiscRep A t.1 t.2 o.2.2 (testForm A φ t.1) ((D o.1 t.1).ψ x)
      by_cases hx : aG A (fun j => ρ j) o t x = 0
      · rw [hx, zero_mul, zero_mul]
      have hxK : x ∈ pieceK (ρ t.1) (A.center o.1) (A.ε o.1) :=
        tsupport_coef_sub hT _ _ _ _ _ _ _ (subset_tsupport _ hx)
      have hxD := pieceK_sub (hρ' t.1) hxK
      rw [hDψ o.1 t.1 x ((hDK o.1 t.1).symm ▸ hxK),
        formDiscRep_testForm hT hu A φ t.1 t.2 o.2.2 (discCut_pos (pieceDom_sub hxD).2).ne']
      rfl
    set η : Form E sphere3 := projF (J.J q) (fun y => ∑ j, ρ j y • testForm A φ j y) with hηdef
    have hηrep : IsFormRep η (Φ w0) := hrep _ w0 hG'
    have hηa : IsAntiJ (J.J q) η := (isAntiJ_iff J).2 fun y _ => projF_mem J q _ y
    have hηs := isSphereSmooth_testForms A (J.J q) (fun j => ρ j) (fun j => (ρ j).contMDiff) hρ'
      φ (fun o => (hφ o).smooth)
    obtain ⟨ξ, hξ, hξη⟩ := exists_sphere_solution (acs_sq J q) hηa hηs
    have hc : IsContSection (X := sphere3) (fun _ => q) ξ := fun x => by
      simp only [tangentCoordChange_self (mem_extChartAt_source q)]
      exact hξ.continuous.continuousAt
    have hr := isRep_smoothBlocks A δ h0 hmono hξ
    have h := isFormRep_linOp (X := sphere3) rfl sphere3_chartsOnto (fun _ => rfl) G hc hr (J.J q)
    have he : projF (X := sphere3) (J.J q) (dForm (X := sphere3) ξ) = η := funext hξη
    rw [he] at h
    have hlin := h.unique hηrep
    refine ⟨smoothBlocksL A δ h0 hmono M hξ, ?_, ?_⟩
    · rw [toBase_smoothBlocksL]; exact smoothBlocks_mem A δ h0 hmono hξ
    · apply (fibreBlocks A δ h0 hmono).toBase_injective M
      rw [toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn M (J.J q), toBase_smoothBlocksL, hlin,
        hΦtoBase]
  have hsub : ΦM '' T ⊆ {z | ∃ w : (blocks A δ h0 hmono) M,
      (blocks A δ h0 hmono).toBase M w ∈ sectionSpace A δ h0 hmono ∧
        linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) w = z} := by
    rintro _ ⟨w, hw, rfl⟩
    exact htest w hw
  rw [← hyfix]
  exact closure_mono hsub (image_closure_subset_closure_image ΦM.continuous ⟨y, hd y, rfl⟩)

end Dense

end GWMemoir
