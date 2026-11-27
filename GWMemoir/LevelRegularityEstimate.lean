import GWMemoir.LinearModelFredholm

/-!
# The elliptic estimate on every level, at a constant map from the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Propositions 4.7,
4.23): the estimate of `GWMemoir.EllipticEstimateSphere` on level `M` of the sc-structure,
`‖ξ‖_{H^{3+M,δ_M}} ≤ C (‖Dξ‖_{H^{2+M,δ_M}} + ‖ξ‖_{H^{2+M,0}})`.

* `crOpL_eq`: on the disc block `i`, read without weight in `H^{2+M,0}`, the identity
  `∂_s v_k + b ∑_l J_{kl} ∂_t v_l = 2 ε_i (D v)_{i,0,k} + Z_{i,0,k} + b ∑_l J_{kl} ((∂_t χ) v_l
  + χ Z_{i,1,l})`.  All terms are classes in `L²`, so it follows from the level-`0` identity
  `crOp_eq_phiOp` and the agreement of the operators on the levels (`toBase_linOpL`).
* `estimate_discL`: `‖v_{i,k}‖_{H^{3+M,0}} ≤ C (‖D v‖ + ‖v‖_{H^{2+M,0}})`, from `cyl_estimate`
  at order `2 + M`.
* **`ellipticEstimateL`**: with the weight transfer `v = χ v`, the estimate on level `M`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology InnerProductSpace NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section Level

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-! ## 1. The operators on level `M`, read without weight -/

/-- `H^{3+M,δ_M} → H^{(2+M)+1,0}`. -/
abbrev incT : H (3 + M) (Neck.δ_nonneg δ h0 hmono M) →L[ℝ] H (2 + M + 1) (le_refl (0 : ℝ)) :=
  inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono M) (by omega) (Neck.δ_nonneg δ h0 hmono M)

/-- `H^{3+M,δ_M} → H^{2+M,0}`. -/
abbrev incS : H (3 + M) (Neck.δ_nonneg δ h0 hmono M) →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono M) (by omega) (Neck.δ_nonneg δ h0 hmono M)

/-- `H^{2+M,δ_M} → H^{2+M,0}`. -/
abbrev incF : H (2 + M) (Neck.δ_nonneg δ h0 hmono M) →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono M) le_rfl (Neck.δ_nonneg δ h0 hmono M)

/-- Multiplication by `χ` on `H^{2+M,0}`. -/
abbrev chiOpL : H (2 + M) (le_refl (0 : ℝ)) →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  idCC.op (2 + M) (le_refl 0) contDiff_chiP tsupport_chiP (le_refl 0)

/-- Multiplication by `∂_t χ` on `H^{2+M,0}`. -/
abbrev dtChiOpL : H (2 + M) (le_refl (0 : ℝ)) →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  idCC.op (2 + M) (le_refl 0) contDiff_dtChiP tsupport_dtChiP (le_refl 0)

/-- The term `Z` on tuples in `H^{2+M,0}`. -/
def zKL (o : Ix A) : (Fin A.nd × Fin (Module.finrank ℝ E) → H (2 + M) (le_refl (0 : ℝ))) →L[ℝ]
    H (2 + M) (le_refl (0 : ℝ)) :=
  ∑ j, ((G.D o.1 j).op (2 + M) (le_refl 0) (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
    (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (le_refl 0)).comp
      (ContinuousLinearMap.proj (j, o.2.2))

/-- The level-`M` blocks read in `H^{2+M,0}`. -/
def kOpL : (blocks A δ h0 hmono) M →L[ℝ]
    (Fin A.nd × Fin (Module.finrank ℝ E) → H (2 + M) (le_refl (0 : ℝ))) :=
  ContinuousLinearMap.pi fun jk => (incS δ h0 hmono M).comp (secProjL δ h0 hmono M jk)

/-- The right side of `crOpL_eq` as a bounded operator of `(D v, v)`. -/
def phiOpL (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) M × (Fin A.nd × Fin (Module.finrank ℝ E) →
      H (2 + M) (le_refl (0 : ℝ))) →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  ((2 * A.ε i) • ((incF δ h0 hmono M).comp ((ContinuousLinearMap.proj (i, 0, k)).comp
      (ContinuousLinearMap.fst ℝ _ _)))).comp (ContinuousLinearMap.fst ℝ _ _) +
    (zKL G M (i, 0, k)).comp (ContinuousLinearMap.snd ℝ _ _) +
    ∑ l, (b * Jc (J.J q) k l) • (((dtChiOpL M).comp (ContinuousLinearMap.proj (i, l)) +
      (chiOpL M).comp (zKL G M (i, 1, l))).comp (ContinuousLinearMap.snd ℝ _ _))

/-! ## 2. The same operators on the `L²` classes -/

/-- `Z` on `L²` classes. -/
def zVal (o : Ix A) (W : Fin A.nd × Fin (Module.finrank ℝ E) → Lp ℝ 2 cyl) : Lp ℝ 2 cyl :=
  ∑ j, (G.D o.1 j).compMul (coefZ o.2.1 (G.ρ j) (A.center o.1) (A.ε o.1) (A.center j) (A.ε j))
    (W (j, o.2.2))

/-- The right side of `crOpL_eq` on `L²` classes. -/
def phiVal (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E)) (Y : Ix A → Lp ℝ 2 cyl)
    (W : Fin A.nd × Fin (Module.finrank ℝ E) → Lp ℝ 2 cyl) : Lp ℝ 2 cyl :=
  (2 * A.ε i) • Y (i, 0, k) + zVal G (i, 0, k) W + ∑ l, (b * Jc (J.J q) k l) •
    (idCC.compMul dtChiP (W (i, l)) + idCC.compMul chiP (zVal G (i, 1, l) W))

lemma val_zKL (o : Ix A) (w : Fin A.nd × Fin (Module.finrank ℝ E) → H (2 + M) (le_refl (0 : ℝ))) :
    valCLM (2 + M) (le_refl 0) (zKL G M o w) = zVal G o fun jk => H.val (w jk) := by
  rw [zKL, sum_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => ChartChange.val_op (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
    (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (le_refl 0) _

lemma val_zK (o : Ix A) (w : Fin A.nd × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) :
    valCLM 2 (le_refl 0) (zK G o w) = zVal G o fun jk => H.val (w jk) := by
  rw [zK, sum_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => ChartChange.val_op (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
    (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (le_refl 0) _

lemma val_phiOpL (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E))
    (y : (fibreBlocks A δ h0 hmono) M)
    (w : Fin A.nd × Fin (Module.finrank ℝ E) → H (2 + M) (le_refl (0 : ℝ))) :
    valCLM (2 + M) (le_refl 0) (phiOpL J G δ h0 hmono M i b k (y, w)) =
      phiVal J G i b k (fun o => H.val (y.1 o)) (fun jk => H.val (w jk)) := by
  simp only [phiOpL, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
    map_add, map_smul, map_sum, val_zKL]
  rw [phiVal]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun l _ => congrArg _ (congrArg₂ (· + ·)
    (ChartChange.val_op contDiff_dtChiP tsupport_dtChiP (le_refl 0) _)
    ((ChartChange.val_op contDiff_chiP tsupport_chiP (le_refl 0) _).trans
      (congrArg (idCC.compMul chiP) (val_zKL G M _ w)))))

lemma val_phiOp (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E))
    (y : (fibreBlocks A δ h0 hmono) 0)
    (w : Fin A.nd × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) :
    valCLM 2 (le_refl 0) (phiOp J G δ h0 hmono i b k (y, w)) =
      phiVal J G i b k (fun o => H.val (y.1 o)) (fun jk => H.val (w jk)) := by
  simp only [phiOp, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
    map_add, map_smul, map_sum, val_zK]
  rw [phiVal]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun l _ => congrArg _ (congrArg₂ (· + ·)
    (ChartChange.val_op contDiff_dtChiP tsupport_dtChiP (le_refl 0) _)
    ((ChartChange.val_op contDiff_chiP tsupport_chiP (le_refl 0) _).trans
      (congrArg (idCC.compMul chiP) (val_zK G _ w)))))

/-! ## 3. The identity in a disc chart on level `M` -/

variable {δ h0 hmono M} in
/-- **The operator in the disc chart `i` on level `M`, read in `H^{2+M,0}`**: for `v` in the
section space, `∂_s v_k + b ∑_l J_{kl} ∂_t v_l = 2 ε_i (D v)_{i,0,k} + Z_{i,0,k}
  + b ∑_l J_{kl} ((∂_t χ) v_l + χ Z_{i,1,l})`. -/
theorem crOpL_eq (v : (blocks A δ h0 hmono) M)
    (hv : (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono) {i : Fin A.nd} {b : ℝ}
    (hb : ∀ p, jMat (X := sphere3) (A.center i) (sphere3.discPt (A.center i) (A.ε i) p)
      (EuclideanSpace.single 0 1) = b • EuclideanSpace.single 1 1)
    (k : Fin (Module.finrank ℝ E)) :
    crOp (2 + M) (fun k l => b * Jc (J.J q) k l) (fun l => incT δ h0 hmono M (v.1 (i, l))) k =
      phiOpL J G δ h0 hmono M i b k
        (linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v, kOpL δ h0 hmono M v) := by
  set v0 := (blocks A δ h0 hmono).toBase M v with hv0
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  have hval : ∀ jk, H.val (v0.1 jk) = H.val (v.1 jk) := fun jk => val_blocks_toBase M v jk
  have h := congrArg (valCLM 2 (le_refl (0 : ℝ)))
    (crOp_eq_phiOp J G v0 (chiP_mul_of_mem hv) hb k)
  apply valCLM_injective (m := 2 + M) (hδ := le_refl (0 : ℝ))
  have hL : valCLM (2 + M) (le_refl 0) (crOp (2 + M) (fun k l => b * Jc (J.J q) k l)
      (fun l => incT δ h0 hmono M (v.1 (i, l))) k) = valCLM 2 (le_refl 0)
        (crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v0.1 (i, l))) k) := by
    simp only [crOp, map_add, map_sum, map_smul]
    exact congrArg₂ (· + ·) (val_dsH_eq _ _ (hval (i, k)).symm)
      (Finset.sum_congr rfl fun l _ => congrArg _ (val_dtH_eq _ _ (hval (i, l)).symm))
  rw [hL, h, val_phiOpL, val_phiOp]
  refine congrArg₂ (phiVal J G i b k) (funext fun o => ?_) (funext fun jk => hval jk)
  rw [← toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn M (J.J q) v]
  exact val_fibre_toBase M _ o

/-! ## 4. The estimate on level `M` -/

variable {δ h0 hmono} in
/-- **The estimate against `H^{2+M,0}`** on the disc block `i`:
`‖v_{i,k}‖_{H^{3+M,0}} ≤ C (‖D v‖ + ‖v‖_{H^{2+M,0}})`. -/
lemma estimate_discL (i : Fin A.nd) : ∃ C : ℝ, ∀ v : {v : (blocks A δ h0 hmono) M //
    (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono}, ∀ k,
      ‖incT δ h0 hmono M (v.1.1 (i, k))‖ ≤
        C * (‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v.1‖ +
          ‖kOpL δ h0 hmono M v.1‖) := by
  obtain ⟨b, hb2, hb⟩ := jMat_disc_const (A.center i) (A.ε i)
  obtain ⟨C0, hC0⟩ := cyl_estimate _ (isCxMat_Jc (J.sq q) hb2) (2 + M)
  set Mc := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) +
    ∑ l, ‖phiOpL J G δ h0 hmono M i b l‖
  refine ⟨max C0 0 * Mc, fun ⟨v, hv⟩ k => ?_⟩
  set N := ‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpL δ h0 hmono M v‖
  have hN : 0 ≤ N := by positivity
  have h1 : ∀ l, ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ ≤ N := fun l => by
    have e : ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ =
        ‖H.val (kOpL δ h0 hmono M v (i, l))‖ := rfl
    rw [e, ← norm_wdv_idx0]
    exact (norm_wdv_le _ _).trans ((norm_le_pi_norm (kOpL δ h0 hmono M v) (i, l)).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have h2 : ∀ l, ‖crOp (2 + M) (fun k l => b * Jc (J.J q) k l)
      (fun l => incT δ h0 hmono M (v.1 (i, l))) l‖ ≤
        ‖phiOpL J G δ h0 hmono M i b l‖ * N := fun l => by
    rw [crOpL_eq J G v hv hb l]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hS : ∑ l, ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ + ∑ l, ‖crOp (2 + M)
      (fun k l => b * Jc (J.J q) k l) (fun l => incT δ h0 hmono M (v.1 (i, l))) l‖ ≤ Mc * N := by
    have := add_le_add (Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h1 l)
      (Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h2 l)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul] at this
    linarith
  have hk := hC0 (fun l => incT δ h0 hmono M (v.1 (i, l))) k
  have hS0 : 0 ≤ ∑ l, ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ + ∑ l, ‖crOp (2 + M)
      (fun k l => b * Jc (J.J q) k l) (fun l => incT δ h0 hmono M (v.1 (i, l))) l‖ := by
    positivity
  calc ‖incT δ h0 hmono M (v.1 (i, k))‖ ≤ max C0 0 *
        (∑ l, ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ + ∑ l, ‖crOp (2 + M)
          (fun k l => b * Jc (J.J q) k l) (fun l => incT δ h0 hmono M (v.1 (i, l))) l‖) :=
        hk.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS0)
    _ ≤ max C0 0 * (Mc * N) := mul_le_mul_of_nonneg_left hS (le_max_right _ _)
    _ = max C0 0 * Mc * N := by ring

/-- **The elliptic estimate on level `M`** at a constant map from `sphere3`:
`‖ξ‖_{H^{3+M,δ_M}} ≤ C (‖Dξ‖_{H^{2+M,δ_M}} + ‖ξ‖_{H^{2+M,0}})` for the sections of class
`(3+M, δ_M)`. -/
theorem ellipticEstimateL : ∃ C : ℝ, ∀ v : (blocks A δ h0 hmono) M,
    (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono →
      ‖v‖ ≤ C * (‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v‖ +
        ‖kOpL δ h0 hmono M v‖) := by
  set hd := Neck.δ_nonneg δ h0 hmono M
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  obtain ⟨C1, hC1⟩ := exists_common_bound (ι := Fin A.nd)
    (f := fun i (x : {v : (blocks A δ h0 hmono) M // (blocks A δ h0 hmono).toBase M v ∈
      sectionSpace A δ h0 hmono} × Fin (Module.finrank ℝ E)) =>
        ‖incT δ h0 hmono M (x.1.1.1 (i, x.2))‖)
    (g := fun x => ‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) x.1.1‖ +
      ‖kOpL δ h0 hmono M x.1.1‖) (fun x => by positivity)
    (fun i => by
      obtain ⟨C, hC⟩ := estimate_discL J G M i
      exact ⟨C, fun x => hC x.1 x.2⟩)
  -- the weight transfer `v = χ v`, from `H^{3+M,0}` to `H^{3+M,δ_M}`
  set chiT : H (2 + M + 1) (le_refl (0 : ℝ)) →L[ℝ] H (3 + M) hd :=
    (inclH hd hd (by omega : 3 + M ≤ 2 + M + 1) le_rfl).comp
      (idCC.op (2 + M + 1) (le_refl 0) contDiff_chiP tsupport_chiP hd)
  have hχv : ∀ {v : (blocks A δ h0 hmono) M},
      (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono → ∀ jk,
        chiT (incT δ h0 hmono M (v.1 jk)) = v.1 jk := fun hv jk => by
    apply valCLM_injective (m := 3 + M) (hδ := hd)
    have h1 := chiP_mul_of_mem hv jk
    rw [val_blocks_toBase] at h1
    exact (ChartChange.val_op contDiff_chiP tsupport_chiP hd _).trans h1
  refine ⟨‖chiT‖ * max C1 0, fun v hv => ?_⟩
  have hN : 0 ≤ ‖chiT‖ * max C1 0 * (‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v‖ +
      ‖kOpL δ h0 hmono M v‖) := by positivity
  have hb : ∀ jk, ‖v.1 jk‖ ≤ ‖chiT‖ * max C1 0 *
      (‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpL δ h0 hmono M v‖) := by
    rintro ⟨i, k⟩
    have h1 := hC1 i (⟨v, hv⟩, k)
    have h1' : ‖incT δ h0 hmono M (v.1 (i, k))‖ ≤ max C1 0 *
        (‖linOpL sphere3_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpL δ h0 hmono M v‖) :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [← hχv hv (i, k)]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
  refine norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hN).2 hb, ?_⟩
  rw [show v.2 = 0 from funext fun jk => isEmptyElim jk.1, norm_zero]
  exact hN

/-- The level-`n` blocks read in `H^{2+(n+1),0}`. -/
def kLow (n : ℕ) : (blocks A δ h0 hmono) n →L[ℝ]
    (Fin A.nd × Fin (Module.finrank ℝ E) → H (2 + (n + 1)) (le_refl (0 : ℝ))) :=
  ContinuousLinearMap.pi fun jk => (inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono n)
    (by omega : 2 + (n + 1) ≤ 3 + n) (Neck.δ_nonneg δ h0 hmono n)).comp (secProjL δ h0 hmono n jk)

/-- The lower-order term on level `n + 1` only depends on the inclusion into level `n`. -/
lemma kOpL_succ (n : ℕ) (v : (blocks A δ h0 hmono) (n + 1)) :
    kOpL δ h0 hmono (n + 1) v = kLow δ h0 hmono n ((blocks A δ h0 hmono).incl n v) := by
  funext jk
  apply valCLM_injective (m := 2 + (n + 1)) (hδ := le_refl (0 : ℝ))
  change H.val (v.1 jk) = H.val (((blocks A δ h0 hmono).incl n v).1 jk)
  rw [← val_blocks_toBase (n + 1) v jk,
    ← val_blocks_toBase n ((blocks A δ h0 hmono).incl n v) jk]
  rfl

end Level

end GWMemoir
