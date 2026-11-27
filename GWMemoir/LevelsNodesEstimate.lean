import GWMemoir.LevelsNodesOp

/-!
# The elliptic estimate with nodes on every level

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Propositions 4.7,
4.23): at a constant map from two spheres joined at a node (`twoSpheres`), with
`0 < δ₀` and `δ_M < 2π`, the estimate of `GWMemoir.LinearCRNodesEstimate` on level `M`,
`‖ξ‖_{H^{3+M,δ_M}} ≤ C (‖Dξ‖_{H^{2+M,δ_M}} + ‖Kξ‖)`, with `K` the blocks read in `H^{2+M,0}` and
the neck constants.

* `kOpNL`, `zKNL`, `phiOpNL`, `psiNL`: the lower-order terms on level `M`.
* `crOpNL_eq`: on the disc blocks, the identity `crOp_eqN` read in `H^{2+M,0}`; it follows
  from the level-`0` identity, since all its terms are classes in `L²` (`toBase_linOpNL`).
* `neckRowNL_eq`: on the neck blocks, the identity `neckRowN_eq` on level `M`.
* `estimate_discNL` (`cyl_estimate` at order `2 + M`), `estimate_neckNL` (`neck_estimate` at
  order `2 + M`, weight `δ_M`, `0 < δ_M < 2π`), **`ellipticEstimateNL`**.
* `kOpNL_succ`: on level `n + 1` the lower-order term only depends on the inclusion into
  level `n`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The lower-order terms on level `M` -/

section Ops

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

variable (A) in
/-- The target of the lower-order term on level `M`: the disc blocks and the neck remainders
in `H^{2+M,0}`, the neck constants in `ℝ`. -/
abbrev KTgtL : Type :=
  (Fin A.nd × Fin (Module.finrank ℝ E) → H (2 + M) (le_refl (0 : ℝ))) ×
    ((Fin A.nn × Fin (Module.finrank ℝ E) → H (2 + M) (le_refl (0 : ℝ))) ×
      (Fin A.nn × Fin (Module.finrank ℝ E) → ℝ))

/-- The lower-order term on level `M`. -/
def kOpNL : (blocks A δ h0 hmono) M →L[ℝ] KTgtL A M :=
  (ContinuousLinearMap.pi fun ik => (incS δ h0 hmono M).comp (secProjL δ h0 hmono M ik)).prod
    ((ContinuousLinearMap.pi fun jk => (incS δ h0 hmono M).comp (neckWL δ h0 hmono M jk)).prod
      (ContinuousLinearMap.pi fun jk => neckCL δ h0 hmono M jk))

/-- The zeroth-order term `zBlockNL` read through `kOpNL`, in `H^{2+M,0}`. -/
def zKNL (o : Ix A) : KTgtL A M →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  ∑ i', ((G.D o.1 i').op (2 + M) (le_refl 0)
      (contDiff_coefZ twoSpheres_chartsOnto o.2.1 (G.ρ i') _ _ _ _ (G.hρ i'))
      (G.hsZ twoSpheres_chartsOnto o.2.1 o.1 i') (le_refl 0)).comp
        ((ContinuousLinearMap.proj (i', o.2.2)).comp (ContinuousLinearMap.fst ℝ _ _)) +
  ∑ j, ∑ a, ((G.Dn o.1 j a).op (2 + M) (le_refl 0) (G.cN_smooth o.2.1 o.1 j a)
      (G.cN_supp o.2.1 o.1 j a) (le_refl 0)).comp
        ((Neck.shH 0 (G.θ a)).comp ((ContinuousLinearMap.proj (j, o.2.2)).comp
          ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))) +
  ∑ j, ((ContinuousLinearMap.proj (j, o.2.2)).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))).smulRight
    (toHdisc (contDiff_cstD twoSpheres_chartsOnto G o.2.1 o.1 j) (tsupport_cstD G o.2.1 o.1 j)
      (2 + M) (le_refl 0))

lemma val_zKNL (o : Ix A) (v : (blocks A δ h0 hmono) M) :
    valCLM (2 + M) (le_refl 0) (zKNL G M o (kOpNL δ h0 hmono M v)) =
      valCLM (2 + M) (Neck.δ_nonneg δ h0 hmono M)
        (zBlockNL twoSpheres_chartsOnto G δ h0 hmono M o v) := by
  simp only [zKNL, zBlockNL, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_add, map_sum,
    map_smul]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i' _ => ?_
    rw [valCLM_op, valCLM_op]; rfl
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [valCLM_op, valCLM_op]; rfl

/-- `zKNL` on level `M` agrees with `zKN` on level `0`. -/
lemma val_zKNL_zKN (o : Ix A) (v : (blocks A δ h0 hmono) M) :
    valCLM (2 + M) (le_refl 0) (zKNL G M o (kOpNL δ h0 hmono M v)) =
      valCLM 2 (le_refl 0) (zKN G o (kOpN δ h0 hmono ((blocks A δ h0 hmono).toBase M v))) :=
  (val_zKNL G δ h0 hmono M o v).trans ((valEqB_zBlockNL twoSpheres_chartsOnto G δ h0 hmono M o
    v).trans (val_zKN G δ h0 hmono o _).symm)

/-- The term `β'(s - s₀)(v⁺ - c)` of the neck row on level `M`, read through `kOpNL`. -/
def psiNL (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    KTgtL A M →L[ℝ] H (2 + M) (Neck.δ_nonneg δ h0 hmono M) :=
  ∑ i, ∑ a, (Neck.shH 0 (G.θ a)).comp
      (((G.Dd jk.1 i a).op (2 + M) (le_refl 0) (G.cD_smooth jk.1 i a)
        (G.cD_supp jk.1 i a) (Neck.δ_nonneg δ h0 hmono M)).comp
          ((ContinuousLinearMap.proj (i, jk.2)).comp (ContinuousLinearMap.fst ℝ _ _))) +
    (mulHW (mulN (A.s0 jk.1) (G.χ jk.1)) (mult_mulN (G.χ_smooth jk.1) (G.χ_zero jk.1) (2 + M))
      (hasCompactSupport_mulN (G.χ_zero jk.1))).comp
        ((Neck.shH (A.s0 jk.1) 0).comp ((ContinuousLinearMap.proj jk).comp
          ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))) -
    ((ContinuousLinearMap.proj jk).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))).smulRight
      (toH (2 + M) (Neck.δ_nonneg δ h0 hmono M) (isTest_cstN (s₀ := A.s0 jk.1) (G.χ_smooth jk.1)))

lemma mulχ_congr {m m' : ℕ} {χ : ℝ → ℝ} (h : Mult m χ) (h' : Mult m' χ) (f : Lp ℝ 2 cyl) :
    mulχ χ h f = mulχ χ h' f :=
  Lp.ext ((coeFn_mulχ χ h f).trans (coeFn_mulχ χ h' f).symm)

lemma val_psiNL (jk : Fin A.nn × Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) M) :
    valCLM (2 + M) (Neck.δ_nonneg δ h0 hmono M) (psiNL G δ h0 hmono M jk (kOpNL δ h0 hmono M v)) =
      valCLM 2 (Neck.δ_nonneg δ h0 hmono 0)
        (psiBlk G δ h0 hmono jk ((blocks A δ h0 hmono).toBase M v)) := by
  simp only [psiNL, psiBlk, add_apply, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_sub, map_sum, map_smul]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    rw [valCLM_shH, valCLM_shH, valCLM_op, valCLM_op]
    congr 2
    exact (val_blocks_toBase M v _).symm
  · rw [val_mulHW]
    refine (mulχ_congr _ (mult_mulN (G.χ_smooth jk.1) (G.χ_zero jk.1) 2) _).trans ?_
    exact congrArg _ (congrArg (Neck.shLp _ _) (val_neck_toBase δ h0 hmono M v jk).symm)
  · exact congrArg₂ (· • ·) (neckCL_eq δ h0 hmono M jk v) (val_toH_eq _)

end Ops

/-! ## 2. The disc rows on level `M` -/

section Disc

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-- The right side of `crOpNL_eq` as a bounded operator of `(D v, kOpNL v)`. -/
def phiOpNL (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) M × KTgtL A M →L[ℝ] H (2 + M) (le_refl (0 : ℝ)) :=
  ((2 * A.ε i) • ((incF δ h0 hmono M).comp ((ContinuousLinearMap.proj (i, 0, k)).comp
      (ContinuousLinearMap.fst ℝ _ _)))).comp (ContinuousLinearMap.fst ℝ _ _) +
    (zKNL G M (i, 0, k)).comp (ContinuousLinearMap.snd ℝ _ _) +
    ∑ l, (b * Jc (J.J q) k l) • (((dtChiOpL M).comp ((ContinuousLinearMap.proj (i, l)).comp
      (ContinuousLinearMap.fst ℝ _ _)) + (chiOpL M).comp (zKNL G M (i, 1, l))).comp
        (ContinuousLinearMap.snd ℝ _ _))

variable {δ h0 hmono M} in
/-- **The operator in the disc chart `i` on level `M`, read in `H^{2+M,0}`** (the identity
`crOp_eqN` of level `0`, transported along the inclusions). -/
theorem crOpNL_eq (v : (blocks A δ h0 hmono) M)
    (hv : (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono) {i : Fin A.nd} {b : ℝ}
    (hb : ∀ p, jMat (X := twoSpheres) (A.center i) (twoSpheres.discPt (A.center i) (A.ε i) p)
      (EuclideanSpace.single 0 1) = b • EuclideanSpace.single 1 1)
    (k : Fin (Module.finrank ℝ E)) :
    crOp (2 + M) (fun k l => b * Jc (J.J q) k l) (fun l => incT δ h0 hmono M (v.1 (i, l))) k =
      phiOpNL J G δ h0 hmono M i b k
        (linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v, kOpNL δ h0 hmono M v) := by
  set v0 := (blocks A δ h0 hmono).toBase M v with hv0
  have hval : ∀ ik, H.val (v0.1 ik) = H.val (v.1 ik) := fun ik => val_blocks_toBase M v ik
  have h := congrArg (valCLM 2 (le_refl (0 : ℝ)))
    (crOp_eqN J G v0 (chiP_mul_of_memN hv) hb k)
  apply valCLM_injective (m := 2 + M) (hδ := le_refl (0 : ℝ))
  have hL : valCLM (2 + M) (le_refl 0) (crOp (2 + M) (fun k l => b * Jc (J.J q) k l)
      (fun l => incT δ h0 hmono M (v.1 (i, l))) k) = valCLM 2 (le_refl 0)
        (crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v0.1 (i, l))) k) := by
    simp only [crOp, map_add, map_sum, map_smul]
    exact congrArg₂ (· + ·) (val_dsH_eq _ _ (hval (i, k)).symm)
      (Finset.sum_congr rfl fun l _ => congrArg _ (val_dtH_eq _ _ (hval (i, l)).symm))
  rw [hL, h]
  have hD : valCLM (2 + M) (le_refl 0) (incF δ h0 hmono M
      ((linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v).1 (i, 0, k))) =
      valCLM 2 (le_refl 0) (inc22 δ h0 hmono
        ((linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v0).1 (i, 0, k))) := by
    have := val_fibre_toBase M (linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v) (i, 0, k)
    rw [toBase_linOpNL] at this
    exact this.symm
  have hz := fun o => val_zKNL_zKN G δ h0 hmono M o v
  have hdt : ∀ l, valCLM (2 + M) (le_refl 0) (dtChiOpL M ((kOpNL δ h0 hmono M v).1 (i, l))) =
      valCLM 2 (le_refl 0) (dtChiOp (inc2 δ h0 hmono (v0.1 (i, l)))) := fun l =>
    (ChartChange.val_op contDiff_dtChiP tsupport_dtChiP (le_refl 0) _).trans
      ((congrArg (idCC.compMul dtChiP) (hval (i, l)).symm).trans
        (ChartChange.val_op contDiff_dtChiP tsupport_dtChiP (le_refl 0)
          (inc2 δ h0 hmono (v0.1 (i, l)))).symm)
  have hch : ∀ l,
      valCLM (2 + M) (le_refl 0) (chiOpL M (zKNL G M (i, 1, l) (kOpNL δ h0 hmono M v))) =
      valCLM 2 (le_refl 0) (chiOp (zKN G (i, 1, l) (kOpN δ h0 hmono v0))) := fun l =>
    (ChartChange.val_op contDiff_chiP tsupport_chiP (le_refl 0) _).trans
      ((congrArg (idCC.compMul chiP) (hz _)).trans
        (ChartChange.val_op contDiff_chiP tsupport_chiP (le_refl 0) _).symm)
  simp only [phiOpNL, add_apply, ContinuousLinearMap.comp_apply, smul_apply, sum_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
    map_add, map_smul, map_sum]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg _ hD.symm) (hz _).symm)
    (Finset.sum_congr rfl fun l _ => congrArg _ (congrArg₂ (· + ·) (hdt l).symm (hch l).symm))

variable {δ h0 hmono} in
/-- **The estimate against `H^{2+M,0}`** on the disc block `i` on level `M`. -/
lemma estimate_discNL (i : Fin A.nd) : ∃ C : ℝ, ∀ v : {v : (blocks A δ h0 hmono) M //
    (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono}, ∀ k,
      ‖incT δ h0 hmono M (v.1.1 (i, k))‖ ≤
        C * (‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v.1‖ +
          ‖kOpNL δ h0 hmono M v.1‖) := by
  obtain ⟨b, hb2, hb⟩ := jMat_disc_const_two (A.center i) (A.ε i)
  obtain ⟨C0, hC0⟩ := cyl_estimate _ (isCxMat_Jc (J.sq q) hb2) (2 + M)
  set Mc := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) +
    ∑ l, ‖phiOpNL J G δ h0 hmono M i b l‖
  refine ⟨max C0 0 * Mc, fun ⟨v, hv⟩ k => ?_⟩
  set N := ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpNL δ h0 hmono M v‖
  have hN : 0 ≤ N := by positivity
  have h1 : ∀ l, ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ ≤ N := fun l => by
    have e : ‖H.val (incT δ h0 hmono M (v.1 (i, l)))‖ =
        ‖H.val ((kOpNL δ h0 hmono M v).1 (i, l))‖ := rfl
    rw [e, ← norm_wdv_idx0]
    exact (norm_wdv_le _ _).trans ((norm_le_pi_norm (kOpNL δ h0 hmono M v).1 (i, l)).trans
      ((norm_fst_le _).trans (le_add_of_nonneg_left (norm_nonneg _))))
  have h2 : ∀ l, ‖crOp (2 + M) (fun k l => b * Jc (J.J q) k l)
      (fun l => incT δ h0 hmono M (v.1 (i, l))) l‖ ≤
        ‖phiOpNL J G δ h0 hmono M i b l‖ * N := fun l => by
    rw [crOpNL_eq J G v hv hb l]
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

end Disc

/-! ## 3. The neck rows on level `M` -/

section Neck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-- `H^{3+M,δ_M} → H^{(2+M)+1,δ_M}` (the same space). -/
abbrev castW :
    H (3 + M) (Neck.δ_nonneg δ h0 hmono M) →L[ℝ] H (2 + M + 1) (Neck.δ_nonneg δ h0 hmono M) :=
  inclH _ _ (by omega) le_rfl

/-- `H^{(2+M)+1,δ_M} → H^{3+M,δ_M}`. -/
abbrev castW' :
    H (2 + M + 1) (Neck.δ_nonneg δ h0 hmono M) →L[ℝ] H (3 + M) (Neck.δ_nonneg δ h0 hmono M) :=
  inclH _ _ (by omega) le_rfl

lemma castW'_castW (w : H (3 + M) (Neck.δ_nonneg δ h0 hmono M)) :
    castW' δ h0 hmono M (castW δ h0 hmono M w) = w :=
  valCLM_injective (by rw [valCLM_inclH, valCLM_inclH])

/-- **The neck row of `D` on level `M`**: the shifted `(∂_s + J₀ ∂_t) v_j` is twice the neck row
plus `β'(s - s₀)(v⁺ - c)`. -/
theorem neckRowNL_eq (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E))
    (v : (blocks A δ h0 hmono) M) :
    Neck.shH (A.s0 jk.1) 0 (crOpW (2 + M) (Neck.δ_nonneg δ h0 hmono M) (Jc J₀)
      (fun l => castW δ h0 hmono M (neckWL δ h0 hmono M (jk.1, l) v)) jk.2) =
      (2 : ℝ) • neckRowNL G δ h0 hmono M J₀ jk v +
        psiNL G δ h0 hmono M jk (kOpNL δ h0 hmono M v) := by
  set v0 := (blocks A δ h0 hmono).toBase M v
  apply valCLM_injective (m := 2 + M) (hδ := Neck.δ_nonneg δ h0 hmono M)
  have hg : ∀ l, valCLM (2 + M + 1) (Neck.δ_nonneg δ h0 hmono M)
      (castW δ h0 hmono M (neckWL δ h0 hmono M (jk.1, l) v)) =
        valCLM 3 (Neck.δ_nonneg δ h0 hmono 0) (neckW δ h0 hmono (jk.1, l) v0) := fun l => by
    rw [valCLM_inclH]
    exact (valEqB_neckWL δ h0 hmono M _ v)
  have hL : valCLM (2 + M) (Neck.δ_nonneg δ h0 hmono M) (Neck.shH (A.s0 jk.1) 0
      (crOpW (2 + M) (Neck.δ_nonneg δ h0 hmono M) (Jc J₀)
        (fun l => castW δ h0 hmono M (neckWL δ h0 hmono M (jk.1, l) v)) jk.2)) =
      valCLM 2 (Neck.δ_nonneg δ h0 hmono 0) (Neck.shH (A.s0 jk.1) 0
        (crOpW 2 (Neck.δ_nonneg δ h0 hmono 0) (Jc J₀)
          (fun l => neckW δ h0 hmono (jk.1, l) v0) jk.2)) := by
    refine valEq_shH _ _ _ _ ?_
    simp only [crOpW, map_add, map_sum, map_smul]
    exact congrArg₂ (· + ·) (val_dsH_eq _ _ (hg jk.2))
      (Finset.sum_congr rfl fun l _ => congrArg _ (val_dtH_eq _ _ (hg l)))
  rw [hL, neckRowN_eq G δ h0 hmono J₀ jk v0, map_add, map_add, map_smul, map_smul,
    valEqB_neckRowNL G δ h0 hmono M J₀ jk v, val_psiNL]

/-- **The estimate on the neck blocks on level `M`** (`neck_estimate`, `0 < δ_M < 2π`). -/
theorem estimate_neckNL (J : AlmostComplexStructure E Q) (hδ : 0 < δ M)
    (hδ' : δ M < 2 * Real.pi) : ∃ C : ℝ,
    ∀ jk (v : (blocks A δ h0 hmono) M), ‖neckWL δ h0 hmono M jk v‖ ≤
      C * (‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpNL δ h0 hmono M v‖) := by
  set hd := Neck.δ_nonneg δ h0 hmono M
  have hJ : IsCxMat (Jc (J.J q)) := by
    have := isCxMat_Jc (J.sq q) (b := 1) (by norm_num)
    simpa only [one_mul] using this
  obtain ⟨CN, hCN⟩ := neck_estimate (hδ := hd) hJ hδ hδ' (2 + M)
  refine exists_common_bound (ι := Fin A.nn × Fin (Module.finrank ℝ E))
    (f := fun jk v => ‖neckWL δ h0 hmono M jk v‖)
    (g := fun v => ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ +
      ‖kOpNL δ h0 hmono M v‖)
    (fun v => by positivity) fun jk => ?_
  obtain ⟨j, k⟩ := jk
  set Sh : H (2 + M) hd →L[ℝ] H (2 + M) hd := Neck.shH (-(A.s0 j)) (-0)
  set K := ‖castW' δ h0 hmono M‖
  refine ⟨K * (max CN 0 * ∑ l, ‖Sh‖ * (2 + ‖psiNL G δ h0 hmono M (j, l)‖)), fun v => ?_⟩
  set N := ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpNL δ h0 hmono M v‖
  have hN : 0 ≤ N := by positivity
  set g : Fin (Module.finrank ℝ E) → H (2 + M + 1) hd :=
    fun l => castW δ h0 hmono M (neckWL δ h0 hmono M (j, l) v)
  have hl : ∀ l, ‖crOpW (2 + M) hd (Jc (J.J q)) g l‖ ≤
      ‖Sh‖ * (2 + ‖psiNL G δ h0 hmono M (j, l)‖) * N := by
    intro l
    have e : crOpW (2 + M) hd (Jc (J.J q)) g l = Sh ((2 : ℝ) •
        neckRowNL G δ h0 hmono M (J.J q) (j, l) v +
        psiNL G δ h0 hmono M (j, l) (kOpNL δ h0 hmono M v)) := by
      rw [← neckRowNL_eq G δ h0 hmono M (J.J q) (j, l) v]
      exact (Neck.shH_shH _ _ _).symm
    have hrow : ‖neckRowNL G δ h0 hmono M (J.J q) (j, l) v‖ ≤
        ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ := by
      have e2 : neckRowNL G δ h0 hmono M (J.J q) (j, l) v =
          (linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v).2 (j, l) := rfl
      rw [e2]
      exact (norm_le_pi_norm _ (j, l)).trans (norm_snd_le _)
    have hpsi := (psiNL G δ h0 hmono M (j, l)).le_opNorm (kOpNL δ h0 hmono M v)
    rw [e]
    refine (Sh.le_opNorm _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hk : ‖kOpNL δ h0 hmono M v‖ ≤ N := le_add_of_nonneg_left (norm_nonneg _)
    have hD : ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ ≤ N :=
      le_add_of_nonneg_right (norm_nonneg _)
    nlinarith [norm_nonneg (psiNL G δ h0 hmono M (j, l)), norm_nonneg (kOpNL δ h0 hmono M v)]
  have hS : ∑ l, ‖crOpW (2 + M) hd (Jc (J.J q)) g l‖ ≤
      (∑ l, ‖Sh‖ * (2 + ‖psiNL G δ h0 hmono M (j, l)‖)) * N := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun l _ => hl l
  have hS0 : 0 ≤ ∑ l, ‖crOpW (2 + M) hd (Jc (J.J q)) g l‖ := by positivity
  have hgk : ‖g k‖ ≤ max CN 0 * ((∑ l, ‖Sh‖ * (2 + ‖psiNL G δ h0 hmono M (j, l)‖)) * N) :=
    calc ‖g k‖ ≤ CN * ∑ l, ‖crOpW (2 + M) hd (Jc (J.J q)) g l‖ := hCN g k
      _ ≤ max CN 0 * ∑ l, ‖crOpW (2 + M) hd (Jc (J.J q)) g l‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (le_max_right _ _)
  calc ‖neckWL δ h0 hmono M (j, k) v‖ = ‖castW' δ h0 hmono M (g k)‖ := by
        rw [castW'_castW]
    _ ≤ K * ‖g k‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * (max CN 0 * ((∑ l, ‖Sh‖ * (2 + ‖psiNL G δ h0 hmono M (j, l)‖)) * N)) :=
        mul_le_mul_of_nonneg_left hgk (norm_nonneg _)
    _ = _ := by ring

end Neck

/-! ## 4. The estimate on level `M` -/

section Main

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (M : ℕ)

/-- **The elliptic estimate on level `M`** at a constant map from `twoSpheres`, for
`0 < δ_M < 2π`: `‖ξ‖_{H^{3+M,δ_M}} ≤ C (‖Dξ‖_{H^{2+M,δ_M}} + ‖Kξ‖)` for the sections of class
`(3+M, δ_M)`. -/
theorem ellipticEstimateNL (hδ : 0 < δ M) (hδ' : δ M < 2 * Real.pi) :
    ∃ C : ℝ, ∀ v : (blocks A δ h0 hmono) M,
      (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono →
        ‖v‖ ≤ C * (‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ +
          ‖kOpNL δ h0 hmono M v‖) := by
  set hd := Neck.δ_nonneg δ h0 hmono M
  obtain ⟨C1, hC1⟩ := exists_common_bound (ι := Fin A.nd)
    (f := fun i (x : {v : (blocks A δ h0 hmono) M // (blocks A δ h0 hmono).toBase M v ∈
      sectionSpace A δ h0 hmono} × Fin (Module.finrank ℝ E)) =>
        ‖incT δ h0 hmono M (x.1.1.1 (i, x.2))‖)
    (g := fun x => ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) x.1.1‖ +
      ‖kOpNL δ h0 hmono M x.1.1‖) (fun x => by positivity)
    (fun i => by
      obtain ⟨C, hC⟩ := estimate_discNL J G M (δ := δ) (h0 := h0) (hmono := hmono) i
      exact ⟨C, fun x => hC x.1 x.2⟩)
  obtain ⟨C2, hC2⟩ := estimate_neckNL G δ h0 hmono M J hδ hδ'
  set chiT : H (2 + M + 1) (le_refl (0 : ℝ)) →L[ℝ] H (3 + M) hd :=
    (inclH hd hd (by omega : 3 + M ≤ 2 + M + 1) le_rfl).comp
      (idCC.op (2 + M + 1) (le_refl 0) contDiff_chiP tsupport_chiP hd)
  have hχv : ∀ {v : (blocks A δ h0 hmono) M},
      (blocks A δ h0 hmono).toBase M v ∈ sectionSpace A δ h0 hmono → ∀ jk,
        chiT (incT δ h0 hmono M (v.1 jk)) = v.1 jk := fun hv jk => by
    apply valCLM_injective (m := 3 + M) (hδ := hd)
    have h1 := chiP_mul_of_memN hv jk
    rw [val_blocks_toBase] at h1
    exact (ChartChange.val_op contDiff_chiP tsupport_chiP hd _).trans h1
  set C := ‖chiT‖ * max C1 0 + max C2 0 + 1
  refine ⟨C, fun v hv => ?_⟩
  set N := ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono M (J.J q) v‖ + ‖kOpNL δ h0 hmono M v‖
  have hN : 0 ≤ N := by positivity
  have hCN : ∀ {a : ℝ}, a ≤ C → a * N ≤ C * N := fun h => mul_le_mul_of_nonneg_right h hN
  have h0' : 0 ≤ ‖chiT‖ * max C1 0 := mul_nonneg (norm_nonneg _) (le_max_right _ _)
  have hc1 : ‖chiT‖ * max C1 0 ≤ C := by have := le_max_right C2 0; linarith
  have hc2 : max C2 0 ≤ C := by linarith
  have hc3 : (1 : ℝ) ≤ C := by linarith [le_max_right C2 0]
  have hdisc : ∀ jk, ‖v.1 jk‖ ≤ C * N := by
    rintro ⟨i, k⟩
    have h1 := hC1 i (⟨v, hv⟩, k)
    have h1' : ‖incT δ h0 hmono M (v.1 (i, k))‖ ≤ max C1 0 * N :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hN)
    rw [← hχv hv (i, k)]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖chiT‖ * ‖incT δ h0 hmono M (v.1 (i, k))‖ ≤ ‖chiT‖ * (max C1 0 * N) :=
          mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
      _ = (‖chiT‖ * max C1 0) * N := by ring
      _ ≤ C * N := hCN hc1
  have hneck : ∀ jk, ‖v.2 jk‖ ≤ C * N := by
    intro jk
    have hc : ‖(v.2 jk).1‖ ≤ C * N := by
      have e : (v.2 jk).1 = (kOpNL δ h0 hmono M v).2.2 jk := rfl
      have : ‖(v.2 jk).1‖ ≤ N := by
        rw [e]
        exact (norm_le_pi_norm _ jk).trans ((norm_snd_le _).trans ((norm_snd_le _).trans
          (le_add_of_nonneg_left (norm_nonneg _))))
      calc ‖(v.2 jk).1‖ ≤ 1 * N := by rw [one_mul]; exact this
        _ ≤ C * N := hCN hc3
    have hr : ‖(v.2 jk).2‖ ≤ C * N := by
      have e : (v.2 jk).2 = neckWL δ h0 hmono M jk v := rfl
      rw [e]
      calc ‖neckWL δ h0 hmono M jk v‖ ≤ C2 * N := hC2 jk v
        _ ≤ max C2 0 * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN
        _ ≤ C * N := hCN hc2
    exact norm_prod_le_iff.2 ⟨hc, hr⟩
  have hCN0 : 0 ≤ C * N := mul_nonneg (by linarith) hN
  exact norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hCN0).2 hdisc,
    (pi_norm_le_iff_of_nonneg hCN0).2 hneck⟩

/-- The level-`n` blocks read in `H^{2+(n+1),0}`, with the neck constants. -/
def kLowN (n : ℕ) : (blocks A δ h0 hmono) n →L[ℝ] KTgtL A (n + 1) :=
  (ContinuousLinearMap.pi fun ik => (inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono n)
    (by omega : 2 + (n + 1) ≤ 3 + n) (Neck.δ_nonneg δ h0 hmono n)).comp
      (secProjL δ h0 hmono n ik)).prod
    ((ContinuousLinearMap.pi fun jk => (inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono n)
      (by omega : 2 + (n + 1) ≤ 3 + n) (Neck.δ_nonneg δ h0 hmono n)).comp
        (neckWL δ h0 hmono n jk)).prod
      (ContinuousLinearMap.pi fun jk => neckCL δ h0 hmono n jk))

/-- The lower-order term on level `n + 1` only depends on the inclusion into level `n`. -/
lemma kOpNL_succ (n : ℕ) (v : (blocks A δ h0 hmono) (n + 1)) :
    kOpNL δ h0 hmono (n + 1) v = kLowN δ h0 hmono n ((blocks A δ h0 hmono).incl n v) := by
  refine Prod.ext (funext fun ik => ?_) (Prod.ext (funext fun jk => ?_) (funext fun jk => ?_))
  · apply valCLM_injective (m := 2 + (n + 1)) (hδ := le_refl (0 : ℝ))
    change H.val (v.1 ik) = H.val (((blocks A δ h0 hmono).incl n v).1 ik)
    rw [← val_blocks_toBase (n + 1) v ik,
      ← val_blocks_toBase n ((blocks A δ h0 hmono).incl n v) ik]
    rfl
  · apply valCLM_injective (m := 2 + (n + 1)) (hδ := le_refl (0 : ℝ))
    change H.val (v.2 jk).2 = H.val (((blocks A δ h0 hmono).incl n v).2 jk).2
    rw [← val_neck_toBase δ h0 hmono (n + 1) v jk,
      ← val_neck_toBase δ h0 hmono n ((blocks A δ h0 hmono).incl n v) jk]
    rfl
  · change (v.2 jk).1 = (((blocks A δ h0 hmono).incl n v).2 jk).1
    rw [← const_neck_toBase δ h0 hmono (n + 1) v jk,
      ← const_neck_toBase δ h0 hmono n ((blocks A δ h0 hmono).incl n v) jk]
    rfl

end Main

end GWMemoir
