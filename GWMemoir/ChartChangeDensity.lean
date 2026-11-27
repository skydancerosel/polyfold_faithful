import GWMemoir.ChartChangeInstances

/-!
# Density of the smooth sections for the constant maps from `sphere3`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4 (p. 66): the space
`H^{3,δ₀}_c(S, u*TQ)` of sections is an sc-subspace of the block space.

* `secOp`: for a smooth partition of unity `ρ_j` subordinate to the discs of the atlas, the
  operator `(Φv)_{i,k} = ∑_j a_{ij} · (v_{j,k} ∘ trans_{ij})`, `a_{ij} = discCut · (ρ_j ∘ discPt_i)
  / (discCut ∘ trans_{ij})`, at every level (`ChartChange.op`).
* `secOp_fix`: `Φ` is the identity on the representatives of sections.
* `secOp_mem`: `Φ` maps a tuple of test functions to the representatives of a continuous
  section, `y ↦ ∑_j ρ_j(y) / discCut(p_j y) · φ_j(p_j y)`.
* **`sectionsDense_const`**: on a surface without nodes whose charts are onto `ℝ²`, for a
  constant map and any atlas, `SectionsDense`.
* `sphere3_sectionsDense`: the instance on the constant maps from `sphere3`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The coefficients -/

section Coef

variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X)

/-- The coefficient `discCut · (ρ ∘ discPt) / (discCut ∘ dtrans)`. -/
def coefS (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (p : ℝ × ℝ) : ℝ :=
  discCut p * ρ (X.discPt z ε p) / discCut (dtrans z ε z' ε' p)

lemma piece_zero {ρ : X.S → ℝ} {z : X.S} {ε : ℝ} {p : ℝ × ℝ} (hp : p ∉ pieceK ρ z ε) :
    discCut p * ρ (X.discPt z ε p) = 0 := by
  by_cases hc : p ∈ closedDisc
  · rw [image_eq_zero_of_notMem_tsupport fun h => hp ⟨hc, h⟩, mul_zero]
  · rw [discCut_eq_zero hc, zero_mul]

include hT in
lemma tsupport_coefS_sub (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) :
    tsupport (coefS ρ z ε z' ε') ⊆ pieceK ρ z ε :=
  closure_minimal (fun p hp => by_contra fun h => hp (by rw [coefS, piece_zero h, zero_div]))
    (isCompact_pieceK hT ρ z ε).isClosed

include hT in
lemma contDiff_coefS (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯) (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ)
    (hρ : tsupport ρ ⊆ discSet z' ε') : ContDiff ℝ ∞ (coefS ρ z ε z' ε') := by
  set V := pieceDom z ε z' ε'
  have hVo : IsOpen V := isOpen_pieceDom hT z ε z' ε'
  have hW : IsOpen (X.discPt z ε ⁻¹' tsupport ρ)ᶜ :=
    ((isClosed_tsupport ρ).preimage (continuous_discPt hT z ε)).isOpen_compl
  refine contDiff_of_open_cover hVo hW (fun p => ?_) ?_ ?_
  · by_cases h : X.discPt z ε p ∈ tsupport ρ
    · exact Or.inl (hρ h)
    · exact Or.inr h
  · have hdt : ContDiffOn ℝ ∞ (dtrans z ε z' ε') V :=
      (contDiffOn_trans hT z ε z' ε').mono fun p hp => (pieceDom_sub hp).1
    have hcut : ContDiffOn ℝ ∞ (fun p => discCut (dtrans z ε z' ε' p)) V :=
      contDiff_discCut.comp_contDiffOn hdt
    have hne : ∀ p ∈ V, discCut (dtrans z ε z' ε' p) ≠ 0 := fun p hp =>
      (discCut_pos (pieceDom_sub hp).2).ne'
    exact (contDiff_discCut.contDiffOn.mul (contDiff_comp_discPt hT ρ z ε).contDiffOn).div
      hcut hne
  · intro p hp
    simp [coefS, image_eq_zero_of_notMem_tsupport hp]

end Coef

/-! ## 2. Sections from test functions -/

section Sections

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X)
  {q : Q} {u : X.S → Q} (hu : ∀ x, u x = q)

/-- The strip coordinate of `y` in the disc chart `(z, ε)`. -/
def stripPt (z : X.S) (ε : ℝ) (y : X.S) : ℝ × ℝ := placeInv z ε (extChartAt 𝓘(ℝ, E2) z y)

lemma dtrans_eq_stripPt (z : X.S) (ε : ℝ) (z' : X.S) (ε' : ℝ) (p : ℝ × ℝ) :
    dtrans z ε z' ε' p = stripPt z' ε' (X.discPt z ε p) := rfl

/-- One term of the section built from a test function `φ` in the chart `(z, ε)`. -/
def secTerm (ρ : X.S → ℝ) (z : X.S) (ε : ℝ) (φ : ℝ × ℝ → ℝ) (y : X.S) : ℝ :=
  ρ y / discCut (stripPt z ε y) * φ (stripPt z ε y)

lemma continuous_secTerm {ρ : X.S → ℝ} (hρc : Continuous ρ) {z : X.S} {ε : ℝ}
    (hρ : tsupport ρ ⊆ discSet z ε) {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) :
    Continuous (secTerm ρ z ε φ) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y ∈ discSet z ε
  · have hp : ContinuousOn (stripPt z ε) (discSet z ε) :=
      ((continuous_placeInv z ε).comp_continuousOn (continuousOn_extChartAt z)).mono
        fun _ h => h.1
    have hne : ∀ y ∈ discSet z ε, discCut (stripPt z ε y) ≠ 0 := fun y h => (discCut_pos h.2).ne'
    refine (ContinuousOn.continuousAt ?_ ((isOpen_discSet z ε).mem_nhds hy))
    exact (hρc.continuousOn.div (continuous_discCut.comp_continuousOn hp) hne).mul
      (hφ.comp_continuousOn hp)
  · have h0 : ρ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hρ h)
    refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [h0] with y' hy'
    simp [secTerm, hy']

variable (A : SectionAtlas (E := E) X u)

/-- The section `y ↦ ∑_j ρ_j(y) / discCut(p_j y) · φ_{j,k}(p_j y)` (coordinates in the basis). -/
def secOf (ρ : Fin A.nd → X.S → ℝ) (φ : Fin A.nd × Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ) :
    Section E X := fun y =>
  (Module.finBasis ℝ E).equivFun.symm fun kk =>
    ∑ j, secTerm (ρ j) (A.center j) (A.ε j) (φ (j, kk)) y

lemma crd_secOf (ρ : Fin A.nd → X.S → ℝ) (φ : Fin A.nd × Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ)
    (kk : Fin (Module.finrank ℝ E)) (y : X.S) :
    crd kk (secOf A ρ φ y) = ∑ j, secTerm (ρ j) (A.center j) (A.ε j) (φ (j, kk)) y := by
  rw [secOf, crd, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]

lemma continuous_secOf {ρ : Fin A.nd → X.S → ℝ} (hρc : ∀ j, Continuous (ρ j))
    (hρ : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j))
    {φ : Fin A.nd × Fin (Module.finrank ℝ E) → ℝ × ℝ → ℝ} (hφ : ∀ jk, Continuous (φ jk)) :
    Continuous (secOf A ρ φ) :=
  ((Module.finBasis ℝ E).equivFun.symm.toLinearMap.continuous_of_finiteDimensional).comp
    (continuous_pi fun kk => continuous_finsetSum _ fun j _ =>
      continuous_secTerm (hρc j) (hρ j) (hφ (j, kk)))

include hu in
lemma isContSection_of_const {η : Section E X} (hη : Continuous η) : IsContSection u η := by
  intro x
  have e : (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u x) (u y) (η y)) = η := by
    funext y
    simp only [hu]
    exact tangentCoordChange_self (mem_extChartAt_source q)
  rw [e]; exact hη.continuousAt

include hu in
lemma discRep_const (i : Fin A.nd) (kk : Fin (Module.finrank ℝ E)) (η : Section E X)
    (p : ℝ × ℝ) :
    discRep A i kk η p = discCut p * crd kk (η (X.discPt (A.center i) (A.ε i) p)) := by
  simp only [discRep, hu]
  rw [tangentCoordChange_self (mem_extChartAt_source q)]

variable {A}

include hT in
/-- One piece, for a test function. -/
lemma term_eq {ρ : X.S → ℝ} {z : X.S} {ε : ℝ} {z' : X.S} {ε' : ℝ} {D : ChartChange}
    (hDK : D.K = pieceK ρ z ε) (hDψ : ∀ p ∈ D.K, D.ψ p = dtrans z ε z' ε' p)
    (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    coefS ρ z ε z' ε' p * φ (D.ψ p) = discCut p * secTerm ρ z' ε' φ (X.discPt z ε p) := by
  by_cases hp : p ∈ pieceK ρ z ε
  · rw [hDψ p (hDK ▸ hp), coefS, secTerm, dtrans_eq_stripPt]
    ring
  · have h0 : coefS ρ z ε z' ε' p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hp (tsupport_coefS_sub hT _ _ _ _ _ h)
    rw [h0, zero_mul, secTerm, ← mul_assoc, mul_div_assoc', piece_zero hp, zero_div, zero_mul]

include hT hu in
/-- One piece, for the representative of a section. -/
lemma term_rep_eq {ρ : X.S → ℝ} {z : X.S} {ε : ℝ} {j : Fin A.nd}
    (hρ : tsupport ρ ⊆ discSet (A.center j) (A.ε j)) {D : ChartChange}
    (hDK : D.K = pieceK ρ z ε) (hDψ : ∀ p ∈ D.K, D.ψ p = dtrans z ε (A.center j) (A.ε j) p)
    (kk : Fin (Module.finrank ℝ E)) (η : Section E X) (p : ℝ × ℝ) :
    coefS ρ z ε (A.center j) (A.ε j) p * discRep A j kk η (D.ψ p) =
      discCut p * ρ (X.discPt z ε p) * crd kk (η (X.discPt z ε p)) := by
  by_cases hp : p ∈ pieceK ρ z ε
  · have hpD := pieceK_sub hρ hp
    rw [hDψ p (hDK ▸ hp), discRep_const hu, discPt_trans (A.ε_pos j).ne' (pieceDom_sub hpD).1]
    have hne := (discCut_pos (pieceDom_sub hpD).2).ne'
    rw [coefS]
    field_simp
  · have h0 : coefS ρ z ε (A.center j) (A.ε j) p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hp (tsupport_coefS_sub hT _ _ _ _ _ h)
    rw [h0, zero_mul, piece_zero hp, zero_mul]

end Sections

/-! ## 3. The operator at every level -/

section Operator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
variable (D : Fin A.nd → Fin A.nd → ChartChange) (a : Fin A.nd → Fin A.nd → ℝ × ℝ → ℝ)
  (hc : ∀ i j, ContDiff ℝ ∞ (a i j)) (hs : ∀ i j, tsupport (a i j) ⊆ (D i j).K)

variable (δ h0 hmono) in
/-- The disc block `(i, k)` of `Φ`: `v ↦ ∑_j a_{ij} · (v_{j,k} ∘ ψ_{ij})`. -/
def secBlock (n : ℕ) (ik : Fin A.nd × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) n →L[ℝ] H (3 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  ∑ j, ((D ik.1 j).op (3 + n) (Neck.δ_nonneg δ h0 hmono n) (hc ik.1 j) (hs ik.1 j)
      (Neck.δ_nonneg δ h0 hmono n)).comp
        ((ContinuousLinearMap.proj (j, ik.2)).comp (ContinuousLinearMap.fst ℝ _ _))

variable (δ h0 hmono) in
/-- `(Φv)_{i,k} = ∑_j a_{ij} · (v_{j,k} ∘ ψ_{ij})` on the disc blocks, `0` on the neck blocks. -/
def secOp (n : ℕ) : (blocks A δ h0 hmono) n →L[ℝ] (blocks A δ h0 hmono) n :=
  (ContinuousLinearMap.pi fun ik => secBlock δ h0 hmono D a hc hs n ik).prod 0

lemma val_secOp (n : ℕ) (v : (blocks A δ h0 hmono) n) (ik : Fin A.nd × Fin (Module.finrank ℝ E)) :
    H.val ((secOp δ h0 hmono D a hc hs n v).1 ik) =
      ∑ j, (D ik.1 j).compMul (a ik.1 j) (H.val (v.1 (j, ik.2))) := by
  have e1 : (secOp δ h0 hmono D a hc hs n v).1 ik = ∑ j, (D ik.1 j).op (3 + n)
      (Neck.δ_nonneg δ h0 hmono n) (hc ik.1 j) (hs ik.1 j) (Neck.δ_nonneg δ h0 hmono n)
        (v.1 (j, ik.2)) := by
    change secBlock δ h0 hmono D a hc hs n ik v = _
    rw [secBlock, _root_.sum_apply]
    rfl
  rw [e1]
  refine (map_sum (valCLM (3 + n) (Neck.δ_nonneg δ h0 hmono n)) _ _).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  exact ChartChange.val_op (hc ik.1 j) (hs ik.1 j) (Neck.δ_nonneg δ h0 hmono n) _

lemma val_blocks_toBase (n : ℕ) (w : (blocks A δ h0 hmono) n)
    (ik : Fin A.nd × Fin (Module.finrank ℝ E)) :
    H.val (((blocks A δ h0 hmono).toBase n w).1 ik) = H.val (w.1 ik) := by
  have e1 := ScBanach.prod_toBase
    (finPiSc fun _ : Fin A.nd × Fin (Module.finrank ℝ E) => Neck.scCyl δ h0 hmono)
    (finPiSc fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => Neck.scCylC δ h0 hmono) n w
  have e2 := finPiScale_toBase
    (fun _ : Fin A.nd × Fin (Module.finrank ℝ E) => (Neck.scCyl δ h0 hmono).toScScale) n w.1
  have e3 : ((blocks A δ h0 hmono).toBase n w).1 ik =
      (Neck.scCyl δ h0 hmono).toBase n (w.1 ik) := by
    change (((finPiSc _).prod (finPiSc _)).toBase n w).1 ik = _
    rw [e1]
    exact congrFun e2 ik
  rw [e3]
  exact Neck.val_toBase δ h0 hmono n (w.1 ik)

lemma toBase_secOp (hnn : IsEmpty (Fin A.nn)) (n : ℕ) (v : (blocks A δ h0 hmono) n) :
    (blocks A δ h0 hmono).toBase n (secOp δ h0 hmono D a hc hs n v) =
      secOp δ h0 hmono D a hc hs 0 ((blocks A δ h0 hmono).toBase n v) := by
  refine Prod.ext (funext fun ik => ?_) (funext fun jk => isEmptyElim jk.1)
  apply valCLM_injective (m := 3) (hδ := Neck.δ_nonneg δ h0 hmono 0)
  refine ((val_blocks_toBase n _ ik).trans ?_).trans (val_secOp D a hc hs 0 _ ik).symm
  rw [val_secOp]
  exact Finset.sum_congr rfl fun j _ => by rw [val_blocks_toBase]

lemma coeFn_secOp (v : (blocks A δ h0 hmono) 0) (ik : Fin A.nd × Fin (Module.finrank ℝ E)) :
    (H.val ((secOp δ h0 hmono D a hc hs 0 v).1 ik) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => ∑ j, a ik.1 j x * H.val (v.1 (j, ik.2)) ((D ik.1 j).ψ x) := by
  rw [val_secOp]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun j => (D ik.1 j).compMul (a ik.1 j) (H.val (v.1 (j, ik.2))),
    ae_all_iff.2 fun j => (D ik.1 j).coeFn_compMul (hc ik.1 j).continuous (hs ik.1 j)
      (H.val (v.1 (j, ik.2)))] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun j _ => h2 j

end Operator

/-! ## 4. Density of the smooth sections -/

section Main

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hX : X.nodes = ∅) (hT : ChartsOnto X)
  {q : Q} {u : X.S → Q} (hu : ∀ x, u x = q) {A : SectionAtlas (E := E) X u}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
  {ρ : SmoothPartitionOfUnity (Fin A.nd) 𝓘(ℝ, E2) X.S univ}
  (hρ : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j))
  {D : Fin A.nd → Fin A.nd → ChartChange}
  (hDK : ∀ i j, (D i j).K = pieceK (ρ j) (A.center i) (A.ε i))
  (hDψ : ∀ i j, ∀ p ∈ (D i j).K,
    (D i j).ψ p = dtrans (A.center i) (A.ε i) (A.center j) (A.ε j) p)
  (hc : ∀ i j, ContDiff ℝ ∞ (coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)))
  (hs : ∀ i j, tsupport (coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)) ⊆ (D i j).K)

include hT hu hρ hDK hDψ in
/-- `Φ` is the identity on the representatives of sections. -/
lemma secOp_fix (hnn : IsEmpty (Fin A.nn)) {v : (blocks A δ h0 hmono) 0}
    (hv : v ∈ sectionsSub A δ h0 hmono) :
    secOp δ h0 hmono D (fun i j => coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j))
      hc hs 0 v = v := by
  obtain ⟨η, -, -, hr⟩ := hv
  refine Prod.ext (funext fun ik => ?_) (funext fun jk => isEmptyElim jk.1)
  apply valCLM_injective (m := 3) (hδ := Neck.δ_nonneg δ h0 hmono 0)
  apply Lp.ext
  have h1 : ∀ᵐ x ∂cyl, ∀ j, coefS (ρ j) (A.center ik.1) (A.ε ik.1) (A.center j) (A.ε j) x *
      H.val (v.1 (j, ik.2)) ((D ik.1 j).ψ x) =
        coefS (ρ j) (A.center ik.1) (A.ε ik.1) (A.center j) (A.ε j) x *
          discRep A j ik.2 η ((D ik.1 j).ψ x) :=
    ae_all_iff.2 fun j => ChartChange.comp_congr (hs ik.1 j) (hr.1 j ik.2)
  filter_upwards [coeFn_secOp D _ hc hs v ik, h1, hr.1 ik.1 ik.2] with x hx1 hx2 hx3
  refine (hx1.trans ?_).trans hx3.symm
  simp only [hx2]
  rw [Finset.sum_congr rfl fun j _ => term_rep_eq hT hu (hρ j) (hDK ik.1 j) (hDψ ik.1 j) ik.2 η x,
    ← Finset.sum_mul, ← Finset.mul_sum, discRep_const hu]
  have h := ρ.sum_eq_one (x := X.discPt (A.center ik.1) (A.ε ik.1) x) (mem_univ _)
  rw [finsum_eq_sum_of_fintype] at h
  rw [h, mul_one]

include hX hT hu hρ hDK hDψ in
/-- `Φ` maps a tuple of test functions to the representatives of a continuous section. -/
lemma secOp_mem (hnn : IsEmpty (Fin A.nn)) {w : (blocks A δ h0 hmono) 0}
    (hw : ∀ ik, ∃ φ, ∃ hφ : IsTest φ, w.1 ik = toH (3 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ) :
    secOp δ h0 hmono D (fun i j => coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j))
      hc hs 0 w ∈ sectionsSub A δ h0 hmono := by
  choose φ hφ hwφ using hw
  refine ⟨secOf A (fun j => ρ j) φ, isContSection_of_const hu (continuous_secOf A
    (fun j => (ρ j).2.continuous) hρ fun jk => (hφ jk).smooth.continuous), fun x y hxy => ?_,
    fun i kk => ?_, fun j => isEmptyElim j⟩
  · rw [hX] at hxy; exact absurd hxy (notMem_empty _)
  have h1 : ∀ᵐ x ∂cyl, ∀ j, coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) x *
      H.val (w.1 (j, kk)) ((D i j).ψ x) =
        coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j) x * φ (j, kk) ((D i j).ψ x) :=
    ae_all_iff.2 fun j => ChartChange.comp_congr (hs i j) (by
      rw [hwφ (j, kk)]; exact MemLp.coeFn_toLp ((hφ (j, kk)).memLp 2))
  filter_upwards [coeFn_secOp D _ hc hs w (i, kk), h1] with x hx1 hx2
  refine hx1.trans ?_
  simp only [hx2]
  rw [Finset.sum_congr rfl fun j _ => term_eq hT (hDK i j) (hDψ i j) (φ (j, kk)) x,
    ← Finset.mul_sum, discRep_const hu, crd_secOf]

end Main

section Dense

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m}

/-- **The smooth sections are dense** (Memoir p. 66, `H^{3,δ₀}_c(S, u*TQ)` is an sc-subspace):
on a surface without nodes whose charts are onto `ℝ²`, for a constant map and any atlas,
`SectionsDense`. -/
theorem sectionsDense_const (hX : X.nodes = ∅) (hT : ChartsOnto X) {q : Q} {u : X.S → Q}
    (hu : ∀ x, u x = q) (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0)
    (hmono : StrictMono δ) : SectionsDense A δ h0 hmono := by
  obtain ⟨ρ, hρ⟩ := exists_partition hX hT A
  have hρ' : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j) := hρ
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ' j)
  have hc : ∀ i j, ContDiff ℝ ∞ (coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)) :=
    fun i j => contDiff_coefS hT (ρ j) _ _ _ _ (hρ' j)
  have hs : ∀ i j, tsupport (coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j)) ⊆
      (D i j).K := fun i j => (hDK i j).symm ▸ tsupport_coefS_sub hT _ _ _ _ _
  have hnn := isEmpty_neck_of_nodes_empty hX A
  have huc : Continuous u := continuous_const.congr fun x => (hu x).symm
  have hS := sectionSpace_eq_of_nodes_empty huc hX A δ h0 hmono
  set Φ := secOp δ h0 hmono D (fun i j => coefS (ρ j) (A.center i) (A.ε i) (A.center j) (A.ε j))
    hc hs with hΦ
  let T : Set ((blocks A δ h0 hmono) 0) :=
    (univ.pi fun _ => {g : (Neck.scCyl δ h0 hmono) 0 |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (3 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ}) ×ˢ univ
  have hd : Dense T :=
    (dense_pi univ fun _ _ => dense_test (3 + 0) (Neck.δ_nonneg δ h0 hmono 0)).prod dense_univ
  have hmem : ∀ w, Φ 0 w ∈ sectionSpace A δ h0 hmono := by
    intro w
    have h1 : Φ 0 w ∈ closure (Φ 0 '' T) :=
      image_closure_subset_closure_image (Φ 0).continuous ⟨w, hd w, rfl⟩
    rw [hS]
    refine closure_minimal (image_subset_iff.2 fun w hw => ?_)
      (sectionsClosed_of_nodes_empty huc hX A δ h0 hmono) h1
    exact secOp_mem hX hT hu hρ' hDK hDψ hc hs hnn fun ik => hw.1 ik (mem_univ _)
  refine (sectionsDense_iff A δ h0 hmono).2 fun k x hx => ?_
  have hx' : (blocks A δ h0 hmono).toBase k x ∈ sectionsSub A δ h0 hmono := by
    rw [← hS]; exact hx
  have hfix : Φ k x = x := (blocks A δ h0 hmono).toBase_injective k (by
    rw [hΦ, toBase_secOp _ _ _ _ hnn, secOp_fix hT hu hρ' hDK hDψ hc hs hnn hx'])
  have hsm : (blocks A δ h0 hmono).smoothLvl k ⊆ Φ k ⁻¹'
      ((blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) k ∩
        (blocks A δ h0 hmono).smoothLvl k) := fun y hy => by
    refine ⟨?_, (blocks A δ h0 hmono).mem_smoothLvl_iff.2 fun j => ?_⟩
    · change (blocks A δ h0 hmono).toBase k (Φ k y) ∈ sectionSpace A δ h0 hmono
      rw [hΦ, toBase_secOp _ _ _ _ hnn]; exact hmem _
    · obtain ⟨y', hy'⟩ := (blocks A δ h0 hmono).mem_smoothLvl_iff.1 hy j
      exact ⟨Φ j y', by rw [hΦ, toBase_secOp _ _ _ _ hnn, toBase_secOp _ _ _ _ hnn, hy']⟩
  rw [← hfix]
  exact closure_mono (image_subset_iff.2 hsm) (image_closure_subset_closure_image
    (Φ k).continuous ⟨x, (blocks A δ h0 hmono).dense_smooth k x, rfl⟩)

/-- **Instance**: the constant maps from the three-pointed sphere, any atlas. -/
theorem sphere3_sectionsDense (q : Q) (A : SectionAtlas (E := E) sphere3 (fun _ => q))
    (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) : SectionsDense A δ h0 hmono :=
  sectionsDense_const rfl sphere3_chartsOnto (fun _ => rfl) A δ h0 hmono

end Dense

end GWMemoir
