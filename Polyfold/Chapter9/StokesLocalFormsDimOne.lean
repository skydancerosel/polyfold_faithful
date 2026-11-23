import Polyfold.Chapter9.StokesLocalForms
import Polyfold.Chapter9.LocalFormSystemDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 449–451, with Remark 9.5.19,
p. 451** (2017: Theorems 9.6, 9.7, Remark 9.8), point G.153, the case `n = 1`.  Numbers and pages
are the 2021 text's.

# Stokes' theorem from the pieces `β_k ω` near `supp Θ`, for a `1`-dimensional `Θ̂`

`StokesLocalForms.lean` for `n = 1`: the form `ω` is a function, the boundary `∂S` a finite set
of oriented points, and the boundary measures are built on the integration over oriented points
(`EP.zeroFormIntegration` for `Ω⁰_{ep,∞}(X)`, `EP.LocalFormSystemDimOne.pointIntegration` for the
functions near `supp Θ`).  The display on p. 451 is carried out for the pieces of an
`EP.LocalFormSystemDimOne`.

* `EpGroupoid.pointInteg_congr`, `pointInteg_eq_zero`: the integral over an oriented point only
  uses the value at the point.
* `EpGroupoid.boundaryMeasure_univ_eq_crossI`: two boundary measures with the same integrals over
  the boundary sheets have the same total mass.
* `OrientedTameStructure.exists_restrict_all_dim1`: the structures used (sheets in the class of
  every space of forms, boundary sheets with at most one point).
* `EP.stokes_of_localFormSystemDimOne`: the generic statement for one system of pieces.
* **`EP.stokes_of_localFormSystemsDimOne`**, **`EP.stokesEff_of_localFormSystemsDimOne`**:
  Theorems 9.5.17 and 9.5.18 for `n = 1`, from systems of pieces subordinate to every family of
  neighbourhoods.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-- The integral over an oriented point only uses the value at the point. -/
theorem pointInteg_congr {f f' : Obj → ℝ} {N : Set Obj} {g : Obj → X.PObj.OrTangent}
    {B : Set Obj} (h : ∀ y ∈ B ∩ N, f y = f' y) : pointInteg f N g B = pointInteg f' N g B := by
  unfold pointInteg
  split_ifs with hne
  · rw [h _ hne.some_mem]
  · rfl

/-- The integral over an oriented point of a function vanishing there is `0`. -/
theorem pointInteg_eq_zero {f : Obj → ℝ} {N : Set Obj} {g : Obj → X.PObj.OrTangent}
    {B : Set Obj} (h : ∀ y ∈ B ∩ N, f y = 0) : pointInteg f N g B = 0 := by
  unfold pointInteg
  split_ifs with hne
  · rw [h _ hne.some_mem, mul_zero]
  · rfl

section Cross

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  [AddCommGroup Ω'] [Module ℝ Ω']

/-- **The boundary measures of Theorems 9.5.15, 9.5.16 for two spaces of forms integrated over
the same class of sheets have the same total mass on forms with the same integrals over the parts
of the boundary sheets** (`boundaryMeasure_univ_eq_cross` for any integrations). -/
theorem boundaryMeasure_univ_eq_crossI (𝓘 : X.SheetIntegration G Ω)
    (𝓘' : X.SheetIntegration G Ω') {m : ℕ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
      (X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (Φ' : Ω' →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
      (X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (c : Obj → ℝ) (P : ∀ x, X.OrientedTameStructure (m + 1) Θ x → Prop)
    (hcpt : X.IsCompactBranched Θ)
    (hΦ : IsBoundaryLocalI 𝓘 hΘ Φ c P (T := T))
    (hΦ' : IsBoundaryLocalI 𝓘' hΘ Φ' c P (T := T))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) ∧ P x C)
    {ω : Ω} {ω' : Ω'}
    (hω : ∀ (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (i : C.ι) (B : Set Obj),
      B ⊆ C.boundarySheet i →
      𝓘'.integ ω' (C.boundarySheet i) (C.boundaryOrient i).tangent B =
        𝓘.integ ω (C.boundarySheet i) (C.boundaryOrient i).tangent B) :
    Φ' ω' univ = Φ ω univ := by
  have : CompactSpace (X.orbitSupp (X.boundaryTheta Θ)) := isCompact_iff_compactSpace.1
    (isCompact_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums Θ) hcpt)
  refine signedMeasure_univ_eq_of_local (borel_le_lebesgueSigmaBoundaryH (m + 1) Θ)
    (borel_le_lebesgueSigmaBoundaryH (m + 1) Θ) (Φ ω) (Φ' ω') fun q => ?_
  obtain ⟨y, hy, hyq⟩ := q.2
  obtain ⟨C, hCT, hS, hP⟩ := hcov y hy
  refine ⟨Subtype.val ⁻¹' (X.π '' C.U),
    (X.proposition_7_1_8 _ C.isOpen_U).preimage continuous_subtype_val, ⟨y, C.mem_U, hyq⟩,
    fun K hK hKN => ?_⟩
  have hKU : Subtype.val '' K ⊆ X.π '' C.U := by
    rintro _ ⟨q, hq, rfl⟩
    exact hKN hq
  have hK1 : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K :=
    borel_le_lebesgueSigmaBoundaryH (m + 1) Θ _ hK
  rw [hΦ' ω' y C hCT hy hS hP K hK1 hKU, hΦ ω y C hCT hy hS hP K hK1 hKU,
    OrientedSheetFamily.sheetSum, OrientedSheetFamily.sheetSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact hω y C i.1 _ inter_subset_right

end Cross

namespace OrientedTameStructure

/-- **The structures used for Stokes when `n = 1`** (as `exists_restrict_all`, with
`exists_boundarySheet_subsingleton`): every oriented tame structure of dimension `1` restricts to
one whose sheets are in the class of every space of forms and whose boundary sheets have at most
one point, with `x ∈ supp(∂Θ)` or `U(x)^*` disjoint from `supp(∂Θ)`; the natural action of the
restriction is a restriction of the given one. -/
theorem exists_restrict_all_dim1 (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (0 + 1)) {x : Obj}
    (C₀ : X.OrientedTameStructure (0 + 1) Θ x) (hC₀ : C₀.Represents T) :
    ∃ C : X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧
      (∀ i, IsChartBounded X (0 + 1) (C.M i)) ∧
      (∀ i, (C.boundarySheet i).Subsingleton) ∧
      (x ∈ supp (X.boundaryTheta Θ) ∨
        Disjoint (X.π ⁻¹' (X.π '' C.U)) (supp (X.boundaryTheta Θ))) ∧
      C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ := by
  obtain ⟨C₁, hCT₁, hS₁, -, hd₁, hU₁, hΦ₁⟩ := C₀.exists_restrict_all hΘ hcpt hnd hC₀
  obtain ⟨C, hCT, hs, hU, hΦ, V, hV, hM⟩ := C₁.exists_boundarySheet_subsingleton hCT₁
  have hUU : C.U ⊆ C₁.U := by
    rw [C.U_eq, C₁.U_eq]; exact hU
  refine ⟨C, hCT, fun i => ?_, hs, hd₁.imp id fun h =>
    h.mono_left (preimage_mono (image_mono hUU)), hU.trans hU₁, hΦ.trans hΦ₁⟩
  obtain ⟨j, hj⟩ := hM i
  rw [hj]
  exact (hS₁ j).inter_isOpen hV

end OrientedTameStructure

end EpGroupoid

open MPolyfold EpGroupoid

namespace EP

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Stokes' theorem from one system of pieces, generic form, `n = 1`** (the display on p. 451):
let `C_x`, `x ∈ supp Θ`, be structures describing `T̂Θ` with sheets in the class of every space of
forms, boundary sheets with at most one point, the condition `P`, and `x ∈ supp(∂Θ)` or `U(x)^*`
disjoint from `supp(∂Θ)`; let `S` be a system of pieces with `Z_k ⊆ U(x_k)^*`; let `Φ`, `Φb` be
the measures of `Ω_{ep,∞}(X)` and `Φ'`, `Φb'` those of the forms and functions near `supp Θ`, all
with the local formulas for the weights `c` and the condition `P`.  Then
`Φ(dω)(S) = Φb(ω)(∂S)`. -/
theorem stokes_of_localFormSystemDimOne (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (c : A.Obj → ℝ)
    (P : ∀ x, A.X.OrientedTameStructure (0 + 1) Θ x → Prop)
    (Cx : ∀ x, x ∈ supp Θ → A.X.OrientedTameStructure (0 + 1) Θ x)
    (hCT : ∀ x hx, (Cx x hx).Represents T)
    (hCS : ∀ x hx i, IsChartBounded A.X (0 + 1) ((Cx x hx).M i))
    (hCs : ∀ x hx i, ((Cx x hx).boundarySheet i).Subsingleton)
    (hCd : ∀ x hx, x ∈ supp (A.X.boundaryTheta Θ) ∨
      Disjoint (A.X.π ⁻¹' (A.X.π '' (Cx x hx).U)) (supp (A.X.boundaryTheta Θ)))
    (hCP : ∀ x hx, P x (Cx x hx))
    {N : A.Obj → Set A.Obj} {ω : A.epFormsInfty 0} (S : A.LocalFormSystemDimOne Θ N ω)
    (hZ : ∀ k, S.Z k ⊆ A.X.π ⁻¹' (A.X.π '' (Cx (S.pt k) (S.pt_mem k)).U))
    (Φ : A.epFormsInfty (0 + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
      (A.X.lebesgueSigma (A.epFormsInftyEval (0 + 1)).sheetNull Θ))
    (hΦ : ∀ (η : A.epFormsInfty (0 + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (0 + 1) Θ x),
      (∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets) → C.Represents T → P x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (0 + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (0 + 1)).sheetIntegration (Nat.succ_pos 0))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (Φb : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ))
    (hΦb : IsBoundaryLocalI A.zeroFormIntegration hΘ Φb c P (T := T))
    (Φ' : S.Ω1 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ) (A.X.lebesgueSigma S.F1.sheetNull Θ))
    (hΦ' : ∀ (η : S.Ω1) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x),
      (∀ i, C.M i ∈ S.F1.sheets) → C.Represents T → P x C →
      ∀ K : Set (A.X.orbitSupp Θ), MeasurableSet[A.X.lebesgueSigma S.F1.sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ' η K = c x * C.sheetSum (S.F1.sheetIntegration (Nat.succ_pos 0))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (Φb' : S.Ω0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ))
    (hΦb' : IsBoundaryLocalI S.pointIntegration hΘ Φb' c P (T := T)) :
    Φ (A.epFormsInftyD 0 ω) univ = Φb ω univ := by
  have hnd : A.X.IsNDimensional Θ (0 + 1) :=
    FormEval.isNDimensional_of_loc (P := fun _ _ => True) fun x hx => ⟨Cx x hx, trivial⟩
  have hF : ∀ x hx i, (Cx x hx).M i ∈ (A.epFormsInftyEval (0 + 1)).sheets :=
    fun x hx i => (hCS x hx i).mem_sheets _
  have hF1 : ∀ x hx i, (Cx x hx).M i ∈ S.F1.sheets := fun x hx i =>
    (hCS x hx i).mem_sheets S.F1
  have hsupp : ∀ {x} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι),
      C.boundarySheet i ⊆ supp Θ := fun C i y hy =>
    C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
      (C.boundarySheet_subset i hy)
  let Good : ∀ x, A.X.OrientedTameStructure (0 + 1) Θ x → Prop := fun x C =>
    (∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets) ∧ (∀ i, C.M i ∈ S.F1.sheets) ∧
      C.Represents T ∧ P x C
  have hcov : ∀ x ∈ supp Θ, ∃ C, Good x C := fun x hx =>
    ⟨Cx x hx, hF x hx, hF1 x hx, hCT x hx, hCP x hx⟩
  have hsub : ∀ {x}, x ∈ supp (A.X.boundaryTheta Θ) → x ∈ supp Θ := fun hx =>
    (A.X.supp_boundaryTheta_subset Θ hx).2
  have hpt : ∀ x hx i, ((Cx x hx).boundarySheet i).Nonempty →
      (Cx x hx).boundarySheet i ∈ pointSheets A.X := fun x hx i hne =>
    (Cx x hx).boundarySheet_mem_pointSheets hΘ i (hCs x hx i) hne
  have hcovB : ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) ∧ P x C :=
    fun x hx => ⟨Cx x (hsub hx), hCT x _, hpt x _, hCP x _⟩
  have hΦg : ∀ (η : S.Ω1) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ), MeasurableSet[A.X.lebesgueSigma S.F1.sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ' η K = c x * C.sheetSum (S.F1.sheetIntegration (Nat.succ_pos 0))
          η (A.X.π ⁻¹' (Subtype.val '' K)) :=
    fun η x C h => hΦ' η x C h.2.1 h.2.2.1 h.2.2.2
  -- the first and the last equality: the two spaces of forms
  have step1 : Φ' (S.j1 (A.epFormsInftyD 0 ω)) univ = Φ (A.epFormsInftyD 0 ω) univ :=
    measure_univ_eq_cross (A.epFormsInftyEval (0 + 1)) S.F1 (Nat.succ_pos 0) Φ Φ' c Good hcpt
      hcov (fun _ _ h => h.1) (fun _ _ h => h.2.1)
      (fun η x C h => hΦ η x C h.1 h.2.2.1 h.2.2.2) hΦg
      fun y hy M hM hyM β hβ => S.j1_ev _ hM hyM hy β hβ
  have step3 : Φb' (S.j0 ω) univ = Φb ω univ :=
    boundaryMeasure_univ_eq_crossI A.zeroFormIntegration S.pointIntegration hΘ Φb Φb' c P hcpt
      hΦb hΦb' hcovB fun x C i B hB => by
        rw [S.pointIntegration_integ, A.zeroFormIntegration_integ]
        exact pointInteg_congr fun y hy => S.j0_val ω (hsupp C i hy.2)
  -- the pieces
  have huniv : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ]
      (univ : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))) :=
    @MeasurableSet.univ _ (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ)
  have step2 : ∀ k, Φ' (S.v k) univ = Φb' (S.u k) univ := fun k => by
    set C := Cx (S.pt k) (S.pt_mem k) with hC
    have hCg : Good (S.pt k) C := ⟨hF _ _, hF1 _ _, hCT _ _, hCP _ _⟩
    have h1 := measure_univ_eq_of_integ_eq_zero (S.F1.sheetIntegration (Nat.succ_pos 0)) Φ' c
      Good hcpt (fun _ _ h => h.2.1) hcov hΦg (S.v k) C hCg (S.isClosed_Z k)
      (S.isSaturated_Z k) (hZ k) fun x' C' hC' i B hB hBZ => by
        rw [FormEval.sheetIntegration_integ]
        exact S.integ_v_eq_zero k C' i (hC'.2.1 i) B hB hBZ
    simp only [FormEval.sheetIntegration_integ] at h1
    have h2 : ∀ i, S.F1.integ (S.v k) (C.M i) (C.orient i).tangent (C.M i) =
        S.pointIntegration.integ (S.u k) (C.boundarySheet i) (C.boundaryOrient i).tangent
          (C.boundarySheet i) := fun i =>
      S.stokes_sheet k C i (hF1 _ _ i) (hCs _ _ i)
        (C.toTameBranchingStructure.isCompact_inter hcpt (S.isClosed_Z k) (S.isSaturated_Z k)
          (hZ k) i)
    rw [h1, Finset.sum_congr rfl fun i _ => by rw [h2 i]]
    rcases hCd (S.pt k) (S.pt_mem k) with hx | hd
    · exact (boundaryMeasure_univ_eqI S.pointIntegration hΘ Φb' c P
        (fun N B => point_isNull_iff_isHNull_zero N B)
        (fun a N g B h => pointInteg_of_empty h) hcpt hnd hΦb' hcovB (S.u k) C
        (hCT _ _) hx (hpt _ _) (hCP _ _) (S.isClosed_Z k) (S.isSaturated_Z k) (hZ k)
        fun x' C' _ i B hB hBZ => pointInteg_eq_zero fun y hy =>
          S.val_u_eq_zero k (hsupp C' i hy.2) (Set.disjoint_left.1 hBZ hy.1)).symm
    · have h0 : Φb' (S.u k) univ = 0 :=
        boundaryMeasure_eq_zero_of_integ_eq_zeroI S.pointIntegration hΘ Φb' c P hcpt hΦb' hcovB
          (S.u k) huniv fun x' C' _ i B hB => pointInteg_eq_zero fun y hy =>
            S.val_u_eq_zero k (hsupp C' i hy.2) fun hyZ =>
              Set.disjoint_left.1 hd (hZ k hyZ)
                (C'.boundarySheet_subset_supp_boundaryTheta i hy.2)
      rw [h0, Finset.sum_eq_zero fun i _ => ?_, mul_zero]
      rw [S.pointIntegration_integ, pointInteg_of_empty
        (by rw [C.boundarySheet_eq_empty hd i, inter_empty]), mul_zero]
  -- linearity
  let L1 : S.Ω1 →ₗ[ℝ] ℝ :=
    { toFun := fun η => Φ' η univ
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun r a => by rw [map_smul]; rfl }
  let L0 : S.Ω0 →ₗ[ℝ] ℝ :=
    { toFun := fun η => Φb' η univ
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun r a => by rw [map_smul]; rfl }
  have e1 : L1 (S.j1 (A.epFormsInftyD 0 ω)) = ∑ k, L1 (S.v k) := by
    rw [← S.sum_v, map_sum]
  have e0 : L0 (S.j0 ω) = ∑ k, L0 (S.u k) := by
    rw [← S.sum_u, map_sum]
  rw [← step1, ← step3]
  change L1 (S.j1 (A.epFormsInftyD 0 ω)) = L0 (S.j0 ω)
  rw [e1, e0]
  exact Finset.sum_congr rfl fun k _ => step2 k

/-! ### Theorems 9.5.17 and 9.5.18 for `n = 1` -/

open scoped Classical in
/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, with Remark 9.5.19, p. 451, for `n = 1`**: `Θ` a
compact branched ep⁺-subgroupoid, oriented by `T̂Θ = T`, tame (`hloc`), of dimension `1`, and
`ω ∈ Ω⁰_{ep,∞}(X)` with systems of pieces `β_k ω` near `supp Θ` subordinate to every family of
open neighbourhoods `N(x)` of the points of `supp Θ`: `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)`. -/
theorem stokes_of_localFormSystemsDimOne (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0)
    (hsys : ∀ N : A.Obj → Set A.Obj, (∀ x ∈ supp Θ, IsOpen (N x) ∧ x ∈ N x) →
      Nonempty (A.LocalFormSystemDimOne Θ N ω)) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω univ := by
  have hnd : A.X.IsNDimensional Θ (0 + 1) := FormEval.isNDimensional_of_loc hloc
  have hex : ∀ x (_ : x ∈ supp Θ), ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ (∀ i, IsChartBounded A.X (0 + 1) (C.M i)) ∧
      (∀ i, (C.boundarySheet i).Subsingleton) ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ))) := fun x hx => by
    obtain ⟨C₀, hC₀⟩ := hloc x hx
    obtain ⟨C, h1, h2, h3, h4, -, -⟩ := C₀.exists_restrict_all_dim1 hΘ hcpt hnd hC₀
    exact ⟨C, h1, h2, h3, h4⟩
  choose Cx hCT hCS hCs hCd using hex
  let N : A.Obj → Set A.Obj := fun x => if h : x ∈ supp Θ then (Cx x h).U else univ
  obtain ⟨S⟩ := hsys N fun x hx => by
    simp only [N, dif_pos hx]
    exact ⟨(Cx x hx).isOpen_U, (Cx x hx).mem_U⟩
  have hZ : ∀ k, S.Z k ⊆ A.X.π ⁻¹' (A.X.π '' (Cx (S.pt k) (S.pt_mem k)).U) := fun k => by
    have h := S.Z_subset k
    simp only [N, dif_pos (S.pt_mem k)] at h
    exact h
  set F := A.epFormsInftyEval (0 + 1) with hFdef
  have hcov := F.hcov_of_loc hloc
  have hcov1 : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      (∀ i, C.M i ∈ S.F1.sheets) ∧ C.Represents T := fun x hx =>
    ⟨Cx x hx, fun i => (hCS x hx i).mem_sheets S.F1, hCT x hx⟩
  have hcovB1 : ∀ x ∈ supp (A.X.boundaryTheta Θ),
      ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧
        ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X := fun x hx =>
    ⟨Cx x (A.X.supp_boundaryTheta_subset Θ hx).2, hCT x _, fun i hne =>
      (Cx x _).boundarySheet_mem_pointSheets hΘ i (hCs x _ i) hne⟩
  obtain ⟨Φb', hΦb', -⟩ := theorem_9_5_15_hyp S.pointIntegration hΘ hcpt hnd hT
    (fun N B => point_isNull_iff_isHNull_zero N B) hcovB1
  exact A.stokes_of_localFormSystemDimOne hΘ hcpt (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹)
    (fun _ _ => True) Cx hCT hCS hCs hCd (fun _ _ => trivial) S hZ
    (branchedMeasure (F.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov)
    (fun η x C hS hC _ K hK hKU => branchedMeasure_apply (F.sheetIntegration (Nat.succ_pos 0))
      hΘ hcpt hT hcov η C hS hC hK hKU)
    (A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc)
    (fun ω x C hC hx hS _ K hK hKU =>
      (A.theorem_9_5_15_dim1 hΘ hcpt hT hloc).exists.choose_spec ω x C hC hx hS K hK hKU)
    (branchedMeasure (S.F1.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov1)
    (fun η x C hS hC _ K hK hKU => branchedMeasure_apply
      (S.F1.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov1 η C hS hC hK hKU)
    Φb' (fun ω x C hC hx hS _ K hK hKU => hΦb' ω x C hC hx hS K hK hKU)

open scoped Classical in
/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, with Remark 9.5.19, p. 451, for `n = 1`**:
as `stokes_of_localFormSystemsDimOne`, when every point of `supp Θ` has an oriented tame
structure describing `T̂Θ` whose `U(x)` has the local unique continuation property:
`∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)`. -/
theorem stokesEff_of_localFormSystemsDimOne (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty 0)
    (hsys : ∀ N : A.Obj → Set A.Obj, (∀ x ∈ supp Θ, IsOpen (N x) ∧ x ∈ N x) →
      Nonempty (A.LocalFormSystemDimOne Θ N ω)) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc ω univ := by
  have hnd : A.X.IsNDimensional Θ (0 + 1) := FormEval.isNDimensional_of_loc hloc
  have hex : ∀ x (_ : x ∈ supp Θ), ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ (∀ i, IsChartBounded A.X (0 + 1) (C.M i)) ∧
      (∀ i, (C.boundarySheet i).Subsingleton) ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ))) ∧
      C.rep.HasLUC := fun x hx => by
    obtain ⟨C₀, hC₀, hL⟩ := hloc x hx
    obtain ⟨C, h1, h2, h3, h4, hU, hΦ⟩ := C₀.exists_restrict_all_dim1 hΘ hcpt hnd hC₀
    refine ⟨C, h1, h2, h3, h4, ?_⟩
    intro g V hV hne hVU hid y hy
    rw [hΦ] at hid ⊢
    exact hL g V hV hne (hVU.trans hU) hid y (hU hy)
  choose Cx hCT hCS hCs hCd hCL using hex
  let N : A.Obj → Set A.Obj := fun x => if h : x ∈ supp Θ then (Cx x h).U else univ
  obtain ⟨S⟩ := hsys N fun x hx => by
    simp only [N, dif_pos hx]
    exact ⟨(Cx x hx).isOpen_U, (Cx x hx).mem_U⟩
  have hZ : ∀ k, S.Z k ⊆ A.X.π ⁻¹' (A.X.π '' (Cx (S.pt k) (S.pt_mem k)).U) := fun k => by
    have h := S.Z_subset k
    simp only [N, dif_pos (S.pt_mem k)] at h
    exact h
  set F := A.epFormsInftyEval (0 + 1) with hFdef
  have hcov := F.hcovEff_of_loc hloc
  have hcov1 : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      (∀ i, C.M i ∈ S.F1.sheets) ∧ C.Represents T ∧ C.rep.HasLUC := fun x hx =>
    ⟨Cx x hx, fun i => (hCS x hx i).mem_sheets S.F1, hCT x hx, hCL x hx⟩
  have hcovB1 : ∀ x ∈ supp (A.X.boundaryTheta Θ),
      ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) ∧
        C.rep.HasLUC := fun x hx =>
    ⟨Cx x (A.X.supp_boundaryTheta_subset Θ hx).2, hCT x _, fun i hne =>
      (Cx x _).boundarySheet_mem_pointSheets hΘ i (hCs x _ i) hne, hCL x _⟩
  obtain ⟨Φb', hΦb', -⟩ := theorem_9_5_16_hyp S.pointIntegration hΘ hcpt hnd hT
    (fun N B => point_isNull_iff_isHNull_zero N B) hcovB1
  exact A.stokes_of_localFormSystemDimOne hΘ hcpt
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) (fun _ C => C.rep.HasLUC) Cx hCT hCS hCs
    hCd hCL S hZ
    (branchedMeasureEff (F.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov)
    (fun η x C hS hC hP K hK hKU => branchedMeasureEff_apply
      (F.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov η C hS hC hP hK hKU)
    (A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc)
    (fun ω x C hC hx hS hL K hK hKU =>
      (A.theorem_9_5_16_dim1 hΘ hcpt hT hloc).exists.choose_spec ω x C hC hx hS hL K hK hKU)
    (branchedMeasureEff (S.F1.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov1)
    (fun η x C hS hC hP K hK hKU => branchedMeasureEff_apply
      (S.F1.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov1 η C hS hC hP hK hKU)
    Φb' hΦb'

end EP

end Polyfold
