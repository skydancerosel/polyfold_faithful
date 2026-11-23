import Polyfold.Chapter9.LocalFormSystem
import Polyfold.Chapter9.BoundaryLocal
import Polyfold.Chapter11.MultiChartSheetsEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Remark 9.5.19, 2021 p. 451** (2017: Remark 9.8), point G.153.
Numbers and pages are the 2021 text's.

# Two spaces of forms with the same values on the sheets

The integrals of §9.5 are defined for a space of forms with values on tangent vectors
(`EpGroupoid.FormEval`).  For the proof of Theorem 9.5.18 with a partition of unity near `supp Θ`
(Remark 9.5.19) two such spaces are used: `Ω_{ep,∞}(X)` and the forms near `supp Θ`.  This file
compares the integrals and the measures of two spaces of forms.

* `FormEval.integ_cross`, `FormEval.msInteg_cross`: two forms (of two spaces) with the same values
  on the tangent spaces of a sheet have the same integrals over its measurable subsets.
* `signedMeasure_univ_eq_of_local`: two signed measures on a compact space (two σ-algebras
  containing the Borel sets) which agree near every point on the Borel sets have the same total
  mass.
* **`measure_univ_eq_cross`**: `μ_ω(S) = μ'_{ω'}(S)` for the measures of Theorems 9.5.4, 9.5.5 of
  two spaces of forms, `ω` and `ω'` with the same values on the tangent spaces at `supp Θ`.
* **`boundaryMeasure_univ_eq_cross`**: the same for the boundary measures of Theorems 9.5.15,
  9.5.16.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

/-- **Two signed measures that agree locally on the Borel sets have the same total mass**: `μ`,
`ν` signed measures on a compact space for two σ-algebras containing the Borel sets. -/
theorem signedMeasure_univ_eq_of_local {S : Type*} [TopologicalSpace S] [CompactSpace S]
    {m₁ m₂ : MeasurableSpace S} (h₁ : borel S ≤ m₁) (h₂ : borel S ≤ m₂)
    (μ : @SignedMeasure S m₁) (ν : @SignedMeasure S m₂)
    (hloc : ∀ s : S, ∃ N : Set S, IsOpen N ∧ s ∈ N ∧ ∀ K : Set S, MeasurableSet[borel S] K →
      K ⊆ N → ν K = μ K) :
    ν univ = μ univ := by
  classical
  choose N hNo hsN hN using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo
    (fun s _ => mem_iUnion.2 ⟨s, hsN s⟩)
  have key : ∀ t : Finset S, ∀ K : Set S, MeasurableSet[borel S] K → K ⊆ ⋃ s ∈ t, N s →
      ν K = μ K := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro K _ hKt
      have hK0 : K = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun s hs => ?_
        simpa using hKt hs
      rw [hK0, VectorMeasure.empty, VectorMeasure.empty]
    | insert a t _ ih =>
      intro K hK hKt
      have hNa : MeasurableSet[borel S] (N a) :=
        MeasurableSpace.measurableSet_generateFrom (hNo a)
      have h1 : MeasurableSet[borel S] (K ∩ N a) := @MeasurableSet.inter _ (borel S) _ _ hK hNa
      have h2 : MeasurableSet[borel S] (K \ N a) := @MeasurableSet.diff _ (borel S) _ _ hK hNa
      have hsub : K \ N a ⊆ ⋃ s ∈ t, N s := by
        intro s hs
        obtain ⟨b, hb⟩ := mem_iUnion.1 (hKt hs.1)
        obtain ⟨hbt, hsb⟩ := mem_iUnion.1 hb
        rcases Finset.mem_insert.1 hbt with rfl | hbt'
        · exact absurd hsb hs.2
        · exact mem_iUnion₂.2 ⟨b, hbt', hsb⟩
      have hdis : Disjoint (K ∩ N a) (K \ N a) :=
        Set.disjoint_left.2 fun s h h' => h'.2 h.2
      have hK' : K = K ∩ N a ∪ K \ N a := (inter_union_sdiff K (N a)).symm
      have e1 := hN a _ h1 inter_subset_right
      have e2 := ih _ h2 hsub
      have hμ : μ K = μ (K ∩ N a) + μ (K \ N a) := by
        conv_lhs => rw [hK']
        exact VectorMeasure.of_union hdis (h₁ _ h1) (h₁ _ h2)
      have hν : ν K = ν (K ∩ N a) + ν (K \ N a) := by
        conv_lhs => rw [hK']
        exact VectorMeasure.of_union hdis (h₂ _ h1) (h₂ _ h2)
      rw [hν, hμ, e1, e2]
  exact key t univ (@MeasurableSet.univ _ (borel S)) ht

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-! ### The integrals over one sheet -/

namespace FormEval

variable {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω'] {n : ℕ}
  (F : X.FormEval n Ω) (F' : X.FormEval n Ω') {N : Set Obj}

omit [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω'] in
/-- The tangent map of the identity is the identity. -/
theorem tangentMapOn_id_univ (h : X.PObj.IsScSmoothOn X.PObj id univ) :
    MPolyfold.tangentMapOn h = id :=
  funext fun α => MPolyfold.tangentMapOn_id h (show α ∈ X.PObj.tangentPreimage univ from mem_univ _)

omit [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω'] in
/-- The orientation moved by the identity has the same oriented tangent spaces. -/
theorem mapDiffeo_id_tangent (hN : X.PObj.IsSmoothSubmanifold N)
    (o : X.PObj.SubmanifoldOrientation N n)
    (hid : X.PObj.IsScDiffeoOn X.PObj id id univ univ) :
    (o.mapDiffeo hN hid (subset_univ N)).tangent = o.tangent := by
  funext z
  simp only [SubmanifoldOrientation.tangent, SubmanifoldOrientation.mapDiffeo_frames,
    tangentMapOn_id_univ hid.isScSmoothOn, id_eq]
  congr 1
  · rw [image_id']
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨v, hv, rfl⟩

/-- **Two forms with the same values on the tangent spaces of a sheet have the same integrals**
(the sheet in one graph chart, in the classes of both spaces of forms). -/
theorem integ_cross (hN : N ∈ F.sheets) (hN' : N ∈ F'.sheets)
    (o : X.PObj.SubmanifoldOrientation N n) {ω : Ω} {ω' : Ω'}
    (hω : ∀ y ∈ N, ∀ β : Fin n → X.PObj.TangentSpace,
      (∀ i, β i ∈ X.PObj.submanifoldTangent N y) → F'.ev ω' β = F.ev ω β)
    {A : Set Obj} (hA : F.sheetNull.IsMeasIn N A) :
    F'.integ ω' N o.tangent A = F.integ ω N o.tangent A := by
  have hid : X.PObj.IsScDiffeoOn X.PObj id id univ univ := MPolyfold.isScDiffeoOn_id isOpen_univ
  have hfN : id '' N ∈ F'.sheets := by rw [image_id]; exact hN'
  have hc : EvCompatOn F F' hid N ω ω' := fun y hy β hβ => by
    rw [tangentMapOn_id_univ hid.isScSmoothOn]
    exact hω y hy β hβ
  have key := integ_image_cross hid hN hfN (subset_univ N) o hc hA (B := A)
    (by rw [image_id, image_id])
  rw [mapDiffeo_id_tangent hN.1.1 o hid, image_id] at key
  exact key

/-- **Two forms with the same values on the tangent spaces of a sheet have the same integrals**
(the sheet covered by countably many graph charts, in the classes of both spaces of forms). -/
theorem msInteg_cross (hn : 0 < n) (hN : N ∈ F.msheets) (hN' : N ∈ F'.msheets)
    (o : X.PObj.SubmanifoldOrientation N n) {ω : Ω} {ω' : Ω'}
    (hω : ∀ y ∈ N, ∀ β : Fin n → X.PObj.TangentSpace,
      (∀ i, β i ∈ X.PObj.submanifoldTangent N y) → F'.ev ω' β = F.ev ω β)
    {A : Set Obj} (hA : F.sheetNull.IsMeasIn N A) :
    F'.msInteg ω' N o.tangent A = F.msInteg ω N o.tangent A := by
  have hid : X.PObj.IsScDiffeoOn X.PObj id id univ univ := MPolyfold.isScDiffeoOn_id isOpen_univ
  have hfN : id '' N ∈ F'.msheets := by rw [image_id]; exact hN'
  have hc : EvCompatOn F F' hid N ω ω' := fun y hy β hβ => by
    rw [tangentMapOn_id_univ hid.isScSmoothOn]
    exact hω y hy β hβ
  have key := msInteg_image_cross hid hn hN hfN (subset_univ N) o hc hA (B := A)
    (by rw [image_id, image_id])
  rw [mapDiffeo_id_tangent hN.1.1 o hid, image_id] at key
  exact key

end FormEval

/-! ### The measures -/

section Measures

variable {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']

open OrientedTameStructure in
/-- **The measures of Theorems 9.5.4, 9.5.5 for two spaces of forms have the same total mass on
forms with the same values**: `Φ`, `Φ'` with the local formula (weights `c`) for a class of
structures covering `supp Θ` with sheets in the classes of both spaces, and `ω`, `ω'` with the
same values on the tangent spaces of the submanifolds at the points of `supp Θ`. -/
theorem measure_univ_eq_cross {n : ℕ} (F : X.FormEval n Ω) (F' : X.FormEval n Ω') (hn : 0 < n)
    (Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.sheetNull Θ))
    (Φ' : Ω' →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F'.sheetNull Θ))
    (c : Obj → ℝ) (Good : ∀ x, X.OrientedTameStructure n Θ x → Prop)
    (hcpt : X.IsCompactBranched Θ) (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C)
    (hS : ∀ x C, Good x C → ∀ i, C.M i ∈ F.sheets)
    (hS' : ∀ x C, Good x C → ∀ i, C.M i ∈ F'.sheets)
    (hΦ : ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x), Good x C →
      ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K →
        Subtype.val '' K ⊆ X.π '' C.U →
        Φ ω K = c x * C.sheetSum (F.sheetIntegration hn) ω (X.π ⁻¹' (Subtype.val '' K)))
    (hΦ' : ∀ (ω : Ω') (x : Obj) (C : X.OrientedTameStructure n Θ x), Good x C →
      ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F'.sheetNull Θ] K →
        Subtype.val '' K ⊆ X.π '' C.U →
        Φ' ω K = c x * C.sheetSum (F'.sheetIntegration hn) ω (X.π ⁻¹' (Subtype.val '' K)))
    {ω : Ω} {ω' : Ω'}
    (hω : ∀ y ∈ supp Θ, ∀ M : Set Obj, X.PObj.IsSmoothSubmanifold M → y ∈ M →
      ∀ β : Fin n → X.PObj.TangentSpace, (∀ i, β i ∈ X.PObj.submanifoldTangent M y) →
        F'.ev ω' β = F.ev ω β) :
    Φ' ω' univ = Φ ω univ := by
  have : CompactSpace (X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  have hTS : X.HasTameSheetsIn F.sheets Θ := fun y hy => by
    obtain ⟨C, hC⟩ := hcov y hy
    exact ⟨C.toTameBranchingStructure, hS y C hC⟩
  refine signedMeasure_univ_eq_of_local (borel_le_borelNullSigma _) (borel_le_borelNullSigma _)
    (Φ ω) (Φ' ω') fun q => ?_
  obtain ⟨y, hy, hyq⟩ := q.2
  obtain ⟨C, hC⟩ := hcov y hy
  refine ⟨Subtype.val ⁻¹' (X.π '' C.U),
    (X.proposition_7_1_8 _ C.isOpen_U).preimage continuous_subtype_val, ⟨y, C.mem_U, hyq⟩,
    fun K hK hKN => ?_⟩
  have hKU : Subtype.val '' K ⊆ X.π '' C.U := by
    rintro _ ⟨q, hq, rfl⟩
    exact hKN hq
  have hK1 : MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K := borel_le_borelNullSigma _ _ hK
  rw [hΦ' ω' y C hC K (borel_le_borelNullSigma _ _ hK) hKU, hΦ ω y C hC K hK1 hKU, sheetSum,
    sheetSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [FormEval.sheetIntegration_integ]
  exact FormEval.integ_cross F F' (hS y C hC i) (hS' y C hC i) (C.orient i)
    (fun z hz β hβ => hω z
      (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hz) (C.M i)
      (C.isSubmanifoldOfDim i).1 hz β hβ)
    (SheetNullSets.isMeasIn_inter_iff.2 (C.isMeas_preimage hTS (hS y C hC) hK1 i))

/-- **The boundary measures of Theorems 9.5.15, 9.5.16 for two spaces of forms have the same
total mass on forms with the same values**: `Φ`, `Φ'` with the local formula (weights `c`,
condition `P`), structures at the points of `supp(∂Θ)` with nonempty boundary sheets in the
classes of both spaces, and `ω`, `ω'` with the same values on the tangent spaces of the
submanifolds at the points of `supp Θ`. -/
theorem boundaryMeasure_univ_eq_cross {m : ℕ} (F : X.FormEval m Ω) (F' : X.FormEval m Ω')
    (hm : 0 < m) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
      (X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (Φ' : Ω' →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
      (X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (c : Obj → ℝ) (P : ∀ x, X.OrientedTameStructure (m + 1) Θ x → Prop)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1))
    (hΦ : IsBoundaryLocal F hm hΘ Φ c P (T := T))
    (hΦ' : IsBoundaryLocal F' hm hΘ Φ' c P (T := T))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F'.msheets) ∧ P x C)
    {ω : Ω} {ω' : Ω'}
    (hω : ∀ y ∈ supp Θ, ∀ M : Set Obj, X.PObj.IsSmoothSubmanifold M → y ∈ M →
      ∀ β : Fin m → X.PObj.TangentSpace, (∀ i, β i ∈ X.PObj.submanifoldTangent M y) →
        F'.ev ω' β = F.ev ω β) :
    Φ' ω' univ = Φ ω univ := by
  have : CompactSpace (X.orbitSupp (X.boundaryTheta Θ)) := isCompact_iff_compactSpace.1
    (isCompact_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums Θ) hcpt)
  refine signedMeasure_univ_eq_of_local (borel_le_lebesgueSigmaBoundaryH (m + 1) Θ)
    (borel_le_lebesgueSigmaBoundaryH (m + 1) Θ) (Φ ω) (Φ' ω') fun q => ?_
  obtain ⟨y, hy, hyq⟩ := q.2
  obtain ⟨C, hCT, hS, hS', hP⟩ := hcov y hy
  refine ⟨Subtype.val ⁻¹' (X.π '' C.U),
    (X.proposition_7_1_8 _ C.isOpen_U).preimage continuous_subtype_val, ⟨y, C.mem_U, hyq⟩,
    fun K hK hKN => ?_⟩
  have hKU : Subtype.val '' K ⊆ X.π '' C.U := by
    rintro _ ⟨q, hq, rfl⟩
    exact hKN hq
  have hK1 : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K :=
    borel_le_lebesgueSigmaBoundaryH (m + 1) Θ _ hK
  rw [hΦ' ω' y C hCT hy hS' hP K hK1 hKU, hΦ ω y C hCT hy hS hP K hK1 hKU,
    OrientedSheetFamily.sheetSum, OrientedSheetFamily.sheetSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  change F'.msInteg ω' (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (X.π ⁻¹' (Subtype.val '' K) ∩ C.boundarySheet i.1) =
    F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (X.π ⁻¹' (Subtype.val '' K) ∩ C.boundarySheet i.1)
  refine FormEval.msInteg_cross F F' hm (hS i.1 i.2) (hS' i.1 i.2) (C.boundaryOrient i.1)
    (fun z hz β hβ => hω z
      (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i.1
        (C.boundarySheet_subset i.1 hz)) (C.boundarySheet i.1)
      (C.isSubmanifoldOfDim_boundarySheet i.1).1 hz β hβ)
    (SheetNullSets.isMeasIn_inter_iff.2 ?_)
  exact C.isMeasIn_boundarySheet (G := F.msheetNull) (fun _ _ => Iff.rfl) hnd hy i.1 hK1

end Measures

end EpGroupoid

end Polyfold
