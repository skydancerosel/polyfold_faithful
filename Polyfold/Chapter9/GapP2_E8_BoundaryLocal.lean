import Polyfold.Chapter9.GapP2_E7_BoundaryMeasure
import Polyfold.Chapter9.GapP2_E5_MeasureLocal
import Polyfold.Chapter9.GapP2_E5_FunForm
import Polyfold.Chapter9.GapP2_E3_TameOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorems 9.5.17 and 9.5.18** (pp. 449–451; 2017: Theorems
9.6, 9.7), gap G.110.  Numbers and pages are the 2021 text's.

# The boundary measures `μ^∂_ω` are local

The proof on p. 451 evaluates `μ^∂_{ω_k}(∂S)` for the forms `ω_k = β_k ω` with `supp β_k ⊆ U_k^*`
by the local formula of Theorem 9.5.15 on one structure.  This needs that the measure of a form
vanishing on the boundary sheets above a set is zero there (the boundary analogue of E5's
`measure_eq_zero_of_integ_eq_zero` and `measure_univ_eq_of_integ_eq_zero`), for E4's integral
over countably many graph charts (`FormEval.msInteg`).

* `FormEval.msInteg_eq_zero_of_ev_eq_zero`: `∫_B ω = 0` over a sheet of `msheets` when `ω`
  vanishes on the tangent frames at the points of `B`.
* **`boundaryMeasure_eq_zero_of_integ_eq_zero`**: `μ^∂_ω(D) = 0` when the integrals of `ω` over
  the parts of the boundary sheets above `D` vanish.
* **`boundaryMeasure_univ_eq`**: `μ^∂_ω(∂S) = c(x) ∑ᵢ σᵢ ∫_{∂₁Mᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` for one
  structure at `x ∈ supp(∂Θ)` when the integrals vanish off a closed saturated `Z ⊆ U(x)^*`.
* `isOpen_compl_preimage_orbitSupp_boundaryTheta`, `mem_compl_preimage_orbitSupp_boundaryTheta`:
  the complement of `π⁻¹(∂S)` is an open neighbourhood of the points off `supp(∂Θ)`.
* `OrientedTameStructure.exists_restrict_subset`: an oriented tame structure restricted into a
  given open neighbourhood of `x` (sheets in `F.sheets`, the same `T̂Θ`, the same action).
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

/-! ### Vanishing integrals over the sheets of `msheets` -/

namespace FormEval

variable {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {m : ℕ} (F : X.FormEval m Ω)

/-- **`∫_B ω|(N, g) = 0` when `ω` vanishes on the tangent frames at the points of `B ∩ N`**
(E4's integral over countably many graph charts). -/
theorem msInteg_eq_zero_of_ev_eq_zero (ω : Ω) (N : Set Obj) (g : Obj → X.PObj.OrTangent)
    {B : Set Obj} (h : ∀ y ∈ B ∩ N, ∀ (N' : Set Obj), X.PObj.IsSmoothSubmanifold N' → y ∈ N' →
      ∀ α : Fin m → X.PObj.TangentSpace, (∀ i, α i ∈ X.PObj.submanifoldTangent N' y) →
        F.ev ω α = 0) :
    F.msInteg ω N g B = 0 := by
  unfold msInteg
  split_ifs with hN
  · unfold ChartCover.gInteg
    refine (tsum_congr fun k => ?_).trans tsum_zero
    refine F.integ_eq_zero_of_ev_eq_zero ω _ _ fun y hy α hα => ?_
    exact h y ⟨hy.1.1, hy.2.1⟩ _ (hN.1.1.1.1.inter_isOpen (hN.1.1.2.choose.isOpen k)) hy.2 α hα
  · rfl

/-- `∫_B ω|(∅, g) = 0`. -/
theorem msInteg_empty (ω : Ω) (g : Obj → X.PObj.OrTangent) (B : Set Obj) :
    F.msInteg ω ∅ g B = 0 :=
  F.msInteg_of_inter_eq_empty ω g (inter_empty B)

end FormEval

/-! ### Locality of the boundary measures -/

section Local

variable {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {m : ℕ} (F : X.FormEval m Ω) (hm : 0 < m)
  (hΘ : X.IsBranchedEpSubgroupoid Θ)
  (Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
    (X.lebesgueSigmaBoundaryH (m + 1) Θ)) (c : Obj → ℝ)
  (P : ∀ x, X.OrientedTameStructure (m + 1) Θ x → Prop)

/-- The local formula of Theorems 9.5.15, 9.5.16 for `Φ`, for the structures at the points of
`supp(∂Θ)` describing `T̂Θ` with boundary sheets in `F.msheets` and the condition `P`. -/
def IsBoundaryLocal : Prop :=
  ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
    x ∈ supp (X.boundaryTheta Θ) →
    (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) → P x C →
    ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
      MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
      Subtype.val '' K ⊆ X.π '' C.U →
      Φ ω K = c x * (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum (F.msheetIntegration hm) ω
        (X.π ⁻¹' (Subtype.val '' K))

omit [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj] in
open scoped Classical in
/-- A sum over the nonempty sheets is the sum over all sheets when the empty ones contribute `0`. -/
theorem sum_nonempty_eq {ι : Type*} [Fintype ι] (N : ι → Set Obj) (f : ι → ℝ)
    (h0 : ∀ i, ¬ (N i).Nonempty → f i = 0) :
    ∑ i : {i // (N i).Nonempty}, f i.1 = ∑ i, f i := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => (N i).Nonempty) f]
  have hz : ∑ i : {i // ¬ (N i).Nonempty}, f i.1 = 0 :=
    Finset.sum_eq_zero fun i _ => h0 i.1 i.2
  rw [hz, add_zero]

/-- **The boundary measure of a form whose integrals over the parts of the boundary sheets above
`D` vanish**: `Φ(ω)(D) = 0`, for `Φ` with the local formula (Theorems 9.5.15, 9.5.16) on a class
of structures covering `supp(∂Θ)`. -/
theorem boundaryMeasure_eq_zero_of_integ_eq_zero (hcpt : X.IsCompactBranched Θ)
    (hΦ : IsBoundaryLocal F hm hΘ Φ c P (T := T))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        P x C)
    (ω : Ω) {D : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hD : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] D)
    (h0 : ∀ (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x), x ∈ supp (X.boundaryTheta Θ) →
      ∀ i, ∀ B : Set Obj, B ⊆ C.boundarySheet i ∩ X.π ⁻¹' (Subtype.val '' D) →
        F.msInteg ω (C.boundarySheet i) (C.boundaryOrient i).tangent B = 0) :
    Φ ω D = 0 := by
  let _ : MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) := X.lebesgueSigmaBoundaryH (m + 1) Θ
  have : CompactSpace (X.orbitSupp (X.boundaryTheta Θ)) := isCompact_iff_compactSpace.1
    (isCompact_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums Θ) hcpt)
  let J := {j : Σ x, X.OrientedTameStructure (m + 1) Θ x //
    j.1 ∈ supp (X.boundaryTheta Θ) ∧ j.2.Represents T ∧
      (∀ i, (j.2.boundarySheet i).Nonempty → j.2.boundarySheet i ∈ F.msheets) ∧ P j.1 j.2}
  let O : J → Set (X.orbitSupp (X.boundaryTheta Θ)) := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨y, hy, hyq⟩ := q.2
    obtain ⟨C, hCT, hS, hP⟩ := hcov y hy
    exact mem_iUnion.2 ⟨⟨⟨y, C⟩, hy, hCT, hS, hP⟩, y, C.mem_U, hyq⟩
  have hν : (Φ ω).restrict D = 0 :=
    signedMeasure_eq_zero_of_openCover (borel_le_lebesgueSigmaBoundaryH (m + 1) Θ) O hO hcovO _
      fun j K hK hKO => by
        rw [VectorMeasure.restrict_apply _ hD hK,
          hΦ ω j.1.1 j.1.2 j.2.2.1 j.2.1 j.2.2.2.1 j.2.2.2.2 (K ∩ D) (hK.inter hD)
            (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq.1), OrientedSheetFamily.sheetSum]
        rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
        change _ * F.msInteg ω (j.1.2.boundarySheet i.1) (j.1.2.boundaryOrient i.1).tangent _ = 0
        rw [h0 j.1.1 j.1.2 j.2.1 i.1 _ fun y hy =>
          ⟨hy.2, image_mono inter_subset_right hy.1⟩, mul_zero]
  have h := congrArg (fun ν : SignedMeasure (X.orbitSupp (X.boundaryTheta Θ)) => ν univ) hν
  simpa using h

/-- **The second equality of the display on p. 451, boundary side**: let `Φ` have the local
formula of Theorem 9.5.15 (9.5.16) for a class covering `supp(∂Θ)`, `C` a structure of the class
at `x ∈ supp(∂Θ)`, and `Z ⊆ U(x)^*` closed and saturated such that the integrals of `ω` over the
subsets of the boundary sheets disjoint from `Z` vanish.  Then
`Φ(ω)(∂S) = c(x) ∑ᵢ σᵢ ∫_{∂₁Mᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})`. -/
theorem boundaryMeasure_univ_eq (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ (m + 1))
    (hΦ : IsBoundaryLocal F hm hΘ Φ c P (T := T))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        P x C)
    (ω : Ω) {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T)
    (hx : x ∈ supp (X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) (hP : P x C)
    {Z : Set Obj} (hZ : IsClosed Z) (hsat : X.IsSaturated Z) (hZU : Z ⊆ X.π ⁻¹' (X.π '' C.U))
    (h0 : ∀ (x' : Obj) (C' : X.OrientedTameStructure (m + 1) Θ x'),
      x' ∈ supp (X.boundaryTheta Θ) → ∀ i, ∀ B : Set Obj, B ⊆ C'.boundarySheet i →
        Disjoint B Z → F.msInteg ω (C'.boundarySheet i) (C'.boundaryOrient i).tangent B = 0) :
    Φ ω univ = c x * ∑ i, (C.σ i : ℝ) *
      F.msInteg ω (C.boundarySheet i) (C.boundaryOrient i).tangent (C.boundarySheet i) := by
  let _ : MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) := X.lebesgueSigmaBoundaryH (m + 1) Θ
  set D : Set (X.orbitSupp (X.boundaryTheta Θ)) := Subtype.val ⁻¹' (X.π '' Z) with hDdef
  have hDc : IsClosed D := (isClosed_π_image hZ hsat).preimage continuous_subtype_val
  have hD : MeasurableSet D :=
    borel_le_lebesgueSigmaBoundaryH (m + 1) Θ _ (@MeasurableSet.of_compl _ D (borel _)
      (MeasurableSpace.measurableSet_generateFrom hDc.isOpen_compl))
  have h2 : Φ ω Dᶜ = 0 :=
    boundaryMeasure_eq_zero_of_integ_eq_zero F hm hΘ Φ c P hcpt hΦ hcov ω hD.compl
      fun x' C' hx' i B hB => h0 x' C' hx' i B (fun y hy => (hB hy).1)
        (Set.disjoint_left.2 fun y hyB hyZ => by
          obtain ⟨q, hq, hqy⟩ := (hB hyB).2
          exact hq (show q.1 ∈ X.π '' Z from hqy ▸ ⟨y, hyZ, rfl⟩))
  have hDU : Subtype.val '' D ⊆ X.π '' C.U := by
    rintro _ ⟨q, ⟨z, hz, hzq⟩, rfl⟩
    rw [← hzq]
    exact hZU hz
  have h1 := hΦ ω x C hCT hx hS hP D hD hDU
  have hsplit : Φ ω univ = Φ ω D + Φ ω Dᶜ := by
    rw [← VectorMeasure.of_union disjoint_compl_right hD hD.compl, union_compl_self]
  rw [hsplit, h2, add_zero, h1, OrientedSheetFamily.sheetSum]
  congr 1
  set Pr : Set Obj := X.π ⁻¹' (Subtype.val '' D) with hPr
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (sum_nonempty_eq C.boundarySheet
    (fun i => (C.σ i : ℝ) * F.msInteg ω (C.boundarySheet i) (C.boundaryOrient i).tangent
      (C.boundarySheet i)) fun i hi => ?_)
  swap
  · rw [F.msInteg_of_inter_eq_empty ω _ (by rw [not_nonempty_iff_eq_empty.1 hi, inter_empty]),
      mul_zero]
  congr 1
  have hNS := hS i.1 i.2
  have hPm : F.msheetNull.IsMeasIn (C.boundarySheet i.1) Pr :=
    C.isMeasIn_boundarySheet (G := F.msheetNull) (fun _ _ => Iff.rfl) hnd hx i.1 hD
  have hPc : F.msheetNull.IsMeasIn (C.boundarySheet i.1) Prᶜ := MeasurableSet.compl hPm
  have hun : C.boundarySheet i.1 = (Pr ∩ C.boundarySheet i.1) ∪ (Prᶜ ∩ C.boundarySheet i.1) := by
    rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  have hz : F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (Prᶜ ∩ C.boundarySheet i.1) = 0 :=
    h0 x C hx i.1 _ inter_subset_right (Set.disjoint_left.2 fun y hy hyZ => hy.1 (by
      exact ⟨⟨X.π y, C.π_mem_orbitSupp_boundaryTheta hy.2⟩, ⟨y, hyZ, rfl⟩, rfl⟩))
  have e : F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (C.boundarySheet i.1) = F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
        ((Pr ∩ C.boundarySheet i.1) ∪ (Prᶜ ∩ C.boundarySheet i.1)) :=
    congrArg (F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent) hun
  have hu : F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      ((Pr ∩ C.boundarySheet i.1) ∪ (Prᶜ ∩ C.boundarySheet i.1)) =
      F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent (Pr ∩ C.boundarySheet i.1) +
        F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
          (Prᶜ ∩ C.boundarySheet i.1) :=
    (F.msheetIntegration hm).integ_union ω hNS (C.boundaryOrient i.1)
      inter_subset_right inter_subset_right
      (SheetNullSets.isMeasIn_inter_iff.2 hPm) (SheetNullSets.isMeasIn_inter_iff.2 hPc)
      (Set.disjoint_left.2 fun y hy hy' => hy'.1 hy.1)
  change F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
    (Pr ∩ C.boundarySheet i.1) = F.msInteg ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (C.boundarySheet i.1)
  rw [e, hu, hz, add_zero]

end Local

/-! ### Off the boundary -/

/-- The complement of `π⁻¹(∂S)` is open. -/
theorem isOpen_compl_preimage_orbitSupp_boundaryTheta (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) :
    IsOpen (X.π ⁻¹' X.orbitSupp (X.boundaryTheta Θ))ᶜ :=
  ((isClosed_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums Θ) hcpt.isClosed).preimage
    X.continuous_π).isOpen_compl

/-- `supp(∂Θ)` is saturated: a point with the orbit of a point of `supp(∂Θ)` lies in it. -/
theorem mem_supp_boundaryTheta_of_π_eq (hΘ : X.IsBranchedEpSubgroupoid Θ) {a b : Obj}
    (hab : X.π a = X.π b) (ha : a ∈ supp (X.boundaryTheta Θ)) :
    b ∈ supp (X.boundaryTheta Θ) := by
  obtain ⟨φ, rfl, rfl⟩ := X.π_eq_π_iff.1 hab
  change 0 < X.boundaryTheta Θ (X.tgt φ)
  rw [← X.isFunctorial_boundaryTheta hΘ (hasIndependentTangentSums Θ) φ]
  exact ha

/-- A point off `supp(∂Θ)` lies in the complement of `π⁻¹(∂S)`. -/
theorem mem_compl_preimage_orbitSupp_boundaryTheta (hΘ : X.IsBranchedEpSubgroupoid Θ) {x : Obj}
    (hx : x ∉ supp (X.boundaryTheta Θ)) :
    x ∈ (X.π ⁻¹' X.orbitSupp (X.boundaryTheta Θ))ᶜ := fun ⟨_, hz, hzx⟩ =>
  hx (mem_supp_boundaryTheta_of_π_eq hΘ hzx hz)

/-- If `U ⊆ (π⁻¹(∂S))ᶜ` then `U^* = π⁻¹(π(U))` does not meet `supp(∂Θ)`. -/
theorem disjoint_preimage_image_supp_boundaryTheta {U : Set Obj}
    (hU : U ⊆ (X.π ⁻¹' X.orbitSupp (X.boundaryTheta Θ))ᶜ) :
    Disjoint (X.π ⁻¹' (X.π '' U)) (supp (X.boundaryTheta Θ)) :=
  Set.disjoint_left.2 fun y ⟨_, hu, huy⟩ hy => hU hu ⟨y, hy, huy.symm⟩

namespace OrientedTameStructure

open scoped Classical in
/-- **An oriented tame structure restricted into an open neighbourhood `W` of `x`**: sheets in
`F.sheets` stay there, it describes the same `T̂Θ`, and the natural action is the restriction of
the given one (E3's `exists_restrict_mem_sheets` with the neighbourhood prescribed). -/
theorem exists_restrict_subset {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    (F : X.FormEval n Ω) {x : Obj} (C₀ : X.OrientedTameStructure n Θ x) (hC₀ : C₀.Represents T)
    (hS₀ : ∀ i, C₀.M i ∈ F.sheets) {W : Set Obj} (hWo : IsOpen W) (hxW : x ∈ W) :
    ∃ C : X.OrientedTameStructure n Θ x, (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧
      C.U ⊆ W ∧ C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ := by
  obtain ⟨R', hR'sub, hR'Φ, -⟩ := exists_naturalRep_shrink X C₀.rep hWo hxW
  have hsubU : R'.U ⊆ C₀.U := fun y hy => C₀.U_eq ▸ (hR'sub hy).2
  let C : X.OrientedTameStructure n Θ x :=
    { toLocalBranchingStructure :=
        C₀.toLocalBranchingStructure.restrict R'.isOpen_U R'.mem_U hsubU
      rep := R'
      U_eq := rfl
      hasPropernessProperty := C₀.hasPropernessProperty.mono R'.isOpen_U hsubU
      hasTameInducedStructure := fun i =>
        FormEval.tameOpen X _ _ (C₀.isSmoothSubmanifold i) (C₀.hasTameInducedStructure i)
          R'.isOpen_U
      isSubmanifoldOfDim := fun i => (C₀.isSubmanifoldOfDim i).inter_isOpen R'.isOpen_U
      orient := fun i => (C₀.orient i).restrict R'.isOpen_U }
  refine ⟨C, fun i => FormEval.inter_mem_sheets (hS₀ i) R'.isOpen_U, fun y hy hys => ?_,
    fun y hy => (hR'sub hy).1, fun y hy => (hR'sub hy).2, hR'Φ⟩
  have hyU' : y ∈ R'.U := hy
  rw [hC₀ y (hsubU hy) hys, C₀.orientedSum_eq_sum_ite, C.orientedSum_eq_sum_ite]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff : y ∈ C.M i ↔ y ∈ C₀.M i := ⟨fun h => h.1, fun h => ⟨h, hyU'⟩⟩
  have ht : (C.orient i).tangent y = (C₀.orient i).tangent y :=
    (C₀.orient i).restrict_tangent R'.isOpen_U hyU'
  by_cases h : y ∈ C₀.M i
  · rw [if_pos h, if_pos (hiff.2 h), ht]
    rfl
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

/-- **The boundary sheets of a structure whose `U(x)^*` avoids `supp(∂Θ)` are empty.** -/
theorem boundarySheet_eq_empty {m : ℕ} {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x)
    (hd : Disjoint (X.π ⁻¹' (X.π '' C.U)) (supp (X.boundaryTheta Θ))) (i : C.ι) :
    C.boundarySheet i = ∅ :=
  eq_empty_of_forall_notMem fun _ hy => Set.disjoint_left.1 hd
    (subset_preimage_image X.π C.U (C.subset_U i (C.boundarySheet_subset i hy)))
    (C.boundarySheet_subset_supp_boundaryTheta i hy)

end OrientedTameStructure

end EpGroupoid

end Polyfold
