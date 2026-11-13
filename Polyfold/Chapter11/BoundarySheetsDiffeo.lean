import Polyfold.Chapter11.MultiChartSheetsEquivalence
import Polyfold.Chapter9.BoundaryMeasure
import Polyfold.Chapter11.BoundaryOrientationEquiv

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorems 11.4.4 and 11.4.5** (p. 545, new in the 2021 edition),
gap G.131.  Numbers and pages are the 2021 text's.

# Boundary sheets moved by an sc-diffeomorphism

The text says that there are versions of Theorems 11.4.1 and 11.4.2 for the boundary case, which
rely on Theorems 9.5.15 and 9.5.16.  The local step is the same as for Theorem 11.4.1: a
structure is moved by an sc-diffeomorphism `f : W → W'` between open subsets of the object spaces
of two ep-groupoids, now with its boundary sheets `∂₁Mᵢ` and boundary orientations `o_{∂Mᵢ}`
(Definition 9.3.8):

* `boundaryStratum_image_cross`: `∂₁(f(M)) = f(∂₁M)` (the reduced codimension is preserved,
  `hasReducedCodim_map_tangentMapOn_iff`); `boundaryStratum_inter_isOpen`;
* `OrientedTameStructure.boundarySheet_move`, `boundarySheet_restrictRep`, and
  `boundaryOrient_move_tangent`: `T_{f(y)}(∂₁f(Mᵢ), o_∂) = Tf(T_y(∂₁Mᵢ, o_∂))`
  (`boundaryOp_map_tangentMapOn`);
* `OrientedSheetFamily.sheetSum_nonemptyPart`: the sum over the nonempty sheets as a sum over all
  sheets;
* **`OrientedTameStructure.boundarySheetSum_move`**: the sums `∑ σᵢ ∫_{Aᵢ} ω|(∂₁Mᵢ, o_∂)` of
  Theorem 9.5.15 for a structure and its moved structure agree (E4's multi-chart integrals,
  `MultiChartSheetsEquivalence.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open MPolyfold

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-! ### The boundary stratum -/

/-- **`∂₁(f(M)) = f(∂₁M)`** for an sc-diffeomorphism `f : W → W'` between open subsets of the
object spaces of two ep-groupoids and an oriented smooth submanifold `M ⊆ W`. -/
theorem boundaryStratum_image_cross {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj}
    {W' : Set Obj'} (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') {M : Set Obj} {k : ℕ}
    (o : X.PObj.SubmanifoldOrientation M k) (hM : X.PObj.IsSmoothSubmanifold M)
    (hMW : M ⊆ W) :
    Y.PObj.boundaryStratum (f '' M) = f '' X.PObj.boundaryStratum M := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    refine ⟨y, (o.hasReducedCodim_iff_mem_boundaryStratum hy).1 ?_, rfl⟩
    have h1 := ((o.mapDiffeo hM hf hMW).hasReducedCodim_iff_mem_boundaryStratum
      (mem_image_of_mem f hy)).2 ⟨mem_image_of_mem f hy, h⟩
    rw [SubmanifoldOrientation.mapDiffeo_tangent o hM hf hMW hy] at h1
    exact (hasReducedCodim_map_tangentMapOn_iff hf (hMW hy) (o.isOrientedAt_tangent hy).1).1 h1
  · rintro ⟨y, hy, rfl⟩
    have hyM := hy.1
    refine ((o.mapDiffeo hM hf hMW).hasReducedCodim_iff_mem_boundaryStratum
      (mem_image_of_mem f hyM)).1 ?_
    rw [SubmanifoldOrientation.mapDiffeo_tangent o hM hf hMW hyM]
    exact (hasReducedCodim_map_tangentMapOn_iff hf (hMW hyM)
      (o.isOrientedAt_tangent hyM).1).2 ((o.hasReducedCodim_iff_mem_boundaryStratum hyM).2 hy)

/-- `∂₁(M ∩ V) = ∂₁M ∩ V` for an oriented `M` and an open `V`. -/
theorem boundaryStratum_inter_isOpen {M V : Set Obj} {k : ℕ}
    (o : X.PObj.SubmanifoldOrientation M k) (hV : IsOpen V) :
    X.PObj.boundaryStratum (M ∩ V) = X.PObj.boundaryStratum M ∩ V := by
  ext z
  constructor
  · intro h
    have hz := h.1
    have h1 := ((o.restrict hV).hasReducedCodim_iff_mem_boundaryStratum hz).2 h
    rw [o.restrict_tangent hV hz.2] at h1
    exact ⟨(o.hasReducedCodim_iff_mem_boundaryStratum hz.1).1 h1, hz.2⟩
  · rintro ⟨h, hzV⟩
    have hz : z ∈ M ∩ V := ⟨h.1, hzV⟩
    refine ((o.restrict hV).hasReducedCodim_iff_mem_boundaryStratum hz).1 ?_
    rw [o.restrict_tangent hV hzV]
    exact (o.hasReducedCodim_iff_mem_boundaryStratum h.1).2 h

namespace OrientedTameStructure

variable {m : ℕ} {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj}
  (C : X.OrientedTameStructure (m + 1) Θ x)

theorem boundarySheet_restrictRep (R : X.NaturalRep x) (hR : R.U ⊆ C.U) (i : C.ι) :
    (C.restrictRep R hR).boundarySheet i = C.boundarySheet i ∩ R.U :=
  boundaryStratum_inter_isOpen (C.orient i) R.isOpen_U

variable {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}
  (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y)
  (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U)
  (hP : Y.HasPropernessProperty (f '' C.U))

theorem M_subset_W (hUW : C.U ⊆ W) (i : C.ι) : C.M i ⊆ W := (C.subset_U i).trans hUW

/-- **The boundary sheets of the moved structure**: `∂₁f(Mᵢ) = f(∂₁Mᵢ)`. -/
theorem boundarySheet_move (i : C.ι) :
    (C.move hf hUW hxy hΘ R' hR' hP).boundarySheet i = f '' C.boundarySheet i := by
  have h := boundaryStratum_image_cross hf ((C.orient i).restrict hf.isScSmoothOn.isOpen)
    ((C.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) inter_subset_right
  change Y.PObj.boundaryStratum (f '' (C.M i ∩ W)) = _
  rw [h, inter_eq_left.2 (C.M_subset_W hUW i)]
  rfl

theorem boundarySheet_subset_W (hUW : C.U ⊆ W) (i : C.ι) : C.boundarySheet i ⊆ W :=
  (C.boundarySheet_subset i).trans (C.M_subset_W hUW i)

/-- **The boundary orientation of the moved structure**:
`T_{f(y)}(∂₁f(Mᵢ), o_∂) = Tf(T_y(∂₁Mᵢ, o_∂))`. -/
theorem boundaryOrient_move_tangent (i : C.ι) {u : Obj} (hu : u ∈ C.boundarySheet i) :
    ((C.move hf hUW hxy hΘ R' hR' hP).boundaryOrient i).tangent (f u) =
      ((C.boundaryOrient i).tangent u).map (tangentMapOn hf.isScSmoothOn) := by
  have huM : u ∈ C.M i := C.boundarySheet_subset i hu
  have huW : u ∈ W := C.M_subset_W hUW i huM
  have hu' : f u ∈ (C.move hf hUW hxy hΘ R' hR' hP).boundarySheet i := by
    rw [C.boundarySheet_move hf hUW hxy hΘ R' hR' hP]; exact mem_image_of_mem f hu
  rw [(C.move hf hUW hxy hΘ R' hR' hP).boundaryOrient_tangent i hu',
    C.boundaryOrient_tangent i hu]
  have ht : ((C.move hf hUW hxy hΘ R' hR' hP).orient i).tangent (f u) =
      ((C.orient i).tangent u).map (tangentMapOn hf.isScSmoothOn) := by
    change (((C.orient i).restrict hf.isScSmoothOn.isOpen).mapDiffeo
      ((C.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen) hf
      inter_subset_right).tangent (f u) = _
    rw [SubmanifoldOrientation.mapDiffeo_tangent _ _ hf _ (show u ∈ C.M i ∩ W from ⟨huM, huW⟩),
      (C.orient i).restrict_tangent _ huW]
  rw [ht]
  exact boundaryOp_map_tangentMapOn hf huW ((C.orient i).isOrientedAt_tangent huM)

end OrientedTameStructure

/-! ### The sums of Theorem 9.5.15 for a moved structure -/

namespace OrientedSheetFamily

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  (𝓘 : X.SheetIntegration G Ω) {D : Set Obj} {m : ℕ} {x : Obj}

open scoped Classical in
/-- The sum over the nonempty sheets as a sum over all sheets. -/
theorem sheetSum_nonemptyPart (F : X.OrientedSheetFamily D m x) (ω : Ω) (A : Set Obj) :
    F.nonemptyPart.sheetSum 𝓘 ω A = ∑ i, if (F.N i).Nonempty then
      (F.σ i : ℝ) * 𝓘.integ ω (F.N i) (F.orient i).tangent (A ∩ F.N i) else 0 := by
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter fun i => (F.N i).Nonempty)
    (p := fun i => (F.N i).Nonempty) (fun i => by simp)]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ fun _ => rfl

end OrientedSheetFamily

namespace OrientedTameStructure

variable {m : ℕ} {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj}
  (C : X.OrientedTameStructure (m + 1) Θ x)
  {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}
  {ΩS ΩT : Type*} [AddCommGroup ΩS] [Module ℝ ΩS] [AddCommGroup ΩT] [Module ℝ ΩT]
  {FS : X.FormEval m ΩS} {FT : Y.FormEval m ΩT}
  {T : Obj → X.PObj.OrTangent →₀ ℚ} {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}

/-- The nonempty boundary sheets of the moved structure lie in the class `FT.msheets` if those of
`C` lie in `FS.msheets` and every form of `ΩT` is moved to a form of `ΩS` on them. -/
theorem boundarySheet_move_mem_msheets (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
    (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U) (hP : Y.HasPropernessProperty (f '' C.U))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FS.msheets)
    (hcomp : ∀ i, ∀ ωT : ΩT, ∃ ωS : ΩS,
      FormEval.EvCompatOn FS FT hf (C.boundarySheet i) ωS ωT) (i : C.ι)
    (hne : ((C.move hf hUW hxy hΘ R' hR' hP).boundarySheet i).Nonempty) :
    (C.move hf hUW hxy hΘ R' hR' hP).boundarySheet i ∈ FT.msheets := by
  rw [C.boundarySheet_move hf hUW hxy hΘ R' hR' hP] at hne ⊢
  exact FormEval.image_mem_msheets_cross hf (hS i (image_nonempty.1 hne))
    (C.boundarySheet_subset_W hUW i) (hcomp i)

open scoped Classical in
/-- **(11.12) = (11.13) for the boundary sheets**: for a structure `C` whose nonempty boundary
sheets lie in `FS.msheets` and its moved structure,
`∑_{∂₁f(Mᵢ) ≠ ∅} σᵢ ∫_{B ∩ ∂₁f(Mᵢ)} ω_T|(∂₁f(Mᵢ), o_∂)`
`= ∑_{∂₁Mᵢ ≠ ∅} σᵢ ∫_{A ∩ ∂₁Mᵢ} ω_S|(∂₁Mᵢ, o_∂)`
whenever `B` meets `f(∂₁Mᵢ)` in `f(A ∩ ∂₁Mᵢ)`, `A` is measurable in the boundary sheets, and
`ω_T` is moved to `ω_S` on them. -/
theorem boundarySheetSum_move (hm : 0 < m) (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
    (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U) (hP : Y.HasPropernessProperty (f '' C.U))
    (hΘX : X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents T)
    (hΘY : Y.IsBranchedEpSubgroupoid Θ') (hCT' : (C.move hf hUW hxy hΘ R' hR' hP).Represents T')
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FS.msheets)
    (hS' : ∀ i, ((C.move hf hUW hxy hΘ R' hR' hP).boundarySheet i).Nonempty →
      (C.move hf hUW hxy hΘ R' hR' hP).boundarySheet i ∈ FT.msheets)
    {ωS : ΩS} {ωT : ΩT} (hω : ∀ i, FormEval.EvCompatOn FS FT hf (C.boundarySheet i) ωS ωT)
    {A : Set Obj} (hA : ∀ i, FS.sheetNull.IsMeasIn (C.boundarySheet i) A) {B : Set Obj'}
    (hB : ∀ i, B ∩ f '' C.boundarySheet i = f '' (A ∩ C.boundarySheet i)) :
    ((C.move hf hUW hxy hΘ R' hR' hP).boundaryFamily hΘY hCT').nonemptyPart.sheetSum
        (FT.msheetIntegration hm) ωT B =
      (C.boundaryFamily hΘX hCT).nonemptyPart.sheetSum (FS.msheetIntegration hm) ωS A := by
  rw [OrientedSheetFamily.sheetSum_nonemptyPart, OrientedSheetFamily.sheetSum_nonemptyPart]
  refine Finset.sum_congr rfl fun i _ => ?_
  set C' := C.move hf hUW hxy hΘ R' hR' hP
  have hbs : C'.boundarySheet i = f '' C.boundarySheet i :=
    C.boundarySheet_move hf hUW hxy hΘ R' hR' hP i
  change (if (C'.boundarySheet i).Nonempty then (C'.σ i : ℝ) *
      FT.msInteg ωT (C'.boundarySheet i) (C'.boundaryOrient i).tangent
        (B ∩ C'.boundarySheet i) else 0) =
    if (C.boundarySheet i).Nonempty then (C.σ i : ℝ) *
      FS.msInteg ωS (C.boundarySheet i) (C.boundaryOrient i).tangent
        (A ∩ C.boundarySheet i) else 0
  by_cases hne : (C.boundarySheet i).Nonempty
  · have hne' : (C'.boundarySheet i).Nonempty := by rw [hbs]; exact hne.image f
    rw [if_pos hne, if_pos hne']
    congr 1
    have hNW := C.boundarySheet_subset_W hUW i
    have hN := hS i hne
    have hN' := hS' i hne'
    have hfN : f '' C.boundarySheet i ∈ FT.msheets := hbs ▸ hN'
    have hAi : FS.sheetNull.IsMeasIn (C.boundarySheet i) (A ∩ C.boundarySheet i) :=
      SheetNullSets.isMeasIn_inter_iff.2 (hA i)
    have hBi : (B ∩ C'.boundarySheet i) ∩ f '' C.boundarySheet i =
        f '' ((A ∩ C.boundarySheet i) ∩ C.boundarySheet i) := by
      rw [hbs, inter_assoc, inter_self, hB i, inter_assoc, inter_self]
    have hBm : FT.sheetNull.IsMeasIn (C'.boundarySheet i) (B ∩ C'.boundarySheet i) := by
      rw [hbs]
      exact FormEval.isMeasIn_image_cross_of_inter_eq hf hNW hAi (hbs ▸ hBi)
    have e1 := (FT.msheetIntegration hm).integ_congr ωT _ hN' _ hfN (C'.boundaryOrient i)
      ((C.boundaryOrient i).mapDiffeo (C.isSubmanifoldOfDim_boundarySheet i).1 hf hNW)
      (B ∩ C'.boundarySheet i) (fun z hz => ⟨hz.2, hbs ▸ hz.2⟩) hBm fun z hz => by
        have hz' : z ∈ f '' C.boundarySheet i := hbs ▸ hz.2
        obtain ⟨u, hu, rfl⟩ := hz'
        rw [C.boundaryOrient_move_tangent hf hUW hxy hΘ R' hR' hP i hu,
          SubmanifoldOrientation.mapDiffeo_tangent _ _ hf hNW hu]
    simp only [FormEval.msheetIntegration_integ] at e1
    rw [e1]
    exact FormEval.msInteg_image_cross hf hm hN hfN hNW (C.boundaryOrient i) (hω i) hAi hBi
  · have hne' : ¬ (C'.boundarySheet i).Nonempty := by
      rw [hbs]; exact fun h => hne (image_nonempty.1 h)
    rw [if_neg hne, if_neg hne']

end OrientedTameStructure

end EpGroupoid

end Polyfold
