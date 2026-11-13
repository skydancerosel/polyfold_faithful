import Polyfold.Chapter9.GapP3_K2_BoundaryDim1
import Polyfold.Chapter9.GapP3_K2_FaceDim1
import Polyfold.Chapter9.GapP2_E8_Stokes

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.17 and 9.5.18 for `n = 1`** (pp. 449–451; 2017:
Theorems 9.6, 9.7), gap G.110.  Numbers and pages are the 2021 text's.

# Stokes' theorem for a `1`-dimensional `Θ̂`

For `n = 1` the boundary `∂S` is a finite set of oriented points and the boundary measure of
Theorem 9.5.15 is built on E1's integral over oriented points (`EP.zeroFormIntegration`,
`theorem_9_5_15_dim1`).  Stokes' theorem `∫_Θ̂ dω = μ^∂_ω(∂S)` for `ω ∈ Ω⁰_{ep,∞}(X)` follows as
in E8 (`EP.stokes_of_boundaryMeasure`) from E6's `stokes_of_boundary_functional_all`, with
Part I's boundary integral of a `0`-form over a `1`-dimensional sheet computed in
`GapP3_K2_FaceDim1` (`boundaryIntegral_eq_zeroFormIntegration`).  The hypotheses are those of the
text: `X` with sc-smooth partitions of unity, `Θ` compact, oriented, and an oriented tame
structure describing `T̂Θ` at every point (gap G.107's reading); no class hypothesis on the sheets
or the boundary sheets.

## The generic locality lemmas

`IsBoundaryLocalI`, `boundaryMeasure_eq_zero_of_integ_eq_zeroI`, `boundaryMeasure_univ_eqI`: E8's
`IsBoundaryLocal`, `boundaryMeasure_eq_zero_of_integ_eq_zero`, `boundaryMeasure_univ_eq` for an
arbitrary integration over the sheets of a class `S` (E8 states them for `FormEval.msheets`,
which needs `0 < m`).

## Main results

* `EP.stokes_of_boundaryMeasure_dim1`: the generic form (E8's `stokes_of_boundaryMeasure` for
  `n = 1`).
* **`EP.theorem_9_5_17_dim1`**: `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` with the boundary measure of Theorem
  9.5.15 (`boundaryBranchedMeasureDim1`).
* **`EP.theorem_9_5_18_dim1`**: `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)`, for structures with the local unique
  continuation property (`boundaryBranchedMeasureEffDim1`).
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

/-! ### Locality of the boundary measures, for any integration over sheets -/

section Local

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  (𝓘 : X.SheetIntegration G Ω) {m : ℕ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
  (Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
    (X.lebesgueSigmaBoundaryH (m + 1) Θ)) (c : Obj → ℝ)
  (P : ∀ x, X.OrientedTameStructure (m + 1) Θ x → Prop)

/-- The local formula of Theorems 9.5.15, 9.5.16 for `Φ`, for the structures at the points of
`supp(∂Θ)` describing `T̂Θ` with boundary sheets in the class `S` of the integration `𝓘` and the
condition `P` (E8's `IsBoundaryLocal` for any `𝓘`). -/
def IsBoundaryLocalI : Prop :=
  ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
    x ∈ supp (X.boundaryTheta Θ) →
    (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) → P x C →
    ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
      MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
      Subtype.val '' K ⊆ X.π '' C.U →
      Φ ω K = c x * (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum 𝓘 ω
        (X.π ⁻¹' (Subtype.val '' K))

/-- **The boundary measure of a form whose integrals over the parts of the boundary sheets above
`D` vanish** is `0` on `D` (E8's `boundaryMeasure_eq_zero_of_integ_eq_zero` for any `𝓘`). -/
theorem boundaryMeasure_eq_zero_of_integ_eq_zeroI (hcpt : X.IsCompactBranched Θ)
    (hΦ : IsBoundaryLocalI 𝓘 hΘ Φ c P (T := T))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) ∧ P x C)
    (ω : Ω) {D : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hD : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] D)
    (h0 : ∀ (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x), x ∈ supp (X.boundaryTheta Θ) →
      ∀ i, ∀ B : Set Obj, B ⊆ C.boundarySheet i ∩ X.π ⁻¹' (Subtype.val '' D) →
        𝓘.integ ω (C.boundarySheet i) (C.boundaryOrient i).tangent B = 0) :
    Φ ω D = 0 := by
  let _ : MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) := X.lebesgueSigmaBoundaryH (m + 1) Θ
  have : CompactSpace (X.orbitSupp (X.boundaryTheta Θ)) := isCompact_iff_compactSpace.1
    (isCompact_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums Θ) hcpt)
  let J := {j : Σ x, X.OrientedTameStructure (m + 1) Θ x //
    j.1 ∈ supp (X.boundaryTheta Θ) ∧ j.2.Represents T ∧
      (∀ i, (j.2.boundarySheet i).Nonempty → j.2.boundarySheet i ∈ S) ∧ P j.1 j.2}
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
        change _ * 𝓘.integ ω (j.1.2.boundarySheet i.1) (j.1.2.boundaryOrient i.1).tangent _ = 0
        rw [h0 j.1.1 j.1.2 j.2.1 i.1 _ fun y hy =>
          ⟨hy.2, image_mono inter_subset_right hy.1⟩, mul_zero]
  have h := congrArg (fun ν : SignedMeasure (X.orbitSupp (X.boundaryTheta Θ)) => ν univ) hν
  simpa using h

/-- **The second equality of the display on p. 451, boundary side**, for any `𝓘` whose null sets
are those of dimension `m` and which vanishes over sets missing the sheet (E8's
`boundaryMeasure_univ_eq`): `Φ(ω)(∂S) = c(x) ∑ᵢ σᵢ ∫_{∂₁Mᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})`. -/
theorem boundaryMeasure_univ_eqI (hG : ∀ N A, G.IsNull N A ↔ X.PObj.IsHNull m (A ∩ N))
    (hempty : ∀ ω N g B, B ∩ N = ∅ → 𝓘.integ ω N g B = 0)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1))
    (hΦ : IsBoundaryLocalI 𝓘 hΘ Φ c P (T := T))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) ∧ P x C)
    (ω : Ω) {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T)
    (hx : x ∈ supp (X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) (hP : P x C)
    {Z : Set Obj} (hZ : IsClosed Z) (hsat : X.IsSaturated Z) (hZU : Z ⊆ X.π ⁻¹' (X.π '' C.U))
    (h0 : ∀ (x' : Obj) (C' : X.OrientedTameStructure (m + 1) Θ x'),
      x' ∈ supp (X.boundaryTheta Θ) → ∀ i, ∀ B : Set Obj, B ⊆ C'.boundarySheet i →
        Disjoint B Z → 𝓘.integ ω (C'.boundarySheet i) (C'.boundaryOrient i).tangent B = 0) :
    Φ ω univ = c x * ∑ i, (C.σ i : ℝ) *
      𝓘.integ ω (C.boundarySheet i) (C.boundaryOrient i).tangent (C.boundarySheet i) := by
  let _ : MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) := X.lebesgueSigmaBoundaryH (m + 1) Θ
  set D : Set (X.orbitSupp (X.boundaryTheta Θ)) := Subtype.val ⁻¹' (X.π '' Z) with hDdef
  have hDc : IsClosed D := (isClosed_π_image hZ hsat).preimage continuous_subtype_val
  have hD : MeasurableSet D :=
    borel_le_lebesgueSigmaBoundaryH (m + 1) Θ _ (@MeasurableSet.of_compl _ D (borel _)
      (MeasurableSpace.measurableSet_generateFrom hDc.isOpen_compl))
  have h2 : Φ ω Dᶜ = 0 :=
    boundaryMeasure_eq_zero_of_integ_eq_zeroI 𝓘 hΘ Φ c P hcpt hΦ hcov ω hD.compl
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
    (fun i => (C.σ i : ℝ) * 𝓘.integ ω (C.boundarySheet i) (C.boundaryOrient i).tangent
      (C.boundarySheet i)) fun i hi => ?_)
  swap
  · rw [hempty ω _ _ _ (by rw [not_nonempty_iff_eq_empty.1 hi, inter_empty]), mul_zero]
  congr 1
  have hNS := hS i.1 i.2
  have hPm : G.IsMeasIn (C.boundarySheet i.1) Pr :=
    C.isMeasIn_boundarySheet hG hnd hx i.1 hD
  have hPc : G.IsMeasIn (C.boundarySheet i.1) Prᶜ := MeasurableSet.compl hPm
  have hun : C.boundarySheet i.1 = (Pr ∩ C.boundarySheet i.1) ∪ (Prᶜ ∩ C.boundarySheet i.1) := by
    rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  have hz : 𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (Prᶜ ∩ C.boundarySheet i.1) = 0 :=
    h0 x C hx i.1 _ inter_subset_right (Set.disjoint_left.2 fun y hy hyZ => hy.1 (by
      exact ⟨⟨X.π y, C.π_mem_orbitSupp_boundaryTheta hy.2⟩, ⟨y, hyZ, rfl⟩, rfl⟩))
  have e : 𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (C.boundarySheet i.1) = 𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
        ((Pr ∩ C.boundarySheet i.1) ∪ (Prᶜ ∩ C.boundarySheet i.1)) :=
    congrArg (𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent) hun
  have hu : 𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      ((Pr ∩ C.boundarySheet i.1) ∪ (Prᶜ ∩ C.boundarySheet i.1)) =
      𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent (Pr ∩ C.boundarySheet i.1) +
        𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
          (Prᶜ ∩ C.boundarySheet i.1) :=
    𝓘.integ_union ω hNS (C.boundaryOrient i.1)
      inter_subset_right inter_subset_right
      (SheetNullSets.isMeasIn_inter_iff.2 hPm) (SheetNullSets.isMeasIn_inter_iff.2 hPc)
      (Set.disjoint_left.2 fun y hy hy' => hy'.1 hy.1)
  change 𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
    (Pr ∩ C.boundarySheet i.1) = 𝓘.integ ω (C.boundarySheet i.1) (C.boundaryOrient i.1).tangent
      (C.boundarySheet i.1)
  rw [e, hu, hz, add_zero]

end Local

end EpGroupoid

/-! ### Stokes for `n = 1` -/

namespace EP

open MPolyfold EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- `∫_B βa|(N, g) = 0` over oriented points when `β` vanishes on `B ∩ N`. -/
theorem zeroFormIntegration_smul_eq_zero {β : A.Obj → ℝ}
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (a : A.epFormsInfty 0) (N : Set A.Obj)
    (g : A.Obj → A.X.PObj.OrTangent) {B : Set A.Obj} (h : ∀ y ∈ B ∩ N, β y = 0) :
    A.zeroFormIntegration.integ (A.epFormsInftySmul β 0 hβ hinv a) N g B = 0 := by
  rw [zeroFormIntegration_integ, pointInteg]
  split_ifs with hne
  · rw [A.zeroFormEval_epFormsInftySmul hβ hinv a, h _ hne.some_mem, zero_mul, mul_zero]
  · rfl

/-- **The boundary integrals of `βa` over the sheets of one structure** (`n = 1`; last equality
of the display on p. 451): for `supp β ⊆ U(x)^*`, `Θ` compact and boundary sheets with at most one
point, `∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βa = ∑ᵢ σᵢ ∫_{∂₁Mᵢ} βa|(∂₁Mᵢ, o_{∂Mᵢ})`. -/
theorem sum_boundaryIntegral_smul_eq_dim1 (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) {x : A.Obj}
    (C : A.X.OrientedTameStructure (0 + 1) Θ x)
    (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets)
    (hs : ∀ i, (C.boundarySheet i).Subsingleton)
    {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hsupp : tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U)) (a : A.epFormsInfty 0) :
    ∑ i, (C.σ i : ℝ) * (C.orientedSheet (A.epFormsInftyEval (0 + 1)) hS i).boundaryIntegral
        (A.epFormsInftyToObj 0 (A.epFormsInftySmul β 0 hβ hinv a)) =
      ∑ i, (C.σ i : ℝ) * A.zeroFormIntegration.integ (A.epFormsInftySmul β 0 hβ hinv a)
        (C.boundarySheet i) (C.boundaryOrient i).tangent (C.boundarySheet i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hK : IsCompact (C.M i ∩ tsupport β) :=
    C.toTameBranchingStructure.isCompact_inter hcpt (isClosed_tsupport β)
      (EpGroupoid.isSaturated_tsupport hinv) hsupp i
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  have h0 : (C.orientedSheet (A.epFormsInftyEval (0 + 1)) hS i).VanishesOff (tsupport β)
      (A.epFormsInftyToObj 0 (A.epFormsInftySmul β 0 hβ hinv a)) := fun y hy =>
    A.formsInftyRestrict_smul_eq_zero_all (hcs := hcs) hβ hinv a y hy
  exact A.boundaryIntegral_eq_zeroFormIntegration hΘ C hS i (hs i) _ (isClosed_tsupport β) hK h0

/-- **The structures used for Stokes when `n = 1`**: from an oriented tame structure describing
`T̂Θ` at `x ∈ supp Θ`, one with the same action, sheets in one graph chart, boundary sheets with
at most one point, and `U(x)^*` either centred on `supp(∂Θ)` or disjoint from it. -/
theorem exists_good_dim1 (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    {x : A.Obj} (C₀ : A.X.OrientedTameStructure (0 + 1) Θ x) (hC₀ : C₀.Represents T) :
    ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Subsingleton) ∧ C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ))) := by
  obtain ⟨C₁, hS₁, hCT₁, hU₁, hΦ₁⟩ := (A.epFormsInftyEval (0 + 1)).exists_restrict_mem_sheets
    (FormEval.tameOpen A.X) C₀ hC₀
  obtain ⟨C₂, hCT₂, hs₂, hU₂, hΦ₂, V, hV, hM⟩ := C₁.exists_boundarySheet_subsingleton hCT₁
  have hS₂ : ∀ i, C₂.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets := fun i => by
    obtain ⟨j, hj⟩ := hM i
    rw [hj]
    exact FormEval.inter_mem_sheets (hS₁ j) hV
  by_cases hxb : x ∈ supp (A.X.boundaryTheta Θ)
  · exact ⟨C₂, hCT₂, hS₂, hs₂, hU₂.trans hU₁, hΦ₂.trans hΦ₁, Or.inl hxb⟩
  · obtain ⟨C, hS, hCT, hUW, hU, hΦeq⟩ :=
      C₂.exists_restrict_subset (A.epFormsInftyEval (0 + 1)) hCT₂ hS₂
        (isOpen_compl_preimage_orbitSupp_boundaryTheta hΘ hcpt)
        (mem_compl_preimage_orbitSupp_boundaryTheta hΘ hxb)
    have hd := disjoint_preimage_image_supp_boundaryTheta hUW
    refine ⟨C, hCT, hS, fun i => ?_, hU.trans (hU₂.trans hU₁), hΦeq.trans (hΦ₂.trans hΦ₁),
      Or.inr hd⟩
    rw [C.boundarySheet_eq_empty hd i]
    exact subsingleton_empty

variable (Φ : A.epFormsInfty (0 + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
    (A.X.lebesgueSigma (A.epFormsInftyEval (0 + 1)).sheetNull Θ))
  (Φb : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
    (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ))
  (c : A.Obj → ℝ) (P : ∀ x, A.X.OrientedTameStructure (0 + 1) Θ x → Prop)

/-- **Stokes' theorem with the boundary measure for `n = 1`, generic form** (E8's
`stokes_of_boundaryMeasure` for `n = 1`): let `Φ` have the local formula of Theorem 9.5.4 or 9.5.5
and `Φb` the one of Theorem 9.5.15 or 9.5.16 over the oriented boundary points (weights `c`, a
condition `P` on the structures, inherited by restrictions with the same action), and let every
point of `supp Θ` have a structure describing `T̂Θ` with `P`.  Then `Φ(dω)(S) = Φb(ω)(∂S)`. -/
theorem stokes_of_boundaryMeasure_dim1 (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hPres : ∀ x (C₀ C : A.X.OrientedTameStructure (0 + 1) Θ x), P x C₀ →
      C.rep.U ⊆ C₀.rep.U → C.rep.Φ = C₀.rep.Φ → P x C)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧ P x C)
    (hΦ : ∀ (η : A.epFormsInfty (0 + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (0 + 1) Θ x),
      (∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets) → C.Represents T → P x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (0 + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (0 + 1)).sheetIntegration (Nat.succ_pos 0))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (hΦb : IsBoundaryLocalI A.zeroFormIntegration hΘ Φb c P (T := T))
    (ω : A.epFormsInfty 0) :
    Φ (A.epFormsInftyD 0 ω) univ = Φb ω univ := by
  have hnd : A.X.IsNDimensional Θ (0 + 1) := FormEval.isNDimensional_of_loc hloc
  let Good : ∀ x, A.X.OrientedTameStructure (0 + 1) Θ x → Prop := fun x C =>
    ((∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets) ∧ C.Represents T ∧ P x C) ∧
      (∀ i, (C.boundarySheet i).Subsingleton) ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ)))
  have hcov : ∀ x ∈ supp Θ, ∃ C, Good x C := fun x hx => by
    obtain ⟨C₀, hCT₀, hP₀⟩ := hloc x hx
    obtain ⟨C, hCT, hS, hs, hU, hΦeq, hor⟩ := A.exists_good_dim1 hΘ hcpt C₀ hCT₀
    exact ⟨C, ⟨hS, hCT, hPres x C₀ C hP₀ hU hΦeq⟩, hs, hor⟩
  have hcovB : ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) ∧
        P x C := fun x hx => by
    obtain ⟨C, ⟨-, hCT, hP⟩, hs, -⟩ := hcov x (A.X.supp_boundaryTheta_subset Θ hx).2
    exact ⟨C, hCT, fun i hne => C.boundarySheet_mem_pointSheets hΘ i (hs i) hne, hP⟩
  let Φb' : A.epFormsInfty 0 →ₗ[ℝ] ℝ :=
    { toFun := fun ω => Φb ω univ
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun r a => by rw [map_smul]; rfl }
  have huniv : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ]
      (univ : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))) :=
    @MeasurableSet.univ _ (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ)
  refine A.stokes_of_boundary_functional_all Φ c Good hPU hcpt (fun _ _ h => h.1.1) hcov
    (fun η x C hC K hK hKU => hΦ η x C hC.1.1 hC.1.2.1 hC.1.2.2 K hK hKU) Φb'
    (fun x C hC β hβ hinv hs ω => ?_) (fun β hβ hinv hd ω => ?_) ω
  · change Φb (A.epFormsInftySmul β 0 hβ hinv ω) univ = _
    rw [A.sum_boundaryIntegral_smul_eq_dim1 hΘ hcpt C hC.1.1 hC.2.1 hβ hinv hs ω]
    rcases hC.2.2 with hx | hd
    · exact boundaryMeasure_univ_eqI A.zeroFormIntegration hΘ Φb c P
        (fun N B => point_isNull_iff_isHNull_zero N B)
        (fun ω N g B h => A.zeroFormIntegration_integ_of_empty ω g h) hcpt hnd hΦb hcovB _ C
        hC.1.2.1 hx (fun i hne => C.boundarySheet_mem_pointSheets hΘ i (hC.2.1 i) hne)
        hC.1.2.2 (isClosed_tsupport β) (EpGroupoid.isSaturated_tsupport hinv) hs
        fun x' C' _ i B _ hBZ => A.zeroFormIntegration_smul_eq_zero hβ hinv ω _ _ fun y hy =>
          image_eq_zero_of_notMem_tsupport (Set.disjoint_left.1 hBZ hy.1)
    · have h1 : Φb (A.epFormsInftySmul β 0 hβ hinv ω) univ = 0 :=
        boundaryMeasure_eq_zero_of_integ_eq_zeroI A.zeroFormIntegration hΘ Φb c P hcpt hΦb hcovB
          _ huniv
          fun x' C' _ i B hB => A.zeroFormIntegration_smul_eq_zero hβ hinv ω _ _ fun y hy =>
            image_eq_zero_of_notMem_tsupport fun hyt => Set.disjoint_left.1 hd (hs hyt)
              (C'.boundarySheet_subset_supp_boundaryTheta i (hB hy.1).1)
      rw [h1, Finset.sum_eq_zero fun i _ => ?_, mul_zero]
      rw [A.zeroFormIntegration_integ_of_empty _ _
        (by rw [C.boundarySheet_eq_empty hd i, inter_empty]),
        mul_zero]
  · change Φb (A.epFormsInftySmul β 0 hβ hinv ω) univ = 0
    exact boundaryMeasure_eq_zero_of_integ_eq_zeroI A.zeroFormIntegration hΘ Φb c P hcpt hΦb
      hcovB _ huniv
      fun x' C' _ i B hB => A.zeroFormIntegration_smul_eq_zero hβ hinv ω _ _ fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hyt => Set.disjoint_left.1 hd hyt
          (C'.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
            (C'.boundarySheet_subset i (hB hy.1).1))

/-! ### Theorems 9.5.17 and 9.5.18 for `n = 1` -/

/-- **The boundary measure `ω ↦ μ^{∂Θ̂}_ω` of Theorem 9.5.15 for `n = 1`** (`theorem_9_5_15_dim1`),
on `Ω⁰_{ep,∞}(X)`. -/
def boundaryBranchedMeasureDim1 (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ) :=
  (A.theorem_9_5_15_dim1 hΘ hcpt hT hloc).exists.choose

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449 (2017: Theorem 9.6), for `n = 1`**: `X` with sc-smooth
partitions of unity, `Θ` compact, oriented by `T̂Θ = T`, `1`-dimensional and tame (an oriented
tame structure describing `T̂Θ` at every point of `supp Θ`), `ω ∈ Ω⁰_{ep,∞}(X)`.  Then
`∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for the boundary measure of Theorem 9.5.15 (here `∂S` is a finite set of
oriented points).  No class hypothesis. -/
theorem theorem_9_5_17_dim1 (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω univ := by
  set F := A.epFormsInftyEval (0 + 1) with hF
  have hcov := F.hcov_of_loc hloc
  exact A.stokes_of_boundaryMeasure_dim1
    (branchedMeasure (F.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov)
    (A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc)
    (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹) (fun _ _ => True) hPU hΘ hcpt
    (fun _ _ _ _ _ _ => True.intro)
    (fun x hx => (hloc x hx).imp fun _ h => ⟨h, True.intro⟩)
    (fun η x C hS hCT _ K hK hKU => branchedMeasure_apply (F.sheetIntegration (Nat.succ_pos 0))
      hΘ hcpt hT hcov η C hS hCT hK hKU)
    (fun ω x C hCT hx hS _ K hK hKU =>
      (A.theorem_9_5_15_dim1 hΘ hcpt hT hloc).exists.choose_spec ω x C hCT hx hS K hK hKU) ω

/-- **The effective boundary measure of Theorem 9.5.16 for `n = 1`** (`theorem_9_5_16_dim1`). -/
def boundaryBranchedMeasureEffDim1 (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ) :=
  (A.theorem_9_5_16_dim1 hΘ hcpt hT hloc).exists.choose

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450 (2017: Theorem 9.7), for `n = 1`**:
`∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` with the effective boundary measure of Theorem 9.5.16, when every
point of `supp Θ` has an oriented tame structure describing `T̂Θ` whose `U(x)` has the local
unique continuation property of Definition 7.2.18. -/
theorem theorem_9_5_18_dim1 (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty 0) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ hcpt hT hloc
        (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc ω univ := by
  set F := A.epFormsInftyEval (0 + 1) with hF
  have hcov := F.hcovEff_of_loc hloc
  exact A.stokes_of_boundaryMeasure_dim1
    (branchedMeasureEff (F.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov)
    (A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc)
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) (fun _ C => C.rep.HasLUC) hPU hΘ hcpt
    (fun _ C₀ C hL hU hΦ g V hV hne hVU hid y hy => by
      rw [hΦ] at hid ⊢
      exact hL g V hV hne (hVU.trans hU) hid y (hU hy))
    hloc
    (fun η x C hS hCT hL K hK hKU => branchedMeasureEff_apply
      (F.sheetIntegration (Nat.succ_pos 0)) hΘ hcpt hT hcov η C hS hCT hL hK hKU)
    (fun ω x C hCT hx hS hL K hK hKU =>
      (A.theorem_9_5_16_dim1 hΘ hcpt hT hloc).exists.choose_spec ω x C hCT hx hS hL K hK hKU) ω

end EP

end Polyfold
