import Polyfold.Chapter11.GapP2_H4BdGeom
import Polyfold.Chapter11.GapP2_H4Eff

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorems 11.4.4 and 11.4.5** (p. 545, new in the 2021 edition),
gap G.131.  Numbers and pages are the 2021 text's.

# The canonical boundary measures along an equivalence

## The text, paraphrased

(p. 545) "There are versions of Theorem 11.4.1 and Theorem 11.4.2 for the boundary case, which
rely on Theorem 9.5.15 and Theorem 9.5.16."  (Theorem 11.4.4) For a generalized isomorphism
`f : X → Y` and `Θ̂`, `Θ̂'` oriented, tame, compact, of dimension `n`, and forms `ω`, `ω'` of
degree `n - 1`: on `|supp(∂Θ)|`, `µ^{∂Θ̂}_ω = µ^{∂ f_*Θ̂}_{f_*ω} ∘ |f|` and
`µ^{∂ f^*Θ̂'}_{f^*ω'} = µ^{∂Θ̂'}_{ω'} ∘ |f|`.  (Theorem 11.4.5) The same for the effective boundary
measures, for ep-groupoids with the local unique continuation property.

## What is formalized

The measures are E7's (`theorem_9_5_15_msheets`, `theorem_9_5_16_msheets`) for E4's integration
over sheets covered by countably many graph charts, `n = m + 1`:

* `EpGroupoid.boundaryMeasure`, `EpGroupoid.boundaryMeasureEff` (the unique maps of Theorems
  9.5.15, 9.5.16) with their local formulas;
* `|Φ|` maps the sets of measure zero of `∂S` to sets of measure zero, both ways
  (`isMeasureZeroBoundary_image`, `isMeasureZeroBoundary_preimage`), so
  `|Φ| : (∂S, L(∂S)) → (∂S', L(∂S'))` is measurable both ways (`measurable_bsuppMap`,
  `measurable_bsuppInv`);
* the covering hypothesis `hcov` of Theorem 9.5.15 (E7's one added hypothesis: nonempty boundary
  sheets in the class) passes to `Φ^*Θ̂'` and `Φ_*Θ̂` (`hcovB_pull`, `hcovB_push`);
* **`measure_pull_core_bd`**: the gluing argument of Theorem 11.4.1 for any pair of measures with
  the local formulas of Theorem 9.5.15 and normalizations that agree along transport charts;
* **`theorem_11_4_4_pull_equiv`**, **`theorem_11_4_4_push_equiv`**,
  **`theorem_11_4_5_pull_equiv`**, **`theorem_11_4_5_push_equiv`**.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

/-! ### The boundary measures of Theorems 9.5.15 and 9.5.16 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  {m : ℕ}

variable (X) in
/-- **The canonical boundary measures `ω ↦ µ^{∂Θ̂}_ω` of Theorem 9.5.15** (2021 p. 449; 2017:
Theorem 9.4) on `(∂S, L(∂S))`, for E4's integration over sheets covered by countably many graph
charts: the unique linear map of `theorem_9_5_15_msheets`. -/
def boundaryMeasure (F : X.FormEval m Ω) (hm : 0 < m) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1))
    (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) :
    Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
      (X.lebesgueSigmaBoundaryH (m + 1) Θ) :=
  (theorem_9_5_15_msheets F hm hΘ hcpt hnd hT hcov).exists.choose

theorem boundaryMeasure_apply (F : X.FormEval m Ω) (hm : 0 < m)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets)
    (ω : Ω) {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T)
    (hx : x ∈ supp (X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets)
    {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ X.π '' C.U) :
    X.boundaryMeasure F hm hΘ hcpt hnd hT hcov ω K = (Nat.card (X.Isotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum (F.msheetIntegration hm) ω
        (X.π ⁻¹' (Subtype.val '' K)) :=
  (theorem_9_5_15_msheets F hm hΘ hcpt hnd hT hcov).exists.choose_spec ω x C hCT hx hS K hK hKU

variable (X) in
/-- **The effective canonical boundary measures of Theorem 9.5.16** (2021 p. 449; 2017:
Theorem 9.5): the unique linear map of `theorem_9_5_16_msheets`. -/
def boundaryMeasureEff (F : X.FormEval m Ω) (hm : 0 < m) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1))
    (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        C.rep.HasLUC) :
    Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
      (X.lebesgueSigmaBoundaryH (m + 1) Θ) :=
  (theorem_9_5_16_msheets F hm hΘ hcpt hnd hT hcov).exists.choose

theorem boundaryMeasureEff_apply (F : X.FormEval m Ω) (hm : 0 < m)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        C.rep.HasLUC)
    (ω : Ω) {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T)
    (hx : x ∈ supp (X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets)
    (hL : C.rep.HasLUC) {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ X.π '' C.U) :
    X.boundaryMeasureEff F hm hΘ hcpt hnd hT hcov ω K = (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum (F.msheetIntegration hm) ω
        (X.π ⁻¹' (Subtype.val '' K)) :=
  (theorem_9_5_16_msheets F hm hΘ hcpt hnd hT hcov).exists.choose_spec ω x C hCT hx hS hL K hK
    hKU

/-- Under LUC the covering hypothesis of Theorem 9.5.15 gives that of Theorem 9.5.16 (every natural
representation has the property of Definition 7.2.18, `isLUC_iff_forall_naturalRep`). -/
theorem hcovB_addLUC {F : X.FormEval m Ω} (hL : X.IsLUC)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) :
    ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        C.rep.HasLUC := fun x hx => by
  obtain ⟨C, h1, h2⟩ := hcov x hx
  exact ⟨C, h1, h2, X.isLUC_iff_forall_naturalRep.1 hL x C.rep⟩

/-- The covering hypothesis of Theorem 9.5.16 gives that of Theorem 9.5.15. -/
theorem hcovB_dropLUC {F : X.FormEval m Ω}
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        C.rep.HasLUC) :
    ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets :=
  fun x hx => let ⟨C, h1, h2, _⟩ := hcov x hx; ⟨C, h1, h2⟩

namespace OrientedTameStructure

/-- The nonempty boundary sheets of a restricted structure lie in the class if those of the
structure do. -/
theorem boundarySheet_restrictRep_mem_msheets {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x)
    (R : X.NaturalRep x) (hR : R.U ⊆ C.U) {F : X.FormEval m Ω}
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) (i : C.ι)
    (hne : ((C.restrictRep R hR).boundarySheet i).Nonempty) :
    (C.restrictRep R hR).boundarySheet i ∈ F.msheets := by
  rw [boundarySheet_restrictRep] at hne ⊢
  exact FormEval.msheets_inter_isOpen (hS i (hne.mono inter_subset_left)) R.isOpen_U

end OrientedTameStructure

end EpGroupoid

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y} {m : ℕ}
  {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']
  {FX : X.FormEval m Ω} {FY : Y.FormEval m Ω'} {P : Ω' →ₗ[ℝ] Ω}
  {Θ' : Obj' → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ} {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}

open EpGroupoid OrientedTameStructure MPolyfold

/-! ### `|supp ∂(Φ^*Θ')| = |Φ|⁻¹(|supp ∂Θ'|)` -/

theorem mem_supp_boundaryTheta_pull (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    {x : Obj} :
    x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')) ↔ Φ.obj x ∈ supp (Y.boundaryTheta Θ') := by
  rw [← boundaryTheta_pullbackTheta hΦ hΘ' (hasIndependentTangentSums (X := Y) Θ')]
  exact Iff.rfl

theorem orbitSupp_boundaryTheta_pull (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsBranchedEpSubgroupoid Θ') :
    X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ')) =
      Φ.orbitMap ⁻¹' Y.orbitSupp (Y.boundaryTheta Θ') := by
  rw [← boundaryTheta_pullbackTheta hΦ hΘ' (hasIndependentTangentSums (X := Y) Θ')]
  exact orbitSupp_pullbackTheta Φ
    (Y.isFunctorial_boundaryTheta hΘ' (hasIndependentTangentSums (X := Y) Θ'))

/-! ### `|Φ|` between the supports -/

section Supp

variable {ΘX : Obj → ℚ} {ΘY : Obj' → ℚ}

/-- `|Φ|⁻¹ : |supp ΘY| → |supp ΘX|` when `|supp ΘX| = |Φ|⁻¹(|supp ΘY|)`. -/
def bsuppInv (hΦ : Φ.IsEquivalence) (h : X.orbitSupp ΘX = Φ.orbitMap ⁻¹' Y.orbitSupp ΘY) :
    Y.orbitSupp ΘY → X.orbitSupp ΘX :=
  fun q' => ⟨(IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm q'.1, by
    rw [h, mem_preimage]
    have e : Φ.orbitMap ((IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm q'.1) = q'.1 :=
      (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).apply_symm_apply q'.1
    rw [e]; exact q'.2⟩

/-- `|Φ| : |supp ΘX| → |supp ΘY|`. -/
def bsuppMap (h : X.orbitSupp ΘX = Φ.orbitMap ⁻¹' Y.orbitSupp ΘY) :
    X.orbitSupp ΘX → Y.orbitSupp ΘY :=
  fun q => ⟨Φ.orbitMap q.1, (show q.1 ∈ Φ.orbitMap ⁻¹' Y.orbitSupp ΘY from h ▸ q.2)⟩

variable (hΦ : Φ.IsEquivalence) (h : X.orbitSupp ΘX = Φ.orbitMap ⁻¹' Y.orbitSupp ΘY)

theorem orbitMap_bsuppInv (q' : Y.orbitSupp ΘY) : Φ.orbitMap (bsuppInv hΦ h q').1 = q'.1 :=
  (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).apply_symm_apply q'.1

theorem preimage_bsuppInv (K : Set (X.orbitSupp ΘX)) :
    bsuppInv hΦ h ⁻¹' K = Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) := by
  ext q'
  constructor
  · intro hq
    exact ⟨_, ⟨_, hq, rfl⟩, orbitMap_bsuppInv hΦ h q'⟩
  · rintro ⟨p, ⟨q, hq, rfl⟩, he⟩
    have e : bsuppInv hΦ h q' = q := by
      apply Subtype.ext
      exact (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm_apply_eq.2 he.symm
    rw [mem_preimage, e]
    exact hq

theorem preimage_bsuppMap (t : Set (Y.orbitSupp ΘY)) :
    Subtype.val '' (bsuppMap h ⁻¹' t) = Φ.orbitMap ⁻¹' (Subtype.val '' t) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, hq, rfl⟩
  · rintro ⟨q', hq', he⟩
    have hp : p ∈ X.orbitSupp ΘX := by rw [h, mem_preimage, ← he]; exact q'.2
    refine ⟨⟨p, hp⟩, ?_, rfl⟩
    change (⟨Φ.orbitMap p, _⟩ : Y.orbitSupp ΘY) ∈ t
    convert hq' using 1
    exact Subtype.ext he.symm

theorem continuous_bsuppInv : Continuous (bsuppInv hΦ h) :=
  ((IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

include h in
theorem continuous_bsuppMap : Continuous (bsuppMap h) :=
  (Φ.continuous_orbitMap.comp continuous_subtype_val).subtype_mk _

end Supp

/-! ### `|Φ|` and the sets of measure zero of `∂S` -/

/-- **`|Φ|` maps the subsets of `∂S` of measure zero to subsets of `∂S'` of measure zero** (2021
p. 448). -/
theorem isMeasureZeroBoundary_image (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcovX : ∀ x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')),
      Nonempty (X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x))
    {N : Set X.OrbitSpace}
    (hN : X.IsMeasureZeroBoundary (X.PObj.boundaryNullSets (m + 1)) (Φ.pullbackTheta Θ') N) :
    Y.IsMeasureZeroBoundary (Y.PObj.boundaryNullSets (m + 1)) Θ' (Φ.orbitMap '' N) := by
  have hall := isMeasureZeroBoundaryAll_of _ (hasIndependentTangentSums (X := X) _) hN
  intro y hy
  obtain ⟨x, hx, ⟨Tc⟩⟩ := exists_transportChart_of_mem_supp hΦ
    (Y.isFunctorial_boundaryTheta hΘ' (hasIndependentTangentSums (X := Y) Θ')) hy
  have hx' : x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')) :=
    (mem_supp_boundaryTheta_pull hΦ hΘ').2 hx
  obtain ⟨C⟩ := hcovX x hx'
  obtain ⟨V', hyV', hV'P⟩ := Y.exists_hasPropernessProperty y
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push hΦ C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  set C₁ := C.restrictRep R hRU
  have hP' : Y.HasPropernessProperty (Tc.Q '' C₁.U) := hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  have hΘQ := Tc.pullbackTheta_Q hΘ'.isFunctorial
  set C₂ := C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'
  refine ⟨C₂.toTameBranchingStructure, fun i => submanifoldBoundary_mem_tameBoundaries
    (C₂.isSubmanifoldOfDim i) (C₂.hasTameInducedStructure i), fun i => ?_⟩
  have h1 := hall x hx' C₁.toLocalBranchingStructure (fun j =>
    submanifoldBoundary_mem_tameBoundaries (C₁.isSubmanifoldOfDim j)
      (C₁.hasTameInducedStructure j)) i
  rw [boundaryNullSets_isNull_iff] at h1 ⊢
  have hMW : C₁.M i ⊆ Tc.W := C₁.M_subset_W hRW i
  have h2 := h1.image_of_isScDiffeoOn_cross Tc.isScDiffeoOn_Q
    (fun u hu => hMW (by obtain ⟨-, h, -⟩ := hu.2; exact h))
  refine h2.mono ?_
  rintro z ⟨⟨hzb, hzN⟩, -⟩
  change z ∈ Y.PObj.submanifoldBoundary (Tc.Q '' (C₁.M i ∩ Tc.W)) at hzb
  rw [inter_eq_left.2 hMW] at hzb
  have hzM : z ∈ Tc.Q '' C₁.M i := by obtain ⟨-, h, -⟩ := hzb; exact h
  obtain ⟨u, hu, rfl⟩ := hzM
  have hub := (mem_submanifoldBoundary_image_iff_of_isScDiffeoOn Tc.isScDiffeoOn_Q
    (C₁.isSmoothSubmanifold i) hMW (hMW hu)).1 hzb
  refine mem_image_of_mem _ ⟨⟨hub, ?_⟩, hub⟩
  obtain ⟨q, hq, he⟩ := hzN
  rw [Tc.π_Q (hMW hu), ← Φ.orbitMap_π] at he
  rw [mem_preimage, ← Φ.injective_orbitMap_of_full hΦ.full he]
  exact hq

/-- **`|Φ|⁻¹` maps the subsets of `∂S'` of measure zero to subsets of `∂S` of measure zero.** -/
theorem isMeasureZeroBoundary_preimage (hΦ : Φ.IsEquivalence)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcovY : ∀ y ∈ supp (Y.boundaryTheta Θ'), Nonempty (Y.OrientedTameStructure (m + 1) Θ' y))
    {N' : Set Y.OrbitSpace}
    (hN : Y.IsMeasureZeroBoundary (Y.PObj.boundaryNullSets (m + 1)) Θ' N') :
    X.IsMeasureZeroBoundary (X.PObj.boundaryNullSets (m + 1)) (Φ.pullbackTheta Θ')
      (Φ.orbitMap ⁻¹' N') := by
  have hall := isMeasureZeroBoundaryAll_of _ (hasIndependentTangentSums (X := Y) Θ') hN
  intro x hx
  have hx' := (mem_supp_boundaryTheta_pull hΦ hΘ').1 hx
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  obtain ⟨D⟩ := hcovY _ hx'
  obtain ⟨R, R', h1, h2, h3, h4⟩ := exists_pullData hΦ Tc D
  have hΘQ := Tc.pullbackTheta_Q hΘ'.isFunctorial
  set D₁ := D.restrictRep R' h1
  set C := pullStructure Tc hΘQ D R R' h1 h2 h3 h4
  refine ⟨C.toTameBranchingStructure, fun i => submanifoldBoundary_mem_tameBoundaries
    (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i), fun i => ?_⟩
  have g1 := hall _ hx' D₁.toLocalBranchingStructure (fun j =>
    submanifoldBoundary_mem_tameBoundaries (D₁.isSubmanifoldOfDim j)
      (D₁.hasTameInducedStructure j)) i
  rw [boundaryNullSets_isNull_iff] at g1 ⊢
  have hW' : D₁.M i ⊆ Tc.W' := fun z hz =>
    restrictRep_U_subset_W' Tc D R R' h1 h2 h3 (D₁.subset_U i hz)
  have g2 := g1.image_of_isScDiffeoOn_cross Tc.isScDiffeoOn_Q.symm
    (fun z hz => hW' (by obtain ⟨-, h, -⟩ := hz.2; exact h))
  refine g2.mono ?_
  rintro u ⟨⟨hub, huN⟩, -⟩
  change u ∈ X.PObj.submanifoldBoundary (Tc.Qinv '' (D₁.M i ∩ Tc.W')) at hub
  rw [inter_eq_left.2 hW'] at hub
  have huM : u ∈ Tc.Qinv '' D₁.M i := by obtain ⟨-, h, -⟩ := hub; exact h
  obtain ⟨z, hz, rfl⟩ := huM
  have hzb := (mem_submanifoldBoundary_image_iff_of_isScDiffeoOn Tc.isScDiffeoOn_Q.symm
    (D₁.isSmoothSubmanifold i) hW' (hW' hz)).1 hub
  refine mem_image_of_mem _ ⟨⟨hzb, ?_⟩, hzb⟩
  have hzW' := hW' hz
  have hgz := Tc.isScDiffeoOn_Q.mapsTo_inv hzW'
  rw [mem_preimage, mem_preimage, Φ.orbitMap_π, ← Tc.π_Q hgz,
    Tc.isScDiffeoOn_Q.right_inv z hzW'] at huN
  exact huN

/-- **`|Φ|⁻¹ : ∂S' → ∂S` is measurable for the σ-algebras `L(∂S')`, `L(∂S)`** (Definition
9.5.14): `|Φ|` maps `L(∂S)` into `L(∂S')`. -/
theorem measurable_bsuppInv (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcovX : ∀ x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')),
      Nonempty (X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x)) :
    @Measurable _ _ (Y.lebesgueSigmaBoundaryH (m + 1) Θ')
      (X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ'))
      (bsuppInv hΦ (orbitSupp_boundaryTheta_pull hΦ hΘ')) := by
  let _ : MeasurableSpace (Y.orbitSupp (Y.boundaryTheta Θ')) :=
    Y.lebesgueSigmaBoundaryH (m + 1) Θ'
  refine measurable_generateFrom fun t ht => ?_
  rcases ht with ht | ht
  · exact borel_le_borelNullSigma _ _ ((continuous_bsuppInv hΦ _).borel_measurable ht)
  · refine measurableSet_borelNullSigma_of_mem ?_
    change Y.IsMeasureZeroBoundary _ _ _
    rw [preimage_bsuppInv, val_image_preimage (orbitSupp_boundaryTheta_pull hΦ hΘ').subset]
    exact isMeasureZeroBoundary_image hΦ hΘ' hcovX ht

/-- **`|Φ| : ∂S → ∂S'` is measurable for the σ-algebras `L(∂S)`, `L(∂S')`.** -/
theorem measurable_bsuppMap (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcovY : ∀ y ∈ supp (Y.boundaryTheta Θ'), Nonempty (Y.OrientedTameStructure (m + 1) Θ' y)) :
    @Measurable _ _ (X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ'))
      (Y.lebesgueSigmaBoundaryH (m + 1) Θ')
      (bsuppMap (orbitSupp_boundaryTheta_pull hΦ hΘ')) := by
  let _ : MeasurableSpace (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ')
  refine measurable_generateFrom fun t ht => ?_
  rcases ht with ht | ht
  · exact borel_le_borelNullSigma _ _ ((continuous_bsuppMap _).borel_measurable ht)
  · refine measurableSet_borelNullSigma_of_mem ?_
    change X.IsMeasureZeroBoundary _ _ _
    rw [preimage_bsuppMap]
    exact isMeasureZeroBoundary_preimage hΦ hΘ' hcovY ht

/-! ### The pulled-back structures at the points of `supp ∂(Φ^*Θ')` -/

/-- **The pulled-back structures for the boundary**: a structure at `y ∈ supp(∂Θ')` with nonempty
boundary sheets in the class, restricted to `Q(U(x))` and moved to `x ∈ supp ∂(Φ^*Θ')`. -/
def IsBPulled (FY : Y.FormEval m Ω') (Φ : EpFunctor X Y) (hΘ' : Y.IsFunctorial Θ')
    (T' : Obj' → Y.PObj.OrTangent →₀ ℚ) {x : Obj}
    (C : X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x) : Prop :=
  ∃ (y : Obj') (Tc : Φ.TransportChart x y) (D : Y.OrientedTameStructure (m + 1) Θ' y)
    (_ : x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')))
    (_ : y ∈ supp (Y.boundaryTheta Θ')) (_ : D.Represents T')
    (_ : ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets)
    (R : X.NaturalRep x) (R' : Y.NaturalRep y)
    (h1 : R'.U ⊆ D.U) (h2 : R.U ⊆ Tc.W) (h3 : R'.U = Tc.Q '' R.U)
    (h4 : X.HasPropernessProperty R.U),
    C = pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 h2 h3 h4

/-- Every point of `supp ∂(Φ^*Θ')` carries a pulled-back structure. -/
theorem exists_isBPulled (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcov' : ∀ y ∈ supp (Y.boundaryTheta Θ'), ∃ D : Y.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets)
    {x : Obj} (hx : x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ'))) :
    ∃ C : X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x,
      IsBPulled FY Φ hΘ'.isFunctorial T' C := by
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  have hx' := (mem_supp_boundaryTheta_pull hΦ hΘ').1 hx
  obtain ⟨D, hDT, hDS⟩ := hcov' _ hx'
  obtain ⟨R, R', h1, h2, h3, h4⟩ := exists_pullData hΦ Tc D
  exact ⟨_, _, Tc, D, hx, hx', hDT, hDS, R, R', h1, h2, h3, h4, rfl⟩

theorem IsBPulled.mem_msheets (hP : FX.IsPullback FY Φ P) {hΘ' : Y.IsFunctorial Θ'} {x : Obj}
    {C : X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x}
    (hC : IsBPulled FY Φ hΘ' T' C) :
    ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets := by
  obtain ⟨y, Tc, D, -, -, -, hDS, R, R', h1, h2, h3, h4, rfl⟩ := hC
  have hW' : ∀ i, (D.restrictRep R' h1).boundarySheet i ⊆ Tc.W' := fun i z hz =>
    restrictRep_U_subset_W' Tc D R R' h1 h2 h3
      ((D.restrictRep R' h1).subset_U i ((D.restrictRep R' h1).boundarySheet_subset i hz))
  exact (D.restrictRep R' h1).boundarySheet_move_mem_msheets Tc.isScDiffeoOn_Q.symm _ _ _ R _ _
    (D.boundarySheet_restrictRep_mem_msheets R' h1 hDS) (fun i ωT => by
      obtain ⟨ω', rfl⟩ := hP.surjective ωT
      exact ⟨ω', Tc.evCompatOn_Qinv hP ω'
        ((D.restrictRep R' h1).isSubmanifoldOfDim_boundarySheet i).1 (hW' i)⟩)

theorem IsBPulled.represents (hΦ : Φ.IsEquivalence) {hΘ' : Y.IsFunctorial Θ'} {x : Obj}
    (hT : X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    {C : X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x}
    (hC : IsBPulled FY Φ hΘ' T' C) : C.Represents T := by
  obtain ⟨y, Tc, D, -, -, hDT, -, R, R', h1, h2, h3, h4, rfl⟩ := hC
  exact represents_pullStructure Tc _ D R R' h1 h2 h3 h4 hΦ hT (hTT Tc) hDT

/-- **The covering hypothesis of Theorem 9.5.15 for `Φ^*Θ̂'`**: E7's `hcov` passes from `Θ̂'` to
`Φ^*Θ̂'`. -/
theorem hcovB_pull (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hT : X.IsGrHatSection T)
    (hTT : Φ.IsTransported T T')
    (hcov' : ∀ y ∈ supp (Y.boundaryTheta Θ'), ∃ D : Y.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets) :
    ∀ x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')),
      ∃ C : X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x,
        C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets :=
  fun x hx => by
    obtain ⟨C, hC⟩ := exists_isBPulled hΦ hΘ' hcov' hx
    exact ⟨C, hC.represents hΦ hT hTT, hC.mem_msheets hP⟩

/-- **The covering hypothesis of Theorem 9.5.15 for `Φ_*Θ̂`**: E7's `hcov` passes from `Θ̂` to
`Φ_*Θ̂`. -/
theorem hcovB_push (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) {Θ : Obj → ℚ}
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets) :
    ∀ y ∈ supp (Y.boundaryTheta (Φ.pushforwardTheta Θ)),
      ∃ D : Y.OrientedTameStructure (m + 1) (Φ.pushforwardTheta Θ) y,
        D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets :=
  fun y hy => by
    have hΘ'' := isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ
    have he := pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial
    obtain ⟨x, hx, ⟨Tc⟩⟩ := exists_transportChart_of_mem_supp hΦ
      (Y.isFunctorial_boundaryTheta hΘ'' (hasIndependentTangentSums (X := Y) _)) hy
    have hx' := (mem_supp_boundaryTheta_pull hΦ hΘ'').2 hx
    rw [he] at hx'
    obtain ⟨C, hCT, hCS⟩ := hcov x hx'
    have hΘQ : ∀ u ∈ Tc.W, Φ.pushforwardTheta Θ (Tc.Q u) = Θ u := fun u hu => by
      rw [Tc.pullbackTheta_Q hΘ''.isFunctorial u hu, he]
    obtain ⟨V', hyV', hV'P⟩ := Y.exists_hasPropernessProperty y
    obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push hΦ C.rep hV'P.1 hyV'
    have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
    set C₁ := C.restrictRep R hRU
    have hP' : Y.HasPropernessProperty (Tc.Q '' C₁.U) := hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
    refine ⟨C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP', ?_, ?_⟩
    · refine C₁.represents_move _ _ _ _ _ _ _ (C.represents_restrictRep R hRU hCT) ?_
      rintro _ ⟨u, hu, rfl⟩ hzs
      have huW := hRW hu
      have hus := (Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj huW).1 hzs
      rw [Tc.isScDiffeoOn_Q.left_inv u huW]
      exact ⟨hus, hTT Tc u huW hus⟩
    · exact C₁.boundarySheet_move_mem_msheets Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'
        (C.boundarySheet_restrictRep_mem_msheets R hRU hCS) fun i ω' =>
          ⟨P ω', Tc.evCompatOn_Q hP ω' (C₁.isSubmanifoldOfDim_boundarySheet i).1
            (C₁.boundarySheet_subset_W hRW i)⟩

/-! ### The gluing -/

/-- **The core of Theorems 11.4.4 and 11.4.5** for an equivalence `Φ`, `Θ = Φ^*Θ'`, `T̂'` the
orientation `T̂` moved by the transport charts, the pull-back `P` of the forms: two signed measures
`µ₁` on `(∂S, L(∂S))` and `µ'` on `(∂S', L(∂S'))` given by the local formulas of Theorem 9.5.15
with normalizations `c`, `c'` that agree along transport charts satisfy
`µ₁(K) = µ'(|Φ|(K))`, and `|Φ|(K) ∈ L(∂S')`. -/
theorem measure_pull_core_bd (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) (hm : 0 < m)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hnd' : Y.IsNDimensional Θ' (m + 1))
    (hcov' : ∀ y ∈ supp (Y.boundaryTheta Θ'), ∃ D : Y.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets)
    {Θ : Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (c : Obj → ℝ) (c' : Obj' → ℝ)
    (hc : ∀ {x : Obj} {y : Obj'} (Tc : Φ.TransportChart x y) (R : X.NaturalRep x)
      (R' : Y.NaturalRep y), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → c x = c' y)
    (ω' : Ω')
    (μ₁ : @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ)) (X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (μ' : @SignedMeasure (Y.orbitSupp (Y.boundaryTheta Θ'))
      (Y.lebesgueSigmaBoundaryH (m + 1) Θ'))
    (hμ₁ : ∀ (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
      x ∈ supp (X.boundaryTheta Θ) →
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets) →
      ∀ K, MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
        Subtype.val '' K ⊆ X.π '' C.U →
        μ₁ K = c x * (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum (FX.msheetIntegration hm)
          (P ω') (X.π ⁻¹' (Subtype.val '' K)))
    (hμ' : ∀ (y : Obj') (D : Y.OrientedTameStructure (m + 1) Θ' y) (hDT : D.Represents T'),
      y ∈ supp (Y.boundaryTheta Θ') →
      (∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets) →
      ∀ K, MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) Θ'] K →
        Subtype.val '' K ⊆ Y.π '' D.U →
        μ' K = c' y * (D.boundaryFamily hΘ' hDT).nonemptyPart.sheetSum
          (FY.msheetIntegration hm) ω' (Y.π ⁻¹' (Subtype.val '' K)))
    {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      μ₁ K = μ' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hΘeq
  have hΘf := hΘ'.isFunctorial
  have hsupp := orbitSupp_boundaryTheta_pull hΦ hΘ'
  have hcovX : ∀ x ∈ supp (X.boundaryTheta (Φ.pullbackTheta Θ')),
      Nonempty (X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x) := fun x hx => by
    obtain ⟨C, -⟩ := exists_isBPulled hΦ hΘ' hcov' hx
    exact ⟨C⟩
  have hm' := measurable_bsuppInv hΦ hΘ' hcovX
  have hmeas : ∀ K : Set (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))),
      MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ')] K →
      MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [← preimage_bsuppInv hΦ hsupp K]; exact hm' hK
  refine ⟨hmeas K hK, ?_⟩
  let _ : MeasurableSpace (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ')
  let _ : MeasurableSpace (Y.orbitSupp (Y.boundaryTheta Θ')) :=
    Y.lebesgueSigmaBoundaryH (m + 1) Θ'
  have : CompactSpace (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    isCompact_iff_compactSpace.1
      (isCompact_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums (X := X) _) hcpt)
  set μ₂ : SignedMeasure (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    μ'.map (bsuppInv hΦ hsupp)
  have hμ₂ : ∀ K, MeasurableSet K →
      μ₂ K = μ' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [VectorMeasure.map_apply _ hm' hK, preimage_bsuppInv]
  -- the local agreement on a pulled-back structure
  have hloc : ∀ {x : Obj} (C : X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x),
      IsBPulled FY Φ hΘf T' C → ∀ K, MeasurableSet K → Subtype.val '' K ⊆ X.π '' C.U →
      μ₂ K = μ₁ K := by
    intro x C hC K hK hKU
    have hS := hC.mem_msheets hP
    have hR := hC.represents hΦ hT.isGrHatSection hTT
    obtain ⟨y, Tc, D, hx, hy, hDT, hDS, R, R', h1, h2, h3, h4, rfl⟩ := hC
    set D₁ := D.restrictRep R' h1
    have hval := val_image_preimage hsupp.subset K
    have hD₁S := D.boundarySheet_restrictRep_mem_msheets R' h1 hDS
    have hD₁T := D.represents_restrictRep R' h1 hDT
    have hK' := hmeas K hK
    have hKU' : Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
        Set (Y.orbitSupp (Y.boundaryTheta Θ'))) ⊆ Y.π '' D₁.U := by
      rw [hval, restrictRep_U, h3]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨u, hu, hπ⟩ := hKU hp
      rw [pullStructure_U] at hu
      exact ⟨Tc.Q u, mem_image_of_mem _ hu, by rw [Tc.π_Q (h2 hu), ← Φ.orbitMap_π, hπ]⟩
    have hW' : ∀ {z}, z ∈ D₁.U → z ∈ Tc.W' := fun hz =>
      restrictRep_U_subset_W' Tc D R R' h1 h2 h3 hz
    have hbW' : ∀ i, D₁.boundarySheet i ⊆ Tc.W' := fun i z hz =>
      hW' (D₁.subset_U i (D₁.boundarySheet_subset i hz))
    have hA : ∀ i, FY.sheetNull.IsMeasIn (D₁.boundarySheet i)
        (Y.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
          Set (Y.orbitSupp (Y.boundaryTheta Θ'))))) := fun i =>
      D₁.isMeasIn_boundarySheet (G := FY.msheetNull) (fun _ _ => Iff.rfl) hnd' hy i hK'
    have hB : ∀ i, X.π ⁻¹' (Subtype.val '' K) ∩ Tc.Qinv '' D₁.boundarySheet i =
        Tc.Qinv '' (Y.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
          Set (Y.orbitSupp (Y.boundaryTheta Θ')))) ∩ D₁.boundarySheet i) := by
      intro i
      ext u
      constructor
      · rintro ⟨hu, z, hz, rfl⟩
        have hzW' := hbW' i hz
        refine ⟨z, ⟨?_, hz⟩, rfl⟩
        rw [mem_preimage, hval]
        refine ⟨_, hu, ?_⟩
        rw [Φ.orbitMap_π, ← Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          Tc.isScDiffeoOn_Q.right_inv z hzW']
      · rintro ⟨z, ⟨hzA, hz⟩, rfl⟩
        have hzW' := hbW' i hz
        refine ⟨?_, z, hz, rfl⟩
        rw [mem_preimage, hval] at hzA
        obtain ⟨p, hp, he⟩ := hzA
        rw [← Tc.isScDiffeoOn_Q.right_inv z hzW', Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          ← Φ.orbitMap_π] at he
        rw [mem_preimage, ← Φ.injective_orbitMap_of_full hΦ.full he]
        exact hp
    have e := D₁.boundarySheetSum_move (FS := FY) (FT := FX) hm Tc.isScDiffeoOn_Q.symm _ _ _ R
      _ _ hΘ' hD₁T hΘ hR hD₁S hS
      (fun i => Tc.evCompatOn_Qinv hP ω' (D₁.isSubmanifoldOfDim_boundarySheet i).1 (hbW' i))
      hA hB
    rw [hμ₂ K hK, hμ' y D₁ hD₁T hy hD₁S _ hK' hKU', hμ₁ x _ hR hx hS K hK hKU,
      hc Tc R R' h2 h3]
    exact congrArg _ e.symm
  -- gluing over the pulled-back structures
  let J := {j : Σ x, X.OrientedTameStructure (m + 1) (Φ.pullbackTheta Θ') x //
    IsBPulled FY Φ hΘf T' j.2}
  let O : J → Set (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨x, hx, hxq⟩ := q.2
    obtain ⟨C, hC⟩ := exists_isBPulled hΦ hΘ' hcov' hx
    exact mem_iUnion.2 ⟨⟨⟨x, C⟩, hC⟩, x, C.mem_U, hxq⟩
  obtain ⟨Ψ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    (borel_le_borelNullSigma _) O hO hcovO (fun _ => LinearMap.toSpanSingleton ℝ _ μ₁)
    (fun _ _ _ _ _ _ => rfl)
  have e1 := huniq (LinearMap.toSpanSingleton ℝ _ μ₁) fun _ _ _ _ _ => rfl
  have e2 := huniq (LinearMap.toSpanSingleton ℝ _ μ₂) fun j t K hK hKO => by
    change (t • μ₂) K = (t • μ₁) K
    change t • μ₂ K = t • μ₁ K
    rw [hloc j.1.2 j.2 K hK (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq)]
  have e3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure
      (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ'))) => L 1) (e2.trans e1.symm)
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at e3
  rw [← hμ₂ K hK, e3]

/-! ### Theorems 11.4.4 and 11.4.5 for an equivalence -/

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), second identity, for an equivalence
`Φ : X → Y`**: for `Θ̂'` on `Y` oriented, tame (nonempty boundary sheets in the class, E7's `hcov`),
compact, of dimension `m + 1`, a form `ω'` of degree `m`, and `K ∈ L(|supp ∂(Φ^*Θ')|)`:
`|Φ|(K) ∈ L(|supp ∂Θ'|)` and `µ^{∂Φ^*Θ̂'}_{Φ^*ω'}(K) = µ^{∂Θ̂'}_{ω'}(|Φ|(K))`. -/
theorem theorem_11_4_4_pull_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hm : 0 < m) (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hnd' : Y.IsNDimensional Θ' (m + 1)) (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.boundaryTheta Θ'), ∃ D : Y.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets)
    (ω' : Ω') {K : Set (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ')))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryMeasure FX hm (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isNDimensional_pullbackTheta hΦ hnd')
        (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y) Θ') hT')
        (hcovB_pull hΦ hP hΘ'
          (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y) Θ') hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hcov') (P ω') K =
        Y.boundaryMeasure FY hm hΘ' hcpt' hnd' hT' hcov' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) :=
  measure_pull_core_bd hΦ hP hm hΘ' hnd' hcov' rfl (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y) Θ') hT')
    (isTransported_pull hΦ hT'.isGrHatSection) (fun x => (Nat.card (X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) ω' _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ C hCT hx hS hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ D hDT hy hS hK hKU) hK

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), first identity, for an equivalence
`Φ : X → Y`**: for `Θ̂` on `X` oriented, tame (E7's `hcov`), compact, of dimension `m + 1`,
`K ∈ L(|supp ∂Θ|)` and `Φ_*ω = ω'` (the form with `Φ^*ω' = ω`): `|Φ|(K) ∈ L(|supp ∂Φ_*Θ|)` and
`µ^{∂Θ̂}_ω(K) = µ^{∂Φ_*Θ̂}_{Φ_*ω}(|Φ|(K))`. -/
theorem theorem_11_4_4_push_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hm : 0 < m) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets)
    {ω : Ω} {ω' : Ω'} (hω : P ω' = ω) {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) (Φ.pushforwardTheta Θ)]
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryMeasure FX hm hΘ hcpt hnd hT hcov ω K =
        Y.boundaryMeasure FY hm (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
          (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
          (isNDimensional_pushforwardTheta hΦ hΘ.isFunctorial hnd)
          (isOrientation_pushSection hΦ hΘ (hasIndependentTangentSums (X := X) Θ) hT)
          (hcovB_push hΦ hP hΘ (isTransported_push hΦ hT.isGrHatSection) hcov) ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hω
  exact measure_pull_core_bd hΦ hP hm (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
    (isNDimensional_pushforwardTheta hΦ hΘ.isFunctorial hnd)
    (hcovB_push hΦ hP hΘ (isTransported_push hΦ hT.isGrHatSection) hcov)
    (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)
    hΘ hcpt hT (isTransported_push hΦ hT.isGrHatSection) (fun x => (Nat.card (X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) ω' _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ C hCT hx hS hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasure_apply _ _ _ _ _ _ _ _ D hDT hy hS hK hKU) hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), second identity, for an equivalence
`Φ : X → Y` between ep-groupoids with the local unique continuation property**: as
`theorem_11_4_4_pull_equiv` for the effective boundary measures of Theorem 9.5.16. -/
theorem theorem_11_4_5_pull_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hm : 0 < m) (hLY : Y.IsLUC) (hΘ' : Y.IsBranchedEpSubgroupoid Θ')
    (hcpt' : Y.IsCompactBranched Θ') (hnd' : Y.IsNDimensional Θ' (m + 1))
    (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp (Y.boundaryTheta Θ'), ∃ D : Y.OrientedTameStructure (m + 1) Θ' y,
      D.Represents T' ∧ (∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ FY.msheets) ∧
        D.rep.HasLUC)
    (ω' : Ω') {K : Set (X.orbitSupp (X.boundaryTheta (Φ.pullbackTheta Θ')))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryMeasureEff FX hm (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isNDimensional_pullbackTheta hΦ hnd')
        (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y) Θ') hT')
        (hcovB_addLUC ((proposition_10_1_16 hΦ).2 hLY) (hcovB_pull hΦ hP hΘ'
          (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y) Θ') hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) (hcovB_dropLUC hcov'))) (P ω') K =
        Y.boundaryMeasureEff FY hm hΘ' hcpt' hnd' hT' hcov' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  have hLX := (proposition_10_1_16 hΦ).2 hLY
  exact measure_pull_core_bd hΦ hP hm hΘ' hnd' (hcovB_dropLUC hcov') rfl
    (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := Y) Θ') hT')
    (isTransported_pull hΦ hT'.isGrHatSection) (fun x => (Nat.card (X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (Y.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (X.isLUC_iff_forall_naturalRep.1 hLX _ R)
        (Y.isLUC_iff_forall_naturalRep.1 hLY _ R'))) ω' _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ C hCT hx hS
      (X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ D hDT hy hS
      (Y.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) hK hKU) hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), first identity, for an equivalence
`Φ : X → Y` between ep-groupoids with the local unique continuation property**: as
`theorem_11_4_4_push_equiv` for the effective boundary measures of Theorem 9.5.16. -/
theorem theorem_11_4_5_push_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hm : 0 < m) (hLX : X.IsLUC) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ FX.msheets) ∧
        C.rep.HasLUC)
    {ω : Ω} {ω' : Ω'} (hω : P ω' = ω) {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.lebesgueSigmaBoundaryH (m + 1) (Φ.pushforwardTheta Θ)]
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      X.boundaryMeasureEff FX hm hΘ hcpt hnd hT hcov ω K =
        Y.boundaryMeasureEff FY hm (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
          (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
          (isNDimensional_pushforwardTheta hΦ hΘ.isFunctorial hnd)
          (isOrientation_pushSection hΦ hΘ (hasIndependentTangentSums (X := X) Θ) hT)
          (hcovB_addLUC ((proposition_10_1_16 hΦ).1 hLX)
            (hcovB_push hΦ hP hΘ (isTransported_push hΦ hT.isGrHatSection) (hcovB_dropLUC hcov)))
          ω' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hω
  have hLY := (proposition_10_1_16 hΦ).1 hLX
  exact measure_pull_core_bd hΦ hP hm (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
    (isNDimensional_pushforwardTheta hΦ hΘ.isFunctorial hnd)
    (hcovB_push hΦ hP hΘ (isTransported_push hΦ hT.isGrHatSection) (hcovB_dropLUC hcov))
    (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)
    hΘ hcpt hT (isTransported_push hΦ hT.isGrHatSection)
    (fun x => (Nat.card (X.EffIsotropy x) : ℝ)⁻¹) (fun y => (Nat.card (Y.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (X.isLUC_iff_forall_naturalRep.1 hLX _ R)
        (Y.isLUC_iff_forall_naturalRep.1 hLY _ R'))) ω' _ _
    (fun _ C hCT hx hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ C hCT hx hS
      (X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) hK hKU)
    (fun _ D hDT hy hS _ hK hKU => boundaryMeasureEff_apply _ _ _ _ _ _ _ _ D hDT hy hS
      (Y.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) hK hKU) hK

end EpFunctor

end Polyfold
