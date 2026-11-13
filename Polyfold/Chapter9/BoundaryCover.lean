import Polyfold.Chapter9.CornerFinite
import Polyfold.Chapter9.StokesBoundaryMeasure
import Polyfold.Chapter9.FiniteTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps G.109, G.110).  Numbers and pages are
the 2021 text's.

# The class conditions `hcov`, `hcovS` from the text's hypotheses

Theorems 9.5.15–9.5.18 were formalized (E7, E8) under a class condition: at the points of
`supp(∂Θ)` (resp. `supp Θ`) there are oriented tame structures describing `T̂Θ` whose nonempty
boundary sheets `∂₁Mᵢ` lie in the class `msheets` (and whose sheets lie in one graph chart).
Here the condition is derived from the text's hypotheses: `Θ` compact, branched, of dimension
`m + 1`, oriented and tame in the reading `hloc` (an oriented tame structure describing `T̂Θ` at
every point of `supp Θ`, E4).

* `OrientedTameStructure.exists_restrict_eq`: a structure restricted into an open `W ∋ x`, with
  `Mᵢ' = Mᵢ ∩ U(x)'` (E8's `exists_restrict_subset` with the sheets made explicit).
* `LocalBranchingStructure.isCompact_M_inter`: `Mᵢ ∩ L` is compact for compact `L ⊆ U(x)` (the
  inclusion `Mᵢ → U(x)` is proper).
* **`EP.exists_restrict_boundary_mem_msheets`**: every structure `C₀` at `x` restricts to one with
  sheets in one graph chart and nonempty boundary sheets in `msheets`: shrink `U(x)` into the
  interior of a closed neighbourhood `t ⊆ U(x)`; then `∂₁Mᵢ' ⊆ Mᵢ ∩ t ∩ K` with `K` the compact
  set containing `supp Θ ∩ U(x)` (E4's `exists_isCompact_supp_inter`), and
  `EP.boundaryStratum_inter_mem_msheets` (`CornerFinite`) applies.
* **`EP.hcovS_of_loc`**, `EP.hcovS_of_loc_isLUC`, `EP.hcov_of_loc`, `EP.hcov_of_loc_isLUC`: the
  hypotheses `hcovS` (E8) and `hcov` (E7) from `hloc` (with `X.IsLUC` for the effective forms).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable section

namespace Polyfold

universe u

open MPolyfold

/-- `∂₁(A ∩ V) = ∂₁A ∩ V` for an open `V` (the stratum is read in the tangent spaces, which are
local). -/
theorem MPolyfold.k1_boundaryStratum_inter_isOpen {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} {A V : Set Z} (hV : IsOpen V) :
    P.boundaryStratum (A ∩ V) = P.boundaryStratum A ∩ V := by
  ext y
  constructor
  · rintro ⟨⟨hyA, hyV⟩, h⟩
    exact ⟨⟨hyA, fun c => by rw [← submanifoldTangent_inter_isOpen hV hyV]; exact h c⟩, hyV⟩
  · rintro ⟨⟨hyA, h⟩, hyV⟩
    exact ⟨⟨hyA, hyV⟩, fun c => by rw [submanifoldTangent_inter_isOpen hV hyV]; exact h c⟩

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-- **`Mᵢ ∩ L` is compact** for a compact `L ⊆ U(x)`: `Mᵢ` is closed in `U(x)` (the inclusion is
proper). -/
theorem LocalBranchingStructure.isCompact_M_inter {x : Obj} (B : X.LocalBranchingStructure Θ x)
    (i : B.ι) {L : Set Obj} (hL : IsCompact L) (hLU : L ⊆ B.U) : IsCompact (B.M i ∩ L) := by
  have hcl : IsClosed (range (Set.inclusion (B.subset_U i))) :=
    (B.isProperMap i).isClosedMap.isClosed_range
  obtain ⟨F, hF, hFeq⟩ := isClosed_induced_iff.1 hcl
  have e : B.M i ∩ L = F ∩ L := by
    ext y
    constructor
    · rintro ⟨hyM, hyL⟩
      have : (⟨y, B.subset_U i hyM⟩ : B.U) ∈ range (Set.inclusion (B.subset_U i)) :=
        ⟨⟨y, hyM⟩, rfl⟩
      rw [← hFeq] at this
      exact ⟨this, hyL⟩
    · rintro ⟨hyF, hyL⟩
      have : (⟨y, hLU hyL⟩ : B.U) ∈ Subtype.val ⁻¹' F := hyF
      rw [hFeq] at this
      obtain ⟨⟨z, hz⟩, hzy⟩ := this
      have hzy' : z = y := congrArg Subtype.val hzy
      exact ⟨hzy' ▸ hz, hyL⟩
  rw [e]
  exact hL.inter_left hF

namespace OrientedTameStructure

/-- **A structure restricted into an open `W ∋ x`** (E8's `exists_restrict_subset`, with the
sheets `Mᵢ' = Mᵢ ∩ U(x)'` made explicit and no condition on the sheets). -/
theorem exists_restrict_eq {n : ℕ} {x : Obj} (C₀ : X.OrientedTameStructure n Θ x)
    (hC₀ : C₀.Represents T) {W : Set Obj} (hWo : IsOpen W) (hxW : x ∈ W) :
    ∃ C : X.OrientedTameStructure n Θ x, C.Represents T ∧ C.U ⊆ W ∧ C.U ⊆ C₀.U ∧
      (∀ i, ∃ j, C.M i = C₀.M j ∩ C.U) ∧
      C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ := by
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
  refine ⟨C, fun y hy hys => ?_, fun y hy => (hR'sub hy).1, hsubU, fun i => ⟨i, rfl⟩,
    fun y hy => (hR'sub hy).2, hR'Φ⟩
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

end OrientedTameStructure

end EpGroupoid

/-- **The boundary stratum near a compact part of a tame sheet lies in `msheets`**, for the
forms `Ωᵐ_{ep,∞}(X)` (`A.epFormsInftyEval m`, `m > 0`): `EpGroupoid.FormEval.
boundaryStratum_inter_mem_msheets` with Part I's restriction of the forms to the sheet. -/
theorem EP.boundaryStratum_inter_mem_msheets (A : EP.{u}) {m : ℕ} (hm : 0 < m) {M : Set A.Obj}
    (hM : A.X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : A.X.PObj.HasTameInducedStructure M)
    {V : Set A.Obj} (hV : IsOpen V) {K : Set A.Obj} (hK : IsCompact K) (hKM : K ⊆ M)
    (hNK : A.X.PObj.boundaryStratum M ∩ V ⊆ K)
    (hne : (A.X.PObj.boundaryStratum M ∩ V).Nonempty) :
    A.X.PObj.boundaryStratum M ∩ V ∈ (A.epFormsInftyEval m).msheets := by
  let _ := A.X.PObj.paracompactSpace_subtype M
  let hcs := hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  let _ := (subPolyfold hM.1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold hM.1.isSubMPolyfold).isManifold_cornerChartedSpace hcs
  exact (A.epFormsInftyEval m).boundaryStratum_inter_mem_msheets (hcs := hcs) rfl hM ht
    (fun a => ⟨formsInftyRestrict m hcs (A.epFormsInftyToObj m a),
      (contMDiffForm_formsInftyRestrict (hcs := hcs) rfl (A.epFormsInftyToObj m a)).of_le
        (by simp),
      fun y v => A.formsInftyRestrict_epFormsInftyToObj hm hM.1 a y v⟩) hV hK hKM hNK hne

namespace EP

open EpGroupoid

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Every oriented tame structure restricts to one whose sheets lie in one graph chart and whose
nonempty boundary sheets lie in `msheets`** (`Θ` compact, of dimension `m + 1`, `m > 0`): the
natural action of the restriction is a restriction of the given one (so LUC is kept). -/
theorem exists_restrict_boundary_mem_msheets (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hnd : A.X.IsNDimensional Θ (m + 1)) {x : A.Obj}
    (C₀ : A.X.OrientedTameStructure (m + 1) Θ x) (hC₀ : C₀.Represents T) :
    ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
      C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ := by
  obtain ⟨C₁, hS₁, hC₁, hU₁, hΦ₁⟩ := FormEval.exists_restrict_mem_sheets
    (F := A.epFormsInftyEval (m + 1)) (FormEval.tameOpen A.X) C₀ hC₀
  obtain ⟨K, hK, hUK, -⟩ :=
    exists_isCompact_supp_inter hΘ.isFunctorial hcpt hnd C₁.hasPropernessProperty.2
  obtain ⟨t, htn, htc, htU⟩ := exists_mem_nhds_isClosed_subset (C₁.isOpen_U.mem_nhds C₁.mem_U)
  obtain ⟨C, hCT, hCW, -, hCM, hrepU, hrepΦ⟩ := C₁.exists_restrict_eq hC₁ isOpen_interior
    (mem_interior_iff_mem_nhds.2 htn)
  refine ⟨C, hCT, fun i => ?_, fun i hne => ?_, hrepU.trans hU₁, hrepΦ.trans hΦ₁⟩
  · obtain ⟨j, hj⟩ := hCM i
    rw [hj]
    exact FormEval.inter_mem_sheets (hS₁ j) C.isOpen_U
  · obtain ⟨j, hj⟩ := hCM i
    have hb : C.boundarySheet i = A.X.PObj.boundaryStratum (C₁.M j) ∩ C.U := by
      change A.X.PObj.boundaryStratum (C.M i) = _
      rw [hj, MPolyfold.k1_boundaryStratum_inter_isOpen C.isOpen_U]
    rw [hb] at hne ⊢
    refine A.boundaryStratum_inter_mem_msheets hm (C₁.isSubmanifoldOfDim j)
      (C₁.hasTameInducedStructure j) C.isOpen_U
      (C₁.toLocalBranchingStructure.isCompact_M_inter j (hK.inter_right htc)
        fun y hy => htU hy.2) inter_subset_left ?_ hne
    rintro y ⟨hy, hyU⟩
    have hyM : y ∈ C₁.M j := hy.1
    refine ⟨hyM, hUK ⟨C₁.toLocalBranchingStructure.M_subset_supp j hyM, C₁.subset_U j hyM⟩,
      interior_subset (hCW hyU)⟩

/-- **E8's hypothesis `hcovS` from the text's hypotheses**: for `Θ` compact, branched, oriented
and tame in the reading `hloc` (an oriented tame structure of dimension `m + 1` describing `T̂Θ`
at every point of `supp Θ`), every point of `supp Θ` has a structure describing `T̂Θ` with sheets
in one graph chart and nonempty boundary sheets in `msheets`. -/
theorem hcovS_of_loc (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets :=
  fun x hx => by
    obtain ⟨C₀, hC₀⟩ := hloc x hx
    obtain ⟨C, hCT, hS, hb, -, -⟩ := A.exists_restrict_boundary_mem_msheets hm hΘ hcpt
      (FormEval.isNDimensional_of_loc hloc) C₀ hC₀
    exact ⟨C, hCT, hS, hb⟩

/-- `hcovS` with the property of Definition 7.2.18 on `U(x)`, from `hloc` with that property (it
passes to restrictions with the same action). -/
theorem hcovS_of_loc_hasLUC (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        C.rep.HasLUC :=
  fun x hx => by
    obtain ⟨C₀, hC₀, hL⟩ := hloc x hx
    obtain ⟨C, hCT, hS, hb, hU, hΦ⟩ := A.exists_restrict_boundary_mem_msheets hm hΘ hcpt
      (FormEval.isNDimensional_of_loc hloc) C₀ hC₀
    refine ⟨C, hCT, hS, hb, fun g V hV hne hVU hid y hy => ?_⟩
    rw [hΦ] at hid ⊢
    exact hL g V hV hne (hVU.trans hU) hid y (hU hy)

/-- `hcovS` with LUC on `U(x)`, for an ep-groupoid with the local unique continuation property
(Definition 7.2.18; every natural representation then has the property). -/
theorem hcovS_of_loc_isLUC (hm : 0 < m) (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        C.rep.HasLUC :=
  fun x hx => by
    obtain ⟨C, hCT, hS, hb⟩ := A.hcovS_of_loc hm hΘ hcpt hloc x hx
    exact ⟨C, hCT, hS, hb, A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep⟩

/-- **E7's hypothesis `hcov` from the text's hypotheses** (Theorem 9.5.15): at every point of
`supp(∂Θ)` an oriented tame structure describing `T̂Θ` whose nonempty boundary sheets lie in
`msheets`. -/
theorem hcov_of_loc (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧
        ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets :=
  A.hcovB_of_hcovS (A.hcovS_of_loc hm hΘ hcpt hloc)

/-- E7's hypothesis `hcov` of Theorem 9.5.16 (with LUC on `U(x)`), for an ep-groupoid with the
local unique continuation property. -/
theorem hcov_of_loc_isLUC (hm : 0 < m) (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
          C.rep.HasLUC :=
  fun x hx => by
    obtain ⟨C, hCT, -, hb, hL⟩ :=
      A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc x (A.X.supp_boundaryTheta_subset Θ hx).2
    exact ⟨C, hCT, hb, hL⟩

end EP

end Polyfold
