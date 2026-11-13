import Polyfold.Chapter9.GapP2_E4_FiniteDominated
import Polyfold.Chapter9.GapP2_E4_MultiChartTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.4 and 9.5.5** (p. 438; 2017: Theorems 9.2, 9.3), gap
G.107.  Numbers and pages are the 2021 text's.

# Theorems 9.5.4 and 9.5.5 for every oriented tame structure

`theorem_9_5_4_multi` (`GapP2_E4_MultiChartTheorem.lean`) characterizes `ω ↦ μ_ω` by the local
formula for the oriented tame structures whose sheets lie in the class `F.msheets` (countably
many graph charts, `∫_{Mᵢ} |ω| < ∞`).  Here this class condition is shown to hold for every
oriented tame structure of a compact `n`-dimensional branched ep⁺-subgroupoid, so the local
formula holds for every structure describing `T̂Θ`, as the text states it.

* `exists_isCompact_supp_inter`: for `Θ` compact and `n`-dimensional and an open `U` whose
  closure is a proper set (Definition 7.5.8), `supp Θ ∩ U` lies in a compact subset of `supp Θ`.
  (`supp Θ` is locally compact, being locally a finite union of finite-dimensional
  submanifolds; a compact `K' ⊆ supp Θ` meets every orbit of `supp Θ` since `|supp Θ|` is
  compact; and `supp Θ ∩ U ⊆ s({φ | s(φ) ∈ cl U, t(φ) ∈ K'})`, compact by the properness of
  `cl U`.)
* `msheets_of_subset_isCompact`: an `n`-dimensional submanifold in a compact subset of `supp Θ`
  is covered by finitely many one-chart sheets of local branching structures at points of the
  compact set, hence lies in `F.msheets` (`msheets_of_list`).
* `msheets_of_orientedTameStructure`: the sheets `Mᵢ` of every oriented tame structure are in
  `F.msheets`.
* **`theorem_9_5_4_full`, `theorem_9_5_5_full`**: Theorems 9.5.4, 9.5.5 with the local formula for
  every oriented tame structure describing `T̂Θ` (no class condition).  The `n`-dimensionality
  of `Θ` used above follows from the hypothesis that oriented tame structures of dimension `n`
  exist at all points of `supp Θ` (`isNDimensional_of_loc`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Θ : Obj → ℚ}

/-! ### Compactness of `supp Θ ∩ U` -/

/-- **`supp Θ` is locally compact**: near a point of the support of an `n`-dimensional `Θ`, the
support lies in a compact subset of itself. -/
theorem exists_isCompact_nhds_supp (hnd : X.IsNDimensional Θ n) {p : Obj} (hp : p ∈ supp Θ) :
    ∃ W : Set Obj, IsOpen W ∧ p ∈ W ∧
      ∃ K : Set Obj, IsCompact K ∧ supp Θ ∩ W ⊆ K ∧ K ⊆ supp Θ := by
  obtain ⟨B, hB⟩ := hnd p hp
  choose W hW hpW K hK hWK hKM using fun j =>
    MPolyfold.exists_compact_nhds_submanifold (hB j) (B.mem_M j)
  refine ⟨B.U ∩ ⋂ j, W j, B.isOpen_U.inter (isOpen_iInter_of_finite hW),
    ⟨B.mem_U, mem_iInter.2 hpW⟩, ⋃ j, K j, isCompact_iUnion hK, ?_, ?_⟩
  · rintro y ⟨hys, hyU, hyW⟩
    obtain ⟨j, hj⟩ := (B.mem_supp_iff hyU).1 hys
    exact mem_iUnion.2 ⟨j, hWK j ⟨hj, mem_iInter.1 hyW j⟩⟩
  · intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.1 hy
    exact (B.mem_supp_iff (B.subset_U j (hKM j hj))).2 ⟨j, hKM j hj⟩

/-- **A compact subset of `supp Θ` meeting every orbit of `supp Θ`**, for a compact
`n`-dimensional `Θ`. -/
theorem exists_isCompact_lift (hfun : X.IsFunctorial Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ n) :
    ∃ K' : Set Obj, IsCompact K' ∧ K' ⊆ supp Θ ∧ ∀ y ∈ supp Θ, ∃ z ∈ K', X.π y = X.π z := by
  choose W hW hpW K hK hWK hKs using fun p : supp Θ => exists_isCompact_nhds_supp hnd p.2
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover (fun p => X.π '' W p)
    (fun p => X.proposition_7_1_8 _ (hW p)) (by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_iUnion.2 ⟨⟨y, hy⟩, y, hpW _, rfl⟩)
  refine ⟨⋃ p ∈ t, K p, t.isCompact_biUnion fun p _ => hK p,
    iUnion₂_subset fun p _ => hKs p, fun y hy => ?_⟩
  obtain ⟨p, hpt, z, hzW, hzy⟩ := mem_iUnion₂.1 (ht ⟨y, hy, rfl⟩)
  have hzs : z ∈ supp Θ := by
    rw [← preimage_π_orbitSupp hfun]
    change X.π z ∈ X.orbitSupp Θ
    rw [hzy]; exact ⟨y, hy, rfl⟩
  exact ⟨z, mem_iUnion₂.2 ⟨p, hpt, hWK p ⟨hzs, hzW⟩⟩, hzy.symm⟩

/-- **`supp Θ ∩ U` lies in a compact subset of `supp Θ`** for a compact `n`-dimensional `Θ` and
an open `U` whose closure is a proper set (Definition 7.5.8). -/
theorem exists_isCompact_supp_inter (hfun : X.IsFunctorial Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ n) {U : Set Obj} (hU : X.IsProperSubset (closure U)) :
    ∃ K : Set Obj, IsCompact K ∧ supp Θ ∩ U ⊆ K ∧ K ⊆ supp Θ := by
  obtain ⟨K', hK'c, hK's, hK'⟩ := exists_isCompact_lift hfun hcpt hnd
  set f := (X.src ⁻¹' closure U).domRestrict X.tgt with hf
  have hc : IsCompact (f ⁻¹' K') := hU.isCompact_preimage hK'c
  refine ⟨(fun φ : X.src ⁻¹' closure U => X.src φ.1) '' (f ⁻¹' K'),
    hc.image (X.continuous_src.comp continuous_subtype_val), ?_, ?_⟩
  · rintro y ⟨hys, hyU⟩
    obtain ⟨z, hzK, hyz⟩ := hK' y hys
    obtain ⟨φ, hs, ht⟩ := (X.π_eq_π_iff).1 hyz
    have hφ : φ ∈ X.src ⁻¹' closure U := by
      change X.src φ ∈ closure U
      rw [hs]; exact subset_closure hyU
    refine ⟨⟨φ, hφ⟩, ?_, hs⟩
    change X.tgt φ ∈ K'
    rw [ht]; exact hzK
  · rintro _ ⟨⟨φ, hφ⟩, hφK, rfl⟩
    change 0 < Θ (X.src φ)
    rw [hfun φ]
    exact hK's hφK

namespace FormEval

variable {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}
  {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-! ### Sheets of `F.msheets` -/

/-- **Near a point of `supp Θ` the support is covered by finitely many one-chart sheets**: the
pieces `Mⱼ ∩ Vⱼ ∈ F.sheets` of the sheets of a local branching structure. -/
theorem exists_sheets_nhds_supp (hnd : X.IsNDimensional Θ n) {p : Obj} (hp : p ∈ supp Θ) :
    ∃ W : Set Obj, IsOpen W ∧ p ∈ W ∧ ∃ L : List (Set Obj), (∀ s ∈ L, s ∈ F.sheets) ∧
      supp Θ ∩ W ⊆ ⋃ s ∈ L, s := by
  classical
  obtain ⟨B, hB⟩ := hnd p hp
  choose V hV hpV hVs using fun j => exists_mem_sheets (F := F) (hB j) (B.mem_M j)
  refine ⟨B.U ∩ ⋂ j, V j, B.isOpen_U.inter (isOpen_iInter_of_finite hV),
    ⟨B.mem_U, mem_iInter.2 hpV⟩, (Finset.univ : Finset B.ι).toList.map fun j => B.M j ∩ V j,
    ?_, ?_⟩
  · intro s hs
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact hVs j
  · rintro y ⟨hys, hyU, hyV⟩
    obtain ⟨j, hj⟩ := (B.mem_supp_iff hyU).1 hys
    exact mem_iUnion₂.2 ⟨B.M j ∩ V j, List.mem_map.2 ⟨j, Finset.mem_toList.2
      (Finset.mem_univ j), rfl⟩, hj, mem_iInter.1 hyV j⟩

/-- **An `n`-dimensional submanifold in a compact subset of `supp Θ` is in `F.msheets`.** -/
theorem msheets_of_subset_isCompact (hnd : X.IsNDimensional Θ n) {N : Set Obj}
    (hN : X.PObj.IsSubmanifoldOfDim N n) (hne : N.Nonempty) {K : Set Obj} (hK : IsCompact K)
    (hKs : K ⊆ supp Θ) (hNK : N ⊆ K) : N ∈ F.msheets := by
  classical
  choose W hW hpW L hL hWL using fun p : K => exists_sheets_nhds_supp (F := F) hnd (hKs p.2)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hW fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hpW _⟩
  refine msheets_of_list hN hne (L := t.toList.flatMap L) (fun s hs => ?_) fun y hy => ?_
  · obtain ⟨p, -, hsp⟩ := List.mem_flatMap.1 hs
    exact hL p s hsp
  · obtain ⟨p, hpt, hyp⟩ := mem_iUnion₂.1 (ht (hNK hy))
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 (hWL p ⟨hKs (hNK hy), hyp⟩)
    exact mem_iUnion₂.2 ⟨s, List.mem_flatMap.2 ⟨p, Finset.mem_toList.2 hpt, hs⟩, hys⟩

/-- **The sheets of every oriented tame structure lie in the class `F.msheets`** (Theorem 9.5.4,
2021 p. 438, standing assumptions: `Θ` compact and `n`-dimensional): `Mᵢ ⊆ supp Θ ∩ U(x)`, which
lies in a compact subset of `supp Θ` by the properness property of `U(x)`. -/
theorem msheets_of_orientedTameStructure (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ n) {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (i : C.ι) : C.M i ∈ F.msheets := by
  obtain ⟨K, hK, hUK, hKs⟩ :=
    exists_isCompact_supp_inter hΘ.isFunctorial hcpt hnd C.hasPropernessProperty.2
  refine msheets_of_subset_isCompact hnd (C.isSubmanifoldOfDim i) ⟨x, C.mem_M i⟩ hK hKs
    fun y hy => hUK ⟨?_, C.subset_U i hy⟩
  exact (C.toLocalBranchingStructure.mem_supp_iff (C.subset_U i hy)).2 ⟨i, hy⟩

omit [AddCommGroup Ω] [Module ℝ Ω] in
/-- Oriented tame structures of dimension `n` at all points of `supp Θ` make `Θ`
`n`-dimensional. -/
theorem isNDimensional_of_loc {P : ∀ x, X.OrientedTameStructure n Θ x → Prop}
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, P x C) :
    X.IsNDimensional Θ n := fun x hx => by
  obtain ⟨C, -⟩ := hloc x hx
  exact ⟨C.toLocalBranchingStructure, C.isSubmanifoldOfDim⟩

variable (F)

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2)**, for the integrals over sheets covered by
several graph charts (`F.msheetIntegration`): `Θ` a compact branched ep⁺-subgroupoid with an
orientation `T̂Θ = T` described near every point of its support by an oriented tame structure of
dimension `n ≥ 1`.  There is exactly one linear map `ω ↦ μ_ω` into the signed measures on
`(S, L(S))` with `μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for **every** oriented tame structure
describing `T̂Θ` and every measurable `K ⊆ |U(x)|`. -/
theorem theorem_9_5_4_full (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.msheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x), C.Represents T →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.msheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasure (F.msheetIntegration hn) ω (Subtype.val '' K) := by
  have hnd : X.IsNDimensional Θ n := isNDimensional_of_loc hloc
  obtain ⟨Φ, hΦ, huniq⟩ := theorem_9_5_4_multi F hn hΘ hcpt hT hloc
  refine ⟨Φ, fun ω x C hC => hΦ ω x C ⟨fun i => msheets_of_orientedTameStructure hΘ hcpt hnd C i,
    hC⟩, fun Ψ hΨ => huniq Ψ fun ω x C hC => hΨ ω x C hC.2⟩

/-- **Theorem 9.5.5, 2021 p. 438 (2017: Theorem 9.3)**, for the integrals over sheets covered by
several graph charts: the same with the weights `1/♯G_x^eff`, for every oriented tame structure
describing `T̂Θ` whose `U(x)` has the property of Definition 7.2.18. -/
theorem theorem_9_5_5_full (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.msheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        (C.Represents T ∧ C.rep.HasLUC) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.msheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasureEff (F.msheetIntegration hn) ω (Subtype.val '' K) := by
  have hnd : X.IsNDimensional Θ n := isNDimensional_of_loc hloc
  obtain ⟨Φ, hΦ, huniq⟩ := theorem_9_5_5_multi F hn hΘ hcpt hT hloc
  refine ⟨Φ, fun ω x C hC => hΦ ω x C ⟨fun i => msheets_of_orientedTameStructure hΘ hcpt hnd C i,
    hC⟩, fun Ψ hΨ => huniq Ψ fun ω x C hC => hΨ ω x C hC.2⟩

end FormEval

end EpGroupoid

end Polyfold
