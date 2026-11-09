import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_61

/-! Round trip for V9_61 (2021 Lemma 9.6.4, p. 455: top-goodness does not depend on the
structure).

The item lists the definitions `MPolyfold.TopMultiplicity`, `MPolyfold.TopMultiplicityAt`
(vocabulary: the hypothesis replacing Proposition 9.6.5) and seven theorems; `A` is the
conjunction of their types, universes at `0`: `topMultiplicity_zero` (`A1`),
`topMultiplicity_rn_of_le` (`A2`), `lemma_9_6_4` (`A3`: under `TopMultiplicity (topDim)`, for two
labelled structures at `x`, `y ∈ U ∩ U'` is top-good for one iff for the other),
`isTopBadPoint_iff` (`A4`: the same for top-bad), `topMultiplicityAt_of_hasGraphChartAt` (`A5`),
`topMultiplicity_rn` (`A6`: `TopMultiplicity` holds in every `ℝᵐ`), `lemma_9_6_4_of_hasGraphChartAt`
(`A7`: Lemma 9.6.4 under the graph representation at every point).  No branched hypothesis.

`B`: for branched `Θ`, `x ∈ supp Θ`, two structures with blind dimension labels and
`y ∈ U ∩ U'`: `IsTopGoodB B dim y ↔ IsTopGoodB B' dim' y` (`IsTopGoodB` includes `y ∈ M^k_U`).
No further hypothesis.

Glue: labels as in V9_59 (`IsDimLabelB ↔ IsSubmanifoldOfDim`, from `RoundTrip/Items/V9_2.lean`);
`IsTopGoodB L dim y ↔ y ∈ M^k_U ∧ IsTopGoodPoint L dim y` (as in V9_60).

* `A → B` fails: `A`'s Lemma 9.6.4 is conditional on `TopMultiplicity` of the top dimension (or
  the graph representation at every point), which the project proves only in `ℝᵐ` (`A6`) and for
  `k = 0` (`A1`); the project says the text's last step ("as in the discussion of good points")
  needs exactly this.  Proved: `A_to_B_of_topMultiplicity` (`B` under `TopMultiplicity`, from
  `A3` and the non-item `mem_topUnion_iff_of_mem`), `A_to_B_rn` (`B` for every ep-groupoid over
  `ℝᵐ`, with `A6`).
* `B → A` fails: `A1`, `A2`, `A5`, `A6` are facts about `TopMultiplicity` in M-polyfolds, not in
  `B`; `A3`, `A4`, `A7` hold for every `Θ`, `B` only for branched `Θ`.  Proved:
  `B_to_A3_of_branched`, `B_to_A4_of_branched` — for branched `Θ` `B` gives Lemma 9.6.4 for
  labelled structures *without* the `TopMultiplicity` hypothesis (off `M^k_U` both sides reduce
  to `y ∈ supp Θ`: the project's top-good points include, vacuously, the points of `M_U ∖ M^k_U`). -/

namespace RoundTrip.V9_61
open Polyfold EpGroupoid MPolyfold Set
open Polyfold.EpGroupoid.LocalBranchingStructure

/-- The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.MPolyfold.topMultiplicity_zero.{0}
def A2 : Prop := type_of% @Polyfold.topMultiplicity_rn_of_le
def A3 : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4.{0}
def A4 : Prop := type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff.{0}
def A5 : Prop := type_of% @Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt.{0}
def A6 : Prop := type_of% @Polyfold.MPolyfold.topMultiplicity_rn
def A7 : Prop :=
  type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt.{0}
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.topMultiplicity_zero.{0}, @Polyfold.topMultiplicity_rn_of_le,
    @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff.{0},
    @Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt.{0},
    @Polyfold.MPolyfold.topMultiplicity_rn,
    @Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt.{0}⟩

/-! ### The two dimension notions agree on submanifolds (from `RoundTrip/Items/V9_2.lean`) -/

section Dim
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

theorem tyMB_eq {A : Set Z} {y : Z} (hyA : y ∈ A) : TyMB P A y = P.submanifoldTangent A y := by
  ext α
  constructor
  · rintro ⟨d, hyV, β, hβ, rfl⟩
    have hβ' : P.levelVal 1 (P.tangentProj β) = y := hβ
    have hβV : β ∈ P.tangentPreimage d.V := by
      change P.levelVal 1 (P.tangentProj β) ∈ d.V
      rw [hβ']; exact hyV
    have := d.tmap_mem_submanifoldTangent hβV
    rwa [hβ', d.apply_eq_self ⟨hyA, hyV⟩] at this
  · rintro ⟨hαy, d, hyV, hfix⟩
    exact ⟨d, hyV, α, hαy, hfix⟩

theorem chartImgB_eq {φ : MChart Z} (hφ : P.IsChart φ) {A : Set Z} {y : Z} (hyA : y ∈ A) :
    chartImgB hφ (TyMB P A y) = P.chartTangent hφ A y := by
  rw [chartImgB, tyMB_eq hyA]
  rfl

theorem hasDimB_of {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} {n : ℕ}
    (h : P.HasDimAt A y n) : HasDimB P A y n := by
  have hyA := h.1
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hφ hA hyA hyφ
  refine ⟨φ, hφ, hyφ, N, hfin, ?_, ?_⟩
  · rw [chartImgB_eq hφ hyA, hN]
  · set d := hA.data hyA
    have hyV := hA.mem_data_V hyA
    have hy1 := d.mem_levelSet_one hyA hyV
    have hz := P.toBase_levelLift hφ hyφ hy1
    have h1 := h.finrank_eq d hφ hyV hyφ hz
    rw [← chartTangent_eq hφ d hyA hyV hyφ, ← hN, Submodule.span_eq] at h1
    exact h1

theorem hasDimAt_of {A : Set Z} (hA : P.IsSmoothSubmanifold A) {y : Z} (hyA : y ∈ A) {n : ℕ}
    (h : HasDimB P A y n) : P.HasDimAt A y n := by
  obtain ⟨φ, hφ, hyφ, S, -, hS, hn⟩ := h
  set d := hA.data hyA
  have hyV := hA.mem_data_V hyA
  have hy1 := d.mem_levelSet_one hyA hyV
  have hz := P.toBase_levelLift hφ hyφ hy1
  refine ⟨hyA, d, φ, levelLift φ 1 y, hyV, hφ, hyφ, hz, ?_⟩
  rw [← chartTangent_eq hφ d hyA hyV hyφ, ← chartImgB_eq hφ hyA, hS, Submodule.span_eq]
  exact hn

end Dim

section Labels
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}

theorem isSubmanifoldOfDim_of_label {L : X.LocalBranchingStructure Θ x} {dim : L.ι → ℕ}
    (h : IsDimLabelB L dim) : ∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i) := fun i =>
  ⟨L.isSmoothSubmanifold i, fun m hm => hasDimAt_of (L.isSmoothSubmanifold i) hm (h i m hm)⟩

theorem label_of_isSubmanifoldOfDim {L : X.LocalBranchingStructure Θ x} {dim : L.ι → ℕ}
    (h : ∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) : IsDimLabelB L dim := fun i m hm =>
  hasDimB_of (L.isSmoothSubmanifold i) ((h i).2 m hm)

/-- On `M^k_U`, the project's top-good point is the blind "the top sheets coincide near `y`"
(as in `RoundTrip/Items/V9_60.lean`). -/
theorem isTopGoodPoint_iff_topCoincideB (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ)
    {y : Obj} (hy : y ∈ MkB L dim (topDimB L dim)) :
    L.IsTopGoodPoint dim y ↔ TopCoincideB L dim y := by
  have hy' : ∃ i, dim i = topDimB L dim ∧ y ∈ L.M i := by
    simpa [MkB] using hy
  obtain ⟨i₀, -, hyi₀⟩ := hy'
  constructor
  · rintro ⟨-, V, hV, hyV, -, hVeq⟩
    exact ⟨V, hV, hyV, hVeq⟩
  · rintro ⟨V, hV, hyV, hVeq⟩
    refine ⟨mem_iUnion.2 ⟨i₀, hyi₀⟩, V ∩ L.U, hV.inter L.isOpen_U,
      ⟨hyV, L.subset_U i₀ hyi₀⟩, inter_subset_right, fun i j hi hj hyi hyj => ?_⟩
    have h := hVeq i j hi hj hyi hyj
    calc V ∩ L.U ∩ L.M i = L.U ∩ (V ∩ L.M i) := by ext; simp only [mem_inter_iff]; tauto
      _ = L.U ∩ (V ∩ L.M j) := by rw [h]
      _ = V ∩ L.U ∩ L.M j := by ext; simp only [mem_inter_iff]; tauto

theorem isTopGoodB_iff (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) (y : Obj) :
    IsTopGoodB L dim y ↔ y ∈ L.topUnion dim (L.topDim dim) ∧ L.IsTopGoodPoint dim y :=
  ⟨fun h => ⟨h.1, (isTopGoodPoint_iff_topCoincideB L dim h.1).2 h.2⟩,
    fun h => ⟨h.1, (isTopGoodPoint_iff_topCoincideB L dim h.1).1 h.2⟩⟩

/-- Off `M^k_U` the project's top-good points are the points of `M_U` (vacuously). -/
theorem isTopGoodPoint_iff_of_notMem (L : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ)
    {y : Obj} (hyU : y ∈ L.U) (hyT : y ∉ L.topUnion dim (L.topDim dim)) :
    L.IsTopGoodPoint dim y ↔ y ∈ supp Θ := by
  rw [L.mem_supp_iff hyU]
  refine ⟨fun h => mem_iUnion.1 h.1, fun h => ⟨mem_iUnion.2 h, L.U, L.isOpen_U, hyU, subset_rfl,
    fun i j hi _ hyi _ => (hyT (L.mem_topUnion.2 ⟨i, hi, hyi⟩)).elim⟩⟩

end Labels

/-! ### What `A` gives of `B` -/

/-- **`B` under `TopMultiplicity` of the top dimension.** -/
theorem A_to_B_of_topMultiplicity : A →
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      ∀ x ∈ EpGroupoid.supp Θ, ∀ (L L' : X.LocalBranchingStructure Θ x)
        (dim : L.ι → ℕ) (dim' : L'.ι → ℕ), IsDimLabelB L dim → IsDimLabelB L' dim' →
        X.PObj.TopMultiplicity (topDimB L dim) →
        ∀ y ∈ L.U ∩ L'.U, IsTopGoodB L dim y ↔ IsTopGoodB L' dim' y := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ _ x _ L L' dim dim' hl hl' hT y hy
  have hd := isSubmanifoldOfDim_of_label hl
  have hd' := isSubmanifoldOfDim_of_label hl'
  rw [isTopGoodB_iff, isTopGoodB_iff]
  exact and_congr (mem_topUnion_iff_of_mem hd hd' hy.1 hy.2) (hA.2.2.1 hT hd hd' hy.1 hy.2)

/-- **`B` over `ℝᵐ`** (`TopMultiplicity` there is `A6`). -/
theorem A_to_B_rn : A →
    ∀ (m : ℕ) (Mor : Type) [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid (Fin m → ℝ) Mor), X.PObj = rnPolyfold m →
      ∀ (Θ : (Fin m → ℝ) → ℚ), X.IsBranchedEpSubgroupoid Θ →
      ∀ x ∈ EpGroupoid.supp Θ, ∀ (L L' : X.LocalBranchingStructure Θ x)
        (dim : L.ι → ℕ) (dim' : L'.ι → ℕ), IsDimLabelB L dim → IsDimLabelB L' dim' →
        ∀ y ∈ L.U ∩ L'.U, IsTopGoodB L dim y ↔ IsTopGoodB L' dim' y := by
  intro hA m Mor _ _ _ X hX Θ hΘ x hx L L' dim dim' hl hl'
  have hT : X.PObj.TopMultiplicity (topDimB L dim) := by
    rw [hX]; exact hA.2.2.2.2.2.1 m _
  exact A_to_B_of_topMultiplicity hA _ Mor X Θ hΘ x hx L L' dim dim' hl hl' hT

/-! ### What `B` gives of `A`: Lemma 9.6.4 for branched `Θ`, with no `TopMultiplicity` -/

theorem B_to_A3_of_branched (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj)
      (L L' : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) (dim' : L'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (L'.M j) (dim' j)) →
      ∀ y ∈ L.U, y ∈ L'.U → (L.IsTopGoodPoint dim y ↔ L'.IsTopGoodPoint dim' y) := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x L L' dim dim' hd hd' y hyU hyU'
  have hT := mem_topUnion_iff_of_mem hd hd' hyU hyU'
  by_cases hyT : y ∈ L.topUnion dim (L.topDim dim)
  · obtain ⟨i, -, -⟩ := L.mem_topUnion.1 hyT
    have hx : x ∈ supp Θ := (L.mem_supp_iff L.mem_U).2 ⟨i, L.mem_M i⟩
    have h := hB Obj Mor X Θ hΘ x hx L L' dim dim' (label_of_isSubmanifoldOfDim hd)
      (label_of_isSubmanifoldOfDim hd') y ⟨hyU, hyU'⟩
    rw [isTopGoodB_iff, isTopGoodB_iff] at h
    exact ⟨fun hg => (h.1 ⟨hyT, hg⟩).2, fun hg => (h.2 ⟨hT.1 hyT, hg⟩).2⟩
  · rw [isTopGoodPoint_iff_of_notMem L dim hyU hyT,
      isTopGoodPoint_iff_of_notMem L' dim' hyU' fun h => hyT (hT.2 h)]

theorem B_to_A4_of_branched (hB : B) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ → ∀ (x : Obj)
      (L L' : X.LocalBranchingStructure Θ x) (dim : L.ι → ℕ) (dim' : L'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (L.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (L'.M j) (dim' j)) →
      ∀ y ∈ L.U, y ∈ L'.U → (L.IsTopBadPoint dim y ↔ L'.IsTopBadPoint dim' y) := by
  intro Obj Mor _ _ _ _ _ _ X Θ hΘ x L L' dim dim' hd hd' y hyU hyU'
  exact and_congr (mem_topUnion_iff_of_mem hd hd' hyU hyU')
    (not_congr (B_to_A3_of_branched hB Obj Mor X Θ hΘ x L L' dim dim' hd hd' y hyU hyU'))

#rt_check RoundTrip.V9_61.A_to_B_of_topMultiplicity [Polyfold.MPolyfold.topMultiplicity_zero,
  Polyfold.topMultiplicity_rn_of_le, Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4,
  Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff,
  Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt, Polyfold.MPolyfold.topMultiplicity_rn,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt]
#rt_check RoundTrip.V9_61.A_to_B_rn [Polyfold.MPolyfold.topMultiplicity_zero,
  Polyfold.topMultiplicity_rn_of_le, Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4,
  Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff,
  Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt, Polyfold.MPolyfold.topMultiplicity_rn,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt]
#rt_check RoundTrip.V9_61.B_to_A3_of_branched [Polyfold.MPolyfold.topMultiplicity_zero,
  Polyfold.topMultiplicity_rn_of_le, Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4,
  Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff,
  Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt, Polyfold.MPolyfold.topMultiplicity_rn,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt]
#rt_check RoundTrip.V9_61.B_to_A4_of_branched [Polyfold.MPolyfold.topMultiplicity_zero,
  Polyfold.topMultiplicity_rn_of_le, Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4,
  Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff,
  Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt, Polyfold.MPolyfold.topMultiplicity_rn,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt]
#rt_overlap RoundTrip.V9_61.B_to_A4_of_branched [Polyfold.MPolyfold.topMultiplicity_zero,
  Polyfold.topMultiplicity_rn_of_le, Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4,
  Polyfold.EpGroupoid.LocalBranchingStructure.isTopBadPoint_iff,
  Polyfold.MPolyfold.topMultiplicityAt_of_hasGraphChartAt, Polyfold.MPolyfold.topMultiplicity_rn,
  Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt]

end RoundTrip.V9_61
