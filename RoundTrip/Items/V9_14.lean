import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_14

/-! Round trip for V9_14 (Theorem 9.2.1 (1), p. 409 of the 2021 book; 2017: Theorem 9.1,
p. 298: `∑ σᵢ · T_xMᵢ` does not depend on the local branching structure).

`A` is the conjunction of the types of the nine listed theorems, universes instantiated at `0`
(`B` lives in `Type`; `hasIndependentTangentSums_rn`, `tangentSum_structureβ_eq_structureγ` and
`hasIndependentTangentSums_indicator` have no universe parameter):
* `LocalBranchingStructure.tangentSum_eq_of_isGoodPoint` (at a good point, no hypothesis);
* `hasIndependentTangentSums_of_subset_goodSet` (if every point of `supp Θ` is good);
* `hasIndependentTangentSums_of_isOfDim` (all structures `n`-dimensional, tangent slices
  `HasTangentSlicesAt` on `supp Θ`);
* `hasIndependentTangentSums_of_dimPartsAgreeNear` (Proposition 9.1.12's conclusion, tangent
  slices);
* `hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt` (equidimensional, graph charts);
* `hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt` (any `Θ`, a graph
  chart for all dimensions and local constancy of the dimension on `supp Θ`);
* `hasIndependentTangentSums_rn` (object M-polyfold `ℝᵐ`, every `Θ`, no hypothesis);
* `Remark913Hyp.tangentSum_structureβ_eq_structureγ` (the two structures of Remark 9.1.3 (b));
* `hasIndependentTangentSums_indicator` (the indicator of a point of `ℝⁿ`).

The two sums agree by `rfl`: `B`'s `sumB` is the project's `tangentSum`.

* `B_to_A`: proved, using `B`.  Every conjunct of `A` concludes `B₁.tangentSum = B₂.tangentSum`
  for two structures of one `Θ` at one `x`.  `key` derives this from `B` for ANY `Θ` on ANY
  ep-groupoid (`Obj Mor : Type`), branched or not.  Off `supp Θ` both sums are `0`.  On it, put
  `W = U₁ ∩ U₂`, pass to the trivial ep-groupoid of `X.PObj` (`EpGroupoid.trivial`, the same
  M-polyfold, so the same `submanifoldTangent`) and to `Θ' = 1_W · Θ`.  `Θ'` is a branched
  ep⁺-subgroupoid there: it is functorial since all morphisms are identities, `supp Θ' ⊆ ⋃ Mᵢ`
  lies in `X_∞` (`subset_smoothSet`), the orbit space is `Obj` and metrizable
  (`MPolyfold.metrizableSpace`), so `|supp Θ'|` is paracompact, and the structures restrict to
  every point of `supp Θ'`.  The structures restricted to `W` are structures of `Θ'`, `B`
  applies, and `tangentSum_restrict` returns to `B₁`, `B₂`.
* `A → B`: not proved; a genuine gap in `A`.  `A` gives the independence on a general
  M-polyfold only under `HasTangentSlicesAt`, `HasGraphChartsAt`, or `HasGraphChartAt` with
  `HasLocallyConstantDimAt` (the content of Proposition 9.2.8 and Lemmas 9.2.9–9.2.11 and of
  Remark 9.1.1).  Those are proved only for `ℝᵐ`, and `B` claims the independence for every
  branched `Θ` on every ep-groupoid.
* `A_to_B_of_graphChart`: proved.  These are the only missing hypotheses: under
  `HasGraphChartAt` and `HasLocallyConstantDimAt` on `supp Θ` (both satisfiable: every point of
  `ℝᵐ`), `A` gives `B`'s conclusion. -/

namespace RoundTrip.V9_14
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isGoodPoint.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasIndependentTangentSums_of_subset_goodSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasIndependentTangentSums_of_dimPartsAgreeNear.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt.{0}) ∧
  (type_of%
    @Polyfold.EpGroupoid.hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasIndependentTangentSums_rn) ∧
  (type_of% @Polyfold.EpGroupoid.Remark913Hyp.tangentSum_structureβ_eq_structureγ) ∧
  (type_of% @Polyfold.hasIndependentTangentSums_indicator)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isGoodPoint.{0},
    @Polyfold.EpGroupoid.hasIndependentTangentSums_of_subset_goodSet.{0},
    @Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim.{0},
    @Polyfold.EpGroupoid.hasIndependentTangentSums_of_dimPartsAgreeNear.{0},
    @Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt.{0},
    @Polyfold.EpGroupoid.hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt.{0},
    @Polyfold.EpGroupoid.hasIndependentTangentSums_rn,
    @Polyfold.EpGroupoid.Remark913Hyp.tangentSum_structureβ_eq_structureγ,
    @Polyfold.hasIndependentTangentSums_indicator⟩

section Transfer

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ Θ' : Obj → ℚ}

/-- A structure of `Θ` on `X` is a structure of `Θ'` on the trivial ep-groupoid of `X.PObj`
when `Θ' = Θ` on its domain. -/
def toTrivial {x : Obj} (D : X.LocalBranchingStructure Θ x) (h : ∀ y ∈ D.U, Θ' y = Θ y) :
    (EpGroupoid.trivial X.PObj).LocalBranchingStructure Θ' x where
  U := D.U
  isOpen_U := D.isOpen_U
  mem_U := D.mem_U
  ι := D.ι
  M := D.M
  subset_U := D.subset_U
  isSmoothSubmanifold := D.isSmoothSubmanifold
  mem_M := D.mem_M
  isProperMap := D.isProperMap
  σ := D.σ
  σ_pos := D.σ_pos
  eq_sum y hy := by rw [h y hy]; exact D.eq_sum y hy

theorem sumB_toTrivial {x : Obj} (D : X.LocalBranchingStructure Θ x)
    (h : ∀ y ∈ D.U, Θ' y = Θ y) : sumB (toTrivial D h) = D.tangentSum := rfl

/-- `1_W · Θ` is a branched ep⁺-subgroupoid of the trivial ep-groupoid of `X.PObj`, for an open
`W` inside the domain of a local branching structure of `Θ`. -/
theorem isBranched_indicator {x : Obj} (D : X.LocalBranchingStructure Θ x) {W : Set Obj}
    (hW : IsOpen W) (hWU : W ⊆ D.U) :
    (EpGroupoid.trivial X.PObj).IsBranchedEpSubgroupoid (W.indicator Θ) where
  nonneg y := by
    by_cases hy : y ∈ W
    · rw [indicator_of_mem hy, D.eq_sum y (hWU hy)]
      exact Finset.sum_nonneg fun i _ => (D.σ_pos i).le
    · rw [indicator_of_notMem hy]
  isFunctorial _ := rfl
  support_subset y hy := by
    have hy' : 0 < W.indicator Θ y := hy
    have hyW : y ∈ W := by
      by_contra hn
      rw [indicator_of_notMem hn] at hy'
      exact lt_irrefl _ hy'
    rw [indicator_of_mem hyW] at hy'
    obtain ⟨i, hi⟩ := (D.mem_supp_iff (hWU hyW)).1 hy'
    exact (D.isSmoothSubmanifold i).subset_smoothSet hi
  paracompactSpace_orbitSupp := by
    have := X.PObj.metrizableSpace
    have : TopologicalSpace.MetrizableSpace (EpGroupoid.trivial X.PObj).OrbitSpace :=
      (EpGroupoid.trivialOrbitHomeomorph X.PObj).isEmbedding.metrizableSpace
    exact paracompactSpace_of_metrizableSpace _
  localBranching y hy := by
    have hy' : 0 < W.indicator Θ y := hy
    have hyW : y ∈ W := by
      by_contra hn
      rw [indicator_of_notMem hn] at hy'
      exact lt_irrefl _ hy'
    set C := D.restrictAt (hWU hyW)
    have hV : IsOpen (W ∩ C.U) := hW.inter C.isOpen_U
    exact ⟨toTrivial (C.restrict hV ⟨hyW, C.mem_U⟩ inter_subset_right)
      fun z hz => indicator_of_mem hz.1 _⟩

/-- **From `B`, the independence for every `Θ` on every ep-groupoid.** -/
theorem key (hB : B) {x : Obj} (B₁ B₂ : X.LocalBranchingStructure Θ x) :
    B₁.tangentSum = B₂.tangentSum := by
  by_cases hx : x ∈ EpGroupoid.supp Θ
  swap
  · rw [B₁.tangentSum_eq_zero hx, B₂.tangentSum_eq_zero hx]
  have hW : IsOpen (B₁.U ∩ B₂.U) := B₁.isOpen_U.inter B₂.isOpen_U
  have hxW : x ∈ B₁.U ∩ B₂.U := ⟨B₁.mem_U, B₂.mem_U⟩
  have hbr := isBranched_indicator B₁ hW inter_subset_left
  have hx' : x ∈ EpGroupoid.supp ((B₁.U ∩ B₂.U).indicator Θ) := by
    change 0 < (B₁.U ∩ B₂.U).indicator Θ x
    rw [indicator_of_mem hxW]
    exact hx
  have h := hB Obj Obj (EpGroupoid.trivial X.PObj) _ hbr x hx'
    (toTrivial (B₁.restrict hW hxW inter_subset_left) fun y hy => indicator_of_mem hy _)
    (toTrivial (B₂.restrict hW hxW inter_subset_right) fun y hy => indicator_of_mem hy _)
  rw [← B₁.tangentSum_restrict hW hxW inter_subset_left,
    ← B₂.tangentSum_restrict hW hxW inter_subset_right]
  exact h

theorem indep (hB : B) : X.HasIndependentTangentSums Θ := fun _ B₁ B₂ => key hB B₁ B₂

end Transfer

theorem B_to_A : B → A := fun hB =>
  ⟨fun B₁ B₂ _ => key hB B₁ B₂,
    fun _ => indep hB,
    fun _ _ => indep hB,
    fun _ _ => indep hB,
    fun _ _ => indep hB,
    fun _ _ => indep hB,
    fun _ _ => indep hB,
    fun _ _ => key hB _ _,
    fun _ _ => indep hB⟩

/-- `A → B` under the hypotheses of `A`'s general theorem: a graph chart for all dimensions
and local constancy of the dimension at the points of `supp Θ` (both hold in `ℝᵐ`). -/
theorem A_to_B_of_graphChart (hA : A) :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
      (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      (∀ x ∈ EpGroupoid.supp Θ, X.PObj.HasGraphChartAt x) →
      (∀ x ∈ EpGroupoid.supp Θ, X.PObj.HasLocallyConstantDimAt x) →
      ∀ x ∈ EpGroupoid.supp Θ, ∀ (B₁ B₂ : X.LocalBranchingStructure Θ x),
        sumB B₁ = sumB B₂ := by
  intro Obj Mor _ _ _ _ _ _ X Θ _ hG hLC x _ B₁ B₂
  exact hA.2.2.2.2.2.1 hG hLC x B₁ B₂

#rt_check RoundTrip.V9_14.B_to_A
  [Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isGoodPoint,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_subset_goodSet,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_dimPartsAgreeNear,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt,
  Polyfold.EpGroupoid.hasIndependentTangentSums_rn,
  Polyfold.EpGroupoid.Remark913Hyp.tangentSum_structureβ_eq_structureγ,
  Polyfold.hasIndependentTangentSums_indicator]
#rt_check RoundTrip.V9_14.A_to_B_of_graphChart
  [Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isGoodPoint,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_subset_goodSet,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_dimPartsAgreeNear,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt,
  Polyfold.EpGroupoid.hasIndependentTangentSums_rn,
  Polyfold.EpGroupoid.Remark913Hyp.tangentSum_structureβ_eq_structureγ,
  Polyfold.hasIndependentTangentSums_indicator]
#rt_overlap RoundTrip.V9_14.B_to_A
  [Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_eq_of_isGoodPoint,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_subset_goodSet,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_dimPartsAgreeNear,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt,
  Polyfold.EpGroupoid.hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt,
  Polyfold.EpGroupoid.hasIndependentTangentSums_rn,
  Polyfold.EpGroupoid.Remark913Hyp.tangentSum_structureβ_eq_structureγ,
  Polyfold.hasIndependentTangentSums_indicator]

end RoundTrip.V9_14
