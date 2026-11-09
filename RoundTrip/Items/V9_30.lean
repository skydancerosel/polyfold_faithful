import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_30

set_option maxSynthPendingDepth 3

/-! Round trip for V9_30 (Definition 9.3.2, p. 423 of the 2021 book; 2017: Definition 9.8,
p. 311: orientations of `Θ`).

The item lists the definitions `SubmanifoldOrientation`, `OrientedBranchingStructure`,
`orientedSum`, `IsOrientation`, `IsOrientable`, `orientedSection` (vocabulary) and seven
theorems.  `A` is the conjunction of the theorems' types, universes at `0`:
`grForget_orientedSum`, `IsOrientation.mk'` (the lifting condition from (9.9) given Theorem
9.2.1's independence), `orientedSection_comp_grHatProj`, `orientedSection_comp_grForgetFunctor_obj`,
`isOrientation_zero`, `isOrientation_sum_rn` (given independence) and
`isOrientation_sum_trivial_rn` (no universe parameters).

* `B` says that for every branched ep⁺-subgroupoid `Θ` and every `T`, the project's
  `IsOrientation Θ T` is the blind `IsOrientationB X Θ T`.  This holds (`B_holds`), so `A_to_B`
  does not use `A`.  `mem`, `natural`/`functor` and `lifts` agree by unfolding `GrHat`,
  `grHatPush` and `grForget`.  In (9.9) the project's `OrientedBranchingStructure` also asks
  `IsSubmanifoldOfDim (Mᵢ) (dᵢ)`, which the blind side omits; it follows from the orientation:
  an orientation `oᵢ` of `Mᵢ` in dimension `dᵢ` makes the chart image of `T_yMᵢ` a
  `dᵢ`-dimensional subspace at every `y ∈ Mᵢ`, which is `HasDimAt` through the chart description
  `chartVec_image_submanifoldTangent` and `hasDimAt_of_finrank` (`hasDimAt_of_orientation`).
  The sums agree definitionally.
* `B_to_A`: `isOrientation_zero` is obtained through `B` (`Θ = 0` is branched, and
  `IsOrientationB` is checked directly).  The other conjuncts are stated for arbitrary `Θ` or
  are computations/witnesses that `B` does not state; they are re-proved outright as copies of
  the project's proofs, with the banned `grForget_orientedSum`, `IsOrientation.mk'` and
  `isOrientation_sum_rn` (and `grForget_orientedSum_self`, built on the first) replaced by
  local copies. -/

namespace RoundTrip.V9_30
open Polyfold Set Module

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.OrientedBranchingStructure.grForget_orientedSum.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsOrientation.mk'.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.orientedSection_comp_grHatProj.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.orientedSection_comp_grForgetFunctor_obj.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOrientation_zero.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOrientation_sum_rn) ∧
  (type_of% @Polyfold.EpGroupoid.isOrientation_sum_trivial_rn)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.OrientedBranchingStructure.grForget_orientedSum.{0},
    @Polyfold.EpGroupoid.IsOrientation.mk'.{0},
    @Polyfold.EpGroupoid.orientedSection_comp_grHatProj.{0},
    @Polyfold.EpGroupoid.orientedSection_comp_grForgetFunctor_obj.{0},
    @Polyfold.EpGroupoid.isOrientation_zero.{0},
    @Polyfold.EpGroupoid.isOrientation_sum_rn,
    @Polyfold.EpGroupoid.isOrientation_sum_trivial_rn⟩

/-! ### `B` holds: the definitions agree -/

/-- **An orientation in dimension `n` forces dimension `n`**: if `o` orients the smooth
submanifold `M` in dimension `n`, then `M` has dimension `n` at every point. -/
theorem hasDimAt_of_orientation {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {M : Set Z} (hM : P.IsSmoothSubmanifold M) {n : ℕ}
    (o : P.SubmanifoldOrientation M n) {a : Z} (ha : a ∈ M) : P.HasDimAt M a n := by
  obtain ⟨-, φ, hφ, haφ, N, hN, -, hrank, -⟩ := o.isOrientedAt a ha
  set d := hM.data ha
  have haV : a ∈ d.V := hM.mem_data_V ha
  have ha1 : a ∈ P.levelSet 1 := d.mem_levelSet_one ha haV
  have hz : φ.model.E.toBase 1 (MPolyfold.levelLift φ 1 a) = φ a :=
    P.toBase_levelLift hφ haφ ha1
  have hchart := MPolyfold.chartVec_image_submanifoldTangent hφ d ha haV haφ
  refine MPolyfold.hasDimAt_of_finrank hM ha hφ (d.toSubData.isOpen_shrink φ)
    (d.toSubData.shrink_subset_source φ) (d.toSubData.isScRetract_image φ hφ)
    (d.toSubData.mem_shrink φ ha haV haφ) hz ?_
  have hset : tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ M))
      (MPolyfold.levelLift φ 1 a) = (N : Set (φ.model.E 0)) := hchart.symm.trans hN.symm
  rw [hset, Submodule.span_eq]
  exact hrank

theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X Θ _ T
  constructor
  · intro hT
    refine ⟨fun x hx => hT.mem x hx, fun φ hφ => hT.natural φ hφ, fun x hx => hT.lifts x hx,
      fun x hx => ?_⟩
    obtain ⟨Bo, hBo⟩ := hT.locallyOriented x hx
    exact ⟨Bo.toLocalBranchingStructure, Bo.dim, Bo.orient, fun y hy hys => hBo y hy hys⟩
  · intro hT
    refine ⟨fun x hx => hT.mem x hx, fun φ hφ => hT.functor φ hφ, fun x hx => hT.lifts x hx,
      fun x hx => ?_⟩
    obtain ⟨Bl, n, o, hBl⟩ := hT.locRep x hx
    exact ⟨⟨Bl, n, fun i => ⟨Bl.isSmoothSubmanifold i,
      fun a ha => hasDimAt_of_orientation (Bl.isSmoothSubmanifold i) (o i) ha⟩, o⟩,
      fun y hy hys => hBl y hy hys⟩

theorem A_to_B : A → B := fun _ => B_holds

/-! ### `B → A` -/

section Copies

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

open scoped Classical in
/-- Copy of `grForget_orientedSum`. -/
theorem grForget_orientedSum' {Θ : Obj → ℚ} {x : Obj} (Bo : X.OrientedBranchingStructure Θ x)
    (y : Obj) :
    X.grForget (Bo.orientedSum y) =
      ∑ i with y ∈ Bo.M i, Finsupp.single (X.PObj.submanifoldTangent (Bo.M i) y) (Bo.σ i) := by
  rw [EpGroupoid.OrientedBranchingStructure.orientedSum, EpGroupoid.grForget,
    Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

/-- Copy of `grForget_orientedSum_self`. -/
theorem grForget_orientedSum_self' {Θ : Obj → ℚ} {x : Obj}
    (Bo : X.OrientedBranchingStructure Θ x) :
    X.grForget (Bo.orientedSum x) = Bo.tangentSum := by
  classical
  rw [grForget_orientedSum', EpGroupoid.LocalBranchingStructure.tangentSum,
    Finset.filter_true_of_mem fun i _ => Bo.mem_M i]

/-- Copy of `IsOrientation.mk'`. -/
theorem isOrientation_mk' {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hind : X.HasIndependentTangentSums Θ)
    (hmem : ∀ x ∈ X.PObj.smoothSet, T x ∈ X.GrHat x)
    (hnat : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet → X.grHatPush φ (T (X.src φ)) = T (X.tgt φ))
    (hzero : ∀ x ∈ X.PObj.smoothSet, x ∉ EpGroupoid.supp Θ → T x = 0)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ Bo : X.OrientedBranchingStructure Θ x,
      ∀ y ∈ Bo.U, y ∈ X.PObj.smoothSet → T y = Bo.orientedSum y) :
    X.IsOrientation Θ T where
  mem := hmem
  natural := hnat
  lifts x hx := by
    by_cases hxs : x ∈ EpGroupoid.supp Θ
    · obtain ⟨Bo, hBo⟩ := hloc x hxs
      rw [hBo x Bo.mem_U hx, grForget_orientedSum_self',
        X.tangentValue_eq hind Bo.toLocalBranchingStructure]
    · rw [hzero x hx hxs, X.tangentValue_eq_zero hxs, EpGroupoid.grForget,
        Finsupp.mapDomain_zero]
  locallyOriented := hloc

end Copies

section Rn

variable {n : ℕ}

open scoped Classical in
/-- Copy of `isOrientation_sum_rn`. -/
theorem isOrientation_sum_rn' {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i))
    (hind : (EpGroupoid.trivial (rnPolyfold n)).HasIndependentTangentSums
      (fun y => ∑ i with y ∈ M i, σ i)) :
    (EpGroupoid.trivial (rnPolyfold n)).IsOrientation (fun y => ∑ i with y ∈ M i, σ i)
      (EpGroupoid.orientedSumRn M σ o) := by
  have hmem : ∀ y, EpGroupoid.orientedSumRn M σ o y ∈
      (EpGroupoid.trivial (rnPolyfold n)).GrHat y := fun y => by
    rw [← EpGroupoid.orientedSum_sum_rn_eq M σ hσ hM hc o
      (EpGroupoid.orientedBranchingStructure_sum_rn M σ hσ hM hc o y).mem_U]
    exact EpGroupoid.OrientedBranchingStructure.orientedSum_mem _ y
  refine isOrientation_mk' hind (fun y _ => hmem y)
    (fun φ _ => EpGroupoid.grHatPush_unit (hmem φ))
    (fun y _ hy => ?_) (fun x _ => ⟨EpGroupoid.orientedBranchingStructure_sum_rn M σ hσ hM hc o x,
      fun y hy _ => (EpGroupoid.orientedSum_sum_rn_eq M σ hσ hM hc o hy).symm⟩)
  refine Finset.sum_eq_zero fun i hi => (hy ?_).elim
  exact Finset.sum_pos' (fun j _ => (hσ j).le) ⟨i, hi, hσ i⟩

end Rn

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `grForget_orientedSum`
    intro Obj Mor _ _ _ _ _ _ X Θ x Bo y
    exact grForget_orientedSum' Bo y
  · -- `IsOrientation.mk'`
    intro Obj Mor _ _ _ _ _ _ X Θ T hind hmem hnat hzero hloc
    exact isOrientation_mk' hind hmem hnat hzero hloc
  · -- `orientedSection_comp_grHatProj`
    intro Obj Mor _ _ _ _ _ _ X Θ T hT
    rfl
  · -- `orientedSection_comp_grForgetFunctor_obj`
    intro Obj Mor _ _ _ _ _ _ X Θ T hT hΘ hind x
    change (⟨x.pt, x.smooth, X.grForget (T x.pt), _⟩ : X.GrObj) =
      ⟨x.pt, x.smooth, X.tangentValue Θ x.pt, _⟩
    congr 1
    exact hT.lifts _ x.smooth
  · -- `isOrientation_zero`, through `B`
    intro Obj Mor _ _ _ _ _ _ X
    refine (hB Obj Mor X 0 (EpGroupoid.isBranchedEpSubgroupoid_zero X) fun _ => 0).2
      ⟨fun x _ => ⟨fun _ => le_rfl, fun g hg => by simp at hg⟩,
        fun φ _ => by rw [Finsupp.mapDomain_zero], fun x _ => ?_,
        fun x hx => (lt_irrefl (0 : ℚ) hx).elim⟩
    rw [Finsupp.mapDomain_zero, X.tangentValue_eq_zero (fun h => lt_irrefl (0 : ℚ) h)]
  · -- `isOrientation_sum_rn`
    intro n ι _ M σ hσ dim hM hc o hind
    exact isOrientation_sum_rn' M σ hσ hM hc o hind
  · -- `isOrientation_sum_trivial_rn`
    intro n ι _ M σ hσ dim hM hc o
    exact isOrientation_sum_rn' M σ hσ hM hc o (EpGroupoid.hasIndependentTangentSums_rn rfl _)

#rt_check RoundTrip.V9_30.A_to_B [
  Polyfold.EpGroupoid.OrientedBranchingStructure.grForget_orientedSum,
  Polyfold.EpGroupoid.IsOrientation.mk', Polyfold.EpGroupoid.orientedSection_comp_grHatProj,
  Polyfold.EpGroupoid.orientedSection_comp_grForgetFunctor_obj,
  Polyfold.EpGroupoid.isOrientation_zero, Polyfold.EpGroupoid.isOrientation_sum_rn,
  Polyfold.EpGroupoid.isOrientation_sum_trivial_rn]
#rt_check RoundTrip.V9_30.B_to_A [
  Polyfold.EpGroupoid.OrientedBranchingStructure.grForget_orientedSum,
  Polyfold.EpGroupoid.IsOrientation.mk', Polyfold.EpGroupoid.orientedSection_comp_grHatProj,
  Polyfold.EpGroupoid.orientedSection_comp_grForgetFunctor_obj,
  Polyfold.EpGroupoid.isOrientation_zero, Polyfold.EpGroupoid.isOrientation_sum_rn,
  Polyfold.EpGroupoid.isOrientation_sum_trivial_rn]
#rt_overlap RoundTrip.V9_30.B_to_A [
  Polyfold.EpGroupoid.OrientedBranchingStructure.grForget_orientedSum,
  Polyfold.EpGroupoid.IsOrientation.mk', Polyfold.EpGroupoid.orientedSection_comp_grHatProj,
  Polyfold.EpGroupoid.orientedSection_comp_grForgetFunctor_obj,
  Polyfold.EpGroupoid.isOrientation_zero, Polyfold.EpGroupoid.isOrientation_sum_rn,
  Polyfold.EpGroupoid.isOrientation_sum_trivial_rn]

end RoundTrip.V9_30
