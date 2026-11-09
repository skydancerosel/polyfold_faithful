import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_28

/-! Round trip for V9_28 (Remark 9.2.17, p. 421 of the 2021 book; 2017: Remark 9.6, p. 310:
`∂Θ` is in general not the restriction of `Θ` to `∂X`).

`A` is the conjunction of the types of the six listed theorems, universes at `0` (`B` lives in
`Type`): `EpGroupoid.boundaryTheta_le` (`∂Θ ≤ Θ`, given Theorem 9.2.1's independence `hind`),
the witnesses `boundaryTheta_halfLineCorner` (for `Θ = 1_{0}` on `[0, ∞)`: `0 ∈ ∂X`,
`Θ(0) = 1`, `∂Θ(0) = 0`), `boundaryTheta_halfLine_one` (`Θ = 1` on `[0, ∞)`: `∂Θ(0) = 1`),
`EpGroupoid.boundaryTheta_indicator_of_mem` (`∂ 1_{p} = 0`), `isBranchedEpSubgroupoid_one` and
`boundaryTheta_one` (the ingredients of the second witness).

* `B` (an ep-groupoid, a branched ep⁺-subgroupoid `Θ`, a local branching structure at a point of
  `supp Θ` and `y ∈ U(x) ∩ ∂X` with `∑_{y ∈ ∂Mᵢ} σᵢ ≠ Θ(y)`) is the existential content of the
  remark.  `A_to_B` takes `A`'s witness `boundaryTheta_halfLineCorner`: a local branching
  structure at the corner exists since `Θ` is branched, and by the local formula
  `boundaryTheta_eq` (not an item theorem here; it needs the `hind` that the witness provides)
  its boundary sum at the corner is `∂Θ(0) = 0 ≠ 1 = Θ(0)`.
* `B_to_A`: `B` is a bare existence statement, and `A`'s conjuncts are a general inequality and
  three concrete examples; none follows from `B`.  They are re-proved outright, as copies of the
  project's proofs with the banned theorems replaced by local copies (`boundaryTheta_eq`,
  `mem_submanifoldBoundary_iff`, `boundaryTheta_halfLineCorner`'s ingredients
  `isBranchedEpSubgroupoid_indicator_of_mem`, `hasIndependentTangentSums_indicator_of_mem`,
  `hasIndependentTangentSums_one`, `halfLineCorner_mem_submanifoldBoundary` are not banned).
  So `B_to_A` does not use `B` (flagged). -/

namespace RoundTrip.V9_28
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.boundaryTheta_le.{0}) ∧
  (type_of% @Polyfold.boundaryTheta_halfLineCorner) ∧
  (type_of% @Polyfold.boundaryTheta_halfLine_one) ∧
  (type_of% @Polyfold.EpGroupoid.boundaryTheta_indicator_of_mem.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.boundaryTheta_one.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.boundaryTheta_le.{0}, @Polyfold.boundaryTheta_halfLineCorner,
    @Polyfold.boundaryTheta_halfLine_one, @Polyfold.EpGroupoid.boundaryTheta_indicator_of_mem.{0},
    @Polyfold.EpGroupoid.isBranchedEpSubgroupoid_one.{0}, @Polyfold.EpGroupoid.boundaryTheta_one.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA
  have hc := hA.2.1
  simp only at hc
  obtain ⟨hΘ, hind, hb, h1, h0, -⟩ := hc
  have hs : halfLineCorner ∈ EpGroupoid.supp
      (({halfLineCorner} : Set (quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0)).indicator
        (1 : quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0 → ℚ)) := by
    change (0 : ℚ) < _
    rw [h1]; exact one_pos
  obtain ⟨Bs⟩ := hΘ.localBranching _ hs
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, _, hΘ, halfLineCorner, hs, Bs, halfLineCorner, Bs.mem_U, hb, ?_⟩
  rw [bsumB, ← EpGroupoid.boundaryTheta_eq hind Bs Bs.mem_U, h0, h1]
  exact zero_ne_one

/-! ### `B → A`, outright -/

section Copies

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)

/-- Copy of `boundaryTheta_indicator_of_mem`. -/
theorem boundaryTheta_indicator_of_mem' {p : Z} (hp : p ∈ P.smoothSet) :
    (EpGroupoid.trivial P).boundaryTheta (({p} : Set Z).indicator 1) = 0 := by
  classical
  funext y
  by_cases hy : y = p
  · subst hy
    rw [(EpGroupoid.trivial P).boundaryTheta_eq
      (EpGroupoid.hasIndependentTangentSums_indicator_of_mem P hp)
      (EpGroupoid.localBranchingStructure_indicator_of_mem P hp) (mem_univ y)]
    refine Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 ?_
    exact MPolyfold.not_mem_submanifoldBoundary_singleton (P := P) y
  · exact EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp
      (by rw [EpGroupoid.supp_indicator_singleton']; exact hy)

/-- Copy of `isBranchedEpSubgroupoid_one`. -/
theorem isBranchedEpSubgroupoid_one' (hP : P.HasCornerStructure) :
    (EpGroupoid.trivial P).IsBranchedEpSubgroupoid fun _ => 1 where
  nonneg _ := zero_le_one
  isFunctorial _ := rfl
  support_subset y _ := by
    obtain ⟨χ, hχ, hy, hcorner⟩ := MPolyfold.hasCornerStructure_iff.1 hP y
    exact (P.mem_smoothSet_iff_of_isChart hχ hy).2 (hcorner.mem_smooth _)
  paracompactSpace_orbitSupp :=
    EpGroupoid.paracompactSpace_orbitSupp_trivial_of_isClosed P
      (by rw [EpGroupoid.supp_one]; exact isClosed_univ)
  localBranching x _ := ⟨EpGroupoid.localBranchingStructure_one P hP x⟩

/-- Copy of `boundaryTheta_one`. -/
theorem boundaryTheta_one' (hP : P.HasCornerStructure) {y : Z}
    (hy : y ∈ P.submanifoldBoundary univ) :
    (EpGroupoid.trivial P).boundaryTheta (fun _ => 1) y = 1 := by
  classical
  rw [(EpGroupoid.trivial P).boundaryTheta_eq (EpGroupoid.hasIndependentTangentSums_one P hP)
    (EpGroupoid.localBranchingStructure_one P hP y) (mem_univ y)]
  change ∑ i ∈ Finset.univ.filter fun (_ : PUnit) => y ∈ P.submanifoldBoundary univ, (1 : ℚ) = 1
  rw [Finset.filter_true_of_mem fun _ _ => hy]
  simp

end Copies

theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `boundaryTheta_le`
    intro Obj Mor _ _ _ _ _ _ X Θ hΘ hind y
    classical
    by_cases hy : y ∈ EpGroupoid.supp Θ
    · obtain ⟨Bs⟩ := hΘ.localBranching y hy
      rw [X.boundaryTheta_eq hind Bs Bs.mem_U, Bs.eq_sum y Bs.mem_U]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
        fun i _ _ => (Bs.σ_pos i).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ((MPolyfold.mem_submanifoldBoundary_iff (Bs.isSmoothSubmanifold i)).1 hi).1
    · rw [EpGroupoid.boundaryTheta_eq_zero_of_not_mem_supp hy]
      exact hΘ.nonneg y
  · -- `boundaryTheta_halfLineCorner`
    intro P Θ
    refine ⟨EpGroupoid.isBranchedEpSubgroupoid_indicator_of_mem P halfLineCorner_mem_smoothSet,
      EpGroupoid.hasIndependentTangentSums_indicator_of_mem P halfLineCorner_mem_smoothSet,
      halfLineCorner_mem_boundary, by simp [Θ], ?_, MPolyfold.isTangentReducedAt_singleton
        (MPolyfold.isSmoothSubmanifold_singleton halfLineCorner_mem_smoothSet)⟩
    rw [boundaryTheta_indicator_of_mem' P halfLineCorner_mem_smoothSet]
    rfl
  · -- `boundaryTheta_halfLine_one`
    intro P
    exact ⟨isBranchedEpSubgroupoid_one' P MPolyfold.halfLine_hasCornerStructure,
      EpGroupoid.hasIndependentTangentSums_one P MPolyfold.halfLine_hasCornerStructure,
      boundaryTheta_one' P MPolyfold.halfLine_hasCornerStructure
        MPolyfold.halfLineCorner_mem_submanifoldBoundary⟩
  · -- `boundaryTheta_indicator_of_mem`
    intro Z _ _ _ P p hp
    exact boundaryTheta_indicator_of_mem' P hp
  · -- `isBranchedEpSubgroupoid_one`
    intro Z _ _ _ P hP
    exact isBranchedEpSubgroupoid_one' P hP
  · -- `boundaryTheta_one`
    intro Z _ _ _ P hP y hy
    exact boundaryTheta_one' P hP hy

#rt_check RoundTrip.V9_28.A_to_B [Polyfold.EpGroupoid.boundaryTheta_le,
  Polyfold.boundaryTheta_halfLineCorner, Polyfold.boundaryTheta_halfLine_one,
  Polyfold.EpGroupoid.boundaryTheta_indicator_of_mem,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_one, Polyfold.EpGroupoid.boundaryTheta_one]
#rt_check RoundTrip.V9_28.B_to_A [Polyfold.EpGroupoid.boundaryTheta_le,
  Polyfold.boundaryTheta_halfLineCorner, Polyfold.boundaryTheta_halfLine_one,
  Polyfold.EpGroupoid.boundaryTheta_indicator_of_mem,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_one, Polyfold.EpGroupoid.boundaryTheta_one]
#rt_overlap RoundTrip.V9_28.B_to_A [Polyfold.EpGroupoid.boundaryTheta_le,
  Polyfold.boundaryTheta_halfLineCorner, Polyfold.boundaryTheta_halfLine_one,
  Polyfold.EpGroupoid.boundaryTheta_indicator_of_mem,
  Polyfold.EpGroupoid.isBranchedEpSubgroupoid_one, Polyfold.EpGroupoid.boundaryTheta_one]

end RoundTrip.V9_28
