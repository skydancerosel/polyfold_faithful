import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_24

/-! Round trip for V9_24 (Lemma 9.2.13, p. 419 of the 2021 book; 2017: Lemma 9.9): for a
submanifold `M` and `x ∈ M`, (1) `x ∈ ∂X` and `d_M(x) = 0` iff (2) `T_xM ⊆ T^R_xX`.

`A` is the conjunction of the types of the thirteen listed theorems, universe instantiated at `0`
where there is one (`B` lives in `Type`): the chart lemmas `isReducedTangentAt_iff_subset_reduced`,
`isReducedTangentAt_iff_subset_partialCone`, `isReducedTangentAt_chart_change`,
`isTangentReducedAt_iff_forall`, `lemma_9_2_13_chart`, `subDegIndex_le` (Lemma 2.26 for
submanifolds), the sc⁺-retraction lemmas `ScRetraction.IsScPlus.exists_injOn_proj`,
`ScRetraction.IsScPlus.exists_flat`, the lemma itself `lemma_9_2_13` ((1) ⇒ (2)),
`lemma_9_2_13_two_one` ((2) ⇒ (1) for `x ∈ ∂X`), `lemma_9_2_13_iff` (the equivalence at
`x ∈ M ∩ ∂X`), `subDegIndex_eq_zero_iff` (`d_M(x) = 0 ↔ (2)` at every `x ∈ M`), and
`not_lemma_9_2_13_two_one` (a point of `ℝⁿ` satisfies (2) but not (1)).

* `B` (literal, at every `x ∈ M`) is **false**, as its author predicted: `not_B`, with the point
  `{p}` of `ℝ¹` (off `∂X`, (2) holds: `isTangentReducedAt_of_not_mem_boundary`, the first half
  of the project's `lemma_9_2_13_of_not_mem_boundary` re-proved).  So `A → B` is
  false and `B → A` holds only ex falso.
* `BRepaired` is `B` with the hypothesis `x ∈ ∂X` (the author's suggested repair, the project's
  `lemma_9_2_13_iff`).  `A_to_BRepaired` is proved.  `BRepaired_gives_main` derives the four
  main conjuncts (`lemma_9_2_13`, `lemma_9_2_13_two_one`, `lemma_9_2_13_iff`,
  `subDegIndex_eq_zero_iff`, the last with the off-boundary case re-proved here from
  Lemma 2.26); `BRepaired → A` is not proved: `A` also has the chart
  lemmas (chart independence of (2), the chart form of (1) ⇒ (2) for every chart), the
  sc⁺-retraction lemmas and Lemma 2.26, which `BRepaired` does not state. -/

namespace RoundTrip.V9_24
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.isReducedTangentAt_iff_subset_reduced) ∧
  (type_of% @Polyfold.isReducedTangentAt_iff_subset_partialCone) ∧
  (type_of% @Polyfold.MPolyfold.subDegIndex_le.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isReducedTangentAt_chart_change.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isTangentReducedAt_iff_forall.{0}) ∧
  (type_of% @Polyfold.MPolyfold.lemma_9_2_13_chart.{0}) ∧
  (type_of% @Polyfold.MPolyfold.lemma_9_2_13.{0}) ∧
  (type_of% @Polyfold.MPolyfold.lemma_9_2_13_two_one.{0}) ∧
  (type_of% @Polyfold.MPolyfold.lemma_9_2_13_iff.{0}) ∧
  (type_of% @Polyfold.MPolyfold.subDegIndex_eq_zero_iff.{0}) ∧
  (type_of% @Polyfold.ScRetraction.IsScPlus.exists_injOn_proj) ∧
  (type_of% @Polyfold.ScRetraction.IsScPlus.exists_flat) ∧
  (type_of% @Polyfold.MPolyfold.not_lemma_9_2_13_two_one)

theorem A_holds : A :=
  ⟨@Polyfold.isReducedTangentAt_iff_subset_reduced,
    @Polyfold.isReducedTangentAt_iff_subset_partialCone,
    @Polyfold.MPolyfold.subDegIndex_le.{0}, @Polyfold.MPolyfold.isReducedTangentAt_chart_change.{0},
    @Polyfold.MPolyfold.isTangentReducedAt_iff_forall.{0},
    @Polyfold.MPolyfold.lemma_9_2_13_chart.{0}, @Polyfold.MPolyfold.lemma_9_2_13.{0},
    @Polyfold.MPolyfold.lemma_9_2_13_two_one.{0}, @Polyfold.MPolyfold.lemma_9_2_13_iff.{0},
    @Polyfold.MPolyfold.subDegIndex_eq_zero_iff.{0},
    @Polyfold.ScRetraction.IsScPlus.exists_injOn_proj,
    @Polyfold.ScRetraction.IsScPlus.exists_flat,
    @Polyfold.MPolyfold.not_lemma_9_2_13_two_one⟩

/-! ### Off `∂X`: (2) holds, and `d_M = 0`

The project's `lemma_9_2_13_of_not_mem_boundary` proves both, but reaches the item theorem
`subDegIndex_le` for the second; its first half is re-proved here verbatim, the second from
Lemma 2.26 (`lemma_2_4_6`) directly. -/

section offBoundary
open MPolyfold
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

theorem isTangentReducedAt_of_not_mem_boundary {M : Set Z} (hA : P.IsSmoothSubmanifold M)
    {a : M} (ha : a.1 ∉ P.boundary) : P.IsTangentReducedAt M a := by
  have h0 : P.degIndex a.1 = 0 := by
    have : ¬ 1 ≤ P.degIndex a.1 := ha
    omega
  obtain ⟨φ, hφ, haφ, hd⟩ := P.exists_isChart_degIndex_eq a.1
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet a.2)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  refine ⟨a.2, hA.data a.2, φ, n, W, T, z, hA.mem_data_V a.2, hφ, haφ, hT, hz, ?_⟩
  intro v _
  refine (mem_minimalSubspaceWith T).2 fun i hi => ?_
  exfalso
  rw [chartDegIndex, degIndex_eq T hT (φ.apply_mem_C haφ), h0, degIndexWith, quadrantDeg] at hd
  rw [hz] at hi
  have hmem : i ∈ Finset.univ.filter fun j => (T 0 (φ a)).1 j = 0 :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
  rw [Finset.card_eq_zero.1 hd.symm] at hmem
  exact Finset.notMem_empty _ hmem

theorem subDegIndex_eq_zero_of_not_mem_boundary {M : Set Z} (hA : P.IsSmoothSubmanifold M)
    {a : M} (ha : a.1 ∉ P.boundary) : P.subDegIndex hA.isSubMPolyfold a = 0 := by
  have h0 : P.degIndex a.1 = 0 := by
    have : ¬ 1 ≤ P.degIndex a.1 := ha
    omega
  let := P.paracompactSpace_subtype M
  have hle : P.subDegIndex hA.isSubMPolyfold a ≤ P.degIndex a.1 :=
    lemma_2_4_6 hA.isSubMPolyfold a
  omega

end offBoundary

/-! ### `B` is false -/

theorem not_B : ¬ B := by
  intro hB
  set p : Fin 1 → ℝ := 0
  have hM := rnPolyfold_isSmoothSubmanifold_singleton 1 p
  have hb : p ∉ (rnPolyfold 1).boundary := by
    simp [MPolyfold.boundary, rnPolyfold_degIndex]
  have hred := isTangentReducedAt_of_not_mem_boundary hM (a := ⟨p, Set.mem_singleton p⟩) hb
  exact hb ((hB _ (rnPolyfold 1) {p} p hM (Set.mem_singleton p)).2 hred).1

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### The repaired statement: `B` at points of `∂X` -/

/-- `B` with the hypothesis `x ∈ ∂X`. -/
def BRepaired : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (M : Set Z) (x : Z), P.IsSmoothSubmanifold M → x ∈ M → x ∈ P.boundary →
      ((x ∈ P.boundary ∧ x ∉ P.submanifoldBoundary M) ↔ P.IsTangentReducedAt M x)

theorem not_mem_submanifoldBoundary_iff {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} {M : Set Z} (hM : P.IsSmoothSubmanifold M) (a : M) :
    a.1 ∉ P.submanifoldBoundary M ↔ P.subDegIndex hM.isSubMPolyfold a = 0 := by
  rw [MPolyfold.mem_submanifoldBoundary_iff_subDegIndex hM a.2, not_le, Nat.lt_one_iff]

theorem A_to_BRepaired : A → BRepaired := by
  intro hA Z _ _ _ P M x hM hx hb
  have h : (x ∈ P.boundary ∧ P.subDegIndex hM.isSubMPolyfold ⟨x, hx⟩ = 0) ↔
      P.IsTangentReducedAt M x := by
    have hb' : (⟨x, hx⟩ : M).1 ∈ P.boundary := hb
    exact hA.2.2.2.2.2.2.2.2.1 hM hb'
  rw [← h, not_mem_submanifoldBoundary_iff hM ⟨x, hx⟩]

/-- `BRepaired` in the project's form, at `a ∈ M ∩ ∂X`. -/
theorem BRepaired_iff (hB : BRepaired) {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {P : MPolyfold Z} {M : Set Z} (hM : P.IsSmoothSubmanifold M) (a : M)
    (hb : a.1 ∈ P.boundary) :
    (a.1 ∈ P.boundary ∧ P.subDegIndex hM.isSubMPolyfold a = 0) ↔ P.IsTangentReducedAt M a := by
  rw [← not_mem_submanifoldBoundary_iff hM a]
  exact hB Z P M a.1 hM a.2 hb

/-- The four main conjuncts of `A` (`lemma_9_2_13`, `lemma_9_2_13_two_one`, `lemma_9_2_13_iff`,
`subDegIndex_eq_zero_iff`) from `BRepaired`. -/
theorem BRepaired_gives_main (hB : BRepaired) :
    (type_of% @Polyfold.MPolyfold.lemma_9_2_13.{0}) ∧
    (type_of% @Polyfold.MPolyfold.lemma_9_2_13_two_one.{0}) ∧
    (type_of% @Polyfold.MPolyfold.lemma_9_2_13_iff.{0}) ∧
    (type_of% @Polyfold.MPolyfold.subDegIndex_eq_zero_iff.{0}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z _ _ _ P M hM a h
    exact (BRepaired_iff hB hM a h.1).1 h
  · intro Z _ _ _ P M hM a hb h
    exact (BRepaired_iff hB hM a hb).2 h
  · intro Z _ _ _ P M hM a hb
    exact BRepaired_iff hB hM a hb
  · intro Z _ _ _ P M hM a
    by_cases hb : a.1 ∈ P.boundary
    · exact ⟨fun h0 => (BRepaired_iff hB hM a hb).1 ⟨hb, h0⟩,
        fun h => ((BRepaired_iff hB hM a hb).2 h).2⟩
    · exact iff_of_true (subDegIndex_eq_zero_of_not_mem_boundary hM hb)
        (isTangentReducedAt_of_not_mem_boundary hM hb)

#rt_check RoundTrip.V9_24.not_B [Polyfold.isReducedTangentAt_iff_subset_reduced,
  Polyfold.isReducedTangentAt_iff_subset_partialCone, Polyfold.MPolyfold.subDegIndex_le,
  Polyfold.MPolyfold.isReducedTangentAt_chart_change,
  Polyfold.MPolyfold.isTangentReducedAt_iff_forall, Polyfold.MPolyfold.lemma_9_2_13_chart,
  Polyfold.MPolyfold.lemma_9_2_13, Polyfold.MPolyfold.lemma_9_2_13_two_one,
  Polyfold.MPolyfold.lemma_9_2_13_iff, Polyfold.MPolyfold.subDegIndex_eq_zero_iff,
  Polyfold.ScRetraction.IsScPlus.exists_injOn_proj, Polyfold.ScRetraction.IsScPlus.exists_flat,
  Polyfold.MPolyfold.not_lemma_9_2_13_two_one]
#rt_check RoundTrip.V9_24.B_to_A [Polyfold.isReducedTangentAt_iff_subset_reduced,
  Polyfold.isReducedTangentAt_iff_subset_partialCone, Polyfold.MPolyfold.subDegIndex_le,
  Polyfold.MPolyfold.isReducedTangentAt_chart_change,
  Polyfold.MPolyfold.isTangentReducedAt_iff_forall, Polyfold.MPolyfold.lemma_9_2_13_chart,
  Polyfold.MPolyfold.lemma_9_2_13, Polyfold.MPolyfold.lemma_9_2_13_two_one,
  Polyfold.MPolyfold.lemma_9_2_13_iff, Polyfold.MPolyfold.subDegIndex_eq_zero_iff,
  Polyfold.ScRetraction.IsScPlus.exists_injOn_proj, Polyfold.ScRetraction.IsScPlus.exists_flat,
  Polyfold.MPolyfold.not_lemma_9_2_13_two_one]
#rt_check RoundTrip.V9_24.A_to_BRepaired [Polyfold.isReducedTangentAt_iff_subset_reduced,
  Polyfold.isReducedTangentAt_iff_subset_partialCone, Polyfold.MPolyfold.subDegIndex_le,
  Polyfold.MPolyfold.isReducedTangentAt_chart_change,
  Polyfold.MPolyfold.isTangentReducedAt_iff_forall, Polyfold.MPolyfold.lemma_9_2_13_chart,
  Polyfold.MPolyfold.lemma_9_2_13, Polyfold.MPolyfold.lemma_9_2_13_two_one,
  Polyfold.MPolyfold.lemma_9_2_13_iff, Polyfold.MPolyfold.subDegIndex_eq_zero_iff,
  Polyfold.ScRetraction.IsScPlus.exists_injOn_proj, Polyfold.ScRetraction.IsScPlus.exists_flat,
  Polyfold.MPolyfold.not_lemma_9_2_13_two_one]
#rt_check RoundTrip.V9_24.BRepaired_gives_main [Polyfold.isReducedTangentAt_iff_subset_reduced,
  Polyfold.isReducedTangentAt_iff_subset_partialCone, Polyfold.MPolyfold.subDegIndex_le,
  Polyfold.MPolyfold.isReducedTangentAt_chart_change,
  Polyfold.MPolyfold.isTangentReducedAt_iff_forall, Polyfold.MPolyfold.lemma_9_2_13_chart,
  Polyfold.MPolyfold.lemma_9_2_13, Polyfold.MPolyfold.lemma_9_2_13_two_one,
  Polyfold.MPolyfold.lemma_9_2_13_iff, Polyfold.MPolyfold.subDegIndex_eq_zero_iff,
  Polyfold.ScRetraction.IsScPlus.exists_injOn_proj, Polyfold.ScRetraction.IsScPlus.exists_flat,
  Polyfold.MPolyfold.not_lemma_9_2_13_two_one]
#rt_overlap RoundTrip.V9_24.not_B [Polyfold.isReducedTangentAt_iff_subset_reduced,
  Polyfold.isReducedTangentAt_iff_subset_partialCone, Polyfold.MPolyfold.subDegIndex_le,
  Polyfold.MPolyfold.isReducedTangentAt_chart_change,
  Polyfold.MPolyfold.isTangentReducedAt_iff_forall, Polyfold.MPolyfold.lemma_9_2_13_chart,
  Polyfold.MPolyfold.lemma_9_2_13, Polyfold.MPolyfold.lemma_9_2_13_two_one,
  Polyfold.MPolyfold.lemma_9_2_13_iff, Polyfold.MPolyfold.subDegIndex_eq_zero_iff,
  Polyfold.ScRetraction.IsScPlus.exists_injOn_proj, Polyfold.ScRetraction.IsScPlus.exists_flat,
  Polyfold.MPolyfold.not_lemma_9_2_13_two_one]
#rt_overlap RoundTrip.V9_24.BRepaired_gives_main [Polyfold.isReducedTangentAt_iff_subset_reduced,
  Polyfold.isReducedTangentAt_iff_subset_partialCone, Polyfold.MPolyfold.subDegIndex_le,
  Polyfold.MPolyfold.isReducedTangentAt_chart_change,
  Polyfold.MPolyfold.isTangentReducedAt_iff_forall, Polyfold.MPolyfold.lemma_9_2_13_chart,
  Polyfold.MPolyfold.lemma_9_2_13, Polyfold.MPolyfold.lemma_9_2_13_two_one,
  Polyfold.MPolyfold.lemma_9_2_13_iff, Polyfold.MPolyfold.subDegIndex_eq_zero_iff,
  Polyfold.ScRetraction.IsScPlus.exists_injOn_proj, Polyfold.ScRetraction.IsScPlus.exists_flat,
  Polyfold.MPolyfold.not_lemma_9_2_13_two_one]

end RoundTrip.V9_24
