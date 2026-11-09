import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_20

/-! Round trip for V9_20 (Lemma 9.2.7 (1), p. 412 of the 2021 book; 2017: Lemma 9.5 (1)):
`S^g_Θ` open and dense, `S^b_Θ` closed and nowhere dense in `supp(Θ)`.

`A` is the conjunction of the types of the four listed theorems, universe instantiated at `0`
(`B` lives in `Type`): `EpGroupoid.lemma_9_2_7_1` (open / closed), `EpGroupoid.dense_goodSet`,
`EpGroupoid.isNowhereDense_badSet`, `EpGroupoid.lemma_9_2_7_1_dense`.  None of them has a
dimension hypothesis.

* `A_to_B`: B's `IsGoodAt` is the project's `IsGoodPoint` (`⋃ i, M i` is `MU`, `Mᵢ ∩ V` vs.
  `V ∩ Mᵢ`), so B's `Sg`, `Sb` are the preimages in `↥(supp Θ)` of `goodSet`, `badSet`
  (`Sg_eq`, `Sb_eq`); B's equidimensionality hypothesis is not needed.
* `B_to_A` is not proved: B only covers equidimensional `Θ` (`∃ n, IsNDimensional Θ n`), while
  every conjunct of `A` holds for every branched ep⁺-subgroupoid. -/

namespace RoundTrip.V9_20
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_9_2_7_1.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.dense_goodSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isNowhereDense_badSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_2_7_1_dense.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.lemma_9_2_7_1.{0}, @Polyfold.EpGroupoid.dense_goodSet.{0},
    @Polyfold.EpGroupoid.isNowhereDense_badSet.{0}, @Polyfold.EpGroupoid.lemma_9_2_7_1_dense.{0}⟩

section glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ}

/-- B's good point is the project's `IsGoodPoint`. -/
theorem isGoodAt_iff {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) :
    IsGoodAt B y ↔ B.IsGoodPoint y := by
  unfold IsGoodAt EpGroupoid.LocalBranchingStructure.IsGoodPoint
  refine and_congr Iff.rfl (exists_congr fun V => and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr Iff.rfl ?_)))
  refine ⟨fun h i j hi hj => ?_, fun h i j hij => ?_⟩
  · rw [inter_comm, h i j ⟨hi, hj⟩, inter_comm]
  · rw [inter_comm, h i j hij.1 hij.2, inter_comm]

theorem Sg_eq : Sg X Θ = ((↑) ⁻¹' X.goodSet Θ : Set (EpGroupoid.supp Θ)) := by
  ext y
  simp only [Sg, IsGoodPt, mem_ofPred_eq, mem_preimage, EpGroupoid.goodSet, isGoodAt_iff]
  exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

theorem Sb_eq : Sb X Θ = ((↑) ⁻¹' X.badSet Θ : Set (EpGroupoid.supp Θ)) := by
  ext y
  simp only [Sb, IsGoodPt, mem_ofPred_eq, mem_preimage, EpGroupoid.badSet, Set.mem_sdiff,
    EpGroupoid.goodSet, isGoodAt_iff]
  exact ⟨fun h => ⟨y.2, fun h' => h h'.2⟩, fun h h' => h.2 ⟨y.2, h'⟩⟩

end glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X Θ hΘ _
  rw [Sg_eq, Sb_eq]
  exact ⟨(hA.1 hΘ).1, (hA.2.2.2 hΘ).1, (hA.1 hΘ).2, (hA.2.2.2 hΘ).2⟩

#rt_check RoundTrip.V9_20.A_to_B [Polyfold.EpGroupoid.lemma_9_2_7_1,
  Polyfold.EpGroupoid.dense_goodSet, Polyfold.EpGroupoid.isNowhereDense_badSet,
  Polyfold.EpGroupoid.lemma_9_2_7_1_dense]
#rt_overlap RoundTrip.V9_20.A_to_B [Polyfold.EpGroupoid.lemma_9_2_7_1,
  Polyfold.EpGroupoid.dense_goodSet, Polyfold.EpGroupoid.isNowhereDense_badSet,
  Polyfold.EpGroupoid.lemma_9_2_7_1_dense]

end RoundTrip.V9_20
