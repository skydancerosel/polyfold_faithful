import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_49

/-! Round trip for V9_49 (Definition 9.5.1, 2021 p. 437; 2017: Definition 9.15): sets of
measure zero in `S = |supp(Θ)|`.

`A` is the conjunction of the types of the four listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `SheetNullSets.isNull_union`, `SheetNullSets.isNull_iUnion_countable`,
`SheetNullSets.isNull_of_cover` and `LocalBranchingStructure.hasNullPreimages_iff_isNullIn`.  The
listed definitions (`SheetNullSets`, `SheetMeasureGeometry`, `toSheetNullSets`,
`HasNullPreimages`, `HasTameSheetsIn`, `IsMeasureZeroSupp`, `IsMeasureZeroSuppAny`,
`IsMeasureZeroSuppAll`) are vocabulary.

`B` says that the project's `IsMeasureZeroSupp` is the blind reading `IsMeasureZeroB` of the
definition.  The comparison of the definitions is `B_holds`: for every ep-groupoid, every
`SheetNullSets` and every `A`, without the hypotheses of `B` (oriented, tame, compact,
`n`-dimensional, `A ⊆ S`), the two definitions agree, since the blind preimage
`{y ∈ Mᵢ | π(y) ∈ A ∩ π(M_U)}` is the project's `Mᵢ ∩ π⁻¹(A)` (`Mᵢ ⊆ M_U`); both ask for one tame
local branching structure at every `x ∈ supp(Θ)` with sheets in the class.

* `A → B` is `B_holds`; it does not use `A` (flagged).
* `B → A`: `A`'s four lemmas (σ-ideal and covering facts for an abstract `SheetNullSets`, and
  the translation of null preimages into §9.4's `IsNullIn`) are re-proved outright from the
  structure fields; they do not use `B` (flagged).  `B` contains nothing that implies them.
-/

namespace RoundTrip.V9_49
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SheetNullSets.isNull_union.{0}) ∧
  (type_of% @Polyfold.SheetNullSets.isNull_iUnion_countable.{0, 0}) ∧
  (type_of% @Polyfold.SheetNullSets.isNull_of_cover.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.LocalBranchingStructure.hasNullPreimages_iff_isNullIn.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SheetNullSets.isNull_union.{0}, @Polyfold.SheetNullSets.isNull_iUnion_countable.{0, 0},
    @Polyfold.SheetNullSets.isNull_of_cover.{0},
    @Polyfold.EpGroupoid.LocalBranchingStructure.hasNullPreimages_iff_isNullIn.{0}⟩

/-- **The definitions agree**: the project's `IsMeasureZeroSupp` is `IsMeasureZeroB`, for every
`A` and without `B`'s hypotheses. -/
theorem isMeasureZeroSupp_iff {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) {𝒮 : Set (Set Obj)} (G : SheetNullSets 𝒮) (Θ : Obj → ℚ)
    (A : Set X.OrbitSpace) : X.IsMeasureZeroSupp G Θ A ↔ IsMeasureZeroB X G Θ A := by
  have key : ∀ x (Bt : X.TameBranchingStructure Θ x) i,
      {y | y ∈ Bt.M i ∧ X.π y ∈ A ∩ X.π '' Bt.MU} = Bt.M i ∩ X.π ⁻¹' A := by
    intro x Bt i
    ext y
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, y, mem_iUnion.2 ⟨i, h1⟩, rfl⟩
  constructor
  · intro h x hx
    obtain ⟨Bt, hS, hN⟩ := h x hx
    exact ⟨Bt, hS, fun i => by rw [key]; exact hN i⟩
  · intro h x hx
    obtain ⟨Bt, hS, hN⟩ := h x hx
    exact ⟨Bt, hS, fun i => by rw [← key]; exact hN i⟩

theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X 𝒮 G Θ n _ _ _ _ _ A _
  exact isMeasureZeroSupp_iff X G Θ A

/-- `A → B`, without using `A`. -/
theorem A_to_B : A → B := fun _ => B_holds

/-! ### `A`, re-proved from the structure fields -/

theorem isNull_iUnion_countable' {X : Type} [TopologicalSpace X] {S : Set (Set X)}
    (G : SheetNullSets S) {κ : Type} [Countable κ] {N : Set X} {A : κ → Set X}
    (h : ∀ k, G.IsNull N (A k)) : G.IsNull N (⋃ k, A k) := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rw [iUnion_of_empty]
    exact G.isNull_empty N
  · obtain ⟨f, hf⟩ := exists_surjective_nat κ
    rw [← hf.iUnion_comp]
    exact G.isNull_iUnion fun n => h (f n)

/-- `B → A`, without using `B`. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X _ S G N A A' h h'
    rw [union_eq_iUnion]
    exact isNull_iUnion_countable' G fun b => by cases b <;> assumption
  · intro X _ S G κ _ N A h
    exact isNull_iUnion_countable' G h
  · intro X _ S G N C hN hC h
    refine G.isNull_of_local N hN C fun z hz => ?_
    obtain ⟨V, hV, hzV, κ, _, F, hFS, hcov, hnull⟩ := h z hz
    refine ⟨V, hV, hzV, G.isNull_mono (isNull_iUnion_countable' G (A := fun k => C ∩ F k)
      fun k => ?_) ?_⟩
    · exact G.isNull_transfer _ (hFS k) _ hN _ (fun w hw => ⟨hw.2, hC hw.1⟩) (hnull k)
    · intro w hw
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov hw)
      exact mem_iUnion.2 ⟨k, hw.1, hk⟩
  · intro Obj Mor _ _ _ _ _ _ X S Θ G x B hBS A
    refine ⟨fun h i => ?_, fun h => ⟨hBS, fun i => ?_⟩⟩
    · rw [inter_comm]; exact h.2 i
    · change G.IsNull _ _
      rw [inter_comm]; exact h i

#rt_check RoundTrip.V9_49.A_to_B [Polyfold.SheetNullSets.isNull_union,
  Polyfold.SheetNullSets.isNull_iUnion_countable, Polyfold.SheetNullSets.isNull_of_cover,
  Polyfold.EpGroupoid.LocalBranchingStructure.hasNullPreimages_iff_isNullIn]
#rt_check RoundTrip.V9_49.B_to_A [Polyfold.SheetNullSets.isNull_union,
  Polyfold.SheetNullSets.isNull_iUnion_countable, Polyfold.SheetNullSets.isNull_of_cover,
  Polyfold.EpGroupoid.LocalBranchingStructure.hasNullPreimages_iff_isNullIn]
#rt_overlap RoundTrip.V9_49.B_to_A [Polyfold.SheetNullSets.isNull_union,
  Polyfold.SheetNullSets.isNull_iUnion_countable, Polyfold.SheetNullSets.isNull_of_cover,
  Polyfold.EpGroupoid.LocalBranchingStructure.hasNullPreimages_iff_isNullIn]

end RoundTrip.V9_49
