import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_42

/-!
Round trip for V7_42 (Theorem 7.2: `|X|` is locally metrizable, regular, Hausdorff, and
metrizable when paracompact).

`A` is the conjunction of the types of the three listed theorems, universes at `0`
(`Obj Mor : Type`; `metrizableSpace_of_locally` has one universe, also at `0`):
* `EpGroupoid.theorem_7_3_1`: `|X|` is locally metrizable (every point has an open neighbourhood
  with metrizable subspace topology), `RegularSpace`, `T2Space`;
* `EpGroupoid.theorem_7_3_1_metrizable`: `ParacompactSpace |X| → MetrizableSpace |X|`;
* `metrizableSpace_of_locally` (Part I, Smirnov's theorem): every paracompact Hausdorff locally
  metrizable space (in `Type`) is metrizable.

`B`: B's `LocallyMetrizable`, the text's regularity `IsRegularText`, `T2Space`, and
`ParacompactSpace → MetrizableSpace`, for `|X|`.

`A ⇒ B`: the first two theorems, with Mathlib's `RegularSpace` = the text's regularity
(`regular_iff_text`; the empty closed set is automatic, `𝓝ˢ ∅ = ⊥`).  `B ⇒ A`: the first two
conjuncts from B (`B_to_A_core`).  The third conjunct of `A` is a general metrization theorem,
not a statement about ep-groupoids, and B (about orbit spaces only) cannot give it; it is proved
outright, without B, from the project's Part I lemma `metrizableSpace_of_pullback` (applied to
`id`), which is the project's own one-line proof of `metrizableSpace_of_locally` (the banned
theorem itself is not used).  So that conjunct of `B ⇒ A` is vacuous for the audit.
-/

namespace RoundTrip.V7_42
open Polyfold Set Filter Topology

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.theorem_7_3_1.{0} ∧
  type_of% @Polyfold.EpGroupoid.theorem_7_3_1_metrizable.{0} ∧
  type_of% @Polyfold.metrizableSpace_of_locally.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.theorem_7_3_1, @EpGroupoid.theorem_7_3_1_metrizable, @metrizableSpace_of_locally⟩

/-- Mathlib's regularity is the text's. -/
theorem regular_iff_text (Y : Type) [TopologicalSpace Y] :
    RegularSpace Y ↔ IsRegularText Y := by
  constructor
  · intro h S _ hS z hz
    have hd : Disjoint (𝓝ˢ S) (𝓝 z) := RegularSpace.regular hS hz
    obtain ⟨V, ⟨hVo, hSV⟩, U, ⟨hzU, hUo⟩, hVU⟩ :=
      ((hasBasis_nhdsSet S).disjoint_iff (nhds_basis_opens z)).1 hd
    exact ⟨U, V, hUo, hVo, hzU, hSV, by rw [inter_comm]; exact hVU.inter_eq⟩
  · intro h
    refine ⟨fun {S z} hS hz => ?_⟩
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨U, V, hUo, hVo, hzU, hSV, hUV⟩ := h S hne hS z hz
    exact Filter.disjoint_iff.2 ⟨V, hVo.mem_nhdsSet.2 hSV, U, hUo.mem_nhds hzU,
      Set.disjoint_iff_inter_eq_empty.2 (by rw [inter_comm]; exact hUV)⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  obtain ⟨h1, h2, h3⟩ := hA.1 X
  exact ⟨h1, (regular_iff_text _).1 h2, h3, hA.2.1 X⟩

/-- The part of `A` about ep-groupoids follows from `B`. -/
theorem B_to_A_core : B →
    (type_of% @Polyfold.EpGroupoid.theorem_7_3_1.{0} ∧
      type_of% @Polyfold.EpGroupoid.theorem_7_3_1_metrizable.{0}) := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨h1, h2, h3, -⟩ := hB Obj Mor X
    exact ⟨h1, (regular_iff_text _).2 h2, h3⟩
  · intro Obj Mor _ _ _ _ _ _ X
    exact (hB Obj Mor X).2.2.2

/-- `B ⇒ A`; the last conjunct (Smirnov's theorem for arbitrary spaces) does not use `B`. -/
theorem B_to_A : B → A := fun hB =>
  ⟨(B_to_A_core hB).1, (B_to_A_core hB).2, fun {_} _ _ _ h =>
    metrizableSpace_of_pullback id continuous_id h⟩

#rt_check RoundTrip.V7_42.A_to_B [Polyfold.EpGroupoid.theorem_7_3_1,
  Polyfold.EpGroupoid.theorem_7_3_1_metrizable, Polyfold.metrizableSpace_of_locally]
#rt_check RoundTrip.V7_42.B_to_A [Polyfold.EpGroupoid.theorem_7_3_1,
  Polyfold.EpGroupoid.theorem_7_3_1_metrizable, Polyfold.metrizableSpace_of_locally]
#rt_check RoundTrip.V7_42.B_to_A_core [Polyfold.EpGroupoid.theorem_7_3_1,
  Polyfold.EpGroupoid.theorem_7_3_1_metrizable, Polyfold.metrizableSpace_of_locally]
#rt_overlap RoundTrip.V7_42.B_to_A [Polyfold.EpGroupoid.theorem_7_3_1,
  Polyfold.EpGroupoid.theorem_7_3_1_metrizable, Polyfold.metrizableSpace_of_locally]
#rt_overlap RoundTrip.V7_42.B_to_A_core [Polyfold.EpGroupoid.theorem_7_3_1,
  Polyfold.EpGroupoid.theorem_7_3_1_metrizable, Polyfold.metrizableSpace_of_locally]

end RoundTrip.V7_42
