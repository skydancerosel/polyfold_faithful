import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_11

/-! Round trip for V2_11 (Definition 2.12: sc-smooth atlases and their equivalence).

`A` is the conjunction of the types of `Polyfold.MAtlas.equiv_iff`, `Polyfold.MAtlas.Equiv.refl`,
`Polyfold.MAtlas.Equiv.symm` and (refresh 2026-11-02, added to the row) `Polyfold.MAtlas.Equiv.trans`,
`Polyfold.MAtlas.equivalence`, universe instantiated at `0` (B lives in `Type`).  `MAtlas` and
`MAtlas.Equiv` are definitions (vocabulary); B characterizes them.

The only gap between the project's `MAtlas` (compatibility for ALL pairs, including `φ = φ`) and
B's `Set.Pairwise` (distinct pairs) is self-compatibility, which is `MChart.compatible_self`
(item V2_10, not banned here).

Transitivity of atlas equivalence (the new conjuncts) is not in `B` (the text does not discuss it);
`B_to_A` gets it from `B`'s characterization of `Equiv` (pairwise compatibility) plus the project's
locality of compatibility `MChart.compatible_of_locally` (not banned here), exactly as the project
does: that lemma carries the mathematics of `trans`. -/

namespace RoundTrip.V2_11
open Polyfold Set

/-- The project's statement, universe instantiated at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.MAtlas.equiv_iff.{0}) ∧
    (type_of% @Polyfold.MAtlas.Equiv.refl.{0}) ∧
    (type_of% @Polyfold.MAtlas.Equiv.symm.{0}) ∧
    (type_of% @Polyfold.MAtlas.Equiv.trans.{0}) ∧
    (type_of% @Polyfold.MAtlas.equivalence.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MAtlas.equiv_iff.{0}, @Polyfold.MAtlas.Equiv.refl.{0},
    @Polyfold.MAtlas.Equiv.symm.{0}, @Polyfold.MAtlas.Equiv.trans.{0},
    @Polyfold.MAtlas.equivalence.{0}⟩

/-- The chart sets of project atlases are B's atlases. -/
theorem charts_iff {X : Type} [TopologicalSpace X] (S : Set (MChart X)) :
    (∃ A : MAtlas X, A.charts = S) ↔ IsAtlasB S := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨fun φ hφ ψ hψ _ => A.compatible φ hφ ψ hψ, A.cover⟩
  · rintro ⟨hpair, hcov⟩
    refine ⟨⟨S, fun φ hφ ψ hψ => ?_, hcov⟩, rfl⟩
    by_cases h : φ = ψ
    · subst h; exact MChart.compatible_self φ
    · exact hpair hφ hψ h

theorem A_to_B : A → B := by
  rintro ⟨hiff, -, -, -, -⟩ X _
  refine ⟨charts_iff, fun A A' => ?_⟩
  constructor
  · rintro ⟨D, hD⟩
    exact (charts_iff _).1 ⟨D, hD⟩
  · rintro ⟨hpair, -⟩
    refine (hiff A A').2 fun φ hφ ψ hψ => ?_
    by_cases h : φ = ψ
    · subst h; exact MChart.compatible_self φ
    · exact hpair (Or.inl hφ) (Or.inr hψ) h

/-- `equiv_iff` from `B`'s characterization of `Equiv`. -/
theorem equiv_iff_of_B (hB : B) : type_of% @Polyfold.MAtlas.equiv_iff.{0} := by
  intro X _ A A'
  rw [(hB X).2 A A']
  constructor
  · rintro ⟨hpair, -⟩ φ hφ ψ hψ
    by_cases h : φ = ψ
    · subst h; exact MChart.compatible_self φ
    · exact hpair (Or.inl hφ) (Or.inr hψ) h
  · intro h
    refine ⟨fun φ hφ ψ hψ _ => ?_, fun x => ?_⟩
    · rcases hφ with hφ | hφ <;> rcases hψ with hψ | hψ
      · exact A.compatible φ hφ ψ hψ
      · exact h φ hφ ψ hψ
      · exact (h ψ hψ φ hφ).symm
      · exact A'.compatible φ hφ ψ hψ
    · obtain ⟨φ, hφ, hx⟩ := A.cover x
      exact ⟨φ, Or.inl hφ, hx⟩

theorem refl_of_B (hB : B) : type_of% @Polyfold.MAtlas.Equiv.refl.{0} := by
  intro X _ A
  rw [(hB X).2 A A, union_self]
  exact ((hB X).1 A.charts).1 ⟨A, rfl⟩

theorem symm_of_B (hB : B) : type_of% @Polyfold.MAtlas.Equiv.symm.{0} := by
  intro X _ A A' h
  rw [(hB X).2] at h ⊢
  rwa [union_comm]

/-- `trans`: `B`'s pairwise-compatibility reading of `Equiv` plus the locality of compatibility
through the charts of the middle atlas (`MChart.compatible_of_locally`, a project lemma). -/
theorem trans_of_B (hB : B) : type_of% @Polyfold.MAtlas.Equiv.trans.{0} := by
  intro X _ A₁ A₂ A₃ h12 h23
  rw [equiv_iff_of_B hB] at h12 h23 ⊢
  intro φ hφ ψ hψ
  exact MChart.compatible_of_locally φ ψ A₂.charts (fun χ hχ => h12 φ hφ χ hχ)
    (fun χ hχ => h23 χ hχ ψ hψ) fun x _ => A₂.cover x

theorem B_to_A : B → A := fun hB =>
  ⟨equiv_iff_of_B hB, refl_of_B hB, symm_of_B hB, trans_of_B hB,
    fun {_} _ => ⟨refl_of_B hB, symm_of_B hB, trans_of_B hB⟩⟩

#rt_check RoundTrip.V2_11.A_to_B [Polyfold.MAtlas.equiv_iff, Polyfold.MAtlas.Equiv.refl,
  Polyfold.MAtlas.Equiv.symm, Polyfold.MAtlas.Equiv.trans, Polyfold.MAtlas.equivalence]
#rt_check RoundTrip.V2_11.B_to_A [Polyfold.MAtlas.equiv_iff, Polyfold.MAtlas.Equiv.refl,
  Polyfold.MAtlas.Equiv.symm, Polyfold.MAtlas.Equiv.trans, Polyfold.MAtlas.equivalence]
#rt_overlap RoundTrip.V2_11.B_to_A [Polyfold.MAtlas.equiv_iff, Polyfold.MAtlas.Equiv.refl,
  Polyfold.MAtlas.Equiv.symm, Polyfold.MAtlas.Equiv.trans, Polyfold.MAtlas.equivalence]

end RoundTrip.V2_11
