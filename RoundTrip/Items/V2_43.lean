import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_43

/-! Round trip for V2_43 (Definition 2.37: tame M-polyfolds).

`A` is the conjunction of the types of `Polyfold.MPolyfold.isChart_of_mem_equiv` and
`Polyfold.MPolyfold.IsTame.exists_chart`, universe instantiated at `0`.  `MPolyfold.IsTame` is a
definition (vocabulary).

The definitions agree (`B_holds`): the project's `IsTame` and B's `IsTameMB` are the same
existential, except that the project's `MAtlas.Equiv A B` ("some atlas `D` has chart set
`A ∪ B`") replaces B's `EquivB A B` ("all charts of `A ∪ B` are pairwise compatible"); these are
equivalent (`equivB_iff`, through the project's `MAtlas.equiv_iff`).  So `A → B` does not use A.

`B → A`: `IsTame.exists_chart` (a tame M-polyfold has, around every point, a chart of the structure
modelled on a tame retract) follows from B: B's atlas covers `x`, and B's pairwise compatibility
makes its charts compatible with the structure's atlas.  `isChart_of_mem_equiv` does not mention
tameness, so B does not bear on it; it is proved outright from `MAtlas.equiv_iff`. -/

namespace RoundTrip.V2_43
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.isChart_of_mem_equiv.{0}) ∧
    (type_of% @Polyfold.MPolyfold.IsTame.exists_chart.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isChart_of_mem_equiv.{0}, @Polyfold.MPolyfold.IsTame.exists_chart.{0}⟩

/-! ### Glue -/

/-- The project's equivalence of atlases is B's. -/
theorem equivB_iff {X : Type} [TopologicalSpace X] (A B : MAtlas X) : A.Equiv B ↔ EquivB A B := by
  constructor
  · rintro ⟨D, hD⟩ φ hφ ψ hψ
    exact D.compatible φ (hD ▸ hφ) ψ (hD ▸ hψ)
  · intro h
    exact (MAtlas.equiv_iff A B).2 fun φ hφ ψ hψ => h φ (Or.inl hφ) ψ (Or.inr hψ)

/-- B holds outright: the project's tame M-polyfolds are B's. -/
theorem B_holds : B := by
  intro X _ _ _ P
  exact exists_congr fun A => and_congr_left' (equivB_iff A P.atlas)

/-- `A → B`: B holds outright (A unused). -/
theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · -- `isChart_of_mem_equiv` (no tameness involved): outright
    intro X _ _ _ P A hA φ hφ ψ hψ
    exact (MAtlas.equiv_iff A P.atlas).1 hA φ hφ ψ hψ
  · -- `IsTame.exists_chart`, from B
    intro X _ _ _ P hP x
    obtain ⟨A, hA, htame⟩ := (hB X P).1 hP
    obtain ⟨φ, hφ, hx⟩ := A.cover x
    exact ⟨φ, fun ψ hψ => hA φ (Or.inl hφ) ψ (Or.inr hψ), hx, htame φ hφ⟩

#rt_check RoundTrip.V2_43.A_to_B [Polyfold.MPolyfold.isChart_of_mem_equiv,
  Polyfold.MPolyfold.IsTame.exists_chart]
#rt_check RoundTrip.V2_43.B_to_A [Polyfold.MPolyfold.isChart_of_mem_equiv,
  Polyfold.MPolyfold.IsTame.exists_chart]
#rt_overlap RoundTrip.V2_43.B_to_A [Polyfold.MPolyfold.isChart_of_mem_equiv,
  Polyfold.MPolyfold.IsTame.exists_chart]

end RoundTrip.V2_43
