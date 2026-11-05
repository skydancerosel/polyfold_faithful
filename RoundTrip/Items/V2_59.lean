import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_59

/-! Round trip for V2_59 (Definition 2.52: sections, sc-smooth sections and sc⁺-sections of a
strong bundle).

`A` is the type of the theorem `StrongBundle.isScPlusSection_iff`, at universes `0, 0`.
`IsSection`, `StrongBundle.IsScSmoothSection`, `StrongBundle.localRepOne`,
`StrongBundle.IsScPlusSection` are definitions (vocabulary).

`A → B`: `IsSection` (`∀ x, P (f x) = x`) is B's `P ∘ f = id` by `funext`;
`IsScSmoothSection` is B's `IsScSmoothSectionB` (both: section and `PX.IsScSmoothMap
Bd.toMPolyfold0 f`); the project's chart-wise `IsScPlusSection` is B's "sc-smooth into `Y[1]`"
exactly by `isScPlusSection_iff` (the hypothesis), with `oneVal ∘ g = f` ↔ `∀ x, oneVal (g x) = f x`.

`B → A`: B's third equivalence, rewritten with its first, is `isScPlusSection_iff`. -/

namespace RoundTrip.V2_59
open Polyfold Set

/-- The project's statement (universes `0`). -/
def A : Prop := type_of% @Polyfold.StrongBundle.isScPlusSection_iff.{0, 0}

theorem A_holds : A := @Polyfold.StrongBundle.isScPlusSection_iff.{0, 0}

theorem isSection_iff {X Y : Type} (P : Y → X) (f : X → Y) : IsSection P f ↔ IsSectionB P f :=
  ⟨fun h => funext h, fun h x => congrFun h x⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ P _ _ _ _ Bd f
  refine ⟨isSection_iff P f, ?_, ?_⟩
  · exact ⟨fun ⟨h1, h2⟩ => ⟨(isSection_iff P f).1 h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨(isSection_iff P f).2 h1, h2⟩⟩
  · rw [hA Bd f]
    exact ⟨fun ⟨h1, g, hg, hs⟩ => ⟨(isSection_iff P f).1 h1, g, congrFun hg, hs⟩,
      fun ⟨h1, g, hg, hs⟩ => ⟨(isSection_iff P f).2 h1, g, funext hg, hs⟩⟩

theorem B_to_A : B → A := by
  intro hB X _ _ _ PX Y _ P _ _ _ _ Bd f
  obtain ⟨hsec, -, hplus⟩ := hB PX P Bd f
  rw [hplus, IsScPlusSectionB, ← hsec]
  exact ⟨fun ⟨h1, g, hg, hs⟩ => ⟨h1, g, funext hg, hs⟩,
    fun ⟨h1, g, hg, hs⟩ => ⟨h1, g, congrFun hg, hs⟩⟩

#rt_check RoundTrip.V2_59.A_to_B [Polyfold.StrongBundle.isScPlusSection_iff]
#rt_check RoundTrip.V2_59.B_to_A [Polyfold.StrongBundle.isScPlusSection_iff]
#rt_overlap RoundTrip.V2_59.B_to_A [Polyfold.StrongBundle.isScPlusSection_iff]

end RoundTrip.V2_59
