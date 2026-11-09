import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_35

/-!
Round trip for V4_35 (Proposition 4.15 (3)).  `A` is the type of
`Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_three`, universe instantiated at `0`.

Glue: B's `IsSmoothSubmanifoldB` is the project's `IsSmoothSubmanifold` (`smooth_iff`, copied
from V4_33); the induced structure `subPolyfold` does not depend on the proof of
`IsSubMPolyfold` (proof irrelevance); `MPolyfold.boundary` is by definition `{x | 1 ≤ degIndex x}`.
-/

namespace RoundTrip.V4_35
open Polyfold

def A : Prop := type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_three.{0}

theorem A_holds : A := @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_three.{0}

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9/V4_33). -/
theorem retractionOn_iff (P : MPolyfold X) (r : X → X) (V : Set X) :
    P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V := by
  constructor
  · intro h
    refine ⟨h.isScSmoothOn.isOpen, h.isScSmoothOn, h.mapsTo, h.idem, h.mem_levelSet,
      fun g hg => ?_⟩
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact MPolyfold.IsScSmoothOn.of_exists_charts h.isScSmoothOn.isOpen
        (fun y _ => (IsEmpty.false y).elim) (fun y _ => (IsEmpty.false y).elim)
    · refine (h.isScSmoothOn_one (g x)).congr fun y hy => ?_
      change P.toLevelOne (g x) (r y) = g y
      rw [← hg y hy, MPolyfold.toLevelOne_levelVal]
  · rintro ⟨-, h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun x₀ =>
      h5 _ fun x hx => MPolyfold.levelVal_toLevelOne x₀ (h4 x hx)⟩

/-- Definition 4.13: the project's notion is B's (V4_29/V4_33). -/
theorem smooth_iff (P : MPolyfold X) (S : Set X) :
    P.IsSmoothSubmanifold S ↔ IsSmoothSubmanifoldB P S := by
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, s, hs, himg⟩ := h a ha
    exact ⟨V, s, hV, haV, (retractionOn_iff P s V).1 hs, himg⟩
  · intro h a ha
    obtain ⟨V, s, hV, haV, hs, himg⟩ := h a ha
    exact ⟨V, hV, haV, s, (retractionOn_iff P s V).2 hs, himg⟩

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ P S hS hsub _ a ha
  have hS' : P.IsSmoothSubmanifold S := (smooth_iff P S).2 hS
  exact hA hS' ⟨a, ha, rfl⟩

theorem B_to_A : B → A := by
  rintro hB X _ _ _ P S hS _ _ ⟨a, ha, rfl⟩
  exact hB X P S ((smooth_iff P S).1 hS) hS.isSubMPolyfold inferInstance a ha

#rt_check RoundTrip.V4_35.A_to_B [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_three]
#rt_check RoundTrip.V4_35.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_three]
#rt_overlap RoundTrip.V4_35.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_three]

end RoundTrip.V4_35
