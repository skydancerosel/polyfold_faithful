import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_40

/-!
Round trip for V4_40 (Definition 4.17).  The item lists only the definition
`Polyfold.MPolyfold.IsTameSubmanifold`, so `A = True`; the comparison is B itself (the project's
tame submanifolds are the text's), proved outright (`B_holds`).

`IsTameSubmanifold A := ∃ hA : IsSmoothSubmanifold A, (subPolyfold hA.isSubMPolyfold).IsTame`;
B's right-hand side is `∃ hA : IsSubMPolyfold A, (subPolyfold hA).IsTame`.  Under B's hypothesis
(`A` a smooth submanifold, `smooth_iff` of V4_33) the two agree: the induced structure does not
depend on the proof of `IsSubMPolyfold` (proof irrelevance).
-/

namespace RoundTrip.V4_40
open Polyfold

def A : Prop := True

theorem A_holds : A := trivial

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

/-- Definition 4.17: the project's notion is the text's. -/
theorem B_holds : B := by
  intro X _ _ _ P S _ hS
  constructor
  · rintro ⟨hS', htame⟩
    exact ⟨hS'.isSubMPolyfold, htame⟩
  · rintro ⟨_, htame⟩
    exact ⟨(smooth_iff P S).2 hS, htame⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V4_40.A_to_B []
#rt_check RoundTrip.V4_40.B_to_A []
#rt_overlap RoundTrip.V4_40.B_to_A []
#rt_check RoundTrip.V4_40.B_holds []

end RoundTrip.V4_40
