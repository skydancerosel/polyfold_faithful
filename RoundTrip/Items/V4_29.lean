import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_29

/-!
Round trip for V4_29 (Definition 4.13, smooth finite-dimensional submanifolds).  The decls list
two definitions (`MPolyfold.IsSmoothSubmanifold`, `MPolyfold.SubmanifoldData`, plus the def
`SubmanifoldData.toSubData`; vocabulary) and two theorems, so `A` is the conjunction of the types
of `Polyfold.MPolyfold.isSmoothSubmanifold_iff` and
`Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold`, universe instantiated at `0`.
`B` states that the project's `IsSmoothSubmanifold` is the text's notion.

Glue: the project's `IsScPlusRetractionOn` and B's `IsScPlusRetractionOnB` agree
(`retractionOn_iff`, copied from V4_9): B's `IsOpen V` is the `isOpen` field of `IsScSmoothOn`;
the project quantifies over junk values `x₀` of `1₀¹ = toLevelOne x₀`, B over all lifts
`g : X → X₁` of `s` on `V`; on `V` they coincide.  With this, `IsSmoothSubmanifold` unfolds to
`IsSmoothSubmanifoldB` (the order of the existentials differs only).
-/

namespace RoundTrip.V4_29
open Polyfold

def A : Prop :=
  type_of% @Polyfold.MPolyfold.isSmoothSubmanifold_iff.{0} ∧
    type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isSmoothSubmanifold_iff.{0},
    @Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9). -/
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

/-- Definition 4.13: the project's notion is B's (this is B itself, proved from the
definitions). -/
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

/-- `A → B`: B is a statement about definitions only; it is proved outright from the definitions
(A, two lemmas about the project's notion, plays no role). -/
theorem A_to_B : A → B := fun _ _ _ _ _ P S => smooth_iff P S

/-- `B → A`: both conjuncts of A follow from B (which converts the project's notion into B's
explicit form) and the definitional agreement of sc⁺-retractions. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ _ _ {P} {S} => ?_, fun {X} _ _ _ {P} {S} hS => ?_⟩
  · rw [hB X P S]
    constructor
    · intro h a ha
      obtain ⟨V, s, hV, haV, hs, himg⟩ := h a ha
      exact ⟨⟨V, s, hV, (retractionOn_iff P s V).2 hs, himg⟩, haV⟩
    · intro h a ha
      obtain ⟨d, had⟩ := h a ha
      exact ⟨d.V, d.s, d.isOpen, had, (retractionOn_iff P d.s d.V).1 d.isScPlusRetractionOn,
        d.image⟩
  · have h := (hB X P S).1 hS
    intro a ha
    obtain ⟨V, s, hV, haV, ⟨-, h1, h2, h3, -, -⟩, himg⟩ := h a ha
    exact ⟨V, hV, haV, s, h2, h1, h3, himg⟩

#rt_check RoundTrip.V4_29.A_to_B [Polyfold.MPolyfold.isSmoothSubmanifold_iff,
  Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold]
#rt_check RoundTrip.V4_29.B_to_A [Polyfold.MPolyfold.isSmoothSubmanifold_iff,
  Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold]
#rt_overlap RoundTrip.V4_29.B_to_A [Polyfold.MPolyfold.isSmoothSubmanifold_iff,
  Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold]

end RoundTrip.V4_29
