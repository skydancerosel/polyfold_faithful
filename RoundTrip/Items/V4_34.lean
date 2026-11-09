import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_34

/-!
Round trip for V4_34 (Proposition 4.15 (2)).  `A` is the type of
`Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_two`, universe instantiated at `0`.

Glue:
* B's `IsSmoothSubmanifoldB` is the project's `IsSmoothSubmanifold` (`smooth_iff`, copied from
  V4_33: the sc⁺-retraction notions agree).
* B's `IsLocallyClosedB` (the text's definition: every `a ∈ A` has an open `V ∋ a` with
  `V ∩ closure A ⊆ A`) is Mathlib's `IsLocallyClosed` (the project's choice), through
  `isLocallyClosed_tfae` (item 3, `∀ x ∈ s, ∃ U, x ∈ U ∧ IsOpen U ∧ U ∩ closure s ⊆ s`) and
  `mem_closure_iff`.
-/

namespace RoundTrip.V4_34
open Polyfold

def A : Prop := type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_two.{0}

theorem A_holds : A := @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_two.{0}

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

/-- The text's "locally closed" is Mathlib's. -/
theorem isLocallyClosedB_iff {X : Type} [TopologicalSpace X] (S : Set X) :
    IsLocallyClosedB S ↔ IsLocallyClosed S := by
  refine Iff.trans ?_ ((isLocallyClosed_tfae S).out 0 3).symm
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, hcl⟩ := h a ha
    refine ⟨V, haV, hV, fun b hb => hcl b hb.1 fun U hU hbU => ?_⟩
    have := mem_closure_iff.1 hb.2 U hU hbU
    exact this
  · intro h a ha
    obtain ⟨V, haV, hV, hcl⟩ := h a ha
    exact ⟨V, hV, haV, fun b hbV hb => hcl ⟨hbV, mem_closure_iff.2 fun U hU hbU => hb U hU hbU⟩⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ P S hS
  exact (isLocallyClosedB_iff S).2 (hA ((smooth_iff P S).2 hS))

theorem B_to_A : B → A := by
  intro hB X _ _ _ P S hS
  exact (isLocallyClosedB_iff S).1 (hB X P S ((smooth_iff P S).1 hS))

#rt_check RoundTrip.V4_34.A_to_B [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_two]
#rt_check RoundTrip.V4_34.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_two]
#rt_overlap RoundTrip.V4_34.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_2_3_two]

end RoundTrip.V4_34
