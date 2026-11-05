import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_9

/-!
Round trip for V4_9 (Definition 4.4, sc⁺-retractions).  The decls list two definitions
(`ScRetraction.IsScPlus`, `MPolyfold.IsScPlusRetractionOn`, vocabulary) and one theorem, so `A` is
the type of `Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ` (no universe parameters).  `B` states
that both project definitions agree with the blind ones.

Glue:
* `ScRetraction.IsScPlus R = IsScPlus R.U R` (lift `E.liftOne ∘ R`, sc-smooth into `E¹`); B asks
  for `r(U_m) ⊆ E_{m+1}` and SOME sc-smooth lift `g : E₀ → E¹ = E₁`.  `IsScPlus.iff_exists`
  converts the lifts; `r(U_m) ⊆ E_{m+1}` is A.
* `IsScPlusRetractionOn`: B's `IsOpen V` is the `isOpen` field of `IsScSmoothOn`; the project
  quantifies over junk values `x₀` of `1₀¹ = toLevelOne x₀`, B over all lifts `g : X → X₁` of `r`
  on `V`.  On `V` every lift equals `toLevelOne x₀ ∘ r` (`toLevelOne_levelVal`), and
  `toLevelOne x₀ ∘ r` is a lift (`levelVal_toLevelOne`); for `X = ∅` both are vacuous.
-/

namespace RoundTrip.V4_9
open Polyfold

def A : Prop := type_of% @Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ

theorem A_holds : A := @Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The M-polyfold half of B (does not involve A). -/
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

end Glue

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun E C R => ?_, fun X _ _ _ P r V => retractionOn_iff P r V⟩
  constructor
  · intro hR
    refine ⟨fun m x hx => ?_, E.liftOne ∘ R, fun x hx => IsScPlus.toBase_lift hR hx,
      hR.isScSmooth_lift⟩
    obtain ⟨y, -, hy⟩ := hA hR m hx
    exact ⟨y, hy⟩
  · rintro ⟨-, g, hg, hgs⟩
    exact (IsScPlus.iff_exists R.isScDomain).2 ⟨g, hgs, hg⟩

theorem B_to_A : B → A := by
  rintro ⟨hB, -⟩ E C R hR m x hx
  obtain ⟨y, hy⟩ := ((hB E C R).1 hR).1 m x hx
  refine ⟨y, ?_, hy⟩
  rw [ScBanach.mem_lvlSet]
  rw [hy]
  exact R.mapsTo hx

#rt_check RoundTrip.V4_9.A_to_B [Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ]
#rt_check RoundTrip.V4_9.B_to_A [Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ]
#rt_overlap RoundTrip.V4_9.B_to_A [Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ]

end RoundTrip.V4_9
