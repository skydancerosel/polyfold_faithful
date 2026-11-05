import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_2

/-! Round trip for V2_2 (Definition 2.3: sc-smooth retracts).

`A` is the conjunction of the types of `Polyfold.ScRetraction.isScRetract` and
`Polyfold.IsRelOpenInQuadrant.isScRetract` (no universe parameters: `ScBanach` lives in `Type`).
`IsScRetract`, `ScRetraction.id` and `LocalModel` are definitions (vocabulary).

The item is a definition.  B says that the project's `IsScRetract E C O`
(`∃ R : ScRetraction E C, R.retract = O`) is B's `IsScRetractB` (`∃ U r`, `r` an sc-smooth
retraction on `U`, `O = r(U)`), and that every `LocalModel` is a retract in B's sense.  Both are
definitional: `A → B` is proved outright (the hypothesis is not needed).

`B → A`: `ScRetraction.isScRetract` and `IsRelOpenInQuadrant.isScRetract` are obtained from B's
characterisation (the second with the identity retraction, sc-smooth by the project lemma
`isScSmooth_id`). -/

namespace RoundTrip.V2_2
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScRetraction.isScRetract) ∧
    (type_of% @Polyfold.IsRelOpenInQuadrant.isScRetract)

theorem A_holds : A :=
  ⟨@Polyfold.ScRetraction.isScRetract, @Polyfold.IsRelOpenInQuadrant.isScRetract⟩

/-- The project's `IsScRetract` is B's notion (definitional). -/
theorem isScRetract_iff (E : ScBanach) (C O : Set (E.lvl 0)) :
    IsScRetract E C O ↔ IsScRetractB E C O := by
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨R.U, R.toFun, ⟨R.relOpen, R.mapsTo, R.isScSmooth, R.idem⟩, rfl⟩
  · rintro ⟨U, r, ⟨h1, h2, h3, h4⟩, rfl⟩
    exact ⟨⟨U, r, h1, h2, h3, h4⟩, rfl⟩

theorem A_to_B : A → B := by
  intro _
  exact ⟨isScRetract_iff, fun M => (isScRetract_iff M.E M.C M.O).1 M.isScRetract⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro E C R
    exact (hB.1 E C R.retract).2
      ⟨R.U, R.toFun, ⟨R.relOpen, R.mapsTo, R.isScSmooth, R.idem⟩, rfl⟩
  · intro E C U hU
    exact (hB.1 E C U).2
      ⟨U, _root_.id, ⟨hU, mapsTo_id U, isScSmooth_id hU.isScDomain, fun _ _ => rfl⟩,
        (image_id U).symm⟩

#rt_check RoundTrip.V2_2.A_to_B [Polyfold.ScRetraction.isScRetract,
  Polyfold.IsRelOpenInQuadrant.isScRetract]
#rt_check RoundTrip.V2_2.B_to_A [Polyfold.ScRetraction.isScRetract,
  Polyfold.IsRelOpenInQuadrant.isScRetract]
#rt_overlap RoundTrip.V2_2.B_to_A [Polyfold.ScRetraction.isScRetract,
  Polyfold.IsRelOpenInQuadrant.isScRetract]

end RoundTrip.V2_2
