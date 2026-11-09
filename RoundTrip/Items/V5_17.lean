import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_17

namespace RoundTrip.V5_17
open Polyfold Filter Topology

/-- The project's statement (Propositions 5.30 and 5.10), universe instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.proposition_5_5_3.{0} ∧ type_of% @Polyfold.proposition_5_3_2.{0}

theorem A_holds : A := ⟨@Polyfold.proposition_5_5_3.{0}, @Polyfold.proposition_5_3_2.{0}⟩

/-- `B ⇒ A`: A's hypothesis `AdmitsBumpFunctions` (`f(x) ≠ 0`) implies B's
`AdmitsBumpFunctionsWeak` (`AdmitsBumpFunctions.weak`, not one of the item's theorems); the
conclusions are identical. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ _ _ {PX} h {x} {U} hU hx => hB X PX h.weak x U hU hx,
    fun {X} _ _ _ {PX} h {x} {U} hU hx => hB X PX h.weak x U hU hx⟩

/-- The intended comparison: A is exactly B's `BStrong` (the same claim under the pointwise
hypothesis). -/
theorem A_to_BStrong : A → BStrong := by
  intro hA X _ _ _ PX h x U hU hx
  exact hA.1 h hU hx

theorem BStrong_to_A : BStrong → A := by
  intro hB
  exact ⟨fun {X} _ _ _ {PX} h {x} {U} hU hx => hB X PX h x U hU hx,
    fun {X} _ _ _ {PX} h {x} {U} hU hx => hB X PX h x U hU hx⟩

/-! `A ⇒ B` is not proved: B assumes only `AdmitsBumpFunctionsWeak` (for every `x` and open
`U ∋ x` an sc-smooth bump not identically zero with support in `U`), A assumes
`AdmitsBumpFunctions` (a bump with `f(x) ≠ 0`).  Deriving A's hypothesis from B's would need a
bump that is non-zero AT the given point from bumps that are only non-zero somewhere near it; on
an M-polyfold there are no translations (translation by a non-smooth point is not even sc⁰ on the
levels), so this is a genuine gap, not glue.  Whether B itself holds in general is unclear. -/

#rt_check RoundTrip.V5_17.B_to_A [Polyfold.proposition_5_5_3, Polyfold.proposition_5_3_2]
#rt_check RoundTrip.V5_17.A_to_BStrong [Polyfold.proposition_5_5_3, Polyfold.proposition_5_3_2]
#rt_check RoundTrip.V5_17.BStrong_to_A [Polyfold.proposition_5_5_3, Polyfold.proposition_5_3_2]
#rt_overlap RoundTrip.V5_17.B_to_A [Polyfold.proposition_5_5_3, Polyfold.proposition_5_3_2]

end RoundTrip.V5_17
