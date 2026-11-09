import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_6

namespace RoundTrip.V5_6
open Polyfold

/-- The project's statement (Proposition 5.3, comparison part), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.proposition_5_1_3_compare.{0, 0}

theorem A_holds : A := @Polyfold.proposition_5_1_3_compare.{0, 0}

/-- `A ⇒ B`: the same statement (same setting, same auxiliary norms, same inequalities). -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd N₀ N₁ h₀ h₁
  exact hA h₀ h₁

/-- `B ⇒ A`. -/
theorem B_to_A : B → A := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd N₀ N₁ h₀ h₁
  exact hB PX P Bd N₀ N₁ h₀ h₁

#rt_check RoundTrip.V5_6.A_to_B [Polyfold.proposition_5_1_3_compare]
#rt_check RoundTrip.V5_6.B_to_A [Polyfold.proposition_5_1_3_compare]
#rt_overlap RoundTrip.V5_6.B_to_A [Polyfold.proposition_5_1_3_compare]

end RoundTrip.V5_6
