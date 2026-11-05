import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_58

/-!
Round trip for V5_58 (Proposition 5.38).  `A` is the type of `Polyfold.proposition_5_38`
(no universe parameter to instantiate: `LocalModel` has its levels in `Type`).

Both sides: for every local model `M`, if `E₀` admits `C^∞` partitions of unity (the project's
`AdmitsContDiffPartitionsOfUnity (M.E 0) ⊤`) then `M.HasApproxProperty`.  B writes `M.E.lvl 0`
for the project's `M.E 0` (the coercion of `ScBanach` to its level function), so the two
statements are the same up to unfolding.
-/

namespace RoundTrip.V5_58
open Polyfold

/-- The project's statement. -/
def A : Prop := type_of% @Polyfold.proposition_5_38

theorem A_holds : A := @Polyfold.proposition_5_38

theorem A_to_B : A → B := fun hA M hM => hA M hM

theorem B_to_A : B → A := fun hB M hM => hB M hM

#rt_check RoundTrip.V5_58.A_to_B [Polyfold.proposition_5_38]
#rt_check RoundTrip.V5_58.B_to_A [Polyfold.proposition_5_38]
#rt_overlap RoundTrip.V5_58.B_to_A [Polyfold.proposition_5_38]

end RoundTrip.V5_58
