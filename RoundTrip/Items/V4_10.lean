import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_10

/-!
Round trip for V4_10 (Lemma 4.5: being an sc⁺-retraction depends only on the retract).
`A` is the type of `Polyfold.lemma_4_5` (no universe parameters; `ScBanach` lives in `Type`).

Both statements are the same proposition up to the order of the bound variables and the
orientation of the equation of retracts (`T.retract = S.retract` in A, `s.retract = t.retract` in
B); both directions are a reshuffle.
-/

namespace RoundTrip.V4_10
open Polyfold

def A : Prop := type_of% @Polyfold.lemma_4_5

theorem A_holds : A := @Polyfold.lemma_4_5

theorem A_to_B : A → B := fun hA _ _ _ _ ht hst => hA ht hst.symm

theorem B_to_A : B → A := fun hB _ _ _ S hT hTS => hB _ _ _ S hT hTS.symm

#rt_check RoundTrip.V4_10.A_to_B [Polyfold.lemma_4_5]
#rt_check RoundTrip.V4_10.B_to_A [Polyfold.lemma_4_5]
#rt_overlap RoundTrip.V4_10.B_to_A [Polyfold.lemma_4_5]

end RoundTrip.V4_10
