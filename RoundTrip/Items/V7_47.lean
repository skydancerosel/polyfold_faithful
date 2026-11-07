import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_47

/-!
Round trip for V7_47 (Corollary 7.1: a second countable orbit space is metrizable).

`A` is the type of `Polyfold.EpGroupoid.corollary_7_1` at universe `0`: for every ep-groupoid
`X : EpGroupoid Obj Mor` (`Obj Mor : Type`) with `[SecondCountableTopology X.OrbitSpace]`,
`MetrizableSpace X.OrbitSpace`.  `B` is the same statement with the second countability as an
explicit hypothesis; both use Mathlib's `SecondCountableTopology` and `MetrizableSpace` on the
quotient topology of `X.OrbitSpace`.  The two are the same proposition up to the binder kind.
-/

namespace RoundTrip.V7_47
open Polyfold

/-- The project's Corollary 7.1, universes at `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.corollary_7_1.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.corollary_7_1.{0}

theorem A_to_B : A → B := fun hA _ _ _ _ _ _ _ _ X h => @hA _ _ _ _ _ _ _ _ X h

theorem B_to_A : B → A := fun hB {Obj Mor} _ _ _ _ _ _ X h => hB Obj Mor X h

#rt_check RoundTrip.V7_47.A_to_B [Polyfold.EpGroupoid.corollary_7_1]
#rt_check RoundTrip.V7_47.B_to_A [Polyfold.EpGroupoid.corollary_7_1]
#rt_overlap RoundTrip.V7_47.B_to_A [Polyfold.EpGroupoid.corollary_7_1]
#rt_overlap RoundTrip.V7_47.A_to_B [Polyfold.EpGroupoid.corollary_7_1]

end RoundTrip.V7_47
