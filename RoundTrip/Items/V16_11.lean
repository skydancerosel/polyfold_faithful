import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_11

set_option maxSynthPendingDepth 3

/-! Round trip for V16_11 (2021 Lemma 16.1.19, p. 714; 2017: Lemma 16.2: tameness is invariant).

`A` is the type of `PolyfoldStructure.lemma_16_1_19` at universe `0` (`Z : Type`): for equivalent
polyfold structures `p ∼ q`, `X` tame iff `Y` tame.  `B` is the one-directional form (the text:
if `X` is tame, so is `Y`).
* `A_to_B`: the forward half of the `↔`.
* `B_to_A`: the forward half is `B`; the backward half is `B` applied to `q ∼ p`
  (`Equiv.symm`, a non-item lemma). -/

namespace RoundTrip.V16_11
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Polyfold.PolyfoldStructure.lemma_16_1_19.{0}

theorem A_holds : A := @Polyfold.PolyfoldStructure.lemma_16_1_19.{0}

theorem A_to_B : A → B := fun hA _ _ _ _ h hs => (hA h).1 hs

theorem B_to_A : B → A := fun hB Z _ p q h => ⟨hB Z p q h, hB Z q p h.symm⟩

#rt_check RoundTrip.V16_11.A_to_B [Polyfold.PolyfoldStructure.lemma_16_1_19]
#rt_check RoundTrip.V16_11.B_to_A [Polyfold.PolyfoldStructure.lemma_16_1_19]
#rt_overlap RoundTrip.V16_11.B_to_A [Polyfold.PolyfoldStructure.lemma_16_1_19]

end RoundTrip.V16_11
