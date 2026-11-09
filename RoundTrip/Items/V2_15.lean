import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_15

/-! Round trip for V2_15 (Lemma 2.15: the inclusions `X_{m+1} → X_m` are continuous).

`A` is the type of `Polyfold.lemma_2_3_9`, universe instantiated at `0` (B lives in `Type`).
`MPolyfold.levelIncl` is a definition (vocabulary), used verbatim by B.

The two statements are the same up to the binder kinds of `X`, `P`: `lemma_2_3_9` takes the space
implicitly, B explicitly. -/

namespace RoundTrip.V2_15
open Polyfold

/-- The project's statement (Lemma 2.15), universe instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.lemma_2_3_9.{0}

theorem A_holds : A := @Polyfold.lemma_2_3_9.{0}

theorem A_to_B : A → B := by
  intro hA X _ _ _ P m
  exact hA P m

theorem B_to_A : B → A := by
  intro hB X _ _ _ P m
  exact hB X P m

#rt_check RoundTrip.V2_15.A_to_B [Polyfold.lemma_2_3_9]
#rt_check RoundTrip.V2_15.B_to_A [Polyfold.lemma_2_3_9]
#rt_overlap RoundTrip.V2_15.B_to_A [Polyfold.lemma_2_3_9]

end RoundTrip.V2_15
