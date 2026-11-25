import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_54

set_option maxSynthPendingDepth 3

/-! Round trip for V16_54 (2021 Theorem 16.3.15, p. 727; 2017: Theorem 16.3).

`A` is the conjunction of the types of `StrongPolyfoldBundle.theorem_16_3_15_one` and
`theorem_16_3_15_two`, at universe `0` (B lives in `Type`).  Both sides use the same project
vocabulary (`HasReflexiveFibers`, `IsAuxNorm`, `IsReflexiveAuxNorm`, `Y01`), and `B` is literally
the conjunction of the two conclusions under the common hypothesis, so both directions are
repackaging. -/

namespace RoundTrip.V16_54
open Polyfold

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_15_one.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_15_two.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_3_15_one.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_3_15_two.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, h2⟩ Y Z _ _ p c hc
  exact ⟨h1 hc, fun n hn => h2 hc hn⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun hc => (hB _ hc).1, fun hc n hn => (hB _ hc).2 n hn⟩

/- The main conjunct is (2) together with (1); B is their conjunction, so the main comparison is
with the whole of `A`. -/
#rt_check RoundTrip.V16_54.A_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_3_15_one,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_15_two]
#rt_check RoundTrip.V16_54.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_3_15_one,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_15_two]
#rt_overlap RoundTrip.V16_54.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_3_15_one,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_15_two]

end RoundTrip.V16_54
