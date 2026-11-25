import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_76

set_option maxSynthPendingDepth 3

/-! Round trip for V16_76 (2021 Theorem 16.6.4, p. 737; 2017: Theorem 16.7).

`A` is the type of `StrongPolyfoldBundle.theorem_16_6_4` at universe `0`:
`List.TFAE [HasCompactSolutionSet, IsProper, IsProperLtInfty]` for `s.1`, `s` an sc-Fredholm
section.  `B` is the same with the TFAE written as two `↔`; `(f : c.ScSection)` is `f.1`.
Both directions are `List.TFAE` bookkeeping. -/

namespace RoundTrip.V16_76
open Polyfold

def A : Prop := type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_4.{0}

theorem A_holds : A := @Polyfold.StrongPolyfoldBundle.theorem_16_6_4.{0}

theorem A_to_B : A → B := by
  intro h Y Z _ _ p c f
  have h' := h f
  exact ⟨h'.out 0 1, h'.out 1 2⟩

theorem B_to_A : B → A := by
  intro hB Y Z _ _ p c s
  obtain ⟨h12, h23⟩ := hB c s
  tfae_have 1 ↔ 2 := h12
  tfae_have 2 ↔ 3 := h23
  tfae_finish

#rt_check RoundTrip.V16_76.A_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_6_4]
#rt_check RoundTrip.V16_76.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_6_4]
#rt_overlap RoundTrip.V16_76.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_6_4]

end RoundTrip.V16_76
