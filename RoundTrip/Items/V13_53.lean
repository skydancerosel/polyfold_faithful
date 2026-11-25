import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_53

set_option maxSynthPendingDepth 3

/-! Round trip for V13_53 (2021 Theorem 13.4.4, pp. 626–628; 2017: Theorem 13.5: the pull-back
along a proper strong bundle covering is structurable).

`A` is the conjunction of the types of `theorem_13_4_4` and `theorem_13_4_4_structured` at
universe `0` (`PullMap.ofCovering` is vocabulary).

* `A_to_B`: `theorem_13_4_4` is `B` verbatim (`Λ ∘ Φ` is `fun w => Λ (Φ w)` by definition).
* `B_to_A`: `theorem_13_4_4` from `B`.  The structured form (a map of structured
  sc⁺-multisections with `forget (pull L) = forget L ∘ Φ`, `pull [T] = [pullTuple T P]`,
  `I_y = I_{F(y)}`, `τ_{y,y'}(φ) = τ_{F(y),F(y')}(F(φ))`) is not a consequence of `B`, which
  speaks only of structurability; it is proved outright from the general pull-back machinery
  `PullMap.pullStructured`, `forget_pullStructured`, `pullStructured_mk` (not items of V13_53). -/

namespace RoundTrip.V13_53
open Polyfold Polyfold.SBLocalization

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.theorem_13_4_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_4_4_structured.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.theorem_13_4_4.{0},
    @Polyfold.SBLocalization.theorem_13_4_4_structured.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h4, -⟩ C A F Φ hΦ Λ hΛ
  exact h4 hΦ hΛ

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun hΦ _ h => hB _ _ _ _ hΦ _ h, fun hΦ => ?_⟩
  exact ⟨(PullMap.ofCovering hΦ).pullStructured, (PullMap.ofCovering hΦ).forget_pullStructured,
    fun T P => ⟨(PullMap.ofCovering hΦ).pullStructured_mk T P, fun _ => rfl, fun _ _ _ => rfl⟩⟩

#rt_check RoundTrip.V13_53.A_to_B [Polyfold.SBLocalization.theorem_13_4_4,
  Polyfold.SBLocalization.theorem_13_4_4_structured]
#rt_check RoundTrip.V13_53.B_to_A [Polyfold.SBLocalization.theorem_13_4_4,
  Polyfold.SBLocalization.theorem_13_4_4_structured]
#rt_overlap RoundTrip.V13_53.B_to_A [Polyfold.SBLocalization.theorem_13_4_4,
  Polyfold.SBLocalization.theorem_13_4_4_structured]

end RoundTrip.V13_53
