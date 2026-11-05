import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_5

/-! Round trip for V1_5 (Proposition 1.6: finite-dimensional sc-subspaces).

`A` is the conjunction of the types of `ScBanach.proposition_1_6_iff` and
`ScBanach.proposition_1_6` (no universe parameters).  The two statements differ only in packaging:
`A`'s second conjunct assumes `F ⊆ E_∞`, `B`'s assumes `F` is an sc-subspace; the first conjunct
(shared) converts one into the other. -/

namespace RoundTrip.V1_5
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.proposition_1_6_iff) ∧
    (type_of% @Polyfold.ScBanach.proposition_1_6)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.proposition_1_6_iff, @Polyfold.ScBanach.proposition_1_6⟩

theorem A_to_B : A → B := by
  intro hA E F hF
  refine ⟨hA.1 E F, fun h => hA.2 E F ((hA.1 E F).1 h)⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun E F _ => (hB E F inferInstance).1, fun E F _ hF => ?_⟩
  exact (hB E F inferInstance).2 ((hB E F inferInstance).1.2 hF)

#rt_check RoundTrip.V1_5.A_to_B [Polyfold.ScBanach.proposition_1_6_iff,
  Polyfold.ScBanach.proposition_1_6]
#rt_check RoundTrip.V1_5.B_to_A [Polyfold.ScBanach.proposition_1_6_iff,
  Polyfold.ScBanach.proposition_1_6]
#rt_overlap RoundTrip.V1_5.B_to_A [Polyfold.ScBanach.proposition_1_6_iff,
  Polyfold.ScBanach.proposition_1_6]

end RoundTrip.V1_5
