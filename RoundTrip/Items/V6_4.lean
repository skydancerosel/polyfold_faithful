import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_4

/-! Round trip for V6_4 (Proposition 6.4, naturality of `ι`).  A is `proposition_6_4`, universes
at `0`.  The two statements are the same equality of linear maps: B writes `Φ*` as
`LinearMap.dualMap`, A as `Module.Dual.transpose` (definitionally equal), and the dimension proofs
passed to `maxPowMap` are different terms of one `Prop` (proof irrelevance). -/

namespace RoundTrip.V6_4
open Polyfold

/-- The project's statement (Proposition 6.4), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.proposition_6_4.{0, 0}

theorem A_holds : A := @Polyfold.proposition_6_4.{0, 0}

theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ Φ
  exact hA Φ

theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ _ _ Φ
  exact hB E F Φ

#rt_check RoundTrip.V6_4.A_to_B [Polyfold.proposition_6_4]
#rt_check RoundTrip.V6_4.B_to_A [Polyfold.proposition_6_4]
#rt_overlap RoundTrip.V6_4.B_to_A [Polyfold.proposition_6_4]

end RoundTrip.V6_4
