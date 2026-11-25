import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_8

set_option maxSynthPendingDepth 3

/-! Round trip for V13_8 (2021 Theorem 13.1.8, p. 604; 2017: Theorem 13.2: existence of good
systems inside given open neighbourhoods).

`A` is the type of `EpGroupoid.theorem_13_1_8` at universe `0` (`B` lives in `Type`).  Both sides
use the project's `HasParacompactOrbitSpace` and `GoodSystem`, quantify over the same
ep-groupoids (`T2`, paracompact object and morphism spaces) and over the same families
`W : Obj → Set Obj` of open neighbourhoods; the conclusion `∃ 𝒰, ∀ x, 𝒰.U x ⊆ W x` is literally
the same.  Both directions are re-binding of the arguments. -/

namespace RoundTrip.V13_8
open Polyfold

/-- The project's statement at universe `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.theorem_13_1_8.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.theorem_13_1_8.{0}

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X hX W hW hxW
  exact hA X hX W hW hxW

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X hX W hW hxW
  exact hB Obj Mor X hX W hW hxW

#rt_check RoundTrip.V13_8.A_to_B [Polyfold.EpGroupoid.theorem_13_1_8]
#rt_check RoundTrip.V13_8.B_to_A [Polyfold.EpGroupoid.theorem_13_1_8]
#rt_overlap RoundTrip.V13_8.B_to_A [Polyfold.EpGroupoid.theorem_13_1_8]

end RoundTrip.V13_8
