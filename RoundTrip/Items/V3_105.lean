import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_105

/-!
Round trip for V3_105 (Theorem 3.15 for tame germ data).  `A` is the conjunction of the types of
`Polyfold.theorem_3_1_18_tame` and `Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd`,
universes instantiated at `0`.

Refresh 2026-11-02: both conjuncts now state the germ reading of Definitions 3.50/3.51
(`IsScFredholmSectionTame`, `IsScFredholmGermTame` with `IsFillingGerm`, `IsScPlusGerm` in a tame
chart), and so does B; the proof is unchanged.

* `A → B`: B is `theorem_3_1_18_tame` with the extra hypothesis `IsTameStrongBundle Bd` (unused).
* `B → A` is not proved: `A` assumes no tame strong bundle (no `PX.IsTame`, no tame atlas), and
  its second conjunct is a pointwise germ statement (`f` only a section with tame germ data at
  one point `x`), neither of which `B` gives.
-/

namespace RoundTrip.V3_105
open Polyfold

/-- The project's statement: Theorem 3.15 for tame germ data and its germ form, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_1_18_tame.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_1_18_tame.{0, 0}, @Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f s _ hf hs
  exact hA.1 hf hs

#rt_check RoundTrip.V3_105.A_to_B [Polyfold.theorem_3_1_18_tame,
  Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd]

end RoundTrip.V3_105
