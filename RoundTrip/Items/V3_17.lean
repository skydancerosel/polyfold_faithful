import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_17

/-!
Round trip for V3_17 (Theorem 3.15).  `A` is the conjunction of the types of
`Polyfold.theorem_3_15`, `Polyfold.StrongBundle.IsScSmoothSection.sectionAdd`,
`Polyfold.StrongBundle.regularizing_sectionAdd` and
`Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd`, universes instantiated at `0`.

Refresh 2026-11-02: `theorem_3_15`, `regularizing_sectionAdd` and `IsScFredholmGerm.sectionAdd`
now state the germ reading of Definition 3.11 (`IsScFredholmSection`/`IsScFredholmGerm` with
`IsFillingGerm`, `IsScPlusGerm`), and so does B's `IsScFredholmSection`; the proof is unchanged.

* `A → B`: B is the first conjunct of A with the extra hypothesis `PX.IsTame` (unused).
* `B → A`: not proved.  B only speaks about tame bases and sc-Fredholm `f`; A's `theorem_3_15` has
  no tameness hypothesis, and A's other conjuncts are about sc-smooth sections that need not be
  sc-Fredholm and about a single germ.  None of these follows from B without re-proving them.
-/

namespace RoundTrip.V3_17
open Polyfold

/-- The project's statement: Theorem 3.15 and its three clauses, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_15.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsScSmoothSection.sectionAdd.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.regularizing_sectionAdd.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_15.{0, 0}, @Polyfold.StrongBundle.IsScSmoothSection.sectionAdd.{0, 0},
    @Polyfold.StrongBundle.regularizing_sectionAdd.{0, 0},
    @Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f s _ hf hs
  exact hA.1 hf hs

#rt_check RoundTrip.V3_17.A_to_B [Polyfold.theorem_3_15,
  Polyfold.StrongBundle.IsScSmoothSection.sectionAdd, Polyfold.StrongBundle.regularizing_sectionAdd,
  Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd]

end RoundTrip.V3_17
