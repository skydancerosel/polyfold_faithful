import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_60

/-!
Round trip for V7_60 (Proposition 7.13: proper subsets are closed).

`A` is the conjunction of the types of `Polyfold.EpGroupoid.proposition_7_5_9` and
`Polyfold.EpGroupoid.IsProperSubset.isClosed`, universes at `0`: for every ep-groupoid
`X : EpGroupoid Obj Mor` (`Obj Mor : Type`) and `Q : Set Obj`, `X.IsProperSubset Q → IsClosed Q`
(the second is the dot-notation alias of the first, with `X` implicit).  `B` is the same
statement with all binders explicit.
-/

namespace RoundTrip.V7_60
open Polyfold

/-- The project's Proposition 7.13 and its alias, universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.proposition_7_5_9.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsProperSubset.isClosed.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.proposition_7_5_9.{0}, @Polyfold.EpGroupoid.IsProperSubset.isClosed.{0}⟩

theorem A_to_B : A → B := fun hA _ _ _ _ _ _ _ _ X _ hQ => hA.1 X hQ

theorem B_to_A : B → A := fun hB =>
  ⟨fun {Obj Mor} _ _ _ _ _ _ X _ hQ => hB Obj Mor X _ hQ,
   fun {Obj Mor} _ _ _ _ _ _ X _ hQ => hB Obj Mor X _ hQ⟩

#rt_check RoundTrip.V7_60.A_to_B [Polyfold.EpGroupoid.proposition_7_5_9,
  Polyfold.EpGroupoid.IsProperSubset.isClosed]
#rt_check RoundTrip.V7_60.B_to_A [Polyfold.EpGroupoid.proposition_7_5_9,
  Polyfold.EpGroupoid.IsProperSubset.isClosed]
#rt_overlap RoundTrip.V7_60.B_to_A [Polyfold.EpGroupoid.proposition_7_5_9,
  Polyfold.EpGroupoid.IsProperSubset.isClosed]
#rt_overlap RoundTrip.V7_60.A_to_B [Polyfold.EpGroupoid.proposition_7_5_9,
  Polyfold.EpGroupoid.IsProperSubset.isClosed]

end RoundTrip.V7_60
