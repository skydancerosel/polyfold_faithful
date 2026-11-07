import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_45

/-!
Round trip for V7_45 (Lemma 7.6: `|X|` is Hausdorff).

`A` is the conjunction of the types of the two listed theorems, universes at `0`:
`Polyfold.EpGroupoid.t1Space_orbitSpace` (`T1Space X.OrbitSpace`) and
`Polyfold.EpGroupoid.lemma_7_6` (`T2Space X.OrbitSpace`), for every ep-groupoid
`X : EpGroupoid Obj Mor` with `Obj Mor : Type`.  `B` is `T2Space X.OrbitSpace` in the same
setting.  `A ⇒ B` is the second conjunct; `B ⇒ A` uses Mathlib's `T2Space → T1Space`.
-/

namespace RoundTrip.V7_45
open Polyfold

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.t1Space_orbitSpace.{0} ∧
  type_of% @Polyfold.EpGroupoid.lemma_7_6.{0}

theorem A_holds : A := ⟨@EpGroupoid.t1Space_orbitSpace, @EpGroupoid.lemma_7_6⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  exact hA.2 X

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X
    have := hB Obj Mor X
    infer_instance
  · intro Obj Mor _ _ _ _ _ _ X
    exact hB Obj Mor X

#rt_check RoundTrip.V7_45.A_to_B [Polyfold.EpGroupoid.t1Space_orbitSpace,
  Polyfold.EpGroupoid.lemma_7_6]
#rt_check RoundTrip.V7_45.B_to_A [Polyfold.EpGroupoid.t1Space_orbitSpace,
  Polyfold.EpGroupoid.lemma_7_6]
#rt_overlap RoundTrip.V7_45.B_to_A [Polyfold.EpGroupoid.t1Space_orbitSpace,
  Polyfold.EpGroupoid.lemma_7_6]

end RoundTrip.V7_45
