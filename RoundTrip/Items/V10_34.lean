import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_34

/-! Round trip for V10_34 (2021 Lemma 10.3.2, p. 484; 2017: Lemma 10.3, p. 348: a refinement
of a refinement of `d` is a refinement of `d`).

`A` is the conjunction of the types of the two listed theorems, universe at `0` (`B` lives in
`EP.{0}`): `Diagram.lemma_10_3_2` (`d' ≤ d`, `d'' ≤ d'` ⇒ `d'' ≤ d`) and
`Diagram.IsRefinement.trans` (the same with the hypotheses swapped).

B's `IsRefinementB` is the project's `Diagram.IsRefinement` by definition
(`NaturallyEquivalent F G` is `Nonempty (EpNatTrans F G)`), so both directions are the identity
up to the order of the hypotheses. -/

namespace RoundTrip.V10_34
open Polyfold EPLocalization

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.lemma_10_3_2.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.trans.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.Diagram.lemma_10_3_2.{0},
    @Polyfold.EPLocalization.Diagram.IsRefinement.trans.{0}⟩

/-- B's refinement relation is the project's, by definition. -/
theorem isRefinementB_iff {X Y : EP.{0}} (d' d : Diagram X Y) :
    IsRefinementB d' d ↔ d'.IsRefinement d := Iff.rfl

theorem A_to_B : A → B := by
  rintro ⟨h1, -⟩
  intro X Y d d' d'' h' h''
  exact (isRefinementB_iff _ _).2 (h1 ((isRefinementB_iff _ _).1 h') ((isRefinementB_iff _ _).1 h''))

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro X Y d d' d'' h' h''
    exact hB X Y d d' d'' h' h''
  · intro X Y d d' d'' h'' h'
    exact hB X Y d d' d'' h' h''

#rt_check RoundTrip.V10_34.A_to_B [Polyfold.EPLocalization.Diagram.lemma_10_3_2,
  Polyfold.EPLocalization.Diagram.IsRefinement.trans]
#rt_check RoundTrip.V10_34.B_to_A [Polyfold.EPLocalization.Diagram.lemma_10_3_2,
  Polyfold.EPLocalization.Diagram.IsRefinement.trans]
#rt_overlap RoundTrip.V10_34.B_to_A [Polyfold.EPLocalization.Diagram.lemma_10_3_2,
  Polyfold.EPLocalization.Diagram.IsRefinement.trans]

end RoundTrip.V10_34
