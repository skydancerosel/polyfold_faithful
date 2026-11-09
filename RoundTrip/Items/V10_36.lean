import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_36

/-! Round trip for V10_36 (2021 Lemma 10.3.4, p. 485; 2017: Lemma 10.4, p. 349: if `(d, d')`
and `(d', d'')` have common refinements, so has `(d, d'')`).

`A` is the conjunction of the types of the three listed theorems, universe at `0` (`B` lives in
`EP.{0}`): `Diagram.lemma_10_3_4` and `Diagram.Equiv.trans` (both: `Equiv d d' → Equiv d' d'' →
Equiv d d''`, where the project's `Diagram.Equiv d d'` is "`(d, d')` has a common refinement",
Definition 10.3.5) and `Diagram.IsRefinement.equiv` (a refinement is equivalent to the refined
diagram).

* `A_to_B`: `Equiv d d'` is by definition `∃ e, e.IsRefinement d ∧ e.IsRefinement d'`, which is
  B's `∃ e, IsCommonRefinementB e d d'` (B's `IsRefinementB` is the project's `IsRefinement`:
  `NaturallyEquivalent F G` is `Nonempty (EpNatTrans F G)`); so B is `lemma_10_3_4`.
* `B_to_A`: `lemma_10_3_4` and `Equiv.trans` are B.  `IsRefinement.equiv` is not a consequence
  of B (B only propagates common refinements that already exist; producing the first one needs
  reflexivity of refinement): it is re-proved outright, with `d'` as the common refinement of
  `(d', d)` (`d'` refines itself by `H = 1_{A'}`, `refl'` below). -/

namespace RoundTrip.V10_36
open Polyfold EPLocalization

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.lemma_10_3_4.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.Equiv.trans.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.equiv.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.Diagram.lemma_10_3_4.{0},
    @Polyfold.EPLocalization.Diagram.Equiv.trans.{0},
    @Polyfold.EPLocalization.Diagram.IsRefinement.equiv.{0}⟩

/-- B's "`(d, d')` has a common refinement" is the project's `Diagram.Equiv`, by definition. -/
theorem exists_commonRefinementB_iff {X Y : EP.{0}} (d d' : Diagram X Y) :
    (∃ e : Diagram X Y, IsCommonRefinementB e d d') ↔ Diagram.Equiv d d' := Iff.rfl

theorem A_to_B : A → B := by
  rintro ⟨h1, -, -⟩
  intro X Y d d' d'' h h'
  exact (exists_commonRefinementB_iff _ _).2
    (h1 ((exists_commonRefinementB_iff _ _).1 h) ((exists_commonRefinementB_iff _ _).1 h'))

/-- Every diagram refines itself (`H = 1_A`), proved directly. -/
theorem refl' {X Y : EP.{0}} (d : Diagram X Y) : d.IsRefinement d :=
  ⟨EpFunctor.id d.A.X, EpFunctor.IsEquivalence.id _, EpFunctor.NaturallyEquivalent.refl _,
    EpFunctor.NaturallyEquivalent.refl _⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro X Y d d' d'' h h'
    exact hB X Y d d' d'' h h'
  · intro X Y d d' d'' h h'
    exact hB X Y d d' d'' h h'
  · intro X Y d' d h
    exact ⟨d', refl' d', h⟩

#rt_check RoundTrip.V10_36.A_to_B [Polyfold.EPLocalization.Diagram.lemma_10_3_4,
  Polyfold.EPLocalization.Diagram.Equiv.trans, Polyfold.EPLocalization.Diagram.IsRefinement.equiv]
#rt_check RoundTrip.V10_36.B_to_A [Polyfold.EPLocalization.Diagram.lemma_10_3_4,
  Polyfold.EPLocalization.Diagram.Equiv.trans, Polyfold.EPLocalization.Diagram.IsRefinement.equiv]
#rt_overlap RoundTrip.V10_36.B_to_A [Polyfold.EPLocalization.Diagram.lemma_10_3_4,
  Polyfold.EPLocalization.Diagram.Equiv.trans, Polyfold.EPLocalization.Diagram.IsRefinement.equiv]

end RoundTrip.V10_36
