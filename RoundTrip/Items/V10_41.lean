import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_41

/-! Round trip for V10_41 (2021 Definition 10.3.9, p. 489; 2017: Definition 10.8, p. 352:
generalized maps and generalized isomorphisms).

The item lists the definitions `EPLoc.homMk` (`[d] = ⟦d⟧`) and `EPLoc.IsGeneralizedIso`
(`∃ g, f ≫ g = 𝟙 ∧ g ≫ f = 𝟙` in the project's category `EPLoc`) and one theorem; `A` is its type,
universe at `0`: `isGeneralizedIso_iff_isIso` (generalized isomorphisms are Mathlib's `IsIso`).

`B` (at universe `0`) checks the project's definitions against the text: (1) every generalized
map is a class `[d] = homMk d`; (2) `[d] = [d']` iff `d`, `d'` have a common refinement
(`EquivB`, definitionally `Diagram.Equiv`); (3) `IsGeneralizedIso [d]` iff some diagram `e` has
`EquivB (d.comp e) (id X)` and `EquivB (e.comp d) (id Y)`.

Both statements are definitional facts, provable outright:
* `B_holds`: (1) `Quotient.exists_rep`; (2) `Quotient.eq`; (3) `homMk d ≫ homMk e` is
  definitionally `homMk (d.comp e)` and `𝟙 (of X)` is `homMk (id X)`, so (3) is `Quotient.eq` on
  both equations after choosing a representative of the inverse.
* `A` is `⟨fun h => ⟨h⟩, fun h => h.out⟩` (`IsIso` is the same existential).
So `A_to_B` and `B_to_A` hold without using their hypotheses (flagged in the JSON): the item has
no mathematical content beyond the definitions, which `B_holds` shows agree with the text.
-/

namespace RoundTrip.V10_41
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universe at `0`). -/
def A : Prop := type_of% @Polyfold.EPLocalization.EPLoc.isGeneralizedIso_iff_isIso.{0}

theorem A_holds : A := @EPLoc.isGeneralizedIso_iff_isIso.{0}

/-- `B` holds outright: the project's definitions are the text's. -/
theorem B_holds : B.{0} := by
  refine ⟨fun X Y f => Quotient.exists_rep f, fun X Y d d' => Quotient.eq, fun X Y d => ?_⟩
  constructor
  · rintro ⟨g, h₁, h₂⟩
    obtain ⟨e, rfl⟩ := Quotient.exists_rep g
    exact ⟨e, Quotient.eq.1 h₁, Quotient.eq.1 h₂⟩
  · rintro ⟨e, h₁, h₂⟩
    exact ⟨Quotient.mk (Diagram.setoid Y X) e, Quotient.sound h₁, Quotient.sound h₂⟩

/-- `A` holds outright (re-proved: `IsIso f` is the same existential). -/
theorem A_holds' : A := fun {_ _} _ => ⟨fun h => ⟨h⟩, fun h => h.out⟩

/-- Vacuous: `B` holds outright. -/
theorem A_to_B : A → B.{0} := fun _ => B_holds

/-- Vacuous: `A` holds outright. -/
theorem B_to_A : B.{0} → A := fun _ => A_holds'

#rt_check RoundTrip.V10_41.A_to_B [Polyfold.EPLocalization.EPLoc.isGeneralizedIso_iff_isIso]
#rt_check RoundTrip.V10_41.B_to_A [Polyfold.EPLocalization.EPLoc.isGeneralizedIso_iff_isIso]
#rt_overlap RoundTrip.V10_41.B_to_A [Polyfold.EPLocalization.EPLoc.isGeneralizedIso_iff_isIso]

end RoundTrip.V10_41
