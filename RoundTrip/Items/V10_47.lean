import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_47

/-! Round trip for V10_47 (2021 Proposition 10.3.17, p. 492; new in the 2021 edition): (LUC) is
invariant under generalized isomorphisms.

The item lists three theorems; `A` is the conjunction of their types, universes at `0` (`B` lives
in `Type`): `EPLoc.exists_diagram_of_isGeneralizedIso` (a generalized isomorphism has a
representative with both legs equivalences, from Theorem 10.3.10),
`EPLoc.iff_of_isGeneralizedIso` (a property of `EP` invariant under equivalences is invariant
under generalized isomorphisms), and `EPLoc.proposition_10_3_17` (for `f` a generalized
isomorphism, `X.IsLUC ↔ Y.IsLUC`).

`B`: for a diagram `d : X → Y` with a two-sided inverse `e` up to common refinement
(`IsGenIsoB d`), `X.IsLUC ↔ Y.IsLUC`.  `IsGenIsoB d` is `EPLoc.IsGeneralizedIso [d]` unfolded
(B's `EquivB` is definitionally `Diagram.Equiv`; `[d] ≫ [e] = [d.comp e]`, `𝟙 = [1_X]` by `rfl`).

* `A_to_B`: `proposition_10_3_17` at `f = [d]`, with inverse `[e]`.
* `B_to_A`: `proposition_10_3_17` from `B` (representatives `d`, `e` of `f` and its inverse).
  The two general lemmas are not consequences of `B` (which is about (LUC) only, and does not
  mention representatives with both legs equivalences); they are re-proved outright from the
  non-item `EPLoc.theorem_10_3_10` (Theorem 10.3.10), as in the project. -/

namespace RoundTrip.V10_47
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.exists_diagram_of_isGeneralizedIso.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.proposition_10_3_17.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.exists_diagram_of_isGeneralizedIso.{0},
    @Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso.{0},
    @Polyfold.EPLocalization.EPLoc.proposition_10_3_17.{0}⟩

theorem A_to_B : A → B.{0} := by
  rintro ⟨-, -, hLUC⟩
  rintro X Y d ⟨e, h₁, h₂⟩
  exact hLUC (f := EPLoc.homMk d)
    ⟨EPLoc.homMk e, EPLoc.homMk_eq_homMk_iff.2 h₁, EPLoc.homMk_eq_homMk_iff.2 h₂⟩

/-- `exists_diagram_of_isGeneralizedIso`, re-proved outright (Theorem 10.3.10). -/
theorem exists_diagram' {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}
    (hf : EPLoc.IsGeneralizedIso f) :
    ∃ d : Diagram X Y, EPLoc.homMk d = f ∧ d.Φ.IsEquivalence := by
  obtain ⟨d, rfl⟩ := EPLoc.homMk_surjective f
  exact ⟨d, rfl, (EPLoc.theorem_10_3_10 d).1.1 hf⟩

theorem B_to_A : B.{0} → A := by
  intro hB
  refine ⟨fun hf => exists_diagram' hf, fun {X Y} P hP {f} hf => ?_, fun {X Y} {f} hf => ?_⟩
  · -- the general invariance lemma, outright: `X ←F A →Φ Y` with `F`, `Φ` equivalences
    obtain ⟨d, -, hΦ⟩ := exists_diagram' hf
    exact (hP d.F d.isEquivalence_F).symm.trans (hP d.Φ hΦ)
  · -- Proposition 10.3.17, from `B`
    obtain ⟨d, rfl⟩ := EPLoc.homMk_surjective f
    obtain ⟨g, h₁, h₂⟩ := hf
    obtain ⟨e, rfl⟩ := EPLoc.homMk_surjective g
    exact hB X Y d ⟨e, EPLoc.homMk_eq_homMk_iff.1 h₁, EPLoc.homMk_eq_homMk_iff.1 h₂⟩

#rt_check RoundTrip.V10_47.A_to_B [
  Polyfold.EPLocalization.EPLoc.exists_diagram_of_isGeneralizedIso,
  Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso,
  Polyfold.EPLocalization.EPLoc.proposition_10_3_17]
#rt_check RoundTrip.V10_47.B_to_A [
  Polyfold.EPLocalization.EPLoc.exists_diagram_of_isGeneralizedIso,
  Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso,
  Polyfold.EPLocalization.EPLoc.proposition_10_3_17]
#rt_overlap RoundTrip.V10_47.B_to_A [
  Polyfold.EPLocalization.EPLoc.exists_diagram_of_isGeneralizedIso,
  Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso,
  Polyfold.EPLocalization.EPLoc.proposition_10_3_17]

end RoundTrip.V10_47
