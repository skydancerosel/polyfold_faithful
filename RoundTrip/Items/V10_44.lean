import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_44

/-! Round trip for V10_44 (2021 Definition 10.3.12, p. 490; 2017: Definition 10.9, p. 354): the
category `EP(E⁻¹)`.

The item lists the definition `EPLoc` (a one-field structure around `EP`, with its `Category`
instance; vocabulary) and six theorems; `A` is the conjunction of their types, universes at `0`
(`B` lives in `Type`): `EPLoc.toEP_of`, `EPLoc.of_toEP` (`of`, `toEP` inverse), `homMk_comp`
(`[d] ≫ [e] = [d.comp e]`), `id_eq` (`𝟙 = [1_X]`), `homMk_eq_homMk_iff` (`[d] = [d']` iff a
common refinement) and `homMk_surjective` (every morphism is a `[d]`).

`B` says the same about the project's `EPLoc`: `toEP` is bijective; every morphism is a `[d]`;
`[d] = [d']` iff `EquivB d d'` (B's common refinement, definitionally the project's
`Diagram.Equiv`: `NaturallyEquivalent` is `Nonempty EpNatTrans`); `[d] ≫ [e] = [d.comp e]`;
`𝟙 = [1_X]`.

* `A_to_B`: bijectivity from `toEP_of` / `of_toEP`; the other four parts are the corresponding
  conjuncts of `A` (the iff up to `Iff.rfl`).
* `B_to_A`: `homMk_comp`, `id_eq`, `homMk_eq_homMk_iff`, `homMk_surjective` are parts of `B`.
  `toEP_of`, `of_toEP` are not consequences of `B` (bijectivity of `toEP` says nothing about
  which inverse `of` is); both are `rfl` (structure eta) and are proved outright. -/

namespace RoundTrip.V10_44
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.EPLoc.toEP_of.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.of_toEP.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.homMk_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.id_eq.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.homMk_eq_homMk_iff.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.homMk_surjective.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.EPLoc.toEP_of.{0}, @Polyfold.EPLocalization.EPLoc.of_toEP.{0},
    @Polyfold.EPLocalization.EPLoc.homMk_comp.{0}, @Polyfold.EPLocalization.EPLoc.id_eq.{0},
    @Polyfold.EPLocalization.EPLoc.homMk_eq_homMk_iff.{0},
    @Polyfold.EPLocalization.EPLoc.homMk_surjective.{0}⟩

theorem A_to_B : A → B.{0} := by
  rintro ⟨hto, hof, hcomp, hid, hiff, hsurj⟩
  refine ⟨⟨fun X Y h => ?_, fun X => ⟨EPLoc.of X, hto X⟩⟩, fun X Y f => hsurj f,
    fun X Y d d' => hiff, fun X Y Z d e => hcomp d e, fun X => hid X⟩
  rw [← hof X, ← hof Y, h]

theorem B_to_A : B.{0} → A := by
  rintro ⟨-, hsurj, hiff, hcomp, hid⟩
  exact ⟨fun X => rfl, fun X => rfl, fun d e => hcomp _ _ _ d e, fun X => hid X,
    fun {X Y d d'} => hiff X Y d d', fun {X Y} f => hsurj X Y f⟩

#rt_check RoundTrip.V10_44.A_to_B [Polyfold.EPLocalization.EPLoc.toEP_of,
  Polyfold.EPLocalization.EPLoc.of_toEP, Polyfold.EPLocalization.EPLoc.homMk_comp,
  Polyfold.EPLocalization.EPLoc.id_eq, Polyfold.EPLocalization.EPLoc.homMk_eq_homMk_iff,
  Polyfold.EPLocalization.EPLoc.homMk_surjective]
#rt_check RoundTrip.V10_44.B_to_A [Polyfold.EPLocalization.EPLoc.toEP_of,
  Polyfold.EPLocalization.EPLoc.of_toEP, Polyfold.EPLocalization.EPLoc.homMk_comp,
  Polyfold.EPLocalization.EPLoc.id_eq, Polyfold.EPLocalization.EPLoc.homMk_eq_homMk_iff,
  Polyfold.EPLocalization.EPLoc.homMk_surjective]
#rt_overlap RoundTrip.V10_44.B_to_A [Polyfold.EPLocalization.EPLoc.toEP_of,
  Polyfold.EPLocalization.EPLoc.of_toEP, Polyfold.EPLocalization.EPLoc.homMk_comp,
  Polyfold.EPLocalization.EPLoc.id_eq, Polyfold.EPLocalization.EPLoc.homMk_eq_homMk_iff,
  Polyfold.EPLocalization.EPLoc.homMk_surjective]

end RoundTrip.V10_44
