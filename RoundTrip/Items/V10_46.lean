import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_46

/-! Round trip for V10_46 (2021 Theorem 10.3.15, p. 492; 2017: Theorem 10.6, p. 355): the orbit
space functor `|·| : EP(E⁻¹) → TOP`.

The item lists the definition `EPLoc.orbitFunctor : EPLoc ⥤ TopCat` (vocabulary: `X ↦ |X|`,
`f ↦ |f|` with `map_id`, `map_comp` from `EPLoc.orbitMap_id`, `proposition_10_3_11`) and the
theorem `EPLoc.theorem_10_3_15`; `A` is its type, universe at `0` (`B` lives in `Type`):
`orbitFunctor.obj (of X) = TopCat.of |X|` and `⇑(orbitFunctor.map [d]).hom = |Φ| ∘ |F|⁻¹`.

`B` says, for the project's `EPLoc.orbitMap`: (1) `|[d]| = |Φ| ∘ |F|⁻¹`, (2) every `|f|` is
continuous, (3) `|1_X| = id`, (4) `|f ≫ g| = |g| ∘ |f|` (the functor stated elementarily).

* `A_to_B`: (1) is `A`'s second conjunct (`⇑(orbitFunctor.map f).hom` is `EPLoc.orbitMap f` by
  `rfl`); (2)–(4) are read off the functor `orbitFunctor` of `A`'s statement: the continuity of
  its morphisms in `TopCat`, and its fields `map_id`, `map_comp`.
* `B_to_A`: the first conjunct is `rfl`, the second is `B` (1). -/

namespace RoundTrip.V10_46
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universe at `0`). -/
def A : Prop := type_of% @Polyfold.EPLocalization.EPLoc.theorem_10_3_15.{0}

theorem A_holds : A := @Polyfold.EPLocalization.EPLoc.theorem_10_3_15.{0}

theorem A_to_B : A → B.{0} := by
  rintro ⟨-, hmap⟩
  refine ⟨fun X Y d => hmap d, fun X Y f => (EPLoc.orbitFunctor.map f).hom.continuous,
    fun X => ?_, fun X Y Z f g => ?_⟩
  · -- `|1_X| = id`, from the functor law `map_id` of `orbitFunctor`
    have h := congrArg (fun k => ⇑(TopCat.Hom.hom k)) (EPLoc.orbitFunctor.map_id (EPLoc.of X))
    exact h
  · -- `|f ≫ g| = |g| ∘ |f|`, from the functor law `map_comp` of `orbitFunctor`
    have h := congrArg (fun k => ⇑(TopCat.Hom.hom k)) (EPLoc.orbitFunctor.map_comp f g)
    exact h

theorem B_to_A : B.{0} → A := by
  rintro ⟨hval, -, -, -⟩
  exact ⟨fun X => rfl, fun {X Y} d => hval X Y d⟩

#rt_check RoundTrip.V10_46.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_10_3_15]
#rt_check RoundTrip.V10_46.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_10_3_15]
#rt_overlap RoundTrip.V10_46.B_to_A [Polyfold.EPLocalization.EPLoc.theorem_10_3_15]

end RoundTrip.V10_46
