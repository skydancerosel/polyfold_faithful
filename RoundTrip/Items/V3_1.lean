import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_1

/-! Round trip for V3_1 (Definition 3.1: sc-germs of neighbourhoods).

`A` is the conjunction of the types of the two listed theorems
`Polyfold.IsPartialQuadrant.isQuadrantLike` and `Polyfold.ScNbhdGerm.uniqueDiffWithinAt` (no
universe parameters).  `ScNbhdGerm`, `ScNbhdGerm.tangent`, `ScNbhdGerm.ofSet`, `IsQuadrantLike`
are definitions (vocabulary); the comparison of definitions is B itself, which is proved.

* `A → B` is proved, but B is a statement about the project's definitions and is proved outright
  (the hypothesis is not used): `ScNbhdGerm` has exactly the fields of B's `IsScGermB`
  (`nested`, `relOpen` with `E.lvlSet C m = levelB E C m` definitionally, `zero_mem`); the tangent
  germ's levels `G.U (m+1) ×ˢ univ` are `TUB G.U`, `E.tangentSet C = TCB E C` definitionally, and
  `ofSet` has levels `E.lvlSet U m = ofSetB E U m`.
* `B → A` is proved outright as well (B says nothing about convexity or unique differentiability):
  the two auxiliary lemmas are re-proved from non-banned project lemmas
  (`IsPartialQuadrant.convex_lvlSet`, `.interior_lvlSet_nonempty`,
  `IsQuadrantLike.uniqueDiffWithinAt`). -/

namespace RoundTrip.V3_1
open Polyfold Set

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.IsPartialQuadrant.isQuadrantLike) ∧
    (type_of% @Polyfold.ScNbhdGerm.uniqueDiffWithinAt)

theorem A_holds : A :=
  ⟨@Polyfold.IsPartialQuadrant.isQuadrantLike, @Polyfold.ScNbhdGerm.uniqueDiffWithinAt⟩

/-- The project's germs satisfy B's definition. -/
theorem germ_isScGermB {E : ScBanach} {C : Set (E.lvl 0)} (G : ScNbhdGerm E C) :
    IsScGermB E C G.U :=
  ⟨G.nested, G.relOpen, G.zero_mem⟩

/-- B's germs are the project's. -/
def germOfB {E : ScBanach} {C : Set (E.lvl 0)} (U : ∀ m, Set (E.lvl m)) (hU : IsScGermB E C U) :
    ScNbhdGerm E C where
  U := U
  nested := hU.1
  zero_mem := hU.2.2
  relOpen := hU.2.1

theorem tangent_U_eq {E : ScBanach} {C : Set (E.lvl 0)} (G : ScNbhdGerm E C) :
    G.tangent.U = TUB G.U := by
  funext m
  ext p
  exact ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

theorem B_holds : B := by
  intro E C _hC
  refine ⟨germ_isScGermB, fun U hU => ⟨germOfB U hU, rfl⟩, fun U hU => ?_, ⟨rfl, tangent_U_eq⟩,
    fun U hU h0 => germ_isScGermB (ScNbhdGerm.ofSet hU h0), fun U hU h0 => rfl⟩
  have := germ_isScGermB (germOfB U hU).tangent
  rw [tangent_U_eq] at this
  exact this

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro E C hC
    exact
      { zero_mem := by
          obtain ⟨n, W, T, rfl⟩ := hC
          show T 0 0 ∈ quadrant n W 0
          rw [map_zero]; intro i; exact le_rfl
        convex := hC.convex_lvlSet
        interior_nonempty := hC.interior_lvlSet_nonempty }
  · intro E C G hC m x hx
    obtain ⟨O, hO, h⟩ := G.relOpen m
    rw [h] at hx ⊢
    exact hC.uniqueDiffWithinAt hO hx

#rt_check RoundTrip.V3_1.A_to_B [Polyfold.IsPartialQuadrant.isQuadrantLike,
  Polyfold.ScNbhdGerm.uniqueDiffWithinAt]
#rt_check RoundTrip.V3_1.B_to_A [Polyfold.IsPartialQuadrant.isQuadrantLike,
  Polyfold.ScNbhdGerm.uniqueDiffWithinAt]
#rt_overlap RoundTrip.V3_1.B_to_A [Polyfold.IsPartialQuadrant.isQuadrantLike,
  Polyfold.ScNbhdGerm.uniqueDiffWithinAt]

end RoundTrip.V3_1
