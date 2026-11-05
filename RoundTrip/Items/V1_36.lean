import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_36

/-! Round trip for V1_36 (Definitions 1.11 and 1.13: level shifts and tangents of tuples are
tuples).

`A` is the conjunction of the types of the theorems among the item's declarations:
`IsPartialQuadrant.shift`, `IsRelOpenInQuadrant.shift`, `IsPartialQuadrant.tangentSet`,
`IsRelOpenInQuadrant.tangentSet`, `ScBanach.shift_tangentSet`.  `ScIso.shift` and
`tangentQuadrantIso` are definitions (vocabulary).  None of the theorems has universe parameters
(`ScBanach` lives in `Type`). -/

namespace RoundTrip.V1_36
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsPartialQuadrant.shift) ∧
  (type_of% @Polyfold.IsRelOpenInQuadrant.shift) ∧
  (type_of% @Polyfold.IsPartialQuadrant.tangentSet) ∧
  (type_of% @Polyfold.IsRelOpenInQuadrant.tangentSet) ∧
  (type_of% @Polyfold.ScBanach.shift_tangentSet)

theorem A_holds : A :=
  ⟨@Polyfold.IsPartialQuadrant.shift, @Polyfold.IsRelOpenInQuadrant.shift,
    @Polyfold.IsPartialQuadrant.tangentSet, @Polyfold.IsRelOpenInQuadrant.tangentSet,
    @Polyfold.ScBanach.shift_tangentSet⟩

theorem A_to_B : A → B := by
  intro hA E C U hU
  exact ⟨hA.2.2.2.1 hU, hA.2.1 hU⟩

/-- A partial quadrant is relatively open in itself. -/
theorem relOpen_self {E : ScBanach} {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsRelOpenInQuadrant E C C :=
  ⟨hC, Set.univ, isOpen_univ, (Set.univ_inter C).symm⟩

/-- `B → A`: the four quadrant statements are `B` (for `U = C` when only `C` is concerned).  The
fifth conjunct, `(TU)¹ = T(U¹)` as sets, is an unfolding identity not addressed by `B`; it is
proved directly (without `B`). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {E C} hC => (hB E C C (relOpen_self hC)).2.isPartialQuadrant,
    fun {E C U} hU => (hB E C U hU).2,
    fun {E C} hC => (hB E C C (relOpen_self hC)).1.isPartialQuadrant,
    fun {E C U} hU => (hB E C U hU).1, ?_⟩
  intro E U
  ext p
  rw [ScBanach.mem_lvlSet_tangentSet]
  exact Iff.rfl

#rt_check RoundTrip.V1_36.A_to_B [Polyfold.IsPartialQuadrant.shift,
  Polyfold.IsRelOpenInQuadrant.shift, Polyfold.IsPartialQuadrant.tangentSet,
  Polyfold.IsRelOpenInQuadrant.tangentSet, Polyfold.ScBanach.shift_tangentSet]
#rt_check RoundTrip.V1_36.B_to_A [Polyfold.IsPartialQuadrant.shift,
  Polyfold.IsRelOpenInQuadrant.shift, Polyfold.IsPartialQuadrant.tangentSet,
  Polyfold.IsRelOpenInQuadrant.tangentSet, Polyfold.ScBanach.shift_tangentSet]
#rt_overlap RoundTrip.V1_36.B_to_A [Polyfold.IsPartialQuadrant.shift,
  Polyfold.IsRelOpenInQuadrant.shift, Polyfold.IsPartialQuadrant.tangentSet,
  Polyfold.IsRelOpenInQuadrant.tangentSet, Polyfold.ScBanach.shift_tangentSet]

end RoundTrip.V1_36
