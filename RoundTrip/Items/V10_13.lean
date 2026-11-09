import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_13

/-! Round trip for V10_13 (2021 Proposition 10.1.16, p. 474: (LUC) under equivalences).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpFunctor.proposition_10_1_16` (the proposition),
`EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff` (`𝐗^T` closed iff `𝐘^T` closed, the
core of the proof) and `EpGroupoid.proposition_7_2_21_2021` (Chapter 7's criterion
"(LUC) iff `𝐗^T` closed", cited by the proof).

* `A_to_B`: `proposition_10_1_16` is `B` verbatim.
* `B_to_A`: `proposition_10_1_16` is `B`; the closedness statement is `B` rewritten with
  Proposition 7.2.21.  Proposition 7.2.21 itself is a statement about a single ep-groupoid and
  not a consequence of `B`; it is re-proved outright (`prop_7_2_21'`) from the non-item lemmas
  `isClosed_nonEffectivePart_of_isLUC`, `isLUC_iff_forall_naturalRep`,
  `NaturalRep.hasLUC_of_isClosed` (the project's own two-line proof). -/

namespace RoundTrip.V10_13
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.proposition_10_1_16.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_2_21_2021.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.proposition_10_1_16.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff.{0, 0},
    @Polyfold.EpGroupoid.proposition_7_2_21_2021.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -, -⟩ Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
  exact h hF

/-- Chapter 7's criterion (2021 Proposition 7.2.21), re-proved from non-item lemmas. -/
theorem prop_7_2_21' {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) :
    X.IsLUC ↔ IsClosed X.nonEffectivePart :=
  ⟨X.isClosed_nonEffectivePart_of_isLUC, fun h => X.isLUC_iff_forall_naturalRep.2
    fun _ R => R.hasLUC_of_isClosed h⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, @prop_7_2_21'⟩
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    exact hB Obj Mor Obj' Mor' X Y F hF
  · intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    rw [← prop_7_2_21' X, ← prop_7_2_21' Y]
    exact hB Obj Mor Obj' Mor' X Y F hF

#rt_check RoundTrip.V10_13.A_to_B [Polyfold.EpFunctor.proposition_10_1_16,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpGroupoid.proposition_7_2_21_2021]
#rt_check RoundTrip.V10_13.B_to_A [Polyfold.EpFunctor.proposition_10_1_16,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpGroupoid.proposition_7_2_21_2021]
#rt_overlap RoundTrip.V10_13.B_to_A [Polyfold.EpFunctor.proposition_10_1_16,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpGroupoid.proposition_7_2_21_2021]

end RoundTrip.V10_13
