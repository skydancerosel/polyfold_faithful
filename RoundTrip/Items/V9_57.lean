import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_57

/-! Round trip for V9_57 (2021 Proposition 9.5.13, p. 446: the normalizing factors).

The item lists the definition `LocalBranchingStructure.toReduced` (vocabulary: a local branching
structure on `X` is one on `X_R`) and three theorems; `A` is the conjunction of their types,
universes at `0`:
`card_effIsotropy_eq_of_isEffective` (`A1`: effective ⇒ `♯G^eff_x = ♯G_x`),
`isFunctorial_reduced_iff` (`A2`: `Θ` is functorial on `X_R` iff on `X`),
`card_effIsotropy_eq_reduced` (`A3`: `♯G^eff_x = ♯G^R_x` and `♯(G^R_x)^eff = ♯G^R_x`, for every
`X` whose `T_R` is Hausdorff and paracompact, **no LUC hypothesis**).

`B` = (1) effective ⇒ `T_x = ⊥` and `♯G^eff_x = ♯G_x`; (2) under (LUC), with `T_R` Hausdorff and
paracompact, `♯G^R_x = ♯G^eff_x`.

* `A_to_B` (proved): (1) `T_x = ⊥` is the non-item `isEffective_iff_trivialSubgroup_eq_bot`
  (the project's proof of `A1` goes through it), the order equality is `A1`; (2) is the first
  half of `A3` (LUC unused).
* `B → A` (not proved as a whole): `A` is more general and has more.  `A3`'s first half holds
  for every `X` (with the instances), while `B` (2) needs (LUC); and `A2` (the data induced on
  `X_R`) is not in `B`.  What `B` does give:
  - `B_to_A1`: `A1` from `B` (1);
  - `B_to_A3_of_isLUC`: `A3` for (LUC) `X`, the first half from `B` (2), the second from `B` (1)
    applied to `X_R` (effective by the non-item `isEffective_reducedEpGroupoid`).
  The missing pieces hold outright from non-item lemmas (`A2_outright`: `surjective_reducedπ`;
  `A3_fst_outright`: the isomorphism `effIsotropyEquivReduced`), which shows that the gap is only
  generality, not a mathematical difference on the text's content. -/

namespace RoundTrip.V9_57
open Polyfold

/-- The project's statement, universes at `0`. -/
def A1 : Prop := type_of% @Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective.{0}
def A2 : Prop := type_of% @Polyfold.EpGroupoid.isFunctorial_reduced_iff.{0}
def A3 : Prop := type_of% @Polyfold.EpGroupoid.card_effIsotropy_eq_reduced.{0}

def A : Prop := A1 ∧ A2 ∧ A3

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective.{0},
    @Polyfold.EpGroupoid.isFunctorial_reduced_iff.{0},
    @Polyfold.EpGroupoid.card_effIsotropy_eq_reduced.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, -, h3⟩
  refine ⟨fun Obj Mor _ _ _ _ _ _ X hX x =>
    ⟨(EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot X).1 hX x, h1 hX x⟩, ?_⟩
  intro Obj Mor _ _ _ _ _ _ X _ _ _ x
  exact (h3 X x).1.symm

/-! ### What `B` gives of `A` -/

theorem B_to_A1 : B → A1 := fun hB Obj Mor _ _ _ _ _ _ X hX x =>
  (hB.1 Obj Mor X hX x).2

/-- `A3` for the `X` satisfying (LUC), from `B`. -/
theorem B_to_A3_of_isLUC : B →
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      X.IsLUC → ∀ [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor] (x : Obj),
      Nat.card (X.EffIsotropy x) = Nat.card (X.reducedEpGroupoid.Isotropy x) ∧
        Nat.card (X.reducedEpGroupoid.EffIsotropy x) =
          Nat.card (X.reducedEpGroupoid.Isotropy x) := by
  intro hB Obj Mor _ _ _ _ _ _ X hLUC _ _ x
  exact ⟨(hB.2 Obj Mor X hLUC x).symm,
    (hB.1 Obj X.ReducedMor X.reducedEpGroupoid X.isEffective_reducedEpGroupoid x).2⟩

/-! ### The parts of `A` not in `B`, outright (non-item lemmas) -/

theorem A2_outright : A2 := by
  intro Obj Mor _ _ _ _ _ _ X _ _ Θ
  refine ⟨fun h φ => h (X.reducedπ φ), fun h q => ?_⟩
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
  exact h φ

theorem A3_fst_outright :
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor] (x : Obj),
      Nat.card (X.EffIsotropy x) = Nat.card (X.reducedEpGroupoid.Isotropy x) :=
  fun _ _ _ _ _ _ _ _ X _ _ x => Nat.card_congr (X.effIsotropyEquivReduced x).toEquiv

#rt_check RoundTrip.V9_57.A_to_B [Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective,
  Polyfold.EpGroupoid.isFunctorial_reduced_iff, Polyfold.EpGroupoid.card_effIsotropy_eq_reduced]
#rt_check RoundTrip.V9_57.B_to_A1 [Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective,
  Polyfold.EpGroupoid.isFunctorial_reduced_iff, Polyfold.EpGroupoid.card_effIsotropy_eq_reduced]
#rt_check RoundTrip.V9_57.B_to_A3_of_isLUC [Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective,
  Polyfold.EpGroupoid.isFunctorial_reduced_iff, Polyfold.EpGroupoid.card_effIsotropy_eq_reduced]
#rt_check RoundTrip.V9_57.A2_outright [Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective,
  Polyfold.EpGroupoid.isFunctorial_reduced_iff, Polyfold.EpGroupoid.card_effIsotropy_eq_reduced]
#rt_check RoundTrip.V9_57.A3_fst_outright [Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective,
  Polyfold.EpGroupoid.isFunctorial_reduced_iff, Polyfold.EpGroupoid.card_effIsotropy_eq_reduced]
#rt_overlap RoundTrip.V9_57.B_to_A3_of_isLUC [Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective,
  Polyfold.EpGroupoid.isFunctorial_reduced_iff, Polyfold.EpGroupoid.card_effIsotropy_eq_reduced]

end RoundTrip.V9_57
