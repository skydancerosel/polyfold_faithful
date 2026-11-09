import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_65

/-!
Round trip for V10_65 (2021 Theorem 10.3.19, pp. 493–494; 2017: Theorem 10.7), read literally.

The item lists the definition `EPLoc.Theorem_10_3_19` (vocabulary: the literal statement, in
universe `u`) and five theorems; `A` is the conjunction of their types (they are already in
universe `0`): `not_theorem_10_3_19 : ¬ Theorem_10_3_19.{0}`, `theorem_10_3_19_counterexample`
(`z3EP = ℤ/3 × ℝ ⇉ ℝ` with the trivial action has (LR), `[X ←1 X →Inv X]` and `[1_X]` are
generalized isomorphisms with the same orbit map, and they differ), `isLR_trivialZ3`,
`not_naturallyEquivalent_id_inv` (no natural transformation `1 → Inv`) and
`not_isEffective_trivialZ3`.

`B` is the literal statement: for `X, Y : EPLoc.{0}` with (LR) on one side, generalized
isomorphisms `f, f' : X ⟶ Y` with `orbitMap f = orbitMap f'` are equal.  It is
`Theorem_10_3_19.{0}` up to writing `X ⟶ Y` for `of X.toEP ⟶ of Y.toEP` (`B_iff_Theorem`, by
`Iff.rfl` modulo structure eta).

* **`¬ B`** (`not_B`): `B` at `of z3EP`, `of z3EP`, `genInv`, `genId`.  (LR) of `ℤ/3 × ℝ ⇉ ℝ` is
  re-proved below (`isLR_trivialZ3'`, the project's six-line argument: orbits are points, so an
  orbit-preserving `β` is the identity `= Φ(1)`); the remaining facts are the non-item lemmas
  `isGeneralizedIso_genInv`, `isGeneralizedIso_genId`, `orbitMap_genInv`, `genInv_ne_genId`
  (the base part of `remark_10_5_5`).
* Hence `A ⇒ B` is false (`not_A_to_B`, since `A` holds), and `B ⇒ A` holds only ex falso
  (`B_to_A`).  `A` is precisely the refutation of `B` plus its ingredients.
-/

namespace RoundTrip.V10_65
open Polyfold Polyfold.EPLocalization Polyfold.EpGroupoid.Examples
  Polyfold.LocalizationLRCounterexample Set

/-- The project's statement (all in universe `0`). -/
def A : Prop :=
  type_of% @Polyfold.LocalizationLRCounterexample.not_theorem_10_3_19 ∧
  type_of% @Polyfold.LocalizationLRCounterexample.theorem_10_3_19_counterexample ∧
  type_of% @Polyfold.EpGroupoid.Examples.isLR_trivialZ3 ∧
  type_of% @Polyfold.LocalizationLRCounterexample.not_naturallyEquivalent_id_inv ∧
  type_of% @Polyfold.EpGroupoid.Examples.not_isEffective_trivialZ3

theorem A_holds : A :=
  ⟨Polyfold.LocalizationLRCounterexample.not_theorem_10_3_19,
    Polyfold.LocalizationLRCounterexample.theorem_10_3_19_counterexample,
    Polyfold.EpGroupoid.Examples.isLR_trivialZ3,
    Polyfold.LocalizationLRCounterexample.not_naturallyEquivalent_id_inv,
    Polyfold.EpGroupoid.Examples.not_isEffective_trivialZ3⟩

/-- `B` is the project's literal statement `Theorem_10_3_19` in universe `0`. -/
theorem B_iff_Theorem : B ↔ EPLoc.Theorem_10_3_19.{0} :=
  ⟨fun h X Y hLR f f' => h (EPLoc.of X) (EPLoc.of Y) hLR f f',
    fun h X Y hLR f f' => h X.toEP Y.toEP hLR f f'⟩

/-- (LR) for `ℤ/3 × ℝ ⇉ ℝ` (trivial action), re-proved: its orbits are points. -/
theorem isLR_trivialZ3' : trivialZ3EpGroupoid.IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := trivialZ3EpGroupoid.theorem_7_1_13 x hO hxO
  refine ⟨R, hRO, fun β β' _ hπ => ⟨1, fun y hy => ?_⟩⟩
  obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ y hy)
  rw [R.Φ_one y hy]
  exact h1.symm.trans h2

/-- **`B` does not hold**: on `ℤ/3 × ℝ ⇉ ℝ`, which has (LR), `[X ←1 X →Inv X]` and `[1_X]` are
generalized isomorphisms with the same orbit map that differ. -/
theorem not_B : ¬ B := fun hB =>
  genInv_ne_genId (hB (EPLoc.of z3EP) (EPLoc.of z3EP) (Or.inl isLR_trivialZ3') genInv genId
    isGeneralizedIso_genInv isGeneralizedIso_genId orbitMap_genInv)

/-- Hence `A ⇒ B` is false (`A` holds). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B ⇒ A`, ex falso. -/
theorem B_to_A : B → A := fun hB => (not_B hB).elim

#rt_check RoundTrip.V10_65.not_B [Polyfold.LocalizationLRCounterexample.not_theorem_10_3_19,
  Polyfold.LocalizationLRCounterexample.theorem_10_3_19_counterexample,
  Polyfold.EpGroupoid.Examples.isLR_trivialZ3,
  Polyfold.LocalizationLRCounterexample.not_naturallyEquivalent_id_inv,
  Polyfold.EpGroupoid.Examples.not_isEffective_trivialZ3]
#rt_check RoundTrip.V10_65.B_to_A [Polyfold.LocalizationLRCounterexample.not_theorem_10_3_19,
  Polyfold.LocalizationLRCounterexample.theorem_10_3_19_counterexample,
  Polyfold.EpGroupoid.Examples.isLR_trivialZ3,
  Polyfold.LocalizationLRCounterexample.not_naturallyEquivalent_id_inv,
  Polyfold.EpGroupoid.Examples.not_isEffective_trivialZ3]
#rt_overlap RoundTrip.V10_65.B_to_A [Polyfold.LocalizationLRCounterexample.not_theorem_10_3_19,
  Polyfold.LocalizationLRCounterexample.theorem_10_3_19_counterexample,
  Polyfold.EpGroupoid.Examples.isLR_trivialZ3,
  Polyfold.LocalizationLRCounterexample.not_naturallyEquivalent_id_inv,
  Polyfold.EpGroupoid.Examples.not_isEffective_trivialZ3]
#print axioms RoundTrip.V10_65.not_B

end RoundTrip.V10_65
