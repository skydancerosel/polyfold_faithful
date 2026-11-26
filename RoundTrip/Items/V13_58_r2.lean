import Polyfold
import Polyfold.Chapter13.Theorem1357Atomic
import RoundTrip.Check
import RoundTrip.Blind.V13_58

set_option maxSynthPendingDepth 3

/-! Round trip for V13_58_r2 (refresh of V13_58: 2021 Theorem 13.5.7, p. 635; 2017: Theorem 13.10:
a structurable sc⁺-multisection is a locally finite commensurable sum of atomic ones).  `B` is the
existing blind statement `RoundTrip.V13_58.B`.

* `A`: the conjunction of the types of the four theorems of the row (`multisectionSmulFun_of_eq_zero`,
  `exists_orbit_nbhd`, `theorem_13_5_7`, `theorem_13_5_7_book`) and of the three theorems of
  `Chapter13/Theorem1357Atomic` (`theorem_13_5_7_isAtomic`, `theorem_13_5_7_isAtomic_book`,
  `theorem_13_5_7_isAtomic_sum`), at universe `0`.
* The new theorems rerun the construction of the proof with the partition of unity subordinate to
  `π⁻¹(Oₓ)`, `cl(Oₓ) ⊆ |Uᶜ(x)|`, where `Uᶜ(x)` is the connected component of `x` in the good
  system's `U(x)`, the domain of a natural representation with the `Φ`, `Γ` of `U(x)` and the
  properness property.  So every summand is `IsAtomic` (Definition 13.5.1 on the connected domain
  of a natural representation), as `B` asks.
* Main conjunct `theorem_13_5_7_isAtomic_sum`: the statement in the form of the text (common data
  `c`, a structure `o` of `Λ` over it, a family indexed by a type `J`).  It is `B` at universe `0`:
  `main_to_B` and `B_to_main` are each one application.  Hence `A_to_B`.
* `B_to_A` is not claimed: `theorem_13_5_7` and `theorem_13_5_7_isAtomic` decompose every
  structured tuple `T` over `T`'s own data, keeping its sections on every `U(x)`, with the family
  indexed by `X`; `B` gives some common data and an arbitrary index type.
-/

namespace RoundTrip.V13_58_r2
open Polyfold Polyfold.SBLocalization

abbrev B : Prop := RoundTrip.V13_58.B

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.multisectionSmulFun_of_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_orbit_nbhd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7_book.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7_isAtomic.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7_isAtomic_book.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_5_7_isAtomic_sum.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.multisectionSmulFun_of_eq_zero.{0},
    @Polyfold.SBLocalization.exists_orbit_nbhd.{0},
    @Polyfold.SBLocalization.theorem_13_5_7.{0},
    @Polyfold.SBLocalization.theorem_13_5_7_book.{0},
    @Polyfold.SBLocalization.theorem_13_5_7_isAtomic.{0},
    @Polyfold.SBLocalization.theorem_13_5_7_isAtomic_book.{0},
    @Polyfold.SBLocalization.theorem_13_5_7_isAtomic_sum.{0}⟩

/-- The main conjunct: Theorem 13.5.7 in the form of the text, with `IsAtomic` summands. -/
def Amain : Prop := type_of% @Polyfold.SBLocalization.theorem_13_5_7_isAtomic_sum.{0}

theorem main_to_B : Amain → B := by
  intro h A hpara hpu Λ hΛ
  exact h hpara hpu hΛ

theorem B_to_main : B → Amain := by
  intro h A hpara hpu Λ hΛ
  exact h A hpara hpu Λ hΛ

theorem A_to_B : A → B := fun h => main_to_B h.2.2.2.2.2.2

#rt_check RoundTrip.V13_58_r2.A_to_B [Polyfold.SBLocalization.multisectionSmulFun_of_eq_zero,
  Polyfold.SBLocalization.exists_orbit_nbhd, Polyfold.SBLocalization.theorem_13_5_7,
  Polyfold.SBLocalization.theorem_13_5_7_book, Polyfold.SBLocalization.theorem_13_5_7_isAtomic,
  Polyfold.SBLocalization.theorem_13_5_7_isAtomic_book,
  Polyfold.SBLocalization.theorem_13_5_7_isAtomic_sum]
#rt_check RoundTrip.V13_58_r2.main_to_B [Polyfold.SBLocalization.theorem_13_5_7_isAtomic,
  Polyfold.SBLocalization.theorem_13_5_7_isAtomic_book,
  Polyfold.SBLocalization.theorem_13_5_7_isAtomic_sum]
#rt_check RoundTrip.V13_58_r2.B_to_main [Polyfold.SBLocalization.theorem_13_5_7_isAtomic,
  Polyfold.SBLocalization.theorem_13_5_7_isAtomic_book,
  Polyfold.SBLocalization.theorem_13_5_7_isAtomic_sum]

end RoundTrip.V13_58_r2
