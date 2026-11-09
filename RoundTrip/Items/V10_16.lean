import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_16

/-! Round trip for V10_16 (2021 Proposition 10.1.19, p. 477: (SLR) under equivalences).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`
(`B` lives in `EP.{0}`): `EP.proposition_10_1_19` (the proposition, from Proposition 10.1.9 in
`Chapter10/EquivalenceLR.lean`), `EP.isSLR_iff_of_isLR_iff` (the reduction: (SLR) passes along `F`
once (LR) passes along every equivalence `Xⁱ → Yⁱ`) and `EP.isLR_iff_lift_self` (that
hypothesis holds for `B = A`; a satisfiability witness, `Iff.rfl`).

`B`'s `SLR A` is `∀ i, (A.lift i).X.IsLR`, which is the project's `EP.IsSLR A` by `rfl`.

* `A_to_B`: `proposition_10_1_19` is `B` (with `SLR = EP.IsSLR` by `rfl`).
* `B_to_A`: `proposition_10_1_19` is `B`; `isSLR_iff_of_isLR_iff` has `B`'s conclusion under
  `B`'s hypothesis plus an extra one, so it follows from `B` without its extra hypothesis;
  `isLR_iff_lift_self` is `Iff.rfl` (proved outright, it does not involve `B`). -/

namespace RoundTrip.V10_16
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EP.proposition_10_1_19.{0}) ∧
  (type_of% @Polyfold.EP.isSLR_iff_of_isLR_iff.{0}) ∧
  (type_of% @Polyfold.EP.isLR_iff_lift_self.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EP.proposition_10_1_19.{0}, @Polyfold.EP.isSLR_iff_of_isLR_iff.{0},
    @Polyfold.EP.isLR_iff_lift_self.{0}⟩

/-- `B`'s (SLR) is the project's `EP.IsSLR`. -/
theorem SLR_eq (A : EP.{0}) : SLR A = A.IsSLR := rfl

theorem A_to_B : A → B := by
  rintro ⟨h, -, -⟩ A B F hF
  rw [SLR_eq, SLR_eq]
  exact h hF

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, fun _ _ _ _ => Iff.rfl⟩
  · intro A B F hF
    rw [← SLR_eq, ← SLR_eq]
    exact hB A B F hF
  · intro A B F hF _
    rw [← SLR_eq, ← SLR_eq]
    exact hB A B F hF

#rt_check RoundTrip.V10_16.A_to_B [Polyfold.EP.proposition_10_1_19,
  Polyfold.EP.isSLR_iff_of_isLR_iff, Polyfold.EP.isLR_iff_lift_self]
#rt_check RoundTrip.V10_16.B_to_A [Polyfold.EP.proposition_10_1_19,
  Polyfold.EP.isSLR_iff_of_isLR_iff, Polyfold.EP.isLR_iff_lift_self]
#rt_overlap RoundTrip.V10_16.B_to_A [Polyfold.EP.proposition_10_1_19,
  Polyfold.EP.isSLR_iff_of_isLR_iff, Polyfold.EP.isLR_iff_lift_self]

end RoundTrip.V10_16
