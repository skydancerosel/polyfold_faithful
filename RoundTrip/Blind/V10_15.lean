import Polyfold
/-! Blind formalization of V10_15 (the text's Part II, §10.1, Proposition 10.1.18, p. 476 of the
Springer 2021 book; new in the 2021 edition).

Text: if `F` is an equivalence, `X` satisfies (SLUC) iff `Y` does.

Choices:
- Setting: the iterated lifts `Xⁱ` entering (SLUC) are defined in the project for bundled
  ep-groupoids only, so `X`, `Y` are `A B : EP.{0}` (types in `Type`, universe 0, their
  topologies, the ep-groupoids `A.X`, `B.X`) and `F : EpFunctor A.X B.X` (as in
  `RoundTrip/Blind/V8_45.lean`, `V8_52.lean`).
- "equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1, read with
  `#print`, characterized in `RoundTrip/Blind/V10_1.lean`).
- (SLUC) (2021 Definition 7.4.12): (LUC) for every `Xⁱ`, `i ≥ 0`, written out as `SLUC`
  (identical to the project's `EP.IsSLUC`, which I did not use).  `Xⁱ` is the project's
  `A.lift i` (`X⁰ = X`, `X^{i+1} = (Xⁱ)¹`, read with `#print`); (LUC) is the project's
  `EpGroupoid.IsLUC` (2021 Definition 7.2.18, read with `#print`; trusted as in V8_45).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_15
open Polyfold

/-- (SLUC), 2021 Definition 7.4.12: (LUC) for every `Xⁱ`. -/
def SLUC (A : EP) : Prop := ∀ i : ℕ, (A.lift i).X.IsLUC

/-- Proposition 10.1.18: (SLUC) is invariant under equivalences. -/
def B : Prop :=
  ∀ (A B : EP.{0}) (F : EpFunctor A.X B.X), F.IsEquivalence → (SLUC A ↔ SLUC B)

end RoundTrip.V10_15
