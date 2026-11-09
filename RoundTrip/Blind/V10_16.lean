import Polyfold
/-! Blind formalization of V10_16 (the text's Part II, §10.1, Proposition 10.1.19, p. 477 of the
Springer 2021 book; new in the 2021 edition).

Text: if `F` is an equivalence, `X` satisfies (SLR) iff `Y` does.

Choices:
- Setting: as in my `RoundTrip/Blind/V10_15.lean`: the lifts `Xⁱ` need bundled ep-groupoids, so
  `A B : EP.{0}` (spaces in `Type`, universe 0) and `F : EpFunctor A.X B.X`.
- "equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1, read with
  `#print`, characterized in `RoundTrip/Blind/V10_1.lean`).
- (SLR) (2021 Definition 7.4.23): (LR) for every `Xⁱ`, `i ≥ 0`, written out as `SLR` (identical
  to the project's `EP.IsSLR`, not used).  `Xⁱ` is `A.lift i` (read with `#print`).  (LR) is
  the project's `EpGroupoid.IsLR` (2021 Definition 7.4.19), read with `#print`: for every `x` and
  every open `O ∋ x` there is a natural representation `U(x) ⊆ O` such that every
  sc-diffeomorphism `β : U(x) → U(x)` with `|β(y)| = |y|` for `y ∈ U(x)` equals `Φ(g)` on `U(x)`
  for some `g ∈ G_x`.  Trusted as the text's notion.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_16
open Polyfold

/-- (SLR), 2021 Definition 7.4.23: (LR) for every `Xⁱ`. -/
def SLR (A : EP) : Prop := ∀ i : ℕ, (A.lift i).X.IsLR

/-- Proposition 10.1.19: (SLR) is invariant under equivalences. -/
def B : Prop :=
  ∀ (A B : EP.{0}) (F : EpFunctor A.X B.X), F.IsEquivalence → (SLR A ↔ SLR B)

end RoundTrip.V10_16
