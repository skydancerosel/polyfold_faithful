import Polyfold
/-! Blind formalization of V8_52 (the 2021 book, Part II, §8.1, Proposition 8.1.17 (2), p. 371).

Text: if `X` has (SLUC), so has `TX`.  (The proof: by (1) every `T(Xⁱ)` has (LUC), and
naturally `(TX)ⁱ = T(Xⁱ)`.)

Choices:
- The iterated lifts `Xⁱ` are defined in the project for bundled ep-groupoids only, so the
  statement quantifies over `A : EP.{0}` (types in `Type`, their topologies, the ep-groupoid
  `A.X`); `Xⁱ` is the project's `A.lift i` (`X⁰ = X`, `X^{i+1} = (Xⁱ)¹`, read with `#print`) and
  `TX` is `A.tangentEP` (the bundled `A.X.tangentEpGroupoid`, in `EP.{1}`, read with `#print`).
- (LUC): the project's `EpGroupoid.IsLUC` (2021 Definition 7.2.18, read with `#print`: every
  object has a natural representation on which `Φ(g) = id` on a nonempty open subset forces
  `Φ(g) = id`).  (SLUC) (2021 Definition 7.4.12) = (LUC) for every `Xⁱ`, written out in the
  statement: the hypothesis is (LUC) of every `Xⁱ`, the conclusion (LUC) of every `(TX)ⁱ` (the
  item's "for every `(TX)ⁱ`").
- "naturally `(TX)ⁱ = T(Xⁱ)`" is a step of the proof (an identification of ep-groupoids), not
  part of the claim; it is not formalized.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_52
open Polyfold

/-- Proposition 8.1.17 (2): if every `Xⁱ` has (LUC), then every `(TX)ⁱ` has (LUC). -/
def B : Prop :=
  ∀ A : EP.{0}, (∀ i : ℕ, (A.lift i).X.IsLUC) → ∀ i : ℕ, (A.tangentEP.lift i).X.IsLUC

end RoundTrip.V8_52
