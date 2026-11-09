import Polyfold
/-! Blind formalization of V10_62 (the Springer 2021 book, Part II, §10.1, Proposition 10.1.9,
pp. 468–470; new in the 2021 edition): (LR) under equivalences.

Text: if `F : X → Y` is an equivalence and one of `X`, `Y` has the local regularity property, so
has the other.  (The proof transports `U(x)` along `Q = ψ̂ ∘ F`; that is the proof, not part of
the claim.)

Choices:
- Setting: universe 0 (all spaces in `Type`), `X`, `Y` objects of the project's bundled `EP.{0}`
  (ep-groupoids, Definition 7.3 with its Hausdorff and paracompactness instances), `F` an
  sc-smooth functor `EpFunctor X.X Y.X` (the text's sc-smooth functors, as in
  `RoundTrip/Blind/V7_9.lean`).
- "equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1; compared with
  the text in `RoundTrip/Blind/V10_1.lean`: full and faithful, `|F|` a homeomorphism, local
  sc-diffeomorphism on objects).
- "(LR)": the project's `EpGroupoid.IsLR` (2021 Definition 7.4.19, read with `#print`: for every
  `x` and open `O ∋ x` a natural representation `U(x) ⊆ O` such that every sc-diffeomorphism
  `β : U(x) → U(x)` with `|β(y)| = |y|` on `U(x)` is `Φ(g)` on `U(x)` for some `g ∈ G_x`), as in
  `RoundTrip/Blind/V8_48.lean` and `RoundTrip/Blind/V10_49.lean`.
- "if one has (LR), so has the other": `X.IsLR ↔ Y.IsLR`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_62
open Polyfold

/-- **Proposition 10.1.9**: an equivalence `F : X → Y` transports (LR) both ways. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (F : EpFunctor X.X Y.X), F.IsEquivalence → (X.X.IsLR ↔ Y.X.IsLR)

end RoundTrip.V10_62
