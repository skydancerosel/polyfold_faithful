import Polyfold
/-! Blind formalization of V16_11 (the text's Part II, §16.1, Lemma 16.1.19, p. 714 of the
Springer 2021 book; 2017: Lemma 16.2).

Text: if `(X, α) ∼ (Y, β)` and `X` is tame, so is `Y`.

Choices:
- Setting: `Z : Type` (universe `0`), polyfold structures `s t : PolyfoldStructure Z` on the same
  space, equivalence `PolyfoldStructure.Equiv` (Definition 16.1.2: a generalized isomorphism
  `𝔣 : X → Y` with `α = β ∘ |𝔣|`).
- "`X` is tame": Definition 7.1.6, the project's `EpGroupoid.IsTame` (`#print`ed: the object
  M-polyfold is tame).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_11
open Polyfold

/-- Lemma 16.1.19: tameness passes along an equivalence of polyfold structures. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (s t : PolyfoldStructure Z), s.Equiv t →
    s.X.X.IsTame → t.X.X.IsTame

end RoundTrip.V16_11
