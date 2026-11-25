import Polyfold
/-! Blind formalization of V16_5 (the text's Part II, §16.1, Proposition 16.1.4, p. 708 of the
Springer 2021 book; 2017: Proposition 16.2).

Text: for equivalent `(X, α)`, `(Y, β)`: (1) `X` admits sc-smooth bump functions iff `Y` does;
(2) `X` admits sc-smooth partitions of unity iff `Y` does.

Choices:
- Setting: `Z : Type` (universe `0`), two polyfold structures `s t : PolyfoldStructure Z`
  (Definition 16.1.1: an ep-groupoid with paracompact orbit space, (ZHOU), and a homeomorphism
  `|X| ≃ₜ Z`), "equivalent" = the project's `PolyfoldStructure.Equiv` (`#print`ed: a generalized
  isomorphism `𝔣 : X → Y` with `α = β ∘ |𝔣|`, Definition 16.1.2).
- "the ep-groupoid `X` admits sc-smooth bump functions": I read this as the text's notion for an
  ep-groupoid, Definition 12.3.1 (the project's `EpGroupoid.AdmitsBumpFunctions`, `#print`ed:
  for every object `x` and every saturated open `U ∋ x` an sc-smooth `f : X → ℝ`, not
  identically `0`, with `supp f ⊆ U` and `f ∘ s = f ∘ t` on morphisms).  Doubt: the text might
  instead mean the object M-polyfold admits bump functions (Definition 5.3.1,
  `X.PObj.AdmitsBumpFunctions`); I did not use that reading.
- "admits sc-smooth partitions of unity": Definition 7.5.5, the project's
  `EpGroupoid.HasScPartitionsOfUnity` (saturated open covers, invariant subordinate sc-smooth
  partitions of unity, locally finite in the saturated sense).
- The equivalence is used in the given direction `s ∼ t`; B is the conjunction of the two `↔`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_5
open Polyfold

/-- Proposition 16.1.4: bump functions and sc-smooth partitions of unity transfer along an
equivalence of polyfold structures. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (s t : PolyfoldStructure Z), s.Equiv t →
    (s.X.X.AdmitsBumpFunctions ↔ t.X.X.AdmitsBumpFunctions) ∧
    (s.X.X.HasScPartitionsOfUnity ↔ t.X.X.HasScPartitionsOfUnity)

end RoundTrip.V16_5
