import Polyfold
/-! Blind formalization of V16_8 (the text's Part II, §16.1, Lemma 16.1.13, p. 712 of the
Springer 2021 book; 2017: Lemma 16.1).

Text: equivalent structures give `d_{(X,β)} = d_{(X',β')}`, where `d_{(X,β)}(z) = d_X(x)` for
`β(|x|) = z`.

Choices:
- Setting: `Z : Type` (universe `0`), polyfold structures `s t : PolyfoldStructure Z`, equivalence
  `PolyfoldStructure.Equiv` (Definition 16.1.2).
- `d_X(x)`: the degeneracy index of the object M-polyfold of `X` at the object `x`
  (`s.X.X.PObj.degIndex x`, Definition 2.4.1 / 7.1.5).
- I do not use the project's `PolyfoldStructure.degIndex` (it is `degIndexOrbit ∘ β⁻¹`); instead
  I state the lemma directly through its defining formula: whenever `β(|x|) = z = β'(|x'|)` for an
  object `x` of `X` and an object `x'` of `X'`, then `d_X(x) = d_{X'}(x')`.  This contains both
  the claim `d_{(X,β)} = d_{(X',β')}` and the fact that the formula does not depend on the
  choice of `x` (take `s = t` when `s.Equiv s`; I do not add reflexivity).
- `|x|` is the class of `x` in the orbit space `Quotient s.X.X.orbitSetoid`
  (`GroupoidStr.OrbitSpace` is reducibly this quotient).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_8
open Polyfold

/-- Lemma 16.1.13: for equivalent polyfold structures, `d_X(x) = d_{X'}(x')` whenever
`β(|x|) = β'(|x'|)`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (s t : PolyfoldStructure Z), s.Equiv t →
    ∀ (x : s.X.Obj) (x' : t.X.Obj),
      s.β (Quotient.mk _ x) = t.β (Quotient.mk _ x') →
        s.X.X.PObj.degIndex x = t.X.X.PObj.degIndex x'

end RoundTrip.V16_8
