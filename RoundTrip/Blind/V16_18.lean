import Polyfold
/-! Blind formalization of V16_18 (the text's Part II, §16.2, Definition 16.2.3, p. 719 of the
Springer 2021 book; 2017: Definition 16.14).

Text: `Tc` is the class of the structures `(TX, Tα)`; `(T(Z, c), Tc)` is a polyfold.

Choices:
- Setting: `Z : Type` (universe `0`), a polyfold `c : PolyfoldClass Z`.
- `T(Z, c)` and `Tα : |TX| → T(Z, c)`: the project's `c.TangentSpace` (with its topology, the one
  of Lemma 16.2.2) and `PolyfoldClass.tangentMap q hq` (`#print`ed: `|T𝔣|` for a generalized
  isomorphism `𝔣 : X → X₀`, `α₀ ∘ |𝔣| = α`).  `TX` is the project's tangent ep-groupoid
  `q.X.tangentAny` (Theorem 8.1.1).
- I do not use the project's `tangentStructure`; I build `(TX, Tα)` myself (`TStr`) from the three
  conditions of Definition 16.1.1, given as hypotheses.
- B is the conjunction of
  (1) `(TX, Tα)` is a polyfold structure on `T(Z, c)` for every `(X, α) ∈ c`: `|TX|` paracompact,
      `TX` satisfies (ZHOU), `Tα` a homeomorphism;
  (2) any two of these structures are equivalent (Definition 16.1.2), so they form one class;
  (3) that class is the project's `c.tangent` (the definition "`Tc` is the class of the
      `(TX, Tα)`"), so `(T(Z, c), Tc)` is a polyfold.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_18
open Polyfold

/-- The structure `(TX, Tα)` on `T(Z, c)` for `(X, α) = q ∈ c`. -/
noncomputable def TStr {Z : Type} [TopologicalSpace Z] (c : PolyfoldClass Z)
    (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (h1 : q.X.tangentAny.X.HasParacompactOrbitSpace)
    (h2 : q.X.tangentAny.X.IsZhou) (h3 : IsHomeomorph (PolyfoldClass.tangentMap q hq)) :
    PolyfoldStructure c.TangentSpace :=
  ⟨q.X.tangentAny, h1, h2, h3.homeomorph⟩

/-- Definition 16.2.3: the `(TX, Tα)`, `(X, α) ∈ c`, are polyfold structures on `T(Z, c)`, all
equivalent, and their class is `Tc`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z),
    (∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c),
      q.X.tangentAny.X.HasParacompactOrbitSpace ∧ q.X.tangentAny.X.IsZhou ∧
        IsHomeomorph (PolyfoldClass.tangentMap q hq)) ∧
    (∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) h1 h2 h3
        (q' : PolyfoldStructure Z) (hq' : ⟦q'⟧ = c) h1' h2' h3',
      (TStr c q hq h1 h2 h3).Equiv (TStr c q' hq' h1' h2' h3')) ∧
    (∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) h1 h2 h3,
      (⟦TStr c q hq h1 h2 h3⟧ : PolyfoldClass c.TangentSpace) = c.tangent)

end RoundTrip.V16_18
