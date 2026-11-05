import Polyfold
/-! Blind formalization of V1_20 (the text's §1.3, Theorem 1.21, the chain rule, p. 13).

Text: let `U ⊂ C ⊂ E`, `V ⊂ D ⊂ F` and `W ⊂ Q ⊂ G` be relatively open subsets of partial
quadrants in sc-Banach spaces and `f : U → V`, `g : V → W` be `sc¹`.  Then `g ∘ f : U → W` is `sc¹`
and `T(g ∘ f) = Tg ∘ Tf`.

Choices:
- Setting: `E F G : ScBanach` (levels in `Type`, forced by `ScBanach`).  The maps are total
  functions `f : E₀ → F₀`, `g : F₀ → G₀` with `f(U) ⊆ V`, `g(V) ⊆ W`; only their values on `U`,
  `V` matter.  "Relatively open subset of a partial quadrant" is `IsRelOpenInQuadrant`
  (checked with `#print`).
- `sc¹` is the project's `IsSc1 U f` (Definition 1.14; checked with `#print`: there is a family
  `Df(x) : E₀ → F₀`, `x ∈ U₁`, of bounded operators such that `f` is `sc⁰`, `f : U₁ → F₀` has
  derivative `Df(x)|E₁` within `U₁` at each `x ∈ U₁`, and `Tf` is `sc⁰`).
- The tangent maps `Tf : TU → TF`, `Tf(x, h) = (f(x), Df(x)h)` on `TU = U₁ ⊕ E₀`, are the project's
  `tangentMap U f` (built with a chosen derivative family `scDeriv`).  I accept this choice: on
  `U₁` (locally convex with nonempty interior in `E₁`, so of unique differentiability) `Df(x)` is
  determined on `E₁`, hence on `E₀` by density of `E₁ ⊆ E₀`; so `Tf` is canonical on `TU`.
- `T(g ∘ f) = Tg ∘ Tf` is an equality of maps on `TU` (`E.tangentSet U`, checked: the pairs
  `(x, h) ∈ E₁ × E₀` with `x ∈ U₁`).
- "`g ∘ f : U → W`" is included as the (trivial) conjunct `(g ∘ f)(U) ⊆ W`.
-/
namespace RoundTrip.V1_20
open Polyfold

/-- The chain rule for `sc¹` maps between relatively open subsets of partial quadrants. -/
def B : Prop :=
  ∀ (E F G : ScBanach) (C U : Set (E.lvl 0)) (D V : Set (F.lvl 0)) (Q W : Set (G.lvl 0))
    (f : E.lvl 0 → F.lvl 0) (g : F.lvl 0 → G.lvl 0),
    IsRelOpenInQuadrant E C U → IsRelOpenInQuadrant F D V → IsRelOpenInQuadrant G Q W →
    Set.MapsTo f U V → Set.MapsTo g V W → IsSc1 U f → IsSc1 V g →
      Set.MapsTo (g ∘ f) U W ∧ IsSc1 U (g ∘ f) ∧
      Set.EqOn (tangentMap U (g ∘ f)) (tangentMap V g ∘ tangentMap U f) (E.tangentSet U)

end RoundTrip.V1_20
