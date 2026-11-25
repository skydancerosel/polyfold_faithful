import Polyfold
/-! Blind formalization of V16_17 (the text's Part II, §16.2, Lemma 16.2.2, p. 718 of the
Springer 2021 book; 2017: Lemma 16.4).

Text: `T(Z, c)` has a unique natural topology for which every `Tα` is a homeomorphism; it is
metrizable.

Choices:
- Setting: `Z : Type` (universe `0`), a polyfold `c : PolyfoldClass Z` (Definition 16.1.3).
- The set `T(Z, c)` and the maps `Tα : |TX| → T(Z, c)` for `(X, α) ∈ c` (2021 p. 717, (16.4)):
  the project's `c.TangentSpace` (a model of the set, `|TX₀|` for the chosen `(X₀, α₀) = c.out`)
  and `PolyfoldClass.tangentMap q hq` (`#print`ed: `|T𝔣|` for a generalized isomorphism
  `𝔣 : X → X₀` with `α₀ ∘ |𝔣| = α`, which is the text's `Tα`).  `|TX|` carries its orbit-space
  topology.
- I do NOT use the topology instance the project puts on `c.TangentSpace`: B quantifies over
  topologies `τ` on the set.  "Unique topology for which every `Tα` is a homeomorphism" is
  `∃! τ, ∀ (X, α) ∈ c, Tα is a homeomorphism for τ`; "it is metrizable" is: every such `τ`
  (i.e. the unique one) is metrizable (`TopologicalSpace.MetrizableSpace`).
- "every `Tα`": every polyfold structure `q` with `⟦q⟧ = c` (all structures in `c` live on `Z`).
- "natural" is not formalized beyond the characterization.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_17
open Polyfold

/-- `τ` makes every `Tα : |TX| → T(Z, c)`, `(X, α) ∈ c`, a homeomorphism. -/
def AllTαHomeo {Z : Type} [TopologicalSpace Z] (c : PolyfoldClass Z)
    (τ : TopologicalSpace c.TangentSpace) : Prop :=
  ∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c),
    @IsHomeomorph _ _ _ τ (PolyfoldClass.tangentMap q hq)

/-- Lemma 16.2.2: there is exactly one topology on `T(Z, c)` making every `Tα` a homeomorphism,
and it is metrizable. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z),
    (∃! τ : TopologicalSpace c.TangentSpace, AllTαHomeo c τ) ∧
    (∀ τ : TopologicalSpace c.TangentSpace, AllTαHomeo c τ →
      @TopologicalSpace.MetrizableSpace _ τ)

end RoundTrip.V16_17
