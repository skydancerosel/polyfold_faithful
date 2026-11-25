import Polyfold
/-! Blind formalization of V17_53 (the text's §17.2, Proposition 17.2.16, pp. 782–783, (17.52)
of the Springer 2021 book; 2017: Proposition 17.5).

Text: `|TC|` carries a natural metrizable topology (from `|TX_Ψ|` via `TΓ`, independent of `Ψ`),
`TC` is a GCT and `|P| : |TC| → |C_1|` is continuous.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`; `hU : S.HasUniformizers` (`F(α) ≠ ∅` for all `α`; the project's
  `TΓ_Ψ` is built with it, and the text presupposes the reference uniformizers `Ψ_α`,
  pp. 769–771) and `hc : S.HasCoveringUniformizers` (the footprints cover `|C|`; it is implied by
  `hU`, and is needed to name the topology of `|C_1|`, which the text transports from a covering
  set, Theorem 17.1.28).
- `TC` = the project's groupoid `S.tangentCatGroupoid` (Definition 17.2.6); `|TC|` its orbit
  space.  `X_Ψ` = the project's model `S.modelEpGroupoid c.Ψ` of a covering family `c`,
  `TX_Ψ` its tangent ep-groupoid (`tangentEpGroupoid`, Part II), `|TX_Ψ|` its orbit space with
  the quotient topology, and `TΓ_Ψ : TX_Ψ → TC` the project's `S.tangentModelFunctor hU c.Ψ`
  ((17.52)).  These are the text's constructions, taken from the vocabulary; the project's
  `tangentOrbitTopology` and `tangentGCT` are not used.
- "natural metrizable topology from `|TX_Ψ|` via `TΓ`, independent of `Ψ`": a topology `T` on
  `|TC|` which is metrizable and for which `|TΓ_Ψ| : |TX_Ψ| → |TC|` is a homeomorphism for EVERY
  covering family `Ψ` (so `T` is transported from each `|TX_Ψ|` and does not depend on `Ψ`).
- "`TC` is a GCT": `TC` is a groupoidal category (finite morphism sets, Lemma 17.2.7, built into
  the project's `S.tangentCategory`, universe `1`); with the metrizable `T` it is a GCT
  (`GCT.mk S.tangentCategory` with `T`).  Given the metrizability conjunct this adds no further
  condition, so it is not a separate conjunct of B.
- `P : TC → C_1` = the project's `S.tangentCatProj` ((17.33), (17.34)); `|C_1|` carries the
  topology of Theorem 17.1.28, the project's `S.levelOneGCT hc` (whose groupoid is `S.regSub 1`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_53
open Polyfold

/-- Proposition 17.2.16: `|TC|` has a natural metrizable topology (transported from every
`|TX_Ψ|` along `|TΓ_Ψ|`), `TC` is a GCT, and `|P| : |TC| → |C_1|` is continuous. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (hc : S.HasCoveringUniformizers),
    ∃ T : TopologicalSpace S.tangentCatGroupoid.OrbitSpace,
      @TopologicalSpace.MetrizableSpace _ T ∧
      (∀ c : S.CoveringFamily,
        @IsHomeomorph _ _ _ T (S.tangentModelFunctor hU c.Ψ).orbitMap) ∧
      @Continuous _ _ T (S.levelOneGCT hc).top S.tangentCatProj.orbitMap

end RoundTrip.V17_53
