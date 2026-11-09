import Polyfold
/-! Blind formalization of V9_23 (the text's Part II, §9.2, Definition 9.2.12, p. 418 of the
Springer 2021 book; 2017: Definition 9.6, p. 306): for a branched ep⁺-subgroupoid
`Θ : X → ℚ⁺` there is a well-defined branched ep⁺-subgroupoid `TΘ : TX → ℚ⁺` with
`TΘ(h) = 0` for `h ∈ T_xX` with `Θ(x) = 0`, and `TΘ(h) = ∑_{i : h ∈ TMᵢ} σᵢ` for `h` over
`U(x)`, `(Mᵢ)`, `(σᵢ)` a local branching structure on `U(x)`; by the previous discussion this
does not depend on the structure, and the local definitions fit together.

Choices:
- This item is a definition with a claim ("well-defined branched ep⁺-subgroupoid").  B is about
  the project's `EpGroupoid.tangentTheta X Θ` (its `TΘ`), and says: (1) `TΘ(h) = 0` if
  `Θ(p h) = 0`; (2) for EVERY `x ∈ supp Θ`, EVERY local branching structure `B` of `Θ` at `x` and
  every `h` with `p h ∈ U(x)`, `TΘ(h) = ∑_{i : h ∈ T_{p h} Mᵢ} σᵢ` (this "for every structure and
  every `x`" is the text's "does not depend on the structure" and "the local definitions fit
  together"); (3) `TΘ` is a branched ep⁺-subgroupoid (project's `IsBranchedEpSubgroupoid`) of the
  tangent ep-groupoid `TX` (project's `EpGroupoid.tangentEpGroupoid`).  (1) and (2) determine a
  function on `TX`, so B pins down the project's definition.
- Setting: ep-groupoid `X : EpGroupoid Obj Mor`, `Obj Mor : Type` (universe 0, as in the
  Chapter 7 blind files), `Θ` a branched ep⁺-subgroupoid of `X`; no further hypothesis (the text
  states none).
- `TX`, `p`, `TMᵢ`: the objects of `TX` are Part I's tangent vectors `X.PObj.TangentSpace`;
  `p h` is the base point `levelVal 1 (tangentProj h)` of `h` (a point of `X₁`, viewed in `X`);
  `h ∈ TMᵢ` is `h ∈ T_{p h}Mᵢ` with the project's `MPolyfold.submanifoldTangent`.
- Nothing looks false to me in the text's claim.  (The text does not discuss the paracompactness
  of `|supp TΘ|` required by the 2021 Definition 9.1.2 (1); I include it, as part of being a
  branched ep⁺-subgroupoid, without extra hypotheses.)
-/
namespace RoundTrip.V9_23
open Polyfold

/-- The base point `p(h) ∈ X` of a tangent vector `h ∈ TX`. -/
def baseB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (h : X.PObj.TangentSpace) : Obj :=
  X.PObj.levelVal 1 (X.PObj.tangentProj h)

open Classical in
/-- **Definition 9.2.12**: the tangent `TΘ` vanishes over the zero set of `Θ`, is given over the
domain of every local branching structure by `∑_{h ∈ TMᵢ} σᵢ`, and is a branched
ep⁺-subgroupoid of `TX`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
      -- (1) `TΘ(h) = 0` over `{Θ = 0}`
      (∀ h : X.PObj.TangentSpace, Θ (baseB X h) = 0 → X.tangentTheta Θ h = 0) ∧
      -- (2) the local formula, for every local branching structure
      (∀ x ∈ EpGroupoid.supp Θ, ∀ (B : X.LocalBranchingStructure Θ x) (h : X.PObj.TangentSpace),
        baseB X h ∈ B.U →
          X.tangentTheta Θ h =
            ∑ i with h ∈ X.PObj.submanifoldTangent (B.M i) (baseB X h), B.σ i) ∧
      -- (3) `TΘ` is a branched ep⁺-subgroupoid of `TX`
      X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta Θ)

end RoundTrip.V9_23
