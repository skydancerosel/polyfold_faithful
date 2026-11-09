import Polyfold
/-! Blind formalization of V11_25 (the Springer 2021 book, Part II, §11.3, Theorem 11.3.9,
p. 542, "oriented boundaries, for a representative").

Text: for oriented tame branched ep⁺-subgroupoids, `∂(f_*Θ̂) = f_*(∂Θ̂)` and
`∂(f^*Θ̂') = f^*(∂Θ̂')`; the proof is left to the reader.

Choices:
- Setting: objects `X Y : EP.{0}` (all spaces in `Type`), `f` a generalized isomorphism of the
  project's `EP(E⁻¹)` (`EPLoc.IsGeneralizedIso`, `#print`ed); "for a representative": `f_*`,
  `f^*` are computed on a representative `d = X ←F A →G Y` of `f` (`EPLoc.homMk d = f`) and B
  asserts the identities for every representative.  `f_*`, `f^*` on functors and on sections:
  the project's `Diagram.pushTheta`, `pullTheta`, `pushSection`, `pullSection` (`#print`ed; see
  my `V11_18.lean`, `V11_20.lean`).
- "oriented tame branched ep⁺-subgroupoid" `Θ̂ = (Θ, T̂_Θ)`: `IsBranchedEpSubgroupoid Θ`,
  `IsTameBranched Θ` (Definition 9.3.6), `IsOrientation Θ T` (Definition 9.3.2), all project
  definitions (`#print`ed; compared with the text in `V9_30.lean`, `V9_38.lean`).
- `∂Θ̂ = (∂Θ, T̂_{∂Θ})` (Definition 9.3.10): `∂Θ` the project's `boundaryTheta` (see my
  `V11_24.lean`), `T̂_{∂Θ}` the project's `boundaryLift bd T` (`#print`ed: the image under the
  boundary operation `bd : T_y(M, o) ↦ T_y(∂M, o_{∂M})` of Definition 9.3.8 of the degree-1
  part of `T̂_Θ(y)`; compared with (9.12) in `V9_38.lean`).  The project has no canonical
  boundary operation (`boundaryLift` takes `bd` as an argument), so B quantifies over operations
  `bd_X`, `bd_Y` on `X` and `Y` that are natural (`IsNaturalBdB`): `bd_Y(Tg_* L̂) = Tg_*(bd_X L̂)`
  for every sc-diffeomorphism `g : W → W'` between open subsets of the object spaces of `X` and
  `Y` and every oriented subspace `L̂ ⊆ T_zX` of degree `1` (and the same from `Y` to `X`).  The
  canonical operation of Definition 9.3.8 (outward normal first) is natural in this sense, so
  this hypothesis is satisfiable and does not restrict the text's claim; but it is my addition,
  and B is stronger than the text (which concerns the canonical `bd` only).  `Tg`: Part I's
  `tangentMapOn`; `Tg_*`: `OrTangent.map`; "degree 1": the project's `HasSubDegree … 1`
  (`#print`ed, as used inside `boundaryLift`).
- Pairs are compared componentwise; all four maps produce functions vanishing off `Y_∞` (resp.
  `X_∞`), so the section identities are equalities of functions.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_25
open Polyfold Polyfold.EPLocalization

/-- `bd`, `bd'` are boundary operations on `P`, `Q` that commute with the tangent maps of all
sc-diffeomorphisms between open subsets of `P` and `Q`, in degree `1`. -/
def IsNaturalBdB {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : MPolyfold X) (Q : MPolyfold Y)
    (bd : P.OrTangent → P.OrTangent) (bd' : Q.OrTangent → Q.OrTangent) : Prop :=
  ∀ (g : X → Y) (g' : Y → X) (W : Set X) (W' : Set Y) (hg : P.IsScDiffeoOn Q g g' W W'),
    IsOpen W → IsOpen W' → ∀ z ∈ W, ∀ L : P.OrTangent, P.IsOrientedAt z L →
      P.HasSubDegree z 1 L →
        bd' (MPolyfold.OrTangent.map (MPolyfold.tangentMapOn hg.isScSmoothOn) L) =
          MPolyfold.OrTangent.map (MPolyfold.tangentMapOn hg.isScSmoothOn) (bd L)

/-- Theorem 11.3.9: `∂(f_*Θ̂) = f_*(∂Θ̂)` and `∂(f^*Θ̂') = f^*(∂Θ̂')` for oriented tame branched
ep⁺-subgroupoids, on every representative of `f`. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
    ∀ (bdX : X.X.PObj.OrTangent → X.X.PObj.OrTangent)
      (bdY : Y.X.PObj.OrTangent → Y.X.PObj.OrTangent),
      IsNaturalBdB X.X.PObj Y.X.PObj bdX bdY → IsNaturalBdB Y.X.PObj X.X.PObj bdY bdX →
      (∀ (Θ : X.Obj → ℚ) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ),
        X.X.IsBranchedEpSubgroupoid Θ → X.X.IsTameBranched Θ → X.X.IsOrientation Θ T →
          Y.X.boundaryTheta (d.pushTheta Θ) = d.pushTheta (X.X.boundaryTheta Θ) ∧
          Y.X.boundaryLift bdY (d.pushSection T) = d.pushSection (X.X.boundaryLift bdX T)) ∧
      (∀ (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ),
        Y.X.IsBranchedEpSubgroupoid Θ' → Y.X.IsTameBranched Θ' → Y.X.IsOrientation Θ' T' →
          X.X.boundaryTheta (d.pullTheta Θ') = d.pullTheta (Y.X.boundaryTheta Θ') ∧
          X.X.boundaryLift bdX (d.pullSection T') = d.pullSection (Y.X.boundaryLift bdY T'))

end RoundTrip.V11_25
