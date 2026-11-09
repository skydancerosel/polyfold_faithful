import Polyfold
/-! Blind formalization of V11_23 (the Springer 2021 book, Part II, §11.3, Theorem 11.3.7,
p. 541).

Text: `(Tf)_*TΘ = T(f_*Θ)` and `(Tf)^*TΘ' = T(f^*Θ')` for `Tf = [TX ← TA → TY]`; the proof is
left to the reader.

Choices:
- Setting: objects `X Y : EP.{1}` (all spaces in `Type 1`), because the project's tangent
  ep-groupoid `EP.tangent` and the tangent diagram `Diagram.tangent` are only defined on
  `EP.{max u 1}`; nothing in the statement depends on the universe.  `f : X → Y` a generalized
  isomorphism of the project's `EP(E⁻¹)` (`EPLoc.IsGeneralizedIso`, `#print`ed), the setting of
  §11.3; representatives `d = X ←F A →G Y` the project's `Diagram` with `EPLoc.homMk d = f`.
- `Tf = [TX ← TA → TY]`: computed on the tangent diagram `TX ←TF TA →TG TY` of a representative
  `d` of `f`, the project's `Diagram.tangent` (`#print`ed: `⟨TA, TF, _, TG⟩` with
  `EpFunctor.tangent`, Part I's tangent maps); I do not go through the project's
  `EPLoc.tangentFunctor` (whose action on morphisms is this construction, `#print`ed).
- `f_*`, `f^*` and `(Tf)_*`, `(Tf)^*` of functors to `ℚ⁺`: the project's `Diagram.pushTheta`,
  `Diagram.pullTheta` on the respective representatives (`#print`ed; `f_* = G_*F^*`,
  `f^* = F_*G^*`).
- `TΘ : TX → ℚ⁺` (Definition 9.2.4: `TΘ(h) = ∑_{i : h ∈ TMᵢ} σᵢ`, via `T_Θ`): the project's
  `tangentTheta` (`#print`ed: the weight of the tangent vector `h ∈ T_xX` in the sum `T_Θ(x)`,
  `x` the base point at level 1).
- `Θ`, `Θ'`: branched ep⁺-subgroupoids (`IsBranchedEpSubgroupoid`), for which `TΘ` is defined.
  The equalities are equalities of functions on all of `TY`, `TX`.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_23
open Polyfold Polyfold.EPLocalization

/-- Theorem 11.3.7: `(Tf)_*TΘ = T(f_*Θ)` and `(Tf)^*TΘ' = T(f^*Θ')`, with `Tf` computed on the
tangent diagram of a representative of `f`. -/
def B : Prop :=
  ∀ (X Y : EP.{1}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ Θ : X.Obj → ℚ, X.X.IsBranchedEpSubgroupoid Θ →
        (Diagram.tangent.{0} d).pushTheta (X.X.tangentTheta Θ) =
          Y.X.tangentTheta (d.pushTheta Θ)) ∧
      (∀ Θ' : Y.Obj → ℚ, Y.X.IsBranchedEpSubgroupoid Θ' →
        (Diagram.tangent.{0} d).pullTheta (Y.X.tangentTheta Θ') =
          X.X.tangentTheta (d.pullTheta Θ'))

end RoundTrip.V11_23
