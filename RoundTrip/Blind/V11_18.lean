import Polyfold
/-! Blind formalization of V11_18 (the Springer 2021 book, Part II, §11.3, Theorem 11.3.3,
p. 537).

Text: for a generalized isomorphism `f`: (1), (2) `f_*` and `f^*` map branched ep⁺-subgroupoids to
branched ep⁺-subgroupoids; they preserve (3) closedness, (4) compactness, (5) orbifold- and
manifold-type, (6) the dimensional decomposition.

Choices:
- Setting: `X`, `Y` objects of the project's bundled `EP.{0}` (all spaces in `Type`, as in the
  earlier blind files `V10_33.lean`–`V10_36.lean`, `V11_16.lean`); `f : X → Y` a morphism of the
  project's localization `EP(E⁻¹)` (`EPLoc.of X ⟶ EPLoc.of Y`); "generalized isomorphism": the
  project's `EPLoc.IsGeneralizedIso` (Definition 10.3.9, `#print`ed: some `g` with `f ≫ g = 𝟙`,
  `g ≫ f = 𝟙`).
- `f_*`, `f^*` (2021 p. 536: `f_* = Φ_*F^*`, `f^* = F_*Φ^*` on a representative
  `X ←F A →Φ Y`): the project's `Diagram.pushTheta`, `Diagram.pullTheta` (`#print`ed: exactly
  `d.Φ.pushforwardTheta (d.F.pullbackTheta Θ)` and `d.F.pushforwardTheta (d.Φ.pullbackTheta Θ')`,
  with `pushforwardTheta`, `pullbackTheta` `#print`ed and matching Definition 11.3.1).  Since the
  text computes `f_*`, `f^*` on a representative (and says separately that the result does not
  depend on it), B asserts the properties for every representative `d` of `f` (`EPLoc.homMk d =
  f`); this contains the project's `EPLoc.pushTheta f` (computed on the chosen representative)
  without relying on it.
- "branched ep⁺-subgroupoid", closed, compact, orbifold-type, manifold-type, dimensional
  decomposition: the project's `IsBranchedEpSubgroupoid`, `IsClosedBranched`,
  `IsCompactBranched`, `IsOrbifoldType`, `IsManifoldType`, `IsDimDecomposition` (all `#print`ed;
  Definitions 9.1.2, 9.1.6, 9.1.8, Proposition 9.1.11), exactly as in my `V11_17.lean`.
- "preserve" is read as an implication, for branched ep⁺-subgroupoids.  (6) is read as: every
  dimensional decomposition `(Θ_k)` of `Θ` goes to the dimensional decomposition `(f_*Θ_k)` of
  `f_*Θ` (the decomposition is not unique as stated, see `V9_9.lean`, so "the" decomposition is
  read as "any").
- Nothing looks false to me.
-/
namespace RoundTrip.V11_18
open Polyfold Polyfold.EPLocalization

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- **The properties (1)–(6) of Theorem 11.3.3** for a push-forward `push` and a pull-back
`pull` of functors `X → ℚ⁺`, `Y → ℚ⁺`. -/
def Thm1133B (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor')
    (push : (Obj → ℚ) → Obj' → ℚ) (pull : (Obj' → ℚ) → Obj → ℚ) : Prop :=
  -- (1), (2)
  (∀ Θ, X.IsBranchedEpSubgroupoid Θ → Y.IsBranchedEpSubgroupoid (push Θ)) ∧
  (∀ Θ', Y.IsBranchedEpSubgroupoid Θ' → X.IsBranchedEpSubgroupoid (pull Θ')) ∧
  -- (3) closedness
  (∀ Θ, X.IsBranchedEpSubgroupoid Θ → X.IsClosedBranched Θ → Y.IsClosedBranched (push Θ)) ∧
  (∀ Θ', Y.IsBranchedEpSubgroupoid Θ' → Y.IsClosedBranched Θ' → X.IsClosedBranched (pull Θ')) ∧
  -- (4) compactness
  (∀ Θ, X.IsBranchedEpSubgroupoid Θ → X.IsCompactBranched Θ → Y.IsCompactBranched (push Θ)) ∧
  (∀ Θ', Y.IsBranchedEpSubgroupoid Θ' → Y.IsCompactBranched Θ' →
    X.IsCompactBranched (pull Θ')) ∧
  -- (5) orbifold-type and manifold-type
  (∀ Θ, X.IsBranchedEpSubgroupoid Θ → EpGroupoid.IsOrbifoldType Θ →
    EpGroupoid.IsOrbifoldType (push Θ)) ∧
  (∀ Θ', Y.IsBranchedEpSubgroupoid Θ' → EpGroupoid.IsOrbifoldType Θ' →
    EpGroupoid.IsOrbifoldType (pull Θ')) ∧
  (∀ Θ, X.IsBranchedEpSubgroupoid Θ → X.IsManifoldType Θ → Y.IsManifoldType (push Θ)) ∧
  (∀ Θ', Y.IsBranchedEpSubgroupoid Θ' → Y.IsManifoldType Θ' → X.IsManifoldType (pull Θ')) ∧
  -- (6) the dimensional decomposition
  (∀ (Θ : Obj → ℚ) (Θk : ℕ → Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    X.IsDimDecomposition Θ Θk → Y.IsDimDecomposition (push Θ) (fun k => push (Θk k))) ∧
  (∀ (Θ' : Obj' → ℚ) (Θk' : ℕ → Obj' → ℚ), Y.IsBranchedEpSubgroupoid Θ' →
    Y.IsDimDecomposition Θ' Θk' → X.IsDimDecomposition (pull Θ') (fun k => pull (Θk' k)))

end

/-- Theorem 11.3.3: for a generalized isomorphism `f`, `f_*` and `f^*` (on any representative)
have the properties (1)–(6). -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f → Thm1133B X.X Y.X d.pushTheta d.pullTheta

end RoundTrip.V11_18
