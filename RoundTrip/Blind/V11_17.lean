import Polyfold
/-! Blind formalization of V11_17 (the Springer 2021 book, Part II, §11.3, Theorem 11.3.3, the
proof for an equivalence, pp. 537–538).

Text: for an equivalence `F : X → Y`, the local branching structures of `Θ` at `x` are carried
by `ψ̂ ∘ F` (for `ψ : F(x) → y`) to local branching structures of `F_*Θ` at `y`; the properties of
Theorem 11.3.3 follow from `|F|` being a homeomorphism.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'` (the project's
  Definition 7.1.3 structure, as in the earlier blind files `V10_13.lean`, `V10_14.lean`), all four
  spaces in `Type` (universe 0), with the Hausdorff and paracompact instances `EpGroupoid` asks
  for.  "Equivalence": the project's `EpFunctor.IsEquivalence` (Definition 10.1.1, `#print`ed:
  full, faithful, `|F|` a homeomorphism, a local sc-diffeomorphism on objects).
- `F_*Θ`, `F^*Θ'` (Definition 11.3.1): the project's `EpFunctor.pushforwardTheta`,
  `EpFunctor.pullbackTheta`, read with `#print`: `F^*Θ' = Θ' ∘ F`, and `(F_*Θ)(y) = Θ(x)` for a
  chosen `x` with `F(x) ≅ y` (junk `0` if there is none, which does not happen for an
  equivalence).  Exactly the text's formulas.
- "branched ep⁺-subgroupoid", "local branching structure": the project's
  `IsBranchedEpSubgroupoid`, `LocalBranchingStructure` (`#print`ed; they match Definition 9.1.2 as
  read in `V9_1.lean`).  "closed", "compact" (Definition 9.1.6): `IsClosedBranched`,
  `IsCompactBranched` (`#print`ed: `|supp Θ|` closed / compact in `|X|`).  "orbifold-type",
  "manifold-type" (Definition 9.1.8): `IsOrbifoldType`, `IsManifoldType` (`#print`ed).
  "dimensional decomposition `Θ = Θ₀ + Θ₁ + ⋯`" (Proposition 9.1.11): the project's
  `IsDimDecomposition` (`#print`ed: every `Θ_k` a `k`-dimensional branched ep⁺-subgroupoid,
  pointwise finitely many nonzero, `Θ = ∑ᶠ Θ_k`).  Since the decomposition is not unique as stated
  (see `V9_9.lean`), property (6) is read as: every dimensional decomposition `(Θ_k)` of `Θ` is
  carried to the dimensional decomposition `(F_*Θ_k)` of `F_*Θ` (and likewise for `F^*`).
- "the properties of Theorem 11.3.3" (`Thm1133B`, the same shape as in `V11_18.lean`): (1) `F_*`
  and (2) `F^*` map branched ep⁺-subgroupoids to branched ep⁺-subgroupoids; for branched ones they
  preserve (3) closedness, (4) compactness, (5) orbifold- and manifold-type, (6) dimensional
  decompositions.  "Preserve" is read as an implication (the converse follows from `F^*F_* = id`).
- "carried by `ψ̂ ∘ F`" (`TransportB`): for a branched `Θ`, an object `x`, a local branching
  structure `B` of `Θ` at `x` and a morphism `ψ : F(x) → y`, there is an open `W ∋ x` inside
  `U(x)` on which `g = ψ̂ ∘ F` is an sc-diffeomorphism onto an open set `W'`, and a local branching
  structure of `F_*Θ` at `y` whose domain is `g(W)`, whose sheets are the `g(Mᵢ ∩ W)` and whose
  weights are the `σᵢ` (the same index set up to a bijection).  `ψ̂ = t ∘ (s|U(ψ))⁻¹` is the
  project's `EpGroupoid.hat` (Definition 7.1.4, on the chosen sheet through `ψ`; any sheet gives
  the same germ).  "The same weights" is not said in this item but is how a carried structure is
  read (the proof of 11.3.5 says it explicitly).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_17
open Polyfold

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- The local branching structure `B'` (of some `Θ'` at `y`) is the image of `B` (of `Θ` at `x`)
under `g` on `W`: domain `g(W)`, sheets `g(Mᵢ ∩ W)`, the same weights `σᵢ`. -/
def IsImageStructureB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Θ : Obj → ℚ}
    {Θ' : Obj' → ℚ} {x : Obj} {y : Obj'} (B : X.LocalBranchingStructure Θ x)
    (B' : Y.LocalBranchingStructure Θ' y) (g : Obj → Obj') (W : Set Obj) : Prop :=
  B'.U = g '' W ∧ ∃ e : B.ι ≃ B'.ι, ∀ i, B'.M (e i) = g '' (B.M i ∩ W) ∧ B'.σ (e i) = B.σ i

/-- The proof's step: local branching structures of `Θ` at `x` are carried by `ψ̂ ∘ F` to local
branching structures of `F_*Θ` at `y`, for every `ψ : F(x) → y`. -/
def TransportB (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y) : Prop :=
  ∀ Θ : Obj → ℚ, X.IsBranchedEpSubgroupoid Θ →
    ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (ψ : Mor') (y : Obj'),
      Y.src ψ = F.obj x → Y.tgt ψ = y →
      ∃ W : Set Obj, IsOpen W ∧ x ∈ W ∧ W ⊆ B.U ∧
        (∃ (g' : Obj' → Obj) (W' : Set Obj'), IsOpen W' ∧
          X.PObj.IsScDiffeoOn Y.PObj (Y.hat ψ ∘ F.obj) g' W W') ∧
        ∃ B' : Y.LocalBranchingStructure (F.pushforwardTheta Θ) y,
          IsImageStructureB B B' (Y.hat ψ ∘ F.obj) W

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

/-- Theorem 11.3.3 for an equivalence `F`: local branching structures are carried by `ψ̂ ∘ F`,
and `F_*`, `F^*` have the properties (1)–(6). -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    F.IsEquivalence →
      TransportB X Y F ∧ Thm1133B X Y F.pushforwardTheta F.pullbackTheta

end RoundTrip.V11_17
