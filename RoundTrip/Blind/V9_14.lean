import Polyfold
/-! Blind formalization of V9_14 (the text's Part II, §9.2, Theorem 9.2.1 (1), p. 409 of the
Springer 2021 book; 2017: Theorem 9.1, p. 298): the formal sum `∑_{i ∈ I} σᵢ · T_xMᵢ ∈ Gr(x)` does
not depend on the local branching structure `(Mᵢ)_{i ∈ I}`, `(σᵢ)_{i ∈ I}` of `Θ` at `x`.

Choices:
- Setting: an ep-groupoid `X : EpGroupoid Obj Mor` with `Obj Mor : Type` (universe 0, as in the
  Chapter 7 blind files, e.g. `RoundTrip/Blind/V7_10.lean`), Hausdorff and paracompact, and a
  branched ep⁺-subgroupoid `Θ : Obj → ℚ` (the project's `IsBranchedEpSubgroupoid`, Definition
  9.1.2: functor to `ℚ⁺`, `supp Θ ⊆ X_∞`, `|supp Θ|` paracompact, local branching structures at
  every point of the support; fields read with `#print`).  No dimension hypothesis: the theorem is
  for every branched ep⁺-subgroupoid (the equidimensional case is only a step of the proof).
- "local branching structure at `x`": the project's `LocalBranchingStructure Θ x` (fields read
  with `#print`: open `U ∋ x`, finite index type `ι`, smooth finite-dimensional submanifolds
  `Mᵢ ⊆ U` through `x` with proper inclusions `Mᵢ → U`, weights `σᵢ > 0`,
  `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ` on `U`).  This is Definition 9.1.2 (2)–(4).
- `T_xMᵢ`: the project's `MPolyfold.submanifoldTangent (Mᵢ) x`, a subset of Part I's tangent
  bundle `TX` (the image of `Ts(x)` for the sc⁺-retraction `s` of the submanifold, Remark 4.14).
- `Gr(x)` and the formal sum: a formal sum `∑ σ_L · L` is a finitely supported function from
  subsets `L ⊆ TX` to `ℚ`; `∑ σᵢ · T_xMᵢ` is `∑ᵢ single (T_xMᵢ) σᵢ` (`sumB`), so that equal
  tangent spaces add their weights, as in the free abelian monoid of the text.  (This is the same
  expression as the project's `LocalBranchingStructure.tangentSum`, written out.)  The claim
  "`∈ Gr(x)`" and part (2) (functoriality of `TΘ`) are not part of this item.
- Range of `x`: `x ∈ supp Θ` (for `x ∉ supp Θ` every structure at `x` has no submanifolds, so
  the claim is trivial there).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_14
open Polyfold

/-- The formal sum `∑_{i ∈ I} σᵢ · T_xMᵢ` of a local branching structure at `x`. -/
noncomputable def sumB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) :
    Set X.PObj.TangentSpace →₀ ℚ :=
  ∑ i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) x) (B.σ i)

/-- **Theorem 9.2.1 (1)**: for a branched ep⁺-subgroupoid `Θ` and `x ∈ supp Θ`, the formal sum
`∑ σᵢ · T_xMᵢ` is the same for any two local branching structures of `Θ` at `x`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ x ∈ EpGroupoid.supp Θ, ∀ (B₁ B₂ : X.LocalBranchingStructure Θ x), sumB B₁ = sumB B₂

end RoundTrip.V9_14
