import Polyfold
/-! Blind formalization of V9_26 (the text's Part II, §9.2, Proposition 9.2.15, p. 420 of the
Springer 2021 book; 2017: Proposition 9.4, p. 308): the boundary weights.

Text: for `x ∈ supp(Θ) ∩ ∂X` and two local branching structures: (1) `∑_{y ∈ ∂Mᵢ} σᵢ` does not
depend on the structure; (2) it vanishes where `d_X(y) = 0`; (3) these sums define a functor
`∂Θ ≥ 0` supported in `∂X`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files; the project's `EpGroupoid`
  has `Obj`, `Mor` in one universe), `X : EpGroupoid Obj Mor` (the project's ep-groupoid, as in the
  Chapter 7 blind files), `Θ` a branched ep⁺-subgroupoid: the project's
  `X.IsBranchedEpSubgroupoid Θ` (fields `#print`ed: `Θ ≥ 0`, functorial, `supp Θ ⊆ X_∞`,
  `|supp Θ|` paracompact, a local branching structure at every point of `supp Θ`; see
  `RoundTrip/Blind/V9_1.lean`).  No tameness: §9.2 precedes the tame notion (Remark 9.2.17).
- Local branching structures: the project's `X.LocalBranchingStructure Θ x` (`#print`ed: open
  `U ∋ x`, finite family of smooth submanifolds `Mᵢ ⊆ U` through `x` with proper inclusions,
  weights `σᵢ > 0`, `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ` on `U`).  "Two local branching structures" at `x`:
  two arbitrary ones, on possibly different `U`, `U'`.
- `∂Mᵢ`: the project's `MPolyfold.submanifoldBoundary` (`#print`ed: the `y ∈ Mᵢ` with
  `d_{Mᵢ}(y) ≥ 1`, `d_{Mᵢ}` the degeneracy index of the induced structure, `subDegIndex`).
  `∂X`: the project's `MPolyfold.boundary` (`{d_X ≥ 1}`), `d_X`: `MPolyfold.degIndex`, both of
  the object M-polyfold.  `bsumB B y = ∑_{i : y ∈ ∂Mᵢ} σᵢ`.
- (1) The sum is a function of `y`; I read "does not depend on the structure" as: for two
  structures at `x` the sums agree at every `y` in both neighbourhoods `U ∩ U'` (with one common
  `U` this is the text's statement; on `U ∩ U'` it is the same claim at the points `y`).
- (2) "where `d_X(y) = 0`": at every `y ∈ U(x)` with `d_X(y) = 0`, the sum is `0`.
- (3) "these sums define a functor `∂Θ ≥ 0` supported in `∂X`": there is `F : Obj → ℚ`,
  `F ≥ 0`, functorial (`F(s φ) = F(t φ)` for every morphism, a functor to `ℚ⁺` with identities
  only), `supp F ⊆ ∂X`, equal to the sum on `U(x)` for EVERY local branching structure at every
  `x ∈ supp Θ` (here `x ∉ ∂X` allowed), and `F = 0` where `Θ = 0` (there every such sum is empty;
  "defined by these sums" leaves no other value).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_26
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- The boundary weight `∑_{i : y ∈ ∂Mᵢ} σᵢ` of a local branching structure at `y`. -/
noncomputable def bsumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (y : Obj) : ℚ :=
  ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i

end

/-- **Proposition 9.2.15**: the boundary weights `∑_{y ∈ ∂Mᵢ} σᵢ` do not depend on the local
branching structure, vanish at points with `d_X(y) = 0`, and define a functor `∂Θ ≥ 0`
supported in `∂X`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    -- (1) independence of the structure
    (∀ x ∈ EpGroupoid.supp Θ, x ∈ X.PObj.boundary →
      ∀ (B B' : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U ∩ B'.U, bsumB B y = bsumB B' y) ∧
    -- (2) vanishing where `d_X(y) = 0`
    (∀ x ∈ EpGroupoid.supp Θ, x ∈ X.PObj.boundary →
      ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U, X.PObj.degIndex y = 0 → bsumB B y = 0) ∧
    -- (3) the functor `∂Θ`
    (∃ F : Obj → ℚ, (∀ y, 0 ≤ F y) ∧ (∀ φ : Mor, F (X.src φ) = F (X.tgt φ)) ∧
      EpGroupoid.supp F ⊆ X.PObj.boundary ∧
      (∀ x ∈ EpGroupoid.supp Θ, ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U,
        F y = bsumB B y) ∧
      (∀ y, Θ y = 0 → F y = 0))

end RoundTrip.V9_26
