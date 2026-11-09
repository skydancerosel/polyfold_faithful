import Polyfold
/-! Blind formalization of V9_27 (the text's Part II, §9.2, Definition 9.2.16, p. 421 of the
Springer 2021 book; 2017: Definition 9.7, p. 309): the boundary `∂Θ`.

Text: in view of the preceding proposition the boundary `∂Θ` of `Θ` is the functor uniquely
characterized by (1) `supp(∂Θ) ⊆ ∂X` and (2) `∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ` on local branching
structures at points of `supp(∂Θ)`.

Choices:
- Setting and notions as in my `RoundTrip/Blind/V9_26.lean`: `Obj Mor : Type`, the project's
  `X : EpGroupoid Obj Mor`, `X.IsBranchedEpSubgroupoid Θ`, `X.LocalBranchingStructure Θ x`,
  `∂X = X.PObj.boundary`, `∂Mᵢ = X.PObj.submanifoldBoundary (Mᵢ)` (all `#print`ed),
  `bsumB B y = ∑_{i : y ∈ ∂Mᵢ} σᵢ`.
- This item is a definition ("`∂Θ` is the functor uniquely characterized by …").  Its content is
  that exactly one functor has (1) and (2), and the project's `X.boundaryTheta Θ` is meant to be
  it.  B says: the project's `boundaryTheta X Θ` is a functor `X → ℚ⁺` (values `≥ 0`, equal on
  source and target of every morphism) with (1) and (2), and every functor `F : X → ℚ⁺` with (1)
  and (2) equals it.
- (2), literally: for every `x ∈ supp(F)`, every local branching structure of `Θ` at `x` (on
  `U(x)`) and every `y ∈ U(x)`, `F(y) = ∑_{i : y ∈ ∂Mᵢ} σᵢ`.  "Functor" = functor to `ℚ⁺`
  (the codomain of `Θ` and of Proposition 9.2.15 (3)).
- I believe B is FALSE as printed: (2) only speaks about points of `supp(F)`, so `F ≡ 0`
  satisfies (1) and (2) vacuously, while `∂Θ ≠ 0` in general (e.g. `X = [0, ∞)` with identity
  morphisms, `Θ = 1`, one sheet `M = [0, ∞)`, `d_M(0) = 1`: `∂Θ(0) = 1`).  Also at points of
  `cl(supp Θ) \ supp Θ` in `∂X` there are no local branching structures, so (2) cannot fix `F`
  there.  The intended characterization presumably has (2) at the points of `supp Θ` and
  `∂Θ = 0` off `supp Θ` (cf. my V9_26 (3)).  Formalized literally anyway.
-/
namespace RoundTrip.V9_27
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- The boundary weight `∑_{i : y ∈ ∂Mᵢ} σᵢ` of a local branching structure at `y`. -/
noncomputable def bsumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (y : Obj) : ℚ :=
  ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i

/-- `F : X → ℚ⁺` is a functor with the two properties of Definition 9.2.16: (1)
`supp(F) ⊆ ∂X`; (2) `F(y) = ∑_{y ∈ ∂Mᵢ} σᵢ` on every local branching structure of `Θ` at every
point of `supp(F)`. -/
def IsCharacterizedB (X : EpGroupoid Obj Mor) (Θ F : Obj → ℚ) : Prop :=
  (∀ y, 0 ≤ F y) ∧ (∀ φ : Mor, F (X.src φ) = F (X.tgt φ)) ∧
  -- (1)
  EpGroupoid.supp F ⊆ X.PObj.boundary ∧
  -- (2)
  ∀ x ∈ EpGroupoid.supp F, ∀ (B : X.LocalBranchingStructure Θ x), ∀ y ∈ B.U, F y = bsumB B y

end

/-- **Definition 9.2.16**: the project's `∂Θ` is the unique functor `X → ℚ⁺` with
`supp(∂Θ) ⊆ ∂X` and `∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ` on the local branching structures at the points of
`supp(∂Θ)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    IsCharacterizedB X Θ (X.boundaryTheta Θ) ∧
    ∀ F : Obj → ℚ, IsCharacterizedB X Θ F → F = X.boundaryTheta Θ

end RoundTrip.V9_27
