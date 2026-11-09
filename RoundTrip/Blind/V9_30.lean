import Polyfold
/-! Blind formalization of V9_30 (the text's Part II, §9.3, Definition 9.3.2, p. 423 of the
Springer 2021 book; 2017: Definition 9.8, p. 311): orientations of `Θ`.

Text: an orientation of `Θ` is a section functor `T̂_Θ : X^∞ → Gr̂(X)` lifting `T_Θ` such that
near every `x ∈ supp(Θ)` there is an oriented local branching structure `(Mᵢ, oᵢ)`, `(σᵢ)` with
`T̂_Θ(y) = ∑_{y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)` (9.9).

Choices:
- This item is a definition.  B says: for every branched ep⁺-subgroupoid `Θ` (the project's
  `IsBranchedEpSubgroupoid`, see `RoundTrip/Blind/V9_1.lean`) and every assignment
  `T : Obj → (oriented tangent sets →₀ ℚ)`, the project's `X.IsOrientation Θ T` holds iff `T` is
  an orientation in the text's sense, my `IsOrientationB` below.
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.
- A section functor `T̂ : X^∞ → Gr̂(X)` (`π̂ ∘ T̂ = Id`, `T̂(φ) = (T̂(s φ), φ)`) is given by its
  values `T̂(x) ∈ Gr̂(x)` at the smooth objects `x` (values elsewhere are junk and unconstrained);
  it is a functor iff `(T̂(s φ), φ)` is a morphism `T̂(s φ) → T̂(t φ)` of `Gr̂(X)`, i.e.
  `Tφ_*(T̂(s φ)) = T̂(t φ)` for every morphism `φ` with smooth source (then the target is smooth).
  `Gr̂(x)`: finite sums with weights `≥ 0` of `L̂` with `X.PObj.IsOrientedAt x L̂` (see my
  `RoundTrip/Blind/V9_29.lean`); `Tφ_*` pushes carrier and frames forward by the project's
  `X.tangentMor φ` (`#print`ed: `Tt ∘ (Ts)⁻¹` on `T_{s φ}X`), written out with `Finsupp.mapDomain`.
- "lifting `T_Θ`": `f(T̂(x)) = T_Θ(x)` for smooth `x`, `f` the forgetful map `(L, o) ↦ L`
  extended linearly (`Finsupp.mapDomain carrier`), and `T_Θ` the section of Theorem 9.2.1:
  the project's `X.tangentValue Θ x` (`#print`ed: `∑ᵢ σᵢ T_xMᵢ` for a (chosen) local branching
  structure at `x` if there is one, `0` otherwise; by Theorem 9.2.1 this is the text's `T_Θ`).
- "an oriented local branching structure `(Mᵢ, oᵢ)`, `(σᵢ)` near `x`": a local branching
  structure at `x` (project's `LocalBranchingStructure`) with, for every `i`, a dimension `nᵢ` and
  an orientation `oᵢ` of the `nᵢ`-dimensional submanifold `Mᵢ` (the project's
  `SubmanifoldOrientation (Mᵢ) nᵢ`, `#print`ed: positive frames of `T_yMᵢ` for `y ∈ Mᵢ`, each an
  oriented `nᵢ`-dimensional subspace, depending continuously on `y` in a chart).  `T_y(Mᵢ, oᵢ)` is
  `(oᵢ).tangent y` (`#print`ed: `(T_yMᵢ, positive frames at y)`).  (9.9) is required for the
  smooth `y ∈ U(x)` (where `T̂` is defined).  I do not ask the `Mᵢ` to be
  `IsSubmanifoldOfDim (Mᵢ) nᵢ` separately (the project's `OrientedBranchingStructure` does).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_30
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- `∑_{i : y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)` for a local branching structure with orientations `oᵢ` of the
`nᵢ`-dimensional `Mᵢ`. -/
noncomputable def orSumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) :
    X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ B.M i, Finsupp.single ((o i).tangent y) (B.σ i)

/-- **Definition 9.3.2**: `T` is an orientation of `Θ`: a section functor `X^∞ → Gr̂(X)` lifting
`T_Θ`, locally of the form (9.9). -/
structure IsOrientationB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ)
    (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop where
  /-- `T̂(x) ∈ Gr̂(x)` for `x ∈ X^∞`. -/
  mem : ∀ x ∈ X.PObj.smoothSet,
    (∀ g, 0 ≤ T x g) ∧ ∀ g ∈ (T x).support, X.PObj.IsOrientedAt x g
  /-- `T̂(φ) = (T̂(s φ), φ)` is a morphism `T̂(s φ) → T̂(t φ)` of `Gr̂(X)`. -/
  functor : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
    Finsupp.mapDomain (MPolyfold.OrTangent.push (X.tangentMor φ)) (T (X.src φ)) = T (X.tgt φ)
  /-- `f ∘ T̂ = T_Θ`. -/
  lifts : ∀ x ∈ X.PObj.smoothSet,
    Finsupp.mapDomain MPolyfold.OrTangent.carrier (T x) = X.tangentValue Θ x
  /-- (9.9) near every point of `supp Θ`. -/
  locRep : ∀ x ∈ EpGroupoid.supp Θ, ∃ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)),
    ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = orSumB B n o y

end

/-- **Definition 9.3.2**: the project's orientations of `Θ` are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ T : Obj → X.PObj.OrTangent →₀ ℚ, X.IsOrientation Θ T ↔ IsOrientationB X Θ T

end RoundTrip.V9_30
