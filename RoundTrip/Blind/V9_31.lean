import Polyfold
/-! Blind formalization of V9_31 (the text's Part II, §9.3, Remark 9.3.3, p. 423 of the Springer
2021 book; 2017: Remark 9.8, p. 311): orientations are not unique.

Text: the local oriented representation (9.9) is not unique, and an orientation of `Θ` is not
unique.

Choices:
- Notions as in my `RoundTrip/Blind/V9_30.lean` (copied): `IsOrientationB` (Definition 9.3.2)
  and `orSumB` (the right side of (9.9)); the project's `IsBranchedEpSubgroupoid`,
  `LocalBranchingStructure`, `SubmanifoldOrientation`.  Examples live in `Type` (universe 0).
- "not unique" is read as "not unique in general": existence of examples (not "never unique").
- (a) "the local oriented representation (9.9) is not unique": there are an orientation `T̂` of a
  branched ep⁺-subgroupoid `Θ`, a point `x ∈ supp Θ` and two oriented local branching structures
  at `x` on the same `U(x)`, both representing `T̂` by (9.9) on `U(x)`, whose families of sheets
  are different as sets of subsets, `{Mᵢ} ≠ {M'ⱼ}` (a genuine difference, not a relabelling or a
  splitting of a sheet into copies with smaller weights).  E.g. Example 9.3.5 with all four
  graphs oriented by `(1, β'(s))`.
- (b) "an orientation of `Θ` is not unique": some `Θ` has two orientations that differ at a
  smooth object (orientations are only defined on `X^∞`).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_31
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- `∑_{i : y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)` (as in `RoundTrip/Blind/V9_30.lean`). -/
noncomputable def orSumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) :
    X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ B.M i, Finsupp.single ((o i).tangent y) (B.σ i)

/-- **Definition 9.3.2** (as in `RoundTrip/Blind/V9_30.lean`): `T` is an orientation of `Θ`. -/
structure IsOrientationB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ)
    (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop where
  mem : ∀ x ∈ X.PObj.smoothSet,
    (∀ g, 0 ≤ T x g) ∧ ∀ g ∈ (T x).support, X.PObj.IsOrientedAt x g
  functor : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
    Finsupp.mapDomain (MPolyfold.OrTangent.push (X.tangentMor φ)) (T (X.src φ)) = T (X.tgt φ)
  lifts : ∀ x ∈ X.PObj.smoothSet,
    Finsupp.mapDomain MPolyfold.OrTangent.carrier (T x) = X.tangentValue Θ x
  locRep : ∀ x ∈ EpGroupoid.supp Θ, ∃ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)),
    ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = orSumB B n o y

end

/-- **Remark 9.3.3**: (a) an oriented local representation (9.9) is not unique; (b) an
orientation of `Θ` is not unique. -/
def B : Prop :=
  -- (a)
  (∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj) (_ : ParacompactSpace Obj)
    (_ : TopologicalSpace Mor) (_ : T2Space Mor) (_ : ParacompactSpace Mor)
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ),
    X.IsBranchedEpSubgroupoid Θ ∧ IsOrientationB X Θ T ∧
    ∃ x ∈ EpGroupoid.supp Θ,
      ∃ (B₁ : X.LocalBranchingStructure Θ x) (n₁ : B₁.ι → ℕ)
        (o₁ : ∀ i, X.PObj.SubmanifoldOrientation (B₁.M i) (n₁ i))
        (B₂ : X.LocalBranchingStructure Θ x) (n₂ : B₂.ι → ℕ)
        (o₂ : ∀ i, X.PObj.SubmanifoldOrientation (B₂.M i) (n₂ i)),
        B₁.U = B₂.U ∧
        (∀ y ∈ B₁.U, y ∈ X.PObj.smoothSet → T y = orSumB B₁ n₁ o₁ y) ∧
        (∀ y ∈ B₂.U, y ∈ X.PObj.smoothSet → T y = orSumB B₂ n₂ o₂ y) ∧
        Set.range B₁.M ≠ Set.range B₂.M) ∧
  -- (b)
  (∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj) (_ : ParacompactSpace Obj)
    (_ : TopologicalSpace Mor) (_ : T2Space Mor) (_ : ParacompactSpace Mor)
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ),
    X.IsBranchedEpSubgroupoid Θ ∧ IsOrientationB X Θ T₁ ∧ IsOrientationB X Θ T₂ ∧
    ∃ y ∈ X.PObj.smoothSet, T₁ y ≠ T₂ y)

end RoundTrip.V9_31
