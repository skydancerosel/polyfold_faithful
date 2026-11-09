import Polyfold
/-! Blind formalization of V9_38 (the 2021 book's Part II, §9.3, Definition 9.3.10, p. 428;
2017: Definition 9.11, p. 314): the oriented boundary `T̂_{∂Θ}`.

Text: for an oriented tame `Θ`, `T̂_{∂Θ}(y) = 0` off `supp(Θ)` and
`T̂_{∂Θ}(y) = ∑_{y ∈ ∂Mᵢ, d_{Mᵢ}(y) = 1} σᵢ T_y(∂Mᵢ, o_{∂Mᵢ})` on `U(x)` (9.12).

Choices:
- This item is a definition.  B says that the project's `boundaryLift` satisfies the two defining
  clauses (so it is the text's `T̂_{∂Θ}`, and the definition does not depend on the local
  structure used).
- Setting: `Obj Mor : Type` (universe 0) with the instances of the project's `EpGroupoid`,
  `X : EpGroupoid Obj Mor`.  "Oriented tame `Θ`": a branched ep⁺-subgroupoid
  (`IsBranchedEpSubgroupoid`), tame (`IsTameBranched`), with an orientation `T̂Θ = T`
  (`IsOrientation X Θ T`, read with `#print`: a natural section of `Gr̂(X)` over `X_∞` lifting
  `TΘ`, locally of the form (9.9)).  `T̂_{∂Θ}` is a section over `X_∞`, so both clauses are stated
  at smooth points `y ∈ X_∞`.
- "on `U(x)`": for `x ∈ supp(Θ)` and every oriented local branching structure `(Mᵢ, oᵢ)`, `(σᵢ)`
  at `x` (`OrientedBranchingStructure`) with tame sheets (`HasTameInducedStructure`, the structures
  of an oriented tame `Θ`) representing `T̂Θ` on `U(x)` as in (9.9)
  (`T y = orientedSum y` at smooth `y ∈ U(x)`), formula (9.12) at every smooth `y ∈ U(x)`.
- `y ∈ ∂Mᵢ, d_{Mᵢ}(y) = 1`: `y ∈ Mᵢ` with degeneracy index `1` of `y` in `Mᵢ` with its induced
  structure (the project's `subDegIndex`; `y ∈ ∂Mᵢ` is then automatic).
- `T_y(∂Mᵢ, o_{∂Mᵢ})`: the boundary orientation of Definition 9.3.8, which depends on `(Mᵢ, oᵢ)`
  only through the oriented tangent space `T_y(Mᵢ, oᵢ)` (its subspace `T_y∂Mᵢ` and the outward
  direction are determined by `T_yMᵢ`).  `TX` carries no linear structure in the project, so I
  write this operation as a map `bd : T_y(M, o) ↦ T_y(∂M, o_{∂M})` on oriented tangent spaces,
  as the project's `boundaryLift` takes it; B quantifies over every `bd` (the identity (9.12) does
  not depend on which operation is used), which is stronger than the text needs.
- "`= 0` off `supp(Θ)`" is quoted as such (off `supp(∂Θ)` would be equivalent, since (9.12) is an
  empty sum at points of `supp(Θ) ∖ supp(∂Θ)`).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_38
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- The right-hand side of **(9.12)**: `∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) = 1} σᵢ · T_y(∂Mᵢ, o_{∂Mᵢ})`, with
`T_y(∂Mᵢ, o_{∂Mᵢ}) = bd (T_y(Mᵢ, oᵢ))`. -/
noncomputable def boundarySumB (X : EpGroupoid Obj Mor) {Θ : Obj → ℚ} {x : Obj}
    (bd : X.PObj.OrTangent → X.PObj.OrTangent) (B : X.OrientedBranchingStructure Θ x)
    (y : Obj) : X.PObj.OrTangent →₀ ℚ :=
  ∑ i with (∃ (h : X.PObj.IsSubMPolyfold (B.M i)) (hy : y ∈ B.M i),
      X.PObj.subDegIndex h ⟨y, hy⟩ = 1),
    Finsupp.single (bd ((B.orient i).tangent y)) (B.σ i)

end

/-- Definition 9.3.10: the project's `boundaryLift` vanishes off `supp(Θ)` and is given by (9.12)
on the domain of every tame oriented local branching structure representing `T̂Θ`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ)
    (bd : X.PObj.OrTangent → X.PObj.OrTangent),
    X.IsBranchedEpSubgroupoid Θ → X.IsTameBranched Θ → X.IsOrientation Θ T →
    (∀ y ∈ X.PObj.smoothSet, y ∉ EpGroupoid.supp Θ → X.boundaryLift bd T y = 0) ∧
    ∀ x ∈ EpGroupoid.supp Θ, ∀ B : X.OrientedBranchingStructure Θ x,
      (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) →
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → X.boundaryLift bd T y = boundarySumB X bd B y

end RoundTrip.V9_38
