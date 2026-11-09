import Polyfold
/-! Blind formalization of V9_28 (the text's Part II, §9.2, Remark 9.2.17, p. 421 of the Springer
2021 book; 2017: Remark 9.6, p. 310).

Text: `∂Θ` is in general not the restriction of `Θ` to `∂X`; in Section 9.5, Definition 9.3.6, a
tame notion is introduced.

Choices:
- Setting and notions as in my `RoundTrip/Blind/V9_26.lean`: `Obj Mor : Type`, the project's
  `X : EpGroupoid Obj Mor`, `X.IsBranchedEpSubgroupoid Θ`, `X.LocalBranchingStructure Θ x`,
  `∂X = X.PObj.boundary`, `∂Mᵢ = X.PObj.submanifoldBoundary (Mᵢ)` (`#print`ed),
  `bsumB B y = ∑_{i : y ∈ ∂Mᵢ} σᵢ`.
- "`∂Θ` is in general not the restriction of `Θ` to `∂X`": there are an ep-groupoid and a
  branched ep⁺-subgroupoid `Θ` and a point `y ∈ ∂X` where `∂Θ(y) ≠ Θ(y)`.  I write `∂Θ(y)` by its
  defining local formula (Proposition 9.2.15 (3) / Definition 9.2.16: `∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ`
  for a local branching structure at a point `x ∈ supp Θ` with `y ∈ U(x)`), not by the project's
  `boundaryTheta`, since Definition 9.2.16 as printed does not pin `∂Θ` down (my V9_27).  The
  example lives in `Type` (universe 0).  (E.g. `X = [0, ∞)`, `Θ = 1_{{0}}`, `M = {0}`,
  `d_M(0) = 0`.)
- The second sentence is a forward reference with no claim; not formalized.  "Section 9.5"
  looks like a misprint for Section 9.3 (Definition 9.3.6 is in §9.3).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_28
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

/-- **Remark 9.2.17**: for some branched ep⁺-subgroupoid `Θ`, `∂Θ` differs from `Θ` at a point
of `∂X`. -/
def B : Prop :=
  ∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj) (_ : ParacompactSpace Obj)
    (_ : TopologicalSpace Mor) (_ : T2Space Mor) (_ : ParacompactSpace Mor)
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ ∧
    ∃ x ∈ EpGroupoid.supp Θ, ∃ (B : X.LocalBranchingStructure Θ x), ∃ y ∈ B.U,
      y ∈ X.PObj.boundary ∧ bsumB B y ≠ Θ y

end RoundTrip.V9_28
