import Polyfold
/-! Blind formalization of V9_19 (the text's Part II, §9.2, Definition 9.2.6, p. 411 of the
Springer 2021 book; 2017: Definition 9.5, p. 300): `S^g_Θ` is the set of good points of
`supp(Θ)`, `S^b_Θ` the set of bad points; by Remark 9.2.4 (c) being good is a property of `|x|`.

Choices:
- This item is a definition plus the remark that justifies reading it on `|X|`.  B is the
  conjunction of: (1) the project's `goodSet X Θ` is `{y ∈ supp Θ | y good}`; (2) the project's
  `badSet X Θ` is `{y ∈ supp Θ | y not good}`; (3) "being good is a property of `|x|`": for every
  morphism `φ`, `s(φ) ∈ S^g_Θ ↔ t(φ) ∈ S^g_Θ`, and likewise for `S^b_Θ` (both sets are
  saturated, so they are the preimages of subsets of `|supp Θ|`).
- Setting: as in `RoundTrip/Blind/V9_15.lean`: ep-groupoid `X : EpGroupoid Obj Mor`,
  `Obj Mor : Type` (universe 0), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n`.
- "good point of `supp(Θ)`": `y ∈ supp Θ` that is good (my `IsGoodAt`, Definition 9.2.2) for
  SOME local branching structure of `Θ` (at some point) whose domain contains `y`; by Remark
  9.2.4 (a) this is the same as for every such structure.  A bad point of `supp Θ` is a point of
  `supp Θ` that is not good (every `y ∈ supp Θ` lies in `M_U` of a structure at `y`).
- Project definitions characterized: `goodSet`, `badSet`; used: `supp`,
  `LocalBranchingStructure`.  Nothing looks false to me.
-/
namespace RoundTrip.V9_19
open Polyfold

/-- The text's good point `y` of the local branching structure `B` (Definition 9.2.2). -/
def IsGoodAt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- `y` is a good point of `Θ`: good for some local branching structure whose domain contains
`y`. -/
def IsGoodPt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (y : Obj) : Prop :=
  ∃ (x : Obj) (B : X.LocalBranchingStructure Θ x), y ∈ B.U ∧ IsGoodAt B y

/-- **Definition 9.2.6**: `S^g_Θ` and `S^b_Θ` are the good and the bad points of `supp Θ`, and
both are unions of isomorphism classes. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
      X.goodSet Θ = {y | y ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ y} ∧
      X.badSet Θ = {y | y ∈ EpGroupoid.supp Θ ∧ ¬ IsGoodPt X Θ y} ∧
      (∀ φ : Mor, X.src φ ∈ X.goodSet Θ ↔ X.tgt φ ∈ X.goodSet Θ) ∧
      (∀ φ : Mor, X.src φ ∈ X.badSet Θ ↔ X.tgt φ ∈ X.badSet Θ)

end RoundTrip.V9_19
