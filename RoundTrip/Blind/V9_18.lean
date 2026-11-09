import Polyfold
/-! Blind formalization of V9_18 (the text's Part II, §9.2, Lemma 9.2.5, p. 411 of the Springer
2021 book; 2017: Lemma 9.4, p. 300): for an equidimensional `Θ` and a morphism `φ`, `s(φ)` is a
good point iff `t(φ)` is a good point.

Choices:
- Setting: as in `RoundTrip/Blind/V9_15.lean`: an ep-groupoid `X : EpGroupoid Obj Mor`,
  `Obj Mor : Type` (universe 0), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n`.
  `s, t` are the project's `X.src`, `X.tgt`; `φ` ranges over all morphisms.
- "good" for a point (no structure named): after Lemma 9.2.3 / Remark 9.2.4 (a) goodness is
  intrinsic; I read "`y` is good" as `IsGoodPt`: `y` is good (my `IsGoodAt`, Definition 9.2.2 as
  in `RoundTrip/Blind/V9_15.lean`) for SOME local branching structure of `Θ`, at some point,
  whose domain contains `y`.  (By Remark 9.2.4 (a) this is the same as "for every such
  structure".)  A point off `supp Θ` is never good (it lies in no `Mᵢ`).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_18
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

/-- **Lemma 9.2.5**: `s(φ)` is good iff `t(φ)` is good, for every morphism `φ`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
    ∀ φ : Mor, IsGoodPt X Θ (X.src φ) ↔ IsGoodPt X Θ (X.tgt φ)

end RoundTrip.V9_18
