import Polyfold
/-! Blind formalization of V9_20 (the text's Part II, §9.2, Lemma 9.2.7 (1), p. 412 of the
Springer 2021 book; 2017: Lemma 9.5 (1), p. 300): for an equidimensional `Θ`, `S^g_Θ` is open
and dense in `supp(Θ)` and `S^b_Θ` is closed and nowhere dense in `supp(Θ)`.

Choices:
- Setting: as in `RoundTrip/Blind/V9_15.lean`: ep-groupoid `X : EpGroupoid Obj Mor`,
  `Obj Mor : Type` (universe 0), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n`.
- `S^g_Θ`, `S^b_Θ` (Definition 9.2.6, as in `RoundTrip/Blind/V9_19.lean`): the points of
  `supp Θ` that are, resp. are not, good (my `IsGoodAt`, Definition 9.2.2) for some local
  branching structure of `Θ` whose domain contains them.  I use my own `Sg`, `Sb` rather than
  the project's `goodSet`, `badSet` (V9_19 says they agree).
- "open / dense / closed / nowhere dense in `supp(Θ)`": in the subspace topology of
  `supp Θ ⊆ X` (the object space), i.e. for the preimages in the subtype `↥(supp Θ)`; nowhere
  dense is Mathlib's `IsNowhereDense` (closure has empty interior).
- "the text derives the density from (2)": the proof route, not part of the claim.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_20
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

/-- `S^g_Θ`, as a subset of the subspace `supp Θ`. -/
def Sg {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) : Set (EpGroupoid.supp Θ) :=
  {y | IsGoodPt X Θ y}

/-- `S^b_Θ`, as a subset of the subspace `supp Θ`. -/
def Sb {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) : Set (EpGroupoid.supp Θ) :=
  {y | ¬ IsGoodPt X Θ y}

/-- **Lemma 9.2.7 (1)**: in `supp Θ`, the good set is open and dense and the bad set is closed and
nowhere dense. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
      IsOpen (Sg X Θ) ∧ Dense (Sg X Θ) ∧ IsClosed (Sb X Θ) ∧ IsNowhereDense (Sb X Θ)

end RoundTrip.V9_20
