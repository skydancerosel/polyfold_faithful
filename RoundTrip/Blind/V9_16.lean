import Polyfold
/-! Blind formalization of V9_16 (the text's Part II, §9.2, Lemma 9.2.3, p. 410 of the Springer
2021 book; 2017: Lemma 9.3, p. 299): for two local branching structures of an equidimensional
`Θ` on `U(x)`, a point that is good for one of them is good for the other.

Choices:
- Setting: as in `RoundTrip/Blind/V9_15.lean`: an ep-groupoid `X : EpGroupoid Obj Mor`,
  `Obj Mor : Type` (universe 0), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n` (project's
  "`n`-dimensional": some `n`-dimensional structure at every point of `supp Θ`).
- "two local branching structures ... on `U(x)`": two structures `B₁ B₂` of `Θ` at the same point
  `x` (project's `LocalBranchingStructure Θ x`) with the same domain, `B₁.U = B₂.U`.  They are
  not required to be `n`-dimensional (the text only says `Θ` is equidimensional).
- "good": my `IsGoodAt` (Definition 9.2.2, as in `RoundTrip/Blind/V9_15.lean`): `y ∈ ⋃ᵢ Mᵢ` and
  some open `V ∋ y`, `V ⊆ U(x)`, has `Mᵢ ∩ V = Mⱼ ∩ V` whenever `y ∈ Mᵢ ∩ Mⱼ`.
- The claim is one direction for an arbitrary ordered pair, hence both directions.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_16
open Polyfold

/-- The text's good point `y` of the local branching structure `B` (Definition 9.2.2). -/
def IsGoodAt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- **Lemma 9.2.3**: a point good for one local branching structure of an equidimensional `Θ` on
`U(x)` is good for every other one on the same `U(x)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
    ∀ (x : Obj) (B₁ B₂ : X.LocalBranchingStructure Θ x), B₁.U = B₂.U →
      ∀ y : Obj, IsGoodAt B₁ y → IsGoodAt B₂ y

end RoundTrip.V9_16
