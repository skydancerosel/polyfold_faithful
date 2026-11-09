import Polyfold
/-! Blind formalization of V9_17 (the text's Part II, §9.2, Remark 9.2.4 (a), (b), p. 411 of the
Springer 2021 book; 2017: Remark 9.4, p. 300), for an equidimensional `Θ`:
(a) being a good point is intrinsic; (b) near a good point `y`, `Θ` is represented by one
submanifold with weight `Θ(y)`.

Choices:
- Setting: as in `RoundTrip/Blind/V9_15.lean`: an ep-groupoid `X : EpGroupoid Obj Mor`,
  `Obj Mor : Type` (universe 0), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n` (project's
  "`n`-dimensional"), the standing hypothesis of §9.2 for Definition 9.2.2 – Lemma 9.2.7.
- "good": my `IsGoodAt` (Definition 9.2.2, as in `RoundTrip/Blind/V9_15.lean`).
- (a) "intrinsic": whether `y` is good does not depend on the local branching structure used:
  for any two structures `B₁` at `x₁` and `B₂` at `x₂` (arbitrary centres and domains, not
  required to be `n`-dimensional) whose domains both contain `y`, `y` is good for `B₁` iff good
  for `B₂`.  This is stronger than Lemma 9.2.3 (same `U(x)`); I read "intrinsic" as this
  independence of all choices.
- (b) "represented by one submanifold with weight `Θ(y)`": there is a local branching structure
  of `Θ` at `y` (project's `LocalBranchingStructure Θ y`: open `U' ∋ y`, submanifolds through `y`
  closed in `U'`, `Θ = ∑ σᵢ 1_{Mᵢ}` on `U'`) with exactly one submanifold, of weight `Θ(y)`.
  "a good point `y`": good for some local branching structure `B` (at some `x`) of `Θ`.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_17
open Polyfold

/-- The text's good point `y` of the local branching structure `B` (Definition 9.2.2). -/
def IsGoodAt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- **Remark 9.2.4 (a), (b)**: goodness does not depend on the structure, and near a good point
`y` the functor `Θ` is `Θ(y)` times the indicator of a single submanifold. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
      -- (a)
      (∀ (x₁ x₂ : Obj) (B₁ : X.LocalBranchingStructure Θ x₁)
          (B₂ : X.LocalBranchingStructure Θ x₂) (y : Obj),
          y ∈ B₁.U → y ∈ B₂.U → (IsGoodAt B₁ y ↔ IsGoodAt B₂ y)) ∧
      -- (b)
      (∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (y : Obj), IsGoodAt B y →
        ∃ B' : X.LocalBranchingStructure Θ y, Fintype.card B'.ι = 1 ∧ ∀ i, B'.σ i = Θ y)

end RoundTrip.V9_17
