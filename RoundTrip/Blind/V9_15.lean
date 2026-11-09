import Polyfold
/-! Blind formalization of V9_15 (the text's Part II, §9.2, Definition 9.2.2, p. 410 of the
Springer 2021 book; 2017: Definition 9.4, p. 299): for an equidimensional `Θ` and a local
branching structure `(Mᵢ)_{i ∈ I}`, `(σᵢ)` on `U(x)`, `M_U = ⋃ᵢ Mᵢ`; a point `y ∈ M_U` is
**good** if there is an open `V(y) ⊆ U(x)` (a neighbourhood of `y`) with
`Mᵢ ∩ V(y) = Mⱼ ∩ V(y)` for all `i, j` with `y ∈ Mᵢ ∩ Mⱼ`; otherwise `y` is **bad**.

Choices:
- This item is a definition.  B says that the project's `LocalBranchingStructure.MU` is
  `⋃ᵢ Mᵢ` and that the project's `LocalBranchingStructure.IsGoodPoint` is my `IsGoodAt` (the
  text's definition, written from Mathlib-level data), and that "bad" (for `y ∈ M_U`) is the
  negation of my `IsGoodAt`, which is trivially the negation of `IsGoodPoint`.
- Setting: an ep-groupoid `X : EpGroupoid Obj Mor`, `Obj Mor : Type` (universe 0, as in the
  Chapter 7 blind files), a branched ep⁺-subgroupoid `Θ` (project's `IsBranchedEpSubgroupoid`)
  that is equidimensional, read as `∃ n, X.IsNDimensional Θ n` (the project's "`Θ` is
  `n`-dimensional": at every point of `supp Θ` some local branching structure has all `Mᵢ`
  `n`-dimensional; `#print`ed).  The given structure is any local branching structure at `x`
  (the text: "a structure on `U(x)`"), not required to be `n`-dimensional.  The definition does
  not use the equidimensionality; I keep it as the text's standing hypothesis.
- `V(y)`: read as an open set containing `y` (the notation `V(y)` of the text is a
  neighbourhood of `y`), contained in `U(x)`.
- "for all `i, j` with `y ∈ Mᵢ ∩ Mⱼ`": `i, j` range over the whole index set `I`.
- Project definition used: `LocalBranchingStructure` (fields `U`, `ι`, `M`, `σ`, read with
  `#print`).  Nothing looks false to me.
-/
namespace RoundTrip.V9_15
open Polyfold

/-- The text's good point `y` of the local branching structure `B` on `U(x)`: `y ∈ ⋃ᵢ Mᵢ` and
some open `V ∋ y`, `V ⊆ U(x)`, has `Mᵢ ∩ V = Mⱼ ∩ V` whenever `y ∈ Mᵢ ∩ Mⱼ`. -/
def IsGoodAt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- **Definition 9.2.2**: `M_U = ⋃ᵢ Mᵢ`, the project's good points are the text's good points,
and the bad points of `M_U` are the points of `M_U` that are not good. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
    ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x),
      B.MU = ⋃ i, B.M i ∧
      (∀ y : Obj, B.IsGoodPoint y ↔ IsGoodAt B y) ∧
      (∀ y ∈ B.MU, ¬ B.IsGoodPoint y ↔ (y ∈ ⋃ i, B.M i ∧ ¬ IsGoodAt B y))

end RoundTrip.V9_15
