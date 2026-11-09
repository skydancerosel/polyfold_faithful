import Polyfold
/-! Blind formalization of V9_43 (the 2021 book's Part II, §9.4, Definition 9.4.5, p. 431;
2017: Definition 9.13, p. 317): sets of measure zero.

Text: `K ⊆ M_i` has measure zero if for every smooth chart `φ` of `M_i` the set `φ(U ∩ K)` has
Lebesgue measure zero.

Choices:
- This item is a definition.  B says that the project's `IsMeasureZero` is the text's notion.
- Setting: the definition only uses the structure of `M_i` as a smooth manifold with boundary and
  corners, so I state it for such a manifold `M : Type` of dimension `n`, in Mathlib's sense as in
  my V9_39 (`ChartedSpace (EuclideanQuadrant n) M`,
  `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M`).  How the sheets `M_i` of a local
  branching structure carry this structure is not part of this item.
- "every smooth chart `φ : U → …`": every chart `e` of Mathlib's maximal `C^∞` atlas, `U` its
  source, `φ = e.extend I : U → ℝⁿ` (the chart read in `ℝⁿ`).  The text's charts into
  `[0,∞)^k × ℝ^{n-k}` differ from quadrant charts by diffeomorphisms, which preserve Lebesgue
  null sets, so nothing is lost.
- "Lebesgue measure": `volume` on `EuclideanSpace ℝ (Fin n)` (Mathlib's
  `measureSpaceOfInnerProductSpace`, the Lebesgue measure for the Euclidean structure).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_43
open Polyfold
open scoped Manifold ContDiff

/-- The model with corners `[0, ∞)ⁿ ⊆ ℝⁿ`. -/
abbrev Q (n : ℕ) := modelWithCornersEuclideanQuadrant n

/-- **Definition 9.4.5**: `K ⊆ M` has measure zero if `φ(U ∩ K)` is Lebesgue-null for every smooth
chart `φ : U → ℝⁿ`. -/
def IsMeasureZeroB {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    (K : Set M) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas (Q n) ∞ M,
    MeasureTheory.volume ((e.extend (Q n)) '' (e.source ∩ K)) = 0

/-- Definition 9.4.5: the project's sets of measure zero are the text's. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    [IsManifold (Q n) ∞ M] (K : Set M),
    IsMeasureZero (Q n) K ↔ IsMeasureZeroB (n := n) K

end RoundTrip.V9_43
