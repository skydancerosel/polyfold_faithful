import Polyfold
/-! Blind formalization of V9_40 (the 2021 book's Part II, §9.4, Lemma 9.4.2, p. 430;
2017: Lemma 9.11, p. 315): the essential set is closed.

Text: `K^e` is closed in `K`, so `K ∖ K^e` is open in `K`.

Choices:
- Setting as in my V9_39: `M : Type`, an `n`-dimensional smooth manifold with boundary and corners
  (`ChartedSpace (EuclideanQuadrant n) M`, `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M`),
  `K ⊆ M` arbitrary (Definition 9.4.1 is for arbitrary subsets).
- `K^e`: the project's `essentialSet` (read with `#print`; my V9_39 states that it is the text's
  Definition 9.4.1 (2)).  "Closed in `K`" / "open in `K`": closed / open in the subspace `K`, i.e.
  the preimages under the inclusion `K → M`.
- Both claims are stated, although the second follows from the first.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_40
open Polyfold
open scoped Manifold ContDiff

/-- The model with corners `[0, ∞)ⁿ ⊆ ℝⁿ`. -/
abbrev Q (n : ℕ) := modelWithCornersEuclideanQuadrant n

/-- Lemma 9.4.2: `K^e` is closed and `K^{ne} = K ∖ K^e` is open in the subspace `K`. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    [IsManifold (Q n) ∞ M] (K : Set M),
    IsClosed (((↑) : K → M) ⁻¹' essentialSet (Q n) K) ∧
      IsOpen (((↑) : K → M) ⁻¹' (K \ essentialSet (Q n) K))

end RoundTrip.V9_40
