import Polyfold
/-! Blind formalization of V9_39 (the 2021 book's Part II, §9.4, Definition 9.4.1, p. 429;
2017: Definition 9.12, p. 315): the relative tangent space `T^K_zM` and essential points.

Text: for `K ⊆ M`, `M` a smooth manifold with boundary and corners, `T^K_zM` is the linear hull
of the unit vectors `e = lim φ(z_k)/|φ(z_k)|`, `z_k → z` in `K ∖ {z}`, in a chart `φ` centred at
`z`, independent of the chart; `z ∈ K` is essential if it is a limit of `z_k ∈ K` with
`T^K_{z_k}M = T_{z_k}M`.

Choices:
- This item is a definition with one embedded claim ("independent of the chart").  B is the
  conjunction of (a) the project's `relTangent` is my `relTangentB`, (b) chart independence,
  (c) the project's `essentialSet` is my `essentialB`.
- Setting: `M : Type` (universe 0), a smooth (`C^∞`) manifold with boundary and corners of
  dimension `n` in Mathlib's sense: `ChartedSpace (EuclideanQuadrant n) M` with
  `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M`.  The text's charts into
  `[0,∞)^k × ℝ^{n-k}` reduce to charts into the quadrant `[0,∞)ⁿ` (`ℝ ≅ (0,∞)`), so this is
  the text's notion; I did not use a general `ModelWithCorners`.
- `T_zM` is Mathlib's `TangentSpace`, i.e. `ℝⁿ = EuclideanSpace ℝ (Fin n)` read in the preferred
  chart `extChartAt _ z`; "the subspace `T^K_zM ⊆ T_zM`" is therefore a `Submodule` of `ℝⁿ`, and
  "`T^K_zM = T_zM`" is `= ⊤`.
- "a chart centred at `z`": instead of centring I subtract `φ(z)` (`(φ(z_k) − φ(z))/|…|`), which
  is the same for a translated chart.  The sequence lies in `K ∖ {z}` and converges to `z` in `M`;
  the chart map is Mathlib's total `e.extend I` (junk off `e.source`, irrelevant for limits).
- (b) "independent of the chart": for every chart `e` of the maximal smooth atlas with
  `z ∈ e.source`, the hull computed in `e`, carried to `T_zM` by the derivative (within the
  quadrant `range I`) of the transition map `extChartAt z ∘ (e.extend I)⁻¹` at `e.extend I z`, is
  the hull computed in the preferred chart.
- (a) compares with the project's `relTangent` (read with `#print`: the span of Mathlib's tangent
  cone of the chart image; equal to my span of unit vectors since the nonzero tangent-cone vectors
  are the positive multiples of the unit limit directions).
- "`K^{ne} = K ∖ K^e`" is a notation; not formalized.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_39
open Polyfold
open scoped Manifold ContDiff Topology
noncomputable section

/-- The model with corners `[0, ∞)ⁿ ⊆ ℝⁿ`. -/
abbrev Q (n : ℕ) := modelWithCornersEuclideanQuadrant n

/-- The unit vectors `e = lim (φ(z_k) − φ(z))/|φ(z_k) − φ(z)|` for sequences `z_k ∈ K ∖ {z}`,
`z_k → z`, read through a coordinate map `φ : M → ℝⁿ`. -/
def unitVecsB {n : ℕ} {M : Type} [TopologicalSpace M] (φ : M → EuclideanSpace ℝ (Fin n))
    (K : Set M) (z : M) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | ∃ u : ℕ → M, (∀ k, u k ∈ K ∧ u k ≠ z) ∧ Filter.Tendsto u Filter.atTop (𝓝 z) ∧
    Filter.Tendsto (fun k => ‖φ (u k) - φ z‖⁻¹ • (φ (u k) - φ z)) Filter.atTop (𝓝 v)}

/-- The linear hull of the unit vectors, computed in the coordinates `φ`. -/
def relTangentInB {n : ℕ} {M : Type} [TopologicalSpace M] (φ : M → EuclideanSpace ℝ (Fin n))
    (K : Set M) (z : M) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (unitVecsB φ K z)

/-- **Definition 9.4.1 (1)**: `T^K_zM ⊆ T_zM = ℝⁿ`, computed in the preferred chart at `z`. -/
def relTangentB {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    (K : Set M) (z : M) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  relTangentInB (extChartAt (Q n) z) K z

/-- **Definition 9.4.1 (2)**: the essential points of `K`: limits of sequences `z_k ∈ K` with
`T^K_{z_k}M = T_{z_k}M`. -/
def essentialB {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    (K : Set M) : Set M :=
  {z | z ∈ K ∧ ∃ u : ℕ → M, (∀ k, u k ∈ K ∧ relTangentB (n := n) K (u k) = ⊤) ∧
    Filter.Tendsto u Filter.atTop (𝓝 z)}

/-- Definition 9.4.1: the project's `T^K_zM` and `K^e` are the text's, and `T^K_zM` does not
depend on the chart. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    [IsManifold (Q n) ∞ M] (K : Set M),
    -- (a) the project's relative tangent space is the text's
    (∀ z : M, relTangent (Q n) K z = relTangentB K z) ∧
    -- (b) independent of the chart
    (∀ z : M, ∀ e ∈ IsManifold.maximalAtlas (Q n) ∞ M, z ∈ e.source →
      Submodule.map
          (fderivWithin ℝ (extChartAt (Q n) z ∘ (e.extend (Q n)).symm) (Set.range (Q n))
            (e.extend (Q n) z)).toLinearMap
          (relTangentInB (e.extend (Q n)) K z) = relTangentB K z) ∧
    -- (c) the project's essential points are the text's
    essentialSet (Q n) K = essentialB (n := n) K

end
end RoundTrip.V9_39
