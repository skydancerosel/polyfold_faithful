import Polyfold
/-! Blind formalization of V4_62 (the text's §4.3, proof of Theorem 4.23, p. 166).

Text: "`T_{z'}(A ∩ F_σ°) = T_{z'}(({λ} × A_λ) ∩ F_σ°) ⊕ ξ_{z'}` ... in view of the assumption (2)
... `T_{z'}({λ} × A_λ)` has a sc-complement in `T^R_{z'}X`."

Choices:
- Setting: the hypotheses of Theorem 4.23, copied from the blind file V4_54: `X : Type`
  (universe 0), Hausdorff, paracompact, `PX` tame (`IsTame`, Definition 2.37); `Z = ℝᵐ × X` with
  the product charts, the project's `(rnPolyfold m).prod PX` (paracompactness of `ℝᵐ × X` is an
  instance hypothesis); `A ⊆ Z` a smooth submanifold with tame induced structure
  (`IsTameSubmanifold`, Definition 4.17, `A` paracompact) with compact closure; `ε > 0`;
  (1) `p⁻¹(λ)` compact and nonempty for `|λ| ≤ ε` (`|·|` the Euclidean norm `eucNorm`);
  (2) `A` in general position at every point (the project's `IsGeneralPositionAt`, Definition
  4.21).
- The step concerns a point `z' = (λ, x') ∈ A` over a regular value `λ` of `p_σ`, `σ` the local
  faces through `z'`.  The text speaks of `T_{z'}({λ} × A_λ)`, so it presupposes that
  `A_λ = {x | (λ, x) ∈ A}` (the project's `fibreSet`) is, near `x'`, a smooth finite-dimensional
  submanifold of `X` (the text has it for `A_λ ∩ U(z)`, item V4_61).  B assumes this only near
  `x'`: data `(V', s')` of Definition 4.13 for `A_λ` at `x'` (an sc⁺-retraction `s'` of an open
  `V' ∋ x'`, the project's `IsScPlusRetractionOn`, with `s'(V') = A_λ ∩ V'`), which the chart
  reading below needs anyway.
- Charts (the tangent spaces are read in a chart, as in Definitions 4.16, 4.21): a product chart
  `ψ = (r ↦ r − a) × φ` of `Z` (`rnChart m a`, `φ` a chart of `X`), a presentation `T` of the
  partial quadrant of `φ`, data `(V, s)` of Definition 4.13 for `A` at `z'` with `V` in the domain
  of `ψ`, data `(V', s')` for `A_λ` at `x'` with `V'` in the domain of `φ`, and the level-`1` lift
  `y` of `ψ(z')`.  Then `T_{z'}A = N_A = T_y(ψ(A ∩ V))`, `T_{z'}({λ} × A_λ) = {0} × N_λ` with
  `N_λ = T_{y₂}(φ(A_λ ∩ V'))`, `T^R_{z'}Z = T_yO_Z ∩ (ℝᵐ × E_{y₂})` (`E_{y₂}`:
  `minimalSubspaceWith T`, the vectors whose coordinates vanish where those of `y₂` do), so
  `T_{z'}(A ∩ F_σ°) = N_A ∩ (ℝᵐ × E_{y₂})` and
  `T_{z'}(({λ} × A_λ) ∩ F_σ°) = {0} × (N_λ ∩ E_{y₂})`
  (tangent spaces of the strata: the reduced tangent spaces, Definition 2.38).  The derivative of
  `P` in `ψ` is `v ↦ v.1`.  The hypothesis "`λ` is a regular value of `p_σ`" is used at `z'` in
  this chart: `v ↦ v.1` maps `N_A ∩ (ℝᵐ × E_{y₂})` onto `ℝᵐ`.  The chart is arbitrary (not required
  to be modelled on a tame retract).
- Conclusions: (a) the decomposition: some subspace `ξ` (the text's `ξ_{z'}`, on which `Tp` is an
  isomorphism onto `ℝᵐ`: each `μ ∈ ℝᵐ` is `v.1` for exactly one `v ∈ ξ`) with
  `N_A ∩ (ℝᵐ × E_{y₂}) = ({0} × (N_λ ∩ E_{y₂})) ⊕ ξ` (algebraic direct sum); (b)
  "`T_{z'}({λ} × A_λ)` has an sc-complement in `T^R_{z'}X`": I read this (garbled: the complement
  must lie in `T_{x'}X` and inside `T^R_{x'}X`) as Definition 4.21 for `A_λ` at `x'`, the project's
  `IsGeneralPositionAt` (the section's title: general position of the fibre).
- Nothing looks false to me apart from the garbled wording of the last clause.
-/
namespace RoundTrip.V4_62
open Polyfold

/-- The Euclidean norm `|λ|` on `ℝᵐ`. -/
noncomputable def eucNorm {m : ℕ} (l : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, l i ^ 2)

/-- In the proof of Theorem 4.23: at a point `z' = (λ, x')` of `A` over a regular value of
`p_σ`, `T_{z'}(A ∩ F_σ°) = T_{z'}(({λ} × A_λ) ∩ F_σ°) ⊕ ξ_{z'}`, and `A_λ` is in general position
at `x'`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (m : ℕ) [ParacompactSpace ((Fin m → ℝ) × X)] (A : Set ((Fin m → ℝ) × X)) (ε : ℝ),
    PX.IsTame →
    (∃ _ : ParacompactSpace A, ((rnPolyfold m).prod PX).IsTameSubmanifold A) →
    IsCompact (closure A) →
    0 < ε →
    -- (1)
    (∀ l : Fin m → ℝ, eucNorm l ≤ ε →
      IsCompact {z | z ∈ A ∧ z.1 = l} ∧ {z | z ∈ A ∧ z.1 = l}.Nonempty) →
    -- (2) general position of `A` at every point
    (∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z) →
    ∀ z' ∈ A,
    ∀ (a : Fin m → ℝ) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
      (V : Set ((Fin m → ℝ) × X)) (s : (Fin m → ℝ) × X → (Fin m → ℝ) × X)
      (V' : Set X) (s' : X → X) (y : ((rnSc m).prod φ.model.E).lvl 1)
      (NA : Submodule ℝ (((rnSc m).prod φ.model.E).lvl 0)) (Nl : Submodule ℝ (φ.model.E.lvl 0)),
      PX.IsChart φ → φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 →
      ((rnPolyfold m).prod PX).IsScPlusRetractionOn s V → s '' V = A ∩ V → z' ∈ V →
      V ⊆ ((rnChart m a).prod φ).toPartialEquiv.source →
      PX.IsScPlusRetractionOn s' V' → s' '' V' = fibreSet A z'.1 ∩ V' → z'.2 ∈ V' →
      V' ⊆ φ.toPartialEquiv.source →
      ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ).toPartialEquiv z' →
      -- `N_A = T_{z'}A`, `N_λ = T_{x'}A_λ`
      (NA : Set (((rnSc m).prod φ.model.E).lvl 0)) =
        tangentSpace ((rnSc m).prod φ.model.E) (Set.univ ×ˢ φ.model.C)
          (((rnChart m a).prod φ).toPartialEquiv '' (A ∩ V)) y →
      (Nl : Set (φ.model.E.lvl 0)) =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (fibreSet A z'.1 ∩ V')) y.2 →
      -- `λ` regular for `p_σ` at `z'`: `Tp` maps `T_{z'}(A ∩ F_σ°)` onto `ℝᵐ`
      (∀ μ : Fin m → ℝ, ∃ v ∈ NA,
        v.2 ∈ minimalSubspaceWith T (φ.model.E.toBase 1 y.2) ∧ v.1 = μ) →
        -- (a) `T_{z'}(A ∩ F_σ°) = T_{z'}(({λ} × A_λ) ∩ F_σ°) ⊕ ξ_{z'}`
        (∃ ξ : Submodule ℝ ((Fin m → ℝ) × φ.model.E.lvl 0),
          Disjoint (Submodule.prod ⊥ (Nl ⊓ minimalSubspaceWith T (φ.model.E.toBase 1 y.2))) ξ ∧
          Submodule.prod ⊥ (Nl ⊓ minimalSubspaceWith T (φ.model.E.toBase 1 y.2)) ⊔ ξ =
            NA ⊓ Submodule.prod ⊤ (minimalSubspaceWith T (φ.model.E.toBase 1 y.2)) ∧
          ∀ μ : Fin m → ℝ, ∃! v, v ∈ ξ ∧ v.1 = μ) ∧
        -- (b) `A_λ` is in general position at `x'`
        PX.IsGeneralPositionAt (fibreSet A z'.1) z'.2

end RoundTrip.V4_62
