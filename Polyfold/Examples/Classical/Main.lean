import Polyfold.Examples.Classical.Count

/-!
# The classical reduction: Theorem 16.6.6 for an equivariant map of `ℝⁿ`

Theorem 16.6.6, 2021 p. 739, for Fredholm index `0`, for the sc-Fredholm section
`|x| ↦ |(x, φ x)|` of the strong polyfold bundle `|ℝⁿ × ℝⁿ| → ℝⁿ/G`: `G` a finite group acting
linearly and faithfully on `ℝⁿ`, `σ` a fibre action with `det ρ(g) · det σ(g) > 0`, and
`φ : ℝⁿ → ℝⁿ` a proper equivariant `C^∞` map, `φ (g • x) = σ g (φ x)`.  The count of the constant
form `1` for every admissible perturbation with the canonical orientation is the classical count
`(1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`, for any regular value `c` with `gNorm σ c ≤ 1`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `theorem_16_6_6_hypotheses_classical`: the hypotheses of
  `theorem_16_6_6_index_zero_count_eq_unconditional` hold: `∂Z = ∅`, the solution set is compact,
  `n = nG σ` is an auxiliary norm, `Z = ℝⁿ/G` is open, `(n, Z)` controls compactness, and
  `CanonicalGermInput o 0` for the orientation `o = clOrientationRep`.
* **`count_eq_classicalCount`**: the value `Λ(f(x)) = ♯{g | φ x = σ g c} / ♯G` of the
  multisection of the constant branches `σ g c`; an admissible perturbed solution set with the
  canonical orientation exists; and every such `Q` has `Q.count 1 = classicalCount G φ c`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure SBLocalization PolyfoldClass

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-- **The hypotheses of Theorem 16.6.6 (2021 p. 739, index `0`) for the section
`|x| ↦ |(x, φ x)|` of `|ℝⁿ × ℝⁿ| → ℝⁿ/G`**: `∂Z = ∅`, the solution set is compact, `nG σ` is an
auxiliary norm, `Z` is open, `(nG σ, Z)` controls compactness, and the model of the orientation
`clOrientationRep` has tame germ data and Fredholm index `0`. -/
theorem theorem_16_6_6_hypotheses_classical (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    (clBundle σ).polyfold.boundary = ∅ ∧ (clFredholmSection σ hφ heq).1.HasCompactSolutionSet ∧
      (clBundle σ).IsAuxNorm (nG σ) ∧ IsOpen (univ : Set (AG σ).X.OrbitSpace) ∧
      (clFredholmSection σ hφ heq).1.ControlsCompactness (nG σ)
        (univ : Set (AG σ).X.OrbitSpace) ∧
      CanonicalGermInput (clOrientationRep σ hφ heq hdet) 0 :=
  ⟨clBundle_boundary_eq_empty σ, hasCompactSolutionSet hφ heq hprop, isAuxNorm_nG σ,
    isOpen_univ, controlsCompactness_nG hφ heq hprop,
    canonicalGermInput_clOrientationRep σ hφ heq hdet⟩

/-- **Theorem 16.6.6 (2021 p. 739, index `0`) for a proper equivariant map of `ℝⁿ`: the count is
the classical count.**  Let `G` act linearly and faithfully on `ℝⁿ`, `σ` be a fibre action with
`det ρ(g) · det σ(g) > 0`, `φ` a proper equivariant `C^∞` map and `c` a regular value of `φ`
with `gNorm σ c ≤ 1`.  Then
1. the multisection `Λ` of the constant branches `x ↦ σ g c`, weight `1/♯G` each, takes the
   value `Λ(f(x)) = ♯{g | φ x = σ g c} / ♯G`;
2. its class `λ = tG σ c` gives an admissible perturbed solution set with the canonical
   orientation `clOrientationRep`;
3. every admissible perturbed solution set `Q` with the canonical orientation has count
   `Q.count 1 = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)` on the constant form `1`. -/
theorem count_eq_classicalCount
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : gNorm σ c ≤ 1) :
    (∀ x : Fin n → ℝ, ΛG σ c (fSec φ x) =
      ((Finset.univ.filter fun g : G => φ x = σ g c).card : ℚ≥0) / Fintype.card G) ∧
    (∃ Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1, Q.t = tG σ c ∧
      Q.IsAdmissible (nG σ) (univ : Set (AG σ).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q) ∧
    ∀ Q : PointOrientedPerturbation (clFredholmSection σ hφ heq).1,
      Q.IsAdmissible (nG σ) (univ : Set (AG σ).X.OrbitSpace) →
      IsCanonicalPointSolutionSet (clOrientationRep σ hφ heq hdet) Q →
      Q.count (clOne σ) = classicalCount G φ c := by
  obtain ⟨Q₁, ht₁, a₁, c₁⟩ := exists_canonical_tG σ hφ heq hdet hprop hc hc1
  refine ⟨ΛG_fSec σ φ c, ⟨Q₁, ht₁, a₁, c₁⟩, fun Q a hcan => ?_⟩
  exact (theorem_16_6_6_index_zero_count_eq_unconditional (clBundle_boundary_eq_empty σ)
    (isAuxNorm_nG σ) isOpen_univ (controlsCompactness_nG hφ heq hprop)
    (canonicalGermInput_clOrientationRep σ hφ heq hdet) a hcan a₁ c₁ (clOne σ)
    (d_clOne σ)).1.trans (count_tG_eq_classicalCount σ hφ heq hdet hprop hc ht₁ c₁)

end Polyfold.Examples.Classical
