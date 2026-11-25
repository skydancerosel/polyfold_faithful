import Polyfold.Examples.Classical.ProductCount
import Polyfold.Examples.Classical.Corollaries

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: Theorem 16.6.6

Theorem 16.6.6, 2021 p. 739, for Fredholm index `0`, for the sc-Fredholm section
`|(x, e)| ↦ |((x, φ x), (e, e))|` of the strong polyfold bundle
`|(ℝⁿ × ℝⁿ) × (H ◁ H)| → (ℝⁿ × H)/G`: `G` a finite group acting linearly and faithfully on `ℝⁿ`
and trivially on the sc-Hilbert space `H` of `WeightedEllTwo.lean` (strictly nested levels), `σ` a
fibre action on `ℝⁿ` with `det ρ(g) · det σ(g) > 0`, and `φ : ℝⁿ → ℝⁿ` a proper equivariant `C^∞`
map.  The count of the constant form `1` for every admissible perturbation with the canonical
orientation is the classical count `(1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)`, the same number as
without the factor `H` (`count_eq_classicalCount`), for any regular value `c` with
`gNorm σ c ≤ 1`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `theorem_16_6_6_hypotheses_product`: the hypotheses of
  `theorem_16_6_6_index_zero_count_eq_unconditional` hold: `∂Z = ∅`, the solution set is compact,
  `nP σ` is an auxiliary norm, `Z = (ℝⁿ × H)/G` is open, `(nP σ, Z)` controls compactness, and
  `CanonicalGermInput o 0` for the orientation `o = prOrientationRep`.
* **`count_eq_classicalCount_product`**: the value
  `Λ(f(x, e)) = ♯{g | φ x = σ g c} / ♯G` if `e = 0` and `0` otherwise, of the multisection of the
  branches `((x, σ g c), (e, 0))`; an admissible perturbed solution set with the canonical
  orientation exists; and every such `Q` has `Q.count 1 = classicalCount G φ c`.
* **`count_powMap_product`**: for `z ↦ z^k` on `ℂ/ℤₚ` (weight `1` on `ℂ`, fibre weight `k`)
  crossed with `H`, the count is `k / p`; `count_pow_two_five_product` (`2/5`),
  `count_conjPowMap_product` (`z ↦ z̄^k`, `−k / p`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo SBLocalization PolyfoldClass
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

section General

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-- **The hypotheses of Theorem 16.6.6 (2021 p. 739, index `0`) for the section
`|(x, e)| ↦ |((x, φ x), (e, e))|` over `(ℝⁿ × H)/G`**: `∂Z = ∅`, the solution set is compact,
`nP σ` is an auxiliary norm, `Z` is open, `(nP σ, Z)` controls compactness, and the model of the
orientation `prOrientationRep` has tame germ data and Fredholm index `0`. -/
theorem theorem_16_6_6_hypotheses_product (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    (prBundle σ).polyfold.boundary = ∅ ∧
      (prFredholmSection σ hφ heq).1.HasCompactSolutionSet ∧
      (prBundle σ).IsAuxNorm (nP σ) ∧ IsOpen (univ : Set (AP σ).X.OrbitSpace) ∧
      (prFredholmSection σ hφ heq).1.ControlsCompactness (nP σ)
        (univ : Set (AP σ).X.OrbitSpace) ∧
      CanonicalGermInput (prOrientationRep σ hφ heq hdet) 0 :=
  ⟨prBundle_boundary_eq_empty σ, hasCompactSolutionSet_prFredholmSection hφ heq hprop,
    isAuxNorm_nP σ, isOpen_univ, controlsCompactness_nP hφ heq hprop,
    canonicalGermInput_prOrientationRep σ hφ heq hdet⟩

open scoped _root_.Classical in
/-- **Theorem 16.6.6 (2021 p. 739, index `0`) for a proper equivariant map of `ℝⁿ` crossed with
the sc-Hilbert space `H`: the count is the classical count.**  Let `G` act linearly and
faithfully on `ℝⁿ` and trivially on `H`, `σ` be a fibre action with `det ρ(g) · det σ(g) > 0`,
`φ` a proper equivariant `C^∞` map and `c` a regular value of `φ` with `gNorm σ c ≤ 1`.  For the
section `f(x, e) = ((x, φ x), (e, e))`,
1. the multisection `Λ` of the branches `(x, e) ↦ ((x, σ g c), (e, 0))`, weight `1/♯G` each,
   takes the value `Λ(f(x, e)) = ♯{g | φ x = σ g c} / ♯G` for `e = 0` and `0` otherwise;
2. its class `λ = tP σ c` gives an admissible perturbed solution set with the canonical
   orientation `prOrientationRep`;
3. every admissible perturbed solution set `Q` with the canonical orientation has count
   `Q.count 1 = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} sign det Dφ(x)` on the constant form `1`. -/
theorem count_eq_classicalCount_product
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : gNorm σ c ≤ 1) :
    (∀ x : (Fin n → ℝ) × HObj, ΛP σ c (fP σ φ x) =
      if x.2 = h0 then
        ((Finset.univ.filter fun g : G => φ x.1 = σ g c).card : ℚ≥0) / Fintype.card G
      else 0) ∧
    (∃ Q : PointOrientedPerturbation (prFredholmSection σ hφ heq).1, Q.t = tP σ c ∧
      Q.IsAdmissible (nP σ) (univ : Set (AP σ).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (prOrientationRep σ hφ heq hdet) Q) ∧
    ∀ Q : PointOrientedPerturbation (prFredholmSection σ hφ heq).1,
      Q.IsAdmissible (nP σ) (univ : Set (AP σ).X.OrbitSpace) →
      IsCanonicalPointSolutionSet (prOrientationRep σ hφ heq hdet) Q →
      Q.count (prOne σ) = classicalCount G φ c := by
  obtain ⟨Q₁, ht₁, a₁, c₁⟩ := exists_canonical_tP σ hφ heq hdet hprop hc hc1
  refine ⟨fun x => ?_, ⟨Q₁, ht₁, a₁, c₁⟩, fun Q a hcan => ?_⟩
  · rw [ΛP_fP_eq]
  · exact (theorem_16_6_6_index_zero_count_eq_unconditional (prBundle_boundary_eq_empty σ)
      (isAuxNorm_nP σ) isOpen_univ (controlsCompactness_nP hφ heq hprop)
      (canonicalGermInput_prOrientationRep σ hφ heq hdet) a hcan a₁ c₁ (prOne σ)
      (d_prOne σ)).1.trans (count_tP_eq_classicalCount σ hφ heq hdet hprop hc ht₁ c₁)

end General

/-! ### `z ↦ z^k` and `z ↦ z̄^k` on `ℂ/ℤₚ`, crossed with `H` -/

section Cyclic

open Polyfold.Examples.Classical.Cyclic

variable {p : ℕ} [NeZero p] {k : ℕ}

/-- **`z ↦ z^k` on `ℂ/ℤₚ` crossed with `H`** (Theorem 16.6.6, 2021 p. 739, index `0`): for the
section `|(z, e)| ↦ |((z, z^k), (e, e))|` an admissible perturbed solution set with the canonical
orientation exists, and every such `Q` has `Q.count 1 = k / p`. -/
theorem count_powMap_product (hk : 0 < k) :
    (∃ Q : PointOrientedPerturbation
        (prFredholmSection (σk p k) (contDiff_powMap k) (powMap_smul p k)).1,
      Q.t = tP (σk p k) (c₀ p k) ∧
      Q.IsAdmissible (nP (σk p k)) (univ : Set (AP (σk p k)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet
        (prOrientationRep (σk p k) (contDiff_powMap k) (powMap_smul p k) (hdet_σk p k)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (prFredholmSection (σk p k) (contDiff_powMap k) (powMap_smul p k)).1,
      Q.IsAdmissible (nP (σk p k)) (univ : Set (AP (σk p k)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet
        (prOrientationRep (σk p k) (contDiff_powMap k) (powMap_smul p k) (hdet_σk p k)) Q →
      Q.count (prOne (σk p k)) = (k : ℝ) / p := by
  obtain ⟨-, hex, hall⟩ := count_eq_classicalCount_product (σk p k) (hdet_σk p k)
    (contDiff_powMap k) (powMap_smul p k) (isCompact_preimage_powMap hk)
    (surjective_fderiv_powMap hk) (gNorm_σk_c₀ p k).le
  exact ⟨hex, fun Q hQ hcan => (hall Q hQ hcan).trans (classicalCount_powMap hk)⟩

/-- **`z ↦ z²` on `ℂ/ℤ₅` crossed with `H`**: every admissible perturbed solution set with the
canonical orientation has `Q.count 1 = 2/5`. -/
theorem count_pow_two_five_product
    (Q : PointOrientedPerturbation
      (prFredholmSection (σk 5 2) (contDiff_powMap 2) (powMap_smul 5 2)).1)
    (hQ : Q.IsAdmissible (nP (σk 5 2)) (univ : Set (AP (σk 5 2)).X.OrbitSpace))
    (hcan : IsCanonicalPointSolutionSet
      (prOrientationRep (σk 5 2) (contDiff_powMap 2) (powMap_smul 5 2) (hdet_σk 5 2)) Q) :
    Q.count (prOne (σk 5 2)) = 2 / 5 := by
  rw [(count_powMap_product (p := 5) (k := 2) (by norm_num)).2 Q hQ hcan]
  norm_num

/-- **`z ↦ z̄^k` on `ℂ/ℤₚ` crossed with `H`**, fibre weight `−k` (Theorem 16.6.6, 2021 p. 739,
index `0`): an admissible perturbed solution set with the canonical orientation exists, and every
such `Q` has `Q.count 1 = −k / p`. -/
theorem count_conjPowMap_product (hk : 0 < k) :
    (∃ Q : PointOrientedPerturbation
        (prFredholmSection (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)).1,
      Q.t = tP (σnk p k) (c₀ p k) ∧
      Q.IsAdmissible (nP (σnk p k)) (univ : Set (AP (σnk p k)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet
        (prOrientationRep (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)
          (hdet_σnk p k)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (prFredholmSection (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)).1,
      Q.IsAdmissible (nP (σnk p k)) (univ : Set (AP (σnk p k)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet
        (prOrientationRep (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)
          (hdet_σnk p k)) Q →
      Q.count (prOne (σnk p k)) = -((k : ℝ) / p) := by
  obtain ⟨-, hex, hall⟩ := count_eq_classicalCount_product (σnk p k) (hdet_σnk p k)
    (contDiff_conjPowMap k) (conjPowMap_smul p k) (isCompact_preimage_conjPowMap hk)
    (surjective_fderiv_conjPowMap hk) (gNorm_σnk_c₀ p k).le
  exact ⟨hex, fun Q hQ hcan => (hall Q hQ hcan).trans (classicalCount_conjPowMap hk)⟩

end Cyclic

end Polyfold.Examples.Classical.Product
