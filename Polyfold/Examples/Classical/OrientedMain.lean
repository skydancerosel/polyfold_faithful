import Polyfold.Examples.Classical.Main
import Polyfold.Examples.Classical.OrientedTransport

/-!
# The classical reduction: oriented finite-dimensional spaces

Theorem 16.6.6, 2021 p. 739 (Fredholm index `0`) for a proper equivariant map `φ : V → W`
between oriented finite-dimensional real normed spaces of dimension `n`, a finite group `G`
acting linearly on `V` and `W` through `ρ`, `σ` with `0 < det ρ(g) · det σ(g)`.

## Where the polyfold objects enter

The hypotheses are stated with Mathlib objects only: `ContDiff`, `IsCompact`, `fderiv`,
`LinearMap.det`, `Orientation.map`, `Function.Injective`.  The count
`orientedClassicalCount G oV oW φ c` is a Mathlib-only expression (see `OrientedTransport`).
Polyfold objects enter only in the conclusion, for the data transported to `ℝⁿ` by positively
oriented linear isomorphisms `eV : V ≃L ℝⁿ`, `eW : W ≃L ℝⁿ` (action `tAct eV ρ`, fibre action
`tσ eW σ`, map `tφ eV eW φ`, value `eW c`): the strong polyfold bundle `clBundle (tσ eW σ)`
through the sc-Fredholm section `clFredholmSection`, the perturbations
`PointOrientedPerturbation`, the auxiliary norm `nG`, the multisection class `tG`, the
orientation `clOrientationRep`, and the constant form `clOne`.

## What is formalized (namespace `Polyfold.Examples.Classical.Oriented`)

* `count_eq_orientedClassicalCount_of`: the oriented statement from the statement for `ℝⁿ`
  for the transported action, taken as a hypothesis `hRn`.
* **`count_eq_orientedClassicalCount`**: the same with `hRn` supplied by
  `count_eq_classicalCount` (the only place where the theorem for `ℝⁿ` is used); this needs
  `ρ` injective, through `tAct_faithfulSMul`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Oriented

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure SBLocalization PolyfoldClass

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ}
  {oV : Orientation ℝ V (Fin n)} {oW : Orientation ℝ W (Fin n)}
  (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ))
  (ρ : G →* (V →L[ℝ] V)) (σ : G →* (W →L[ℝ] W)) {φ : V → W}

/-- **Theorem 16.6.6 (2021 p. 739, index `0`) for oriented `V`, `W`, from the statement for
`ℝⁿ`.**  Let `eV`, `eW` carry `oV`, `oW` to the standard orientation of `ℝⁿ`, let `ρ` act
faithfully, and assume `hRn`: the statement of `count_eq_classicalCount` (existence and count)
for the transported action `tAct eV ρ` and every fibre action, map and value.  Then for the
transported section `|x| ↦ |(x, tφ eV eW φ x)|` of `|ℝⁿ × ℝⁿ| → ℝⁿ/G` an admissible perturbed
solution set with the canonical orientation and `Q.t = tG (tσ eW σ) (eW c)` exists, and every
such `Q` has `Q.count 1 = orientedClassicalCount G oV oW φ c`. -/
theorem count_eq_orientedClassicalCount_of (hρ : Injective ρ)
    (heV : Orientation.map (Fin n) eV.toLinearEquiv oV = stdOrientation n)
    (heW : Orientation.map (Fin n) eW.toLinearEquiv oW = stdOrientation n)
    (hdet : ∀ g : G, 0 < LinearMap.det (ρ g : V →ₗ[ℝ] V) * LinearMap.det (σ g : W →ₗ[ℝ] W))
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (ρ g x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : W}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : ∑ g : G, ‖eW (σ g c)‖ ≤ 1)
    (hRn : letI := tAct eV ρ
      haveI := tAct_smulCommClass eV ρ
      haveI := tAct_faithfulSMul eV ρ hρ
      ∀ (σ' : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
        (hdet' : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
          LinearMap.det (σ' g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
        {φ' : (Fin n → ℝ) → (Fin n → ℝ)} (hφ' : ContDiff ℝ ∞ φ')
        (heq' : ∀ (g : G) x, φ' (g • x) = σ' g (φ' x)),
        (∀ K, IsCompact K → IsCompact (φ' ⁻¹' K)) → ∀ {c' : Fin n → ℝ},
        (∀ x, φ' x = c' → Surjective (fderiv ℝ φ' x)) → gNorm σ' c' ≤ 1 →
        (∃ Q : PointOrientedPerturbation (clFredholmSection σ' hφ' heq').1, Q.t = tG σ' c' ∧
          Q.IsAdmissible (nG σ') (univ : Set (AG σ').X.OrbitSpace) ∧
          IsCanonicalPointSolutionSet (clOrientationRep σ' hφ' heq' hdet') Q) ∧
        ∀ Q : PointOrientedPerturbation (clFredholmSection σ' hφ' heq').1,
          Q.IsAdmissible (nG σ') (univ : Set (AG σ').X.OrbitSpace) →
          IsCanonicalPointSolutionSet (clOrientationRep σ' hφ' heq' hdet') Q →
          Q.count (clOne σ') = classicalCount G φ' c') :
    letI := tAct eV ρ
    haveI := tAct_smulCommClass eV ρ
    haveI := tAct_faithfulSMul eV ρ hρ
    (∃ Q : PointOrientedPerturbation
        (clFredholmSection (tσ eW σ) (contDiff_tφ eV eW hφ) (tφ_smul eV eW ρ σ heq)).1,
      Q.t = tG (tσ eW σ) (eW c) ∧
      Q.IsAdmissible (nG (tσ eW σ)) (univ : Set (AG (tσ eW σ)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (clOrientationRep (tσ eW σ) (contDiff_tφ eV eW hφ)
        (tφ_smul eV eW ρ σ heq) (hdet_transport eV eW ρ σ hdet)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (clFredholmSection (tσ eW σ) (contDiff_tφ eV eW hφ) (tφ_smul eV eW ρ σ heq)).1,
      Q.IsAdmissible (nG (tσ eW σ)) (univ : Set (AG (tσ eW σ)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet (clOrientationRep (tσ eW σ) (contDiff_tφ eV eW hφ)
        (tφ_smul eV eW ρ σ heq) (hdet_transport eV eW ρ σ hdet)) Q →
      Q.count (clOne (tσ eW σ)) = orientedClassicalCount G oV oW φ c := by
  let := tAct eV ρ
  have := tAct_smulCommClass eV ρ
  have := tAct_faithfulSMul eV ρ hρ
  obtain ⟨hex, hall⟩ := hRn (tσ eW σ) (hdet_transport eV eW ρ σ hdet) (contDiff_tφ eV eW hφ)
    (tφ_smul eV eW ρ σ heq) (isCompact_preimage_tφ eV eW hprop)
    (surjective_fderiv_tφ eV eW hc) ((gNorm_tσ eW σ c).trans_le hc1)
  exact ⟨hex, fun Q hQ hcan => (hall Q hQ hcan).trans (classicalCount_tφ eV eW heV heW φ c)⟩

/-- **Theorem 16.6.6 (2021 p. 739, index `0`) for a proper equivariant map of oriented
finite-dimensional spaces: the count is the oriented classical count.**  Let `G` act linearly
and faithfully on `V` by `ρ` and linearly on `W` by `σ` with `0 < det ρ(g) · det σ(g)`, let
`φ : V → W` be a proper equivariant `C^∞` map and `c` a regular value of `φ`, and let `eV`, `eW`
be linear isomorphisms onto `ℝⁿ` carrying `oV`, `oW` to the standard orientation, with
`∑_g ‖eW (σ g c)‖ ≤ 1` (the condition `gNorm ≤ 1` of the sup norm of `ℝⁿ` read through `eW`).
For the transported section `|x| ↦ |(x, eW (φ (eV⁻¹ x)))|` of `|ℝⁿ × ℝⁿ| → ℝⁿ/G`:
1. an admissible perturbed solution set `Q` with the canonical orientation `clOrientationRep`
   and `Q.t = tG (tσ eW σ) (eW c)` exists;
2. every admissible perturbed solution set `Q` with the canonical orientation has
   `Q.count 1 = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} orientedSign oV oW (Dφ x)`. -/
theorem count_eq_orientedClassicalCount (hρ : Injective ρ)
    (heV : Orientation.map (Fin n) eV.toLinearEquiv oV = stdOrientation n)
    (heW : Orientation.map (Fin n) eW.toLinearEquiv oW = stdOrientation n)
    (hdet : ∀ g : G, 0 < LinearMap.det (ρ g : V →ₗ[ℝ] V) * LinearMap.det (σ g : W →ₗ[ℝ] W))
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (ρ g x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : W}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : ∑ g : G, ‖eW (σ g c)‖ ≤ 1) :
    letI := tAct eV ρ
    haveI := tAct_smulCommClass eV ρ
    haveI := tAct_faithfulSMul eV ρ hρ
    (∃ Q : PointOrientedPerturbation
        (clFredholmSection (tσ eW σ) (contDiff_tφ eV eW hφ) (tφ_smul eV eW ρ σ heq)).1,
      Q.t = tG (tσ eW σ) (eW c) ∧
      Q.IsAdmissible (nG (tσ eW σ)) (univ : Set (AG (tσ eW σ)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (clOrientationRep (tσ eW σ) (contDiff_tφ eV eW hφ)
        (tφ_smul eV eW ρ σ heq) (hdet_transport eV eW ρ σ hdet)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (clFredholmSection (tσ eW σ) (contDiff_tφ eV eW hφ) (tφ_smul eV eW ρ σ heq)).1,
      Q.IsAdmissible (nG (tσ eW σ)) (univ : Set (AG (tσ eW σ)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet (clOrientationRep (tσ eW σ) (contDiff_tφ eV eW hφ)
        (tφ_smul eV eW ρ σ heq) (hdet_transport eV eW ρ σ hdet)) Q →
      Q.count (clOne (tσ eW σ)) = orientedClassicalCount G oV oW φ c :=
  count_eq_orientedClassicalCount_of eV eW ρ σ hρ heV heW hdet hφ heq hprop hc hc1
    (by
      let := tAct eV ρ
      have := tAct_smulCommClass eV ρ
      have := tAct_faithfulSMul eV ρ hρ
      exact fun σ' hdet' _ hφ' heq' hprop' _ hc' hc1' =>
        (count_eq_classicalCount σ' hdet' hφ' heq' hprop' hc' hc1').2)

end Polyfold.Examples.Classical.Oriented
