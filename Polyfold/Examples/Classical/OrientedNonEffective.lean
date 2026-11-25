import Polyfold.Examples.Classical.NonEffectiveEffCount
import Polyfold.Examples.Classical.OrientedTransport

/-!
# The classical reduction: oriented finite-dimensional spaces, action not necessarily faithful

Theorem 16.6.6, 2021 p. 739 (Fredholm index `0`) for a proper equivariant map `φ : V → W`
between oriented finite-dimensional real normed spaces of dimension `n`, a finite group `G`
acting linearly on `V` through `ρ` (not necessarily injective) and on `W` through `σ`, with
`0 < det ρ(g) · det σ(g)`.  The kernel `ker ρ` plays the part of `K`.

## Where the polyfold objects enter

The hypotheses are stated with Mathlib objects only (`ContDiff`, `IsCompact`, `fderiv`,
`LinearMap.det`, `Orientation.map`, `MonoidHom.ker`), and so are both right-hand sides:
`orientedClassicalCount G oV oW φ c` (`OrientedTransport`) and `♯ker ρ`.  Polyfold objects enter
only in the conclusion, for the data transported to `ℝⁿ` by positively oriented linear
isomorphisms `eV`, `eW` (action `tAct eV ρ`, fibre action `tσ eW σ`, map `tφ eV eW φ`, value
`eW c`): `clFredholmSection` of the strong polyfold bundle
`clBundle (tσ eW σ)`, `PointOrientedPerturbation`, `nG`, `tG`, `clOrientationRep`,
`clOne`, and the count and effective count `Q.count`, `Q.countEff`.

## What is formalized (namespace `Polyfold.Examples.Classical.NonEffective.Oriented`)

* `mem_baseKernel_tAct_iff`, `card_baseKernel_tAct`: the kernel of the transported action is
  `ker ρ`.
* **`count_countEff_eq_orientedClassicalCount`**: an admissible perturbed solution set with the
  canonical orientation exists, and every such `Q` has
  `Q.count 1 = orientedClassicalCount G oV oW φ c` and
  `Q.countEff 1 = ♯ker ρ · orientedClassicalCount G oV oW φ c`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.NonEffective.Oriented

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure SBLocalization PolyfoldClass
open Polyfold.Examples.Classical.Oriented

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ}
  {oV : Orientation ℝ V (Fin n)} {oW : Orientation ℝ W (Fin n)}
  (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ))
  (ρ : G →* (V →L[ℝ] V)) (σ : G →* (W →L[ℝ] W)) {φ : V → W}

/-- The kernel of the transported action is `ker ρ`. -/
theorem mem_baseKernel_tAct_iff (g : G) :
    (letI := tAct eV ρ; g ∈ baseKernel G n) ↔ g ∈ ρ.ker := by
  let := tAct eV ρ
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun v => ?_
    have := h (eV v)
    change eV (ρ g (eV.symm (eV v))) = eV v at this
    simpa using this
  · intro h z
    change eV (ρ g (eV.symm z)) = z
    rw [h]
    simp

/-- `♯K = ♯ker ρ` for the transported action. -/
theorem card_baseKernel_tAct :
    (letI := tAct eV ρ; Nat.card (baseKernel G n)) = Nat.card ρ.ker := by
  let := tAct eV ρ
  exact Nat.card_congr (Equiv.subtypeEquivRight (mem_baseKernel_tAct_iff eV ρ))

/-- **Theorem 16.6.6 (2021 p. 739, index `0`) for a proper equivariant map of oriented
finite-dimensional spaces, for an action that need not be faithful: the count and the effective
count.**  Let `G` act linearly on `V` by `ρ` and on `W` by `σ` with `0 < det ρ(g) · det σ(g)`,
let `φ : V → W` be a proper equivariant `C^∞` map and `c` a regular value of `φ`, and let `eV`,
`eW` be linear isomorphisms onto `ℝⁿ` carrying `oV`, `oW` to the standard orientation, with
`∑_g ‖eW (σ g c)‖ ≤ 1`.  For the transported section `|x| ↦ |(x, eW (φ (eV⁻¹ x)))|` of
`|ℝⁿ × ℝⁿ| → ℝⁿ/G`:
1. an admissible perturbed solution set `Q` with the canonical orientation and
   `Q.t = tG (tσ eW σ) (eW c)` exists;
2. every admissible perturbed solution set `Q` with the canonical orientation has
   `Q.count 1 = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} orientedSign oV oW (Dφ x)` and
   `Q.countEff 1 = (♯ker ρ/♯G) · ∑_{x ∈ φ⁻¹(c)} orientedSign oV oW (Dφ x)`. -/
theorem count_countEff_eq_orientedClassicalCount
    (heV : Orientation.map (Fin n) eV.toLinearEquiv oV = Oriented.stdOrientation n)
    (heW : Orientation.map (Fin n) eW.toLinearEquiv oW = Oriented.stdOrientation n)
    (hdet : ∀ g : G, 0 < LinearMap.det (ρ g : V →ₗ[ℝ] V) * LinearMap.det (σ g : W →ₗ[ℝ] W))
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (ρ g x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) {c : W}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) (hc1 : ∑ g : G, ‖eW (σ g c)‖ ≤ 1) :
    letI := tAct eV ρ
    haveI := tAct_smulCommClass eV ρ
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
      Q.count (clOne (tσ eW σ)) = orientedClassicalCount G oV oW φ c ∧
        Q.countEff (clOne (tσ eW σ)) =
          (Nat.card ρ.ker : ℝ) * orientedClassicalCount G oV oW φ c := by
  let := tAct eV ρ
  have := tAct_smulCommClass eV ρ
  have hg : gNorm (tσ eW σ) (eW c) ≤ 1 := by
    refine le_of_eq_of_le ?_ hc1
    unfold gNorm
    simp
  obtain ⟨hex, hall⟩ := count_countEff_eq_classicalCount (tσ eW σ)
    (hdet_transport eV eW ρ σ hdet) (contDiff_tφ eV eW hφ) (tφ_smul eV eW ρ σ heq)
    (isCompact_preimage_tφ eV eW hprop) (surjective_fderiv_tφ eV eW hc) hg
  refine ⟨hex, fun Q hQ hcan => ?_⟩
  obtain ⟨h1, h2⟩ := hall Q hQ hcan
  rw [classicalCount_tφ eV eW heV heW φ c] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [card_baseKernel_tAct eV ρ]

end Polyfold.Examples.Classical.NonEffective.Oriented
