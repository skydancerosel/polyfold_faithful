import Polyfold.Chapter16.InvariantAllAdmissible
import Polyfold.Chapter16.CircleSectionPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8) over all admissible perturbations, on an example.

# The hypotheses of `theorem_16_6_6_all_admissible_wellDefined` on the circle section

The strong polyfold bundle `ℝ² × ℝ → ℝ²` with the section `x ↦ (x, |x|² − 1)` of
`Chapter16/CircleSectionPolyfold` (non-zero fibres, solution set the unit circle, index `1`):

* `theorem_16_6_6_all_admissible_hypotheses_circle`: `∂Z = ∅`, the standing hypotheses
  `CanonicalBumpInput` hold in the model of the orientation, and a perturbed solution set with
  non-empty support carrying the canonical orientation exists.
* `theorem_16_6_6_all_admissible_circle`: the conclusions of
  `theorem_16_6_6_all_admissible_wellDefined` for every `(n, U)` controlling compactness.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid SEP StrongPolyfoldBundle
  PolyfoldClass StrongBundleEquivalenceExamples

/-- **The hypotheses of Theorem 16.6.6 over all admissible perturbations hold on the circle
section**: `∂Z = ∅`, the standing hypotheses in the model of the orientation (bump functions,
tame germ data, index `1`), and a perturbed solution set with non-empty support and the canonical
orientation of `(f, o)`. -/
theorem theorem_16_6_6_all_admissible_hypotheses_circle :
    circlePolyfoldBundle.polyfold.boundary = ∅ ∧
    CanonicalBumpInput circleOrientationRep (0 + 1) ∧
    ∃ (P : OrientedRegularPerturbation (epSEP 2 1) circleSection 0)
      (Q : OrientedPerturbation circleFredholmSection.1 0),
      (EpGroupoid.supp (fun z => (P.Λ (circleSection z) : ℚ))).Nonempty ∧
      (ModelPerturbation.ofRegular P).toOrientedPerturbation circleOrientationRep.ha = Q ∧
      IsCanonicalSolutionSet circleOrientationRep Q := by
  obtain ⟨P, -, hcan, hsupp⟩ := exists_isCanonicalPerturbation_circleSection
  exact ⟨circlePolyfoldBundle_boundary_eq_empty,
    canonicalInput_circleOrientationRep.canonicalBumpInput
      circlePolyfoldBundle_admitsScPartitionsOfUnity, P, _, hsupp, rfl,
    IsInheritedFrom.isCanonicalSolutionSet ⟨P, hcan, rfl⟩⟩

/-- **Theorem 16.6.6 over all admissible perturbations on the circle section**: for every
`(n, U)` controlling compactness, every admissible `λ` has a canonically oriented `θ̂ = λ ∘ f`,
the integrals of closed forms over any two of them agree, and they depend only on `[τ]`. -/
theorem theorem_16_6_6_all_admissible_circle {n : _ → ℝ} (hn : circlePolyfoldBundle.IsAuxNorm n)
    {U : Set _} (hU : IsOpen U) (hcc : circleFredholmSection.1.ControlsCompactness n U) :
    (∀ t : ScPlusMultisection circlePolyfoldBundle, t.IsControlledBy n U →
      circleFredholmSection.1.IsInGeneralPositionWith t →
      ∃ Q : OrientedPerturbation circleFredholmSection.1 0, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalSolutionSet circleOrientationRep Q) ∧
    (∀ Q₀ Q₁ : OrientedPerturbation circleFredholmSection.1 0, Q₀.IsAdmissible n U →
      IsCanonicalSolutionSet circleOrientationRep Q₀ → Q₁.IsAdmissible n U →
      IsCanonicalSolutionSet circleOrientationRep Q₁ →
      ∀ τ : ScForm circlePolyfoldBundle.polyfold (0 + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ) ∧
    ∀ Q : OrientedPerturbation circleFredholmSection.1 0,
      ∀ (τ : ScForm circlePolyfoldBundle.polyfold (0 + 1))
        (η : ScForm circlePolyfoldBundle.polyfold 0),
        Q.integral (τ + ScForm.d η) = Q.integral τ ∧
          Q.integralEff (τ + ScForm.d η) = Q.integralEff τ :=
  theorem_16_6_6_all_admissible_wellDefined theorem_16_6_6_all_admissible_hypotheses_circle.1
    hn hU hcc theorem_16_6_6_all_admissible_hypotheses_circle.2.1

end TrivialBundle

end Polyfold
