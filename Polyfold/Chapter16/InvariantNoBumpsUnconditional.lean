import Polyfold.Chapter16.InvariantNoBumps
import Polyfold.Chapter15.RestrictedSeedsAssembly

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8), with Definition 16.6.5 (p. 739), Theorem 15.4.3 and
Corollary 15.4.4 (pp. 702–703).

# Theorem 16.6.6 over all admissible perturbations, with no bump functions

## The text, paraphrased

(Theorem 16.6.6) Let `∂Z = ∅`, `f` be an oriented sc-Fredholm section of `p : Y → Z` with compact
solution set and index `k`, and `(n, U)` control compactness.  For an sc⁺-multisection `λ`
controlled by `(n, U)` with `(f, λ)` in general position, the branched integrals `∫_θ̂ τ`,
`∮_θ̂ τ` of a closed `k`-form `τ` over `θ̂ = λ ∘ f` with the orientation inherited from `f` are
well defined, do not depend on `λ`, and depend only on `[τ]`.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

The standing hypotheses in the model of the orientation `o` are `CanonicalGermInput o k`: tame
germ data of the representative `F` and index `k` at the smooth points.  Neither sc-smooth bump
functions nor partitions of unity are assumed.

* `hasRestrictedFamilies_of_germInput`: the local families near the compact set exist
  (`SBLocalization.hasRestrictedCylinderFamilies_of_seedCentres`).
* **`theorem_16_6_6_integral_eq_unconditional`**: for any two admissible perturbed solution sets
  with the canonical orientation of `(f, o)`, `∫_θ̂ τ` and `∮_θ̂ τ` agree for closed `τ`.
* **`theorem_16_6_6_all_admissible_unconditional`**: `theorem_16_6_6_statement` for the predicate
  "`θ̂` carries the canonical orientation of `(f, o)`".
* **`theorem_16_6_6_wellDefined_unconditional`**: existence for every admissible `λ`,
  independence of `λ`, and dependence on `[τ]` only.

## Reading

The orientation inherited from `f` is the canonical orientation of Definition 15.4.2 in the model
carrying `o`.  The functions used for the perturbation of the cylinder are sc-smooth near the
compact set only (Remark 9.5.19), and the cobordism argument runs on the restriction of the model
to a saturated open neighbourhood of that set; the orientations are compared in chart domains.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP EpGroupoid

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **The local families near the compact set exist in the model of `o`**, for `∂Z = ∅` and
tame germ data. -/
theorem hasRestrictedFamilies_of_germInput (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {o : OrientationRep s} {k : ℕ} (H : CanonicalGermInput o k)
    (n : Y → ℝ) (U : Set Z) : HasRestrictedFamilies o n U := fun _ _ hr₀ hr₁ =>
  hasRestrictedCylinderFamilies_of_seedCentres
    (degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS) o.a.S.paracompact o.hsec o.hF H.tame
    hr₀ hr₁

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8): the integrals do not depend on the
admissible perturbation.**  Let `∂Z = ∅`, `(n, U)` control the compactness of `f`, and `o` be an
orientation of `f` (Definition 16.6.5) whose model has tame germ data and Fredholm index
`m + 1`.  Let `θ̂₀ = λ₀ ∘ f` and `θ̂₁ = λ₁ ∘ f` be perturbed solution sets of admissible `λ₀`,
`λ₁` (controlled by `(n, U)`, in general position), with the canonical orientation of `(f, o)`.
Then `∫_{θ̂₀} τ = ∫_{θ̂₁} τ` and `∮_{θ̂₀} τ = ∮_{θ̂₁} τ` for every closed `τ`.  Neither bump
functions nor partitions of unity are assumed. -/
theorem theorem_16_6_6_integral_eq_unconditional (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalGermInput o (m + 1)) {Q₀ Q₁ : OrientedPerturbation s.1 m}
    (a₀ : Q₀.IsAdmissible n U) (c₀ : IsCanonicalSolutionSet o Q₀)
    (a₁ : Q₁.IsAdmissible n U) (c₁ : IsCanonicalSolutionSet o Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  theorem_16_6_6_integral_eq_of_restrictedFamilies hbd hn hU hcc H
    (hasRestrictedFamilies_of_germInput hbd H n U) a₀ c₀ a₁ c₁ τ hτ

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), over all admissible perturbations.**
For `∂Z = ∅`, `f` with `(n, U)` controlling compactness and every orientation `o` of `f` whose
model has tame germ data and Fredholm index `m + 1`: over the admissible perturbed solution sets
`θ̂ = λ ∘ f` with the canonical orientation of `(f, o)`, `∫_θ̂ τ` and `∮_θ̂ τ` depend only on
`[τ]`, and a closed `τ` has the same `∫_θ̂ τ` and `∮_θ̂ τ` for any two of them.  Neither bump
functions nor partitions of unity are assumed. -/
theorem theorem_16_6_6_all_admissible_unconditional (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (m : ℕ) :
    theorem_16_6_6_statement s n U m
      (fun o Q => CanonicalGermInput o (m + 1) ∧ IsCanonicalSolutionSet o Q) := by
  intro hbd _ hn hU hcc o
  refine ⟨fun P _ _ τ η =>
    P.toCompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty hbd τ η, ?_⟩
  rintro P₀ P₁ a₀ ⟨H, c₀⟩ a₁ ⟨-, c₁⟩ τ hτ
  exact theorem_16_6_6_integral_eq_unconditional hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ

/-- **2021 Theorem 16.6.6, p. 739, existence and independence over all admissible `λ`.**  Under
the hypotheses of `theorem_16_6_6_all_admissible_unconditional`: (1) every sc⁺-multisection `λ`
controlled by `(n, U)` with `(f, λ)` in general position has a perturbed solution set
`θ̂ = λ ∘ f`, compact, tame and oriented of dimension `m + 1`, with the canonical orientation of
`(f, o)`; (2) for any two such `θ̂` the integrals `∫_θ̂ τ` and `∮_θ̂ τ` of a closed `τ` agree;
(3) they depend only on `[τ]`. -/
theorem theorem_16_6_6_wellDefined_unconditional (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalGermInput o (m + 1)) :
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalSolutionSet o Q) ∧
    (∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U → IsCanonicalSolutionSet o Q₀ →
      Q₁.IsAdmissible n U → IsCanonicalSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ) ∧
    ∀ Q : OrientedPerturbation s.1 m, ∀ (τ : ScForm c.polyfold (m + 1))
      (η : ScForm c.polyfold m),
      Q.integral (τ + ScForm.d η) = Q.integral τ ∧
        Q.integralEff (τ + ScForm.d η) = Q.integralEff τ :=
  theorem_16_6_6_wellDefined_of_restrictedFamilies hbd hn hU hcc H
    (hasRestrictedFamilies_of_germInput hbd H n U)

end StrongPolyfoldBundle

end Polyfold
