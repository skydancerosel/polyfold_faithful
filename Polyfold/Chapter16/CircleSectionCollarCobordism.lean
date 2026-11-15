import Polyfold.Chapter15.CollarCobordismCorollary
import Polyfold.Chapter16.CircleSectionCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) with the collar cobordism, on the circle section.

# The collar cobordism for the circle section over `ℝ²`

## What is formalized (namespace `Polyfold.TrivialBundle`)

The example is `ℝ² × ℝ → ℝ²` over the trivial ep-groupoid of `ℝ²` (`epSEP 2 1`) with
`f(x) = (x, x₀² + x₁² − 1)`, index `1`, solution set the unit circle, fibres `ℝ`.

* **`corollary_15_4_4_oriented_collar_circleSection`**: the conclusion of
  `corollary_15_4_4_oriented_collar` there, from the one hypothesis that `ℝ²` admits sc-smooth
  partitions of unity (no compact solution set hypothesis, no partitions of unity in step (b)).
* **`collar_cobordism_circleSection`**: a canonically oriented regular perturbation `P` (with
  `|supp Θ|` the circle) and a regular perturbation `Λ̃` of `f̃` on `[0, 1] × ℝ²` for the collar
  norm with `Λ̃ = Λ_P` on both ends, whose `Θ̃ = Λ̃ ∘ f̃` meets the boundary `{0, 1} × ℝ²` of the
  cylinder; and the oriented compact cobordism `hasOrientedCobordism_collar` from `P` to `P`.
  Both ends are the same perturbation here.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15 SEP
  StrongBundleEquivalenceExamples StrongBundleLocalizationExamples

/-- **Corollary 15.4.4 (2021 p. 703) for the circle section, with partitions of unity only for
Stokes** (`corollary_15_4_4_oriented_collar`): exact `1`-forms integrate to `0` over every
regular perturbation of `f` with the canonical orientation of `(f, o)`, and a closed `1`-form
has the same integral over any two of them. -/
theorem corollary_15_4_4_oriented_collar_circleSection :
    corollary_15_4_4_statement (epSEP 2 1) circleSection 0
      (IsCanonicalPerturbation isScFredholmSectionFunctor_circleSection.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation) := by
  obtain ⟨-, -, hd, hpara, -, -, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_circleSection
  exact corollary_15_4_4_oriented_collar hd hF hft (hasScPlusSectionsThrough_epSEP 2 1)
    (hasScPlusSectionsThrough_cubeSEP_epSEP 2 1) circleSectionOrientation ho hinv hidx hpara
    (rnPolyfold_admitsScPartitionsOfUnity 2)

/-- **The collar cobordism on the circle section is not degenerate**: there is a regular
perturbation `P` of `f` with the canonical orientation and `|supp Θ| ≠ ∅`, a regular perturbation
`Λ̃` of `f̃` on `[0, 1] × ℝ²` for the collar norm with `Λ̃ = Λ_P` on the ends `t = 0` and `t = 1`,
a point `z` of the boundary of the cylinder with `0 < Λ̃(f̃(z))`, and `P` is joined to itself by
the oriented compact cobordism of `hasOrientedCobordism_collar`. -/
theorem collar_cobordism_circleSection :
    ∃ P : OrientedRegularPerturbation (epSEP 2 1) circleSection 0,
      IsCanonicalPerturbation isScFredholmSectionFunctor_circleSection.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation P ∧
      (EpGroupoid.supp (fun z => (P.Λ (circleSection z) : ℚ))).Nonempty ∧
      P.HasOrientedCobordism P ∧
      ∃ Λ' : ((epSEP 2 1).cubeSEP 1).W → ℚ≥0,
        IsRegularPerturbation ((epSEP 2 1).cubeSEP 1)
          (cubeLiftEp (n := 1) circleSection isScFredholmSectionFunctor_circleSection.1.1.1)
          (collarAuxNorm (epSEP 2 1) P.N P.N) (interpSet (epSEP 2 1) P.U P.U) Λ' ∧
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P.Λ (cubeVal w).2) ∧
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P.Λ (cubeVal w).2) ∧
        ∃ z ∈ ((epSEP 2 1).cubeSEP 1).X.PObj.boundary,
          0 < Λ' (cubeLiftEp (n := 1) circleSection
            isScFredholmSectionFunctor_circleSection.1.1.1 z) := by
  obtain ⟨-, -, hd, hpara, hPU, hPUC, hF, hft, -, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_circleSection
  obtain ⟨P, -, hP, x, hx⟩ := exists_isCanonicalPerturbation_circleSection
  have hbump := EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU
  have hcob : P.HasOrientedCobordism P :=
    hasOrientedCobordism_collar hd hF hft (hasScPlusSectionsThrough_epSEP 2 1)
      (hasScPlusSectionsThrough_cubeSEP_epSEP 2 1) circleSectionOrientation ho
      (isOrInvariant_cubeOrientation hF hft (hasScPlusSectionsThrough_epSEP 2 1)
        (hasScPlusSectionsThrough_cubeSEP_epSEP 2 1) circleSectionOrientation hinv)
      hidx hpara hbump (hasScPartitionsOfUnity_cyl hpara hPUC) hP hP
  obtain ⟨Λ', hreg, e0, e1, -, -⟩ :=
    corollary_15_3_10_3_collar hd hpara hbump hF hft P.isRegular P.isRegular
  have hpos : 0 < P.Λ (circleSection x) := by
    have h : (0 : ℚ) < (P.Λ (circleSection x) : ℚ) := hx
    exact_mod_cast h
  let z : ((epSEP 2 1).cubeSEP 1).Obj := (fun _ => 0, x)
  have hz : z ∈ ((epSEP 2 1).cubeSEP 1).X.PObj.boundary :=
    (mem_boundary_cubeSEP_iff (EpGroupoid.isTame_of_degIndex_eq_zero _ hd) hd z).2
      (Or.inl rfl)
  refine ⟨P, hP, ⟨x, hx⟩, hcob, Λ', hreg, e0, e1, z, hz, ?_⟩
  rw [e0 _ rfl]
  exact hpos

end TrivialBundle

end Polyfold
