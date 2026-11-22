import Polyfold.Chapter18.AuxiliaryNormsDirect
import Polyfold.Chapter18.CompactnessExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18, §18.1,
pp. 846–848: **witnesses for `AuxiliaryNormsDirect.lean`** on the reflection bundle
`P : E → ℤ/2 ⋉ ℝ` (`reflQ`).  Numbers and pages are the 2021 text's.

* `reflQ_exists_isAuxNormDirect`, `reflQ_exists_isAuxNormBook`: Definition 18.1.7 (direct and
  printed form) is satisfiable (Theorem 18.1.12 (1)).
* `reflPair_hasReflexivePieces`: the hypothesis of `isReflexiveAuxNormDirect_iff_hyp` holds for
  the model with two copies of `Ψ̄` (fibre model `ℝ`); `reflQ_exists_isReflexiveAuxNormDirect`:
  Definition 18.1.11 is satisfiable, and `reflQ_isReflexiveAuxNormDirect_iff` gives its agreement
  with the model reading on `reflQ`.
* `reflQ_theorem_18_1_12_two`: the hypotheses and the conclusion of Theorem 18.1.12 (2).
* `reflQ_theorem_18_1_12_three`, `reflQ_theorem_18_1_12_three_reflexive`: the hypotheses of
  Theorem 18.1.12 (3) hold (tame `C`, an auxiliary norm on `E|∂C`).  Here `∂C = ∅`
  (`reflection_boundarySet`), so the agreement over `∂C` is empty; a witness with `∂C ≠ ∅` is
  not built.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle

namespace ReflectionBundle

open StrongPolyfoldBundleConstruction PolyfoldConstruction

/-- **Definition 18.1.7 (with continuity of `|N|`) is satisfiable** on the reflection bundle
(Theorem 18.1.12 (1)). -/
theorem reflQ_exists_isAuxNormDirect : ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormDirect N :=
  reflQ.theorem_18_1_12_one reflQ_hasStrongBundleUniformizers

/-- **Definition 18.1.7 as printed is satisfiable** on the reflection bundle. -/
theorem reflQ_exists_isAuxNormBook : ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormBook N := by
  obtain ⟨N, hN⟩ := reflQ_exists_isAuxNormDirect
  exact ⟨N, hN.toIsAuxNormBook⟩

/-- **The pieces of the model with two copies of `Ψ̄` have reflexive `(0, 1)`-fibres** (the
trivial bundle `ℝ × ℝ → ℝ`, fibre model `ℝ`). -/
theorem reflPair_hasReflexivePieces : reflQ.HasReflexivePieces reflPair :=
  fun _ => StrongBundle.hasReflexiveFibers_of_atlas fun c hc => by
    obtain ⟨a, rfl⟩ := hc
    exact isReflexive_of_finiteDimensional (F := Fin 1 → ℝ)

/-- **Definition 18.1.11 is satisfiable** on the reflection bundle. -/
theorem reflQ_exists_isReflexiveAuxNormDirect :
    ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsReflexiveAuxNormDirect N := by
  obtain ⟨N, hN⟩ := reflQ_exists_isReflexiveAuxNormFunctor
  exact ⟨N, hN.isReflexiveAuxNormDirect reflPair⟩

/-- **Definition 18.1.11 and the model reading agree** on the reflection bundle. -/
theorem reflQ_isReflexiveAuxNormDirect_iff {N : reflV.EObj → ℝ≥0∞} :
    reflQ.IsReflexiveAuxNormDirect N ↔ reflQ.IsReflexiveAuxNormFunctor N :=
  reflQ.isReflexiveAuxNormDirect_iff_hyp reflPair reflPair_hasReflexivePieces

/-- **Theorem 18.1.12 (2) on the reflection bundle**: the hypotheses hold (reflexive fibres, an
auxiliary norm `N'`), and `N₁ ≤ N' ≤ N₂` with reflexive `N₁`, `N₂`. -/
theorem reflQ_theorem_18_1_12_two :
    ∃ N' : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor N' ∧ reflQ.HasReflexiveFibers ∧
      ∃ N₁ N₂ : reflV.EObj → ℝ≥0∞, reflQ.IsReflexiveAuxNormFunctor N₁ ∧
        reflQ.IsReflexiveAuxNormFunctor N₂ ∧ ∀ e, N₁ e ≤ N' e ∧ N' e ≤ N₂ e := by
  obtain ⟨N', hN'⟩ := reflQ_exists_isAuxNormFunctor
  exact ⟨N', hN', reflQ_hasReflexiveFibers,
    reflQ.theorem_18_1_12_two reflPair reflQ_hasReflexiveFibers hN'⟩

/-- **Theorem 18.1.12 (3), first part, on the reflection bundle**: `C` is tame and an auxiliary
norm on `E|∂C` exists (the restriction of an auxiliary norm); it extends. -/
theorem reflQ_theorem_18_1_12_three :
    reflectionConstruction.IsTame ∧ ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsBoundaryAuxNormIn reflPair N ∧
      ∃ Ñ : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor Ñ ∧
        ∀ e, reflV.base e ∈ reflectionConstruction.boundarySet → Ñ e = N e := by
  obtain ⟨N, hN⟩ := reflQ_exists_isAuxNormFunctor
  have hb := (hN reflPair).isBoundaryAuxNormIn
  exact ⟨reflectionConstruction_isTame, N, hb,
    reflQ.theorem_18_1_12_three reflPair reflectionConstruction_isTame hb⟩

/-- **Theorem 18.1.12 (3), second part, on the reflection bundle**: with reflexive fibres, a
reflexive auxiliary norm on `E|∂C` exists and extends. -/
theorem reflQ_theorem_18_1_12_three_reflexive :
    ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsReflexiveBoundaryAuxNormIn reflPair N ∧
      ∃ Ñ : reflV.EObj → ℝ≥0∞, reflQ.IsReflexiveAuxNormFunctor Ñ ∧
        ∀ e, reflV.base e ∈ reflectionConstruction.boundarySet → Ñ e = N e := by
  obtain ⟨N, hN⟩ := reflQ_exists_isReflexiveAuxNormFunctor
  have hb := (hN reflPair).isReflexiveBoundaryAuxNormIn
  exact ⟨N, hb, reflQ.theorem_18_1_12_three_reflexive reflPair reflectionConstruction_isTame
    reflQ_hasReflexiveFibers hb⟩

end ReflectionBundle

end GCT.VectorBundle

end Polyfold
