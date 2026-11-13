import Polyfold.Chapter16.PolyfoldBundleUniqueness
import Polyfold.Chapter16.PolyfoldBundleCategory
import Polyfold.Chapter16.PolyfoldAuxNorm
import Polyfold.Chapter16.PolyfoldSections
import Polyfold.Chapter16.PolyfoldExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3: satisfiability of the definitions and hypotheses of §16.3 on the strong polyfold bundle
`ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (`z3Bundle k`, `PolyfoldBundleUniqueness.lean`).

* `z3Bundle_isTame` (Definition 16.3.5 (1)), `z3Bundle_hasReflexiveFibers` (Definition 16.3.12),
  `z3Bundle_exists_reflexiveAuxNorm` (Theorem 16.3.15 (1) applied), `z3Bundle_exists_auxNorm`
  (Proposition 16.3.10 applied).
* `IsAuxNorm.isAuxNormBoundary`: the restriction of an auxiliary norm is one of `Y_{0,1}|∂Z`, so
  the hypotheses of Theorem 16.3.17 (1) are met (`theorem_16_3_17_one_witness`).
* `z3_id_isInvertible`: the identity of `S_PBS` is invertible (Definition 16.3.6).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

open EPLocalization SBLocalization StrongPolyfoldBundleStructure StrongBundleLocalizationExamples
open EpGroupoid.Examples

namespace StrongPolyfoldBundle

universe u

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- The restriction of an auxiliary norm to `Y_{0,1}|∂Z` is an auxiliary norm there. -/
theorem IsAuxNorm.isAuxNormBoundary {n : Y → ℝ} (hn : c.IsAuxNorm n) : c.IsAuxNormBoundary n :=
  fun S hS => (hn S hS).isAuxNormOn _

/-- **The hypotheses of Theorem 16.3.17 (1) can be met** on every tame strong polyfold bundle
(an auxiliary norm of Proposition 16.3.10, restricted to `∂Z`). -/
theorem theorem_16_3_17_one_witness (c : StrongPolyfoldBundle p) :
    ∃ n : Y → ℝ, c.IsAuxNormBoundary n := by
  obtain ⟨n, hn⟩ := c.proposition_16_3_10
  exact ⟨n, hn.isAuxNormBoundary⟩

variable (k : ℕ)

/-- **Witness for Definition 16.3.5 (1)**: `z3Bundle k` is tame. -/
theorem z3Bundle_isTame : (z3Bundle k).IsTame :=
  ⟨(z3Structure k).toPolyfoldStructure, rfl, rnPolyfold_isTame⟩

/-- **Witness for Definition 16.3.12**: `z3Bundle k` has reflexive `1`-fibres. -/
theorem z3Bundle_hasReflexiveFibers : (z3Bundle k).HasReflexiveFibers :=
  ⟨z3Structure k, rfl, TrivialBundle.hasReflexiveFibers_bundle⟩

/-- **Witness for Definition 16.3.13** (Theorem 16.3.15 (1)). -/
theorem z3Bundle_exists_reflexiveAuxNorm :
    ∃ n : (z3SEP k).E.toEpGroupoid.OrbitSpace → ℝ, (z3Bundle k).IsReflexiveAuxNorm n :=
  theorem_16_3_15_one (z3Bundle_hasReflexiveFibers k)

/-- **Witness for Definition 16.3.9** (Proposition 16.3.10). -/
theorem z3Bundle_exists_auxNorm :
    ∃ n : (z3SEP k).E.toEpGroupoid.OrbitSpace → ℝ, (z3Bundle k).IsAuxNorm n :=
  (z3Bundle k).proposition_16_3_10

/-- **Witness for Definition 16.3.6**: the identity morphism of `S_PBS` at `z3Structure k` is
invertible. -/
theorem z3_id_isInvertible :
    (𝟙 (SPBS.mk' (z3Structure k)) : SPBS.Hom _ _).IsInvertible :=
  (SPBS.isIso_iff_isInvertible _).1 inferInstance

end StrongPolyfoldBundle

end Polyfold
