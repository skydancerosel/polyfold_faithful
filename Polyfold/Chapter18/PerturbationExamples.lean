import Polyfold.Chapter18.Perturbation
import Polyfold.Chapter18.OrientationsExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.6, pp. 860–861: **witnesses for Theorem 18.6.1** (`Perturbation.lean`) on the reflection
bundle of Chapter 17.  Numbers and pages are the 2021 text's.

# Theorem 18.6.1 for the diagonal section of the reflection bundle

`C = ℤ/2 ⋉ ℝ`, `E = ℝ × ℝ` with `−1` acting by `(x, v) ↦ (−x, −v)`, `f(x) = (x, x)`
(`reflDiag`), in the two-copy covering model `reflPair`.

* **`theorem_18_6_1_witness`**: every hypothesis of `theorem_18_6_1` holds (tame, bump
  functions, sc-Fredholm in both forms, compact `|S_f|`, an auxiliary norm `N` and `U` with
  `(N, U)` controlling compactness, the continuous functor `h = 1`), so its conclusions hold:
  a structurable `Λ` with (1)–(4) and `Λ ∘ f` compact, tame and branched.  The witness is not
  degenerate: `f ≠ 0` off `0` and the isotropy `−1` of `0` acts on the fibre by `v ↦ −v`
  (here `∂C = ∅`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory StrongPolyfoldBundleConstruction PolyfoldConstruction

/-- The constant functor `h = 1` is a continuous functor `C → (0, 1]`. -/
theorem reflection_isContinuousFunctionFunctor_one :
    reflectionConstruction.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) :=
  ⟨fun _ => rfl, fun _ => continuous_const⟩

/-- **The hypotheses and conclusions of Theorem 18.6.1 for the diagonal section** `f(x) = (x, x)`
of the reflection bundle, in the covering model `reflPair`, with `h = 1`.  Not degenerate:
`f ≠ 0` off `0`, and the isotropy `−1` of `0` acts on the fibre by `v ↦ −v ≠ v`. -/
theorem theorem_18_6_1_witness :
    reflectionConstruction.IsTame ∧ reflectionConstruction.AdmitsModelBumpFunctions ∧
      reflQ.IsScFredholmSectionFunctor reflDiag ∧ reflQ.IsScFredholmSectionFunctorTame reflDiag ∧
      reflDiag.HasCompactModuliSpace ∧
      reflectionConstruction.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) ∧
      (∀ x : Fin 1 → ℝ, x ≠ 0 → reflDiag.toFun x ≠ reflMu.objMk x 0) ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) ∧
      ∃ (N : reflV.EObj → ℝ≥0∞) (U : Set GCT.reflection.toGroupoidStr.OrbitSpace),
        reflQ.IsAuxNormFunctor N ∧ reflDiag.ControlsCompactness N U ∧
        ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ ∧
          (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal 1) ∧ orbitDomSupp Λ ⊆ U ∧
          reflQ.IsTransversalIn reflPair.Ψ reflDiag Λ ∧
          reflQ.IsInGeneralPositionIn reflPair.Ψ reflDiag Λ ∧
          reflectionConstruction.IsBranchedSubcategory (fun α => (Λ (reflDiag.toFun α) : ℚ)) ∧
          GCT.reflection.IsCompactBranched (fun α => (Λ (reflDiag.toFun α) : ℚ)) ∧
          reflectionConstruction.IsTameModel (fun α => (Λ (reflDiag.toFun α) : ℚ)) := by
  obtain ⟨hT, hb, hf, hfT, -, hnd1, hnd2⟩ := reflDiag_orientation_hyp
  obtain ⟨⟨N, hN⟩, hU⟩ := reflDiag_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  exact ⟨hT, hb, hf, hfT, reflDiag_hasCompactModuliSpace,
    reflection_isContinuousFunctionFunctor_one, hnd1, hnd2, N, U, hN, hU.controlsCompactness,
    theorem_18_6_1 reflPair hT hb hf hfT reflDiag_hasCompactModuliSpace hN
      hU.controlsCompactness reflection_isContinuousFunctionFunctor_one
      (fun _ => ⟨one_pos, le_rfl⟩)⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
