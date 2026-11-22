import Polyfold.Chapter18.OrientationWitness
import Polyfold.Chapter18.PerturbationExamples
import Polyfold.Chapter6.UntamedIndexJump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.6, p. 861: **a witness for the orientation clause of Theorem 18.6.1**
(`theorem_18_6_1_oriented`, `Perturbation.lean`) on the reflection bundle of Chapter 17.
Numbers and pages are the 2021 text's.

# The orientation clause of Theorem 18.6.1 for the diagonal section

`C = ℤ/2 ⋉ ℝ`, `E = ℝ × ℝ` with `−1` acting by `(x, v) ↦ (−x, −v)`, `f(x) = (x, x)`
(`reflDiag`), oriented by `reflDiag_isOrientable` (`OrientationWitness.lean`), in the covering
model of one copy of `Ψ̄`.

* `isIndexAt_reflSingleModel`: the model section has Fredholm index `0` at every point (a member of
  `Lin(f, x)` is an operator `ℝ → ℝ` in the translation chart), so the index hypothesis `hidx` of
  `theorem_18_6_1_oriented` holds with `n = 0` at every point, not only on `supp(Λ ∘ f)`.
* **`theorem_18_6_1_oriented_witness`**: all hypotheses of `theorem_18_6_1_oriented` hold
  (an orientation `o` of `f`, `(N, U)` controlling compactness, the perturbation `Λ` of
  `theorem_18_6_1_structurable` with `N(Λ) ≤ 1`, `|dom-supp(Λ)| ⊆ U`, (4), and `hidx`), and so
  does its conclusion.  The witness is not degenerate: the isotropy `−1` of `0` acts on the fibre
  by `v ↦ −v`, and `o` is an orientation of `f`, not a hypothesis.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

open StrongRetr

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory StrongPolyfoldBundleConstruction PolyfoldConstruction TrivialBundle

/-- `dim T_0O = 1` in the translation chart point. -/
theorem finrank_T_reflSingleChartPt (q : Fin 1 → ℝ) :
    Module.finrank ℝ ↥(reflSingleChartPt q).T = 1 := by
  rw [reflSingleChartPt_T]
  exact (finrank_top ℝ _).trans (Module.finrank_fin_fun ℝ)

/-- `dim K_0 = 1` in the translation chart point. -/
theorem finrank_K_reflSingleChartPt (q : Fin 1 → ℝ) :
    Module.finrank ℝ ↥(reflSingleChartPt q).K = 1 := by
  rw [reflSingleChartPt_K]
  exact (finrank_top ℝ _).trans (Module.finrank_fin_fun ℝ)

/-- **The model section of `f` has index `0` at every point** (Definition 6.2.1). -/
theorem isIndexAt_reflSingleModel (x : reflSingleModel.Obj) :
    reflSingleModel.B.IsIndexAt (reflQ.modelSection reflSingle.Ψ reflDiag) x 0 := by
  obtain ⟨⟨⟩, q⟩ := x
  have hf := (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
  obtain ⟨L, hL⟩ := (reflSingleChartPt q).linSet_nonempty hf (reflSingleModel_mem_smoothSet _)
    (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
  have h := ((reflSingleChartPt q).isFredholm_isIndexAt_of_mem_linSet hf hL).2
  have : FiniteDimensional ℝ ((reflSingleChartPt q).c.φ.model.E 0) :=
    (inferInstance : FiniteDimensional ℝ (Fin 1 → ℝ))
  have : FiniteDimensional ℝ ((reflSingleChartPt q).c.F 0) :=
    (inferInstance : FiniteDimensional ℝ (Fin 1 → ℝ))
  have e : fredholmIndex L = 0 := by
    have h1 := finrank_T_reflSingleChartPt q
    have h2 := finrank_K_reflSingleChartPt q
    rw [fredholmIndex_of_finiteDimensional]
    omega
  rw [e] at h
  exact h

open SBLocalization in
/-- **The hypotheses and the conclusion of the orientation clause of Theorem 18.6.1** (p. 861)
for the diagonal section `f(x) = (x, x)` of the reflection bundle, in the covering model of one
copy of `Ψ̄`: `f` is oriented (`reflDiag_isOrientable`), the index hypothesis `hidx` holds at
every point with `n = 0`, `(N, U)` controls compactness, and the perturbation `Λ` of
`theorem_18_6_1_structurable` has `N(Λ) ≤ 1`, `|dom-supp(Λ)| ⊆ U` and (4); hence
`Θ = Λ ∘ f` carries the canonical orientation.  Not degenerate: the isotropy `−1` of `0` acts on
the fibre by `v ↦ −v`, and the orientation is an actual one of `f`. -/
theorem theorem_18_6_1_oriented_witness :
    reflQ.IsOrientable isScFredholmSectionFunctor_reflDiag reflection_admitsModelBumpFunctions
      reflectionConstruction_isTame isScFredholmSectionFunctorTame_reflDiag
      reflQ_hasStrongBundleUniformizers ∧
    (∀ x, reflSingleModel.B.IsIndexAt (reflQ.modelSection reflSingle.Ψ reflDiag) x 0) ∧
    (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) ∧
    ∃ (N : reflV.EObj → ℝ≥0∞) (U : Set GCT.reflection.toGroupoidStr.OrbitSpace),
      reflQ.IsAuxNormFunctor N ∧ reflDiag.ControlsCompactness N U ∧
      ∃ Λ : reflV.EObj → ℚ≥0, IsMorInvariant Λ ∧ reflQ.IsScPlusMultisectionIn reflSingle.Ψ Λ ∧
        (∀ α, pointwiseNormFunctor N Λ α ≤ 1) ∧ orbitDomSupp Λ ⊆ U ∧
        reflQ.IsInGeneralPositionIn reflSingle.Ψ reflDiag Λ ∧
        ∃ o, reflQ.IsOrientation isScFredholmSectionFunctor_reflDiag
          reflection_admitsModelBumpFunctions reflectionConstruction_isTame
          isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers o ∧
        ∃ O : reflectionConstruction.OrientedSubcategory,
          O.Θ = (fun α => (Λ (reflDiag.toFun α) : ℚ)) ∧
          (∀ x ∈ reflSingleModel.X.PObj.smoothSet,
            O.T reflSingle.base x = canonicalOrientation (A := reflSingleModel)
              (reflQ.bundlePull reflSingle.Ψ Λ)
              (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
              (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
              (reflQ.pullCat isScFredholmSectionFunctor_reflDiag
                reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers reflSingle o)
              x) ∧
          IsCanonicalFor (A := reflSingleModel) (reflQ.bundlePull reflSingle.Ψ Λ)
            (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
            (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
            (reflQ.pullCat isScFredholmSectionFunctor_reflDiag
              reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers reflSingle o) 0
            (canonicalOrientation (A := reflSingleModel) (reflQ.bundlePull reflSingle.Ψ Λ)
              (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
              (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
              (reflQ.pullCat isScFredholmSectionFunctor_reflDiag
                reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers reflSingle
                o)) := by
  obtain ⟨hT, hb, hf, hfT, -, -, hnd2⟩ := reflDiag_orientation_hyp
  obtain ⟨⟨N, hN⟩, hU⟩ := reflDiag_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  obtain ⟨Λ, hΛ, h1, h2, -, h4⟩ := theorem_18_6_1_structurable reflSingle hT hb hf hfT
    reflDiag_hasCompactModuliSpace hN hU.controlsCompactness
    reflection_isContinuousFunctionFunctor_one (fun _ => ⟨one_pos, le_rfl⟩)
  have hms : reflQ.IsScPlusMultisectionIn reflSingle.Ψ Λ :=
    ((reflQ.remark_18_3_4 reflSingle).1 hΛ).2.1
  have hN1 : ∀ α, pointwiseNormFunctor N Λ α ≤ 1 := fun α => by
    refine (h1 α).le.trans ?_
    rw [ENNReal.ofReal_one]
  obtain ⟨o, ho⟩ := reflDiag_isOrientable
  exact ⟨⟨o, ho⟩, isIndexAt_reflSingleModel, hnd2, N, U, hN, hU.controlsCompactness, Λ, hΛ.1, hms,
    hN1, h2, h4, o, ho, theorem_18_6_1_oriented reflSingle hT hb hf hfT
      reflQ_hasStrongBundleUniformizers ho hN hU.controlsCompactness hΛ.1 hms hN1 h2 h4
      (fun x _ => isIndexAt_reflSingleModel x)⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
