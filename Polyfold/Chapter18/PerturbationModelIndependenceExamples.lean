import Polyfold.Chapter18.PerturbationModelIndependence
import Polyfold.Chapter18.PerturbationExamples
import Polyfold.Chapter18.MultisectionFunctorsExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18:
**witnesses** for the model-free forms of Theorem 18.6.1 (pp. 860–861) and Theorem 18.4.4
(p. 855) and for Theorem 15.3.9 in the polyfold context (p. 861)
(`PerturbationModelIndependence.lean`), on the reflection bundle of Chapter 17.  Numbers and
pages are the 2021 text's.

# The model-free perturbation theorems for the reflection bundle

`C = ℤ/2 ⋉ ℝ`, `E = ℝ × ℝ` with `−1` acting by `(x, v) ↦ (−x, −v)`, `f(x) = (x, x)`
(`reflDiag`).  The examples are not degenerate in the isotropy: `f ≠ 0` off `0` and the isotropy
`−1` of `0` acts on the fibre by `v ↦ −v`; here `∂C = ∅`.

* `theorem_18_6_1_modelFree_witness`: every hypothesis of `theorem_18_6_1_modelFree`
  holds (including `HasStrongBundleUniformizers`), and the perturbation it gives is transversal
  and in general position in **every** covering model.
* `reflQ_hasModelMPolyfoldPartitionsOfUnity`, `exists_isBoundaryStructurableFunctor`,
  `orbitBoundaryDomSupp_reflection`.
* `theorem_18_4_4_modelFree_witness`: every hypothesis of `theorem_18_4_4_modelFree` holds for an
  auxiliary norm, the non-trivial structurable `Λ` of `proposition_18_4_3_witness`, `V = |C|`
  and `β = 1`, and its conclusion.
* `theorem_15_3_9_categorical_witness`: every hypothesis of `theorem_15_3_9_categorical`
  holds for `reflDiag` with `Λ` as above and `h = 1`, and its conclusion.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory StrongPolyfoldBundleConstruction PolyfoldConstruction SBLocalization

/-- **The model-free Theorem 18.6.1 for the diagonal section of the reflection bundle**, with
`h = 1`: its hypotheses hold, and the structurable perturbation `Λ` it gives has (3) and (4) in
every covering model. -/
theorem theorem_18_6_1_modelFree_witness :
    reflQ.HasStrongBundleUniformizers ∧
      ∃ (N : reflV.EObj → ℝ≥0∞) (U : Set GCT.reflection.toGroupoidStr.OrbitSpace),
        reflQ.IsAuxNormFunctor N ∧ reflDiag.ControlsCompactness N U ∧
        ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ ∧
          (∀ α, pointwiseNormFunctor N Λ α < ENNReal.ofReal 1) ∧ orbitDomSupp Λ ⊆ U ∧
          (∀ c : reflQ.BundleCoveringFamily, reflQ.IsTransversalIn c.Ψ reflDiag Λ ∧
            reflQ.IsInGeneralPositionIn c.Ψ reflDiag Λ) ∧
          reflectionConstruction.IsBranchedSubcategory (fun α => (Λ (reflDiag.toFun α) : ℚ)) ∧
          GCT.reflection.IsCompactBranched (fun α => (Λ (reflDiag.toFun α) : ℚ)) ∧
          reflectionConstruction.IsTameModel (fun α => (Λ (reflDiag.toFun α) : ℚ)) := by
  obtain ⟨hT, hb, hf, hfT, hF, -, -⟩ := reflDiag_orientation_hyp
  obtain ⟨⟨N, hN⟩, hU⟩ := reflDiag_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  obtain ⟨Λ, hΛ, h1, h2, h3, h4, h5⟩ := theorem_18_6_1_modelFree hF hT hb hf hfT
    reflDiag_hasCompactModuliSpace hN hU.controlsCompactness
    reflection_isContinuousFunctionFunctor_one (fun _ => ⟨one_pos, le_rfl⟩)
  have hms := hΛ.isScPlusMultisectionFunctor
  exact ⟨hF, N, U, hN, hU.controlsCompactness, Λ, hΛ, h1, h2, fun c =>
    ⟨(isTransversalFunctor_iff_forall hf hms).1 h3 c,
      (isInGeneralPositionFunctor_iff_forall hf hms).1 h4 c⟩, h5⟩

/-- The objects of the covering model `reflPair` admit sc-smooth partitions of unity. -/
theorem reflQ_hasModelMPolyfoldPartitionsOfUnity : reflQ.HasModelMPolyfoldPartitionsOfUnity :=
  ⟨reflPair, reflModel_admitsScPartitionsOfUnity⟩

/-- The non-trivial structurable `Λ` of `proposition_18_4_3_witness` is structurable over the
boundary in the model-free sense (here `∂C = ∅`). -/
theorem exists_isBoundaryStructurableFunctor :
    ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ ∧
      0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) ∧
      reflQ.IsBoundaryStructurableFunctor Λ := by
  obtain ⟨-, -, Λ, -, hΛ, -, -, hpos⟩ := proposition_18_4_3_witness
  refine ⟨Λ, hΛ, hpos, hΛ.1, reflPair, ?_⟩
  exact isBoundaryStructurable_of_boundary_eq_empty
    (reflectionConstruction.isTame_modelEpGroupoid (Ψ := reflQ.modelBase reflPair.Ψ)
      reflectionConstruction_isTame)
    (reflQ.hasParacompactOrbitSpace_model reflPair) reflModel_boundary
    (reflQ.bundlePull reflPair.Ψ Λ)

/-- `|dom-supp(Λ|∂C)| = ∅` on the reflection bundle. -/
theorem orbitBoundaryDomSupp_reflection (Λ : reflV.EObj → ℚ≥0) :
    orbitBoundaryDomSupp reflectionConstruction Λ = ∅ := by
  unfold orbitBoundaryDomSupp
  rw [reflection_boundarySet]
  simp

/-- **The model-free Theorem 18.4.4 on the reflection bundle**: all hypotheses hold for an
auxiliary norm `N`, the non-trivial structurable `Λ`, `V = |C|` and `β = 1`, and the theorem gives
a structurable `Λ'` with `N(Λ') ≤ 1`. -/
theorem theorem_18_4_4_modelFree_witness :
    reflQ.HasModelMPolyfoldPartitionsOfUnity ∧
      ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormFunctor N ∧
        ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsBoundaryStructurableFunctor Λ ∧
          0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) ∧
          reflectionConstruction.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) ∧
          ∃ Λ' : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ' ∧
            (∀ α, pointwiseNormFunctor N Λ' α ≤ ENNReal.ofReal 1) ∧ orbitDomSupp Λ' ⊆ univ ∧
            ∀ e : reflV.EObj, reflV.base e ∈ reflectionConstruction.boundarySet →
              Λ' e = Λ e := by
  obtain ⟨N, hN⟩ := reflQ_exists_isAuxNormFunctor
  obtain ⟨Λ, -, hpos, hbs⟩ := exists_isBoundaryStructurableFunctor
  refine ⟨reflQ_hasModelMPolyfoldPartitionsOfUnity, N, hN, Λ, hbs, hpos,
    reflection_isContinuousFunctionFunctor_one, ?_⟩
  refine theorem_18_4_4_modelFree reflectionConstruction_isTame
    reflQ_hasModelMPolyfoldPartitionsOfUnity hN hbs isOpen_univ (subset_univ _)
    reflection_isContinuousFunctionFunctor_one (fun _ => zero_le_one) (subset_univ _) ?_
  intro α hα
  rw [orbitBoundaryDomSupp_reflection] at hα
  exact hα.elim

/-- **Theorem 15.3.9 in the polyfold context for the diagonal section of the reflection bundle**,
with the non-trivial structurable `Λ` and `h = 1`: all hypotheses hold (the boundary conditions
because `∂C = ∅`), and the theorem gives a structurable, transversal `Λ'` with `Λ' ∘ f` a
compact branched ep⁺-subcategory. -/
theorem theorem_15_3_9_categorical_witness :
    ∃ (N : reflV.EObj → ℝ≥0∞) (U : Set GCT.reflection.toGroupoidStr.OrbitSpace),
      reflQ.IsAuxNormFunctor N ∧ reflDiag.ControlsCompactness N U ∧
      ∃ Λ : reflV.EObj → ℚ≥0, reflQ.IsBoundaryStructurableFunctor Λ ∧
        0 < Λ (reflV.objMk (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) ∧
        reflQ.IsBoundaryFaceOntoFunctor reflDiag Λ ∧
        ∃ Λ' : reflV.EObj → ℚ≥0, reflQ.IsStructurableFunctor Λ' ∧ orbitDomSupp Λ' ⊆ U ∧
          (∀ α, pointwiseNormFunctor N Λ' α < ENNReal.ofReal 1) ∧
          reflQ.IsTransversalFunctor reflDiag Λ' ∧
          reflectionConstruction.IsBranchedSubcategory (fun α => (Λ' (reflDiag.toFun α) : ℚ)) ∧
          GCT.reflection.IsCompactBranched (fun α => (Λ' (reflDiag.toFun α) : ℚ)) := by
  obtain ⟨hT, -, hf, hfT, -, -, -⟩ := reflDiag_orientation_hyp
  obtain ⟨⟨N, hN⟩, hU⟩ := reflDiag_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  obtain ⟨Λ, -, hpos, hbs⟩ := exists_isBoundaryStructurableFunctor
  have hnb : ∀ α, α ∉ reflectionConstruction.boundarySet := fun α hα => by
    rw [reflection_boundarySet] at hα; exact hα
  have hon : reflQ.IsBoundaryFaceOntoFunctor reflDiag Λ := ⟨reflPair, fun _ _ _ x hx => by
    rw [reflModel_boundary] at hx; exact hx.elim⟩
  obtain ⟨Λ', hΛ', -, h2, h1, h3, h4, h5⟩ := theorem_15_3_9_categorical hT
    reflQ_hasModelMPolyfoldPartitionsOfUnity hf hfT reflDiag_hasCompactModuliSpace hN
    hU.controlsCompactness hbs (by rw [orbitBoundaryDomSupp_reflection]; exact empty_subset _)
    (fun α hα => (hnb α hα).elim) reflection_isContinuousFunctionFunctor_one
    (fun _ => ⟨one_pos, le_rfl⟩) (fun α hα => (hnb α hα).elim) hon
  exact ⟨N, U, hN, hU.controlsCompactness, Λ, hbs, hpos, hon, Λ', hΛ', h2, h1, h3, h4, h5⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
