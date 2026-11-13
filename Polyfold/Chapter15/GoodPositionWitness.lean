import Polyfold.Chapter15.InteriorPerturbationWitness
import Polyfold.Chapter15.GeneralPositionBranched
import Polyfold.Chapter15.GeneralPositionLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.2, pp. 689–690:
satisfiability of the hypotheses of **Theorem 15.2.5** (`theorem_15_2_5_hyp`).

# A witness for the boundary local perturbation theorem

Over the trivial ep-groupoid of `ℝⁿ` with the strong bundle `ℝⁿ × ℝ⁰ → ℝⁿ`
(`StrongBundleEquivalenceExamples.epSEP n 0`), the graph section of `0` and the trivial
multisection `Λ₀` satisfy all hypotheses of `theorem_15_2_5_hyp` at every point: the section is an
sc-Fredholm section functor with germ data in tame charts, `Λ₀` is an sc⁺-multisection, and
`(f, Λ₀)` is in good position (Definition 15.2.4, `IsGoodPositionAt`) at every `x`. Good position
comes from general position (every pair is in general position there, the fibres being `0`)
through Remark 15.3.6 (`remark_15_3_6_goodPosition_hyp`), which uses Part I's Lemma 5.26 for the
branches `(f − sᵢ)|O`.  The same example satisfies the hypotheses of the general position variant
`theorem_15_2_5_generalPosition_hyp` (the trivial ep-groupoid of `ℝⁿ` is tame).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace SBLocalization

open StrongBundle TrivialBundle

/-- **The hypotheses of Theorem 15.2.5 (`theorem_15_2_5_hyp`) are satisfiable at every point**:
over `ℝⁿ × ℝ⁰ → ℝⁿ` on the trivial ep-groupoid of `ℝⁿ`, the zero (graph) section and the trivial
multisection are in good position (Definition 15.2.4) everywhere. -/
theorem theorem_15_2_5_hyp_witness (n : ℕ) :
    (StrongBundleEquivalenceExamples.epSEP n 0).E.IsScFredholmSectionFunctor
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ))) ∧
      (StrongBundleEquivalenceExamples.epSEP n 0).B.IsScFredholmSectionTame
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ))) ∧
      IsScPlusMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) ∧
      ∀ x : Fin n → ℝ, IsGoodPositionAt (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)))
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) x := by
  obtain ⟨hf, hft, hΛ, -, hall⟩ := theorem_15_2_2_hyp_witness n
  refine ⟨hf, hft, hΛ, fun x => ?_⟩
  exact (remark_15_3_6_goodPosition_hyp hf hft hΛ (isInGeneralPosition_epSEP_zero n _ _)
    (hall x).2).1

/-- **Theorem 15.2.5 applies** in the example of `theorem_15_2_5_hyp_witness`: its conclusion
holds at every point of `ℝⁿ` (so the statement is not vacuous). -/
theorem theorem_15_2_5_hyp_applies (n : ℕ) (x : Fin n → ℝ) :
    ∃ (R : (StrongBundleEquivalenceExamples.epSEP n 0).X.NaturalRep x)
      (O : Set (StrongBundleEquivalenceExamples.epSEP n 0).Obj) (k : ℕ)
      (s : Fin k → (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
        (StrongBundleEquivalenceExamples.epSEP n 0).W) (σ : Fin k → ℚ≥0),
      IsOpen O ∧ IsLocalRepOn (StrongBundleEquivalenceExamples.epSEP n 0)
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) O s σ ∧
      ∀ y ∈ R.U, 0 < zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
          (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) y) →
        IsGoodPositionAt (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)))
          (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) y := by
  obtain ⟨hf, hft, hΛ, hgp⟩ := theorem_15_2_5_hyp_witness n
  obtain ⟨R, O, k, s, σ, -, hO, hrep, -, -, -, -, -, -, h2, -⟩ :=
    theorem_15_2_5_hyp hf hft hΛ (hgp x)
  exact ⟨R, O, k, s, σ, hO, hrep, h2⟩

/-- **The hypotheses of the general position variant of Theorem 15.2.5
(`theorem_15_2_5_generalPosition_hyp`) are satisfiable at every point**, in the example of
`theorem_15_2_5_hyp_witness`. -/
theorem theorem_15_2_5_generalPosition_hyp_witness (n : ℕ) :
    (StrongBundleEquivalenceExamples.epSEP n 0).X.IsTame ∧
      (StrongBundleEquivalenceExamples.epSEP n 0).E.IsScFredholmSectionFunctor
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ))) ∧
      (StrongBundleEquivalenceExamples.epSEP n 0).B.IsScFredholmSectionTame
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ))) ∧
      IsScPlusMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) ∧
      ∀ x : Fin n → ℝ, 0 < zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
          (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) x) ∧
        IsInGeneralPositionAt (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)))
          (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) x := by
  obtain ⟨hf, hft, hΛ, -, hall⟩ := theorem_15_2_2_hyp_witness n
  have hgp := (isInGeneralPosition_iff_forall_at hf hΛ).1 (isInGeneralPosition_epSEP_zero n _ _)
  exact ⟨EpGroupoid.isTame_trivial_rn n, hf, hft, hΛ, fun x => ⟨(hall x).2, hgp x (hall x).2⟩⟩

end SBLocalization

end Polyfold
