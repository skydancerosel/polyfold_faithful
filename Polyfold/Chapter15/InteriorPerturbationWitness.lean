import Polyfold.Chapter15.Transversality
import Polyfold.Chapter10.StrongBundleEquivalenceExamples
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter3.NonVacuityG
import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter5.Transversality
import Polyfold.Chapter9.Propositions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.2: satisfiability of
the hypotheses of `theorem_15_2_2_hyp` and `remark_15_2_3_isBranchedEpSubgroupoid_hyp`.

# A witness for the interior local perturbation theorem

Over the trivial ep-groupoid of `ℝⁿ` with the strong bundle `ℝⁿ × ℝ⁰ → ℝⁿ`
(`StrongBundleEquivalenceExamples.epSEP n 0`), the graph section of `0` (the zero section) and the
trivial multisection `Λ₀` (Chapter 13): `f` is an sc-Fredholm section functor with germ data in
tame charts (Part I's `isScFredholmSectionTame_graphSection`), `Λ₀` is an sc⁺-multisection,
`d_X ≡ 0`, `Λ₀ ∘ f ≡ 1`, and `(f, Λ₀)` is transversal (the fibres are `0`, so every operator into
them is onto).  So the added tame-germ hypothesis (suffix `_hyp`) is satisfiable together with all
the other hypotheses, with nonempty `supp(Λ ∘ f)`; with the paracompactness of `|supp|`
(`EpGroupoid.paracompactSpace_orbitSupp_trivial_rn`) the global form of Remark 15.2.3 applies.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold TrivialBundle

/-- **The hypotheses of Theorem 15.2.2 (`theorem_15_2_2_hyp`) and of the global form of Remark
15.2.3 are satisfiable**, with `supp(Λ ∘ f)` all of `ℝⁿ`: the zero (graph) section of
`ℝⁿ × ℝ⁰ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` and the trivial multisection. -/
theorem theorem_15_2_2_hyp_witness (n : ℕ) :
    (StrongBundleEquivalenceExamples.epSEP n 0).E.IsScFredholmSectionFunctor
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ))) ∧
      (StrongBundleEquivalenceExamples.epSEP n 0).B.IsScFredholmSectionTame
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ))) ∧
      IsScPlusMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) ∧
      IsTransversal (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)))
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) ∧
      ∀ x : Fin n → ℝ,
        (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.degIndex x = 0 ∧
        0 < zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
          (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) x) := by
  classical
  have hφ : ContDiff ℝ ∞ (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) := contDiff_const
  have hpos : ∀ x : Fin n → ℝ, 0 < zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
      (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) x) := fun x => by
    unfold zeroMultisection
    rw [if_pos]
    · exact one_pos
    · exact Prod.ext rfl (funext fun i => i.elim0)
  refine ⟨graphSection_mem_fredholmSectionFunctors_epBundle hφ,
    isScFredholmSectionTame_graphSection hφ,
    isScPlusMultisection_zeroMultisection _, fun x _ => ⟨hpos x, ?_⟩,
    fun x => ⟨rnPolyfold_degIndex n x, hpos x⟩⟩
  have hx1 : x ∈ (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.levelSet 1 := by
    have h : (x : Fin n → ℝ) ∈ (rnPolyfold n).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hx1, fun L _ w => ⟨0, ?_⟩⟩
  refine Subtype.ext (Prod.ext ?_ (funext fun i => i.elim0))
  exact ((L 0).2).trans w.2.symm

/-- **The global form of Remark 15.2.3 applies** (`remark_15_2_3_isBranchedEpSubgroupoid_hyp`):
in the example of `theorem_15_2_2_hyp_witness`, `Λ₀ ∘ f` is a branched ep⁺-subgroupoid. -/
theorem remark_15_2_3_isBranchedEpSubgroupoid_hyp_witness (n : ℕ) :
    (StrongBundleEquivalenceExamples.epSEP n 0).X.IsBranchedEpSubgroupoid fun z =>
      (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
        (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) z) : ℚ) := by
  obtain ⟨hf, hft, hΛ, htr, hall⟩ := theorem_15_2_2_hyp_witness n
  exact remark_15_2_3_isBranchedEpSubgroupoid_hyp hf hft hΛ htr (fun y _ => (hall y).1)
    (EpGroupoid.paracompactSpace_orbitSupp_trivial_rn (n := n) _)

end SBLocalization

end Polyfold
