import Polyfold.Chapter15.P3W5PR_RestrictedEp
import Polyfold.Chapter15.P3L_Witness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.2: nonvacuity of the
tame forms of Remark 15.2.3 (`P3W5PR_TameBranched`, `P3W5PR_RestrictedEp`).

# The tame forms of Remark 15.2.3 apply with nonempty support

In the example of `theorem_15_2_2_hyp_witness` (the zero section of `ℝⁿ × ℝ⁰ → ℝⁿ` over the
trivial ep-groupoid of `ℝⁿ` and the trivial multisection `Λ₀`, with `supp(Λ₀ ∘ f) = ℝⁿ`):

* `remark_15_2_3_isTameBranched_hyp_witness`: `Λ₀ ∘ f` is a tame branched ep⁺-subgroupoid of `X`;
* `remark_15_2_3_restricted_hyp_witness`: all hypotheses of `remark_15_2_3_restricted_hyp` hold
  together (here at `0 ∈ ℝ¹`), and on the ep-groupoid `G_x ⋉ U(x)` the functor
  `z ↦ Λ₀(f(z))` is a tame branched ep⁺-subgroupoid.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold TrivialBundle EpGroupoid
open scoped Polyfold.EpGroupoid.NaturalRep

/-- **The global tame form of Remark 15.2.3 applies** (`remark_15_2_3_isTameBranched_hyp`): in
the example of `theorem_15_2_2_hyp_witness`, `Λ₀ ∘ f` is a tame branched ep⁺-subgroupoid. -/
theorem remark_15_2_3_isTameBranched_hyp_witness (n : ℕ) :
    (StrongBundleEquivalenceExamples.epSEP n 0).X.IsBranchedEpSubgroupoid (fun z =>
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
          (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) z) : ℚ)) ∧
      (StrongBundleEquivalenceExamples.epSEP n 0).X.IsTameBranched (fun z =>
        (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
          (graphSection (0 : (Fin n → ℝ) → (Fin 0 → ℝ)) z) : ℚ)) := by
  obtain ⟨hf, hft, hΛ, htr, hall⟩ := theorem_15_2_2_hyp_witness n
  exact remark_15_2_3_isTameBranched_hyp hf hft hΛ htr (fun y _ => (hall y).1)
    (EpGroupoid.paracompactSpace_orbitSupp_trivial_rn (n := n) _)

/-- **The tame form of Remark 15.2.3 on the ep-groupoid `U(x)` applies**
(`remark_15_2_3_restricted_hyp`): there are a strong bundle `A` (the example of
`theorem_15_2_2_hyp_witness`, `ℝⁿ × ℝ⁰ → ℝⁿ`, here with `n = 1`), `f`, `Λ` and `x` with all the
hypotheses, `x` in the support, and `U(x)` on whose translation ep-groupoid `z ↦ Λ(f(z))` is a
tame branched ep⁺-subgroupoid. -/
theorem remark_15_2_3_restricted_hyp_witness :
    ∃ (A : SEP.{0}) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.Obj),
      A.E.IsScFredholmSectionFunctor f ∧ A.B.IsScFredholmSectionTame f ∧
      IsScPlusMultisection A Λ ∧ A.X.PObj.degIndex x = 0 ∧ IsTransversalAt f Λ x ∧
      ∃ R : A.X.NaturalRep x,
        R.translationEpGroupoid.IsBranchedEpSubgroupoid (fun z : R.U => (Λ (f z) : ℚ)) ∧
        R.translationEpGroupoid.IsTameBranched (fun z : R.U => (Λ (f z) : ℚ)) := by
  obtain ⟨hf, hft, hΛ, htr, hall⟩ := theorem_15_2_2_hyp_witness 1
  have hx := htr (0 : Fin 1 → ℝ) (hall 0).2
  obtain ⟨R, -, hB, hT⟩ := remark_15_2_3_restricted_hyp hf hft hΛ (hall 0).1 hx
  exact ⟨_, _, _, _, hf, hft, hΛ, (hall 0).1, hx, R, hB, hT⟩

end SBLocalization

end Polyfold
