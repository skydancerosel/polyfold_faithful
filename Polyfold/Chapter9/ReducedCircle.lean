import Polyfold.Chapter9.ReducedIntegral
import Polyfold.Chapter9.CircleWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.5,
**Proposition 9.5.13 (2)**, p. 446: a witness with nonempty support for the hypotheses of
`proposition_9_5_13_2`.

The unit circle `Θ = 1_{S¹}` in the trivial ep-groupoid of `ℝ²`, with the counter-clockwise
orientation and the integration `(epFormEval 1).sheetIntegration` of the sc-differential `1`-forms
(`circle_witness`, `CircleWitness.lean`): the trivial ep-groupoid has LUC (`isLUC_trivial`), so
every natural representation has the property of Definition 7.2.18, and all hypotheses of
Proposition 9.5.13 (2) hold with `supp Θ = S¹ ≠ ∅` (`circle_hcovL`, `circle_proposition_9_5_13_2`).
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace EpGroupoid

/-- The hypothesis of Theorem 9.5.5 for the circle: every point of `S¹` has an oriented tame
structure with sheets in the class of `epFormEval 1`, describing the orientation, whose `U(x)`
has the property of Definition 7.2.18. -/
theorem circle_hcovL : ∀ x ∈ supp circleTheta,
    ∃ C : (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x,
      (∀ i, C.M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).sheets) ∧
        C.Represents circleT ∧ C.rep.HasLUC := fun x hx => by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := circle_witness
  obtain ⟨C, hS, hT⟩ := h x hx
  exact ⟨C, hS, hT,
    (trivial (rnPolyfold 2)).isLUC_iff_forall_naturalRep.1 (isLUC_trivial _) x C.rep⟩

/-- **Proposition 9.5.13 (2) for the circle** (the hypotheses of `proposition_9_5_13_2` hold
with nonempty support): `X = trivial ℝ²` has LUC, `![1, 0] ∈ supp Θ`, and for every `1`-form `ω`
the effective branched integral of `Θ̂ = 1_{S¹}` on `X` equals the branched integral of the
induced data on `X_R`. -/
theorem circle_proposition_9_5_13_2 :
    (trivial (rnPolyfold 2)).IsLUC ∧ (![1, 0] : Fin 2 → ℝ) ∈ supp circleTheta ∧
      ∀ ω : (trivial (rnPolyfold 2)).epForms 1,
        letI := (trivial (rnPolyfold 2)).t2Space_reducedMor_of_isLUC (isLUC_trivial _)
        branchedIntegralEff (((trivial (rnPolyfold 2)).epFormEval 1).sheetIntegration one_pos)
            circle_witness.1 circle_witness.2.1 circle_witness.2.2.2.2.1 circle_hcovL ω =
          branchedIntegral
            (((trivial (rnPolyfold 2)).epFormEval 1).sheetIntegration one_pos).toReduced
            circle_witness.1.toReduced circle_witness.2.1.toReduced
            circle_witness.2.2.2.2.1.toReduced (hcov_reduced circle_hcovL) ω :=
  ⟨isLUC_trivial _, circle_witness.2.2.2.2.2.1, fun ω =>
    proposition_9_5_13_2 _ (isLUC_trivial _) circle_witness.1 circle_witness.2.1
      circle_witness.2.2.2.2.1 circle_hcovL ω⟩

end EpGroupoid

end Polyfold
