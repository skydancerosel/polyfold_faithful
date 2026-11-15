import Polyfold.Chapter9.StokesTextHypotheses
import Polyfold.Chapter9.HemisphereWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorems 9.5.15 and 9.5.17, p. 449**, gaps G.109, G.110: the
hypotheses of `EP.theorem_9_5_15_class` and `EP.theorem_9_5_17` hold for an example with boundary.
Numbers and pages are the 2021 text's.

For the trivial ep-groupoid of `X = [0,∞) × ℝ²` and `Θ = 1` on the closed upper hemisphere (Hemisphere),
the text's hypotheses (sc-smooth partitions of unity, `Θ` compact, branched, oriented, tame in the
reading `hloc`) hold and `supp(∂Θ)` (the equator) is nonempty.

* **`Hemisphere.stokes`**.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace Hemisphere

open EpGroupoid

/-- `hloc` for the closed hemisphere (an oriented tame structure describing `T̂Θ` at every point
of `supp Θ`). -/
theorem hloc : ∀ x ∈ supp thetaH, ∃ C : AH.X.OrientedTameStructure 2 thetaH x,
    C.Represents TH :=
  fun x hx => (hcov x hx).imp fun _ h => h.1

/-- **Theorem 9.5.17 with the text's hypotheses, for the closed hemisphere**: `supp(∂Θ) ≠ ∅` and
`∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for every `ω ∈ Ω¹_{ep,∞}(X)`, `μ^{∂Θ̂}` the boundary measure of
Theorem 9.5.15 (`EP.boundaryMeasure`). -/
theorem stokes :
    (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧
    ∀ ω : AH.epFormsInfty 1,
      (AH.epFormsInftyEval 2).tameBranchedIntegral (Nat.succ_pos 1) isBranchedEpSubgroupoid
          isCompactBranched isOrientation hloc (AH.epFormsInftyD 1 ω) =
        AH.boundaryMeasure one_pos isBranchedEpSubgroupoid isCompactBranched
          isOrientation hloc ω univ :=
  ⟨boundary_nonempty, AH.theorem_9_5_17 one_pos hasScPartitionsOfUnity
    isBranchedEpSubgroupoid isCompactBranched isOrientation hloc⟩

end Hemisphere

end Polyfold
