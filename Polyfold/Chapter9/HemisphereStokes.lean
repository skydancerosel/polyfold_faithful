import Polyfold.Chapter9.StokesBoundaryMeasure
import Polyfold.Chapter9.HemisphereWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorem 9.5.17 (Stokes), p. 449**, gap G.110: a witness with
boundary.  Numbers and pages are the 2021 text's.

# Stokes' theorem for the closed hemisphere

For the trivial ep-groupoid of `X = [0,∞) × ℝ²`, `Θ = 1` on the closed upper hemisphere
`{|p| = 1}` (a compact `2`-dimensional tame sheet whose boundary stratum is the equator), all
hypotheses of `EP.theorem_9_5_17_msheets` hold (E8W's `e8w_stokes_hypotheses`), so
`∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for every `ω ∈ Ω¹_{ep,∞}(X)`, with `∂S ≠ ∅`.

* **`E8W.e8_hemisphere_stokes`**.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace E8W

open EpGroupoid

/-- **Theorem 9.5.17 for the closed hemisphere**: the boundary `∂S` (the equator) is nonempty,
and `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for every `ω ∈ Ω¹_{ep,∞}(X)`, `μ^{∂Θ̂}` the boundary measure of
Theorem 9.5.15. -/
theorem e8_hemisphere_stokes :
    (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧
    ∀ ω : AH.epFormsInfty 1,
      (AH.epFormsInftyEval 2).tameBranchedIntegral (Nat.succ_pos 1) e8w_isBranchedEpSubgroupoid
          e8w_isCompactBranched e8w_isOrientation (fun x hx => (e8w_hcov x hx).imp fun _ h => h.1)
          (AH.epFormsInftyD 1 ω) =
        AH.boundaryBranchedMeasure one_pos e8w_isBranchedEpSubgroupoid e8w_isCompactBranched
          e8w_isOrientation e8w_hcov ω univ :=
  ⟨e8w_boundary_nonempty, fun ω => AH.theorem_9_5_17_msheets one_pos e8w_hasScPartitionsOfUnity
    e8w_isBranchedEpSubgroupoid e8w_isCompactBranched e8w_isOrientation e8w_hcov ω⟩

end E8W

end Polyfold
