import Polyfold.Chapter9.HemisphereBoundaryMeasure
import Polyfold.Chapter9.HemisphereStokesEffective

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorem 9.5.18 (effective Stokes), p. 450**, point G.110: a witness
with boundary for the text's hypotheses.  Numbers and pages are the 2021 text's.

# The effective Stokes theorem for the closed hemisphere, with the text's hypotheses

The trivial ep-groupoid of the closed upper hemisphere (`HemisphereSheet`) has the local unique continuation
property (Definition 7.2.18), since every natural representation has it (`hasLUC_trivial`).  So
the hypotheses of `EP.theorem_9_5_18` (sc-smooth partitions of unity, `X` with LUC, `Θ`
compact, branched, oriented and tame) hold with `supp(∂Θ) ≠ ∅`.

* `Hemisphere.isLUC`: `X` has the local unique continuation property.
* **`Hemisphere.stokes_eff`**: `supp(∂Θ) ≠ ∅` and `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every
  `ω ∈ Ω¹_{ep,∞}(X)`, by `EP.theorem_9_5_18`.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace Hemisphere

open EpGroupoid

/-- **The trivial ep-groupoid of the closed hemisphere has the local unique continuation
property** (Definition 7.2.18). -/
theorem isLUC : AH.X.IsLUC :=
  AH.X.isLUC_iff_forall_naturalRep.2 fun _ R => hasLUC_trivial R

/-- **Theorem 9.5.18 with the text's hypotheses, for the closed hemisphere**: `supp(∂Θ) ≠ ∅` and
`∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every `ω ∈ Ω¹_{ep,∞}(X)`, `μ^{∂Θ̂,eff}` the effective boundary
measure of Theorem 9.5.16 (`EP.boundaryMeasureEff`). -/
theorem stokes_eff :
    AH.X.IsLUC ∧ (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧
    ∀ ω : AH.epFormsInfty 1,
      (AH.epFormsInftyEval 2).tameBranchedIntegralEff (Nat.succ_pos 1) isBranchedEpSubgroupoid
          isCompactBranched isOrientation (AH.hloc_hasLUC isLUC hloc)
          (AH.epFormsInftyD 1 ω) =
        AH.boundaryMeasureEff one_pos isLUC isBranchedEpSubgroupoid isCompactBranched
          isOrientation hloc ω univ :=
  ⟨isLUC, boundary_nonempty, AH.theorem_9_5_18 one_pos hasScPartitionsOfUnity
    isLUC isBranchedEpSubgroupoid isCompactBranched isOrientation hloc⟩

end Hemisphere

end Polyfold
