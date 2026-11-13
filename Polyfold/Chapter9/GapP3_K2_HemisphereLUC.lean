import Polyfold.Chapter9.GapP3_K1_Hemisphere
import Polyfold.Chapter9.GapP3_K2_HemisphereEff

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorem 9.5.18 (effective Stokes), p. 450**, gap G.110: a witness
with boundary for the text's hypotheses.  Numbers and pages are the 2021 text's.

# The effective Stokes theorem for the closed hemisphere, with the text's hypotheses

The trivial ep-groupoid of E8W's closed upper hemisphere has the local unique continuation
property (Definition 7.2.18), since every natural representation has it (`hasLUC_trivial`).  So
the hypotheses of K1's `EP.theorem_9_5_18` (sc-smooth partitions of unity, `X` with LUC, `Θ`
compact, branched, oriented and tame) hold with `supp(∂Θ) ≠ ∅`.

* `E8W.e8w_isLUC`: `X` has the local unique continuation property.
* **`E8W.k2_hemisphere_stokes_eff`**: `supp(∂Θ) ≠ ∅` and `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every
  `ω ∈ Ω¹_{ep,∞}(X)`, by `EP.theorem_9_5_18`.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace E8W

open EpGroupoid

/-- **The trivial ep-groupoid of the closed hemisphere has the local unique continuation
property** (Definition 7.2.18). -/
theorem e8w_isLUC : AH.X.IsLUC :=
  AH.X.isLUC_iff_forall_naturalRep.2 fun _ R => hasLUC_trivial R

/-- **Theorem 9.5.18 with the text's hypotheses, for the closed hemisphere**: `supp(∂Θ) ≠ ∅` and
`∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every `ω ∈ Ω¹_{ep,∞}(X)`, `μ^{∂Θ̂,eff}` the effective boundary
measure of Theorem 9.5.16 (`EP.boundaryMeasureEff`). -/
theorem k2_hemisphere_stokes_eff :
    AH.X.IsLUC ∧ (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧
    ∀ ω : AH.epFormsInfty 1,
      (AH.epFormsInftyEval 2).tameBranchedIntegralEff (Nat.succ_pos 1) e8w_isBranchedEpSubgroupoid
          e8w_isCompactBranched e8w_isOrientation (AH.hloc_hasLUC e8w_isLUC k1_hloc)
          (AH.epFormsInftyD 1 ω) =
        AH.boundaryMeasureEff one_pos e8w_isLUC e8w_isBranchedEpSubgroupoid e8w_isCompactBranched
          e8w_isOrientation k1_hloc ω univ :=
  ⟨e8w_isLUC, e8w_boundary_nonempty, AH.theorem_9_5_18 one_pos e8w_hasScPartitionsOfUnity
    e8w_isLUC e8w_isBranchedEpSubgroupoid e8w_isCompactBranched e8w_isOrientation k1_hloc⟩

end E8W

end Polyfold
