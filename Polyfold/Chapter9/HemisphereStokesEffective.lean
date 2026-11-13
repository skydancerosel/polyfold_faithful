import Polyfold.Chapter9.HemisphereStokes

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorem 9.5.18 (effective Stokes), p. 450**, gap G.110: a witness
with boundary for the hypotheses of the effective version.  Numbers and pages are the 2021 text's.

# The effective Stokes theorem for the closed hemisphere

E8W's closed upper hemisphere in `X = [0,∞) × ℝ²` (trivial ep-groupoid, `Θ = 1` on `{|p| = 1}`)
satisfies the hypotheses of `EP.theorem_9_5_17_msheets`.  The trivial ep-groupoid has trivial
isotropy groups, so every natural representation has the local unique continuation property of
Definition 7.2.18 (`Φ(g) = Φ(1) = id`).  Hence the hypotheses of `EP.theorem_9_5_18_msheets`
(which ask for LUC of the representations) hold too, jointly with `∂S ≠ ∅`.

* `E8W.hasLUC_trivial`: every natural representation of a trivial ep-groupoid has LUC.
* `E8W.e8w_hcovEff`: the class hypothesis of Theorem 9.5.18 for the hemisphere.
* **`E8W.e8_hemisphere_stokes_eff`**: `∂S ≠ ∅` and `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every
  `ω ∈ Ω¹_{ep,∞}(X)`.
* `E8W.e8w_stokes_eff_hypotheses`: all hypotheses of Theorem 9.5.18, jointly, with
  `supp Θ ≠ ∅` and `supp(∂Θ) ≠ ∅`.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace E8W

open EpGroupoid

/-- **Every natural representation of a trivial ep-groupoid has the local unique continuation
property** (Definition 7.2.18): the isotropy group is trivial, so `Φ(g) = Φ(1)`, the identity on
`U(x)`. -/
theorem hasLUC_trivial {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {x : Z} (R : (trivial P).NaturalRep x) : R.HasLUC := by
  intro g _ _ _ _ _ y hy
  rw [Subsingleton.elim g 1]
  exact R.Φ_one y hy

/-- **The class hypothesis of Theorem 9.5.18 for the closed hemisphere**: E8W's structures
(`e8w_hcov`), whose representations have LUC. -/
theorem e8w_hcovEff : ∀ x ∈ supp thetaH, ∃ C : AH.X.OrientedTameStructure 2 thetaH x,
    C.Represents TH ∧ (∀ i, C.M i ∈ (AH.epFormsInftyEval 2).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty →
        C.boundarySheet i ∈ (AH.epFormsInftyEval 1).msheets) ∧ C.rep.HasLUC := fun x hx => by
  obtain ⟨C, h1, h2, h3⟩ := e8w_hcov x hx
  exact ⟨C, h1, h2, h3, hasLUC_trivial C.rep⟩

/-- **Theorem 9.5.18 for the closed hemisphere**: the boundary `∂S` (the equator) is nonempty,
and `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` for every `ω ∈ Ω¹_{ep,∞}(X)`, with the effective boundary measure
of Theorem 9.5.16. -/
theorem e8_hemisphere_stokes_eff :
    (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧
    ∀ ω : AH.epFormsInfty 1,
      (AH.epFormsInftyEval 2).tameBranchedIntegralEff (Nat.succ_pos 1) e8w_isBranchedEpSubgroupoid
          e8w_isCompactBranched e8w_isOrientation
          (fun x hx => (e8w_hcovEff x hx).imp fun _ h => ⟨h.1, h.2.2.2⟩)
          (AH.epFormsInftyD 1 ω) =
        AH.boundaryBranchedMeasureEff one_pos e8w_isBranchedEpSubgroupoid e8w_isCompactBranched
          e8w_isOrientation e8w_hcovEff ω univ :=
  ⟨e8w_boundary_nonempty, fun ω => AH.theorem_9_5_18_msheets one_pos e8w_hasScPartitionsOfUnity
    e8w_isBranchedEpSubgroupoid e8w_isCompactBranched e8w_isOrientation e8w_hcovEff ω⟩

/-- **The hypotheses of Theorem 9.5.18 are jointly satisfiable with `∂S ≠ ∅`**: partitions of
unity, a compact branched ep⁺-subgroupoid with an orientation, the class hypothesis with LUC,
`supp Θ ≠ ∅` and `supp(∂Θ) ≠ ∅`. -/
theorem e8w_stokes_eff_hypotheses :
    AH.X.HasScPartitionsOfUnity ∧ AH.X.IsBranchedEpSubgroupoid thetaH ∧
      AH.X.IsCompactBranched thetaH ∧ AH.X.IsOrientation thetaH TH ∧
      (∀ x ∈ supp thetaH, ∃ C : AH.X.OrientedTameStructure 2 thetaH x,
        C.Represents TH ∧ (∀ i, C.M i ∈ (AH.epFormsInftyEval 2).sheets) ∧
          (∀ i, (C.boundarySheet i).Nonempty →
            C.boundarySheet i ∈ (AH.epFormsInftyEval 1).msheets) ∧ C.rep.HasLUC) ∧
      (supp (AH.X.boundaryTheta thetaH)).Nonempty ∧ (supp thetaH).Nonempty :=
  ⟨e8w_hasScPartitionsOfUnity, e8w_isBranchedEpSubgroupoid, e8w_isCompactBranched,
    e8w_isOrientation, e8w_hcovEff, e8w_boundary_nonempty, e8w_supp_nonempty⟩

end E8W

end Polyfold
