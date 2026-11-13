import Polyfold.Chapter7.PartitionsOfUnity
import Polyfold.Chapter5.GapP1_SeparablePOU

/-!
# Corollary 7.6.6 without the Godefroy–Troyanski–Whitfield–Zizler hypothesis

2021 Corollary 7.6.6, p. 347 (2017: Corollary 7.3): an ep-groupoid with paracompact orbit space
whose object M-polyfold has an atlas of charts with Hilbert `E₀` admits sc-smooth partitions of
unity subordinate to every cover by saturated open sets.

The project's `EpGroupoid.corollary_7_6_6` took Theorem 5.5.16 (Godefroy–Troyanski–Whitfield–Zizler)
for these `E₀` as an explicit hypothesis.  Part I now has Corollary 5.5.17 with no hypothesis
(`corollary_5_5_17_unconditional`, `GapP1_SeparablePOU.lean`: the `0`-level of an sc-Banach space is
separable, and Theorem 5.5.16 holds for separable spaces) and Theorem 5.5.16 itself
(`theorem_5_5_16`, `GapP1_GTWZ.lean`).  So the corollary holds as printed.

* `EpGroupoid.corollary_7_6_6_unconditional`: Corollary 7.6.6 as printed (one Hilbert chart around
  every point of the object M-polyfold).
* `EpGroupoid.corollary_7_6_6_hypotheses_rn_unconditional`: its hypotheses hold for the trivial
  ep-groupoid of `ℝ¹`.
-/

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Corollary 7.6.6, p. 347 (2017: Corollary 7.3)**, as printed: if `|X|` is paracompact and
the object M-polyfold has an atlas (one chart around every point) whose local models have Hilbert
spaces `E₀` (`‖v‖² = b(v, v)` for a continuous bilinear `b`), then every cover of `X` by saturated
open sets has a subordinate sc-smooth partition of unity of the ep-groupoid.  The proof is the
text's: Corollary 5.5.17 and Theorem 5.5.10 give sc-smooth partitions of unity on the object
M-polyfold (`MPolyfold.admitsScPartitionsOfUnity_of_hilbert_unconditional`), and Theorem 7.5.7
applies. -/
theorem corollary_7_6_6_unconditional (hpara : X.HasParacompactOrbitSpace)
    (h : ∀ x, ∃ φ : MChart Obj, X.PObj.IsChart φ ∧ x ∈ φ.source ∧
      ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) :
    X.HasScPartitionsOfUnity :=
  X.theorem_7_5_7 hpara (MPolyfold.admitsScPartitionsOfUnity_of_hilbert_unconditional h)

/-- **The hypotheses of Corollary 7.6.6 (2017: 7.3) are satisfiable**: the trivial ep-groupoid on
`ℝ¹` has paracompact orbit space, and the chart `id` of `ℝ¹` has a Hilbert `E₀`. -/
theorem corollary_7_6_6_hypotheses_rn_unconditional :
    (trivial (rnPolyfold 1)).HasParacompactOrbitSpace ∧
      ∀ x, ∃ φ : MChart (Fin 1 → ℝ), (trivial (rnPolyfold 1)).PObj.IsChart φ ∧ x ∈ φ.source ∧
        ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v := by
  refine ⟨corollary_7_6_6_hypotheses_rn.1, fun x => ?_⟩
  obtain ⟨φ, hφ, hx, hb, -⟩ := corollary_7_6_6_hypotheses_rn.2 x
  exact ⟨φ, hφ, hx, hb⟩

end EpGroupoid

end Polyfold
