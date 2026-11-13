import Polyfold.Chapter9.FiniteTheorem
import Polyfold.Chapter9.CoveringFromText
import Polyfold.Chapter9.CircleWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorem 9.5.4** (p. 438; 2017: Theorem 9.2), gap G.107.  Numbers and
pages are the 2021 text's.

# Theorem 9.5.4 for every structure, from the printed hypotheses; the circle as a witness

* `theorem_9_5_4_full_of_degIndex_eq_zero`: on an ep-groupoid without boundary, Theorem 9.5.4
  from the printed hypotheses (`Θ` compact, `n`-dimensional, oriented), with the local formula for
  every oriented tame structure describing `T̂Θ` (`theorem_9_5_4_full` with
  `hloc_of_degIndex_eq_zero`).
* `circle_theorem_9_5_4_full`: the hypotheses of `theorem_9_5_4_full` hold for the unit circle
  `S¹ ⊆ ℝ²` (`circle_witness`), so the theorem is not vacuous; its sheets need not lie in one
  graph chart.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

namespace FormEval

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
  {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2), with the printed hypotheses, without
boundary, for every oriented tame structure**: `Θ` a compact `n`-dimensional branched
ep⁺-subgroupoid, `n ≥ 1`, with an orientation `T̂Θ = T`, in an ep-groupoid whose objects have
degeneracy index `0`.  There is exactly one linear map `ω ↦ μ_ω` with the local formula for
every oriented tame structure describing `T̂Θ` and every measurable `K ⊆ |U(x)|`. -/
theorem theorem_9_5_4_full_of_degIndex_eq_zero (hn : 0 < n)
    (hdeg : ∀ a, X.PObj.degIndex a = 0) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ n) (hT : X.IsOrientation Θ T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.msheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x), C.Represents T →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.msheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasure (F.msheetIntegration hn) ω (Subtype.val '' K) :=
  F.theorem_9_5_4_full hn hΘ hcpt hT (hloc_of_degIndex_eq_zero hdeg hnd hT)

end FormEval

/-- **Theorem 9.5.4 (2021 p. 438) for every oriented tame structure, for the unit circle**: the
hypotheses of `theorem_9_5_4_full` hold for `Θ = 1_{S¹}` in `ℝ²` with the counter-clockwise
orientation (`circle_witness`). -/
theorem circle_theorem_9_5_4_full :
    ∃! Φ : (trivial (rnPolyfold 2)).epForms 1 →ₗ[ℝ]
        @SignedMeasure ((trivial (rnPolyfold 2)).orbitSupp circleTheta)
          ((trivial (rnPolyfold 2)).lebesgueSigma
            ((trivial (rnPolyfold 2)).epFormEval 1).msheetNull circleTheta),
      ∀ (w : (trivial (rnPolyfold 2)).epForms 1) (x : Fin 2 → ℝ)
        (C : (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x),
        C.Represents circleT →
        ∀ K : Set ((trivial (rnPolyfold 2)).orbitSupp circleTheta),
          MeasurableSet[(trivial (rnPolyfold 2)).lebesgueSigma
            ((trivial (rnPolyfold 2)).epFormEval 1).msheetNull circleTheta] K →
          Subtype.val '' K ⊆ (trivial (rnPolyfold 2)).π '' C.U →
          Φ w K = C.localMeasure (((trivial (rnPolyfold 2)).epFormEval 1).msheetIntegration
            one_pos) w (Subtype.val '' K) := by
  obtain ⟨hΘ, hcpt, -, -, hT, -, hloc, -⟩ := circle_witness
  exact FormEval.theorem_9_5_4_full _ one_pos hΘ hcpt hT hloc

/-- **The sheets of every oriented tame structure of the circle lie in `F.msheets`**
(`msheets_of_orientedTameStructure` for `Θ = 1_{S¹}`). -/
theorem circle_msheets_of_orientedTameStructure {x : Fin 2 → ℝ}
    (C : (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x) (i : C.ι) :
    C.M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).msheets := by
  obtain ⟨hΘ, hcpt, -, hnd, -⟩ := circle_witness
  exact FormEval.msheets_of_orientedTameStructure hΘ hcpt hnd C i

end EpGroupoid

end Polyfold
