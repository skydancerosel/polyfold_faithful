import Polyfold.Chapter9.CircleWitness
import Polyfold.Chapter9.MultiChartTheorem
import Polyfold.Chapter9.MultiChartCompact
import Polyfold.Chapter9.CoveringFromText

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorem 9.5.4** (p. 438; 2017: Theorem 9.2) and **Definition 9.5.6**
(p. 439), gap G.107.  Numbers and pages are the 2021 text's.

# Theorem 9.5.4 for the circle with the whole circle as one sheet

For `Θ = 1_{S¹}` in the trivial ep-groupoid of `ℝ²` (`CircleWitness.lean`) and a point
`x ∈ S¹`, `circleStructure x` is an oriented tame structure with `U(x) = ℝ²` whose one sheet is
the whole circle `S¹` (`circleStructure_U`, `circleStructure_M`).  Its sheet lies in the class
`F.msheets` (`circleStructure_mem_msheets`, a compact sheet), so the local formula of
`theorem_9_5_4_multi` applies to it, with `U(x) = ℝ²`.  With `K = S` it gives the branched
integral as the integral over the whole circle (`circle_multiBranchedIntegral`):
`∫_Θ̂ ω = ∫_{S¹} ω|(S¹, counter-clockwise)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

namespace EpGroupoid

open scoped Classical

/-- **The oriented tame structure at `x ∈ S¹` whose one sheet is the whole circle**: `U(x) = ℝ²`
with the natural representation `trivialNaturalRep` (`Φ = id`, `Γ = id`). -/
def circleStructure (x : Fin 2 → ℝ) (hx : x ∈ unitCircle2) :
    (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x :=
  let B₀ := orientedBranchingStructure_sum_rn circleSheet (fun _ => (1 : ℚ)) (fun _ => one_pos)
    circleSheet_isSubmanifoldOfDim circleSheet_isClosed (fun _ => circleOrientation) x
  let R := trivialNaturalRep (rnPolyfold 2) x
  have hRU : R.U ⊆ B₀.U := fun _ _ _ _ => hx
  let B := B₀.restrict R.isOpen_U R.mem_U hRU
  { toLocalBranchingStructure := B.toLocalBranchingStructure
    rep := R
    U_eq := rfl
    hasPropernessProperty := hasPropernessProperty_trivial (rnPolyfold 2) R.isOpen_U
    hasTameInducedStructure := fun i =>
      MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (B.isSmoothSubmanifold i)
        fun a _ => rnPolyfold_degIndex 2 a
    isSubmanifoldOfDim := B.isSubmanifoldOfDim
    orient := B.orient }

variable {x : Fin 2 → ℝ} (hx : x ∈ unitCircle2)

/-- `U(x) = ℝ²`. -/
theorem circleStructure_U : (circleStructure x hx).U = univ := rfl

/-- **The sheet is the whole circle.** -/
theorem circleStructure_M (i) : (circleStructure x hx).M i = unitCircle2 := by
  ext y
  refine ⟨fun h => h.1.1, fun h => ⟨⟨h, fun _ _ => hx⟩, mem_univ _⟩⟩

/-- The structure describes the counter-clockwise orientation `T̂`. -/
theorem circleStructure_represents : (circleStructure x hx).Represents circleT := by
  intro y hy _
  set B₀ := orientedBranchingStructure_sum_rn circleSheet (fun _ => (1 : ℚ)) (fun _ => one_pos)
    circleSheet_isSubmanifoldOfDim circleSheet_isClosed (fun _ => circleOrientation) x with hB₀
  have hyU : y ∈ B₀.U := fun _ _ => hx
  have hRU : (trivialNaturalRep (rnPolyfold 2) x).U ⊆ B₀.U := fun _ _ _ _ => hx
  set B := B₀.restrict (trivialNaturalRep (rnPolyfold 2) x).isOpen_U
    (trivialNaturalRep (rnPolyfold 2) x).mem_U hRU with hB
  rw [circleT, ← orientedSum_sum_rn_eq circleSheet (fun _ => (1 : ℚ)) (fun _ => one_pos)
    circleSheet_isSubmanifoldOfDim circleSheet_isClosed _ hyU]
  change B₀.orientedSum y = B.orientedSum y
  rw [OrientedBranchingStructure.orientedSum, OrientedBranchingStructure.orientedSum,
    Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hyi : y ∈ B₀.M i
  · rw [if_pos hyi, if_pos (show y ∈ B.M i from ⟨hyi, mem_univ y⟩)]
    exact congrArg (fun g => Finsupp.single g (B₀.σ i))
      ((B₀.orient i).restrict_tangent isOpen_univ (mem_univ y)).symm
  · rw [if_neg hyi, if_neg (show y ∉ B.M i from fun h => hyi h.1)]

/-- **The whole circle is a sheet of the class `F.msheets`** for the sc-differential `1`-forms
(it is compact; no one-chart condition). -/
theorem circleStructure_mem_msheets (i) :
    (circleStructure x hx).M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).msheets :=
  FormEval.msheets_of_isCompact ((circleStructure x hx).isSubmanifoldOfDim i)
    (by rw [circleStructure_M hx]; exact isCompact_unitCircle2)
    ⟨x, by rw [circleStructure_M hx]; exact hx⟩

/-- **Theorem 9.5.4 (2021 p. 438), local formula on `U(x) = ℝ²`**: the measure of
`theorem_9_5_4_multi` for the circle is given on every measurable `K ⊆ S` by the integral over
the whole circle, through the structure `circleStructure x`.  Obtained from the printed
hypotheses only (`theorem_9_5_4_of_degIndex_eq_zero`: `ℝ²` has no boundary). -/
theorem circle_theorem_9_5_4_multi :
    ∃! Φ : (trivial (rnPolyfold 2)).epForms 1 →ₗ[ℝ]
        @SignedMeasure ((trivial (rnPolyfold 2)).orbitSupp circleTheta)
          ((trivial (rnPolyfold 2)).lebesgueSigma
            ((trivial (rnPolyfold 2)).epFormEval 1).msheetNull circleTheta),
      ∀ (w : (trivial (rnPolyfold 2)).epForms 1) (x : Fin 2 → ℝ)
        (C : (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x),
        ((∀ i, C.M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).msheets) ∧
          C.Represents circleT) →
        ∀ K : Set ((trivial (rnPolyfold 2)).orbitSupp circleTheta),
          MeasurableSet[(trivial (rnPolyfold 2)).lebesgueSigma
            ((trivial (rnPolyfold 2)).epFormEval 1).msheetNull circleTheta] K →
          Subtype.val '' K ⊆ (trivial (rnPolyfold 2)).π '' C.U →
          Φ w K = C.localMeasure (((trivial (rnPolyfold 2)).epFormEval 1).msheetIntegration
            one_pos) w (Subtype.val '' K) := by
  obtain ⟨hΘ, hcpt, -, hnd, hT, -⟩ := circle_witness
  exact FormEval.theorem_9_5_4_of_degIndex_eq_zero _ one_pos (degIndex_rnPolyfold_trivial 2)
    hΘ hcpt hnd hT

/-- The structure `circleStructure x` meets the hypotheses of the local formula, for every
measurable `K ⊆ S` (`U(x) = ℝ²`). -/
theorem circleStructure_admissible :
    ((∀ i, (circleStructure x hx).M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).msheets) ∧
      (circleStructure x hx).Represents circleT) ∧
    ∀ K : Set ((trivial (rnPolyfold 2)).orbitSupp circleTheta),
      Subtype.val '' K ⊆ (trivial (rnPolyfold 2)).π '' (circleStructure x hx).U := by
  refine ⟨⟨circleStructure_mem_msheets hx, circleStructure_represents hx⟩, fun K z _ => ?_⟩
  obtain ⟨y, rfl⟩ := (trivial (rnPolyfold 2)).surjective_π z
  exact ⟨y, mem_univ y, rfl⟩

/-- **Definition 9.5.6 (1), 2021 p. 439, for the circle: `∫_Θ̂ ω = ∫_{S¹} ω|(S¹, ccw)`**.  The
branched integral of `theorem_9_5_4_multi` (any proofs of its hypotheses, e.g. from
`circle_witness`) is the integral of `ω` over the whole circle with the counter-clockwise
orientation, `Mᵢ = S¹` for the one index `i` of `circleStructure x` (`circleStructure_M`). -/
theorem circle_multiBranchedIntegral (hΘ : (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid
      circleTheta) (hcpt : (trivial (rnPolyfold 2)).IsCompactBranched circleTheta)
    (hT : (trivial (rnPolyfold 2)).IsOrientation circleTheta circleT)
    (hloc : ∀ x ∈ supp circleTheta, ∃ C : (trivial (rnPolyfold 2)).OrientedTameStructure 1
      circleTheta x, C.Represents circleT) (w : (trivial (rnPolyfold 2)).epForms 1) :
    ((trivial (rnPolyfold 2)).epFormEval 1).multiBranchedIntegral one_pos hΘ hcpt hT hloc w =
      ∑ i, (((trivial (rnPolyfold 2)).epFormEval 1).msheetIntegration one_pos).integ w
        ((circleStructure x hx).M i) ((circleStructure x hx).orient i).tangent
        ((circleStructure x hx).M i) := by
  obtain ⟨⟨hS, hCT⟩, hKU⟩ := circleStructure_admissible hx
  unfold FormEval.multiBranchedIntegral branchedIntegral
  rw [branchedMeasure_apply _ hΘ hcpt hT _ w (circleStructure x hx) hS hCT MeasurableSet.univ
    (hKU univ), OrientedTameStructure.localMeasure]
  have hcard : Nat.card ((trivial (rnPolyfold 2)).Isotropy x) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
  rw [hcard, Nat.cast_one, inv_one, one_mul, OrientedTameStructure.sheetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hσ : ((circleStructure x hx).σ i : ℝ) = 1 := by
    change (((1 : ℚ)) : ℝ) = 1
    exact Rat.cast_one
  rw [hσ, one_mul]
  congr 1
  refine inter_eq_right.2 fun y hy => ?_
  have hy' : y ∈ unitCircle2 := circleStructure_M hx i ▸ hy
  refine ⟨⟨(trivial (rnPolyfold 2)).π y, ?_⟩, mem_univ _, rfl⟩
  unfold orbitSupp
  rw [supp_circleTheta]
  exact mem_image_of_mem _ hy'

end EpGroupoid

end Polyfold
