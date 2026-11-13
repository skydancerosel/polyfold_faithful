import Polyfold.Chapter9.MultiChartIntegration
import Polyfold.Chapter9.TameOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.4 and 9.5.5** (p. 438; 2017: Theorems 9.2, 9.3) and
**Definition 9.5.6** (p. 439), gap G.107.  Numbers and pages are the 2021 text's.

# Theorems 9.5.4 and 9.5.5 for sheets covered by several graph charts

E3's `theorem_9_5_4_tame` characterizes `ω ↦ μ_ω` by the local formula for the oriented tame
structures whose sheets lie in one graph chart.  With the integration over sheets covered by
countably many graph charts (`F.msheetIntegration`, `MultiChartIntegration.lean`) the local
formula holds for every oriented tame structure whose sheets carry finite integrals `∫_{Mᵢ} |ω|`
(`Mᵢ ∈ F.msheets`): `theorem_9_5_4_multi`, `theorem_9_5_5_multi`, `multiBranchedIntegral`.

The finiteness `∫_{Mᵢ} |ω| < ∞` is what makes the right-hand side of the text's formula
`∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` defined for every measurable `K ⊆ |U(x)|`; the formula is stated for
the structures with this property.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω} {Θ : Obj → ℚ}
  {T : Obj → X.PObj.OrTangent →₀ ℚ}

namespace FormEval

/-- The covering hypothesis of Theorem 9.5.4 for the class `F.msheets`. -/
theorem hcov_msheets_of_loc
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.msheets) ∧ C.Represents T := fun x hx => by
  obtain ⟨C, hC, hCT⟩ := hcov_of_loc (F := F) hloc x hx
  exact ⟨C, fun i => sheets_subset_msheets (hC i), hCT⟩

/-- The covering hypothesis of Theorem 9.5.5 for the class `F.msheets`. -/
theorem hcovEff_msheets_of_loc
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.msheets) ∧ C.Represents T ∧ C.rep.HasLUC := fun x hx => by
  obtain ⟨C, hC, hCT, hL⟩ := hcovEff_of_loc (F := F) hloc x hx
  exact ⟨C, fun i => sheets_subset_msheets (hC i), hCT, hL⟩

variable (F)

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2), for sheets in several graph charts**:
`Θ` a compact branched ep⁺-subgroupoid with an orientation `T̂Θ = T` described near every point
of its support by an oriented tame structure of dimension `n ≥ 1`.  There is exactly one linear
map `ω ↦ μ_ω` into the signed measures on `(S, L(S))` with
`μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for every oriented tame structure describing `T̂Θ`
whose sheets carry finite integrals of `|ω|` (no one-chart condition) and every measurable
`K ⊆ |U(x)|`. -/
theorem theorem_9_5_4_multi (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.msheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.msheets) ∧ C.Represents T) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.msheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasure (F.msheetIntegration hn) ω (Subtype.val '' K) :=
  theorem_9_5_4 (F.msheetIntegration hn) hΘ hcpt hT (hcov_msheets_of_loc hloc)

/-- **Theorem 9.5.5, 2021 p. 438 (2017: Theorem 9.3), for sheets in several graph charts**: the
same with the weights `1/♯G_x^eff`, for structures whose `U(x)` has the property of
Definition 7.2.18. -/
theorem theorem_9_5_5_multi (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.msheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.msheets) ∧ C.Represents T ∧ C.rep.HasLUC) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.msheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasureEff (F.msheetIntegration hn) ω (Subtype.val '' K) :=
  theorem_9_5_5 (F.msheetIntegration hn) hΘ hcpt hT (hcovEff_msheets_of_loc hloc)

/-- **Definition 9.5.6 (1), 2021 p. 439**, for sheets in several graph charts: the branched
integral `∫_Θ̂ ω = μ_ω(S)`. -/
def multiBranchedIntegral (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) (ω : Ω) : ℝ :=
  branchedIntegral (F.msheetIntegration hn) hΘ hcpt hT (hcov_msheets_of_loc hloc) ω

/-- **Definition 9.5.6 (2), 2021 p. 439**, for sheets in several graph charts: the effective
branched integral `∮_Θ̂ ω = μ_ω^eff(S)`. -/
def multiBranchedIntegralEff (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) (ω : Ω) : ℝ :=
  branchedIntegralEff (F.msheetIntegration hn) hΘ hcpt hT (hcovEff_msheets_of_loc hloc) ω

variable {F}

/-- **The local formulas of the two integrations agree** for a structure with one-chart sheets:
the sum (9.21) is the same for `F.sheetIntegration` and `F.msheetIntegration`. -/
theorem sheetSum_msheet_eq (hn : 0 < n) {x : Obj} (C : X.OrientedTameStructure n Θ x)
    (hS : ∀ i, C.M i ∈ F.sheets) (ω : Ω) {A : Set Obj} (hA : C.IsMeas F.sheetNull A) :
    C.sheetSum (F.msheetIntegration hn) ω A = C.sheetSum (F.sheetIntegration hn) ω A := by
  unfold OrientedTameStructure.sheetSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [msheetIntegration_integ, sheetIntegration_integ,
    msInteg_eq_integ hn (hS i) (C.orient i) ω
      (@MeasurableSet.inter Obj (F.sheetNull.sheetSigma (C.M i)) _ _ (hA i)
        (SheetNullSets.isMeasIn_self _))]

end FormEval

end EpGroupoid

end Polyfold
