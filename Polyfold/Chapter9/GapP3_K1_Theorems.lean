import Polyfold.Chapter9.GapP3_K1_BoundaryCover

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps G.109, G.110; rows V9.67, V9.68).
Numbers and pages are the 2021 text's.

# Theorems 9.5.15–9.5.18 with the text's hypotheses

E7 and E8 proved Theorems 9.5.15–9.5.18 under the class conditions `hcov`, `hcovS` (structures
whose nonempty boundary sheets `∂₁Mᵢ` lie in `msheets`, and whose sheets lie in one graph chart).
`GapP3_K1_BoundaryCover` derives them from the text's hypotheses.  Here the theorems are stated
with those hypotheses only: `Θ` a compact branched ep⁺-subgroupoid, oriented by `T̂Θ = T`,
tame in the reading `hloc` (an oriented tame structure of dimension `m + 1` describing `T̂Θ` at
every point of `supp Θ`; this also gives the dimension, E4's `isNDimensional_of_loc`), `X` with
sc-smooth partitions of unity for Stokes, and `X` with the local unique continuation property
(Definition 7.2.18) for the effective versions 9.5.16, 9.5.18.  The case `m ≥ 1` (boundary
dimension `m ≥ 1`); the case `m = 0` is treated separately.

The characterizing local formula is required (and holds) for every oriented tame structure
describing `T̂Θ` whose nonempty boundary sheets lie in `msheets`; such structures exist at every
point (`EP.hcov_of_loc`), which is what uniqueness needs.  Every oriented tame structure has its
nonempty boundary sheets in `msheets` (`GapP3_K1_AllStructures`), which gives the versions
`EP.theorem_9_5_15`, `EP.theorem_9_5_16` with the local formula for every structure.

* `EP.theorem_9_5_15_class`, `EP.boundaryMeasure`: the boundary measure `ω ↦ μ^{∂Θ̂}_ω`.
* `EP.theorem_9_5_16_class`, `EP.boundaryMeasureEff`: the effective boundary measure.
* `EP.theorem_9_5_17`: `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)`.
* `EP.theorem_9_5_18`: `∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)`.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

namespace EP

open EpGroupoid

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- `hloc` with the property of Definition 7.2.18 on `U(x)`, for an ep-groupoid with the local
unique continuation property. -/
theorem hloc_hasLUC {n : ℕ} (hLUC : A.X.IsLUC)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure n Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure n Θ x, C.Represents T ∧ C.rep.HasLUC :=
  fun x hx => (hloc x hx).imp fun C h => ⟨h, A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep⟩

/-- **Theorem 9.5.15, 2021 p. 449 (2017: Theorem 9.4)**, with the text's hypotheses: `Θ`
compact, branched, oriented by `T̂Θ = T`, tame (`hloc`), of dimension `m + 1`, `m ≥ 1`.  There is
a unique linear map `ω ↦ μ^{∂Θ̂}_ω` from `Ωᵐ_{ep,∞}(X)` to the finite signed measures on
`(∂S, L(∂S))` with `μ^{∂Θ̂}_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` for every oriented
tame structure at `x ∈ supp(∂Θ)` describing `T̂Θ` (nonempty `∂₁Mᵢ` in `msheets`) and every
measurable `K ⊆ |U(x)|`. -/
theorem theorem_9_5_15_class (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
        (hCT : C.Represents T),
        x ∈ supp (A.X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty →
          C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
              ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) :=
  theorem_9_5_15_msheets (A.epFormsInftyEval m) hm hΘ hcpt (FormEval.isNDimensional_of_loc hloc)
    hT (A.hcov_of_loc hm hΘ hcpt hloc)

/-- **Theorem 9.5.16, 2021 p. 449 (2017: Theorem 9.5)**, with the text's hypotheses: `X` with
the local unique continuation property, `Θ` as in Theorem 9.5.15.  There is a unique linear
`ω ↦ μ^{∂Θ̂,eff}_ω` with the local formula of Theorem 9.5.15 with `1/♯G_x^eff`. -/
theorem theorem_9_5_16_class (hm : 0 < m) (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
        (hCT : C.Represents T),
        x ∈ supp (A.X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty →
          C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
              ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, huniq⟩ := theorem_9_5_16_msheets (A.epFormsInftyEval m) hm hΘ hcpt
    (FormEval.isNDimensional_of_loc hloc) hT (A.hcov_of_loc_isLUC hm hLUC hΘ hcpt hloc)
  refine ⟨Φ, fun ω x C hCT hx hS => hΦ ω x C hCT hx hS
    (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep), fun Ψ hΨ => huniq Ψ ?_⟩
  exact fun ω x C hCT hx hS _ => hΨ ω x C hCT hx hS

/-- **The boundary measure `ω ↦ μ^{∂Θ̂}_ω` of Theorem 9.5.15, 2021 p. 449**, for `Θ` compact,
branched, oriented, tame (`hloc`), of dimension `m + 1`, `m ≥ 1`. -/
def boundaryMeasure (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (m + 1) Θ) :=
  A.boundaryBranchedMeasure hm hΘ hcpt hT (A.hcovS_of_loc hm hΘ hcpt hloc)

/-- **The effective boundary measure `ω ↦ μ^{∂Θ̂,eff}_ω` of Theorem 9.5.16, 2021 p. 449**, for
`X` with the local unique continuation property. -/
def boundaryMeasureEff (hm : 0 < m) (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (m + 1) Θ) :=
  A.boundaryBranchedMeasureEff hm hΘ hcpt hT (A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc)

/-- `boundaryMeasure` is the measure of Theorem 9.5.15 (it has the local formula). -/
theorem boundaryMeasure_spec (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets)
    (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryMeasure hm hΘ hcpt hT hloc ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
        ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) :=
  (theorem_9_5_15_msheets (A.epFormsInftyEval m) hm hΘ hcpt
    (FormEval.isNDimensional_of_loc (A.hcovS_of_loc hm hΘ hcpt hloc)) hT
    (A.hcovB_of_hcovS (A.hcovS_of_loc hm hΘ hcpt hloc))).exists.choose_spec
    ω x C hCT hx hS K hK hKU

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449 (2017: Theorem 9.6)**, with the text's hypotheses:
`X` with sc-smooth partitions of unity, `Θ` a compact branched ep⁺-subgroupoid, oriented by
`T̂Θ = T`, tame (`hloc`), of dimension `m + 1`, `m ≥ 1`, and `ω ∈ Ωᵐ_{ep,∞}(X)`:
`∫_Θ̂ dω = ∫_{∂S} ω dμ^{∂Θ̂} = μ^{∂Θ̂}_ω(∂S)`. -/
theorem theorem_9_5_17 (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
        (A.epFormsInftyD m ω) =
      A.boundaryMeasure hm hΘ hcpt hT hloc ω univ :=
  A.theorem_9_5_17_msheets hm hPU hΘ hcpt hT (A.hcovS_of_loc hm hΘ hcpt hloc) ω

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450 (2017: Theorem 9.7)**, with the text's
hypotheses: as Theorem 9.5.17 for `X` with the local unique continuation property,
`∮_Θ̂ dω = ∮_{∂S} ω dμ^{∂Θ̂} = μ^{∂Θ̂,eff}_ω(∂S)`. -/
theorem theorem_9_5_18 (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
        (A.hloc_hasLUC hLUC hloc) (A.epFormsInftyD m ω) =
      A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω univ :=
  A.theorem_9_5_18_msheets hm hPU hΘ hcpt hT (A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc) ω

end EP

end Polyfold
