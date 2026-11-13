import Polyfold.Chapter11.BoundaryMeasureGeneralizedIso
import Polyfold.Chapter9.StokesTextHypotheses

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorems 11.4.4 and 11.4.5** (p. 545, new in the 2021 edition),
gap G.131, row V11.29.  Numbers and pages are the 2021 text's.

# Theorems 11.4.4 and 11.4.5 with the text's hypotheses

H4 proved Theorems 11.4.4 and 11.4.5 for a generalized isomorphism `f : X → Y`
(`EPLoc.theorem_11_4_4_pull`, …, `BoundaryMeasureGeneralizedIso.lean`) under E7's class condition `hcov`
(oriented tame structures at the points of `supp(∂Θ)` whose nonempty boundary sheets lie in
`msheets`).  `BoundaryCover` derives that condition from the text's hypotheses
(`EP.hcov_of_loc`).  Here the four identities are stated with the text's hypotheses only: `Θ̂`
(resp. `Θ̂'`) a compact branched ep⁺-subgroupoid, oriented, tame in the reading `hloc` (an
oriented tame structure of dimension `n = m + 1` describing `T̂Θ` at every point of `supp Θ`;
this also gives the dimension), `m ≥ 1`, and for 11.4.5 `X`, `Y` with the local unique
continuation property.

* `EP.boundaryMeasure_eq`, `EP.boundaryMeasureEff_eq`: the measures of `StokesTextHypotheses` are
  H4's `boundaryMeasure`, `boundaryMeasureEff`;
* **`EPLoc.theorem_11_4_4_pull_loc`**, **`EPLoc.theorem_11_4_4_push_loc`**,
  **`EPLoc.theorem_11_4_5_pull_loc`**, **`EPLoc.theorem_11_4_5_push_loc`**.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EP

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- The boundary measure of Theorem 9.5.15 with the text's hypotheses (`EP.boundaryMeasure`) is
H4's `boundaryMeasure` for E7's class condition derived from `hloc`. -/
theorem boundaryMeasure_eq (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    A.boundaryMeasure hm hΘ hcpt hT hloc =
      A.X.boundaryMeasure (A.epFormsInftyEval m) hm hΘ hcpt (FormEval.isNDimensional_of_loc hloc)
        hT (A.hcov_of_loc hm hΘ hcpt hloc) :=
  rfl

/-- The effective boundary measure of Theorem 9.5.16 with the text's hypotheses
(`EP.boundaryMeasureEff`) is H4's `boundaryMeasureEff`. -/
theorem boundaryMeasureEff_eq (hm : 0 < m) (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T) :
    A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc =
      A.X.boundaryMeasureEff (A.epFormsInftyEval m) hm hΘ hcpt
        (FormEval.isNDimensional_of_loc hloc) hT (A.hcov_of_loc_isLUC hm hLUC hΘ hcpt hloc) :=
  rfl

end EP

namespace EPLocalization

open EpFunctor CategoryTheory

namespace EPLoc

variable {X Y : EP.{u}} {m : ℕ}

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), second identity**, with the text's
hypotheses: for a generalized isomorphism `f : X → Y` and `Θ̂'` on `Y` compact, branched,
oriented, tame (`hloc'`), of dimension `n = m + 1 ≥ 2`, and `K ∈ L(|supp ∂f^*Θ'|)`:
`|f|(K) ∈ L(|supp ∂Θ'|)` and `µ^{∂f^*Θ̂'}_{f^*ω'}(K) = µ^{∂Θ̂'}_{ω'}(|f|(K))`. -/
theorem theorem_11_4_4_pull_loc {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y, D.Represents T')
    (ω' : Y.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasure (X.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isNDimensional_dPullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial
            (FormEval.isNDimensional_of_loc hloc'))
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ'
            (hasIndependentTangentSums (X := Y.X) Θ') hT')
          ((rep f).hcovB_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ' hT'
            (Y.hcov_of_loc hm hΘ' hcpt' hloc'))
          (formsPullback f m ω') K =
        Y.boundaryMeasure hm hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) :=
  theorem_11_4_4_pull hf hm hΘ' hcpt' (FormEval.isNDimensional_of_loc hloc') hT'
    (Y.hcov_of_loc hm hΘ' hcpt' hloc') ω' hK

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), first identity**, with the text's
hypotheses: for a generalized isomorphism `f : X → Y` and `Θ̂` on `X` compact, branched,
oriented, tame (`hloc`), of dimension `n = m + 1 ≥ 2`, and `K ∈ L(|supp ∂Θ|)`:
`|f|(K) ∈ L(|supp ∂f_*Θ|)` and `µ^{∂Θ̂}_ω(K) = µ^{∂f_*Θ̂}_{f_*ω}(|f|(K))` (`f_*` computed on the
representative `rep f`). -/
theorem theorem_11_4_4_push_loc {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : X.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.boundaryMeasure hm hΘ hcpt hT hloc ω K =
        Y.X.boundaryMeasure (Y.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isNDimensional_dPushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial
            (FormEval.isNDimensional_of_loc hloc))
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ
            (hasIndependentTangentSums (X := X.X) Θ) hT)
          ((rep f).hcovB_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ hT
            (X.hcov_of_loc hm hΘ hcpt hloc))
          ((rep f).formsPush (isEquivalence_rep_Φ hf) m ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) :=
  theorem_11_4_4_push hf hm hΘ hcpt (FormEval.isNDimensional_of_loc hloc) hT
    (X.hcov_of_loc hm hΘ hcpt hloc) ω hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), second identity**, with the text's
hypotheses: as `theorem_11_4_4_pull_loc` for the effective boundary measures of Theorem 9.5.16,
`X` and `Y` having the local unique continuation property. -/
theorem theorem_11_4_5_pull_loc {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (m + 1) Θ' y, D.Represents T')
    (ω' : Y.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) (pullTheta f Θ')] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) Θ']
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.X.boundaryMeasureEff (X.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pullTheta (isEquivalence_rep_Φ hf) hΘ')
          ((rep f).isCompactBranched_pullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial hcpt')
          ((rep f).isNDimensional_dPullTheta (isEquivalence_rep_Φ hf) hΘ'.isFunctorial
            (FormEval.isNDimensional_of_loc hloc'))
          ((rep f).isOrientation_dPullSection (isEquivalence_rep_Φ hf) hΘ'
            (hasIndependentTangentSums (X := Y.X) Θ') hT')
          (hcovB_addLUC hLX ((rep f).hcovB_pullTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ' hT'
            (Y.hcov_of_loc hm hΘ' hcpt' hloc')))
          (formsPullback f m ω') K =
        Y.boundaryMeasureEff hm hLY hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) :=
  theorem_11_4_5_pull hf hm hLX hLY hΘ' hcpt' (FormEval.isNDimensional_of_loc hloc') hT'
    (Y.hcov_of_loc_isLUC hm hLY hΘ' hcpt' hloc') ω' hK

/-- **Theorem 11.4.5, 2021 p. 545 (new in the 2021 edition), first identity**, with the text's
hypotheses: as `theorem_11_4_4_push_loc` for the effective boundary measures of Theorem 9.5.16,
`X` and `Y` having the local unique continuation property. -/
theorem theorem_11_4_5_push_loc {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    {Θ : X.Obj → ℚ} {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hΘ : X.X.IsBranchedEpSubgroupoid Θ) (hcpt : X.X.IsCompactBranched Θ)
    (hT : X.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : X.epFormsInfty m) {K : Set (X.X.orbitSupp (X.X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    MeasurableSet[Y.X.lebesgueSigmaBoundaryH (m + 1) (pushTheta f Θ)]
        (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) ∧
      X.boundaryMeasureEff hm hLX hΘ hcpt hT hloc ω K =
        Y.X.boundaryMeasureEff (Y.epFormsInftyEval m) hm
          ((rep f).isBranchedEpSubgroupoid_pushTheta (isEquivalence_rep_Φ hf) hΘ)
          ((rep f).isCompactBranched_pushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial hcpt)
          ((rep f).isNDimensional_dPushTheta (isEquivalence_rep_Φ hf) hΘ.isFunctorial
            (FormEval.isNDimensional_of_loc hloc))
          ((rep f).isOrientation_dPushSection (isEquivalence_rep_Φ hf) hΘ
            (hasIndependentTangentSums (X := X.X) Θ) hT)
          (hcovB_addLUC hLY ((rep f).hcovB_pushTheta (isEquivalence_rep_Φ hf)
            (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F m)
            (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) m) hΘ hT
            (X.hcov_of_loc hm hΘ hcpt hloc)))
          ((rep f).formsPush (isEquivalence_rep_Φ hf) m ω)
          (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val '' K))) :=
  theorem_11_4_5_push hf hm hLX hLY hΘ hcpt (FormEval.isNDimensional_of_loc hloc) hT
    (X.hcov_of_loc_isLUC hm hLX hΘ hcpt hloc) ω hK

end EPLoc

end EPLocalization

end Polyfold
