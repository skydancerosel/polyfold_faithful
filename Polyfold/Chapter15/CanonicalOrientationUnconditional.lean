import Polyfold.Chapter15.CollarCobordismUnconditional
import Polyfold.Chapter15.CanonicalOrientationOrientedSection
import Polyfold.Chapter15.CanonicalOrientationLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.3** and **Corollary 15.4.4** (2017: Theorem 15.7, Corollary 15.2) for an
orientation in the sense of Definition 12.5.4 (p. 594) and for an orientation made with local
sc⁺-sections, with Stokes from Remark 9.5.19 (p. 451).  Numbers and pages are the 2021 text's.

# The other forms of Theorem 15.4.3 and Corollary 15.4.4 with no partitions of unity

* `theorem_15_4_3_of_definition_12_5_4_all`, `theorem_15_4_3_eff_of_definition_12_5_4_all`,
  `theorem_15_4_3_of_index_on_paths_all`, `theorem_15_4_3_loc_all`, `theorem_15_4_3_eff_loc_all`:
  the forms of Theorem 15.4.3 without `hPU` (used there for Stokes only).
* `corollary_15_4_4_of_definition_12_5_4_all`, `corollary_15_4_4_loc_all`,
  `corollary_15_4_4_eff_loc_all`: Corollary 15.4.4 along the collar extension
  (`corollary_15_4_4_oriented_collar_all`), with sc-smooth bump functions in place of the
  partitions of unity.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0}

/-- **Theorem 15.4.3 (2021 p. 702) for an orientation in the sense of Definition 12.5.4, with no
sc-smooth partitions of unity**: `theorem_15_4_3_of_definition_12_5_4` without `hPU`. -/
theorem theorem_15_4_3_of_definition_12_5_4_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ := by
  obtain ⟨hinv, ho⟩ :=
    (definition_12_5_4_iff_isOrInvariant_isSectionOrientation hX hbump hF hft hsec o).1 hD
  exact theorem_15_4_3_all hm hX hbump hF hft hcc hΛ hdom hN1 htr hgood hsec o hinv ho hidx

/-- **Theorem 15.4.3, effective version (2021 p. 703), for an orientation in the sense of
Definition 12.5.4, with no sc-smooth partitions of unity**:
`theorem_15_4_3_eff_of_definition_12_5_4` without `hPU`. -/
theorem theorem_15_4_3_eff_of_definition_12_5_4_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hLUC : A.X.IsLUC) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt
            hcan.1 (A.baseEP.hloc_hasLUC hLUC hcan.loc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hcan.1 hcan.loc ω univ := by
  obtain ⟨hinv, ho⟩ :=
    (definition_12_5_4_iff_isOrInvariant_isSectionOrientation hX hbump hF hft hsec o).1 hD
  exact theorem_15_4_3_eff_all hm hX hbump hLUC hF hft hcc hΛ hdom hN1 htr hgood hsec o hinv ho
    hidx

/-- **Theorem 15.4.3 (2021 p. 702) with the index given on sc-smooth path components, with no
sc-smooth partitions of unity**: `theorem_15_4_3_of_index_on_paths` without `hPU`. -/
theorem theorem_15_4_3_of_index_on_paths_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    (hidx₀ : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), ∃ φ : (Fin 1 → ℝ) → A.Obj,
      (rnPolyfold 1).IsScSmoothMap A.X.PObj φ ∧ φ 1 = x ∧ A.B.IsIndexAt f (φ 0) (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ :=
  theorem_15_4_3_of_definition_12_5_4_all hm hX hbump hF hft hcc hΛ hdom hN1 htr hgood hsec o
    hD (isIndexAt_supp_of_paths hbump hft hidx₀)

/-- **Theorem 15.4.3 (2021 p. 702) for an orientation made with local sc⁺-sections, with no
sc-smooth partitions of unity**: `theorem_15_4_3_loc` without `hPU`. -/
theorem theorem_15_4_3_loc_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc hX hF hft oL)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec (orOfLoc hF hft hsec oL) (m + 1)
        (canonicalOrientationLoc hF hft hsec oL Λ),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ :=
  theorem_15_4_3_all hm hX hbump hF hft hcc hΛ hdom hN1 htr hgood hsec _
    (isOrInvariant_orOfLoc hX hbump hF hft hsec oL hoL)
    (isSectionOrientation_orOfLoc hX hbump hF hft hsec oL hoL) hidx

/-- **Theorem 15.4.3, effective version (2021 p. 703), for an orientation made with local
sc⁺-sections, with no sc-smooth partitions of unity**: `theorem_15_4_3_eff_loc` without
`hPU`. -/
theorem theorem_15_4_3_eff_loc_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hLUC : A.X.IsLUC) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc hX hF hft oL)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec (orOfLoc hF hft hsec oL) (m + 1)
        (canonicalOrientationLoc hF hft hsec oL Λ),
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt
            hcan.1 (A.baseEP.hloc_hasLUC hLUC hcan.loc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hcan.1 hcan.loc ω univ :=
  theorem_15_4_3_eff_all hm hX hbump hLUC hF hft hcc hΛ hdom hN1 htr hgood hsec _
    (isOrInvariant_orOfLoc hX hbump hF hft hsec oL hoL)
    (isSectionOrientation_orOfLoc hX hbump hF hft hsec oL hoL) hidx

/-- **Corollary 15.4.4 (2021 p. 703) for an orientation in the sense of Definition 12.5.4, with no
sc-smooth partitions of unity**: `corollary_15_4_4_of_definition_12_5_4` without `hPU`, `hPUC`
and `hS`, along the collar extension (`corollary_15_4_4_oriented_collar_all`); the bump
functions `hbump` were already a hypothesis. -/
theorem corollary_15_4_4_of_definition_12_5_4_all
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hdef : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hf hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  exact corollary_15_4_4_oriented_collar_all hd hf hft hsec hsec' o
    ((isSectionOrientation_iff_continuous hX hbump hft hsec o).2 hdef.1) hdef.2 hidx hpara
    (A.X.theorem_12_3_2_1.2 hbump)

/-- **Corollary 15.4.4 (2021 p. 703) for an orientation made with local sc⁺-sections, with no
sc-smooth partitions of unity**: `corollary_15_4_4_loc` with `hPU` replaced by `hbump` (its use
other than Stokes). -/
theorem corollary_15_4_4_loc_all (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc (MPolyfold.isTame_of_degIndex_eq_zero _ hd) hF hft oL)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) :
    corollary_15_4_4_statement A f m
      (IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL)) :=
  corollary_15_4_4_oriented_collar_all hd hF hft hsec hsec' _
    (isSectionOrientation_orOfLoc _ (A.X.theorem_12_3_2_1.1 hbump) hF hft hsec oL hoL)
    (isOrInvariant_orOfLoc _ (A.X.theorem_12_3_2_1.1 hbump) hF hft hsec oL hoL) hidx hpara hbump

/-- **Corollary 15.4.4, effective version (2021 p. 703), for an orientation made with local
sc⁺-sections, with no sc-smooth partitions of unity**: `corollary_15_4_4_eff_loc` with `hPU`
replaced by `hbump`. -/
theorem corollary_15_4_4_eff_loc_all (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc (MPolyfold.isTame_of_degIndex_eq_zero _ hd) hF hft oL)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) :
    corollary_15_4_4_eff_statement A f m hLUC
      (IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL)) :=
  corollary_15_4_4_eff_oriented_collar_all hd hF hft hsec hsec' _
    (isSectionOrientation_orOfLoc _ (A.X.theorem_12_3_2_1.1 hbump) hF hft hsec oL hoL)
    (isOrInvariant_orOfLoc _ (A.X.theorem_12_3_2_1.1 hbump) hF hft hsec oL hoL) hidx hpara hbump
    hLUC hLUCC

end SBLocalization

end Polyfold
