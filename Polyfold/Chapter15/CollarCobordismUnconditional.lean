import Polyfold.Chapter15.CanonicalPerturbationExists
import Polyfold.Chapter9.StokesLocalPartitions
import Polyfold.Chapter9.StokesLocalPartitionsDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.3** and **Corollary 15.4.4** (2017: Theorem 15.7, Corollary 15.2), with Stokes
from Remark 9.5.19 (p. 451).  Numbers and pages are the 2021 text's.

# Theorem 15.4.3 and Corollary 15.4.4 with no sc-smooth partitions of unity

Theorems 9.5.17 and 9.5.18 hold for every ep-groupoid (`EP.theorem_9_5_17_all`,
`EP.theorem_9_5_18_all` and their `n = 1` forms, `Chapter9/StokesLocalPartitions*.lean`).  The
results of §15.4 that assumed sc-smooth partitions of unity only for Stokes are restated here
without them, by the same arguments.

* `theorem_15_4_3_hyp_all`, `theorem_15_4_3_eff_hyp_all`, `theorem_15_4_3_dim1_hyp_all`,
  **`theorem_15_4_3_all`**, `theorem_15_4_3_eff_all`: Theorem 15.4.3 without `hPU`.
* `OrientedRegularPerturbation.HasOrientedCobordism_all`, `HasOrientedCobordismEff_all`: the
  oriented compact cobordisms of the proof of Corollary 15.4.4, with no partitions of unity on
  the cobordism; `HasOrientedCobordism.to_all`, `HasOrientedCobordismEff.to_all`.
* `corollary_15_4_4_hyp_all`, `corollary_15_4_4_eff_hyp_all`, `corollary_15_4_4_canonical_all`:
  Corollary 15.4.4 from these cobordisms, with no partitions of unity on `X`.
* **`corollary_15_4_4_collar_all`**, `corollary_15_4_4_eff_collar_all`,
  **`corollary_15_4_4_oriented_collar_all`**, `corollary_15_4_4_eff_oriented_collar_all`,
  **`corollary_15_4_4_wellDefined_all`**: Corollary 15.4.4 along the collar extension, with
  sc-smooth bump functions on `X` in place of partitions of unity on `X` and on `[0, 1] × X`.

## Reading

In `corollary_15_4_4_collar` the partitions of unity on `X` had a second use: they gave the
sc-smooth bump functions of the collar construction (`corollary_15_3_10_3_collar`) and of
Theorem 15.4.1.  That use is kept, as the hypothesis `hbump` (Theorem 7.5.7 and Theorem 12.3.2 (1)
give it from partitions of unity).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open EpGroupoid

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, for `n = 1`, for `X` with (LUC)**, with no
sc-smooth partitions of unity on `X` (Remark 9.5.19, p. 451). -/
theorem theorem_9_5_18_dim1_isLUC_all (A : EP.{u}) {Θ : A.Obj → ℚ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ hcpt hT
        (A.hloc_hasLUC_dim1 hLUC hloc) (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc) ω univ :=
  A.theorem_9_5_18_dim1_all hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc) ω

end EP

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}}

/-! ### Theorem 15.4.3 -/

/-- **Theorem 15.4.3, 2021 p. 702 (2017: Theorem 15.7), with no sc-smooth partitions of unity**:
`theorem_15_4_3_hyp` without `hPU`; Stokes is `EP.theorem_9_5_17_all`. -/
theorem theorem_15_4_3_hyp_all {m : ℕ} (hm : 0 < m)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T)
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure (m + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
            (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hT hloc ω univ := by
  obtain ⟨hΘ, hcpt⟩ := theorem_15_4_3_isBranched_hyp hf hft hcc hΛ hdom hN1 htr hgood
  exact ⟨hΘ, hcpt, fun hΘ hcpt ω => A.baseEP.theorem_9_5_17_all hm hΘ hcpt hT hloc ω⟩

/-- **Theorem 15.4.3, effective version, 2021 p. 703, with no sc-smooth partitions of unity**:
`theorem_15_4_3_eff_hyp` without `hPU`. -/
theorem theorem_15_4_3_eff_hyp_all {m : ℕ} (hm : 0 < m)
    (hLUC : A.X.IsLUC) {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T)
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure (m + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
            (A.baseEP.hloc_hasLUC hLUC hloc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω univ := by
  obtain ⟨hΘ, hcpt⟩ := theorem_15_4_3_isBranched_hyp hf hft hcc hΛ hdom hN1 htr hgood
  exact ⟨hΘ, hcpt, fun hΘ hcpt ω => A.baseEP.theorem_9_5_18_all hm hLUC hΘ hcpt hT hloc ω⟩

/-- **Theorem 15.4.3 for index `1`, 2021 p. 702, with no sc-smooth partitions of unity**:
`theorem_15_4_3_dim1_hyp` without `hPU`. -/
theorem theorem_15_4_3_dim1_hyp_all
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hdom : domSupp Λ ⊆ U) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hT : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T)
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure (0 + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty 0),
        (A.baseEP.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
            (A.baseEP.epFormsInftyD 0 ω) =
          A.baseEP.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω univ := by
  obtain ⟨hΘ, hcpt⟩ := theorem_15_4_3_isBranched_hyp hf hft hcc hΛ hdom hN1 htr hgood
  exact ⟨hΘ, hcpt, fun hΘ hcpt ω => A.baseEP.theorem_9_5_17_dim1_all hΘ hcpt hT hloc ω⟩

section TheoremCanonical

variable {f : A.Obj → A.W} {Λ : A.W → ℚ≥0}

/-- **Theorem 15.4.3, 2021 p. 702 (2017: Theorem 15.7), with the canonical orientation and no
sc-smooth partitions of unity**: `theorem_15_4_3` without `hPU`.  `X` tame with sc-smooth bump
functions (Theorem 15.4.1), (1)–(3) of the text: `Θ = Λ ∘ f` is a compact branched
ep⁺-subgroupoid, `canonicalOrientation` is its canonical orientation, and
`∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`. -/
theorem theorem_15_4_3_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ := by
  have hcan := theorem_15_4_1 hX hbump hF hft hΛ hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hΛ htr hgood) hidx
  exact ⟨hcan, theorem_15_4_3_hyp_all hm hF hft hcc hΛ hdom hN1 htr hgood hcan.1 hcan.loc⟩

/-- **Theorem 15.4.3, effective version, 2021 p. 703, with the canonical orientation and no
sc-smooth partitions of unity**: `theorem_15_4_3_eff` without `hPU`. -/
theorem theorem_15_4_3_eff_all {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hLUC : A.X.IsLUC) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt
            hcan.1 (A.baseEP.hloc_hasLUC hLUC hcan.loc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hcan.1 hcan.loc ω univ := by
  have hcan := theorem_15_4_1 hX hbump hF hft hΛ hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hΛ htr hgood) hidx
  exact ⟨hcan, (theorem_15_4_3_eff_hyp_all hm hLUC hF hft hcc hΛ hdom hN1 htr hgood hcan.1
    hcan.loc).2.2⟩

end TheoremCanonical

/-! ### The cobordism argument of Corollary 15.4.4 -/

/-- **The integral of an exact form vanishes when `d_X ≡ 0`** (Corollary 15.4.4, 2021 p. 703),
`m ≥ 1`, with no sc-smooth partitions of unity: `integral_d_eq_zero_of_degIndex_eq_zero` without
`hPU`. -/
theorem integral_d_eq_zero_of_degIndex_eq_zero_all {B : EP.{u}} {m : ℕ} (hm : 0 < m)
    (hd : ∀ x, B.X.PObj.degIndex x = 0) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (η : B.epFormsInfty m) :
    (B.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
      (B.epFormsInftyD m η) = 0 := by
  rw [B.theorem_9_5_17_all hm hΘ hcpt hT hloc η]
  refine boundaryMeasure_univ_eq_zero hm hΘ hcpt hT hloc (fun x hx => ?_) η
  have h1 : 1 ≤ B.X.PObj.degIndex x := hx.1
  rw [hd x] at h1
  exact absurd h1 (by norm_num)

/-- **The integral of an exact form vanishes when `d_X ≡ 0`, dimension `1`** (Corollary 15.4.4,
2021 p. 703), with no sc-smooth partitions of unity. -/
theorem integral_d_eq_zero_of_degIndex_eq_zero_dim1_all {B : EP.{u}}
    (hd : ∀ x, B.X.PObj.degIndex x = 0) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : B.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (η : B.epFormsInfty 0) :
    (B.epFormsInftyEval (0 + 1)).tameBranchedIntegral (Nat.succ_pos 0) hΘ hcpt hT hloc
      (B.epFormsInftyD 0 η) = 0 := by
  rw [B.theorem_9_5_17_dim1_all hΘ hcpt hT hloc η]
  refine signedMeasure_univ_eq_zero_of_boundary (fun x hx => ?_)
    (B.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc η)
  have h1 : 1 ≤ B.X.PObj.degIndex x := hx.1
  rw [hd x] at h1
  exact absurd h1 (by norm_num)

/-- **The cobordism argument of Corollary 15.4.4** (2021 p. 703) with no sc-smooth partitions of
unity on `Y`: `integral_eq_of_cobordism` without `hPU`; Stokes on `Y` is
`EP.theorem_9_5_17_all`. -/
theorem integral_eq_of_cobordism_all {X Y : EP.{u}} (F : EpFunctor Y.X X.X) {m : ℕ}
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty (m + 1) → ℝ)
    (hbd : ∀ ω, Y.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty (m + 1)) (hω : X.epFormsInftyD (m + 1) ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_17_all (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback F (m + 1) ω)
  have hd : Y.epFormsInftyD (m + 1) (EP.epFormsInftyPullback F (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hd, tameBranchedIntegral_zero, hbd] at hS
  linarith

/-- **The effective cobordism argument** (Corollary 15.4.4, effective version, 2021 p. 703) with
no sc-smooth partitions of unity on `Y`: `integralEff_eq_of_cobordism` without `hPU`. -/
theorem integralEff_eq_of_cobordism_all {X Y : EP.{u}} (F : EpFunctor Y.X X.X) {m : ℕ}
    (hLUC : Y.X.IsLUC) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty (m + 1) → ℝ)
    (hbd : ∀ ω, Y.boundaryMeasureEff (Nat.succ_pos m) hLUC hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty (m + 1)) (hω : X.epFormsInftyD (m + 1) ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_18_all (Nat.succ_pos m) hLUC hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback F (m + 1) ω)
  have hd : Y.epFormsInftyD (m + 1) (EP.epFormsInftyPullback F (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hd, tameBranchedIntegralEff_zero, hbd] at hS
  linarith

namespace OrientedRegularPerturbation

variable {f : A.Obj → A.W} {m : ℕ}

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism** (proof of Corollary 15.4.4,
2021 p. 703), with no partitions of unity on the cobordism: `HasOrientedCobordism` without the
field `Y.X.HasScPartitionsOfUnity`. -/
def HasOrientedCobordism_all (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X)
    (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = P₁.integral ω - P₀.integral ω

/-- The effective form of `HasOrientedCobordism_all`: `HasOrientedCobordismEff` without the field
`Y.X.HasScPartitionsOfUnity`. -/
def HasOrientedCobordismEff_all (hLUC : A.X.IsLUC) (P₀ P₁ : OrientedRegularPerturbation A f m) :
    Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X)
    (hLUCY : Y.X.IsLUC) (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasureEff (Nat.succ_pos m) hLUCY hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = P₁.integralEff hLUC ω - P₀.integralEff hLUC ω

/-- A cobordism with partitions of unity on `Y` is one in the sense of
`HasOrientedCobordism_all`. -/
theorem HasOrientedCobordism.to_all {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h : P₀.HasOrientedCobordism P₁) : P₀.HasOrientedCobordism_all P₁ := by
  obtain ⟨Y, F, -, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- The effective form of `HasOrientedCobordism.to_all`. -/
theorem HasOrientedCobordismEff.to_all {hLUC : A.X.IsLUC}
    {P₀ P₁ : OrientedRegularPerturbation A f m} (h : P₀.HasOrientedCobordismEff hLUC P₁) :
    P₀.HasOrientedCobordismEff_all hLUC P₁ := by
  obtain ⟨Y, F, -, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨Y, F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- **Every oriented regular perturbation is cobordant to itself** (`Y = X`, `F = id`, `Θ̃ = 0`),
with no partitions of unity: `hasOrientedCobordism_refl` without `hPU`. -/
theorem hasOrientedCobordism_refl_all (P : OrientedRegularPerturbation A f m) :
    P.HasOrientedCobordism_all P := by
  have hemp : ∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (0 : A.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : A.X.IsCompactBranched (0 : A.Obj → ℚ) := by
    have : A.X.orbitSupp (0 : A.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : A.Obj → ℚ),
      ∃ C : A.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨A.baseEP, EpFunctor.id _, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact boundaryMeasure_univ_eq_zero (B := A.baseEP) (Nat.succ_pos m)
    A.X.isBranchedEpSubgroupoid_zero hcpt0 A.X.isOrientation_zero hloc0 hemp _

/-- The effective form of `hasOrientedCobordism_refl_all`: `hasOrientedCobordismEff_refl`
without `hPU`. -/
theorem hasOrientedCobordismEff_refl_all (hLUC : A.X.IsLUC)
    (P : OrientedRegularPerturbation A f m) : P.HasOrientedCobordismEff_all hLUC P := by
  have hemp : ∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (0 : A.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : A.X.IsCompactBranched (0 : A.Obj → ℚ) := by
    have : A.X.orbitSupp (0 : A.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : A.Obj → ℚ),
      ∃ C : A.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨A.baseEP, EpFunctor.id _, hLUC, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact signedMeasure_univ_eq_zero_of_boundary hemp _

end OrientedRegularPerturbation

/-- **Corollary 15.4.4 from the cobordism, 2021 p. 703, with no sc-smooth partitions of unity**:
`corollary_15_4_4_hyp` without `hPU`, for cobordisms in the sense of
`HasOrientedCobordism_all`. -/
theorem corollary_15_4_4_hyp_all {f : A.Obj → A.W} {m : ℕ}
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hcob : ∀ P₀ P₁, Can P₀ → Can P₁ → P₀.HasOrientedCobordism_all P₁) :
    corollary_15_4_4_statement A f m Can := by
  refine ⟨fun P _ η => ?_, fun P₀ P₁ h₀ h₁ ω hω => ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact integral_d_eq_zero_of_degIndex_eq_zero_dim1_all (B := A.baseEP) hd
        P.isBranched P.isCompact P.isOrientation P.loc η
    · exact integral_d_eq_zero_of_degIndex_eq_zero_all (B := A.baseEP) hm hd
        P.isBranched P.isCompact P.isOrientation P.loc η
  obtain ⟨Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := hcob P₀ P₁ h₀ h₁
  exact integral_eq_of_cobordism_all F hΘ' hcpt' hT' hloc' P₀.integral P₁.integral hbd ω hω

/-- For `d_X ≡ 0` and (LUC), exact forms have effective integral `0` over every oriented regular
perturbation (Corollary 15.4.4, effective version, 2021 p. 703), with no sc-smooth partitions of
unity: `integralEff_d_eq_zero_of_degIndex_eq_zero` without `hPU`. -/
theorem integralEff_d_eq_zero_of_degIndex_eq_zero_all
    (hLUC : A.X.IsLUC) (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedRegularPerturbation A f m) (η : A.baseEP.epFormsInfty m) :
    P.integralEff hLUC (A.baseEP.epFormsInftyD m η) = 0 := by
  have hemp : ∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) :=
    fun x hx => by
      have h1 : 1 ≤ A.X.PObj.degIndex x := hx.1
      rw [hd x] at h1
      exact absurd h1 (by norm_num)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e := A.baseEP.theorem_9_5_18_dim1_isLUC_all hLUC P.isBranched P.isCompact
      P.isOrientation P.loc η
    refine e.trans ?_
    exact signedMeasure_univ_eq_zero_of_boundary hemp _
  · have e := A.baseEP.theorem_9_5_18_all hm hLUC P.isBranched P.isCompact P.isOrientation
      P.loc η
    refine e.trans ?_
    exact signedMeasure_univ_eq_zero_of_boundary hemp _

/-- **Corollary 15.4.4, effective version, from the effective cobordism, 2021 p. 703, with no
sc-smooth partitions of unity**: `corollary_15_4_4_eff_hyp` without `hPU`, for cobordisms in the
sense of `HasOrientedCobordismEff_all`. -/
theorem corollary_15_4_4_eff_hyp_all {f : A.Obj → A.W} {m : ℕ}
    (hLUC : A.X.IsLUC) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hcob : ∀ P₀ P₁, Can P₀ → Can P₁ → P₀.HasOrientedCobordismEff_all hLUC P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can := by
  refine ⟨fun P _ η => integralEff_d_eq_zero_of_degIndex_eq_zero_all hLUC hd P η,
    fun P₀ P₁ h₀ h₁ ω hω => ?_⟩
  obtain ⟨Y, F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := hcob P₀ P₁ h₀ h₁
  exact integralEff_eq_of_cobordism_all F hLUCY hΘ' hcpt' hT' hloc' (P₀.integralEff hLUC)
    (P₁.integralEff hLUC) hbd ω hω

/-- **Step (c) gives the cobordism** (proof of Corollary 15.4.4, 2021 p. 703), with no sc-smooth
partitions of unity on `[0, 1] × X`: `hasOrientedCobordism_of_cylinder` without `hPUC`. -/
theorem hasOrientedCobordism_of_cylinder_all (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} {m : ℕ} {P₀ P₁ : OrientedRegularPerturbation A f m}
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hends : IsCylinderBoundaryOf P₀ P₁ hΘ' hcpt' hT' hloc') :
    P₀.HasOrientedCobordism_all P₁ := by
  refine ⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1, Θ', T', hΘ', hcpt', hT', hloc', fun ω => ?_⟩
  rw [boundaryMeasure_cyl_univ hd (Nat.succ_pos m) hΘ' hcpt' hT' hloc', (hends ω).1,
    (hends ω).2]
  ring

/-- **Step (c), effective form, gives the effective cobordism** (2021 p. 703), with no sc-smooth
partitions of unity on `[0, 1] × X`: `hasOrientedCobordismEff_of_cylinder` without `hPUC`. -/
theorem hasOrientedCobordismEff_of_cylinder_all (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC) {f : A.Obj → A.W} {m : ℕ}
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hends : IsCylinderBoundaryEffOf hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc') :
    P₀.HasOrientedCobordismEff_all hLUC P₁ := by
  refine ⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1, hLUCC, Θ', T', hΘ', hcpt', hT', hloc',
    fun ω => ?_⟩
  rw [boundaryMeasureEff_cyl_univ hd (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc', (hends ω).1,
    (hends ω).2]
  ring

/-- **Corollary 15.4.4, 2021 p. 703 (2017: Corollary 15.2), for the canonical orientation, with
no sc-smooth partitions of unity**: `corollary_15_4_4_canonical` without `hPU`, from cobordisms in
the sense of `HasOrientedCobordism_all`. -/
theorem corollary_15_4_4_canonical_all {f : A.Obj → A.W} {m : ℕ}
    {hF : A.E.IsScFredholmSectionFunctor f} {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy}
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hcob : ∀ P₀ P₁ : OrientedRegularPerturbation A f m, IsCanonicalPerturbation hF.2 hsec o P₀ →
      IsCanonicalPerturbation hF.2 hsec o P₁ → P₀.HasOrientedCobordism_all P₁) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hF.2 hsec o) :=
  corollary_15_4_4_hyp_all hd _ hcob

/-! ### Corollary 15.4.4 along the collar extension -/

variable {f : A.Obj → A.W}

section Collar

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hinvC : (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft)
    hsec' (cubeOrientation hf hft hsec o))
  {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))

include hd ho hinvC hidx in
/-- **The oriented cobordism of Corollary 15.4.4 from the collar extension** (2021 p. 703), with
no sc-smooth partitions of unity on `[0, 1] × X`: `hasOrientedCobordism_collar` without `hPUC`. -/
theorem hasOrientedCobordism_collar_all (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise)
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h₀ : IsCanonicalPerturbation hf.2 hsec o P₀) (h₁ : IsCanonicalPerturbation hf.2 hsec o P₁) :
    P₀.HasOrientedCobordism_all P₁ := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, -, hl₀, hl₁⟩ :=
    exists_collar_local_ends hd hf hft hsec hsec' o ho hinvC hidx hpara hbump h₀ h₁
  exact hasOrientedCobordism_of_cylinder_all hd hΘ' hcpt' hT' hloc'
    (isCylinderBoundaryOf_of_local P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁ hl₀ hl₁)

include hd ho hinvC hidx in
/-- **The effective oriented cobordism from the collar extension** (2021 p. 703), with no
sc-smooth partitions of unity on `[0, 1] × X`: `hasOrientedCobordismEff_collar` without
`hPUC`. -/
theorem hasOrientedCobordismEff_collar_all (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC)
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h₀ : IsCanonicalPerturbation hf.2 hsec o P₀) (h₁ : IsCanonicalPerturbation hf.2 hsec o P₁) :
    P₀.HasOrientedCobordismEff_all hLUC P₁ := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, hl, -, -⟩ :=
    exists_collar_local_ends hd hf hft hsec hsec' o ho hinvC hidx hpara hbump h₀ h₁
  exact hasOrientedCobordismEff_of_cylinder_all hd hLUC hLUCC hΘ' hcpt' hT' hloc'
    (isCylinderBoundaryEffOf_of_local hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁
      (hl hLUC hLUCC).1 (hl hLUC hLUCC).2)

include hd ho hinvC hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) with no sc-smooth partitions of
unity.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth bump functions, and `(f, o)` an
oriented sc-Fredholm section functor with tame germ data and index `m + 1`, with `õ = e ∧ o`
invariant under the morphisms of the cylinder.  Then exact forms integrate to `0` over every
regular perturbation with the canonical orientation of `(f, o)` (Definition 15.4.2), and a closed
form has the same integral over any two of them.  This is `corollary_15_4_4_collar` with the
hypotheses `hPU` (partitions of unity on `X`) and `hPUC` (on `[0, 1] × X`) replaced by `hbump`,
the use of `hPU` other than Stokes. -/
theorem corollary_15_4_4_collar_all (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_hyp_all hd _ fun _ _ h₀ h₁ =>
    hasOrientedCobordism_collar_all hd hf hft hsec hsec' o ho hinvC hidx hpara hbump h₀ h₁

include hd ho hinvC hidx in
/-- **Corollary 15.4.4, effective version (2021 p. 703), with no sc-smooth partitions of unity**:
`corollary_15_4_4_eff_collar` with `hPU`, `hPUC` replaced by `hbump`. -/
theorem corollary_15_4_4_eff_collar_all (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_hyp_all hLUC hd _ fun _ _ h₀ h₁ =>
    hasOrientedCobordismEff_collar_all hd hf hft hsec hsec' o ho hinvC hidx hpara hbump hLUC
      hLUCC h₀ h₁

end Collar

section Oriented

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hinv : A.E.IsOrInvariant hf hsec o)
  {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))

include hd hft hsec' ho hinv hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) for an oriented sc-Fredholm section
functor, with no sc-smooth partitions of unity.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` with
sc-smooth bump functions, and `(f, o)` an oriented sc-Fredholm section functor
(`φ_* o_{s(φ)} = o_{t(φ)}`) with tame germ data and index `m + 1`.  Then exact forms integrate to
`0` over every regular perturbation with the canonical orientation of `(f, o)`, and a closed form
has the same integral over any two of them.  This is `corollary_15_4_4_oriented_collar` with
`hPU` replaced by `hbump` (its use other than Stokes). -/
theorem corollary_15_4_4_oriented_collar_all (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_collar_all hd hf hft hsec hsec' o ho
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hidx hpara hbump

include hd hft hsec' ho hinv hidx in
/-- **Corollary 15.4.4, effective version (2021 p. 703), for an oriented sc-Fredholm section
functor, with no sc-smooth partitions of unity**: `corollary_15_4_4_eff_oriented_collar` with
`hPU` replaced by `hbump`. -/
theorem corollary_15_4_4_eff_oriented_collar_all (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_collar_all hd hf hft hsec hsec' o ho
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hidx hpara hbump hLUC hLUCC

end Oriented

/-- **Corollary 15.4.4, 2021 p. 703, existence and independence, with no sc-smooth partitions of
unity**: for `d_X ≡ 0`, an oriented sc-Fredholm section functor `f` of index `m + 1` with compact
`|S_f|`, paracompact `|X|` and sc-smooth bump functions, canonically oriented regular
perturbations in general position exist, `∫_{Θ} dη = 0` for each of them, and `∫_{Θ} ω` is the
same for any two of them for every closed `ω`.  This is `corollary_15_4_4_wellDefined` with `hPU`
replaced by `hbump` (its use other than Stokes). -/
theorem corollary_15_4_4_wellDefined_all (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hS : A.E.HasCompactSolutionSetEp f) :
    (∃ P : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P ∧ IsInGeneralPosition A f P.Λ) ∧
      corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  ⟨corollary_15_4_4_exists hd hf hft hsec o ho hinv hidx hpara hbump hS,
    corollary_15_4_4_oriented_collar_all hd hf hft hsec hsec' o ho hinv hidx hpara hbump⟩

end SBLocalization

end Polyfold
