import Polyfold.Chapter16.InvariantUnconditional
import Polyfold.Chapter15.CylinderExtensionBump
import Polyfold.Chapter9.StokesLocalPartitionsDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703
(Corollary 15.4.4) and §16.6, p. 739: **Theorem 16.6.6** (2017: Theorem 16.8) **for Fredholm
index `0`**, with Stokes from Remark 9.5.19 (p. 451).  Numbers and pages are the 2021 text's.

# Theorem 16.6.6 for index `0` with no sc-smooth partitions of unity

Stokes for `n = 1` holds on every ep-groupoid (`EP.theorem_9_5_17_dim1_all`,
`EP.theorem_9_5_18_dim1_all`, `Chapter9/StokesLocalPartitionsDimOne.lean`).  The index-`0`
results that assumed sc-smooth partitions of unity only for Stokes are restated here without them.

* `EP.pointIntegral_eq_of_cobordism_all`, `EP.pointIntegralEff_eq_of_cobordism_all`.
* Model level: `PointPerturbation.HasOrientedCobordism_all`, `HasOrientedCobordismEff_all` (no
  partitions of unity on `Y`), their `refl_all` lemmas, `corollary_15_4_4_index_zero_all`,
  `hasOrientedCobordism_of_isCanonical_all` (the cobordism from the collar extension,
  Corollary 15.3.10 (3)), **`corollary_15_4_4_index_zero_oriented_all`**,
  `corollary_15_4_4_index_zero_wellDefined_all`.
* Polyfold level: `PointSuborbifold.HasCobordism_all`, `HasCobordismEff_all`, the counts
  `count_eq_of_hasCobordism_all`, `IndexZeroInput_all`,
  **`theorem_16_6_6_index_zero_canonical_all`**, `theorem_16_6_6_index_zero_polyfold_canonical_all`,
  `theorem_16_6_6_index_zero_inherited_all`, **`theorem_16_6_6_index_zero_wellDefined_all`**.

## Reading

As in `Chapter16/InvariantUnconditional.lean`, the partitions of unity on `Z` (or on `X`) also gave
sc-smooth bump functions in the model (Theorem 15.4.1, the collar construction, the existence of
regular perturbations, the continuity of `o`).  That use is kept, as `hbump`.  The partitions of
unity on `[0, 1] × X` (`hPUC`, the field `pu`) were used for Stokes and for the construction of
the cobordism by the charged extension; the collar extension (`corollary_15_3_10_3_collar`) needs
neither, nor the compactness of `|S_f|` (it is part of `(Nⁱ, Uⁱ)` controlling compactness).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EP

/-- **The cobordism argument of Corollary 15.4.4 in dimension `0`** (2021 p. 703), with no
sc-smooth partitions of unity on `Y`: `pointIntegral_eq_of_cobordism` without `hPU`; Stokes is
Theorem 9.5.17 for `n = 1`, 2021 p. 449, in the form of Remark 9.5.19
(`theorem_9_5_17_dim1_all`). -/
theorem pointIntegral_eq_of_cobordism_all {X Y : EP.{u}} (F : EpFunctor Y.X X.X)
    {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty 0 → ℝ)
    (hbd : ∀ ω, Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F 0 ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty 0) (hω : X.epFormsInftyD 0 ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_17_dim1_all hΘ' hcpt' hT' hloc' (EP.epFormsInftyPullback F 0 ω)
  have hd : Y.epFormsInftyD 0 (EP.epFormsInftyPullback F 0 ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F 0) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hd, SBLocalization.tameBranchedIntegral_zero, hbd] at hS
  linarith

/-- **The effective cobordism argument in dimension `0`** (2021 p. 703), with no sc-smooth
partitions of unity on `Y`: `pointIntegralEff_eq_of_cobordism` without `hPU`; Stokes is
Theorem 9.5.18 for `n = 1`, 2021 p. 450 (`theorem_9_5_18_dim1_isLUC_all`). -/
theorem pointIntegralEff_eq_of_cobordism_all {X Y : EP.{u}} (F : EpFunctor Y.X X.X)
    (hLUC : Y.X.IsLUC) {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty 0 → ℝ)
    (hbd : ∀ ω, Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUC hloc')
      (EP.epFormsInftyPullback F 0 ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty 0) (hω : X.epFormsInftyD 0 ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_18_dim1_isLUC_all hLUC hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback F 0 ω)
  have hd : Y.epFormsInftyD 0 (EP.epFormsInftyPullback F 0 ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F 0) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  have h0 : (Y.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ' hcpt' hT'
      (Y.hloc_hasLUC_dim1 hLUC hloc') 0 = 0 := by
    simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
      branchedIntegralEff, map_zero]
    rfl
  rw [hd, h0, hbd] at hS
  linarith

end EP

namespace SBLocalization

open StrongBundle StrongRetr Linearization15 SEP UnitCube

variable {A : SEP.{u}}

namespace PointPerturbation

variable {f : A.Obj → A.W}

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism of dimension `1`** (the proof of
Corollary 15.4.4 for index `0`, 2021 p. 703), with no partitions of unity on `Y`:
`HasOrientedCobordism` without the field `Y.X.HasScPartitionsOfUnity`. -/
def HasOrientedCobordism_all (P₀ P₁ : PointPerturbation A f) : Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X)
    (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F 0 ω) univ = P₁.count ω - P₀.count ω

/-- The effective form of `HasOrientedCobordism_all`: `HasOrientedCobordismEff` without the
field `Y.X.HasScPartitionsOfUnity`. -/
def HasOrientedCobordismEff_all (hLUC : A.X.IsLUC) (P₀ P₁ : PointPerturbation A f) : Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X)
    (hLUCY : Y.X.IsLUC) (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUCY hloc')
      (EP.epFormsInftyPullback F 0 ω) univ = P₁.countEff hLUC ω - P₀.countEff hLUC ω

/-- A cobordism with partitions of unity on `Y` is one in the sense of
`HasOrientedCobordism_all`. -/
theorem HasOrientedCobordism.to_all {P₀ P₁ : PointPerturbation A f}
    (h : P₀.HasOrientedCobordism P₁) : P₀.HasOrientedCobordism_all P₁ := by
  obtain ⟨Y, F, -, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- The effective form of `HasOrientedCobordism.to_all`. -/
theorem HasOrientedCobordismEff.to_all {hLUC : A.X.IsLUC} {P₀ P₁ : PointPerturbation A f}
    (h : P₀.HasOrientedCobordismEff hLUC P₁) : P₀.HasOrientedCobordismEff_all hLUC P₁ := by
  obtain ⟨Y, F, -, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨Y, F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

private theorem zero_data_all (m : ℕ) :
    (∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (0 : A.Obj → ℚ)) ∧
      A.X.IsCompactBranched (0 : A.Obj → ℚ) ∧
      ∀ x ∈ EpGroupoid.supp (0 : A.Obj → ℚ),
        ∃ C : A.X.OrientedTameStructure m 0 x, C.Represents fun _ => 0 := by
  refine ⟨fun x hx => lt_irrefl (0 : ℚ) hx.2, ?_, fun x hx => absurd hx (lt_irrefl (0 : ℚ))⟩
  have : A.X.orbitSupp (0 : A.Obj → ℚ) = ∅ := by
    rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
    exact fun x hx => lt_irrefl (0 : ℚ) hx
  rw [IsCompactBranched, this]; exact isCompact_empty

/-- **Every perturbation is cobordant to itself** (`Y = X`, `F = id`, `Θ̃ = 0`), with no
partitions of unity: `hasOrientedCobordism_refl` without `hPU`. -/
theorem hasOrientedCobordism_refl_all (P : PointPerturbation A f) :
    HasOrientedCobordism_all P P := by
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data_all (A := A) (0 + 1)
  refine ⟨A.baseEP, EpFunctor.id _, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact signedMeasure_univ_eq_zero_of_boundary (B := A.baseEP) hemp _

/-- **Every perturbation is cobordant to itself for the effective count**, with no partitions of
unity: `hasOrientedCobordismEff_refl` without `hPU`. -/
theorem hasOrientedCobordismEff_refl_all (hLUC : A.X.IsLUC) (P : PointPerturbation A f) :
    HasOrientedCobordismEff_all hLUC P P := by
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data_all (A := A) (0 + 1)
  refine ⟨A.baseEP, EpFunctor.id _, hLUC, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact signedMeasure_univ_eq_zero_of_boundary (B := A.baseEP) hemp _

end PointPerturbation

/-- **Corollary 15.4.4 for Fredholm index `0`** (2021 p. 703), for cobordisms with no partitions
of unity: `corollary_15_4_4_index_zero` for `HasOrientedCobordism_all`,
`HasOrientedCobordismEff_all`. -/
theorem corollary_15_4_4_index_zero_all {f : A.Obj → A.W} (P₀ P₁ : PointPerturbation A f)
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    (P₀.HasOrientedCobordism_all P₁ → P₀.count ω = P₁.count ω) ∧
      ∀ hLUC : A.X.IsLUC, P₀.HasOrientedCobordismEff_all hLUC P₁ →
        P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  refine ⟨fun h => ?_, fun hLUC h => ?_⟩
  · obtain ⟨Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
    exact EP.pointIntegral_eq_of_cobordism_all F hΘ' hcpt' hT' hloc' P₀.count P₁.count hbd ω hω
  · obtain ⟨Y, F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
    exact EP.pointIntegralEff_eq_of_cobordism_all F hLUCY hΘ' hcpt' hT' hloc'
      (P₀.countEff hLUC) (P₁.countEff hLUC) hbd ω hω

/-! ### The cobordism on the cylinder from the collar extension -/

section Cylinder

open MPolyfold EpGroupoid

variable {f : A.Obj → A.W}
  (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)

include hd hft ho hidx in
/-- **The oriented cobordism between two regular perturbations of dimension `0`** (Corollary
15.4.4 for Fredholm index `0`, 2021 p. 703, with Corollary 15.3.10 (3), p. 699, and Theorem
15.4.1, p. 702), with no sc-smooth partitions of unity: `hasOrientedCobordism_of_isCanonical`
with `Λ̃` the collar extension (`corollary_15_3_10_3_collar`) and `hPU` replaced by `hbump`, its
use other than Stokes.  The hypotheses `hPUC` and `hS` of the original are used only by the
charged extension, and are dropped. -/
theorem hasOrientedCobordism_of_isCanonical_all (hinv : A.E.IsOrInvariant hf hsec o)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (P₀ P₁ : PointPerturbation A f)
    (h₀ : P₀.IsCanonical hf.2 hsec o) (h₁ : P₁.IsCanonical hf.2 hsec o) :
    P₀.HasOrientedCobordism_all P₁ ∧
      ∀ hLUC : A.X.IsLUC, P₀.HasOrientedCobordismEff_all hLUC P₁ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbump' : A.X.PObj.AdmitsBumpFunctions := A.X.theorem_12_3_2_1.1 hbump
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump'
  have hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbumpC
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2
  obtain ⟨Λ', hreg, e0, e1, hΘ', hcpt'⟩ :=
    corollary_15_3_10_3_collar hd hpara hbump hf hft P₀.isRegular P₁.isRegular
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have hcan' := theorem_15_4_1_cylinder_index_zero hd hf hft hsec o ho hidx hbump' hsec'
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hΛ' hreg.2.2.2.2 e0 e1 honto
  have hT' := hcan'.1
  have hloc' := hcan'.loc
  have hK' := hcan'.isKernelCanonical (canonContinuous Λ' hXC hbumpC hftC hsec'
    (cubeOrientation hf hft hsec o) (isSectionOrientation_cubeOrientation hX hbump' hf hft ho))
  have hK₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T :=
    IsCanonicalFor.isKernelCanonical h₀ (canonContinuous P₀.Λ hX hbump' hft hsec o ho)
  have hK₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T :=
    IsCanonicalFor.isKernelCanonical h₁ (canonContinuous P₁.Λ hX hbump' hft hsec o ho)
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have m0 := exists_arePointMatchedAt_of_kernelCanonical hd hbump' hf hft
    (fun x hx => (P₀.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 0) (ε := -1)
    (Or.inl ⟨z0, rfl⟩) e0 hΘ' hK₀ hK'
  have m1 := exists_arePointMatchedAt_of_kernelCanonical hd hbump' hf hft
    (fun x hx => (P₁.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 1) (ε := 1)
    (Or.inr ⟨z1, rfl⟩) e1 hΘ' hK₁ hK'
  have hov0 := fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p
  have hov1 := fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p
  refine ⟨⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1, _, _,
    hΘ', hcpt', hT', hloc', fun ω => ?_⟩, fun hLUC => ⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1,
    isLUC_cubeSEP hLUC, _, _, hΘ', hcpt', hT', hloc', fun ω => ?_⟩⟩
  · have E0 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₀.isBranched P₀.isCompact
      P₀.isOrientation P₀.loc hΘ' hcpt' hT' hloc' (i := 0) (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₁.isBranched P₁.isCompact
      P₁.isOrientation P₁.loc hΘ' hcpt' hT' hloc' (i := 1) (q := fun _ => 1) z1 hov1 m1 ω
    refine (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
      ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
      ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω))).trans ((congrArg₂ (· + ·) E0 E1).trans ?_)
    change -1 * P₀.count ω + 1 * P₁.count ω = _
    ring
  · have E0 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC (isLUC_cubeSEP hLUC)
      P₀.isBranched P₀.isCompact P₀.isOrientation (P₀.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 (isLUC_cubeSEP hLUC) hloc') (i := 0)
      (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC (isLUC_cubeSEP hLUC)
      P₁.isBranched P₁.isCompact P₁.isOrientation (P₁.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 (isLUC_cubeSEP hLUC) hloc') (i := 1)
      (q := fun _ => 1) z1 hov1 m1 ω
    refine (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
      ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
      ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT'
        ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 (isLUC_cubeSEP hLUC) hloc')
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω))).trans ((congrArg₂ (· + ·) E0 E1).trans ?_)
    change -1 * P₀.countEff hLUC ω + 1 * P₁.countEff hLUC ω = _
    ring

include hd hft ho hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) for Fredholm index `0`, with no
sc-smooth partitions of unity.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth bump
functions, and `(f, o)` an oriented sc-Fredholm section functor with tame germ data and index
`0`.  Then a closed `0`-form has the same weighted signed count `∫_{(Λ ∘ f, o)} ω` over any two
regular perturbations with the canonical orientation of `(f, o)` (Definition 15.4.2), and the
same effective count `∮` when `X` has the local unique continuation property.  This is
`corollary_15_4_4_index_zero_oriented` with `hPU` replaced by `hbump`; `hPUC` and `hS` are not
used and are dropped. -/
theorem corollary_15_4_4_index_zero_oriented_all (hinv : A.E.IsOrInvariant hf hsec o)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (P₀ P₁ : PointPerturbation A f)
    (h₀ : P₀.IsCanonical hf.2 hsec o) (h₁ : P₁.IsCanonical hf.2 hsec o)
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    P₀.count ω = P₁.count ω ∧ ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  obtain ⟨h, he⟩ := hasOrientedCobordism_of_isCanonical_all hd hf hft hsec o ho hidx hinv hpara
    hbump P₀ P₁ h₀ h₁
  have key := corollary_15_4_4_index_zero_all P₀ P₁ ω hω
  exact ⟨key.1 h, fun hLUC => key.2 hLUC (he hLUC)⟩

end Cylinder

/-- **Corollary 15.4.4 in index `0`, existence and independence** (2021 pp. 699, 703), with no
sc-smooth partitions of unity: `corollary_15_4_4_index_zero_wellDefined` with `hPU` replaced by
`hbump` (pointwise bump functions on `X`, its use other than Stokes) and `hPUC` dropped. -/
theorem corollary_15_4_4_index_zero_wellDefined_all {f : A.Obj → A.W}
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)
    (hinv : A.E.IsOrInvariant hf hsec o) (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hS : A.E.HasCompactSolutionSetEp f) :
    (∃ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o ∧ IsInGeneralPosition A f P.Λ) ∧
      ∀ P₀ P₁ : PointPerturbation A f, P₀.IsCanonical hf.2 hsec o → P₁.IsCanonical hf.2 hsec o →
        ∀ ω : A.baseEP.epFormsInfty 0, A.baseEP.epFormsInftyD 0 ω = 0 →
          P₀.count ω = P₁.count ω ∧
            ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω :=
  ⟨corollary_15_4_4_index_zero_exists hd hf hft hsec o ho hidx hinv hpara hbump hS,
    fun P₀ P₁ h₀ h₁ ω hω => corollary_15_4_4_index_zero_oriented_all hd hf hft hsec o ho hidx
      hinv hpara hbump P₀ P₁ h₀ h₁ ω hω⟩

end SBLocalization

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

namespace PointSuborbifold

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism of dimension `1`** (the proof of
Corollary 15.4.4 for index `0`, 2021 p. 703, in a model `(X, β) ∈ c`), with no partitions of
unity on `Y`: `HasCobordism` without the field `Y.X.HasScPartitionsOfUnity`. -/
def HasCobordism_all (P₀ P₁ : PointSuborbifold c) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F 0 ω) univ =
        P₁.count (ScForm.mk q hq ω) - P₀.count (ScForm.mk q hq ω)

/-- The effective form of `HasCobordism_all`: `HasCobordismEff` without the field
`Y.X.HasScPartitionsOfUnity`. -/
def HasCobordismEff_all (P₀ P₁ : PointSuborbifold c) : Prop :=
  ∃ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) (Y : EP.{u}) (F : EpFunctor Y.X q.X.X)
    (hLUC : Y.X.IsLUC) (Θ' : Y.Obj → ℚ)
    (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUC hloc')
      (EP.epFormsInftyPullback F 0 ω) univ =
        P₁.countEff (ScForm.mk q hq ω) - P₀.countEff (ScForm.mk q hq ω)

/-- A cobordism with partitions of unity on `Y` is one in the sense of `HasCobordism_all`. -/
theorem HasCobordism.to_all {P₀ P₁ : PointSuborbifold c} (h : HasCobordism P₀ P₁) :
    HasCobordism_all P₀ P₁ := by
  obtain ⟨q, hq, Y, F, -, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨q, hq, Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- The effective form of `HasCobordism.to_all`. -/
theorem HasCobordismEff.to_all {P₀ P₁ : PointSuborbifold c} (h : HasCobordismEff P₀ P₁) :
    HasCobordismEff_all P₀ P₁ := by
  obtain ⟨q, hq, Y, F, -, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  exact ⟨q, hq, Y, F, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩

/-- **Cobordant perturbations have the same counts of closed `0`-forms** (Corollary 15.4.4's
argument, 2021 p. 703, on the polyfold), with no partitions of unity on `Y`:
`count_eq_of_hasCobordism` for `HasCobordism_all`. -/
theorem count_eq_of_hasCobordism_all {P₀ P₁ : PointSuborbifold c} (h : HasCobordism_all P₀ P₁)
    (τ : ScForm c 0) (hτ : ScForm.d τ = 0) : P₀.count τ = P₁.count τ := by
  obtain ⟨q, hq, Y, F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD 0 (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := EP.pointIntegral_eq_of_cobordism_all F hΘ' hcpt' hT' hloc'
    (fun ω => P₀.count (ScForm.mk q hq ω)) (fun ω => P₁.count (ScForm.mk q hq ω)) hbd
    (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

/-- **Cobordant perturbations have the same effective counts of closed `0`-forms** (2021
p. 703), with no partitions of unity on `Y`: `countEff_eq_of_hasCobordismEff` for
`HasCobordismEff_all`. -/
theorem countEff_eq_of_hasCobordismEff_all {P₀ P₁ : PointSuborbifold c}
    (h : HasCobordismEff_all P₀ P₁) (τ : ScForm c 0) (hτ : ScForm.d τ = 0) :
    P₀.countEff τ = P₁.countEff τ := by
  obtain ⟨q, hq, Y, F, hLUC, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  have hω : q.X.epFormsInftyD 0 (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have := EP.pointIntegralEff_eq_of_cobordism_all F hLUC hΘ' hcpt' hT' hloc'
    (fun ω => P₀.countEff (ScForm.mk q hq ω)) (fun ω => P₁.countEff (ScForm.mk q hq ω)) hbd
    (ScForm.toStructure q hq τ) hω
  simpa only [ScForm.mk_toStructure] using this

private theorem zero_data_all (q : PolyfoldStructure Z) :
    (∀ x, x ∉ q.X.X.PObj.boundary ∩ EpGroupoid.supp (0 : q.X.Obj → ℚ)) ∧
      q.X.X.IsCompactBranched (0 : q.X.Obj → ℚ) ∧
      ∀ x ∈ EpGroupoid.supp (0 : q.X.Obj → ℚ),
        ∃ C : q.X.X.OrientedTameStructure (0 + 1) 0 x, C.Represents fun _ => 0 := by
  refine ⟨fun x hx => lt_irrefl (0 : ℚ) hx.2, ?_, fun x hx => absurd hx (lt_irrefl (0 : ℚ))⟩
  have : q.X.X.orbitSupp (0 : q.X.Obj → ℚ) = ∅ := by
    rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
    exact fun x hx => lt_irrefl (0 : ℚ) hx
  rw [IsCompactBranched, this]; exact isCompact_empty

/-- **Every `P` is cobordant to itself** (`Y = X`, `F = id`, `Θ̃ = 0`), with no partitions of
unity: `hasCobordism_refl` without `hPU`. -/
theorem hasCobordism_refl_all (P : PointSuborbifold c) : HasCobordism_all P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data_all q
  refine ⟨q, hq, q.X, EpFunctor.id _, 0, fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero,
    hcpt0, q.X.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary (B := q.X) hemp _

/-- **Every `P` is cobordant to itself for the effective count** (`Y = X` has (LUC) by (ZHOU)),
with no partitions of unity: `hasCobordismEff_refl` without `hPU`. -/
theorem hasCobordismEff_refl_all (P : PointSuborbifold c) : HasCobordismEff_all P P := by
  set q := c.out
  have hq : (⟦q⟧ : PolyfoldClass Z) = c := Quotient.out_eq c
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data_all q
  refine ⟨q, hq, q.X, EpFunctor.id _, q.X.X.proposition_7_4_10_of_isZhou q.isZhou, 0,
    fun _ => 0, q.X.X.isBranchedEpSubgroupoid_zero, hcpt0, q.X.X.isOrientation_zero, hloc0,
    fun ω => ?_⟩
  rw [sub_self]
  exact SBLocalization.signedMeasure_univ_eq_zero_of_boundary (B := q.X) hemp _

end PointSuborbifold

end PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-! ### In the model of the orientation -/

/-- **2021 Theorem 16.6.6, p. 739, for Fredholm index `0`, from the cobordisms in the model of
the orientation**, for cobordisms with no partitions of unity: `theorem_16_6_6_index_zero_of_model`
for `HasOrientedCobordism_all`, `HasOrientedCobordismEff_all`. -/
theorem theorem_16_6_6_index_zero_of_model_all (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop)
    (hcob : c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → ∀ (o : OrientationRep s)
      (P₀ P₁ : PointPerturbation o.a.S.A o.a.F), Can o P₀ → Can o P₁ →
      P₀.HasOrientedCobordism_all P₁ ∧
        P₀.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
          P₁) :
    theorem_16_6_6_index_zero_statement s n U Can := by
  intro hbd hcs _ _ _ o P₀ P₁ h₀ h₁ τ hτ
  obtain ⟨h, he⟩ := hcob hbd hcs o P₀ P₁ h₀ h₁
  set q := o.a.S.toPolyfoldStructure
  have hq : (⟦q⟧ : PolyfoldClass Z) = c.polyfold := toPolyfoldStructure_mem o.a.hS
  have hω : q.X.epFormsInftyD 0 (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have key := corollary_15_4_4_index_zero_all P₀ P₁ (ScForm.toStructure q hq τ) hω
  exact ⟨key.1 h, key.2 _ he⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_index_zero_of_model_all` are satisfiable** for
the predicate that singles out one perturbation, with no hypothesis on `Z`:
`theorem_16_6_6_index_zero_hcob_witness` without `hPU`. -/
theorem theorem_16_6_6_index_zero_hcob_witness_all {s : FredholmSection c} (o : OrientationRep s)
    (P : PointPerturbation o.a.S.A o.a.F) :
    P.HasOrientedCobordism_all P ∧
      P.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P :=
  ⟨PointPerturbation.hasOrientedCobordism_refl_all P,
    PointPerturbation.hasOrientedCobordismEff_refl_all _ P⟩

/-! ### On the polyfold -/

/-- **2021 Theorem 16.6.6, p. 739, for index `0` on the polyfold, from the cobordisms**, for
cobordisms with no partitions of unity: `theorem_16_6_6_index_zero_polyfold_hyp` for
`HasCobordism_all`, `HasCobordismEff_all`. -/
theorem theorem_16_6_6_index_zero_polyfold_hyp_all (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (IsInherited : OrientationRep s → PointOrientedPerturbation s.1 → Prop)
    (hcob : ∀ o P₀ P₁, P₀.IsAdmissible n U → IsInherited o P₀ → P₁.IsAdmissible n U →
      IsInherited o P₁ →
      P₀.toPointSuborbifold.HasCobordism_all P₁.toPointSuborbifold ∧
        P₀.toPointSuborbifold.HasCobordismEff_all P₁.toPointSuborbifold) :
    theorem_16_6_6_index_zero_polyfold_statement s n U IsInherited := by
  intro _ _ _ _ _ o P₀ P₁ h₀ i₀ h₁ i₁ τ hτ
  obtain ⟨h, he⟩ := hcob o P₀ P₁ h₀ i₀ h₁ i₁
  exact ⟨PointSuborbifold.count_eq_of_hasCobordism_all h τ hτ,
    PointSuborbifold.countEff_eq_of_hasCobordismEff_all he τ hτ⟩

section Models

variable {a : SectionRep c}

/-- **A cobordism in the model is a cobordism on the polyfold**, with no partitions of unity:
`hasCobordism_pointSuborbifold` for `HasOrientedCobordism_all`, `HasCobordism_all`. -/
theorem hasCobordism_pointSuborbifold_all {P₀ P₁ : PointPerturbation a.S.A a.F}
    (h : P₀.HasOrientedCobordism_all P₁) :
    (pointSuborbifold a P₀).HasCobordism_all (pointSuborbifold a P₁) := by
  obtain ⟨Y', F, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, Θ', T', hΘ', hcpt',
    hT', hloc', fun ω => ?_⟩
  rw [count_pointSuborbifold, count_pointSuborbifold]
  convert hbd ω using 3 <;> first | rfl | (congr 1; exact ScForm.toStructure_mk _ _ ω)

/-- **An effective cobordism in the model is one on the polyfold**, with no partitions of
unity: `hasCobordismEff_pointSuborbifold` for the `_all` predicates. -/
theorem hasCobordismEff_pointSuborbifold_all {P₀ P₁ : PointPerturbation a.S.A a.F}
    (h : P₀.HasOrientedCobordismEff_all (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou) P₁) :
    (pointSuborbifold a P₀).HasCobordismEff_all (pointSuborbifold a P₁) := by
  obtain ⟨Y', F, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
  refine ⟨a.S.toPolyfoldStructure, toPolyfoldStructure_mem a.hS, Y', F, hLUCY, Θ', T', hΘ',
    hcpt', hT', hloc', fun ω => ?_⟩
  rw [countEff_pointSuborbifold, countEff_pointSuborbifold]
  convert hbd ω using 3 <;> first | rfl | (congr 1; exact ScForm.toStructure_mk _ _ ω)

end Models

/-- **2021 Theorem 16.6.6, p. 739, for index `0` on the polyfold, from the cobordisms in the
model of the orientation**, for cobordisms with no partitions of unity:
`theorem_16_6_6_index_zero_polyfold_of_model` for the `_all` predicates. -/
theorem theorem_16_6_6_index_zero_polyfold_of_model_all (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop)
    (hcob : c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → ∀ (o : OrientationRep s)
      (P₀ P₁ : PointPerturbation o.a.S.A o.a.F), Can o P₀ → Can o P₁ →
      P₀.HasOrientedCobordism_all P₁ ∧
        P₀.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
          P₁) :
    theorem_16_6_6_index_zero_polyfold_statement s n U (IsInheritedFromPoint Can) := by
  rintro hbd hcs - - - o P₀ P₁ - ⟨M₀, c₀, rfl⟩ - ⟨M₁, c₁, rfl⟩ τ hτ
  obtain ⟨h, he⟩ := hcob hbd hcs o _ _ c₀ c₁
  exact ⟨PointSuborbifold.count_eq_of_hasCobordism_all (hasCobordism_pointSuborbifold_all h) τ hτ,
    PointSuborbifold.countEff_eq_of_hasCobordismEff_all
      (hasCobordismEff_pointSuborbifold_all he) τ hτ⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_index_zero_polyfold_hyp_all` are satisfiable**
for the predicate that singles out one perturbation, with no hypothesis on `Z`:
`theorem_16_6_6_index_zero_polyfold_hcob_witness` without `hPU`. -/
theorem theorem_16_6_6_index_zero_polyfold_hcob_witness_all {s : FredholmSection c}
    (P : PointOrientedPerturbation s.1) (n : Y → ℝ) (U : Set Z) :
    ∀ (o : OrientationRep s) (P₀ P₁ : PointOrientedPerturbation s.1), P₀.IsAdmissible n U →
      (fun _ Q => Q = P) o P₀ → P₁.IsAdmissible n U → (fun _ Q => Q = P) o P₁ →
      P₀.toPointSuborbifold.HasCobordism_all P₁.toPointSuborbifold ∧
        P₀.toPointSuborbifold.HasCobordismEff_all P₁.toPointSuborbifold := by
  rintro o P₀ P₁ - rfl - rfl
  exact ⟨PointSuborbifold.hasCobordism_refl_all _, PointSuborbifold.hasCobordismEff_refl_all _⟩

/-! ### The canonical orientation -/

/-- **The standing hypotheses of Theorem 16.6.6 for index `0` in the model of an orientation
`o`** (2021 p. 739), with no partitions of unity: `IndexZeroInput o` without the field `pu`.
Tame germ data of the representative `F`, `o` an orientation of `F` in the sense of Definition
6.6.16, and Fredholm index `0` at every smooth point. -/
structure IndexZeroInput_all {s : FredholmSection c} (o : OrientationRep s) : Prop where
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  orient : haveI := paracompactSpace_rn_prod o.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback o.a.S.A.B
    IsSectionOrientation o.a.F o.hF.2 o.o
  index : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x 0

/-- `IndexZeroInput` gives `IndexZeroInput_all`. -/
theorem IndexZeroInput.to_all {s : FredholmSection c} {o : OrientationRep s}
    (H : IndexZeroInput o) : IndexZeroInput_all o :=
  ⟨H.tame, H.orient, H.index⟩

/-- **The cobordisms of Theorem 16.6.6 for index `0` in the model of `o`** (2021 pp. 699, 703),
from the collar extension: for `∂Z = ∅` and `Z` with sc-smooth bump functions, any two regular
perturbations of dimension `0` with the canonical orientation of `(F, o)` are joined by an
oriented compact cobordism of dimension `1` and by an effective one.  This is
`hasOrientedCobordism_of_indexZeroInput` with `hPU` replaced by `hbump` (its use other than
Stokes) and `IndexZeroInput` by `IndexZeroInput_all`; the compactness of the solution set (`hcs`)
is not used and is dropped. -/
theorem hasOrientedCobordism_of_indexZeroInput_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c}
    {o : OrientationRep s} (H : IndexZeroInput_all o) (P₀ P₁ : PointPerturbation o.a.S.A o.a.F)
    (h₀ : P₀.IsCanonical o.hF.2 o.hsec o.o) (h₁ : P₁.IsCanonical o.hF.2 o.hsec o.o) :
    P₀.HasOrientedCobordism_all P₁ ∧
      P₀.HasOrientedCobordismEff_all (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
        P₁ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hbumpq : o.a.S.A.X.PObj.AdmitsBumpFunctions :=
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)
  obtain ⟨h, he⟩ := hasOrientedCobordism_of_isCanonical_all hd o.hF H.tame o.hsec o.o H.orient
    H.index o.isOrientation.2 o.a.S.paracompact (o.a.S.A.X.theorem_12_3_2_1.2 hbumpq) P₀ P₁ h₀ h₁
  exact ⟨h, he _⟩

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, in the model of the orientation** (p. 739;
2017: Theorem 16.8), with no sc-smooth partitions of unity: if `Z` admits sc-smooth bump
functions and the standing hypotheses hold in the model of every orientation, then for `∂Z = ∅`
and `f` oriented with compact solution set the counts `∫`, `∮` of a closed sc-differential
`0`-form over two regular perturbations of dimension `0` with the canonical orientation
(Definition 15.4.2) agree.  This is `theorem_16_6_6_index_zero_canonical` with `hPU` replaced by
`hbump` and `IndexZeroInput` by `IndexZeroInput_all`. -/
theorem theorem_16_6_6_index_zero_canonical_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (H : ∀ o : OrientationRep s, IndexZeroInput_all o) :
    theorem_16_6_6_index_zero_statement s n U
      (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_of_model_all s n U _ fun hbd _ o P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput_all hbump hbd (H o) P₀ P₁ h₀ h₁

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, on the polyfold** (p. 739; 2017: Theorem
16.8), with no sc-smooth partitions of unity: under the hypotheses of
`theorem_16_6_6_index_zero_canonical_all`, a closed `0`-form `τ` on `Z` has the same count
`∫_θ̂ τ` and the same effective count `∮_θ̂ τ` over any two admissible perturbed solution sets of
dimension `0` with the orientation inherited from `(f, o)`.  This is
`theorem_16_6_6_index_zero_polyfold_canonical` with `hPU` replaced by `hbump`. -/
theorem theorem_16_6_6_index_zero_polyfold_canonical_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (H : ∀ o : OrientationRep s, IndexZeroInput_all o) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (IsInheritedFromPoint fun o P => P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_polyfold_of_model_all s n U _ fun hbd _ o P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput_all hbump hbd (H o) P₀ P₁ h₀ h₁

/-- **`IndexZeroInput_all` from the standing hypotheses** (2021 p. 739): for `∂Z = ∅` and `Z`
with sc-smooth bump functions, the field `orient` follows from Definition 16.6.5.  This is
`indexZeroInput_of_canonicalInput` with `hPU` replaced by `hbump` and `CanonicalInput` by
`CanonicalInput_all`. -/
theorem indexZeroInput_of_canonicalInput_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {o : OrientationRep s}
    (H : CanonicalInput_all o 0) : IndexZeroInput_all o :=
  ⟨H.tame, o.isSectionOrientation_of_boundary_eq_empty_all hbump hbd H.tame,
    fun x hx => by exact_mod_cast H.index x hx⟩

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, for every orientation with the standing
hypotheses in its model** (p. 739), with no sc-smooth partitions of unity:
`theorem_16_6_6_index_zero_canonical_input` with `hPU` replaced by `hbump` and `CanonicalInput`
by `CanonicalInput_all`. -/
theorem theorem_16_6_6_index_zero_canonical_input_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) :
    theorem_16_6_6_index_zero_statement s n U
      (fun o P => CanonicalInput_all o 0 ∧ P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_of_model_all s n U _ fun hbd _ _ P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput_all hbump hbd
      (indexZeroInput_of_canonicalInput_all hbump hbd h₀.1) P₀ P₁ h₀.2 h₁.2

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, on the polyfold, for every orientation with the
standing hypotheses in its model** (p. 739), with no sc-smooth partitions of unity: the polyfold
form of `theorem_16_6_6_index_zero_canonical_input_all`. -/
theorem theorem_16_6_6_index_zero_polyfold_canonical_input_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (IsInheritedFromPoint fun o P => CanonicalInput_all o 0 ∧ P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_polyfold_of_model_all s n U _ fun hbd _ _ P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput_all hbump hbd
      (indexZeroInput_of_canonicalInput_all hbump hbd h₀.1) P₀ P₁ h₀.2 h₁.2

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, in the model of the orientation** (p. 739),
with no sc-smooth partitions of unity: `theorem_16_6_6_index_zero_inherited` with `hPU` replaced
by `hbump` and `CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_index_zero_inherited_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (H : ∀ o : OrientationRep s, CanonicalInput_all o 0) :
    theorem_16_6_6_index_zero_statement s n U
      (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) := by
  intro hbd
  exact theorem_16_6_6_index_zero_canonical_all hbump s n U
    (fun o => indexZeroInput_of_canonicalInput_all hbump hbd (H o)) hbd

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, on the polyfold** (p. 739), with no sc-smooth
partitions of unity: `theorem_16_6_6_index_zero_polyfold_inherited` with `hPU` replaced by
`hbump` and `CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_index_zero_polyfold_inherited_all
    (hbump : c.polyfold.AdmitsBumpFunctions) (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (H : ∀ o : OrientationRep s, CanonicalInput_all o 0) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (IsInheritedFromPoint fun o P => P.IsCanonical o.hF.2 o.hsec o.o) := by
  intro hbd
  exact theorem_16_6_6_index_zero_polyfold_canonical_all hbump s n U
    (fun o => indexZeroInput_of_canonicalInput_all hbump hbd (H o)) hbd

/-! ### Existence and independence -/

/-- **2021 Theorem 16.6.6, p. 739, in index `0`, the admissible perturbations exist**, from
sc-smooth bump functions on `Z`: `theorem_16_6_6_index_zero_exists` with `hPU` replaced by
`hbump` and `CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_index_zero_exists_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalInput_all o 0) :
    ∃ Q : PointOrientedPerturbation s.1, Q.IsAdmissible n U ∧
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q := by
  obtain ⟨Λ, hreg, hgp⟩ := o.exists_isRegularPerturbation_all hbump hbd hcs hn hU hcc H.tame
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbumpq : o.a.S.A.X.PObj.AdmitsBumpFunctions :=
    (c.polyfold.definition_16_1_5_one).1 hbump o.a.S.toPolyfoldStructure
      (toPolyfoldStructure_mem o.a.hS)
  have ho := o.isSectionOrientation_of_boundary_eq_empty_all hbump hbd H.tame
  have hgood : ∀ x ∈ o.a.S.A.X.PObj.boundary, 0 < Λ (o.a.F x) →
      SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x _ hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hreg.2.1.1 hgp hpos
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (0 : ℕ) := fun x hx => by
    exact_mod_cast H.index x (mem_smoothSet_of_pos H.tame hreg.2.1.1 (by exact_mod_cast hx))
  set P := PointPerturbation.canonical hX hbumpq o.hF H.tame o.hsec o.o o.isOrientation.2 ho
    hreg hgood hidx
  refine ⟨toPointOrientedPerturbation o.a P o.ha,
    ⟨isControlledBy_of_isRegularPerturbation o.a hreg.2.1.1 (fun x => (hreg.2.2.2.1 x).le)
      hreg.2.2.1, o.a, Λ, hreg.2.1.1, o.ha, rfl, hgp⟩, P, ?_, rfl⟩
  exact PointPerturbation.isCanonical_canonical hX hbumpq o.hF H.tame o.hsec o.o
    o.isOrientation.2 ho hreg hgood hidx

/-- **2021 Theorem 16.6.6, p. 739, in index `0`, existence and independence**, with no sc-smooth
partitions of unity: admissible perturbed solution sets with the signs inherited from `(f, o)`
exist, and a closed `0`-form `τ` has the same weighted signed counts (and effective counts) for
any two of them.  This is `theorem_16_6_6_index_zero_wellDefined` with `hPU` replaced by `hbump`
and `CanonicalInput` by `CanonicalInput_all`. -/
theorem theorem_16_6_6_index_zero_wellDefined_all (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalInput_all o 0) :
    (∃ Q : PointOrientedPerturbation s.1, Q.IsAdmissible n U ∧
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q) ∧
    ∀ Q₀ Q₁ : PointOrientedPerturbation s.1, Q₀.IsAdmissible n U →
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q₀ →
      Q₁.IsAdmissible n U →
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q₁ →
      ∀ τ : ScForm c.polyfold 0, ScForm.d τ = 0 →
        Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  refine ⟨theorem_16_6_6_index_zero_exists_all hbump hbd hcs hn hU hcc H,
    fun Q₀ Q₁ h₀ i₀ h₁ i₁ => ?_⟩
  obtain ⟨P₀, c₀, e₀⟩ := i₀
  obtain ⟨P₁, c₁, e₁⟩ := i₁
  exact theorem_16_6_6_index_zero_polyfold_canonical_input_all hbump s n U hbd hcs hn hU hcc o
    Q₀ Q₁ h₀ ⟨P₀, ⟨H, c₀⟩, e₀⟩ h₁ ⟨P₁, ⟨H, c₁⟩, e₁⟩

end StrongPolyfoldBundle

end Polyfold
