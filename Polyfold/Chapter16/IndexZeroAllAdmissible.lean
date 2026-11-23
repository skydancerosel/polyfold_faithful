import Polyfold.Chapter16.InvariantAllAdmissible
import Polyfold.Chapter16.IndexZeroCylinder
import Polyfold.Chapter9.StokesLocalPartitionsDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8) **for Fredholm index `0`**, with Corollary 15.4.4
(p. 703), Theorem 15.4.3 (p. 702) and Stokes from Remark 9.5.19 (p. 451).

# Theorem 16.6.6 for index `0` over all admissible perturbations

## The text, paraphrased

For Fredholm index `0` the perturbed solution set `θ̂ = λ ∘ f` is a finite set of weighted signed
points, and the invariant is the weighted signed count of a closed `0`-form; it does not depend
on the admissible `λ` (controlled by `(n, U)`, `(f, λ)` in general position).

## What is formalized

Namespace `Polyfold.SBLocalization`:
* `PointSolution A f`: an sc⁺-multisection `Λ` with `Θ = Λ ∘ f` compact and branched and an
  orientation `T̂` described by oriented tame structures of dimension `0` (the data of
  `PointPerturbation` without `(N, U)` and the regularity of `Λ`); `count`, `countEff`,
  `PointSolution.ofRegular`.
* **`pointCount_eq_of_isTransversalPerturbation`**: for `d_X ≡ 0`, `|X|` paracompact, bump
  functions and `(f, o)` oriented of index `0`, a closed `0`-form has the same count `∫` and
  effective count `∮` over the canonically oriented solution sets of any two transversal
  perturbations (`IsTransversalPerturbation`: sc⁺, `N(Λ) ≤ 1`, not assumed structurable).  The
  cobordism is `corollary_15_3_10_3_transversal`; Stokes is `EP.theorem_9_5_17_dim1_all`,
  `EP.theorem_9_5_18_dim1_all`.

Namespace `Polyfold.StrongPolyfoldBundle`:
* `solutionPointPerturbation`, `count_solutionPointSuborbifold`,
  `countEff_solutionPointSuborbifold`: the class of a point solution set of the model, and its
  counts.
* `IsCanonicalPointSolutionSet o Q`: `Q` is the class of a point solution set of the model of
  `o` with the canonical orientation; `IsInheritedFromPoint.isCanonicalPointSolutionSet`.
* `theorem_16_6_6_index_zero_solutionSet_of_bump`: every admissible `λ` has such a `Q`.
* **`theorem_16_6_6_index_zero_count_eq`**, **`theorem_16_6_6_index_zero_all_admissible`**,
  `theorem_16_6_6_index_zero_all_admissible_wellDefined`: Theorem 16.6.6 for index `0` over all
  admissible `λ`, with the standing hypotheses `CanonicalBumpInput o 0`.

## Reading

As in `theorem_16_6_6_all_admissible`: the orientation is the canonical one in the model of `o`,
and no partitions of unity are assumed.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

variable (A) in
/-- **An oriented solution set of dimension `0`**: an sc⁺-multisection `Λ` with `Θ = Λ ∘ f`
compact and branched, and an orientation `T̂` of `Θ` described by oriented tame structures of
dimension `0` whose sheets are points.  Neither structurability of `Λ` nor a bound on `N(Λ)` is
part of the data. -/
structure PointSolution (f : A.Obj → A.W) where
  /-- The perturbation. -/
  Λ : A.W → ℚ≥0
  isScPlusMultisection : IsScPlusMultisection A Λ
  /-- The orientation `T̂` of `Θ = Λ ∘ f`. -/
  T : A.Obj → A.X.PObj.OrTangent →₀ ℚ
  isBranched : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ))
  isCompact : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))
  isOrientation : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T
  loc : A.X.IsPointTame (fun z => (Λ (f z) : ℚ)) T

namespace PointSolution

/-- The point solution set of a regular perturbation of dimension `0`. -/
def ofRegular (P : PointPerturbation A f) : PointSolution A f where
  Λ := P.Λ
  isScPlusMultisection := P.isRegular.2.1.1
  T := P.T
  isBranched := P.isBranched
  isCompact := P.isCompact
  isOrientation := P.isOrientation
  loc := P.loc

/-- **The weighted signed count `∫_{(Λ ∘ f, T̂)} ω`** (Definition 9.5.6 (1) for `n = 0`). -/
def count (P : PointSolution A f) (ω : A.baseEP.epFormsInfty 0) : ℝ :=
  A.baseEP.pointBranchedIntegral P.isBranched P.isCompact P.isOrientation P.loc ω

/-- **The effective count `∮_{(Λ ∘ f, T̂)} ω`** (Definition 9.5.6 (2) for `n = 0`). -/
def countEff (hLUC : A.X.IsLUC) (P : PointSolution A f) (ω : A.baseEP.epFormsInfty 0) : ℝ :=
  A.baseEP.pointBranchedIntegralEff hLUC P.isBranched P.isCompact P.isOrientation P.loc ω

theorem count_ofRegular (P : PointPerturbation A f) (ω : A.baseEP.epFormsInfty 0) :
    (ofRegular P).count ω = P.count ω := rfl

theorem countEff_ofRegular (hLUC : A.X.IsLUC) (P : PointPerturbation A f)
    (ω : A.baseEP.epFormsInfty 0) : (ofRegular P).countEff hLUC ω = P.countEff hLUC ω := rfl

end PointSolution

section Cylinder

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
include hd hft ho hidx in
/-- **2021 Corollary 15.4.4, p. 703, for Fredholm index `0`, over all transversal perturbations
with `N(Λ) ≤ 1`.**  Let `d_X ≡ 0`, `|X|` be paracompact, `X` admit sc-smooth bump functions, and
`(f, o)` be an oriented sc-Fredholm section functor with tame germ data and index `0`.  Let
`P₀`, `P₁` be the point solution sets of transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)` (sc⁺,
dom-supp in `Uⁱ`, `Nⁱ(Λⁱ) ≤ 1`, transversal; not assumed structurable) with the canonical
orientation of `(f, o)`.  Then a closed `0`-form has the same weighted signed count over `P₀` and
`P₁`, and the same effective count when `X` has the local unique continuation property.  No
partitions of unity are assumed. -/
theorem pointCount_eq_of_isTransversalPerturbation (hinv : A.E.IsOrInvariant hf hsec o)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.PObj.AdmitsBumpFunctions)
    {P₀ P₁ : PointSolution A f} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ P₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ P₁.Λ)
    (h₀ : IsCanonicalFor P₀.Λ hf.2 hsec o 0 P₀.T) (h₁ : IsCanonicalFor P₁.Λ hf.2 hsec o 0 P₁.T)
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    P₀.count ω = P₁.count ω ∧ ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbumpC
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  obtain ⟨Λ', hreg, e0, e1, -, hΘ', hcpt'⟩ :=
    corollary_15_3_10_3_transversal hd hpara (A.X.theorem_12_3_2_1.2 hbump) hf hft hr₀ hr₁
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1
  have hcan' := theorem_15_4_1_cylinder_index_zero hd hf hft hsec o ho hidx hbump hsec'
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hΛ' hreg.2.2.2.2 e0 e1 honto
  have hT' := hcan'.1
  have hloc' := hcan'.loc
  have hK' := hcan'.isKernelCanonical (canonContinuous Λ' hXC hbumpC hftC hsec'
    (cubeOrientation hf hft hsec o) (isSectionOrientation_cubeOrientation hX hbump hf hft ho))
  have hK₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T :=
    IsCanonicalFor.isKernelCanonical h₀ (canonContinuous P₀.Λ hX hbump hft hsec o ho)
  have hK₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T :=
    IsCanonicalFor.isKernelCanonical h₁ (canonContinuous P₁.Λ hX hbump hft hsec o ho)
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have m0 := exists_arePointMatchedAt_of_kernelCanonical hd hbump hf hft
    (fun x hx => (P₀.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 0) (ε := -1)
    (Or.inl ⟨z0, rfl⟩) e0 hΘ' hK₀ hK'
  have m1 := exists_arePointMatchedAt_of_kernelCanonical hd hbump hf hft
    (fun x hx => (P₁.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 1) (ε := 1)
    (Or.inr ⟨z1, rfl⟩) e1 hΘ' hK₁ hK'
  have hov0 := fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p
  have hov1 := fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p
  have hdω : (A.cubeSEP 1).baseEP.epFormsInftyD 0
      (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
        0 ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP)
        (A.X.cubeProj 1) 0) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  refine ⟨?_, fun hLUC => ?_⟩
  · have E0 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₀.isBranched P₀.isCompact
      P₀.isOrientation P₀.loc hΘ' hcpt' hT' hloc' (i := 0) (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₁.isBranched P₁.isCompact
      P₁.isOrientation P₁.loc hΘ' hcpt' hT' hloc' (i := 1) (q := fun _ => 1) z1 hov1 m1 ω
    have hsum : (A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) univ = -1 * P₀.count ω + 1 * P₁.count ω :=
      (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
        ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
        ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
          (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
            0 ω))).trans (congrArg₂ (· + ·) E0 E1)
    have hS := (A.cubeSEP 1).baseEP.theorem_9_5_17_dim1_all hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1) 0 ω)
    rw [hdω, tameBranchedIntegral_zero, hsum] at hS
    linarith
  · have hLUCC : (A.cubeSEP 1).X.IsLUC := isLUC_cubeSEP hLUC
    have E0 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC hLUCC
      P₀.isBranched P₀.isCompact P₀.isOrientation (P₀.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc') (i := 0)
      (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC hLUCC
      P₁.isBranched P₁.isCompact P₁.isOrientation (P₁.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc') (i := 1)
      (q := fun _ => 1) z1 hov1 m1 ω
    have hsum : (A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT'
        ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc')
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) univ = -1 * P₀.countEff hLUC ω + 1 * P₁.countEff hLUC ω :=
      (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
        ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
        ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT'
          ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc')
          (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
            0 ω))).trans (congrArg₂ (· + ·) E0 E1)
    have hS := (A.cubeSEP 1).baseEP.theorem_9_5_18_dim1_all hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc')
      (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1) 0 ω)
    have h0 : ((A.cubeSEP 1).baseEP.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff
        (Nat.succ_pos 0) hΘ' hcpt' hT' ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc') 0 =
        0 := by
      simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
        branchedIntegralEff, map_zero]
      rfl
    rw [hdω, h0, hsum] at hS
    linarith

end Cylinder

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP EpGroupoid

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-! ### The class of a point solution set of a model -/

section Models

variable (a : SectionRep c) (P : PointSolution a.S.A a.F)

/-- **The representative `((Λ ∘ F, T̂), (X, γ))`** of a point solution set of the model of `a`,
with `T̂` cut off outside `X_∞`. -/
def solutionPointRep : OrientedRep c.polyfold where
  p := a.S.toPolyfoldStructure
  mem := toPolyfoldStructure_mem a.hS
  A := ⟨fun z => (P.Λ (a.F z) : ℚ), a.S.A.X.smoothPart P.T, P.isBranched,
    EpGroupoid.hasIndependentTangentSums _, P.isOrientation.smoothPart⟩
  smooth := fun _ hx => EpGroupoid.smoothPart_of_notMem hx

theorem isPointTame_solutionPointRep :
    (solutionPointRep a P).p.X.X.IsPointTame (solutionPointRep a P).A.Θ
      (solutionPointRep a P).A.T := fun x hx => by
  obtain ⟨C, hS, hC⟩ := P.loc x hx
  exact ⟨C, hS, C.represents_congr (fun y hy => (EpGroupoid.smoothPart_of_mem hy).symm) hC⟩

/-- The compact oriented branched suborbifold of dimension `0` of a point solution set. -/
def solutionPointSuborbifold : PointSuborbifold c.polyfold where
  θ := ⟦solutionPointRep a P⟧
  isCompact := ⟨(solutionPointRep a P).toBranchedRep, rfl, P.isCompact⟩
  isTame := ⟨solutionPointRep a P, rfl,
    ((solutionPointRep a P).isPointTame_iff_isTameOriented).1 (isPointTame_solutionPointRep a P)⟩

/-- **The oriented perturbed solution set `λ ∘ f` of dimension `0` on the polyfold**, `λ` the
class of `Λ`. -/
def solutionPointPerturbation {s : ScSection c} (ha : ⟦a⟧ = s) :
    PointOrientedPerturbation s where
  toPointSuborbifold := solutionPointSuborbifold a P
  t := ⟦ofFunctor a.S a.hS P.Λ P.isScPlusMultisection⟧
  isPerturbed :=
    (perturbedRep_toFun_ofFunctor a P.Λ P.isScPlusMultisection P.isBranched).trans
      (by rw [ha])

/-- **The count on the polyfold is the count in the model.** -/
theorem count_solutionPointSuborbifold (τ : ScForm c.polyfold 0) :
    (solutionPointSuborbifold a P).count τ =
      P.count (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) := by
  refine ((solutionPointSuborbifold a P).θ.pointIntegralOfTame_eq _ _ τ
    (solutionPointRep a P) rfl).trans ?_
  unfold PointSolution.count OrientedRep.pointIntegral EP.pointBranchedIntegral
    EP.branchedIntegralDimZero branchedIntegral
  rw [EpGroupoid.branchedMeasure_congr_orientation _ P.isBranched P.isCompact P.isOrientation
    P.isOrientation.smoothPart (fun y hy => (EpGroupoid.smoothPart_of_mem hy).symm) P.loc
    (isPointTame_solutionPointRep a P)]
  rfl

/-- **The effective count on the polyfold is the effective count in the model.** -/
theorem countEff_solutionPointSuborbifold (τ : ScForm c.polyfold 0) :
    (solutionPointSuborbifold a P).countEff τ =
      P.countEff (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou)
        (ScForm.toStructure a.S.toPolyfoldStructure (toPolyfoldStructure_mem a.hS) τ) := by
  refine ((solutionPointSuborbifold a P).θ.pointIntegralEffOfTame_eq _ _ τ
    (solutionPointRep a P) rfl).trans ?_
  unfold PointSolution.countEff OrientedRep.pointIntegralEff EP.pointBranchedIntegralEff
    EP.branchedIntegralEffDimZero branchedIntegralEff
  rw [EpGroupoid.branchedMeasureEff_congr_orientation _ P.isBranched P.isCompact P.isOrientation
    P.isOrientation.smoothPart (fun y hy => (EpGroupoid.smoothPart_of_mem hy).symm)
    (P.loc.hasLUC (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou))
    ((isPointTame_solutionPointRep a P).hasLUC
      (a.S.A.X.proposition_7_4_10_of_isZhou a.S.isZhou))]
  rfl

end Models

/-- **`θ̂` of dimension `0` carries the canonical orientation of `(f, o)`** (Definition 15.4.2
read in the model of `o`): `Q` is the class of a point solution set `(Λ, T̂)` of the
representative `F` that carries `o`, with `T̂` the canonical orientation.  Unlike
`IsInheritedFromPoint`, `Λ` need not be a regular perturbation. -/
def IsCanonicalPointSolutionSet {s : FredholmSection c} (o : OrientationRep s)
    (Q : PointOrientedPerturbation s.1) : Prop :=
  ∃ P : PointSolution o.a.S.A o.a.F, IsCanonicalFor P.Λ o.hF.2 o.hsec o.o 0 P.T ∧
    solutionPointPerturbation o.a P o.ha = Q

/-- The orientation inherited from `(f, o)` is a canonical orientation of the solution set. -/
theorem IsInheritedFromPoint.isCanonicalPointSolutionSet {s : FredholmSection c}
    {o : OrientationRep s} {Q : PointOrientedPerturbation s.1}
    (h : IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q) :
    IsCanonicalPointSolutionSet o Q := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨PointSolution.ofRegular P, hP, rfl⟩

/-- An admissible `λ` is a transversal perturbation of the model with `N(Λ) ≤ 1` (index `0`). -/
theorem isTransversalPerturbation_of_isAdmissible_point {s : FredholmSection c}
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s}
    (P : PointSolution o.a.S.A o.a.F)
    (hadm : (solutionPointPerturbation o.a P o.ha).IsAdmissible n U) :
    IsTransversalPerturbation o.a.S.A o.a.F (o.a.S.normOf n) (o.a.g ⁻¹' U) P.Λ := by
  have hΛ := P.isScPlusMultisection
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS P.Λ hΛ
  have ht : ScPlusMultisection.IsControlledBy (c := c) ⟦b⟧ n U := hadm.1
  have hgp := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 _ o.a o.ha hΛ
    (toFun_of_mk_ofFunctor_eq rfl)).1 hadm.2
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) P.Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n P.Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp P.Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨hcca, hΛ, hdom, hN1, IsInGeneralPosition.isTransversal o.hF hΛ hgp⟩

/-- **2021 Theorem 16.6.6, p. 739, index `0`: every admissible `λ` gives a canonically oriented
`θ̂`** of dimension `0`, with bump functions in the model in place of partitions of unity. -/
theorem theorem_16_6_6_index_zero_solutionSet_of_bump (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s}
    (H : CanonicalBumpInput o 0) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (hgp : s.1.IsInGeneralPositionWith t) :
    ∃ Q : PointOrientedPerturbation s.1, Q.t = t ∧ Q.IsAdmissible n U ∧
      IsCanonicalPointSolutionSet o Q := by
  obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t o.a.hS
  have ht' : (⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ : ScPlusMultisection c) = t :=
    mk_ofFunctor_eq t o.a.hS hΛ hl
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t o.a o.ha hΛ hl).1 hgp
  rw [← ht'] at ht
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have ho := o.isSectionOrientation hX H.bump H.tame
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS Λ hΛ
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have htr := IsInGeneralPosition.isTransversal o.hF hΛ hgpΛ
  have hgood : ∀ x, 0 < Λ (o.a.F x) → SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hΛ hgpΛ hpos
  obtain ⟨hbr, hcpt⟩ := theorem_15_4_3_isBranched_hyp o.hF H.tame hcca hΛ hdom hN1 htr
    fun x _ => hgood x
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (0 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hΛ (by exact_mod_cast hx))
  have hcan := theorem_15_4_1 hX H.bump o.hF H.tame hΛ o.hsec o.o o.isOrientation.2 ho
    (fun x hx => hgood x (by exact_mod_cast hx)) hidx
  let P : PointSolution o.a.S.A o.a.F :=
    ⟨Λ, hΛ, canonicalOrientation Λ o.hF.2 o.hsec o.o, hbr, hcpt, hcan.1,
      EpGroupoid.isPointTame_iff.2 hcan.loc⟩
  exact ⟨solutionPointPerturbation o.a P o.ha, ht', ⟨ht, o.a, Λ, hΛ, o.ha, rfl, hgpΛ⟩, P, hcan,
    rfl⟩

/-! ### Independence of the perturbation -/

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), for Fredholm index `0`: the counts do not
depend on the admissible perturbation.**  Let `∂Z = ∅`, `(n, U)` control the compactness of `f`,
and `o` be an orientation of `f` whose model has sc-smooth bump functions, tame germ data and
Fredholm index `0`.  For perturbed solution sets `θ̂₀`, `θ̂₁` of dimension `0` of admissible
`λ₀`, `λ₁` (controlled by `(n, U)`, in general position; neither structurability nor `n(λ) < 1`
is asked) with the canonical orientation of `(f, o)`, a closed `0`-form `τ` has the same weighted
signed count and the same effective count.  No partitions of unity are assumed. -/
theorem theorem_16_6_6_index_zero_count_eq (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalBumpInput o 0)
    {Q₀ Q₁ : PointOrientedPerturbation s.1}
    (a₀ : Q₀.IsAdmissible n U) (c₀ : IsCanonicalPointSolutionSet o Q₀)
    (a₁ : Q₁.IsAdmissible n U) (c₁ : IsCanonicalPointSolutionSet o Q₁)
    (τ : ScForm c.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  obtain ⟨P₀, hT₀, rfl⟩ := c₀
  obtain ⟨P₁, hT₁, rfl⟩ := c₁
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have ho := o.isSectionOrientation hX H.bump H.tame
  have hr₀ := isTransversalPerturbation_of_isAdmissible_point hn hU hcc P₀ a₀
  have hr₁ := isTransversalPerturbation_of_isAdmissible_point hn hU hcc P₁ a₁
  have hq := toPolyfoldStructure_mem o.a.hS
  have hω : o.a.S.A.baseEP.epFormsInftyD 0
      (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
    have h : o.a.S.toPolyfoldStructure.X.epFormsInftyD 0
        (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
      rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
    exact h
  have hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x 0 :=
    fun x hx => by exact_mod_cast H.index x hx
  obtain ⟨e, eE⟩ := pointCount_eq_of_isTransversalPerturbation hd o.hF H.tame o.hsec o.o ho hidx
    o.isOrientation.2 o.a.S.paracompact H.bump hr₀ hr₁ hT₀ hT₁ _ hω
  refine ⟨?_, ?_⟩
  · change (solutionPointSuborbifold o.a P₀).count τ = (solutionPointSuborbifold o.a P₁).count τ
    rw [count_solutionPointSuborbifold, count_solutionPointSuborbifold]
    exact e
  · change (solutionPointSuborbifold o.a P₀).countEff τ =
      (solutionPointSuborbifold o.a P₁).countEff τ
    rw [countEff_solutionPointSuborbifold, countEff_solutionPointSuborbifold]
    exact eE _

/-- **2021 Theorem 16.6.6, p. 739, for Fredholm index `0`, over all admissible perturbations**:
`theorem_16_6_6_index_zero_polyfold_statement` for the predicate "`θ̂` carries the canonical
orientation of `(f, o)`", with the standing hypotheses `CanonicalBumpInput o 0`.  No partitions of
unity are assumed, and the compactness of the solution set of `f` is used only through `(n, U)`
controlling compactness. -/
theorem theorem_16_6_6_index_zero_all_admissible (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (fun o Q => CanonicalBumpInput o 0 ∧ IsCanonicalPointSolutionSet o Q) := by
  rintro hbd - hn hU hcc o Q₀ Q₁ a₀ ⟨H, c₀⟩ a₁ ⟨-, c₁⟩ τ hτ
  exact theorem_16_6_6_index_zero_count_eq hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ

/-- **2021 Theorem 16.6.6, p. 739, index `0`, existence and independence over all admissible
`λ`**: every sc⁺-multisection `λ` controlled by `(n, U)` with `(f, λ)` in general position has a
perturbed solution set of dimension `0` with the canonical orientation of `(f, o)`, and the
counts `∫_θ̂ τ`, `∮_θ̂ τ` of a closed `0`-form agree over any two of them. -/
theorem theorem_16_6_6_index_zero_all_admissible_wellDefined (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalBumpInput o 0) :
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : PointOrientedPerturbation s.1, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalPointSolutionSet o Q) ∧
    ∀ Q₀ Q₁ : PointOrientedPerturbation s.1, Q₀.IsAdmissible n U →
      IsCanonicalPointSolutionSet o Q₀ → Q₁.IsAdmissible n U →
      IsCanonicalPointSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold 0, ScForm.d τ = 0 →
        Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  ⟨fun t ht hgp => theorem_16_6_6_index_zero_solutionSet_of_bump hbd hn hU hcc H t ht hgp,
    fun _ _ a₀ c₀ a₁ c₁ τ hτ =>
      theorem_16_6_6_index_zero_count_eq hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ⟩

end StrongPolyfoldBundle

end Polyfold
