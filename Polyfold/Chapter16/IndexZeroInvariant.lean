import Polyfold.Chapter16.ModelPerturbations
import Polyfold.Chapter9.DimensionZeroIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6, p. 739: **Theorem 16.6.6** (2017: Theorem 16.8) **for Fredholm index `0`**, with the
`0`-dimensional branched integral of §9.5.  Numbers and pages are the 2021 text's.

## The text, paraphrased

(Theorem 9.5.4, Definition 9.5.6) For an oriented, tame, compact branched ep⁺-subgroupoid `Θ̂` of
dimension `n` and a form `ω` of degree `n`, `∫_Θ̂ ω = μ_ω(S)` and `∮_Θ̂ ω = μ^eff_ω(S)`, where
`μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` on `|U(x)|`.  For `n = 0` the sheets are oriented
points and `∫_{{p}} ω|({p}, o) = ±ω(p)`: the integral is a weighted signed count.
(Theorem 16.6.6) If the Fredholm index is `k`, the integrals of a closed `k`-form over `λ ∘ f` do
not depend on `λ`; for `k = 0` the closed `0`-forms are the locally constant functions and the
invariant is the weighted count of the perturbed solutions.

## What is formalized

Ep-groupoid level (namespaces `Polyfold.EpGroupoid`, `Polyfold.EP`):
* `EpGroupoid.IsPointTame Θ T`: `Θ̂ = (Θ, T)` is tame of dimension `0`: at every point of
  `supp Θ` an oriented tame structure of dimension `0` whose sheets are points describes `T`;
  an abbreviation of Part II's `EpGroupoid.IsTameOfDimZero` (`Chapter9/DimensionZeroIntegral`).
* **`EP.pointBranchedIntegral`**, **`EP.pointBranchedIntegralEff`**: Definition 9.5.6 for
  `n = 0`, the total mass of the measures of Theorems 9.5.4 and 9.5.5 for the integration of
  `0`-forms over oriented points (`EP.zeroFormIntegration`); abbreviations of Part II's
  `EP.branchedIntegralDimZero`, `EP.branchedIntegralEffDimZero`; `pointBranchedMeasure_apply`,
  `pointBranchedMeasureEff_apply` are the local formulas, `pointBranchedIntegral_zero` the value
  on the zero form.
* **`EP.pointIntegral_eq_of_cobordism`**, **`pointIntegralEff_eq_of_cobordism`**: the cobordism
  argument of Corollary 15.4.4 in dimension `0`: if a compact oriented tame `1`-dimensional `Θ̃`
  on `Y` has boundary measure `μ^{∂Θ̃}_{F^*ω}(∂S) = I₁(ω) − I₀(ω)`, then `I₀(ω) = I₁(ω)` for
  closed `0`-forms `ω` (Theorems 9.5.17, 9.5.18 for `n = 1`).
* `EpGroupoid.isPointTame_point_rn`: a witness with nonempty support, a point of `ℝⁿ` with
  weight `1` and any orientation.

Model level (namespace `Polyfold.SBLocalization`):
* `PointPerturbation A f`: a regular perturbation `(N, U, Λ)` with `Θ = Λ ∘ f` compact, branched,
  oriented and tame of dimension `0`; `count`, `countEff` (the weighted signed counts
  `∫_{(Λ ∘ f, o)} ω`, `∮_{(Λ ∘ f, o)} ω`); `HasOrientedCobordism`, `HasOrientedCobordismEff` (a
  compact oriented tame `1`-dimensional cobordism with the boundary identity);
  `hasOrientedCobordism_refl`, `hasOrientedCobordismEff_refl`.
* **`corollary_15_4_4_index_zero`**: cobordant perturbations have the same counts of closed
  `0`-forms.

Polyfold level (namespace `Polyfold.StrongPolyfoldBundle`):
* `theorem_16_6_6_index_zero_statement`, **`theorem_16_6_6_index_zero_of_model`**: Theorem
  16.6.6 for index `0`, read in the model of the orientation: for `∂Z = ∅`, `f` with compact
  solution set, and a closed sc-differential `0`-form `τ` on `Z`, the counts `∫`, `∮` of the
  representative of `τ` over any two perturbations of the model with the orientation `Can o`
  agree, given the `1`-dimensional cobordisms in the model.

## Reading

* A tame `0`-dimensional structure is read with sheets that are points (`pointSheets`: one
  smooth point or empty); a `0`-dimensional submanifold is discrete, so this is the form the
  local structures take after shrinking `U(x)`.
* As in dimension `≥ 1`, the perturbations compared are those of the model that carries the
  orientation.  The independence of the count of the model (Theorem 11.4.1 for `n = 0`) is not
  part of this file.
* "Depends only on `[τ]`" has no content in degree `0` (there are no exact `0`-forms but `0`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

variable (X : EpGroupoid Obj Mor) in
/-- **`Θ̂ = (Θ, T)` is tame of dimension `0`** (Definition 9.3.6 for `n = 0`): at every point of
`supp Θ` there is an oriented tame structure of dimension `0` whose sheets are points, describing
`T`.  This is Part II's `EpGroupoid.IsTameOfDimZero`. -/
abbrev IsPointTame (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop :=
  X.IsTameOfDimZero Θ T

variable {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-- With the local unique continuation property, the structures of a tame `0`-dimensional `Θ̂`
have it (Definition 7.2.18). -/
theorem IsPointTame.hasLUC (h : X.IsPointTame Θ T) (hLUC : X.IsLUC) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure 0 Θ x,
      (∀ i, C.M i ∈ pointSheets X) ∧ C.Represents T ∧ C.rep.HasLUC :=
  IsTameOfDimZero.hasLUC h hLUC

end EpGroupoid

namespace EP

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Definition 9.5.6 (1) for `n = 0`: the weighted signed count `∫_Θ̂ ω = μ_ω(|supp Θ|)`** of a
`0`-form `ω` over an oriented, tame, compact `0`-dimensional `Θ̂` (Theorem 9.5.4 with
`∫_{{p}} ω|({p}, o) = ±ω(p)`).  This is Part II's `EP.branchedIntegralDimZero`. -/
abbrev pointBranchedIntegral (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (ω : A.epFormsInfty 0) : ℝ :=
  A.branchedIntegralDimZero hΘ hcpt hT hloc ω

/-- **Definition 9.5.6 (2) for `n = 0`: the effective count `∮_Θ̂ ω = μ^eff_ω(|supp Θ|)`**
(Theorem 9.5.5, weights `1/♯G_x^eff`), for `X` with the local unique continuation property.
This is Part II's `EP.branchedIntegralEffDimZero`. -/
abbrev pointBranchedIntegralEff (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (ω : A.epFormsInfty 0) : ℝ :=
  A.branchedIntegralEffDimZero hLUC hΘ hcpt hT hloc ω

/-- **The local formula of the count** (Theorem 9.5.4 for `n = 0`): on `|U(x)|` the measure is
`(1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` with `∫_{{p}} ω|({p}, o) = ±ω(p)`. -/
theorem pointBranchedMeasure_apply (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (ω : A.epFormsInfty 0) {x : A.Obj} (C : A.X.OrientedTameStructure 0 Θ x)
    (hS : ∀ i, C.M i ∈ pointSheets A.X) (hCT : C.Represents T)
    {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    branchedMeasure A.zeroFormIntegration hΘ hcpt hT hloc ω K =
      C.localMeasure A.zeroFormIntegration ω (Subtype.val '' K) :=
  branchedMeasure_apply A.zeroFormIntegration hΘ hcpt hT hloc ω C hS hCT hK hKU

/-- **The local formula of the effective count** (Theorem 9.5.5 for `n = 0`). -/
theorem pointBranchedMeasureEff_apply (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (ω : A.epFormsInfty 0) {x : A.Obj} (C : A.X.OrientedTameStructure 0 Θ x)
    (hS : ∀ i, C.M i ∈ pointSheets A.X) (hCT : C.Represents T)
    {K : Set (A.X.orbitSupp Θ)}
    (hK : MeasurableSet[A.X.lebesgueSigma (SheetNullSets.point (pointSheets A.X)) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    branchedMeasureEff A.zeroFormIntegration hΘ hcpt hT (hloc.hasLUC hLUC) ω K =
      C.localMeasureEff A.zeroFormIntegration ω (Subtype.val '' K) :=
  branchedMeasureEff_apply A.zeroFormIntegration hΘ hcpt hT (hloc.hasLUC hLUC) ω C hS hCT
    (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep) hK hKU

/-- The count of the zero form is `0`. -/
theorem pointBranchedIntegral_zero (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T) :
    A.pointBranchedIntegral hΘ hcpt hT hloc 0 = 0 := by
  simp only [pointBranchedIntegral, branchedIntegralDimZero, branchedIntegral, map_zero]
  rfl

/-- The count is additive in the form. -/
theorem pointBranchedIntegral_add (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T)
    (ω η : A.epFormsInfty 0) :
    A.pointBranchedIntegral hΘ hcpt hT hloc (ω + η) =
      A.pointBranchedIntegral hΘ hcpt hT hloc ω + A.pointBranchedIntegral hΘ hcpt hT hloc η := by
  simp only [pointBranchedIntegral, branchedIntegralDimZero, branchedIntegral, map_add]
  rfl

variable {A}

/-- **The cobordism argument of Corollary 15.4.4 in dimension `0`**: let `F : Y → X` be an
sc-smooth functor, `Y` with sc-smooth partitions of unity, `Θ̃` compact, branched, oriented and
tame of dimension `1` on `Y`, with `μ^{∂Θ̃}_{F^*ω}(∂S) = I₁(ω) − I₀(ω)` for all `0`-forms `ω`
(Theorem 9.5.15 for `n = 1`).  Then `I₀(ω) = I₁(ω)` for every closed `ω`: by Stokes (Theorem
9.5.17 for `n = 1`), `μ^{∂Θ̃}_{F^*ω}(∂S) = ∫_{Θ̃} d F^*ω = ∫_{Θ̃} F^* dω = 0`. -/
theorem pointIntegral_eq_of_cobordism {X Y : EP.{u}} (F : EpFunctor Y.X X.X)
    (hPU : Y.X.HasScPartitionsOfUnity) {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty 0 → ℝ)
    (hbd : ∀ ω, Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F 0 ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty 0) (hω : X.epFormsInftyD 0 ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_17_dim1 hPU hΘ' hcpt' hT' hloc' (EP.epFormsInftyPullback F 0 ω)
  have hd : Y.epFormsInftyD 0 (EP.epFormsInftyPullback F 0 ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F 0) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hd, SBLocalization.tameBranchedIntegral_zero, hbd] at hS
  linarith

/-- **The effective cobordism argument in dimension `0`** (Theorem 9.5.18 for `n = 1`). -/
theorem pointIntegralEff_eq_of_cobordism {X Y : EP.{u}} (F : EpFunctor Y.X X.X)
    (hPU : Y.X.HasScPartitionsOfUnity) (hLUC : Y.X.IsLUC) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty 0 → ℝ)
    (hbd : ∀ ω, Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUC hloc')
      (EP.epFormsInftyPullback F 0 ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty 0) (hω : X.epFormsInftyD 0 ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_18_dim1 hPU hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUC hloc')
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

/-! ### A witness: an oriented point of `ℝⁿ` -/

namespace EpGroupoid

variable {n : ℕ}

open scoped Classical in
/-- **A point of `ℝⁿ` with weight `1` and an orientation is tame of dimension `0`**, with
nonempty support: for the one sheet `M = {p}`, `Θ = 1_{{p}}` on the trivial ep-groupoid of `ℝⁿ`
and `T̂ = (T_p{p}, o)`, `Θ` is a compact branched ep⁺-subgroupoid, `T̂` an orientation, `p` lies
in the support and `Θ̂` is tame of dimension `0` in the sense of `IsPointTame`. -/
theorem isPointTame_point_rn (p : Fin n → ℝ) (M : Unit → Set (Fin n → ℝ))
    (hMp : ∀ i, M i = {p}) (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) 0) :
    (trivial (rnPolyfold n)).IsBranchedEpSubgroupoid (fun y => ∑ i with y ∈ M i, (1 : ℚ)) ∧
      (trivial (rnPolyfold n)).IsCompactBranched (fun y => ∑ i with y ∈ M i, (1 : ℚ)) ∧
      (trivial (rnPolyfold n)).IsOrientation (fun y => ∑ i with y ∈ M i, (1 : ℚ))
        (orientedSumRn M (fun _ => (1 : ℚ)) o) ∧
      p ∈ supp (fun y => ∑ i with y ∈ M i, (1 : ℚ)) ∧
      (trivial (rnPolyfold n)).IsPointTame (fun y => ∑ i with y ∈ M i, (1 : ℚ))
        (orientedSumRn M (fun _ => (1 : ℚ)) o) := by
  have hM : ∀ i : Unit, (rnPolyfold n).IsSubmanifoldOfDim (M i) 0 := fun i => by
    rw [hMp i]; exact rnPolyfold_isSubmanifoldOfDim_singleton p
  have hc : ∀ i : Unit, IsClosed (M i) := fun i => by rw [hMp i]; exact isClosed_singleton
  have hsupp : supp (fun y => ∑ i with y ∈ M i, (1 : ℚ)) = {p} := by
    ext y
    change (0 : ℚ) < ∑ i with y ∈ M i, (1 : ℚ) ↔ y ∈ ({p} : Set (Fin n → ℝ))
    by_cases hy : y = p
    · refine iff_of_true (Finset.sum_pos (fun _ _ => one_pos) ⟨(), ?_⟩) hy
      rw [Finset.mem_filter, hMp]
      exact ⟨Finset.mem_univ _, hy⟩
    · have he : (Finset.univ.filter fun i => y ∈ M i) = ∅ :=
        Finset.filter_false_of_mem fun i _ => by rw [hMp]; exact hy
      rw [he, Finset.sum_empty]
      exact iff_of_false (lt_irrefl _) hy
  refine ⟨isBranchedEpSubgroupoid_sum_rn M (fun _ => (1 : ℚ)) (fun _ => one_pos)
    (fun i => (hM i).1) hc, ?_,
    isOrientation_sum_trivial_rn M (fun _ => 1) (fun _ => one_pos) hM hc _, ?_, fun x hx => ?_⟩
  · unfold IsCompactBranched orbitSupp
    rw [hsupp, image_singleton]
    exact isCompact_singleton
  · rw [hsupp]; rfl
  · obtain ⟨C, hC⟩ := exists_orientedTameStructure_sum_rn M (fun _ => (1 : ℚ))
      (fun _ => one_pos) hM hc o x
    have hxp : x = p := by
      have h := hx
      rw [hsupp] at h
      exact h
    refine ⟨C, fun i => Or.inr ⟨p, ?_, ?_⟩, hC⟩
    · change p ∈ (rnPolyfold n).smoothSet
      rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ p
    · have hsub : C.M i ⊆ {p} := fun y hy => by
        have h := C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hy
        rw [hsupp] at h
        exact h
      have hmem : p ∈ C.M i := hxp ▸ C.toTameBranchingStructure.toLocalBranchingStructure.mem_M i
      exact Subset.antisymm hsub (singleton_subset_iff.2 hmem)

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr Linearization15 SEP

variable {A : SEP.{u}}

variable (A) in
/-- An **oriented regular perturbation of dimension `0`** (Corollary 15.3.10 (1), Definition
15.4.2, for Fredholm index `0`): a structurable regular perturbation `(N, U, Λ)` of `f` with
`Θ = Λ ∘ f` compact and branched, and an orientation `T̂` of `Θ` described by oriented tame
structures of dimension `0` whose sheets are points. -/
structure PointPerturbation (f : A.Obj → A.W) where
  /-- The auxiliary norm. -/
  N : A.B.One → ℝ
  /-- The controlling neighbourhood. -/
  U : Set A.Obj
  /-- The perturbation. -/
  Λ : A.W → ℚ≥0
  isRegular : IsRegularPerturbation A f N U Λ
  /-- The orientation `T̂` of `Θ = Λ ∘ f`. -/
  T : A.Obj → A.X.PObj.OrTangent →₀ ℚ
  isBranched : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ))
  isCompact : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))
  isOrientation : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T
  loc : A.X.IsPointTame (fun z => (Λ (f z) : ℚ)) T

namespace PointPerturbation

variable {f : A.Obj → A.W}

/-- **The weighted signed count `∫_{(Λ ∘ f, o)} ω`** of the perturbed solutions, for a `0`-form
`ω` (Definition 9.5.6 (1) for `n = 0`). -/
def count (P : PointPerturbation A f) (ω : A.baseEP.epFormsInfty 0) : ℝ :=
  A.baseEP.pointBranchedIntegral P.isBranched P.isCompact P.isOrientation P.loc ω

/-- **The effective count `∮_{(Λ ∘ f, o)} ω`** (Definition 9.5.6 (2) for `n = 0`). -/
def countEff (hLUC : A.X.IsLUC) (P : PointPerturbation A f) (ω : A.baseEP.epFormsInfty 0) : ℝ :=
  A.baseEP.pointBranchedIntegralEff hLUC P.isBranched P.isCompact P.isOrientation P.loc ω

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism of dimension `1`** (the proof of
Corollary 15.4.4 for index `0`): an ep-groupoid `Y` with partitions of unity, an sc-smooth
functor `F : Y → X` and a compact branched `Θ̃` on `Y`, oriented and tame of dimension `1`, with
`μ^{∂Θ̃}_{F^*ω}(∂S) = ∫_{P₁} ω − ∫_{P₀} ω`. -/
def HasOrientedCobordism (P₀ P₁ : PointPerturbation A f) : Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X) (_ : Y.X.HasScPartitionsOfUnity)
    (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F 0 ω) univ = P₁.count ω - P₀.count ω

/-- The effective form of `HasOrientedCobordism` (with the local unique continuation property
on `Y` and the effective boundary measure). -/
def HasOrientedCobordismEff (hLUC : A.X.IsLUC) (P₀ P₁ : PointPerturbation A f) : Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X) (_ : Y.X.HasScPartitionsOfUnity)
    (hLUCY : Y.X.IsLUC) (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (Y.hloc_hasLUC_dim1 hLUCY hloc')
      (EP.epFormsInftyPullback F 0 ω) univ = P₁.countEff hLUC ω - P₀.countEff hLUC ω

private theorem zero_data (m : ℕ) :
    (∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (0 : A.Obj → ℚ)) ∧
      A.X.IsCompactBranched (0 : A.Obj → ℚ) ∧
      ∀ x ∈ EpGroupoid.supp (0 : A.Obj → ℚ),
        ∃ C : A.X.OrientedTameStructure m 0 x, C.Represents fun _ => 0 := by
  refine ⟨fun x hx => lt_irrefl (0 : ℚ) hx.2, ?_, fun x hx => absurd hx (lt_irrefl (0 : ℚ))⟩
  have : A.X.orbitSupp (0 : A.Obj → ℚ) = ∅ := by
    rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
    exact fun x hx => lt_irrefl (0 : ℚ) hx
  rw [IsCompactBranched, this]; exact isCompact_empty

/-- **The cobordism hypothesis is satisfiable**: every perturbation is cobordant to itself
(`Y = X`, `F = id`, `Θ̃ = 0`). -/
theorem hasOrientedCobordism_refl (hPU : A.X.HasScPartitionsOfUnity)
    (P : PointPerturbation A f) : HasOrientedCobordism P P := by
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data (A := A) (0 + 1)
  refine ⟨A.baseEP, EpFunctor.id _, hPU, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact signedMeasure_univ_eq_zero_of_boundary (B := A.baseEP) hemp _

/-- **The effective cobordism hypothesis is satisfiable.** -/
theorem hasOrientedCobordismEff_refl (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (P : PointPerturbation A f) : HasOrientedCobordismEff hLUC P P := by
  obtain ⟨hemp, hcpt0, hloc0⟩ := zero_data (A := A) (0 + 1)
  refine ⟨A.baseEP, EpFunctor.id _, hPU, hLUC, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact signedMeasure_univ_eq_zero_of_boundary (B := A.baseEP) hemp _

end PointPerturbation

/-- **Corollary 15.4.4 for Fredholm index `0`** (p. 703): perturbations joined by an oriented
compact cobordism of dimension `1` have the same weighted counts of closed `0`-forms, and the
same effective counts for the effective cobordisms. -/
theorem corollary_15_4_4_index_zero {f : A.Obj → A.W} (P₀ P₁ : PointPerturbation A f)
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    (P₀.HasOrientedCobordism P₁ → P₀.count ω = P₁.count ω) ∧
      ∀ hLUC : A.X.IsLUC, P₀.HasOrientedCobordismEff hLUC P₁ →
        P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  refine ⟨fun h => ?_, fun hLUC h => ?_⟩
  · obtain ⟨Y, F, hPUY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
    exact EP.pointIntegral_eq_of_cobordism F hPUY hΘ' hcpt' hT' hloc' P₀.count P₁.count hbd ω hω
  · obtain ⟨Y, F, hPUY, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := h
    exact EP.pointIntegralEff_eq_of_cobordism F hPUY hLUCY hΘ' hcpt' hT' hloc'
      (P₀.countEff hLUC) (P₁.countEff hLUC) hbd ω hω

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **2021 Theorem 16.6.6 for Fredholm index `0`**, as a proposition, read in the model of the
orientation: under the text's hypotheses (`∂Z = ∅`, `f` oriented with compact solution set,
`(n, U)` controlling compactness), for every orientation `o` and any two regular perturbations
`P₀`, `P₁` of dimension `0` in the model of `o` with the orientation `Can o`, a closed
sc-differential `0`-form `τ` on `Z` has the same count `∫` and the same effective count `∮` over
`P₀` and `P₁`; the form is read in the model through its representative. -/
def theorem_16_6_6_index_zero_statement (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop) : Prop :=
  c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → c.IsAuxNorm n → IsOpen U →
    s.1.ControlsCompactness n U → ∀ (o : OrientationRep s)
      (P₀ P₁ : PointPerturbation o.a.S.A o.a.F), Can o P₀ → Can o P₁ →
      ∀ τ : ScForm c.polyfold 0, ScForm.d τ = 0 →
        P₀.count (ScForm.toStructure o.a.S.toPolyfoldStructure (toPolyfoldStructure_mem o.a.hS) τ) =
            P₁.count
              (ScForm.toStructure o.a.S.toPolyfoldStructure (toPolyfoldStructure_mem o.a.hS) τ) ∧
          P₀.countEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
              (ScForm.toStructure o.a.S.toPolyfoldStructure (toPolyfoldStructure_mem o.a.hS) τ) =
            P₁.countEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou)
              (ScForm.toStructure o.a.S.toPolyfoldStructure (toPolyfoldStructure_mem o.a.hS) τ)

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, from the cobordisms in the model of the
orientation**: if, for `∂Z = ∅` and `f` with compact solution set, any two perturbations of
dimension `0` with the orientation `Can o` are joined by oriented compact cobordisms of dimension
`1` in the model of `o`, the weighted counts of closed `0`-forms do not depend on the
perturbation. -/
theorem theorem_16_6_6_index_zero_of_model (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (Can : ∀ o : OrientationRep s, PointPerturbation o.a.S.A o.a.F → Prop)
    (hcob : c.polyfold.boundary = ∅ → s.1.HasCompactSolutionSet → ∀ (o : OrientationRep s)
      (P₀ P₁ : PointPerturbation o.a.S.A o.a.F), Can o P₀ → Can o P₁ →
      P₀.HasOrientedCobordism P₁ ∧
        P₀.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P₁) :
    theorem_16_6_6_index_zero_statement s n U Can := by
  intro hbd hcs _ _ _ o P₀ P₁ h₀ h₁ τ hτ
  obtain ⟨h, he⟩ := hcob hbd hcs o P₀ P₁ h₀ h₁
  set q := o.a.S.toPolyfoldStructure
  have hq : (⟦q⟧ : PolyfoldClass Z) = c.polyfold := toPolyfoldStructure_mem o.a.hS
  have hω : q.X.epFormsInftyD 0 (ScForm.toStructure q hq τ) = 0 := by
    rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
  have key := corollary_15_4_4_index_zero P₀ P₁ (ScForm.toStructure q hq τ) hω
  exact ⟨key.1 h, key.2 _ he⟩

/-- **The cobordism hypotheses of `theorem_16_6_6_index_zero_of_model` are satisfiable**: for the
predicate that singles out one perturbation they hold, when `Z` admits sc-smooth partitions of
unity. -/
theorem theorem_16_6_6_index_zero_hcob_witness (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    {s : FredholmSection c} (o : OrientationRep s) (P : PointPerturbation o.a.S.A o.a.F) :
    P.HasOrientedCobordism P ∧
      P.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P := by
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  exact ⟨PointPerturbation.hasOrientedCobordism_refl hPUq P,
    PointPerturbation.hasOrientedCobordismEff_refl hPUq _ P⟩

end StrongPolyfoldBundle

end Polyfold
