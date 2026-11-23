import Polyfold.Chapter15.AdmissibleCobordism
import Polyfold.Chapter15.RelativeStepFamilies
import Polyfold.Chapter15.CylinderOrientationLocal
import Polyfold.Chapter15.CylinderFrameConventionLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.3** and **Corollary 15.4.4**, for transversal perturbations with `N(Λ) ≤ 1`, with
the orientation of `f` read in the local orientation sets and no sc-smooth bump functions.

# Corollary 15.4.4 from local families on the cylinder, without bump functions

## The text, paraphrased

(Corollary 15.4.4) `∫_{(Λ ∘ f, o)} ω` does not depend on the regular perturbation; the proof joins
two perturbations by the cobordism of Corollary 15.3.10 (3) and uses Theorem 15.4.1 on
`[0, 1] × X` and Stokes.

## What is formalized (namespace `Polyfold.SBLocalization`)

The statements of `AdmissibleCobordism.lean` with two changes: the orientation hypothesis is the
continuity of `o` in the local orientation sets (`IsSectionOrientationLoc`), and the perturbation
of the cylinder is obtained from local families at the interior points of the solution set of
the explicit extension (the hypothesis of `corollary_15_3_10_3_transversal_of_families`).

* `exists_cylinder_local_ends_transversal_loc`,
* **`integral_eq_of_isTransversalPerturbation_loc`**,
  **`integralEff_eq_of_isTransversalPerturbation_loc`**.

## Reading

Theorem 15.4.1 on the cylinder is `theorem_15_4_1_cylinder_loc`, the continuity of the canonical
orientations is `canonContinuous_loc`, the frame convention on the ends is
`cylinderKernelFrameConvention_of_isIndexAt_loc`; Stokes is `EP.theorem_9_5_17_all`,
`EP.theorem_9_5_18_all`.
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

section Transversal

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (hoL : IsSectionOrientationLoc (A.X.isTame_of_degIndex_eq_zero hd) hft
    fun y hy => orxLocEquiv hft hsec y hy (o y hy))
  (hinvC : (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft)
    hsec' (cubeOrientation hf hft hsec o))
  {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
include hd hoL hinvC hidx in
/-- **The canonically oriented cobordism between two transversal perturbations**: for `d_X ≡ 0`,
`|X|` paracompact and local families on the cylinder (`H`), let `S₀`, `S₁` be oriented solution sets of
transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)` (sc⁺, `Nⁱ(Λⁱ) ≤ 1`, not assumed structurable) with the
canonical orientation of `(f, o)`.  Then there is an sc⁺-multisection `Λ̃` on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `t = i`, `Θ̃ = Λ̃ ∘ f̃` compact and branched, and the canonical orientation `T̃` of
`(f̃, õ)` on `Θ̃`, described by oriented tame structures of dimension `m + 2`, with
`∂Θ̃ = Θ₁ ⊔ −Θ₀` on the level of the local end identities. -/
theorem exists_cylinder_local_ends_transversal_loc (hpara : A.X.HasParacompactOrbitSpace)
    {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (H : ∀ x ∉ (A.cubeSEP 1).X.PObj.boundary,
      0 < cylExtension S₀.Λ S₁.Λ (cubeLiftEp (n := 1) f hf.1.1.1 x) →
      ∃ Q : Set (A.cubeSEP 1).Obj, IsOpen Q ∧ (A.cubeSEP 1).X.IsSaturated Q ∧ x ∈ Q ∧
        Nonempty (RelGPFamily (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
          (cylExtension S₀.Λ S₁.Λ) (collarAuxNorm A N₀ N₁)
          (interpSet A U₀ U₁ ∩ (A.cubeSEP 1).X.PObj.boundaryᶜ)
          (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
            pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension S₀.Λ S₁.Λ) z) Q)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsTransversalPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (collarAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      ∃ (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
        (hcpt' : (A.cubeSEP 1).X.IsCompactBranched
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
        (T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ)
        (hT' : (A.cubeSEP 1).X.IsOrientation
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) T')
        (hloc' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)),
          ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
            (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) x, C.Represents T')
        (hover₀ : ∀ p : cylEnd (X := A.X)
            (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) 0,
          cylEndMap p ∈ A.X.orbitSupp (fun z => (S₀.Λ (f z) : ℚ)))
        (hover₁ : ∀ p : cylEnd (X := A.X)
            (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) 1,
          cylEndMap p ∈ A.X.orbitSupp (fun z => (S₁.Λ (f z) : ℚ))),
        IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
            (cubeOrientation hf hft hsec o) (m + 1 + 1) T' ∧
          (∀ (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC),
            Adm.IsLocalEndIdentityEff hLUC hLUCC S₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀ ∧
              Adm.IsLocalEndIdentityEff hLUC hLUCC S₁ hΘ' hcpt' hT' hloc' 1 1 hover₁) ∧
          Adm.IsLocalEndIdentity S₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀ ∧
          Adm.IsLocalEndIdentity S₁ hΘ' hcpt' hT' hloc' 1 1 hover₁ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  obtain ⟨Λ', hreg, e0, e1, -, hΘ', hcpt'⟩ :=
    corollary_15_3_10_3_transversal_of_families hd hpara hf hft hr₀ hr₁ H
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1
  have hcan := theorem_15_4_1_cylinder_loc hd hf hft hsec hsec' o hoL hinvC hidx hΛ'
    hreg.2.2.2.2 e0 e1 honto
  have hk' := hcan.isKernelCanonical (canonContinuous_cubeOrientation_loc Λ' hX hf hft hsec hsec' o hoL)
  have hP₀ := IsCanonicalFor.isKernelCanonical h₀ (canonContinuous_loc S₀.Λ hX hft hsec o hoL)
  have hP₁ := IsCanonicalFor.isKernelCanonical h₁ (canonContinuous_loc S₁.Λ hX hft hsec o hoL)
  have hconv₀ := cylinderKernelFrameConvention_of_isIndexAt_loc hf hft hsec hsec' o hidx
    (fun _ => 0)
  have hconv₁ := cylinderKernelFrameConvention_of_isIndexAt_loc hf hft hsec hsec' o hidx
    (fun _ => 1)
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have hm₀ := Adm.exists_areMatchedAt_of_kernelCanonical hd hf hft S₀ hΛ' e0 e1 honto (i := 0)
    (Or.inl ⟨z0, rfl⟩) e0 hΘ' hP₀ hk' hconv₀
  have hm₁ := Adm.exists_areMatchedAt_of_kernelCanonical hd hf hft S₁ hΛ' e0 e1 honto (i := 1)
    (Or.inr ⟨z1, rfl⟩) e1 hΘ' hP₁ hk' hconv₁
  refine ⟨Λ', hreg, hΘ', hcpt', _, hcan.1, hcan.loc,
    fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p,
    fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p, hcan, fun hLUC hLUCC => ⟨?_, ?_⟩,
    ?_, ?_⟩
  · exact Adm.isLocalEndIdentityEff_of_matched hLUC hLUCC S₀ hΘ' hcpt' hcan.1 hcan.loc (i := 0) _
      hm₀
  · exact Adm.isLocalEndIdentityEff_of_matched hLUC hLUCC S₁ hΘ' hcpt' hcan.1 hcan.loc (i := 1) _
      hm₁
  · exact Adm.isLocalEndIdentity_of_matched S₀ hΘ' hcpt' hcan.1 hcan.loc (i := 0) _ hm₀
  · exact Adm.isLocalEndIdentity_of_matched S₁ hΘ' hcpt' hcan.1 hcan.loc (i := 1) _ hm₁

include hd hoL hinvC hidx in
/-- **2021 Corollary 15.4.4, p. 703 (2017: Corollary 15.2), over all transversal perturbations
with `N(Λ) ≤ 1`.**  Let `d_X ≡ 0`, `|X|` be paracompact, the cylinder carry the local families `H`, and
`(f, o)` be an oriented sc-Fredholm section functor with tame germ data and index `m + 1`, with
`õ = e ∧ o` invariant under the morphisms of the cylinder.  Let `S₀`, `S₁` be the solution sets
of transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)` (the perturbations of Theorem 15.4.3: sc⁺,
dom-supp in `Uⁱ`, `Nⁱ(Λⁱ) ≤ 1`, `(f, Λⁱ)` transversal; not assumed structurable) with the canonical
orientation of `(f, o)`.  Then `∫_{S₀} ω = ∫_{S₁} ω` for every closed `ω ∈ Ω^{m+1}_{ep,∞}(X)`.
No partitions of unity are assumed (Stokes on `[0, 1] × X` is `EP.theorem_9_5_17_all`). -/
theorem integral_eq_of_isTransversalPerturbation_loc (hpara : A.X.HasParacompactOrbitSpace)
    {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (H : ∀ x ∉ (A.cubeSEP 1).X.PObj.boundary,
      0 < cylExtension S₀.Λ S₁.Λ (cubeLiftEp (n := 1) f hf.1.1.1 x) →
      ∃ Q : Set (A.cubeSEP 1).Obj, IsOpen Q ∧ (A.cubeSEP 1).X.IsSaturated Q ∧ x ∈ Q ∧
        Nonempty (RelGPFamily (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
          (cylExtension S₀.Λ S₁.Λ) (collarAuxNorm A N₀ N₁)
          (interpSet A U₀ U₁ ∩ (A.cubeSEP 1).X.PObj.boundaryᶜ)
          (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
            pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension S₀.Λ S₁.Λ) z) Q))
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integral ω = S₁.integral ω := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, -, hl₀, hl₁⟩ :=
    exists_cylinder_local_ends_transversal_loc hd hf hft hsec hsec' o hoL hinvC hidx hpara
      hr₀ hr₁ h₀ h₁ H
  have hS := (A.cubeSEP 1).baseEP.theorem_9_5_17_all (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
  have hdω : (A.cubeSEP 1).baseEP.epFormsInftyD (m + 1)
      (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP)
        (A.X.cubeProj 1) (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hdω, tameBranchedIntegral_zero, boundaryMeasure_cyl_univ hd (Nat.succ_pos m) hΘ' hcpt' hT'
    hloc', Adm.boundaryMeasure_cylEnd_of_local S₀ hΘ' hcpt' hT' hloc' hover₀ hl₀ ω,
    Adm.boundaryMeasure_cylEnd_of_local S₁ hΘ' hcpt' hT' hloc' hover₁ hl₁ ω] at hS
  linarith

include hd hoL hinvC hidx in
/-- **2021 Corollary 15.4.4, effective version, p. 703, over all transversal perturbations with
`N(Λ) ≤ 1`**: under the hypotheses of `integral_eq_of_isTransversalPerturbation` and the local
unique continuation property on `X` and on `[0, 1] × X`, `∮_{S₀} ω = ∮_{S₁} ω` for every closed
`ω` (Stokes on `[0, 1] × X` is `EP.theorem_9_5_18_all`). -/
theorem integralEff_eq_of_isTransversalPerturbation_loc (hpara : A.X.HasParacompactOrbitSpace)
    (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (H : ∀ x ∉ (A.cubeSEP 1).X.PObj.boundary,
      0 < cylExtension S₀.Λ S₁.Λ (cubeLiftEp (n := 1) f hf.1.1.1 x) →
      ∃ Q : Set (A.cubeSEP 1).Obj, IsOpen Q ∧ (A.cubeSEP 1).X.IsSaturated Q ∧ x ∈ Q ∧
        Nonempty (RelGPFamily (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
          (cylExtension S₀.Λ S₁.Λ) (collarAuxNorm A N₀ N₁)
          (interpSet A U₀ U₁ ∩ (A.cubeSEP 1).X.PObj.boundaryᶜ)
          (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
            pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension S₀.Λ S₁.Λ) z) Q))
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integralEff hLUC ω = S₁.integralEff hLUC ω := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, hl, -, -⟩ :=
    exists_cylinder_local_ends_transversal_loc hd hf hft hsec hsec' o hoL hinvC hidx hpara
      hr₀ hr₁ h₀ h₁ H
  have hS := (A.cubeSEP 1).baseEP.theorem_9_5_18_all (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
  have hdω : (A.cubeSEP 1).baseEP.epFormsInftyD (m + 1)
      (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP)
        (A.X.cubeProj 1) (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hdω, tameBranchedIntegralEff_zero, boundaryMeasureEff_cyl_univ hd (Nat.succ_pos m) hLUCC
    hΘ' hcpt' hT' hloc',
    Adm.boundaryMeasureEff_cylEnd_of_local hLUC hLUCC S₀ hΘ' hcpt' hT' hloc' hover₀
      (hl hLUC hLUCC).1 ω,
    Adm.boundaryMeasureEff_cylEnd_of_local hLUC hLUCC S₁ hΘ' hcpt' hT' hloc' hover₁
      (hl hLUC hLUCC).2 ω] at hS
  linarith

end Transversal

end SBLocalization

end Polyfold
