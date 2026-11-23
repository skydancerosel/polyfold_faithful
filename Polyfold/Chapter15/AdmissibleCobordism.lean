import Polyfold.Chapter15.AdmissibleCylinderEnds
import Polyfold.Chapter9.StokesLocalPartitions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.3** and **Corollary 15.4.4** (2017: Theorem 15.7, Corollary 15.2), for the
perturbations of Theorem 15.4.3: sc⁺, `N(Λ) ≤ 1`, transversal, structurability not assumed.

# Corollary 15.4.4 over all transversal perturbations with `N(Λ) ≤ 1`

## The text, paraphrased

(Theorem 15.4.3) For `Λ` with dom-supp in `U`, `N(Λ) ≤ 1` and `T(f, Λ)` onto, `Θ = Λ ∘ f` is a
compact tame branched ep⁺-subgroupoid, canonically oriented by `(f, o)`.  (Corollary 15.4.4)
`Φ_{(f,o)}([ω]) = ∫_{(Λ ∘ f, o)} ω` does not depend on the regular perturbation `(N, U, Λ)`; the
proof joins two structurable regular perturbations by the cobordism of Corollary 15.3.10 (3).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `Adm.boundaryMeasureEff_cylEnd_of_local`: the effective end identity from its local form.
* `exists_cylinder_local_ends_transversal`: two canonically oriented solution sets of transversal
  perturbations `(Nⁱ, Uⁱ, Λⁱ)` are the ends of a canonically oriented compact tame `Θ̃` on
  `[0, 1] × X` (`corollary_15_3_10_3_transversal`, Theorem 15.4.1 on the cylinder), with the local
  end identities.
* **`integral_eq_of_isTransversalPerturbation`**,
  **`integralEff_eq_of_isTransversalPerturbation`**: a closed form has the same `∫` and the same
  `∮` over the canonically oriented solution sets of any two transversal perturbations.  Stokes
  on the cylinder is `EP.theorem_9_5_17_all`, `EP.theorem_9_5_18_all` (Remark 9.5.19); no
  partitions of unity are assumed.

## Reading

The perturbations are those of Theorem 15.4.3 with `d_X ≡ 0`.  The pair `(N, U)` may differ for the
two perturbations, as in Corollary 15.3.10 (2).
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

/-- **The effective end identity from the local end identity**: the effective boundary measure
of `pr^*ω` on the whole end `i` is `ε · ∮_{Θ} ω`. -/
theorem Adm.boundaryMeasureEff_cylEnd_of_local {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedSolution A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : Adm.IsLocalEndIdentityEff hLUC hLUCC P hΘ' hcpt' hT' hloc' i ε hover)
    (ω : A.baseEP.epFormsInfty (m + 1)) :
    (A.cubeSEP 1).baseEP.boundaryMeasureEff (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' i) =
      ε * P.integralEff hLUC ω := by
  have : CompactSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) :=
    isCompact_iff_compactSpace.1 P.isCompact
  rw [P.integralEff_eq_measureEff_univ]
  exact signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ') _ _
    (A.X.isClosed_cylEnd Θ' i) (cylEndProj hover) (continuous_cylEndProj hover) ε (h ω)

section Transversal

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

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
include hd ho hinvC hidx in
/-- **The canonically oriented cobordism between two transversal perturbations**: for `d_X ≡ 0`,
`|X|` paracompact and sc-smooth bump functions, let `S₀`, `S₁` be oriented solution sets of
transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)` (sc⁺, `Nⁱ(Λⁱ) ≤ 1`, not assumed structurable) with the
canonical orientation of `(f, o)`.  Then there is an sc⁺-multisection `Λ̃` on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `t = i`, `Θ̃ = Λ̃ ∘ f̃` compact and branched, and the canonical orientation `T̃` of
`(f̃, õ)` on `Θ̃`, described by oriented tame structures of dimension `m + 2`, with
`∂Θ̃ = Θ₁ ⊔ −Θ₀` on the level of the local end identities. -/
theorem exists_cylinder_local_ends_transversal (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T) :
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
  have hbump' : A.X.PObj.AdmitsBumpFunctions := A.X.theorem_12_3_2_1.1 hbump
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump'
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  obtain ⟨Λ', hreg, e0, e1, -, hΘ', hcpt'⟩ :=
    corollary_15_3_10_3_transversal hd hpara hbump hf hft hr₀ hr₁
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1
  have hcan := theorem_15_4_1_cylinder hd hbump' hf hft hsec hsec' o ho hinvC hidx hΛ'
    hreg.2.2.2.2 e0 e1 honto
  have hk' := hcan.isKernelCanonical (canonContinuous Λ' hXC hbumpC hftC hsec'
    (cubeOrientation hf hft hsec o) (isSectionOrientation_cubeOrientation hX hbump' hf hft ho))
  have hP₀ := IsCanonicalFor.isKernelCanonical h₀ (canonContinuous S₀.Λ hX hbump' hft hsec o ho)
  have hP₁ := IsCanonicalFor.isKernelCanonical h₁ (canonContinuous S₁.Λ hX hbump' hft hsec o ho)
  have hconv₀ := cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump'
    (fun _ => 0)
  have hconv₁ := cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump'
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

include hd ho hinvC hidx in
/-- **2021 Corollary 15.4.4, p. 703 (2017: Corollary 15.2), over all transversal perturbations
with `N(Λ) ≤ 1`.**  Let `d_X ≡ 0`, `|X|` be paracompact, `X` admit sc-smooth bump functions, and
`(f, o)` be an oriented sc-Fredholm section functor with tame germ data and index `m + 1`, with
`õ = e ∧ o` invariant under the morphisms of the cylinder.  Let `S₀`, `S₁` be the solution sets
of transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)` (the perturbations of Theorem 15.4.3: sc⁺,
dom-supp in `Uⁱ`, `Nⁱ(Λⁱ) ≤ 1`, `(f, Λⁱ)` transversal; not assumed structurable) with the canonical
orientation of `(f, o)`.  Then `∫_{S₀} ω = ∫_{S₁} ω` for every closed `ω ∈ Ω^{m+1}_{ep,∞}(X)`.
No partitions of unity are assumed (Stokes on `[0, 1] × X` is `EP.theorem_9_5_17_all`). -/
theorem integral_eq_of_isTransversalPerturbation (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integral ω = S₁.integral ω := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, -, hl₀, hl₁⟩ :=
    exists_cylinder_local_ends_transversal hd hf hft hsec hsec' o ho hinvC hidx hpara hbump
      hr₀ hr₁ h₀ h₁
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

include hd ho hinvC hidx in
/-- **2021 Corollary 15.4.4, effective version, p. 703, over all transversal perturbations with
`N(Λ) ≤ 1`**: under the hypotheses of `integral_eq_of_isTransversalPerturbation` and the local
unique continuation property on `X` and on `[0, 1] × X`, `∮_{S₀} ω = ∮_{S₁} ω` for every closed
`ω` (Stokes on `[0, 1] × X` is `EP.theorem_9_5_18_all`). -/
theorem integralEff_eq_of_isTransversalPerturbation (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integralEff hLUC ω = S₁.integralEff hLUC ω := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, hl, -, -⟩ :=
    exists_cylinder_local_ends_transversal hd hf hft hsec hsec' o ho hinvC hidx hpara hbump
      hr₀ hr₁ h₀ h₁
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
