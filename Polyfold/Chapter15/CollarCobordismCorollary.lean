import Polyfold.Chapter15.CylinderOrientationInvariance
import Polyfold.Chapter15.CylinderExtensionBump
import Polyfold.Chapter15.CylinderEndEffectiveMatching

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) with the cobordism of **Corollary 15.3.10 (3)**
(p. 699) built from bump functions.

# Corollary 15.4.4 with partitions of unity only for Stokes

## The text, paraphrased

(p. 703) For two regular perturbations `Λ₀`, `Λ₁` of `f` with their canonical orientations,
Corollary 15.3.10 (3) gives a regular perturbation `Λ̃` of `f̃` on `[0, 1] × X` with `Λ̃ = Λᵢ` over
`{i} × X`; `Θ̃ = Λ̃ ∘ f̃` is canonically oriented by `(f̃, õ)`, `∂Θ̃ = Θ₁ ⊔ −Θ₀`, and Stokes on
`Θ̃` gives the invariance of the integrals.

## What is formalized (namespace `Polyfold.SBLocalization`)

The cobordism is the one of `corollary_15_3_10_3_collar`: the explicit structurable extension
`(β₀ ∘ t) ⊙ pr^*Λ₀ ⊕ (β₁ ∘ t) ⊙ pr^*Λ₁` followed by the relative step from bump functions,
for the collar norm `collarAuxNorm`.  Neither Theorem 14.1.9 nor partitions of unity enter this
step.  Theorem 15.4.1 on the cylinder (`theorem_15_4_1_cylinder`) and the end identities
(`exists_areMatchedAt_of_kernelCanonical`) do not depend on the auxiliary norm.

* **`hasOrientedCobordism_collar`**, `hasOrientedCobordismEff_collar`: two canonically oriented
  regular perturbations are joined by an oriented compact cobordism on `[0, 1] × X`, for `d_X ≡ 0`,
  `|X|` paracompact, bump functions, and partitions of unity on `[0, 1] × X` (Stokes there).
* **`corollary_15_4_4_collar`**, `corollary_15_4_4_eff_collar`: Corollary 15.4.4 for the canonical
  orientations (Definition 15.4.2), with sc-smooth partitions of unity on `X` and on `[0, 1] × X`
  (the hypotheses of Theorems 9.5.17, 9.5.18 for the two Stokes steps) and no other use of them.
  No compactness hypothesis on the solution set is needed: compactness of `Θᵢ` is part of the
  regular perturbations.
* **`corollary_15_4_4_collar_of_admits`**, `corollary_15_4_4_eff_collar_of_admits`: the same with
  the single hypothesis that the object M-polyfold of `X` admits sc-smooth partitions of unity
  (Theorem 7.5.7 gives Definition 7.5.5 on `X` and on `[0, 1] × X`).
* **`corollary_15_4_4_oriented_collar`**, `corollary_15_4_4_eff_oriented_collar`: for an oriented
  `(f, o)` (`φ_* o = o`), the invariance of `õ = e ∧ o` being `isOrInvariant_cubeOrientation`.

## Reading

As in `corollary_15_4_4_canonicalOrientation`: the index of `f` is `m + 1` at every smooth point,
and "`(f, o)` oriented" is Definition 6.6.16 together with the invariance of Definition 12.5.4.
Partitions of unity remain only as the hypothesis of Stokes (Theorems 9.5.17, 9.5.18); whether
they can be dropped there is the question of Remark 9.5.19.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

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

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
include hd ho hinvC hidx in
/-- **The canonically oriented cobordism from the collar extension**: for `d_X ≡ 0`, `|X|`
paracompact and sc-smooth bump functions, every two regular perturbations `P₀`, `P₁` with the
canonical orientation of `(f, o)` have a regular perturbation `Λ̃` of `f̃` on `[0, 1] × X` (for
the collar norm, `corollary_15_3_10_3_collar`) with `Λ̃ = Λᵢ` over `t = i`, `Θ̃ = Λ̃ ∘ f̃` compact
and branched, and an orientation `T̃` of `Θ̃` (the canonical one of `(f̃, õ)`) described by
oriented tame structures of dimension `m + 2`, with `∂Θ̃ = Θ₁ ⊔ −Θ₀` on the level of the local
end identities. -/
theorem exists_collar_local_ends (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h₀ : IsCanonicalPerturbation hf.2 hsec o P₀) (h₁ : IsCanonicalPerturbation hf.2 hsec o P₁) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (collarAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' ∧
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
          cylEndMap p ∈ A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ)))
        (hover₁ : ∀ p : cylEnd (X := A.X)
            (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) 1,
          cylEndMap p ∈ A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ))),
        IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
            (cubeOrientation hf hft hsec o) (m + 1 + 1) T' ∧
          (∀ (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC),
            IsLocalEndIdentityEff hLUC hLUCC P₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀ ∧
              IsLocalEndIdentityEff hLUC hLUCC P₁ hΘ' hcpt' hT' hloc' 1 1 hover₁) ∧
          IsLocalEndIdentity P₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀ ∧
          IsLocalEndIdentity P₁ hΘ' hcpt' hT' hloc' 1 1 hover₁ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbump' : A.X.PObj.AdmitsBumpFunctions := A.X.theorem_12_3_2_1.1 hbump
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump'
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  obtain ⟨Λ', hreg, e0, e1, hΘ', hcpt'⟩ :=
    corollary_15_3_10_3_collar hd hpara hbump hf hft P₀.isRegular P₁.isRegular
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have hcan := theorem_15_4_1_cylinder hd hbump' hf hft hsec hsec' o ho hinvC hidx hΛ'
    hreg.2.2.2.2 e0 e1 honto
  have hk' := hcan.isKernelCanonical (canonContinuous Λ' hXC hbumpC hftC hsec'
    (cubeOrientation hf hft hsec o) (isSectionOrientation_cubeOrientation hX hbump' hf hft ho))
  have hP₀ := IsCanonicalFor.isKernelCanonical h₀ (canonContinuous P₀.Λ hX hbump' hft hsec o ho)
  have hP₁ := IsCanonicalFor.isKernelCanonical h₁ (canonContinuous P₁.Λ hX hbump' hft hsec o ho)
  have hconv₀ := cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump'
    (fun _ => 0)
  have hconv₁ := cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump'
    (fun _ => 1)
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have hm₀ := exists_areMatchedAt_of_kernelCanonical hd hf hft P₀ hΛ' e0 e1 honto (i := 0)
    (Or.inl ⟨z0, rfl⟩) e0 hΘ' hP₀ hk' hconv₀
  have hm₁ := exists_areMatchedAt_of_kernelCanonical hd hf hft P₁ hΛ' e0 e1 honto (i := 1)
    (Or.inr ⟨z1, rfl⟩) e1 hΘ' hP₁ hk' hconv₁
  refine ⟨Λ', hreg, hΘ', hcpt', _, hcan.1, hcan.loc,
    fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p,
    fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p, hcan, fun hLUC hLUCC => ⟨?_, ?_⟩,
    ?_, ?_⟩
  · exact isLocalEndIdentityEff_of_matched hLUC hLUCC P₀ hΘ' hcpt' hcan.1 hcan.loc (i := 0) _ hm₀
  · exact isLocalEndIdentityEff_of_matched hLUC hLUCC P₁ hΘ' hcpt' hcan.1 hcan.loc (i := 1) _ hm₁
  · exact isLocalEndIdentity_of_matched P₀ hΘ' hcpt' hcan.1 hcan.loc (i := 0) _ hm₀
  · exact isLocalEndIdentity_of_matched P₁ hΘ' hcpt' hcan.1 hcan.loc (i := 1) _ hm₁

include hd ho hinvC hidx in
/-- **The oriented cobordism of Corollary 15.4.4 from the collar extension**: for `d_X ≡ 0`, `|X|`
paracompact, sc-smooth bump functions and sc-smooth partitions of unity on `[0, 1] × X` (Stokes on
the cobordism), any two regular perturbations with the canonical orientation of `(f, o)` are
joined by an oriented compact cobordism (`Y = [0, 1] × X`, `F = pr`). -/
theorem hasOrientedCobordism_collar (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hPUC : (A.cubeSEP 1).X.HasScPartitionsOfUnity)
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h₀ : IsCanonicalPerturbation hf.2 hsec o P₀) (h₁ : IsCanonicalPerturbation hf.2 hsec o P₁) :
    P₀.HasOrientedCobordism P₁ := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, -, hl₀, hl₁⟩ :=
    exists_collar_local_ends hd hf hft hsec hsec' o ho hinvC hidx hpara hbump h₀ h₁
  exact hasOrientedCobordism_of_cylinder hd hPUC hΘ' hcpt' hT' hloc'
    (isCylinderBoundaryOf_of_local P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁ hl₀ hl₁)

include hd ho hinvC hidx in
/-- **The effective oriented cobordism from the collar extension**: as
`hasOrientedCobordism_collar`, with the local unique continuation property on `X` and on
`[0, 1] × X`. -/
theorem hasOrientedCobordismEff_collar (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.HasScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h₀ : IsCanonicalPerturbation hf.2 hsec o P₀) (h₁ : IsCanonicalPerturbation hf.2 hsec o P₁) :
    P₀.HasOrientedCobordismEff hLUC P₁ := by
  obtain ⟨Λ', -, hΘ', hcpt', T', hT', hloc', hover₀, hover₁, -, hl, -, -⟩ :=
    exists_collar_local_ends hd hf hft hsec hsec' o ho hinvC hidx hpara hbump h₀ h₁
  exact hasOrientedCobordismEff_of_cylinder hd hLUC hPUC hLUCC hΘ' hcpt' hT' hloc'
    (isCylinderBoundaryEffOf_of_local hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁
      (hl hLUC hLUCC).1 (hl hLUC hLUCC).2)

include hd ho hinvC hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2), partitions of unity only for
Stokes.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` and `[0, 1] × X` with sc-smooth partitions of
unity (Definition 7.5.5; the hypothesis of Theorem 9.5.17 on `X` and on the cobordism), and
`(f, o)` an oriented sc-Fredholm section functor with tame germ data and index `m + 1`, with
`õ = e ∧ o` invariant under the morphisms of the cylinder.  Then exact forms integrate to `0`
over every regular perturbation with the canonical orientation of `(f, o)` (Definition 15.4.2),
and a closed form has the same integral over any two of them.  The cobordism comes from the
collar extension (`corollary_15_3_10_3_collar`, bump functions only); the bump functions come
from the partitions of unity on `X`. -/
theorem corollary_15_4_4_collar (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.HasScPartitionsOfUnity) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_hyp hPU hd _ fun _ _ h₀ h₁ =>
    hasOrientedCobordism_collar hd hf hft hsec hsec' o ho hinvC hidx hpara
      (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU) hPUC h₀ h₁

include hd ho hinvC hidx in
/-- **Corollary 15.4.4, effective version (p. 703), partitions of unity only for Stokes**: the
effective form of `corollary_15_4_4_collar`, with the local unique continuation property on `X`
and on `[0, 1] × X` (Theorem 9.5.18). -/
theorem corollary_15_4_4_eff_collar (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.HasScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_hyp hPU hLUC hd _ fun _ _ h₀ h₁ =>
    hasOrientedCobordismEff_collar hd hf hft hsec hsec' o ho hinvC hidx hpara
      (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU) hLUC hPUC hLUCC
      h₀ h₁

include hd ho hinvC hidx in
/-- **Corollary 15.4.4 with one partition-of-unity hypothesis**: `corollary_15_4_4_collar` when
the object M-polyfold of `X` admits sc-smooth partitions of unity (Definition 5.5.1); Theorem
7.5.7 gives Definition 7.5.5 on `X` and on `[0, 1] × X` (`admitsScPartitionsOfUnity_cubeSEP`). -/
theorem corollary_15_4_4_collar_of_admits (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_collar hd hf hft hsec hsec' o ho hinvC hidx hpara (A.X.theorem_7_5_7 hpara hPU)
    (hasScPartitionsOfUnity_cyl hpara (admitsScPartitionsOfUnity_cubeSEP 1 hPU))

include hd ho hinvC hidx in
/-- **Corollary 15.4.4, effective version, with one partition-of-unity hypothesis**: the
effective form of `corollary_15_4_4_collar_of_admits`. -/
theorem corollary_15_4_4_eff_collar_of_admits (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_collar hd hf hft hsec hsec' o ho hinvC hidx hpara
    (A.X.theorem_7_5_7 hpara hPU) hLUC
    (hasScPartitionsOfUnity_cyl hpara (admitsScPartitionsOfUnity_cubeSEP 1 hPU)) hLUCC

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
functor, partitions of unity only for Stokes.**  Let `d_X ≡ 0`, `|X|` paracompact, the object
M-polyfold of `X` admit sc-smooth partitions of unity, and `(f, o)` be an oriented sc-Fredholm
section functor (`o` an orientation of `f` with `φ_* o_{s(φ)} = o_{t(φ)}`) with tame germ data
and index `m + 1`.  Then exact forms integrate to `0` over every regular perturbation with the
canonical orientation of `(f, o)`, and a closed form has the same integral over any two of them.
Compared with `corollary_15_4_4_oriented`: no compact solution set hypothesis, and one
partition-of-unity hypothesis, used for Stokes on `X` and on `[0, 1] × X` only. -/
theorem corollary_15_4_4_oriented_collar (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_collar_of_admits hd hf hft hsec hsec' o ho
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hidx hpara hPU

include hd hft hsec' ho hinv hidx in
/-- **Corollary 15.4.4, effective version (p. 703), for an oriented sc-Fredholm section
functor, partitions of unity only for Stokes**: the effective form of
`corollary_15_4_4_oriented_collar`. -/
theorem corollary_15_4_4_eff_oriented_collar (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_collar_of_admits hd hf hft hsec hsec' o ho
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hidx hpara hPU hLUC hLUCC

end Oriented

end SBLocalization

end Polyfold
