import Polyfold.Chapter16.IndexZeroNoBumpsCobordism
import Polyfold.Chapter16.IndexZeroNoBumpsPointPull
import Polyfold.Chapter15.RestrictedCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** for Fredholm index `0`, for transversal perturbations with `N(Λ) ≤ 1`,
without sc-smooth bump functions on `X`; with Definition 9.5.6 for `n = 0` and Theorems 11.4.1,
11.4.2 (pp. 543–544).

# Corollary 15.4.4 for index `0` through the restriction to a neighbourhood of the compact set

## The text, paraphrased

(Corollary 15.4.4) The weighted signed count of a closed `0`-form over `Λ ∘ f` does not depend on
the perturbation.  The proof perturbs the cylinder `[0, 1] × X` near a compact set; only a
neighbourhood of that set enters.

## What is formalized

Namespace `Polyfold.EP`:
* `isPointTame_sub`, **`pointBranchedIntegral_sub`**, **`pointBranchedIntegralEff_sub`**: for
  `Θ̂` tame of dimension `0` and compact with `supp Θ ⊆ V`, `V` saturated and open,
  `i : X|V → X` the inclusion: `i^*Θ̂` is tame of dimension `0`, and `∫_Θ̂ ω = ∫_{i^*Θ̂} i^*ω`,
  `∮_Θ̂ ω = ∮_{i^*Θ̂} i^*ω` for `0`-forms.

Namespace `Polyfold.SBLocalization`:
* `PointSolution.restr`, **`PointSolution.count_restr`**, **`PointSolution.countEff_restr`**:
  the point solution set `(Λ|V, i^*T̂)` of `f|V` and its counts.
* **`pointCount_eq_of_isTransversalPerturbation_restr`**: with local families on the cylinder of
  a restriction `X|V` (`HasRestrictedCylinderFamilies`), a closed `0`-form has the same count and
  the same effective count over the canonically oriented point solution sets of two transversal
  perturbations.  The orientation of `f` is continuous in the local orientation sets and
  invariant under the morphisms.  No bump functions on `X` are assumed.

## Reading

Everything is carried to `X|V` as in `Polyfold/Chapter15/RestrictedCobordism.lean`; on `X|V` the
statement is `pointCount_eq_of_isTransversalPerturbation_loc`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace EP

open MPolyfold EpGroupoid

variable (A : EP.{u}) {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V) {Θ : A.Obj → ℚ}
  {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **`i^*Θ̂` is tame of dimension `0`** for the inclusion `i : X|V → X`. -/
theorem isPointTame_sub (hVo : IsOpen V) (hΘ : A.X.IsFunctorial Θ) (hT : A.X.IsGrHatSection T)
    (hloc : A.X.IsPointTame Θ T) :
    (A.sub hV).X.IsPointTame ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T) :=
  EpFunctor.isPointTame_pullSection_of (A.isLocalScDiffeo_subFunctor_obj hV hVo)
    (A.bijective_isotropyHom_subFunctor hV) hΘ hT hloc

/-- **The weighted count over `Θ̂` with `supp Θ ⊆ V` is the weighted count over `i^*Θ̂` on `X|V`**
(Definition 9.5.6 (1) for `n = 0`, Theorem 11.4.1): `∫_Θ̂ ω = ∫_{i^*Θ̂} i^*ω`. -/
theorem pointBranchedIntegral_sub (hVo : IsOpen V)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T) (hsupp : supp Θ ⊆ V)
    (hΘ₁ : (A.sub hV).X.IsBranchedEpSubgroupoid ((A.subFunctor hV).pullbackTheta Θ))
    (hcpt₁ : (A.sub hV).X.IsCompactBranched ((A.subFunctor hV).pullbackTheta Θ))
    (hT₁ : (A.sub hV).X.IsOrientation ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T))
    (hloc₁ : (A.sub hV).X.IsPointTame ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T))
    (ω : A.epFormsInfty 0) :
    A.pointBranchedIntegral hΘ hcpt hT hloc ω =
      (A.sub hV).pointBranchedIntegral hΘ₁ hcpt₁ hT₁ hloc₁
        (epFormsInftyPullback (A.subFunctor hV) 0 ω) := by
  have hd := A.isLocalScDiffeo_subFunctor_obj hV hVo
  exact (EpFunctor.pointIntegral_pull_of (A := A.sub hV) (B := A) hd
    (A.subFunctor_full hV) (A.bijective_isotropyHom_subFunctor hV) hΘ hcpt hT hloc
    (A.orbitSupp_subset_range_subFunctor hV hsupp) hΘ₁ hcpt₁ hT₁
    (fun Tc => Tc.pullSection_Q hd hT.isGrHatSection) hloc₁ ω).symm

/-- **The effective weighted count over `Θ̂` with `supp Θ ⊆ V` is the effective weighted count
over `i^*Θ̂` on `X|V`** (Definition 9.5.6 (2) for `n = 0`, Theorem 11.4.2), for `X` with the
local unique continuation property: `∮_Θ̂ ω = ∮_{i^*Θ̂} i^*ω`. -/
theorem pointBranchedIntegralEff_sub (hVo : IsOpen V) (hLUC : A.X.IsLUC)
    (hLUC₁ : (A.sub hV).X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T) (hloc : A.X.IsPointTame Θ T) (hsupp : supp Θ ⊆ V)
    (hΘ₁ : (A.sub hV).X.IsBranchedEpSubgroupoid ((A.subFunctor hV).pullbackTheta Θ))
    (hcpt₁ : (A.sub hV).X.IsCompactBranched ((A.subFunctor hV).pullbackTheta Θ))
    (hT₁ : (A.sub hV).X.IsOrientation ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T))
    (hloc₁ : (A.sub hV).X.IsPointTame ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T))
    (ω : A.epFormsInfty 0) :
    A.pointBranchedIntegralEff hLUC hΘ hcpt hT hloc ω =
      (A.sub hV).pointBranchedIntegralEff hLUC₁ hΘ₁ hcpt₁ hT₁ hloc₁
        (epFormsInftyPullback (A.subFunctor hV) 0 ω) := by
  have hd := A.isLocalScDiffeo_subFunctor_obj hV hVo
  exact (EpFunctor.pointIntegralEff_pull_of (A := A.sub hV) (B := A) hd
    (A.subFunctor_full hV) (A.bijective_isotropyHom_subFunctor hV) hΘ hcpt hT
    (hloc.hasLUC hLUC) hLUC (A.orbitSupp_subset_range_subFunctor hV hsupp) hΘ₁ hcpt₁ hT₁
    (fun Tc => Tc.pullSection_Q hd hT.isGrHatSection) (hloc₁.hasLUC hLUC₁) ω).symm

end EP

namespace SBLocalization

open StrongBundle MPolyfold SEP EpGroupoid

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- The weighted count depends on `Θ` only. -/
theorem pointBranchedIntegral_congr_theta {B : EP.{u}} {Θa Θb : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (h : Θa = Θb)
    (hΘa : B.X.IsBranchedEpSubgroupoid Θa) (hca : B.X.IsCompactBranched Θa)
    (hTa : B.X.IsOrientation Θa T) (hla : B.X.IsPointTame Θa T)
    (hΘb : B.X.IsBranchedEpSubgroupoid Θb) (hcb : B.X.IsCompactBranched Θb)
    (hTb : B.X.IsOrientation Θb T) (hlb : B.X.IsPointTame Θb T) (ω : B.epFormsInfty 0) :
    B.pointBranchedIntegral hΘa hca hTa hla ω = B.pointBranchedIntegral hΘb hcb hTb hlb ω := by
  subst h
  rfl

/-- The effective weighted count depends on `Θ` only. -/
theorem pointBranchedIntegralEff_congr_theta {B : EP.{u}} {Θa Θb : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (h : Θa = Θb) (hLUC : B.X.IsLUC)
    (hΘa : B.X.IsBranchedEpSubgroupoid Θa) (hca : B.X.IsCompactBranched Θa)
    (hTa : B.X.IsOrientation Θa T) (hla : B.X.IsPointTame Θa T)
    (hΘb : B.X.IsBranchedEpSubgroupoid Θb) (hcb : B.X.IsCompactBranched Θb)
    (hTb : B.X.IsOrientation Θb T) (hlb : B.X.IsPointTame Θb T) (ω : B.epFormsInfty 0) :
    B.pointBranchedIntegralEff hLUC hΘa hca hTa hla ω =
      B.pointBranchedIntegralEff hLUC hΘb hcb hTb hlb ω := by
  subst h
  rfl

/-- **The point solution set `(Λ|V, i^*T̂)` of `f|V`** on the restriction `W|V → X|V` to a
saturated open set `V` containing `supp(Λ ∘ f)`. -/
def PointSolution.restr (hVo : IsOpen V) {f : A.Obj → A.W} (hf : IsSection A.P f)
    (P : PointSolution A f) (hsupp : EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) ⊆ V) :
    PointSolution (A.restr hV) (restrSec hV f hf) where
  Λ := restrMult hV P.Λ
  isScPlusMultisection := isScPlusMultisection_restrMult hV hVo P.isScPlusMultisection
  T := (A.baseEP.subFunctor hV).pullSection P.T
  isBranched := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isBranchedEpSubgroupoid_sub hV hVo P.isBranched P.isCompact hsupp
  isCompact := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isCompactBranched_sub hV hVo P.isBranched.isFunctorial P.isCompact hsupp
  isOrientation := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isOrientation_sub hV hVo P.isOrientation
  loc := by
    rw [restrMult_restrSec_eq_pullbackTheta hV hf]
    exact A.baseEP.isPointTame_sub hV hVo P.isBranched.isFunctorial
      P.isOrientation.isGrHatSection P.loc

@[simp] theorem PointSolution.restr_Λ (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) (P : PointSolution A f)
    (hsupp : EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) ⊆ V) :
    (P.restr hV hVo hf hsupp).Λ = restrMult hV P.Λ := rfl

@[simp] theorem PointSolution.restr_T (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) (P : PointSolution A f)
    (hsupp : EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) ⊆ V) :
    (P.restr hV hVo hf hsupp).T = (A.baseEP.subFunctor hV).pullSection P.T := rfl

/-- **The count of `i^*ω` over `(Λ|V ∘ f|V, i^*T̂)` is the count of `ω` over `(Λ ∘ f, T̂)`** for
`supp(Λ ∘ f) ⊆ V` (Definition 9.5.6 (1) for `n = 0`, Theorem 11.4.1). -/
theorem PointSolution.count_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) (P : PointSolution A f)
    (hsupp : EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) ⊆ V) (ω : A.baseEP.epFormsInfty 0) :
    (P.restr hV hVo hf hsupp).count
        (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) 0 ω) = P.count ω := by
  have hΘ₁ := A.baseEP.isBranchedEpSubgroupoid_sub hV hVo P.isBranched P.isCompact hsupp
  have hc₁ := A.baseEP.isCompactBranched_sub hV hVo P.isBranched.isFunctorial P.isCompact hsupp
  have hT₁ := A.baseEP.isOrientation_sub hV hVo P.isOrientation
  have hl₁ := A.baseEP.isPointTame_sub hV hVo P.isBranched.isFunctorial
    P.isOrientation.isGrHatSection P.loc
  have e := A.baseEP.pointBranchedIntegral_sub hV hVo P.isBranched P.isCompact P.isOrientation
    P.loc hsupp hΘ₁ hc₁ hT₁ hl₁ ω
  refine Eq.trans ?_ e.symm
  exact pointBranchedIntegral_congr_theta (B := A.baseEP.sub hV)
    (restrMult_restrSec_eq_pullbackTheta hV hf P.Λ)
    (P.restr hV hVo hf hsupp).isBranched (P.restr hV hVo hf hsupp).isCompact
    (P.restr hV hVo hf hsupp).isOrientation (P.restr hV hVo hf hsupp).loc hΘ₁ hc₁ hT₁ hl₁ _

/-- **The effective count of `i^*ω` over `(Λ|V ∘ f|V, i^*T̂)` is the effective count of `ω` over
`(Λ ∘ f, T̂)`** for `supp(Λ ∘ f) ⊆ V` (Definition 9.5.6 (2) for `n = 0`, Theorem 11.4.2), for
`X` with the local unique continuation property (then `X|V` has it, `isLUC_restr`). -/
theorem PointSolution.countEff_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : IsSection A.P f) (hLUC : A.X.IsLUC) (P : PointSolution A f)
    (hsupp : EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) ⊆ V) (ω : A.baseEP.epFormsInfty 0)
    (hLUC₁ : (A.restr hV).X.IsLUC) :
    (P.restr hV hVo hf hsupp).countEff hLUC₁
        (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) 0 ω) = P.countEff hLUC ω := by
  have hΘ₁ := A.baseEP.isBranchedEpSubgroupoid_sub hV hVo P.isBranched P.isCompact hsupp
  have hc₁ := A.baseEP.isCompactBranched_sub hV hVo P.isBranched.isFunctorial P.isCompact hsupp
  have hT₁ := A.baseEP.isOrientation_sub hV hVo P.isOrientation
  have hl₁ := A.baseEP.isPointTame_sub hV hVo P.isBranched.isFunctorial
    P.isOrientation.isGrHatSection P.loc
  have e := A.baseEP.pointBranchedIntegralEff_sub hV hVo hLUC hLUC₁ P.isBranched P.isCompact
    P.isOrientation P.loc hsupp hΘ₁ hc₁ hT₁ hl₁ ω
  refine Eq.trans ?_ e.symm
  exact pointBranchedIntegralEff_congr_theta (B := A.baseEP.sub hV)
    (restrMult_restrSec_eq_pullbackTheta hV hf P.Λ) hLUC₁
    (P.restr hV hVo hf hsupp).isBranched (P.restr hV hVo hf hsupp).isCompact
    (P.restr hV hVo hf hsupp).isOrientation (P.restr hV hVo hf hsupp).loc hΘ₁ hc₁ hT₁ hl₁ _

section Restr

variable {f : A.Obj → A.W} (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (hinv : A.E.IsOrInvariant hf hsec o)
  (hoL : IsSectionOrientationLoc (A.X.isTame_of_degIndex_eq_zero hd) hft
    fun y hy => orxLocEquiv hft hsec y hy (o y hy))
  (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)

set_option maxHeartbeats 1600000 in
-- the restricted bundle and its cylinder are unfolded in the hypotheses
include hd hinv hoL hidx in
/-- **2021 Corollary 15.4.4, p. 703, for Fredholm index `0` and transversal perturbations with
`N(Λ) ≤ 1`, without bump functions on `X`.**  Let `d_X ≡ 0`, `|X|` be paracompact, `(f, o)` be
an sc-Fredholm section functor with tame germ data and index `0`, with sc⁺-sections through the
smooth fibre points, `o` invariant under the morphisms and continuous in the local orientation
sets.  Let `P₀`, `P₁` be canonically oriented point solution sets of transversal perturbations
`(Nⁱ, Uⁱ, Λⁱ)`, and let the cylinder of a restriction `X|V` carry the local families
(`HasRestrictedCylinderFamilies`).  Then a closed `0`-form has the same weighted signed count
over `P₀` and `P₁`, and the same effective count when `X` has the local unique continuation
property. -/
theorem pointCount_eq_of_isTransversalPerturbation_restr
    (hpara : A.X.HasParacompactOrbitSpace)
    {P₀ P₁ : PointSolution A f} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ P₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ P₁.Λ)
    (h₀ : IsCanonicalFor P₀.Λ hf.2 hsec o 0 P₀.T) (h₁ : IsCanonicalFor P₁.Λ hf.2 hsec o 0 P₁.T)
    (hR : HasRestrictedCylinderFamilies A f hf N₀ N₁ U₀ U₁ P₀.Λ P₁.Λ)
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    P₀.count ω = P₁.count ω ∧ ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  obtain ⟨V, hV, hVo, hV₀, hV₁, H⟩ := hR
  have hX : A.X.PObj.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hd₁ := degIndex_restr_eq_zero hV hVo hd
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVo hf
  have hft₁ := isScFredholmSectionTame_restrSec hV hVo hf.1 hft
  have hsec₁ := hasScPlusSectionsThrough_restr hV hVo hsec
  have hsec₁' := hasScPlusSectionsThrough_cubeSEP hsec₁
  have hoL₁ := isSectionOrientationLoc_restrOr hV hVo hf hsec hX hft o hoL
  have hinv₁ := isOrInvariant_restrOr hV hVo hf hsec o hinv
  have hinvC₁ := isOrInvariant_cubeOrientation hF₁ hft₁ hsec₁ hsec₁' _ hinv₁
  have hidx₁ : ∀ x ∈ (A.restr hV).X.PObj.smoothSet,
      (A.restr hV).B.IsIndexAt (restrSec hV f hf.1.1.1) x 0 := fun x hx =>
    isIndexAt_restrSec hV hVo hf hsec (hidx _ (restrBase_mem_smoothSet hV hVo hx))
  have hpara₁ := hasParacompactOrbitSpace_restr hV hVo hpara
  have hs₀ := supp_subset_of_isTransversalPerturbation hf.1.1.1 hr₀ hV₀
  have hs₁ := supp_subset_of_isTransversalPerturbation hf.1.1.1 hr₁ hV₁
  have hr₀' := isTransversalPerturbation_restr hV hVo hf hr₀ hV₀
  have hr₁' := isTransversalPerturbation_restr hV hVo hf hr₁ hV₁
  have h₀' := IsCanonicalFor.restr hV hVo hf hsec hX hft hoL h₀
  have h₁' := IsCanonicalFor.restr hV hVo hf hsec hX hft hoL h₁
  have hω₁ : (A.restr hV).baseEP.epFormsInftyD 0
      (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) 0 ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := A.baseEP.sub hV) (B := A.baseEP)
        (A.baseEP.subFunctor hV) 0) ω
    simp only [LinearMap.comp_apply] at this
    rw [hω, map_zero] at this
    exact this
  obtain ⟨e, eE⟩ := pointCount_eq_of_isTransversalPerturbation_loc hd₁ hF₁ hft₁ hsec₁ hsec₁' _
    hoL₁ hinvC₁ hidx₁ hpara₁ (P₀ := P₀.restr hV hVo hf.1.1.1 hs₀)
    (P₁ := P₁.restr hV hVo hf.1.1.1 hs₁) hr₀' hr₁' h₀' h₁' H _ hω₁
  refine ⟨?_, fun hLUC => ?_⟩
  · rw [PointSolution.count_restr, PointSolution.count_restr] at e
    exact e
  · have e' := eE (isLUC_restr hV hVo hLUC)
    rw [PointSolution.countEff_restr hV hVo hf.1.1.1 hLUC,
      PointSolution.countEff_restr hV hVo hf.1.1.1 hLUC] at e'
    exact e'

end Restr

end SBLocalization

end Polyfold
