import Polyfold.Chapter15.AdmissibleCobordismLocal
import Polyfold.Chapter15.RestrictedOrientationCanonical
import Polyfold.Chapter15.RestrictedIntegralSolution
import Polyfold.Chapter15.RestrictedBundleCompactness
import Polyfold.Chapter15.RestrictedBundleGeneralPosition
import Polyfold.Chapter15.CubeSectionsThrough
import Polyfold.Chapter15.CylinderCobordismReduced

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4**, for transversal perturbations with `N(Λ) ≤ 1`, without sc-smooth bump
functions on `X`.

# Corollary 15.4.4 through the restriction to a neighbourhood of the compact set

## The text, paraphrased

(Corollary 15.4.4) `∫_{(Λ ∘ f, o)} ω` does not depend on the perturbation.  The proof perturbs the
cylinder `[0, 1] × X` near a compact set; only a neighbourhood of that set enters.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `HasRestrictedCylinderFamilies A f hf N₀ N₁ U₀ U₁ Λ₀ Λ₁`: there is a saturated open
  `V ⊇ {x ∈ Uⁱ | Nⁱ(f(x)) ≤ 1}` (closures in the orbit space) such that on the cylinder of the
  restriction `X|V` the explicit extension of the restricted end data has local families at the
  interior points of its solution set (the hypothesis of
  `corollary_15_3_10_3_transversal_of_families` for `A.restr hV`).
* **`integral_eq_of_isTransversalPerturbation_restr`**,
  **`integralEff_eq_of_isTransversalPerturbation_restr`**: with such a `V`, a closed form has the
  same `∫` and the same `∮` over the canonically oriented solution sets of two transversal
  perturbations.  The orientation of `f` is continuous in the local orientation sets and
  invariant under the morphisms.  No bump functions on `X` are assumed.

## Reading

Everything is carried to `X|V`: the section, the perturbations, the orientation
(`restrOr`), the canonical orientations (`IsCanonicalFor.restr`), and the integrals
(`OrientedSolution.integral_restr`); on `X|V` the statement is
`integral_eq_of_isTransversalPerturbation_loc`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold EpGroupoid SEP

variable {A : SEP.{u}} {f : A.Obj → A.W}

variable (A) in
/-- **Local families on the cylinder of a restriction `X|V`** to a saturated open neighbourhood
`V` of the sets cut out by the controlling pairs: the hypothesis of
`corollary_15_3_10_3_transversal_of_families` for the restricted data. -/
def HasRestrictedCylinderFamilies (f : A.Obj → A.W) (hf : A.E.IsScFredholmSectionFunctor f)
    (N₀ N₁ : A.B.One → ℝ) (U₀ U₁ : Set A.Obj) (Λ₀ Λ₁ : A.W → ℚ≥0) : Prop :=
  ∃ (V : Set A.Obj) (hV : A.X.IsEpSubgroupoid V) (_ : IsOpen V),
    A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ⊆ V ∧
    A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ⊆ V ∧
    ∀ x ∉ ((A.restr hV).cubeSEP 1).X.PObj.boundary,
      0 < cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)
        (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1) x) →
      ∃ Q : Set ((A.restr hV).cubeSEP 1).Obj, IsOpen Q ∧
        ((A.restr hV).cubeSEP 1).X.IsSaturated Q ∧ x ∈ Q ∧
        Nonempty (RelGPFamily ((A.restr hV).cubeSEP 1)
          (cubeLiftEp (n := 1) (restrSec hV f hf.1.1.1) (isSection_restrSec hV hf.1.1.1))
          (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁))
          (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
          (interpSet (A.restr hV) (restrBase hV ⁻¹' U₀) (restrBase hV ⁻¹' U₁) ∩
            ((A.restr hV).cubeSEP 1).X.PObj.boundaryᶜ)
          (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
            pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
              (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) z) Q)

section Restr

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (hinv : A.E.IsOrInvariant hf hsec o)
  (hoL : IsSectionOrientationLoc (A.X.isTame_of_degIndex_eq_zero hd) hft
    fun y hy => orxLocEquiv hft hsec y hy (o y hy))
  {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))

/-- The support of the solution set of a transversal perturbation lies in every set containing
the saturated closure of `{x ∈ U | N(f(x)) ≤ 1}`. -/
theorem supp_subset_of_isTransversalPerturbation {N : A.B.One → ℝ} {U : Set A.Obj}
    {Λ : A.W → ℚ≥0} (hsecf : IsSection A.P f) (hr : IsTransversalPerturbation A f N U Λ)
    {V : Set A.Obj}
    (hV : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1}) ⊆ V) :
    EpGroupoid.supp (fun z => (Λ (f z) : ℚ)) ⊆ V := by
  intro x hx
  have hpos : 0 < Λ (f x) := by exact_mod_cast hx
  have h := auxLe_of_pos hsecf hr.2.1 hr.1.2.2.2.1 hr.2.2.2.1 hr.2.2.1 hpos
  exact hV (subset_closure ⟨x, h, rfl⟩)

set_option maxHeartbeats 1600000 in
-- the restricted bundle and its cylinder are unfolded in the hypotheses
include hd hinv hoL hidx in
/-- **2021 Corollary 15.4.4, p. 703, for transversal perturbations with `N(Λ) ≤ 1`, without
bump functions on `X`.**  Let `d_X ≡ 0`, `|X|` be paracompact, `(f, o)` be an sc-Fredholm
section functor with tame germ data and index `m + 1`, with sc⁺-sections through the smooth
fibre points, `o` invariant under the morphisms and continuous in the local orientation sets.
Let `S₀`, `S₁` be canonically oriented solution sets of transversal perturbations
`(Nⁱ, Uⁱ, Λⁱ)`, and let the cylinder of a restriction `X|V` carry the local families
(`HasRestrictedCylinderFamilies`).  Then `∫_{S₀} ω = ∫_{S₁} ω` for every closed `ω`. -/
theorem integral_eq_of_isTransversalPerturbation_restr (hpara : A.X.HasParacompactOrbitSpace)
    {S₀ S₁ : OrientedSolution A f m} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (hR : HasRestrictedCylinderFamilies A f hf N₀ N₁ U₀ U₁ S₀.Λ S₁.Λ)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integral ω = S₁.integral ω := by
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
      (A.restr hV).B.IsIndexAt (restrSec hV f hf.1.1.1) x ((m + 1 : ℕ) : ℤ) := fun x hx =>
    isIndexAt_restrSec hV hVo hf hsec (hidx _ (restrBase_mem_smoothSet hV hVo hx))
  have hpara₁ := hasParacompactOrbitSpace_restr hV hVo hpara
  have hs₀ := supp_subset_of_isTransversalPerturbation hf.1.1.1 hr₀ hV₀
  have hs₁ := supp_subset_of_isTransversalPerturbation hf.1.1.1 hr₁ hV₁
  have hr₀' := isTransversalPerturbation_restr hV hVo hf hr₀ hV₀
  have hr₁' := isTransversalPerturbation_restr hV hVo hf hr₁ hV₁
  have h₀' := IsCanonicalFor.restr hV hVo hf hsec hX hft hoL h₀
  have h₁' := IsCanonicalFor.restr hV hVo hf hsec hX hft hoL h₁
  have hω₁ : (A.restr hV).baseEP.epFormsInftyD (m + 1)
      (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := A.baseEP.sub hV) (B := A.baseEP)
        (A.baseEP.subFunctor hV) (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [hω, map_zero] at this
    exact this
  have e := integral_eq_of_isTransversalPerturbation_loc hd₁ hF₁ hft₁ hsec₁ hsec₁' _ hoL₁
    hinvC₁ hidx₁ hpara₁ (S₀ := S₀.restr hV hVo hf.1.1.1 hs₀)
    (S₁ := S₁.restr hV hVo hf.1.1.1 hs₁) hr₀' hr₁' h₀' h₁' H _ hω₁
  rw [OrientedSolution.integral_restr, OrientedSolution.integral_restr] at e
  exact e

set_option maxHeartbeats 1600000 in
-- the restricted bundle and its cylinder are unfolded in the hypotheses
include hd hinv hoL hidx in
/-- **2021 Corollary 15.4.4, effective version, p. 703, without bump functions on `X`**: under
the hypotheses of `integral_eq_of_isTransversalPerturbation_restr` and the local unique
continuation property on `X`, `∮_{S₀} ω = ∮_{S₁} ω` for every closed `ω`. -/
theorem integralEff_eq_of_isTransversalPerturbation_restr
    (hpara : A.X.HasParacompactOrbitSpace) (hLUC : A.X.IsLUC)
    {S₀ S₁ : OrientedSolution A f m} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (hR : HasRestrictedCylinderFamilies A f hf N₀ N₁ U₀ U₁ S₀.Λ S₁.Λ)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integralEff hLUC ω = S₁.integralEff hLUC ω := by
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
      (A.restr hV).B.IsIndexAt (restrSec hV f hf.1.1.1) x ((m + 1 : ℕ) : ℤ) := fun x hx =>
    isIndexAt_restrSec hV hVo hf hsec (hidx _ (restrBase_mem_smoothSet hV hVo hx))
  have hpara₁ := hasParacompactOrbitSpace_restr hV hVo hpara
  have hLUC₁ := isLUC_restr hV hVo hLUC
  have hLUCC₁ := isLUC_cubeSEP hLUC₁
  have hs₀ := supp_subset_of_isTransversalPerturbation hf.1.1.1 hr₀ hV₀
  have hs₁ := supp_subset_of_isTransversalPerturbation hf.1.1.1 hr₁ hV₁
  have hr₀' := isTransversalPerturbation_restr hV hVo hf hr₀ hV₀
  have hr₁' := isTransversalPerturbation_restr hV hVo hf hr₁ hV₁
  have h₀' := IsCanonicalFor.restr hV hVo hf hsec hX hft hoL h₀
  have h₁' := IsCanonicalFor.restr hV hVo hf hsec hX hft hoL h₁
  have hω₁ : (A.restr hV).baseEP.epFormsInftyD (m + 1)
      (EP.epFormsInftyPullback (A.baseEP.subFunctor hV) (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := A.baseEP.sub hV) (B := A.baseEP)
        (A.baseEP.subFunctor hV) (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [hω, map_zero] at this
    exact this
  have e := integralEff_eq_of_isTransversalPerturbation_loc hd₁ hF₁ hft₁ hsec₁ hsec₁' _ hoL₁
    hinvC₁ hidx₁ hpara₁ hLUC₁ hLUCC₁ (S₀ := S₀.restr hV hVo hf.1.1.1 hs₀)
    (S₁ := S₁.restr hV hVo hf.1.1.1 hs₁) hr₀' hr₁' h₀' h₁' H _ hω₁
  rw [OrientedSolution.integralEff_restr hV hVo hf.1.1.1 hLUC,
    OrientedSolution.integralEff_restr hV hVo hf.1.1.1 hLUC] at e
  exact e

end Restr

end SBLocalization

end Polyfold
