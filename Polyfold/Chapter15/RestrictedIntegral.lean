import Polyfold.Chapter15.RestrictedIntegralCore
import Polyfold.Chapter9.LocalFormsSub
import Polyfold.Chapter9.StokesTextHypotheses

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5 (Definition 9.5.6, p. 439) and §11.4 (Theorems 11.4.1, 11.4.2, pp. 543–544), for
the restriction `X|V` of an ep-groupoid to a saturated open set `V` (Proposition 7.1.22).
Numbers and pages are the 2021 text's.

# Branched integrals with support in a saturated open set

Let `Θ̂ = (Θ, T̂)` be a compact oriented branched ep⁺-subgroupoid of `X`, described by oriented
tame structures of dimension `n ≥ 1`, with `supp Θ ⊆ V`, `V` saturated and open, and
`i : X|V → X` the inclusion.

* `EP.isBranchedEpSubgroupoid_sub`, `isCompactBranched_sub`, `isOrientation_sub`, `hloc_sub`:
  `i^*Θ̂ = (Θ ∘ i, i^*T̂)` is a compact oriented branched ep⁺-subgroupoid of `X|V`, described by
  oriented tame structures of dimension `n` (`i^*T̂` is `EpFunctor.pullSection`, (11.9)).
* `EP.isLUC_sub`: the local unique continuation property restricts to `X|V`.
* **`EP.tameBranchedIntegral_sub`**, **`EP.tameBranchedIntegralEff_sub`**:
  `∫_Θ̂ ω = ∫_{i^*Θ̂} i^*ω` and `∮_Θ̂ ω = ∮_{i^*Θ̂} i^*ω` for `ω ∈ Ωⁿ_{ep,∞}(X)`.

The inclusion is full, faithful and a local sc-diffeomorphism on objects, and its image contains
the support; the statements are those of `RestrictedIntegralCore.lean` for it.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace EP

open MPolyfold EpGroupoid

variable (A : EP.{u}) {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V) {n : ℕ} {Θ : A.Obj → ℚ}
  {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- The inclusion `X|V → X` is bijective on the isotropy groups. -/
theorem bijective_isotropyHom_subFunctor (x : (A.sub hV).Obj) :
    Bijective ((A.subFunctor hV).isotropyHom x) := by
  refine ⟨fun g g' h => GroupoidStr.Isotropy.ext
    (A.subFunctor_mor_injective hV (congrArg GroupoidStr.Isotropy.val h)), fun k => ?_⟩
  obtain ⟨φ, hs, ht, he⟩ := ((A.subFunctor hV).full_iff.1 (A.subFunctor_full hV)) x x k.val
    k.src_val k.tgt_val
  exact ⟨⟨φ, hs, ht⟩, GroupoidStr.Isotropy.ext he⟩

/-- `|supp Θ|` lies in the image of `|X|V| → |X|` if `supp Θ ⊆ V`. -/
theorem orbitSupp_subset_range_subFunctor (hsupp : supp Θ ⊆ V) :
    A.X.orbitSupp Θ ⊆ range (A.subFunctor hV).orbitMap := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(A.sub hV).X.π (show (A.sub hV).Obj from (⟨y, hsupp hy⟩ : V)),
    (A.subFunctor hV).orbitMap_π _⟩

/-- `(i^*ω)(α) = ω(Ti ∘ α)` on the tangent spaces of the smooth finite-dimensional
submanifolds of `X|V`. -/
theorem epFormsInftyEval_pullback_subFunctor (hVo : IsOpen V) (ω : A.epFormsInfty n)
    {N : Set (A.sub hV).Obj} (hN : (A.sub hV).X.PObj.IsSmoothSubmanifold N)
    {y : (A.sub hV).Obj} (hy : y ∈ N) (α : Fin n → (A.sub hV).X.PObj.TangentSpace)
    (hα : ∀ i, α i ∈ (A.sub hV).X.PObj.submanifoldTangent N y) :
    ((A.sub hV).epFormsInftyEval n).ev (epFormsInftyPullback (A.subFunctor hV) n ω) α =
      (A.epFormsInftyEval n).ev ω (fun i => (A.subFunctor hV).tangent.obj (α i)) :=
  epFormsInftyEval_epFormsInftyPullback (A.isLocalScDiffeo_subFunctor_obj hV hVo) ω
    ⟨N, y, hN, hy, hα⟩

/-- **The local unique continuation property (2021 Definition 7.2.18) restricts to `X|V`.** -/
theorem isLUC_sub (hVo : IsOpen V) (hLUC : A.X.IsLUC) : (A.sub hV).X.IsLUC :=
  EpFunctor.isLUC_of_isLocalScDiffeo (A.isLocalScDiffeo_subFunctor_obj hV hVo) hLUC

/-- **`Θ ∘ i` is compact** for `Θ` compact with `supp Θ ⊆ V`. -/
theorem isCompactBranched_sub (hVo : IsOpen V) (hΘ : A.X.IsFunctorial Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hsupp : supp Θ ⊆ V) :
    (A.sub hV).X.IsCompactBranched ((A.subFunctor hV).pullbackTheta Θ) :=
  EpFunctor.isCompactBranched_pullbackTheta_of (A.isLocalScDiffeo_subFunctor_obj hV hVo)
    (A.subFunctor_full hV) hΘ hcpt (A.orbitSupp_subset_range_subFunctor hV hsupp)

/-- **`Θ ∘ i` is a branched ep⁺-subgroupoid of `X|V`** for `Θ` compact with `supp Θ ⊆ V`. -/
theorem isBranchedEpSubgroupoid_sub (hVo : IsOpen V) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hsupp : supp Θ ⊆ V) :
    (A.sub hV).X.IsBranchedEpSubgroupoid ((A.subFunctor hV).pullbackTheta Θ) :=
  EpFunctor.isBranchedEpSubgroupoid_pullbackTheta_of (A.isLocalScDiffeo_subFunctor_obj hV hVo)
    (A.subFunctor_full hV) hΘ hcpt (A.orbitSupp_subset_range_subFunctor hV hsupp)

/-- **`i^*T̂` is an orientation of `Θ ∘ i`.** -/
theorem isOrientation_sub (hVo : IsOpen V) (hT : A.X.IsOrientation Θ T) :
    (A.sub hV).X.IsOrientation ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T) :=
  EpFunctor.isOrientation_pullSection_of (A.isLocalScDiffeo_subFunctor_obj hV hVo) hT

/-- **`i^*Θ̂` is described by oriented tame structures of dimension `n`.** -/
theorem hloc_sub (hVo : IsOpen V) (hΘ : A.X.IsFunctorial Θ) (hT : A.X.IsGrHatSection T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure n Θ x, C.Represents T) :
    ∀ x ∈ supp ((A.subFunctor hV).pullbackTheta Θ),
      ∃ C : (A.sub hV).X.OrientedTameStructure n ((A.subFunctor hV).pullbackTheta Θ) x,
        C.Represents ((A.subFunctor hV).pullSection T) :=
  EpFunctor.hloc_pullSection_of (A.isLocalScDiffeo_subFunctor_obj hV hVo)
    (A.bijective_isotropyHom_subFunctor hV) hΘ hT hloc

/-- **The branched integral over `Θ̂` with `supp Θ ⊆ V` is the branched integral over `i^*Θ̂` on
`X|V`** (Definition 9.5.6 (1), Theorem 11.4.1): `∫_Θ̂ ω = ∫_{i^*Θ̂} i^*ω`. -/
theorem tameBranchedIntegral_sub (hVo : IsOpen V) (hn : 0 < n)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure n Θ x, C.Represents T)
    (hsupp : supp Θ ⊆ V)
    (hΘ₁ : (A.sub hV).X.IsBranchedEpSubgroupoid ((A.subFunctor hV).pullbackTheta Θ))
    (hcpt₁ : (A.sub hV).X.IsCompactBranched ((A.subFunctor hV).pullbackTheta Θ))
    (hT₁ : (A.sub hV).X.IsOrientation ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T))
    (hloc₁ : ∀ x ∈ supp ((A.subFunctor hV).pullbackTheta Θ),
      ∃ C : (A.sub hV).X.OrientedTameStructure n ((A.subFunctor hV).pullbackTheta Θ) x,
        C.Represents ((A.subFunctor hV).pullSection T))
    (ω : A.epFormsInfty n) :
    (A.epFormsInftyEval n).tameBranchedIntegral hn hΘ hcpt hT hloc ω =
      ((A.sub hV).epFormsInftyEval n).tameBranchedIntegral hn hΘ₁ hcpt₁ hT₁ hloc₁
        (epFormsInftyPullback (A.subFunctor hV) n ω) := by
  have hd := A.isLocalScDiffeo_subFunctor_obj hV hVo
  exact (EpFunctor.integral_pull_of (FX := (A.sub hV).epFormsInftyEval n)
    (FY := A.epFormsInftyEval n) (P := epFormsInftyPullback (A.subFunctor hV) n) hd
    (A.subFunctor_full hV) (A.bijective_isotropyHom_subFunctor hV)
    (fun ω' _ hN _ hy α hα => A.epFormsInftyEval_pullback_subFunctor hV hVo ω' hN hy α hα) hn
    hΘ hcpt hT (FormEval.hcov_of_tameOpen (FormEval.tameOpen A.X) hloc)
    (A.orbitSupp_subset_range_subFunctor hV hsupp) hΘ₁ hcpt₁ hT₁
    (fun Tc => Tc.pullSection_Q hd hT.isGrHatSection)
    (FormEval.hcov_of_tameOpen (FormEval.tameOpen (A.sub hV).X) hloc₁) ω).symm

/-- **The effective branched integral over `Θ̂` with `supp Θ ⊆ V` is the effective branched
integral over `i^*Θ̂` on `X|V`** (Definition 9.5.6 (2), Theorem 11.4.2), for `X` with the local
unique continuation property: `∮_Θ̂ ω = ∮_{i^*Θ̂} i^*ω`. -/
theorem tameBranchedIntegralEff_sub (hVo : IsOpen V) (hn : 0 < n) (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (hsupp : supp Θ ⊆ V)
    (hΘ₁ : (A.sub hV).X.IsBranchedEpSubgroupoid ((A.subFunctor hV).pullbackTheta Θ))
    (hcpt₁ : (A.sub hV).X.IsCompactBranched ((A.subFunctor hV).pullbackTheta Θ))
    (hT₁ : (A.sub hV).X.IsOrientation ((A.subFunctor hV).pullbackTheta Θ)
      ((A.subFunctor hV).pullSection T))
    (hloc₁ : ∀ x ∈ supp ((A.subFunctor hV).pullbackTheta Θ),
      ∃ C : (A.sub hV).X.OrientedTameStructure n ((A.subFunctor hV).pullbackTheta Θ) x,
        C.Represents ((A.subFunctor hV).pullSection T) ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty n) :
    (A.epFormsInftyEval n).tameBranchedIntegralEff hn hΘ hcpt hT hloc ω =
      ((A.sub hV).epFormsInftyEval n).tameBranchedIntegralEff hn hΘ₁ hcpt₁ hT₁ hloc₁
        (epFormsInftyPullback (A.subFunctor hV) n ω) := by
  have hd := A.isLocalScDiffeo_subFunctor_obj hV hVo
  exact (EpFunctor.integralEff_pull_of (FX := (A.sub hV).epFormsInftyEval n)
    (FY := A.epFormsInftyEval n) (P := epFormsInftyPullback (A.subFunctor hV) n) hd
    (A.subFunctor_full hV) (A.bijective_isotropyHom_subFunctor hV)
    (fun ω' _ hN _ hy α hα => A.epFormsInftyEval_pullback_subFunctor hV hVo ω' hN hy α hα) hn
    hΘ hcpt hT (FormEval.hcovEff_of_tameOpen (FormEval.tameOpen A.X) hloc) hLUC
    (A.orbitSupp_subset_range_subFunctor hV hsupp) hΘ₁ hcpt₁ hT₁
    (fun Tc => Tc.pullSection_Q hd hT.isGrHatSection)
    (FormEval.hcovEff_of_tameOpen (FormEval.tameOpen (A.sub hV).X) hloc₁) ω).symm

end EP

end Polyfold
