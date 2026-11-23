import Polyfold.Chapter15.RestrictedBundleCompactness
import Polyfold.Chapter15.CubeSectionsThrough

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Definition
15.3.5** (p. 693) and the standing hypotheses of Theorem 15.3.7 (p. 694), on the restriction
`W|V → X|V` of a strong bundle to a saturated open set `V` (Proposition 7.1.22, p. 250).

# General position and the standing hypotheses on a saturated open set

## What is formalized (namespace `Polyfold.SBLocalization`)

For `V` open and saturated in `X`:

* `degIndex_restr`, `degIndex_restr_eq_zero`, `isTame_restr`: the degeneracy index of `X|V` is
  that of `X`; `X|V` is tame if `d_X ≡ 0`.
* `hasParacompactOrbitSpace_restr`: `|X|V|` is paracompact if `|X|` is (both are metrizable,
  Theorem 7.3.1).
* `hasScPlusSectionsThrough_restr`: sc⁺-sections through the smooth fibre points of `W|V`, by
  restriction of those of `W`.
* **`isInGeneralPosition_restr`**: `(f|V, Λ|V)` is in general position if `(f, Λ)` is.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold SEP

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- The degeneracy index of `X|V` is that of `X` (Proposition 2.4.4 for the inclusion). -/
theorem degIndex_restr (hVo : IsOpen V) (a : (A.restr hV).Obj) :
    (A.restr hV).X.PObj.degIndex a = A.X.PObj.degIndex (restrBase hV a) :=
  ((A.baseEP.isLocalScDiffeo_subFunctor_obj hV hVo).degIndex_eq a).symm

theorem degIndex_restr_eq_zero (hVo : IsOpen V) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (a : (A.restr hV).Obj) : (A.restr hV).X.PObj.degIndex a = 0 :=
  (degIndex_restr hV hVo a).trans (hd _)

/-- `X|V` is tame if `d_X ≡ 0`. -/
theorem isTame_restr (hVo : IsOpen V) (hd : ∀ x, A.X.PObj.degIndex x = 0) :
    (A.restr hV).X.IsTame :=
  (A.restr hV).X.isTame_of_degIndex_eq_zero (degIndex_restr_eq_zero hV hVo hd)

/-- **`|X|V|` is paracompact if `|X|` is**: `|X|` is metrizable (Theorem 7.3.1, p. 271) and
`|X|V|` is a subspace of it. -/
theorem hasParacompactOrbitSpace_restr (hVo : IsOpen V) (h : A.X.HasParacompactOrbitSpace) :
    (A.restr hV).X.HasParacompactOrbitSpace := by
  have hm : TopologicalSpace.MetrizableSpace A.X.OrbitSpace := A.X.theorem_7_3_1_metrizable h
  have hm' : TopologicalSpace.MetrizableSpace (A.restr hV).X.OrbitSpace :=
    (isOpenEmbedding_orbitMap_restr hV hVo).isEmbedding.metrizableSpace
  let _ := TopologicalSpace.metrizableSpaceMetric (A.restr hV).X.OrbitSpace
  change ParacompactSpace (A.restr hV).X.OrbitSpace
  infer_instance

/-- **Sc⁺-sections through the smooth fibre points of `W|V`**, by restriction of those of
`W`. -/
theorem hasScPlusSectionsThrough_restr (hVo : IsOpen V) (hsec : A.B.HasScPlusSectionsThrough) :
    (A.restr hV).B.HasScPlusSectionsThrough := by
  intro z hz e he hez
  have := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  have hπ := (A.baseEP.subFunctor hV).isScSmoothMap_obj
  have hx : restrBase hV z ∈ A.X.PObj.smoothSet :=
    mem_iInter.2 fun m => hπ.mapsTo_levelSet m (mem_iInter.1 hz m)
  have he' : restrFib hV e ∈ A.B.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => (A.B.isScSmoothMap_pullbackProj' hπ).mapsTo_levelSet m
      (mem_iInter.1 he m)
  have hPe : A.P (restrFib hV e) = restrBase hV z := by rw [P_restrFib, hez]
  obtain ⟨s, hs, hsx⟩ := hsec _ hx _ he' hPe
  set L := restrIso hV hVo z
  have hon := isScPlusSectionOn_isoSec L hVo subset_rfl
    (IsScPlusSectionOn.of_isScPlusSection hs hVo)
  obtain ⟨hP, G, hG, hGs⟩ := hon
  have huniv : ∀ y : (A.restr hV).Obj, y ∈ isoSet L V := fun y => ⟨mem_univ _, restrBase_mem hV y⟩
  refine ⟨isoSec L s, ?_, ?_⟩
  · exact StrongBundle.isScPlusSection_of_locally (fun p => hP p (huniv p)) fun y₀ =>
      ⟨_, isOpen_isoSet L hVo, huniv y₀, G, hGs, fun y hy => hG y hy⟩
  · change L.Ψ (s (restrBase hV z)) = e
    rw [hsx]
    exact L.zero.left_inv e (mem_univ _)

/-- **`(f|V, Λ|V)` is in general position if `(f, Λ)` is** (Definition 15.3.5, p. 693): the
reduced linearizations of `(f|V, Λ|V)` at `a` are those of `(f, Λ)` read through the
inclusion. -/
theorem isInGeneralPosition_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (H : IsInGeneralPosition A f Λ) :
    IsInGeneralPosition (A.restr hV) (restrSec hV f hf.1.1.1) (restrMult hV Λ) := by
  intro x hpos
  set a := (A.restr hV).X.PObj.levelVal 1 x with ha
  set L := restrIso hV hVo a
  have hfr := isScFredholmSectionFunctor_restrSec hV hVo hf
  have ha1 : restrBase hV a ∈ A.X.PObj.levelSet 1 :=
    (L.base.mem_levelSet_iff (mem_univ a) 1).2 (levelVal_mem x)
  set x' := A.X.PObj.levelMk 1 (restrBase hV a) ha1
  have hx' : A.X.PObj.levelVal 1 x' = restrBase hV a := A.X.PObj.levelVal_levelMk 1 _ ha1
  have hpos' : 0 < Λ (f (A.X.PObj.levelVal 1 x')) := by rw [hx']; exact hpos
  have h1 : IsReducedOntoAtLevel f Λ x' := H x' hpos'
  exact (isReducedOntoAtLevel_localIso_iff L hfr hf hΛ (eqOn_restrSec hV hVo hf.1.1.1 a)
    (fun _ _ => rfl) (mem_univ _) hx'.symm).2 h1

end SBLocalization

end Polyfold
