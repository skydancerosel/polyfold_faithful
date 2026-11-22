import Polyfold.Chapter8.TangentPairs

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, **Definition 8.5.1**
(p. 383, proper covering functor), condition (3): the map `L_F : 𝐘 → 𝐗 ₛ×_F Y`,
`φ ↦ (F(φ), s(φ))`.  Numbers and pages are the 2021 text's.

# Condition (3) of a proper covering functor is bijectivity of `L_F`

## The statement

For every sc-smooth functor `F : Y → X` of ep-groupoids the map `L_F : 𝐘 → 𝐗 ₛ×_F Y` into
Part I's fibred-product sub-M-polyfold of `𝐗 × Y` is a local sc-diffeomorphism: its composite
with the second projection `π₂ : 𝐗 ₛ×_F Y → Y` is the source map `s : 𝐘 → Y`, and both `s` and
`π₂` are local sc-diffeomorphisms (`π₂` because `s : 𝐗 → X` is one).  A bijective local
sc-diffeomorphism is an sc-diffeomorphism, so condition (3) of Definition 8.5.1 holds exactly
when `L_F` is bijective.

This is the argument of the proof of Proposition 17.8.15 (pp. 837–838) in general form, and it
is the gluing step for disjoint unions: for a functor between ep-groupoids whose object and
morphism M-polyfolds are disjoint unions, condition (3) reduces to bijectivity, which can be
checked summand by summand; no identification of the fibred product of disjoint unions with a
disjoint union of fibred products is needed.

## What is formalized (namespace `Polyfold.EpFunctor`)

* `continuous_fibredMap`, **`isLocalScDiffeo_fibredMap`** (every sc-smooth functor),
* **`isScDiffeo_fibredMap_of_bijective`**, `bijective_of_isScDiffeo_fibredMap`,
  **`isScDiffeo_fibredMap_iff_bijective`**: Definition 8.5.1 (3) holds iff `L_F` is bijective,
* **`isProperCovering_iff_bijective`**: Definition 8.5.1 with (3) replaced by bijectivity of
  `L_F`, and `isProperCovering_of_bijective` (the constructor).

The use in Chapter 17 is `ProperPolyfoldCoveringStructure.hatModelFunctor_isProperCovering`
(`Polyfold/Chapter17/ProperCoveringGlobalFunctor.lean`).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

section ProperCovering

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

namespace EpFunctor

variable (F : EpFunctor Y X)

/-- `L_F : 𝐘 → 𝐗 ₛ×_F Y` is continuous. -/
theorem continuous_fibredMap : Continuous F.fibredMap :=
  continuous_induced_rng.2 ((continuousOn_univ.1 F.isScSmoothMap_mor.continuousOn).prodMk
    Y.isLocalScDiffeo_src.continuous)

/-- **`L_F : 𝐘 → 𝐗 ₛ×_F Y` is a local sc-diffeomorphism** onto Part I's fibred-product
sub-M-polyfold of `𝐗 × Y`, for every sc-smooth functor `F` (Definition 8.5.1 (3), p. 383):
`π₂ ∘ L_F = s` with `s : 𝐘 → Y` and `π₂ : 𝐗 ₛ×_F Y → Y` local sc-diffeomorphisms. -/
theorem isLocalScDiffeo_fibredMap :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    Y.PMor.IsLocalScDiffeo (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
      F.fibredMap := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  exact MPolyfold.isLocalScDiffeo_of_comp_eq Y.isLocalScDiffeo_src
    (MPolyfold.isLocalScDiffeo_sndOfFibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj)
    F.continuous_fibredMap fun _ => rfl

/-- **Definition 8.5.1 (3) from bijectivity**: a bijective `L_F` is an sc-diffeomorphism
`𝐘 → 𝐗 ₛ×_F Y`. -/
theorem isScDiffeo_fibredMap_of_bijective (h : Bijective F.fibredMap) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    ∃ g : MPolyfold.fibredProduct X.src F.obj → MorY,
      Y.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
        F.fibredMap g univ univ := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  exact ⟨_, F.isLocalScDiffeo_fibredMap.isScDiffeoOn_of_bijective (Equiv.ofBijective _ h)
    fun _ => rfl⟩

/-- An sc-diffeomorphism `L_F` is bijective. -/
theorem bijective_of_isScDiffeo_fibredMap
    (h : letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj;
      letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype
        (MPolyfold.fibredProduct X.src F.obj);
      ∃ g : MPolyfold.fibredProduct X.src F.obj → MorY,
        Y.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
          (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
          F.fibredMap g univ univ) :
    Bijective F.fibredMap := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  obtain ⟨g, hg⟩ := h
  exact ⟨fun a b hab => by
      rw [← hg.left_inv a (mem_univ a), ← hg.left_inv b (mem_univ b), hab],
    fun q => ⟨g q, hg.right_inv q (mem_univ q)⟩⟩

/-- **Definition 8.5.1 (3) holds iff `L_F` is bijective.** -/
theorem isScDiffeo_fibredMap_iff_bijective :
    (letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj;
      letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype
        (MPolyfold.fibredProduct X.src F.obj);
      ∃ g : MPolyfold.fibredProduct X.src F.obj → MorY,
        Y.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
          (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
          F.fibredMap g univ univ) ↔ Bijective F.fibredMap :=
  ⟨F.bijective_of_isScDiffeo_fibredMap, F.isScDiffeo_fibredMap_of_bijective⟩

/-- **A proper covering functor** (Definition 8.5.1, p. 383) from conditions (1), (2) and the
bijectivity of `L_F`. -/
theorem isProperCovering_of_bijective (hs : Surjective F.obj)
    (hl : Y.PObj.IsLocalScDiffeo X.PObj F.obj) (hfin : ∀ x, (F.obj ⁻¹' {x}).Finite)
    (hev : ∀ x, ∃ (U : Set ObjX) (V : ObjY → Set ObjY) (σ : ObjY → ObjX → ObjY),
      IsOpen U ∧ x ∈ U ∧ (F.obj ⁻¹' {x}).PairwiseDisjoint V ∧
      (∀ y ∈ F.obj ⁻¹' {x}, y ∈ V y ∧ Y.PObj.IsScDiffeoOn X.PObj F.obj (σ y) (V y) U) ∧
      F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, V y)
    (hb : Bijective F.fibredMap) : F.IsProperCovering :=
  ⟨hs, hl, hfin, hev, F.isScDiffeo_fibredMap_of_bijective hb⟩

/-- **Definition 8.5.1 with condition (3) replaced by the bijectivity of `L_F`.** -/
theorem isProperCovering_iff_bijective :
    F.IsProperCovering ↔ Surjective F.obj ∧ Y.PObj.IsLocalScDiffeo X.PObj F.obj ∧
      (∀ x, (F.obj ⁻¹' {x}).Finite) ∧
      (∀ x, ∃ (U : Set ObjX) (V : ObjY → Set ObjY) (σ : ObjY → ObjX → ObjY),
        IsOpen U ∧ x ∈ U ∧ (F.obj ⁻¹' {x}).PairwiseDisjoint V ∧
        (∀ y ∈ F.obj ⁻¹' {x}, y ∈ V y ∧ Y.PObj.IsScDiffeoOn X.PObj F.obj (σ y) (V y) U) ∧
        F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, V y) ∧
      Bijective F.fibredMap :=
  ⟨fun h => ⟨h.surjective, h.isLocalScDiffeo, h.finite_fiber, h.evenlyCovered,
      F.bijective_of_isScDiffeo_fibredMap h.isScDiffeo_fibredMap⟩,
    fun ⟨hs, hl, hfin, hev, hb⟩ => F.isProperCovering_of_bijective hs hl hfin hev hb⟩

end EpFunctor

end ProperCovering

end Polyfold
