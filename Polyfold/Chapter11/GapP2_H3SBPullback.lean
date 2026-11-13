import Polyfold.Chapter11.GapP2_H2SBPC
import Polyfold.Chapter10.StrongBundleWeakFibredProduct
import Polyfold.Chapter8.NonVacuityBundle

/-!
# Pull-backs of proper strong bundle coverings (toward 2021 Remark 11.6.9)

**2021 Remark 11.6.9, pp. 563–566 (2017: Remark 11.27)** asks for the localization of the
category `SBPC` of proper strong bundle coverings "as for `PC`", which needs the strong bundle
version of Theorem 11.6.6: the weak fibred product of proper strong bundle coverings is again
one.  In the project, the weak fibred product of strong bundles is a pull-back
(`SBWeakFibredProduct.wfpSEP`, Chapter 10), so the strong bundle part of Theorem 11.6.6 is an
instance of the statement proved here: **the pull-back of a proper strong bundle covering along
an equivalence of proper coverings is a proper strong bundle covering**.

## Main declarations

* `EpStrongBundle.isStrongBundleIso_fibredLift_of_isProperCovering`: condition (3) of
  Definition 8.5.9 holds for **every** strong bundle `W → Y` and every proper covering
  `F : Y → X` (it only involves `W` and `F`: the map `(ψ, w) ↦ ((F(ψ), s(ψ)), w)` is a map of
  pull-backs along the sc-diffeomorphism `ψ ↦ (F(ψ), s(ψ))`).
* `StrongBundle.evenlyCovered_of_isStrongBundleIsoOn`: condition (2) follows from the local
  strong bundle isomorphisms of (1) and the even covering of the proper covering `F`.
* `EpStrongBundle.isProperStrongBundleCovering2021_of`: hence Definition 8.5.9 is (0) and (1)
  for a proper covering `F`.
* `SEP.pullbackCovering A H πP πQ hc : πP*W → πQ*V`, `(p, w) ↦ (H(p), A(w))`, for a square
  `F ∘ πP = πQ ∘ H` of functors; **`SEP.isProperStrongBundleCovering2021_pullbackCovering`**:
  it is a proper strong bundle covering covering `H` when `A` is one covering `F`, `H` is a proper
  covering, `πP`, `πQ` are local sc-diffeomorphisms on objects and `πP` maps the fibres of `H`
  onto those of `F` (all of this holds for an equivalence `(πP, πQ) : H → F` of proper coverings,
  `isProperStrongBundleCovering2021_pullbackCovering_of_isEquivalence`).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Conditions (2) and (3) of Definition 8.5.9 follow from (0), (1) -/

section Generic

set_option linter.unusedSectionVars false

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → ObjY}
  [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] {BW : StrongBundle Y.PObj P}
  [ParacompactSpace (pullbackSpace P Y.src)]
  {V : Type u} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] {BV : StrongBundle X.PObj Q}
  [ParacompactSpace (pullbackSpace Q X.src)]

namespace EpStrongBundle

variable (BW) in
/-- **Definition 8.5.9 (3) holds for every proper covering** (2021 p. 394): for a strong bundle
`P : W → Y` and a proper covering `F : Y → X`, `(ψ, w) ↦ ((F(ψ), s(ψ)), w)` is a strong bundle
isomorphism `𝐘 ₛ×_P W → (𝐗 ₛ×_F Y) ×_{pr₂} W` covering `ψ ↦ (F(ψ), s(ψ))`: both it and its
inverse `((φ, y), w) ↦ (L_F⁻¹(φ, y), w)` are maps of pull-backs (`pullbackMap`), `L_F` being an
sc-diffeomorphism by Definition 8.5.1 (3). -/
theorem isStrongBundleIso_fibredLift_of_isProperCovering {F : EpFunctor Y X}
    (hF : F.IsProperCovering) [ParacompactSpace (MorX × ObjY)]
    [ParacompactSpace (MPolyfold.fibredProduct X.src F.obj)]
    [ParacompactSpace (pullbackSpace P F.fibredSnd)] :
    ∃ (g : MPolyfold.fibredProduct X.src F.obj → MorY)
      (Ψ : pullbackSpace P F.fibredSnd → pullbackSpace P Y.src),
      (BW.pullback Y.isScSmoothMap_src).IsStrongBundleIso (BW.pullback F.isScSmoothMap_fibredSnd)
        F.fibredMap (fibredLift P F) g Ψ := by
  obtain ⟨g, hg⟩ := hF.isScDiffeo_fibredMap
  have hsrc : ∀ r, Y.src (g r) = id (F.fibredSnd r) := fun r =>
    congrArg (fun r : MPolyfold.fibredProduct X.src F.obj => (r : MorX × ObjY).2)
      (hg.right_inv r (mem_univ r))
  refine ⟨g, pullbackMap P F.fibredSnd P Y.src (StrongBundle.IsStrongBundleMap.id BW).covers
    hsrc, ?_⟩
  exact
    { toMap := StrongBundle.isStrongBundleMap_pullbackMap Y.isScSmoothMap_src
        F.isScSmoothMap_fibredSnd (StrongBundle.IsStrongBundleMap.id BW) hg.isScSmoothOn
        fun _ => rfl
      invMap := StrongBundle.isStrongBundleMap_pullbackMap F.isScSmoothMap_fibredSnd
        Y.isScSmoothMap_src (StrongBundle.IsStrongBundleMap.id BW) hg.isScSmoothOn_inv hsrc
      left_inv := fun q => Subtype.ext (Prod.ext (hg.left_inv _ (mem_univ _)) rfl)
      right_inv := fun r => Subtype.ext (Prod.ext (hg.right_inv _ (mem_univ _)) rfl) }

end EpStrongBundle

namespace StrongBundle

/-- **Definition 8.5.9 (2) follows from (1)**: if a strong bundle map `Φ : W → V` covering a
proper covering `F` is a strong bundle isomorphism near every point, it is evenly covered by
strong bundle isomorphisms `W|U(y) → V|U(x)` (cut the sheets of `F` down to the sets where `Φ` is
an isomorphism, and `U(x)` to the intersection of their images). -/
theorem evenlyCovered_of_isStrongBundleIsoOn {F : EpFunctor Y X} (hF : F.IsProperCovering)
    {Φ : W → V} {h : BW.IsStrongBundleMap BV F.obj Φ}
    (hloc : ∀ y, ∃ (U : Set ObjY) (U' : Set ObjX), y ∈ U ∧ BW.IsStrongBundleIsoOn BV h U U')
    (x : ObjX) :
    ∃ (U : Set ObjX) (U' : ObjY → Set ObjY), IsOpen U ∧ x ∈ U ∧
      (F.obj ⁻¹' {x}).PairwiseDisjoint U' ∧
      (∀ y ∈ F.obj ⁻¹' {x}, y ∈ U' y ∧ BW.IsStrongBundleIsoOn BV h (U' y) U) ∧
      F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, U' y := by
  obtain ⟨U₀, Vs, σ, hU₀, hxU₀, hdisj, hV, hcov⟩ := hF.evenlyCovered x
  choose S T hyS hiso using hloc
  choose g hg using fun y => (hiso y).isScDiffeoOn_base
  have hfin : (F.obj ⁻¹' {x}).Finite := hF.finite_fiber x
  have hO : ∀ y ∈ F.obj ⁻¹' {x}, IsOpen (Vs y ∩ S y) := fun y hy =>
    (hV y hy).2.isOpen_source.inter (hg y).isOpen_source
  -- the images `T' y = F(V y ∩ S y)` and the common neighbourhood `U` of `x`
  set T' : ObjY → Set ObjX := fun y => T y ∩ g y ⁻¹' (Vs y ∩ S y)
  have hT' : ∀ y ∈ F.obj ⁻¹' {x},
      Y.PObj.IsScDiffeoOn X.PObj F.obj (g y) (Vs y ∩ S y) (T' y) := fun y hy =>
    (hg y).restrict (hO y hy) inter_subset_right
  have hxT' : ∀ y ∈ F.obj ⁻¹' {x}, x ∈ T' y := fun y hy => by
    have hFy : F.obj y = x := hy
    have h1 := (hg y).mapsTo (hyS y)
    have h2 := (hg y).left_inv y (hyS y)
    rw [hFy] at h1 h2
    exact ⟨h1, by rw [mem_preimage, h2]; exact ⟨(hV y hy).1, hyS y⟩⟩
  set U := U₀ ∩ ⋂ y ∈ F.obj ⁻¹' {x}, T' y
  have hUo : IsOpen U := hU₀.inter (hfin.isOpen_biInter fun y hy => (hT' y hy).isOpen_target)
  have hxU : x ∈ U := ⟨hxU₀, mem_iInter₂.2 hxT'⟩
  have hUT' : ∀ y ∈ F.obj ⁻¹' {x}, U ⊆ T' y := fun y hy _ hu => (mem_iInter₂.1 hu.2) y hy
  refine ⟨U, fun y => (Vs y ∩ S y) ∩ F.obj ⁻¹' U, hUo, hxU,
    hdisj.mono_on fun y _ => inter_subset_left.trans inter_subset_left, fun y hy => ?_, ?_⟩
  · have hFy : F.obj y = x := hy
    have hU' : IsOpen ((Vs y ∩ S y) ∩ F.obj ⁻¹' U) :=
      (hT' y hy).isScSmoothOn.continuousOn.isOpen_inter_preimage (hO y hy) hUo
    refine ⟨⟨⟨(hV y hy).1, hyS y⟩, by rw [mem_preimage, hFy]; exact hxU⟩, ?_⟩
    have e₁ := (hiso y).restrict (hg y) (hO y hy) inter_subset_right
    have e₂ := e₁.restrict (hT' y hy) hU' inter_subset_left
    have hset : T' y ∩ g y ⁻¹' ((Vs y ∩ S y) ∩ F.obj ⁻¹' U) = U := by
      ext t
      constructor
      · rintro ⟨ht, -, hgt⟩
        rwa [mem_preimage, (hT' y hy).right_inv t ht] at hgt
      · intro ht
        have ht' := hUT' y hy ht
        exact ⟨ht', ht'.2, by rw [mem_preimage, (hT' y hy).right_inv t ht']; exact ht⟩
    rwa [hset] at e₂
  · ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hz
      have hz₀ : z ∈ F.obj ⁻¹' U₀ := hz.1
      rw [hcov] at hz₀
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hz₀
      have ht := hUT' y hy hz
      have hgz := ht.2
      have e : g y (F.obj z) = z := by
        have h1 := (hV y hy).2.left_inv z hzy
        have h2 := (hV y hy).2.left_inv _ hgz.1
        rw [(hT' y hy).right_inv _ ht] at h2
        exact h2.symm.trans h1
      exact ⟨y, hy, by rw [← e]; exact hgz, hz⟩
    · rintro ⟨y, -, -, hz⟩
      exact hz

end StrongBundle

namespace EpStrongBundle

variable {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X} {A : W → V}

/-- **Definition 8.5.9 is (0) and (1)**: a surjective strong bundle map `A` (with (0)) covering a
proper covering `F` which is a local strong bundle isomorphism near every point is a proper strong
bundle covering functor; (2) is `evenlyCovered_of_isStrongBundleIsoOn`, (3) is
`isStrongBundleIso_fibredLift_of_isProperCovering`. -/
theorem isProperStrongBundleCovering2021_of (hA : EW.IsMap EV F A) (hs : Surjective A)
    (hF : F.IsProperCovering)
    (hloc : ∀ y : ObjY, ∃ (U : Set ObjY) (U' : Set ObjX), y ∈ U ∧
      BW.IsStrongBundleIsoOn BV hA.isStrongBundleMap U U') :
    EW.IsProperStrongBundleCovering2021 EV F A where
  isMap := hA
  surjective := hs
  isProperCovering := hF
  isLocalStrongBundleIso := hloc
  evenlyCovered := StrongBundle.evenlyCovered_of_isStrongBundleIsoOn hF hloc
  isStrongBundleIso_fibredLift := by
    have := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    have := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    have := BW.paracompactSpace_pullback (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
      F.fibredSnd
    exact isStrongBundleIso_fibredLift_of_isProperCovering BW hF

end EpStrongBundle

end Generic

/-! ### The pull-back of a proper strong bundle covering -/

namespace SEP

open EpStrongBundle

variable {S S' : SEP.{u}} (A : S ⟶ S') {P Q : EP.{u}} (H : EpFunctor P.X Q.X)
  (πP : EpFunctor P.X S.X) (πQ : EpFunctor Q.X S'.X) (hc : (Hom.ϕ A).comp πP = πQ.comp H)

/-- **The pull-back of `A : W → V` along a square `F ∘ πP = πQ ∘ H`**:
`πP*W → πQ*V`, `(p, w) ↦ (H(p), A(w))`, a morphism of `SEP` covering `H`. -/
def pullbackCovering : S.pullbackAlong P πP ⟶ S'.pullbackAlong Q πQ :=
  S'.pullbackLiftHom Q πQ H (S.pullbackHom P πP ≫ A) hc

@[simp] theorem pullbackCovering_ϕ : Hom.ϕ (pullbackCovering A H πP πQ hc) = H := rfl

/-- `(π*V → V) ∘ (pullbackCovering) = A ∘ (π*W → W)`. -/
theorem pullbackCovering_comp_pullbackHom :
    pullbackCovering A H πP πQ hc ≫ S'.pullbackHom Q πQ = S.pullbackHom P πP ≫ A :=
  Hom.ext_obj hc.symm rfl

/-- The square `F ∘ πP = πQ ∘ H` as a functor `(πP, πQ) : H → F` of proper coverings
(Definition 11.6.4 (1)). -/
def pullbackSquare : ProperCoveringHom H (Hom.ϕ A) :=
  ProperCoveringHom.mk πP πQ (fun p => (congrArg (fun G : EpFunctor P.X S'.X => G.obj p) hc).symm)
    (fun m => (congrArg (fun G : EpFunctor P.X S'.X => G.mor m) hc).symm)

variable {A H πP πQ}

/-- **The pull-back of a proper strong bundle covering is a proper strong bundle covering**
(the strong bundle part of 2021 Theorem 11.6.6 (1), used in Remark 11.6.9): if `A : W → V` is a
proper strong bundle covering functor covering `F` (Definition 8.5.9), `H : P → Q` a proper
covering, `πP`, `πQ` local sc-diffeomorphisms on objects with `F ∘ πP = πQ ∘ H`, and `πP` maps
every fibre `H⁻¹(q)` onto `F⁻¹(πQ(q))`, then `(p, w) ↦ (H(p), A(w))` is a proper strong bundle
covering functor `πP*W → πQ*V` covering `H`.  Near `p` it is the composite
`πP*W → W → V ← πQ*V` of local strong bundle isomorphisms. -/
theorem isProperStrongBundleCovering2021_pullbackCovering
    (hA : S.E.IsProperStrongBundleCovering2021 S'.E (Hom.ϕ A) (Hom.Φ A).obj)
    (hH : H.IsProperCovering) (hπP : P.X.PObj.IsLocalScDiffeo S.X.PObj πP.obj)
    (hπQ : Q.X.PObj.IsLocalScDiffeo S'.X.PObj πQ.obj)
    (hfib : ∀ q, SurjOn πP.obj (H.obj ⁻¹' {q}) ((Hom.ϕ A).obj ⁻¹' {πQ.obj q})) :
    (S.pullbackAlong P πP).E.IsProperStrongBundleCovering2021 (S'.pullbackAlong Q πQ).E H
      (Hom.Φ (pullbackCovering A H πP πQ hc)).obj := by
  have hmap := (Hom.isStrongBundleFunctor (pullbackCovering A H πP πQ hc)).isMap
  have := S.B.paracompactSpace_pullback P.X.PObj πP.obj
  have := S'.B.paracompactSpace_pullback Q.X.PObj πQ.obj
  refine isProperStrongBundleCovering2021_of hmap ?_ hH fun p => ?_
  · rintro ⟨⟨q, v⟩, hv⟩
    obtain ⟨w, rfl⟩ := hA.surjective v
    have hw : (Hom.ϕ A).obj (S.P w) = πQ.obj q :=
      ((Hom.isStrongBundleFunctor A).isStrongBundleMap_obj.covers w).symm.trans hv
    obtain ⟨p, hp, hpw⟩ := hfib q hw
    exact ⟨⟨(p, w), hpw.symm⟩, Subtype.ext (Prod.ext hp rfl)⟩
  · obtain ⟨U₁, U₁', hpU₁, hA₁⟩ := hA.isLocalStrongBundleIso (πP.obj p)
    obtain ⟨V₁, V₁', gP, hpV₁, hdP⟩ := hπP p
    obtain ⟨V₂, V₂', gQ, hqV₂, hdQ⟩ := hπQ (H.obj p)
    have iP := S.B.isStrongBundleIsoOn_pullbackProj' πP.isScSmoothMap_obj hdP p
    have iQ := S'.B.isStrongBundleIsoOn_pullbackProj' πQ.isScSmoothMap_obj hdQ (H.obj p)
    obtain ⟨U₀, U₀'', hpU₀, hc₀⟩ := hA₁.exists_comp iP hpV₁ hpU₁
    have hf : (Hom.ϕ A).obj ∘ πP.obj = πQ.obj ∘ H.obj :=
      congrArg (fun G => G.obj) hc
    have hc₁ := hc₀.of_eq hf
    obtain ⟨g₀, hg₀⟩ := hc₁.isScDiffeoOn_base
    have hU₂ : IsOpen (U₀ ∩ H.obj ⁻¹' V₂) :=
      hg₀.isOpen_source.inter (hdQ.isOpen_source.preimage H.continuous_obj')
    have hc₂ := hc₁.restrict hg₀ hU₂ inter_subset_left
    have hres := StrongBundle.IsStrongBundleIsoOn.of_comp
      (h := hmap.isStrongBundleMap)
        (h' := S'.B.isStrongBundleMap_pullbackProj' πQ.isScSmoothMap_obj) hc₂ iQ
      fun _ hy => hy.2
    exact Exists.intro _ (Exists.intro _ (And.intro (And.intro hpU₀ hqV₂) hres))

/-- **The pull-back along an equivalence of proper coverings**: for an equivalence
`(πP, πQ) : H → F` of proper coverings (Definition 11.6.4 (2)), the pull-back of a proper strong
bundle covering `A` covering `F` is a proper strong bundle covering covering `H`. -/
theorem isProperStrongBundleCovering2021_pullbackCovering_of_isEquivalence
    (hA : S.E.IsProperStrongBundleCovering2021 S'.E (Hom.ϕ A) (Hom.Φ A).obj)
    (hH : H.IsProperCovering)
    (hE : (pullbackSquare A H πP πQ hc).IsEquivalence) :
    (S.pullbackAlong P πP).E.IsProperStrongBundleCovering2021 (S'.pullbackAlong Q πQ).E H
      (Hom.Φ (pullbackCovering A H πP πQ hc)).obj :=
  isProperStrongBundleCovering2021_pullbackCovering hc hA hH
    hE.isEquivalence_Ψ.isLocalScDiffeo_obj hE.isEquivalence_Φ.isLocalScDiffeo_obj
    fun q => (hE.isFiberBijective q).surjOn

end SEP

end Polyfold

end
