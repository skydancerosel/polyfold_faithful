import Polyfold.Chapter8.Book2021
import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.5, the text before **Lemma 8.5.10** and the lemma itself (p. 395, new in the 2021 edition).

# `F*V` is a strong bundle over the ep-groupoid `Y`, and `B : W → F*V` is an isomorphism over `Y`

## The text, paraphrased

(p. 395) For a strong bundle `(Q : V → X, μ_V)` over an ep-groupoid and `F : Y → X`, the
pull-back `F*Q : F*V → Y`, `F*V = {(y, v) | F(y) = Q(v)}`, with
`μ_{F*V}(φ, (y, v)) = (t(φ), μ_X(F(φ), v))` "defines the strong bundle" over the ep-groupoid
`Y`.  For a proper strong bundle covering functor `A : W → V` covering `F`, `B(w) = (P(w), A(w))`
satisfies (8.23) and (Lemma 8.5.10) is a strong bundle isomorphism over the ep-groupoid `Y`
covering the identity of `Y`.

## What is formalized

* `EpStrongBundle.pullbackBundle2021 EV F`: the strong bundle `(F*Q, μ_{F*V})` over the
  ep-groupoid `Y` (Definition 8.3.1: `μ_{F*V}` is a surjective strong bundle map covering `t`, a
  local sc-diffeomorphism, with the unit and composition laws), for **every** sc-smooth functor
  `F : Y → X`; it is Chapter 10's pull-back `EpStrongBundle.pullbackAlong`, and its structure map
  is the formula `pullbackμ` of `Book2021.lean` (`pullbackBundle2021_μ`).
* `EpStrongBundle.pullbackBundle2021_isStrongBundle`: the text's sentence, as the existence of an
  `EpStrongBundle` on `F*Q` with structure map `μ_{F*V}`.
* For a proper strong bundle covering functor `h` (Definition 8.5.9):
  `IsProperStrongBundleCovering2021.isMap_bundleB` and `isMap_bundleBInv` (`B` and `B⁻¹` are strong
  bundle maps between strong bundles over ep-groupoids, Definition 8.3.2, covering the identity
  functor of `Y`), and **`lemma_8_5_10_full`**: `B` is a strong bundle isomorphism `W → F*V` over
  the ep-groupoid `Y` in the sense of Definition 8.3.2 in both directions.

## Reading

"Strong bundle isomorphism over the ep-groupoid `Y`" is read as: `B` and `B⁻¹` are inverse strong
bundle maps of strong bundles over ep-groupoids (Definition 8.3.2, `EpStrongBundle.IsMap`),
covering the identity functor of `Y`, the target carrying the structure `pullbackBundle2021`.
This closes the part of the lemma left open in `Book2021.lean` (only the formula of `μ_{F*V}` was
used there).
-/

set_option maxSynthPendingDepth 3

open Set Function

namespace Polyfold

universe u

section PullbackBundle

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}
  {V : Type u} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] {BV : StrongBundle X.PObj Q}
  [ParacompactSpace (pullbackSpace Q X.src)]
  (EV : EpStrongBundle X BV) (F : EpFunctor Y X)
  [ParacompactSpace (pullbackSpace Q F.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj Q F.obj) Y.src)]

namespace EpStrongBundle

/-- **The strong bundle `(F*Q : F*V → Y, μ_{F*V})` over the ep-groupoid `Y`** (2021 p. 395):
Part I's pull-back `F*V` with `μ_{F*V}(φ, (y, v)) = (t(φ), μ_X(F(φ), v))`; it is Chapter 10's
`pullbackAlong`, which proves the conditions of Definition 8.3.1. -/
noncomputable abbrev pullbackBundle2021 : EpStrongBundle Y (BV.pullback F.isScSmoothMap_obj) :=
  EV.pullbackAlong F

/-- The structure map of `pullbackBundle2021` is the text's `μ_{F*V}` (`pullbackμ`). -/
theorem pullbackBundle2021_μ (φ : MorY) (q : pullbackSpace Q F.obj)
    (hq : (q : ObjY × V).1 = Y.src φ) :
    (pullbackBundle2021 EV F).μ ⟨(φ, q), hq⟩ = pullbackμ EV F φ q hq := rfl

/-- **2021 p. 395, "the pull-back `F*Q` defines the strong bundle over `Y`"**: for every sc-smooth
functor `F : Y → X`, the pull-back `F*Q : F*V → Y` with the structure map `μ_{F*V}` satisfies the
conditions of Definition 8.3.1. -/
theorem pullbackBundle2021_isStrongBundle :
    ∃ E : EpStrongBundle Y (BV.pullback F.isScSmoothMap_obj),
      ∀ (φ : MorY) (q : pullbackSpace Q F.obj) (hq : (q : ObjY × V).1 = Y.src φ),
        E.μ ⟨(φ, q), hq⟩ = pullbackμ EV F φ q hq :=
  ⟨pullbackBundle2021 EV F, pullbackBundle2021_μ EV F⟩

end EpStrongBundle

end PullbackBundle

section Lemma8510

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
  {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X} {A : W → V}
  [ParacompactSpace (pullbackSpace Q F.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj Q F.obj) Y.src)]

namespace EpStrongBundle.IsProperStrongBundleCovering2021

variable (h : EW.IsProperStrongBundleCovering2021 EV F A)

/-- **`B : W → F*V` is a strong bundle map over the ep-groupoid `Y`** (Definition 8.3.2), covering
the identity functor of `Y`: a strong bundle map covering `id` with (8.23). -/
theorem isMap_bundleB : EW.IsMap (pullbackBundle2021 EV F) (EpFunctor.id Y) h.bundleB where
  isStrongBundleMap := h.isStrongBundleMap_bundleB
  map_μ γ w hw := h.bundleB_μ γ w hw

/-- **`B⁻¹ : F*V → W` is a strong bundle map over the ep-groupoid `Y`** (Definition 8.3.2),
covering the identity functor of `Y`. -/
theorem isMap_bundleBInv :
    (pullbackBundle2021 EV F).IsMap EW (EpFunctor.id Y) h.bundleBInv where
  isStrongBundleMap := h.isStrongBundleMap_bundleBInv
  map_μ γ q hq := by
    apply h.bijective_bundleB.1
    rw [h.bundleB_bundleBInv]
    refine (pullbackBundle2021_μ EV F γ q hq).trans ?_
    refine Eq.trans ?_ (h.bundleB_μ γ (h.bundleBInv q) ((h.P_bundleBInv q).trans hq)).symm
    have key : ∀ (q' : pullbackSpace Q F.obj) (_ : q' = q) (hq' : (q' : ObjY × V).1 = Y.src γ),
        pullbackμ EV F γ q hq = pullbackμ EV F γ q' hq' := by
      rintro _ rfl _; rfl
    exact key _ (h.bundleB_bundleBInv q) _

/-- **2021 Lemma 8.5.10**, p. 395, in full: `F*V` with `μ_{F*V}` is a strong bundle over the
ep-groupoid `Y` (`pullbackBundle2021`), and `B(w) = (P(w), A(w))` is a strong bundle isomorphism
over `Y` covering the identity of `Y`: `B` and its inverse are strong bundle maps of strong bundles
over ep-groupoids (Definition 8.3.2) covering the identity functor, inverse to each other, and
`A = Ā ∘ B` with `Ā(y, v) = v`. -/
theorem lemma_8_5_10_full :
    EW.IsMap (pullbackBundle2021 EV F) (EpFunctor.id Y) h.bundleB ∧
      (pullbackBundle2021 EV F).IsMap EW (EpFunctor.id Y) h.bundleBInv ∧
      (∀ w, h.bundleBInv (h.bundleB w) = w) ∧ (∀ q, h.bundleB (h.bundleBInv q) = q) ∧
      ∀ w, A w = pullbackProj' Q F.obj (h.bundleB w) :=
  ⟨h.isMap_bundleB, h.isMap_bundleBInv, h.bundleBInv_bundleB, h.bundleB_bundleBInv,
    fun _ => rfl⟩

end EpStrongBundle.IsProperStrongBundleCovering2021

end Lemma8510

end Polyfold
