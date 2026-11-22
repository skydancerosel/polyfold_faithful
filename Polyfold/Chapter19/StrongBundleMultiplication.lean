import Polyfold.Chapter19.StrongBundleTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version", **Theorem 19.6.13** (p. 900), the multiplication (p. 904).
Numbers and pages are the 2021 text's.

# The multiplication of `M(Ψ̄, Ψ̄')` is a strong bundle map

## The text, paraphrased

(p. 904) The multiplication `m : M(Ψ̄', Ψ̄'') ₛ×ₜ M(Ψ̄, Ψ̄') → M(Ψ̄, Ψ̄'')` is understood through
the equivalent formulation
`m̄ : (M(Ψ', Ψ'') ₛ×ₚ' K') ×_{π_K', π_K' ∘ C} (M(Ψ, Ψ') ₛ×ₚ K) → M(Ψ, Ψ'') ₛ×ₚ K`,
`m̄(((q', φ', q''), k'), ((q, φ, q'), k)) = ((q, φ' ∘ φ, q''), k)`, covering
`m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`; it is sc-smooth since `m` is and
`((q, φ, q'), k) ↦ k` is.

## What is formalized (namespace `Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction`)

* `BFP`, `BFPpoly` (the fibred product `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` with its sub-M-polyfold
  structure, as in Definition 17.1.8 (c)), `pr₂BFP`, `mulBase` (`m`), `isScSmoothMap_pr₂BFP`,
  `isScSmoothMap_mulBase` (Corollary 19.5.2).
* `mulBundle`: the strong bundle over `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` on which `m̄` is defined, the
  pull-back of `bundleBar : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` by `pr₂`.
* `mulLift`, `mBar` (`m̄((h', h), h̄) = m(h̄', h̄)` with `h̄'` the element of `M(Ψ̄', Ψ̄'')` over
  `h'` with source `t(h̄)`), and **`theorem_19_6_13_m`**: `m̄` is a strong bundle map covering `m`.

## Readings

* We read the domain of `m̄` printed on p. 904 as the pull-back of `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` by
  `pr₂ : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ')`: a point `(((q', φ', q''), k'), ((q, φ, q'), k))`
  with `k' = π_K'(C((q, φ, q'), k))` is determined by `((q', φ', q''), (q, φ, q'))` and
  `((q, φ, q'), k)`, and `H` identifies the latter with `h̄ ∈ M(Ψ̄, Ψ̄')`.  Through this
  identification `M(Ψ̄', Ψ̄'') ₛ×ₜ M(Ψ̄, Ψ̄')` is the total space of `mulBundle` and the
  multiplication is `mBar`; "the multiplication is a strong bundle map" is read as
  `theorem_19_6_13_m`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

universe u

variable {C : GroupoidalCategory.{u}}

open GroupoidStr (TransitionSet)

namespace StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} {Fb : StrongBundleUniformizerConstruction μ}
  (Fbar : Fb.BundleTransitionData) (Ψ Ψ' Ψ'' : Fb.Unif)

/-- **The fibred product `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`** (the domain of `m`). -/
abbrev BFP : Set (MS Fbar Ψ' Ψ'' × MS Fbar Ψ Ψ') :=
  MPolyfold.fibredProduct
    (fun a : Fbar.toTD.Tr (Fb.baseUnif Ψ') (Fb.baseUnif Ψ'') =>
      (a : (Fb.baseUnif Ψ').1.Trans (Fb.baseUnif Ψ'').1).src)
    (fun a : Fbar.toTD.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') =>
      (a : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1).tgt)

instance instParacompactSpaceProdMS : ParacompactSpace (MS Fbar Ψ' Ψ'' × MS Fbar Ψ Ψ') :=
  MPolyfold.paracompactSpace_prod (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ') (Fb.baseUnif Ψ''))
    (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))

instance instParacompactSpaceBFP : ParacompactSpace (BFP Fbar Ψ Ψ' Ψ'') :=
  ((Fbar.toTD.transPolyfold (Fb.baseUnif Ψ') (Fb.baseUnif Ψ'')).prod
    (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))).paracompactSpace_subtype _

/-- `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` is a sub-M-polyfold of the product (`s` is a local
sc-diffeomorphism, Proposition 2.5.20). -/
theorem isSubMPolyfold_BFP :
    ((Fbar.toTD.transPolyfold (Fb.baseUnif Ψ') (Fb.baseUnif Ψ'')).prod
      (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))).IsSubMPolyfold
      (BFP Fbar Ψ Ψ' Ψ'') :=
  MPolyfold.isSubMPolyfold_fibredProduct
    (Fbar.toTD.isLocalScDiffeo_src (Fb.baseUnif Ψ') (Fb.baseUnif Ψ''))
    (Fbar.toTD.isLocalScDiffeo_tgt (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')).isScSmoothMap

/-- The M-polyfold structure of `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`. -/
def BFPpoly : MPolyfold (BFP Fbar Ψ Ψ' Ψ'') :=
  MPolyfold.subPolyfold (isSubMPolyfold_BFP Fbar Ψ Ψ' Ψ'')

/-- The projection `pr₂ : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ')`. -/
abbrev pr₂BFP (z : BFP Fbar Ψ Ψ' Ψ'') : MS Fbar Ψ Ψ' := z.1.2

/-- The multiplication `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`. -/
abbrev mulBase (z : BFP Fbar Ψ Ψ' Ψ'') : MS Fbar Ψ Ψ'' :=
  Fbar.toTD.toTr (TransitionSet.mul z)

theorem isScSmoothMap_pr₂BFP :
    (BFPpoly Fbar Ψ Ψ' Ψ'').IsScSmoothMap (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (pr₂BFP Fbar Ψ Ψ' Ψ'') :=
  (MPolyfold.isScSmoothMap_snd _ _).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth (isSubMPolyfold_BFP Fbar Ψ Ψ' Ψ''))

theorem isScSmoothMap_mulBase :
    (BFPpoly Fbar Ψ Ψ' Ψ'').IsScSmoothMap
      (Fbar.toTD.transPolyfold (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'')) (mulBase Fbar Ψ Ψ' Ψ'') :=
  Fbar.toTD.isScSmoothMap_mul (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') (Fb.baseUnif Ψ'')

instance instParacompactSpaceMulPB :
    ParacompactSpace (pullbackSpace (projBar Fbar Ψ Ψ') (pr₂BFP Fbar Ψ Ψ' Ψ'')) :=
  paracompactSpace_pullbackSpace (BFPpoly Fbar Ψ Ψ' Ψ'') (bundleBar Fbar Ψ Ψ')

/-- **The strong bundle over `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` on which `m̄` is defined** (p. 904): the
pull-back of `p : M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` by `pr₂`; its points `((h', h), h̄)` correspond to the
pairs `(h̄', h̄)` of `M(Ψ̄', Ψ̄'') ₛ×ₜ M(Ψ̄, Ψ̄')` over `(h', h)`. -/
def mulBundle : StrongBundle (BFPpoly Fbar Ψ Ψ' Ψ'')
    (pullbackProj (projBar Fbar Ψ Ψ') (pr₂BFP Fbar Ψ Ψ' Ψ'')) :=
  (bundleBar Fbar Ψ Ψ').pullback (isScSmoothMap_pr₂BFP Fbar Ψ Ψ' Ψ'')


/-- The lift `(q', φ', k')` of `(h', h)` at `t(h̄)`: the element of `M(Ψ̄', Ψ̄'')` over `h'` with
source `t(h̄)`. -/
def mulLift (w : pullbackSpace (projBar Fbar Ψ Ψ') (pr₂BFP Fbar Ψ Ψ' Ψ'')) : Ψ'.1.Trans Ψ''.1 :=
  (Fb.strU Ψ').lift (Fb.strU Ψ'')
    (w.1.1.1.1 : (Fb.baseUnif Ψ').1.Trans (Fb.baseUnif Ψ'').1) (w.1.2 : Ψ.1.Trans Ψ'.1).tgt
    ((congrArg (fun a : MS Fbar Ψ Ψ' => (a : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1).tgt)
      w.2).trans w.1.1.2.symm)

/-- **2021 p. 904: `m̄`**, `m̄(((q', φ', q''), k'), ((q, φ, q'), k)) = ((q, φ' ∘ φ, q''), k)`. -/
def mBar (w : pullbackSpace (projBar Fbar Ψ Ψ') (pr₂BFP Fbar Ψ Ψ' Ψ'')) : MB Fbar Ψ Ψ'' :=
  Fbar.toETD.toTr (TransitionSet.comp (mulLift Fbar Ψ Ψ' Ψ'' w) (w.1.2 : Ψ.1.Trans Ψ'.1)
    (TransitionSet.mor_composable_of_src_eq_tgt rfl))

/-- **2021 Theorem 19.6.13: the multiplication is a strong bundle map** covering
`m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')` (p. 904: `m̄ = H ∘ (m ∘ π, s ∘ π_{M(Ψ̄,Ψ̄')})`). -/
theorem theorem_19_6_13_m :
    (mulBundle Fbar Ψ Ψ' Ψ'').IsStrongBundleMap (bundleBar Fbar Ψ Ψ'') (mulBase Fbar Ψ Ψ' Ψ'')
      (mBar Fbar Ψ Ψ' Ψ'') := by
  have hΘ := (theorem_19_6_13_s Fbar Ψ Ψ').comp
    ((bundleBar Fbar Ψ Ψ').isStrongBundleMap_pullbackProj' (isScSmoothMap_pr₂BFP Fbar Ψ Ψ' Ψ''))
  have hpair := StrongBundle.isStrongBundleMap_pullbackPair (Fb.strU Ψ).B
    (isScSmoothMap_trSrc Fbar.toTD Ψ Ψ'') (l := mulBase Fbar Ψ Ψ' Ψ'')
    (isScSmoothMap_mulBase Fbar Ψ Ψ' Ψ'') hΘ
  have h := (theorem_19_6_13_H Fbar Ψ Ψ'').toMap.comp hpair
  have key : ∀ (a a' : (Fb.strU Ψ').toBase.Trans (Fb.strU Ψ'').toBase)
      (b b' : (Fb.strU Ψ).toBase.Trans (Fb.strU Ψ').toBase) (ha : a = a') (hb : b = b') hab hab',
      TransitionSet.comp a b hab = TransitionSet.comp a' b' hab' := by
    intros; subst_vars; rfl
  have e : (⇑(altHHomeo Fbar Ψ Ψ'') ∘ pullbackPair (Fb.strU Ψ).p (trSrc Fbar.toTD Ψ Ψ'')
      (mulBase Fbar Ψ Ψ' Ψ'' ∘ pullbackProj (projBar Fbar Ψ Ψ') (pr₂BFP Fbar Ψ Ψ' Ψ''))
      ((fun g : MB Fbar Ψ Ψ' => (g : Ψ.1.Trans Ψ'.1).src) ∘
        pullbackProj' (projBar Fbar Ψ Ψ') (pr₂BFP Fbar Ψ Ψ' Ψ'')) hΘ.covers) =
      mBar Fbar Ψ Ψ' Ψ'' := by
    funext w
    change (altHE Fbar Ψ Ψ'' _ : Ψ.1.Trans Ψ''.1) = TransitionSet.comp (mulLift Fbar Ψ Ψ' Ψ'' w)
      (w.1.2 : Ψ.1.Trans Ψ'.1) (TransitionSet.mor_composable_of_src_eq_tgt rfl)
    exact (Fb.strU Ψ).eq_of_proj (Fb.strU Ψ'') rfl
      ((((Fb.strU Ψ).proj_lift (Fb.strU Ψ'') _ _ _).trans
        (key _ _ _ _ ((Fb.strU Ψ').proj_lift (Fb.strU Ψ'') _ _ _) w.2 _
          (TransitionSet.mor_composable_of_src_eq_tgt w.1.1.2)).symm).trans
        ((Fb.strU Ψ).proj_comp (Fb.strU Ψ') (Fb.strU Ψ'') _ _ _).symm)
  rw [e] at h
  exact h

end StrongBundleUniformizerConstruction

namespace BasicStrongBundleConstruction

open StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} (B : C.BasicStrongBundleConstruction μ)

/-- **2021 Theorem 19.6.13, p. 900: the multiplication is a strong bundle map**, for a basic
bundle construction (representative `F̄ = B.rep`). -/
theorem theorem_19_6_13_m (Ψ Ψ' Ψ'' : B.U.Unif) :
    (mulBundle B.rep Ψ Ψ' Ψ'').IsStrongBundleMap (bundleBar B.rep Ψ Ψ'') (mulBase B.rep Ψ Ψ' Ψ'')
      (mBar B.rep Ψ Ψ' Ψ'') :=
  StrongBundleUniformizerConstruction.theorem_19_6_13_m B.rep Ψ Ψ' Ψ''

end BasicStrongBundleConstruction

end GroupoidalCategory

end Polyfold
