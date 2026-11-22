import Polyfold.Chapter17.StrongBundleStructuresExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.7:
**Definition 17.7.4** (p. 827) and the list of structure maps on p. 828, the multiplication `m̄`.
Numbers and pages are the 2021 text's.

# The multiplication `m̄` of a strong polyfold bundle construction

## The text, paraphrased

(p. 828) The multiplication
`m̄ : M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄') → M(Ψ̄, Ψ̄'')`, `m̄((b, k'), (a, k)) = (b ∘ a, k)`, is an
sc-smooth strong bundle map covering `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`.

## What is formalized (namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`)

* `TransFP`, `transFPPolyfold` (`M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` with its sub-M-polyfold structure, as in
  Definition 17.1.8 (c)), `transFPSnd` (`pr₂`), `transFPMul` (`m`), and their sc-smoothness.
* `transFPBundle`: the strong bundle over `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` on which `m̄` is defined, the
  pull-back of `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` by `pr₂`.
* `BarFP` (the literal fibred product `M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄')`: pairs with
  `s̄(b, k') = t̄(a, k)`, i.e. `k' = T(a, k)`) and `barFPEquiv : BarFP ≃ total space of
  transFPBundle`.
* `transMul` (`m̄` on the total space of `transFPBundle`) and **`isStrongBundleMap_transMul`**:
  `m̄` is an sc-smooth strong bundle map covering `m`.
* `transMulBar` (`m̄` on `BarFP`), `transMulBar_eq` (`m̄((b, k'), (a, k)) = (b ∘ a, k)`, the text's
  formula), `transMulBar_eq_transMul`, and `transT_transMul` (`T(b ∘ a, k) = T(b, T(a, k))`).
* Witness: `isStrongBundleMap_transMul_reflection` for the reflection bundle `reflQ`
  (`StrongBundleStructuresExamples`), where `-1` acts by `v ↦ -v` on the fibres.

## Readings

* We read the strong bundle structure of `M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄') → M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`
  as the pull-back of `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` (the pull-back `s*K`, see `StrongBundleStructures`)
  by `pr₂`: a point `((b, k'), (a, k))` of the fibred product has `k' = T(a, k)`, so it is
  determined by `(b, a)` and `(a, k)` (`barFPEquiv`).  With this structure the text's statement
  is `isStrongBundleMap_transMul`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace GCT

namespace VectorBundle

universe u

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}

open GroupoidStr (TransitionSet)

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData

variable (Q : V.StrongPolyfoldBundleConstruction S) (Ψ Ψ' Ψ'' : Q.Unif)

/-- **The fibred product `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`** (the domain of `m`). -/
abbrev TransFP :
    Set (S.Tr (Q.baseUnif Ψ') (Q.baseUnif Ψ'') × S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')) :=
  MPolyfold.fibredProduct (fun b : S.Tr (Q.baseUnif Ψ') (Q.baseUnif Ψ'') => b.src)
    (fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.tgt)

instance instParacompactSpaceProdTr :
    ParacompactSpace
      (S.Tr (Q.baseUnif Ψ') (Q.baseUnif Ψ'') × S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')) :=
  MPolyfold.paracompactSpace_prod (S.transPolyfold (Q.baseUnif Ψ') (Q.baseUnif Ψ''))
    (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ'))

instance instParacompactSpaceTransFP : ParacompactSpace (Q.TransFP Ψ Ψ' Ψ'') :=
  ((S.transPolyfold (Q.baseUnif Ψ') (Q.baseUnif Ψ'')).prod
    (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ'))).paracompactSpace_subtype _

/-- `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` is a sub-M-polyfold of the product (`s` is a local
sc-diffeomorphism). -/
theorem isSubMPolyfold_transFP :
    ((S.transPolyfold (Q.baseUnif Ψ') (Q.baseUnif Ψ'')).prod
      (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ'))).IsSubMPolyfold (Q.TransFP Ψ Ψ' Ψ'') :=
  MPolyfold.isSubMPolyfold_fibredProduct (S.isLocalScDiffeo_trSrc _ _)
    (S.isLocalScDiffeo_trTgt _ _).isScSmoothMap

/-- The M-polyfold structure of `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`. -/
def transFPPolyfold : MPolyfold (Q.TransFP Ψ Ψ' Ψ'') :=
  MPolyfold.subPolyfold (Q.isSubMPolyfold_transFP Ψ Ψ' Ψ'')

/-- `pr₂ : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ')`. -/
abbrev transFPSnd (z : Q.TransFP Ψ Ψ' Ψ'') : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') := z.1.2

/-- The multiplication `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`. -/
abbrev transFPMul (z : Q.TransFP Ψ Ψ' Ψ'') : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'') :=
  S.toTr (TransitionSet.mul z)

theorem isScSmoothMap_transFPSnd :
    (Q.transFPPolyfold Ψ Ψ' Ψ'').IsScSmoothMap (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ'))
      (Q.transFPSnd Ψ Ψ' Ψ'') :=
  (MPolyfold.isScSmoothMap_snd _ _).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth (Q.isSubMPolyfold_transFP Ψ Ψ' Ψ''))

/-- `m` is sc-smooth (Definition 17.1.8 (c)). -/
theorem isScSmoothMap_transFPMul :
    (Q.transFPPolyfold Ψ Ψ' Ψ'').IsScSmoothMap (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ''))
      (Q.transFPMul Ψ Ψ' Ψ'') :=
  S.isScSmoothMap_trMul (Q.baseUnif Ψ) (Q.baseUnif Ψ') (Q.baseUnif Ψ'')

/-- The total space of `transFPBundle`: pairs `((b, a), (a, k))`. -/
abbrev TransFPSpace : Type u :=
  pullbackSpace (pullbackProj Ψ.1.p fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src)
    (Q.transFPSnd Ψ Ψ' Ψ'')

instance instParacompactSpaceTransFPSpace : ParacompactSpace (Q.TransFPSpace Ψ Ψ' Ψ'') :=
  paracompactSpace_pullbackSpace (Q.transFPPolyfold Ψ Ψ' Ψ'') (Q.transBundle Ψ Ψ')

/-- **The strong bundle `M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄') → M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`** (reading): the
pull-back of `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')` by `pr₂`. -/
def transFPBundle : StrongBundle (Q.transFPPolyfold Ψ Ψ' Ψ'')
    (pullbackProj (pullbackProj Ψ.1.p fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src)
      (Q.transFPSnd Ψ Ψ' Ψ'')) :=
  (Q.transBundle Ψ Ψ').pullback (Q.isScSmoothMap_transFPSnd Ψ Ψ' Ψ'')

/-- `((b, a), (a, k)) ↦ k`, a strong bundle map covering `s ∘ pr₂`. -/
theorem isStrongBundleMap_transFPK :
    (Q.transFPBundle Ψ Ψ' Ψ'').IsStrongBundleMap Ψ.1.B
      ((fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'') => a.src) ∘ Q.transFPMul Ψ Ψ' Ψ'')
      (pullbackProj' Ψ.1.p (fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src) ∘
        pullbackProj' (pullbackProj Ψ.1.p fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src)
          (Q.transFPSnd Ψ Ψ' Ψ'')) :=
  (Ψ.1.B.isStrongBundleMap_pullbackProj' (Q.isScSmoothMap_trSrc Ψ Ψ')).comp
    ((Q.transBundle Ψ Ψ').isStrongBundleMap_pullbackProj' (Q.isScSmoothMap_transFPSnd Ψ Ψ' Ψ''))

/-- **`m̄`** on the total space of `transFPBundle`: `((b, a), (a, k)) ↦ (b ∘ a, k)`. -/
def transMul (w : Q.TransFPSpace Ψ Ψ' Ψ'') : Q.TransSpace Ψ Ψ'' :=
  pullbackPair Ψ.1.p (fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'') => a.src)
    (Q.transFPMul Ψ Ψ' Ψ'' ∘ pullbackProj _ (Q.transFPSnd Ψ Ψ' Ψ''))
    (pullbackProj' Ψ.1.p (fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src) ∘
        pullbackProj' _ (Q.transFPSnd Ψ Ψ' Ψ''))
    (Q.isStrongBundleMap_transFPK Ψ Ψ' Ψ'').covers w

/-- **Definition 17.7.4, p. 828: the multiplication `m̄` is an sc-smooth strong bundle map
covering `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`.** -/
theorem isStrongBundleMap_transMul :
    (Q.transFPBundle Ψ Ψ' Ψ'').IsStrongBundleMap (Q.transBundle Ψ Ψ'') (Q.transFPMul Ψ Ψ' Ψ'')
      (Q.transMul Ψ Ψ' Ψ'') :=
  Ψ.1.B.isStrongBundleMap_pullbackPair (Q.isScSmoothMap_trSrc Ψ Ψ'')
    (Q.isScSmoothMap_transFPMul Ψ Ψ' Ψ'') (Q.isStrongBundleMap_transFPK Ψ Ψ' Ψ'')

/-! ### The literal fibred product `M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄')` -/

/-- **`M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄')`**: pairs `((b, k'), (a, k))` with `s̄(b, k') = k'` equal to
`t̄(a, k) = T(a, k)`. -/
def BarFP : Type u :=
  {z : Q.TransSpace Ψ' Ψ'' × Q.TransSpace Ψ Ψ' // z.1.1.2 = Q.transT Ψ Ψ' z.2}

/-- The base point `(b, a)` of a point of the fibred product:
`s(b) = p'(k') = p'(T(a, k)) = t(a)`. -/
theorem barFP_src_eq (z : Q.BarFP Ψ Ψ' Ψ'') : z.1.1.1.1.src = z.1.2.1.1.tgt := by
  have h1 : Ψ'.1.p z.1.1.1.2 = z.1.1.1.1.src := z.1.1.2
  rw [← h1, z.2]
  exact p_transAct _ _ _

/-- **The identification of `M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄')` with the total space of
`transFPBundle`**: `((b, k'), (a, k)) ↦ ((b, a), (a, k))`, with inverse
`((b, a), (a, k)) ↦ ((b, T(a, k)), (a, k))`. -/
def barFPEquiv : Q.BarFP Ψ Ψ' Ψ'' ≃ Q.TransFPSpace Ψ Ψ' Ψ'' where
  toFun z := ⟨(⟨(z.1.1.1.1, z.1.2.1.1), Q.barFP_src_eq Ψ Ψ' Ψ'' z⟩, z.1.2), rfl⟩
  invFun w := ⟨(⟨(w.1.1.1.1, Q.transT Ψ Ψ' w.1.2), by
      have h2 : w.1.2.1.1 = w.1.1.1.2 := w.2
      have h3 : w.1.1.1.1.src = w.1.1.1.2.tgt := w.1.1.2
      exact (p_transAct w.1.2.1.1 w.1.2.1.2 w.1.2.2).trans
        ((congrArg (fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.tgt) h2).trans
          h3.symm)⟩, w.1.2), rfl⟩
  left_inv z := by
    obtain ⟨⟨⟨⟨b, k'⟩, hb⟩, x⟩, hz⟩ := z
    change k' = Q.transT Ψ Ψ' x at hz
    subst hz
    rfl
  right_inv w := by
    obtain ⟨⟨⟨⟨b, a⟩, hba⟩, x⟩, hw⟩ := w
    change x.1.1 = a at hw
    subst hw
    rfl

/-- **`m̄` on `M(Ψ̄', Ψ̄'') ₛ̄×ₜ̄ M(Ψ̄, Ψ̄')`**, `m̄((b, k'), (a, k)) = (b ∘ a, k)`. -/
def transMulBar (z : Q.BarFP Ψ Ψ' Ψ'') : Q.TransSpace Ψ Ψ'' :=
  ⟨(S.toTr (TransitionSet.comp z.1.1.1.1 z.1.2.1.1
      (TransitionSet.mor_composable_of_src_eq_tgt (Q.barFP_src_eq Ψ Ψ' Ψ'' z))), z.1.2.1.2),
    z.1.2.2⟩

/-- **The text's formula** (p. 828): `m̄((b, k'), (a, k)) = (b ∘ a, k)`. -/
theorem transMulBar_eq (z : Q.BarFP Ψ Ψ' Ψ'') :
    ((Q.transMulBar Ψ Ψ' Ψ'' z).1.1 : (Q.baseUnif Ψ).1.Trans (Q.baseUnif Ψ'').1) =
        TransitionSet.comp z.1.1.1.1 z.1.2.1.1
          (TransitionSet.mor_composable_of_src_eq_tgt (Q.barFP_src_eq Ψ Ψ' Ψ'' z)) ∧
      (Q.transMulBar Ψ Ψ' Ψ'' z).1.2 = z.1.2.1.2 :=
  ⟨rfl, rfl⟩

/-- `m̄` on the literal fibred product is `transMul` through `barFPEquiv`. -/
theorem transMulBar_eq_transMul :
    Q.transMulBar Ψ Ψ' Ψ'' = Q.transMul Ψ Ψ' Ψ'' ∘ Q.barFPEquiv Ψ Ψ' Ψ'' := rfl

/-- **`T ∘ m̄`**: `T(b ∘ a, k) = T(b, T(a, k)) = t̄(b, k')`. -/
theorem transT_transMulBar (z : Q.BarFP Ψ Ψ' Ψ'') :
    Q.transT Ψ Ψ'' (Q.transMulBar Ψ Ψ' Ψ'' z) = Q.transT Ψ' Ψ'' z.1.1 := by
  obtain ⟨⟨⟨⟨b, k'⟩, hb⟩, ⟨⟨a, k⟩, hk⟩⟩, hz⟩ := z
  change k' = transAct a k hk at hz
  subst hz
  exact transAct_comp b a ((show Ψ'.1.p (transAct a k hk) = b.src from hb).symm.trans
    (p_transAct a k hk)) k hk

/-- `T ∘ m̄` on the total space of `transFPBundle`. -/
theorem transT_transMul (w : Q.TransFPSpace Ψ Ψ' Ψ'') :
    Q.transT Ψ Ψ'' (Q.transMul Ψ Ψ' Ψ'' w) =
      Q.transT Ψ' Ψ'' ((Q.barFPEquiv Ψ Ψ' Ψ'').symm w).1.1 := by
  have h := Q.transT_transMulBar Ψ Ψ' Ψ'' ((Q.barFPEquiv Ψ Ψ' Ψ'').symm w)
  rwa [transMulBar_eq_transMul, comp_apply, Equiv.apply_symm_apply] at h

end StrongPolyfoldBundleConstruction

namespace ReflectionBundle

open StrongPolyfoldBundleConstruction StrongBundleUniformizerConstruction

/-- The transition `a = (0, (-1, 0), 0)` of `M(Ψ, Ψ)` for the reflection bundle. -/
def reflTr : Tr where
  src := show Fin 1 → ℝ from 0
  mor := ((-1 : ℤˣ), 0)
  tgt := show Fin 1 → ℝ from 0
  src_mor := rfl
  tgt_mor := smul_zero (-1 : ℤˣ)

/-- **Witness for `m̄`** (p. 828) on the reflection bundle (`-1` acts by `v ↦ -v` on the fibres
`ℝ`; `reflΨ` is its only uniformizer, `unif_eq`): `m̄` is a strong bundle map covering `m`, and it
is not trivial: for `a = (0, (-1, 0), 0)` and `k = (0, 1)` the point `((a, a), (a, k))` has
`t̄(a, k) = -k ≠ k` while `t̄(m̄((a, a), (a, k))) = T(a ∘ a, k) = k`. -/
theorem isStrongBundleMap_transMul_reflection (Ψ : reflQ.Unif) :
    (reflQ.transFPBundle Ψ Ψ Ψ).IsStrongBundleMap (reflQ.transBundle Ψ Ψ)
        (reflQ.transFPMul Ψ Ψ Ψ) (reflQ.transMul Ψ Ψ Ψ) ∧
      ∃ w : reflQ.TransFPSpace Ψ Ψ Ψ,
        reflQ.transT Ψ Ψ (reflQ.transMul Ψ Ψ Ψ w) = w.1.2.1.2 ∧
          reflQ.transT Ψ Ψ w.1.2 ≠ w.1.2.1.2 := by
  refine ⟨reflQ.isStrongBundleMap_transMul Ψ Ψ Ψ, ?_⟩
  obtain rfl := unif_eq Ψ
  let x : reflUC.TransSpace reflΨ reflΨ := ⟨(reflTr, ((0 : Fin 1 → ℝ), fun _ => 1)),
    show reflΨ.1.p ((0 : Fin 1 → ℝ), fun _ => 1) = reflTr.src from rfl⟩
  refine ⟨⟨(⟨(reflTr, reflTr), show reflTr.src = reflTr.tgt from rfl⟩, x), rfl⟩, ?_, ?_⟩
  · refine (transT_eq _).trans ?_
    change (((-1 : ℤˣ) * (-1 : ℤˣ)) • (((0 : Fin 1 → ℝ), fun _ => (1 : ℝ)) : K)) = _
    rw [show ((-1 : ℤˣ) * (-1 : ℤˣ)) = 1 by decide, one_smul]
  · intro h
    have h' := (transT_eq x).symm.trans h
    have := congrFun (congrArg Prod.snd h') 0
    change ((-1 : ℤˣ) • (((0 : Fin 1 → ℝ), fun _ => (1 : ℝ)) : K)).2 0 = 1 at this
    norm_num [Units.smul_def] at this

end ReflectionBundle

end VectorBundle

end GCT

end Polyfold
