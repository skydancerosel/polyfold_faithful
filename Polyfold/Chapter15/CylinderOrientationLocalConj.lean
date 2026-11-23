import Polyfold.Chapter12.IntervalProductLocalIso
import Polyfold.Chapter12.OrientationGermSquare

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276
(Remark 6.6.19), §12.5, pp. 592–594 (Lemma 12.5.1), and §15.4, p. 703.

# The orientation `e ∧ o` over `[0, 1] × X` and local isomorphisms between two bundles

## The text, paraphrased

Over `[0, 1] × X` the section `f̃(t, x) = f(x)` is oriented by the standard orientation of
`[0, 1]` and an orientation `o` of `f` (Remark 6.6.19; p. 703).  The construction is local and
compatible with local strong bundle isomorphisms.

## What is formalized

`IntervalProductLocalIso.lean` treats a local isomorphism of one bundle.  Here the same
statements are made for a local strong bundle isomorphism `L₀ : Y|U₀ → Y'|U₀'` between two
strong bundles and a local isomorphism `L` of the pull-back bundles over `[0, 1] × X` and
`[0, 1] × X'` which is `id × L₀` near a point (for instance the inclusion of the restriction of
`Y'` to an open subset of `X'`).

* `ChartPoint.ivOrFirst₀_conj₂`: the conjugate of `e ∧ o` by `(A × 1, Γ)` is
  `e ∧` (the conjugate of `o` by `(A, Γ)`), for chart points of two bundles.
* `StrongBundle.LocalIso.IsIntervalProductAt₂`: `L` is `id × L₀` near a point.
* `baseDeriv_mpullPt_ivPt`, `fiberMap_mpullPt_ivPt`, `coe_mmorT_ivPt`, `coe_mmorK_ivPt`: the
  identifications from a chart point carried by `L` to the product chart point over a chart
  point carried by `L₀`.
* **`morVia_ivOrFirst₀`**: the orientation map of `L` carries `e ∧ o` to `e ∧ (L₀)_* o`.
* **`orxViaAt_ivFirstFun`**: the orientation map of `L` carries `(e ∧ o')_{(t, x)}` to
  `(e ∧ o)_{(t, a)}` when `(L₀)_* o'_x = o_a`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v u' v'

/-! ### Conjugating `e ∧ o` between two bundles -/

section Conj

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  [ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))]
  {f' : X' → Y'}

namespace ChartPoint

variable {x : X} {x' : X'} (p : ChartPoint B x) (p' : ChartPoint B' x') (b : Fin 1 → Bool)
  {t : Fin 1 → unitInterval} (ht : t ∈ (chart b).source) (b' : Fin 1 → Bool)
  {t' : Fin 1 → unitInterval} (ht' : t' ∈ (chart b').source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
  (q₀' : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))

set_option maxHeartbeats 1600000 in
-- the determinant lines over the two product chart points are compared term by term
private theorem ivOrFirst₀_conj₂_aux (hf : B.IsScFredholmSection f)
    (hf' : B'.IsScFredholmSection f')
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hfc' : (ivBundle B').IsScFredholmSection (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (hx : x ∈ PX.smoothSet) (hx' : x' ∈ PX'.smoothSet)
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f').Nonempty)
    (A : ↥p.T ≃L[ℝ] ↥p'.T) (Γ : ↥p.K ≃L[ℝ] ↥p'.K)
    (Ah : ↥(p.ivPt b ht q₀).T ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').T)
    (Γh : ↥(p.ivPt b ht q₀).K ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').K)
    (hA : ∀ v, p'.ivT b' ht' q₀' (Ah v) =
      (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (p.ivT b ht q₀ v))
    (hΓ : ∀ k, p'.ivK b' ht' q₀' (Γh k) = Γ (p.ivK b ht q₀ k))
    (hmem : ∀ S' ∈ p'.linSet f', ((Γ.symm : ↥p'.K →L[ℝ] ↥p.K) ∘L S' ∘L
      (A : ↥p.T →L[ℝ] ↥p'.T)) ∈ p.linSet f)
    (hmemh : ∀ S' ∈ (p'.ivPt b' ht' q₀').linSet (cubeLift (n := 1) f' hf'.isScSmooth.1),
      ((Γh.symm : ↥(p'.ivPt b' ht' q₀').K →L[ℝ] ↥(p.ivPt b ht q₀).K) ∘L S' ∘L
        (Ah : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p'.ivPt b' ht' q₀').T)) ∈
          (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (o : p.Or f hf) {L' : ↥p'.T →L[ℝ] ↥p'.K} (hL' : L' ∈ p'.linSet f')
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) (h : ∀ v, L' (A v) = Γ (L v)) :
    (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o).conj
        (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc') Ah Γh hmemh =
      p'.ivOrFirst₀ b' ht' q₀' hf' hfc' hx' hne'
        (o.conj (hC' := p'.isFredholm_of_mem_linSet hf') A Γ hmem) := by
  have hLh := p.ivLin_mem_linSet_cubeLift b ht q₀ hf hx hL
  have hLh' := p'.ivLin_mem_linSet_cubeLift b' ht' q₀' hf' hx' hL'
  have hconj : ∀ v, p'.ivLin b' ht' q₀' L' (Ah v) = Γh (p.ivLin b ht q₀ L v) := fun v => by
    apply (p'.ivK b' ht' q₀').injective
    have e1 : p'.ivK b' ht' q₀' (p'.ivLin b' ht' q₀' L' (Ah v)) =
        L' (p'.ivT b' ht' q₀' (Ah v)).1 :=
      (p'.ivLin_conj b' ht' q₀' L' (Ah v)).symm.trans (extOp_apply _ _)
    have e2 : (p'.ivT b' ht' q₀' (Ah v)).1 = A (p.ivT b ht q₀ v).1 :=
      congrArg Prod.fst (hA v)
    have e3 : p.ivK b ht q₀ (p.ivLin b ht q₀ L v) = L (p.ivT b ht q₀ v).1 :=
      (p.ivLin_conj b ht q₀ L v).symm.trans (extOp_apply _ _)
    rw [e1, e2, h, hΓ, e3]
  have : PreconnectedSpace
      ((p'.ivPt b' ht' q₀').linSet (cubeLift (n := 1) f' hf'.isScSmooth.1)) :=
    isPreconnected_iff_preconnectedSpace.1
      ((p'.ivPt b' ht' q₀').convex_linSet hfc').isPreconnected
  have eL := LineOrientation.conj_apply
    (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc') Ah Γh hmemh
    (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o) hLh hLh' hconj
  have eL2 := p.ivOrFirst₀_apply b ht q₀ hf hfc hx hne o L hL
  have eR := p'.ivOrFirst₀_apply b' ht' q₀' hf' hfc' hx' hne'
    (o.conj (hC' := p'.isFredholm_of_mem_linSet hf') A Γ hmem) L' hL'
  have eR2 := LineOrientation.conj_apply (hC' := p'.isFredholm_of_mem_linSet hf') A Γ hmem o hL
    hL' h
  have hequiv : (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
      (p.isFredholm_of_mem_linSet hf _ hL)
        ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hLh)) ≪≫ₗ conjDet Ah Γh hconj =
      conjDet A Γ h ≪≫ₗ extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀')
        (p'.isFredholm_of_mem_linSet hf' _ hL')
          ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc' _ hLh') :=
    LinearEquiv.ext fun y => conjDet_extConjDetFirst_of_conj (p.ivT b ht q₀) (p.ivK b ht q₀)
      (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀') A Γ Ah Γh hA hΓ (L := L) (L' := L') h hconj
      (p.isFredholm_of_mem_linSet hf _ hL) (p'.isFredholm_of_mem_linSet hf' _ hL')
      ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hLh)
      ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc' _ hLh') y
  have m1 := ray_map_map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
    (p.isFredholm_of_mem_linSet hf _ hL) ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hLh))
    (conjDet Ah Γh hconj) (o ⟨L, hL⟩)
  have m2 := ray_map_map (conjDet A Γ h)
    (extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀')
      (p'.isFredholm_of_mem_linSet hf' _ hL')
      ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc' _ hLh')) (o ⟨L, hL⟩)
  have m3 := congrArg (fun e => Module.Ray.map e (o ⟨L, hL⟩)) hequiv
  refine LineOrientation.eq_of_apply_eq ⟨_, hLh'⟩ ?_
  refine (eL.trans (congrArg (Module.Ray.map (conjDet Ah Γh hconj)) eL2)).trans ?_
  refine Eq.trans ?_ (eR.trans (congrArg (Module.Ray.map (extConjDetFirst (p'.ivT b' ht' q₀')
    (p'.ivK b' ht' q₀') (p'.isFredholm_of_mem_linSet hf' _ hL')
    ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc' _ hLh'))) eR2)).symm
  exact m1.trans (m3.trans m2.symm)

/-- **The conjugate of `e ∧ o` is `e ∧` (the conjugate of `o`), for two bundles**: let `p`,
`p'` be chart points of `Y` and `Y'` at smooth points `x`, `x'`, and `A : T_xX ≅ T_{x'}X'`,
`Γ : Y_x ≅ Y'_{x'}` carry `Lin(f', x')` into `Lin(f, x)`.  If `Â`, `Γ̂` between the product
chart points at `(t, x)`, `(t', x')` are `A × 1` and `Γ` in the product coordinates, then the
conjugate by `(Â, Γ̂)` of the orientation `e ∧ o` of `f̃` at `(t, x)` is
`e ∧ (o conjugated by (A, Γ))` at `(t', x')`. -/
theorem ivOrFirst₀_conj₂ (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hfc' : (ivBundle B').IsScFredholmSection (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (hx : x ∈ PX.smoothSet) (hx' : x' ∈ PX'.smoothSet)
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f').Nonempty)
    (A : ↥p.T ≃L[ℝ] ↥p'.T) (Γ : ↥p.K ≃L[ℝ] ↥p'.K)
    (Ah : ↥(p.ivPt b ht q₀).T ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').T)
    (Γh : ↥(p.ivPt b ht q₀).K ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').K)
    (hA : ∀ v, p'.ivT b' ht' q₀' (Ah v) =
      (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (p.ivT b ht q₀ v))
    (hΓ : ∀ k, p'.ivK b' ht' q₀' (Γh k) = Γ (p.ivK b ht q₀ k))
    (hmem : ∀ S' ∈ p'.linSet f', ((Γ.symm : ↥p'.K →L[ℝ] ↥p.K) ∘L S' ∘L
      (A : ↥p.T →L[ℝ] ↥p'.T)) ∈ p.linSet f)
    (hmemh : ∀ S' ∈ (p'.ivPt b' ht' q₀').linSet (cubeLift (n := 1) f' hf'.isScSmooth.1),
      ((Γh.symm : ↥(p'.ivPt b' ht' q₀').K →L[ℝ] ↥(p.ivPt b ht q₀).K) ∘L S' ∘L
        (Ah : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p'.ivPt b' ht' q₀').T)) ∈
          (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (o : p.Or f hf) :
    (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o).conj
        (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc') Ah Γh hmemh =
      p'.ivOrFirst₀ b' ht' q₀' hf' hfc' hx' hne'
        (o.conj (hC' := p'.isFredholm_of_mem_linSet hf') A Γ hmem) :=
  p.ivOrFirst₀_conj₂_aux p' b ht b' ht' q₀ q₀' hf hf' hfc hfc' hx hx' hne hne' A Γ Ah Γh hA hΓ
    hmem hmemh o hne'.some_mem (hmem _ hne'.some_mem)
    (fun v => (Γ.apply_symm_apply (hne'.some (A v))).symm)

end ChartPoint

end Conj

/-! ### Local isomorphisms of the pull-back bundles that are products near a point -/

section Germ

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  [ParacompactSpace ((Fin 1 → unitInterval) × X')]
  [ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))]
  {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set ((Fin 1 → unitInterval) × X)} {U' : Set ((Fin 1 → unitInterval) × X')}
  {U₀ : Set X} {U₀' : Set X'}

/-- **A local strong bundle isomorphism between the pull-back bundles over `[0, 1] × X` and
`[0, 1] × X'` that is the product `id × L₀` near `z`**: on an open `N ∋ z` the base map is
`(s, y) ↦ (s, ϕ₀(y))`, and on the fibre over `z` the bundle map is that of `L₀`. -/
structure IsIntervalProductAt₂ (L : LocalIso (ivBundle B) (ivBundle B') U U')
    (L₀ : LocalIso B B' U₀ U₀') (z : (Fin 1 → unitInterval) × X) : Prop where
  exists_nhds : ∃ N : Set ((Fin 1 → unitInterval) × X), IsOpen N ∧ z ∈ N ∧ N ⊆ U ∧
    (∀ y ∈ N, y.2 ∈ U₀) ∧ ∀ y ∈ N, L.ϕ y = (y.1, L₀.ϕ y.2)
  fiber : ∀ w : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X),
    pullbackProj P Prod.snd w = z → (L.Φ w).1.2 = L₀.Φ w.1.2

variable {L : LocalIso (ivBundle B) (ivBundle B') U U'} {L₀ : LocalIso B B' U₀ U₀'}
  {x : X'} {a : X} {t : Fin 1 → unitInterval}

/-- **The base derivative from a chart point carried by `L` to the product chart point over a
chart point carried by `L₀`** is the one from the original chart point to the original product
chart point, when `L` is `id × L₀` near `(t, a)`. -/
theorem baseDeriv_mpullPt_ivPt (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (A : ChartPoint (ivBundle B') (t, x)) (hA : A.c.φ.source ⊆ U') (hz : (t, a) ∈ U)
    (hϕ : L.ϕ (t, a) = (t, x)) (a₀ : ChartPoint B' x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (v : A.c.φ.model.E 0) :
    (L.mpullPt A hA hz hϕ).baseDeriv ((L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀') v =
      A.baseDeriv (a₀.ivPt b ht q₀) v := by
  obtain ⟨N, hNo, hzN, hNU, hNU₀, hNϕ⟩ := hL.exists_nhds
  set a' := L.mpullPt A hA hz hϕ with ha'
  set Q := a₀.ivPt b ht q₀ with hQ
  set Q' := (L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀' with hQ'
  obtain ⟨G, hGo, hG⟩ := a'.c.φ.exists_isOpen_image_eq (s := N ∩ a'.c.φ.source)
    inter_subset_right (hNo.inter a'.c.φ.isOpen_source)
  set R' := ((A.baseRet Q).restrict (a'.isOpen_overlapW Q')).restrict hGo with hR'
  have hV₁ : R'.U ⊆ (A.baseRet Q).U := fun u hu => hu.1.1
  have hV₃ : R'.U ⊆ (a'.baseRet Q').U := fun u hu => ⟨(A.baseRet_U_subset Q) hu.1.1, hu.1.2⟩
  have hzG : r A.c.R (A.c.φ.model.E.toBase 1 A.z) ∈ G := by
    rw [A.r_toBase_z]
    have : a'.c.φ (t, a) ∈ a'.c.φ '' (N ∩ a'.c.φ.source) := ⟨(t, a), ⟨hzN, a'.mem_source⟩, rfl⟩
    rw [hG] at this
    have h' : a'.c.φ (t, a) = A.c.φ.model.E.toBase 1 A.z := a'.toBase_z.symm
    rw [h'] at this
    exact this.2
  have hzV : A.z ∈ A.c.φ.model.E.lvlSet R'.U 1 :=
    ⟨⟨A.z_mem_baseRet Q, (a'.z_mem_baseRet Q').2⟩, hzG⟩
  have hOO : a'.c.φ.model.O = A.c.φ.model.O := L.transportChart_model_O A.c hA
  have heq : EqOn (a'.c.φ.transition Q'.c.φ ∘ a'.baseRet Q')
      (A.c.φ.transition Q.c.φ ∘ A.baseRet Q) R'.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a'.exists_eq_of_mem_baseRet Q' (hV₃ hu)
    have hrG : r A.c.R u ∈ a'.c.φ.model.O ∩ G :=
      ⟨hOO ▸ A.c.r_mem_O ((A.baseRet_U_subset Q) hu.1.1), hu.2⟩
    rw [← hG] at hrG
    obtain ⟨y₂, ⟨hy₂N, hy₂s⟩, hy₂u⟩ := hrG
    have hyy : y₂ = y := by
      have e : a'.c.φ y₂ = a'.c.φ y := hy₂u.trans hyu
      rw [← a'.c.φ.symm_apply_apply hy₂s, ← a'.c.φ.symm_apply_apply hy, e]
    subst hyy
    have hyu' : r A.c.R u = A.c.φ (L.ϕ y₂) := hyu
    change Q'.c.φ (L.g (A.c.φ.symm (r A.c.R u))) = Q.c.φ (A.c.φ.symm (r A.c.R u))
    rw [hyu', A.c.φ.symm_apply_apply hy.2, L.base.left_inv y₂ hy.1, hNϕ y₂ hy₂N]
    rfl
  exact congrArg (fun T : A.c.φ.model.E 0 →L[ℝ] Q.c.φ.model.E 0 => T v)
    (scDeriv_eq_of_eqOn_relOpen R'.relOpen (a'.isSc1_transition Q') (A.isSc1_transition Q) hV₃ hV₁
      heq hzV)

/-- **The fibre transition from a chart point carried by `L` to the product chart point over a
chart point carried by `L₀`** is the one from the original chart point to the original product
chart point, when on the fibre over `(t, a)` the bundle map of `L` is that of `L₀`. -/
theorem fiberMap_mpullPt_ivPt (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (A : ChartPoint (ivBundle B') (t, x)) (hA : A.c.φ.source ⊆ U') (hz : (t, a) ∈ U)
    (hϕ : L.ϕ (t, a) = (t, x)) (a₀ : ChartPoint B' x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) (k : A.c.F 0) :
    (L.mpullPt A hA hz hϕ).fiberMap ((L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀') k =
      A.fiberMap (a₀.ivPt b ht q₀) k := by
  set w : A.c.φ.model.E 0 × A.c.F 0 :=
    (A.c.φ.model.E.toBase 1 A.z, ρ A.c.R (A.c.φ.model.E.toBase 1 A.z) k) with hw
  have hwK : w ∈ A.c.toPartialEquiv.target := by
    rw [A.c.target_eq]; exact A.c.mem_K_ρ A.toBase_z_mem_O k
  have hsrc := A.c.toPartialEquiv.map_target hwK
  set y := A.c.toPartialEquiv.symm w with hy
  have hPy : pullbackProj P' Prod.snd y = (t, x) := by
    have h1 := A.c.covers _ hsrc
    rw [A.c.toPartialEquiv.right_inv hwK] at h1
    have h2 : A.c.φ.model.E.toBase 1 A.z = A.c.φ (pullbackProj P' Prod.snd y) := h1
    rw [A.c.source_eq] at hsrc
    rw [A.toBase_z] at h2
    rw [← A.c.φ.symm_apply_apply hsrc, ← h2, A.c.φ.symm_apply_apply A.mem_source]
  have hU' : pullbackProj P' Prod.snd y ∈ U' := by rw [hPy]; exact hA A.mem_source
  have hPΨ : pullbackProj P Prod.snd (L.Ψ y) = (t, a) := by
    rw [L.covers_inv _ hU', hPy, ← hϕ, L.base.left_inv _ hz]
  have hfib := hL.fiber (L.Ψ y) hPΨ
  rw [L.zero.right_inv _ hU'] at hfib
  change (a₀.c (L₀.Φ (L.Ψ y).1.2)).2 = (a₀.c y.1.2).2
  rw [← hfib]

/-- The map `T_{(t,x)} → T_{(t,a)}` of `L` between the product chart points is the identity of
`ℝ × T_zO` when `L` is `id × L₀` near `(t, a)`. -/
theorem coe_mmorT_ivPt (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (A : ChartPoint (ivBundle B') (t, x)) (hA : A.c.φ.source ⊆ U') (hz : (t, a) ∈ U)
    (hϕ : L.ϕ (t, a) = (t, x)) (a₀ : ChartPoint B' x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (v : ↥(a₀.ivPt b ht q₀).T) :
    (Subtype.val (L.mmorT (a₀.ivPt b ht q₀) ((L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀') A hA hz
      hϕ v) : (Fin 1 → ℝ) × a₀.c.φ.model.E 0) = Subtype.val v := by
  rw [mmorT_apply]
  have h1 := baseDeriv_mpullPt_ivPt hL A hA hz hϕ a₀ ha₀ ha hϕ₀ b ht q₀ q₀'
    (Subtype.val ((a₀.ivPt b ht q₀).transferT A v))
  have h2 := congrArg Subtype.val (((a₀.ivPt b ht q₀).transferT_trans_apply A
    (a₀.ivPt b ht q₀) v).trans ((a₀.ivPt b ht q₀).transferT_self_apply v))
  exact h1.trans h2

/-- The map `Ŷ'_{(t,x)} → Ŷ_{(t,a)}` of `L` between the product chart points is the identity
of `K_z` when on the fibre over `(t, a)` the bundle map of `L` is that of `L₀`. -/
theorem coe_mmorK_ivPt (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (A : ChartPoint (ivBundle B') (t, x)) (hA : A.c.φ.source ⊆ U') (hz : (t, a) ∈ U)
    (hϕ : L.ϕ (t, a) = (t, x)) (a₀ : ChartPoint B' x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (k : ↥(a₀.ivPt b ht q₀).K) :
    (Subtype.val (L.mmorK (a₀.ivPt b ht q₀) ((L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀') A hA hz
      hϕ k) : a₀.c.F 0) = Subtype.val k := by
  rw [mmorK_apply]
  have h1 := fiberMap_mpullPt_ivPt hL A hA hz hϕ a₀ ha₀ ha hϕ₀ b ht q₀ q₀'
    (Subtype.val ((a₀.ivPt b ht q₀).transferK A k))
  have h2 := congrArg Subtype.val (((a₀.ivPt b ht q₀).transferK_trans_apply A
    (a₀.ivPt b ht q₀) k).trans ((a₀.ivPt b ht q₀).transferK_self_apply k))
  exact h1.trans h2

/-- **The orientation map of `L = id × L₀` carries `e ∧ o` to `e ∧ (L₀)_* o`, in the product
chart points over a chart point `a₀` inside the target of `L₀` and its carried chart point.** -/
theorem morVia_ivPt_ivOrFirst₀ (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hfc' : (ivBundle B').IsScFredholmSection (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (A : ChartPoint (ivBundle B') (t, x)) (hA : A.c.φ.source ⊆ U') (hz : (t, a) ∈ U)
    (hϕ : L.ϕ (t, a) = (t, x))
    (hlin : (L.mpullPt A hA hz hϕ).linSet (cubeLift (n := 1) f hf.isScSmooth.1) =
      A.linSet (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (a₀ : ChartPoint B' x) (ha₀ : a₀.c.φ.source ⊆ U₀') (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x)
    (hlin₀ : (L₀.mpullPt a₀ ha₀ ha hϕ₀).linSet f = a₀.linSet f')
    (hxs : x ∈ PX'.smoothSet) (has : a ∈ PX.smoothSet) (b : Fin 1 → Bool)
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne : (a₀.linSet f').Nonempty) (hne' : ((L₀.mpullPt a₀ ha₀ ha hϕ₀).linSet f).Nonempty)
    (o : a₀.Or f' hf') :
    L.morVia hfc hfc' (a₀.ivPt b ht q₀) ((L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀') A hA hz hϕ
        hlin (prod_cube_mem_smoothSet_iff.2 hxs) (prod_cube_mem_smoothSet_iff.2 has)
        (a₀.ivOrFirst₀ b ht q₀ hf' hfc' hxs hne o) =
      (L₀.mpullPt a₀ ha₀ ha hϕ₀).ivOrFirst₀ b ht q₀' hf hfc has hne'
        (L₀.morPull hf hf' a₀ ha₀ ha hϕ₀ hlin₀ o) := by
  rw [morVia_apply]
  refine ChartPoint.ivOrFirst₀_conj₂ a₀ (L₀.mpullPt a₀ ha₀ ha hϕ₀) b ht b ht q₀ q₀' hf' hf hfc'
    hfc hxs has hne hne' (L₀.mcastT a₀ ha₀ ha hϕ₀) (L₀.mcastK a₀ ha₀ ha hϕ₀) _ _ (fun v => ?_)
    (fun k => ?_) (mcastT_mem hlin₀) _ o
  · have h := coe_mmorT_ivPt hL A hA hz hϕ a₀ ha₀ ha hϕ₀ b ht q₀ q₀' v
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact congrArg Prod.snd h
    · exact congrArg (fun y : (Fin 1 → ℝ) × a₀.c.φ.model.E 0 => ivSign b • y.1) h
  · exact Subtype.ext (coe_mmorK_ivPt hL A hA hz hϕ a₀ ha₀ ha hϕ₀ b ht q₀ q₀' k)

/-- **The orientation map of `L = id × L₀` carries `e ∧ o` to `e ∧ (L₀)_* o`**, in chart
points: for chart points `p'` of `Y'` at `x`, `p` of `Y` at `a` and any chart points `q'` at
`(t, x)`, `q` at `(t, a)`, the orientation map of `L` carries `e ∧ o`, made over `p'` and read
in `q'`, to `e ∧ (L₀)_* o`, made over `p` and read in `q`. -/
theorem morVia_ivOrFirst₀ (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hfc' : (ivBundle B').IsScFredholmSection (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (q' : ChartPoint (ivBundle B') (t, x)) (q : ChartPoint (ivBundle B) (t, a))
    (A : ChartPoint (ivBundle B') (t, x)) (hA : A.c.φ.source ⊆ U') (hz : (t, a) ∈ U)
    (hϕ : L.ϕ (t, a) = (t, x))
    (hlin : (L.mpullPt A hA hz hϕ).linSet (cubeLift (n := 1) f hf.isScSmooth.1) =
      A.linSet (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (p' : ChartPoint B' x) (p : ChartPoint B a)
    (a₀ : ChartPoint B' x) (ha₀ : a₀.c.φ.source ⊆ U₀') (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x)
    (hlin₀ : (L₀.mpullPt a₀ ha₀ ha hϕ₀).linSet f = a₀.linSet f')
    (hxs : x ∈ PX'.smoothSet) (has : a ∈ PX.smoothSet) (b : Fin 1 → Bool)
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne' : (p'.linSet f').Nonempty) (hne : (p.linSet f).Nonempty) (o : p'.Or f' hf') :
    L.morVia hfc hfc' q' q A hA hz hϕ hlin (prod_cube_mem_smoothSet_iff.2 hxs)
        (prod_cube_mem_smoothSet_iff.2 has)
        ((p'.ivPt b ht q₀).orTransfer q' hfc' (prod_cube_mem_smoothSet_iff.2 hxs)
          (p'.ivOrFirst₀ b ht q₀ hf' hfc' hxs hne' o)) =
      (p.ivPt b ht q₀').orTransfer q hfc (prod_cube_mem_smoothSet_iff.2 has)
        (p.ivOrFirst₀ b ht q₀' hf hfc has hne
          (L₀.morVia hf hf' p' p a₀ ha₀ ha hϕ₀ hlin₀ hxs has o)) := by
  have hzs : ((t, x) : (Fin 1 → unitInterval) × X') ∈ ((cubePolyfold 1).prod PX').smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  have hzas : ((t, a) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 has
  have hneA : (a₀.linSet f').Nonempty := p'.nonempty_linSet_transfer a₀ hf' hxs hne'
  have hneA' : ((L₀.mpullPt a₀ ha₀ ha hϕ₀).linSet f).Nonempty := by
    rw [hlin₀]; exact hneA
  set Q := a₀.ivPt b ht q₀ with hQ
  set Q' := (L₀.mpullPt a₀ ha₀ ha hϕ₀).ivPt b ht q₀' with hQ'
  set a' := L.mpullPt A hA hz hϕ with ha'
  have core := morVia_ivPt_ivOrFirst₀ hL hf hf' hfc hfc' A hA hz hϕ hlin a₀ ha₀ ha hϕ₀ hlin₀ hxs
    has b ht q₀ q₀' hneA hneA' (p'.orTransfer a₀ hf' hxs o)
  -- the left-hand side through `Q` and `Q'`
  have eL1 : q'.orTransfer A hfc' hzs ((p'.ivPt b ht q₀).orTransfer q' hfc' hzs
      (p'.ivOrFirst₀ b ht q₀ hf' hfc' hxs hne' o)) =
      Q.orTransfer A hfc' hzs
        (a₀.ivOrFirst₀ b ht q₀ hf' hfc' hxs hneA (p'.orTransfer a₀ hf' hxs o)) := by
    rw [← p'.orTransfer_ivPt_ivOrFirst₀ a₀ b ht b ht q₀ q₀ hf' hfc' hxs hne' hneA o]
    exact (DFunLike.congr_fun ((p'.ivPt b ht q₀).orTransfer_trans q' A hfc' hzs) _).trans
      (DFunLike.congr_fun ((p'.ivPt b ht q₀).orTransfer_trans Q A hfc' hzs) _).symm
  have eL2 : ∀ W : a'.Or (cubeLift (n := 1) f hf.isScSmooth.1) hfc,
      a'.orTransfer q hfc hzas W = Q'.orTransfer q hfc hzas (a'.orTransfer Q' hfc hzas W) :=
    fun W => (DFunLike.congr_fun (a'.orTransfer_trans Q' q hfc hzas) W).symm
  have eR : p.ivOrFirst₀ b ht q₀' hf hfc has hne
      (L₀.morVia hf hf' p' p a₀ ha₀ ha hϕ₀ hlin₀ hxs has o) =
      Q'.orTransfer (p.ivPt b ht q₀') hfc hzas ((L₀.mpullPt a₀ ha₀ ha hϕ₀).ivOrFirst₀ b ht q₀' hf
        hfc has hneA' (L₀.morPull hf hf' a₀ ha₀ ha hϕ₀ hlin₀ (p'.orTransfer a₀ hf' hxs o))) :=
    ((L₀.mpullPt a₀ ha₀ ha hϕ₀).orTransfer_ivPt_ivOrFirst₀ p b ht b ht q₀' q₀' hf hfc has
      hneA' hne _).symm
  rw [eR]
  refine Eq.trans ?_ (DFunLike.congr_fun (Q'.orTransfer_trans (p.ivPt b ht q₀') q hfc hzas)
    _).symm
  change a'.orTransfer q hfc hzas (L.morPull hfc hfc' A hA hz hϕ hlin
    (q'.orTransfer A hfc' hzs _)) = _
  rw [eL1, eL2]
  exact congrArg (Q'.orTransfer q hfc hzas) core

end StrongBundle.LocalIso

end Germ

/-! ### The family `(t, x) ↦ e ∧ o_x` -/

section Family

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [∀ k : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X))]
  [∀ k : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P
    (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X) → (Fin 1 → unitInterval) × X))]
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × X' → X'))]
  {f' : X' → Y'}
  [ParacompactSpace ((Fin 1 → unitInterval) × X')]
  [ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X'))]
  [∀ k : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X'))]
  [∀ k : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P'
    (Prod.snd : (Fin 1 → unitInterval) × X' → X'))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X') → (Fin 1 → unitInterval) × X'))]

/-- `(t, x) ↦ e ∧ o_x` as the transfer of `e ∧ o_x` made in the product chart point over the
chosen chart point of `X` at `x` and the corner chart of `[0, 1]` at `t`. -/
theorem ivFirstFun_eq_orTransfer (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (t : Fin 1 → unitInterval) {x : X} (hxs : x ∈ PX.smoothSet)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne : ((orxPt B x hxs).linSet f).Nonempty) :
    ivFirstFun hf hfc hsec o (t, x) (prod_cube_mem_smoothSet_iff.2 hxs) =
      ((orxPt B x hxs).ivPt (corner t) (mem_chart_corner t) q₀).orTransfer
        (orxPt (ivBundle B) (t, x) (prod_cube_mem_smoothSet_iff.2 hxs)) hfc
        (prod_cube_mem_smoothSet_iff.2 hxs)
        ((orxPt B x hxs).ivOrFirst₀ (corner t) (mem_chart_corner t) q₀ hf hfc hxs hne
          (o x hxs)) := by
  have hzs : ((t, x) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  set p := orxPt B x hxs with hp
  set q := orxPt (ivBundle B) (t, x) hzs with hq
  have e1 := ivFirstFun_orTransfer hf hfc hsec o t hxs p (corner t) (mem_chart_corner t) q₀ hne
  rw [p.orTransfer_self hf hxs] at e1
  exact ((DFunLike.congr_fun (q.orTransfer_trans (p.ivPt (corner t) (mem_chart_corner t) q₀) q
    hfc hzs) _).trans (DFunLike.congr_fun (q.orTransfer_self hfc hzs) _)).symm.trans
    (congrArg ((p.ivPt (corner t) (mem_chart_corner t) q₀).orTransfer q hfc hzs) e1)

namespace StrongBundle.LocalIso

variable {U : Set ((Fin 1 → unitInterval) × X)} {U' : Set ((Fin 1 → unitInterval) × X')}
  {U₀ : Set X} {U₀' : Set X'}
  {L : LocalIso (ivBundle B) (ivBundle B') U U'} {L₀ : LocalIso B B' U₀ U₀'}
  {x : X'} {a : X} {t : Fin 1 → unitInterval}

/-- **The orientation map of `L = id × L₀` carries `(e ∧ o')_{(t, x)}` to `(e ∧ o)_{(t, a)}`**
for families `o'` of orientations of `f'` and `o` of `f` with `(L₀)_* o'_x = o_a`
(2021 Remark 6.6.19 with Lemma 12.5.1). -/
theorem orxViaAt_ivFirstFun (hL : IsIntervalProductAt₂ L L₀ (t, a))
    (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hfc' : (ivBundle B').IsScFredholmSection (cubeLift (n := 1) f' hf'.isScSmooth.1))
    (hfL : EqOn (cubeLift (n := 1) f hf.isScSmooth.1)
      (L.Ψ ∘ cubeLift (n := 1) f' hf'.isScSmooth.1 ∘ L.ϕ) U)
    (hfL₀ : EqOn f (L₀.Ψ ∘ f' ∘ L₀.ϕ) U₀)
    (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
    (hsecc : (ivBundle B).HasScPlusSectionsThrough)
    (hsecc' : (ivBundle B').HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (o' : ∀ y (hy : y ∈ PX'.smoothSet), Orx f' hf' y hy)
    (hz : (t, a) ∈ U) (hϕ : L.ϕ (t, a) = (t, x)) (ha : a ∈ U₀) (hϕ₀ : L₀.ϕ a = x)
    (has : a ∈ PX.smoothSet) (hxs : x ∈ PX'.smoothSet)
    (hinv : L₀.orxViaAt hf hf' hfL₀ hsec hsec' ha has hϕ₀ (o' x hxs) = o a has) :
    L.orxViaAt hfc hfc' hfL hsecc hsecc' hz (prod_cube_mem_smoothSet_iff.2 has) hϕ
        (ivFirstFun hf' hfc' hsec' o' (t, x) (prod_cube_mem_smoothSet_iff.2 hxs)) =
      ivFirstFun hf hfc hsec o (t, a) (prod_cube_mem_smoothSet_iff.2 has) := by
  have hzs : ((t, x) : (Fin 1 → unitInterval) × X') ∈ ((cubePolyfold 1).prod PX').smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  have hzas : ((t, a) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 has
  have hne' := (orxPt B' x hxs).linSet_nonempty hf' hxs hsec'
  have hne := (orxPt B a has).linSet_nonempty hf has hsec
  have q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → unitInterval) × X' → X') :=
    cubeLift (n := 1) f' hf'.isScSmooth.1 (t, x)
  have q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) :=
    cubeLift (n := 1) f hf.isScSmooth.1 (t, a)
  have hA := L.innerPt_sub (t, x) (L.mem_of_ϕ_eq hz hϕ) hzs
  have ha₀ := L₀.innerPt_sub x (L₀.mem_of_ϕ_eq ha hϕ₀) hxs
  have hlin := linSet_mpullPt (p := L.innerPt (t, x) (L.mem_of_ϕ_eq hz hϕ) hzs) (hsub := hA)
    (ha := hz) (hϕ := hϕ) hfc hfc' hfL hsecc hsecc' hzas hzs
  have hlin₀ := linSet_mpullPt (p := L₀.innerPt x (L₀.mem_of_ϕ_eq ha hϕ₀) hxs) (hsub := ha₀)
    (ha := ha) (hϕ := hϕ₀) hf hf' hfL₀ hsec hsec' has hxs
  have key := morVia_ivOrFirst₀ hL hf hf' hfc hfc' (orxPt (ivBundle B') (t, x) hzs)
    (orxPt (ivBundle B) (t, a) hzas) _ hA hz hϕ hlin (orxPt B' x hxs) (orxPt B a has) _ ha₀ ha
    hϕ₀ hlin₀ hxs has (corner t) (mem_chart_corner t) q₀ q₀' hne' hne (o' x hxs)
  rw [ivFirstFun_eq_orTransfer hf' hfc' hsec' o' t hxs q₀ hne',
    ivFirstFun_eq_orTransfer hf hfc hsec o t has q₀' hne, ← hinv]
  exact key

end StrongBundle.LocalIso

end Family

end Polyfold
