import Polyfold.Chapter12.OrientationBundleEp
import Polyfold.Chapter6.IntervalProductSectionOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §12.5, pp. 592–594
(Lemma 12.5.1, Definition 12.5.4), and §6.6, p. 276 (Remark 6.6.19).

# The orientation `e ∧ o` over `[0, 1] × X` and local strong bundle isomorphisms

## The text, paraphrased

A morphism `φ : x → x'` of an ep-groupoid acts on the orientations of `DET(f, x)` by
`φ_* S = μ(φ, S ∘ (Tφ)⁻¹)` (p. 593), and an orientation of `f` is a continuous family `o` with
`φ_* o_x = o_{x'}` (Definition 12.5.4).  Over `[0, 1] × X` the section `f̃(t, x) = f(x)` is
oriented by the standard orientation of `[0, 1]` and `o` (Remark 6.6.19; p. 703).

## What is formalized

`[0, 1] × X` is `(cubePolyfold 1).prod PX` with the bundle `ivBundle B`, as in Part I.

* `ChartPoint.ivOrFirst₀_conj`: for chart points `p` at `x` and `p'` at `x'` and linear
  isomorphisms `A : T_xX → T_{x'}X`, `Γ : Y_x → Y_{x'}`, `Â`, `Γ̂` between the product chart
  points with `Â = A × 1` and `Γ̂ = Γ` in the product coordinates, the conjugate of `e ∧ o` by
  `(Â, Γ̂)` is `e ∧` (the conjugate of `o` by `(A, Γ)`).
* `StrongBundle.LocalIso.IsIntervalProductAt`: a local strong bundle isomorphism `L` of the
  pull-back bundle over `[0, 1] × X` is, near `(t, x')`, the product `id × L₀` of the identity of
  `[0, 1]` with a local strong bundle isomorphism `L₀` of `Y → X`.
* `baseDeriv_pullPt_ivPt`, `fiberMap_pullPt_ivPt`: for such `L`, the identifications from a
  chart point carried by `L` to the product chart point over a chart point carried by `L₀` are
  those from the original chart point to the original product chart point.
* **`orVia_ivOrFirst₀`**: the orientation map of `L` carries `e ∧ o` to `e ∧ (L₀)_* o`.
* `ivFirstFun_orTransfer`: the family `(t, x) ↦ e ∧ o_x` read in the product chart point over
  any chart point of `X`.
* **`orVia_ivFirstFun`**: for a family `o` with `(L₀)_* o_x = o_{x'}`, the orientation map of `L`
  carries `(e ∧ o)_{(t, x)}` to `(e ∧ o)_{(t, x')}`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-! ### Conjugating `e ∧ o` -/

section Conj

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x x' : X} (p : ChartPoint B x) (p' : ChartPoint B x') (b : Fin 1 → Bool)
  {t : Fin 1 → unitInterval} (ht : t ∈ (chart b).source) (b' : Fin 1 → Bool)
  {t' : Fin 1 → unitInterval} (ht' : t' ∈ (chart b').source)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

set_option maxHeartbeats 1600000 in
-- the determinant lines over the two product chart points are compared term by term
private theorem ivOrFirst₀_conj_aux (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hx : x ∈ PX.smoothSet) (hx' : x' ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f).Nonempty)
    (A : ↥p.T ≃L[ℝ] ↥p'.T) (Γ : ↥p.K ≃L[ℝ] ↥p'.K)
    (Ah : ↥(p.ivPt b ht q₀).T ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').T)
    (Γh : ↥(p.ivPt b ht q₀).K ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').K)
    (hA : ∀ v, p'.ivT b' ht' q₀' (Ah v) =
      (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (p.ivT b ht q₀ v))
    (hΓ : ∀ k, p'.ivK b' ht' q₀' (Γh k) = Γ (p.ivK b ht q₀ k))
    (hmem : ∀ S' ∈ p'.linSet f, ((Γ.symm : ↥p'.K →L[ℝ] ↥p.K) ∘L S' ∘L
      (A : ↥p.T →L[ℝ] ↥p'.T)) ∈ p.linSet f)
    (hmemh : ∀ S' ∈ (p'.ivPt b' ht' q₀').linSet (cubeLift (n := 1) f hf.isScSmooth.1),
      ((Γh.symm : ↥(p'.ivPt b' ht' q₀').K →L[ℝ] ↥(p.ivPt b ht q₀).K) ∘L S' ∘L
        (Ah : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p'.ivPt b' ht' q₀').T)) ∈
          (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (o : p.Or f hf) {L' : ↥p'.T →L[ℝ] ↥p'.K} (hL' : L' ∈ p'.linSet f)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) (h : ∀ v, L' (A v) = Γ (L v)) :
    (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o).conj
        (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc) Ah Γh hmemh =
      p'.ivOrFirst₀ b' ht' q₀' hf hfc hx' hne'
        (o.conj (hC' := p'.isFredholm_of_mem_linSet hf) A Γ hmem) := by
  have hLh := p.ivLin_mem_linSet_cubeLift b ht q₀ hf hx hL
  have hLh' := p'.ivLin_mem_linSet_cubeLift b' ht' q₀' hf hx' hL'
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
  have : PreconnectedSpace ((p'.ivPt b' ht' q₀').linSet (cubeLift (n := 1) f hf.isScSmooth.1)) :=
    isPreconnected_iff_preconnectedSpace.1 ((p'.ivPt b' ht' q₀').convex_linSet hfc).isPreconnected
  have eL := LineOrientation.conj_apply
    (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc) Ah Γh hmemh
    (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o) hLh hLh' hconj
  have eL2 := p.ivOrFirst₀_apply b ht q₀ hf hfc hx hne o L hL
  have eR := p'.ivOrFirst₀_apply b' ht' q₀' hf hfc hx' hne'
    (o.conj (hC' := p'.isFredholm_of_mem_linSet hf) A Γ hmem) L' hL'
  have eR2 := LineOrientation.conj_apply (hC' := p'.isFredholm_of_mem_linSet hf) A Γ hmem o hL
    hL' h
  have hequiv : (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
      (p.isFredholm_of_mem_linSet hf _ hL)
        ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hLh)) ≪≫ₗ conjDet Ah Γh hconj =
      conjDet A Γ h ≪≫ₗ extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀')
        (p'.isFredholm_of_mem_linSet hf _ hL')
          ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc _ hLh') :=
    LinearEquiv.ext fun y => conjDet_extConjDetFirst_of_conj (p.ivT b ht q₀) (p.ivK b ht q₀)
      (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀') A Γ Ah Γh hA hΓ (L := L) (L' := L') h hconj
      (p.isFredholm_of_mem_linSet hf _ hL) (p'.isFredholm_of_mem_linSet hf _ hL')
      ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hLh)
      ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc _ hLh') y
  have m1 := ray_map_map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
    (p.isFredholm_of_mem_linSet hf _ hL) ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hLh))
    (conjDet Ah Γh hconj) (o ⟨L, hL⟩)
  have m2 := ray_map_map (conjDet A Γ h)
    (extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀') (p'.isFredholm_of_mem_linSet hf _ hL')
      ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc _ hLh')) (o ⟨L, hL⟩)
  have m3 := congrArg (fun e => Module.Ray.map e (o ⟨L, hL⟩)) hequiv
  refine LineOrientation.eq_of_apply_eq ⟨_, hLh'⟩ ?_
  refine (eL.trans (congrArg (Module.Ray.map (conjDet Ah Γh hconj)) eL2)).trans ?_
  refine Eq.trans ?_ (eR.trans (congrArg (Module.Ray.map (extConjDetFirst (p'.ivT b' ht' q₀')
    (p'.ivK b' ht' q₀') (p'.isFredholm_of_mem_linSet hf _ hL')
    ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc _ hLh'))) eR2)).symm
  exact m1.trans (m3.trans m2.symm)

/-- **The conjugate of `e ∧ o` is `e ∧` (the conjugate of `o`)**: let `p`, `p'` be chart points
at smooth points `x`, `x'`, and `A : T_xX ≅ T_{x'}X`, `Γ : Y_x ≅ Y_{x'}` carry `Lin(f, x')` into
`Lin(f, x)`.  If `Â`, `Γ̂` between the product chart points at `(t, x)`, `(t', x')` are
`A × 1` and `Γ` in the product coordinates (`ivT`, `ivK`), then the conjugate by `(Â, Γ̂)` of the
orientation `e ∧ o` of `f̃` at `(t, x)` is `e ∧ (o conjugated by (A, Γ))` at `(t', x')`. -/
theorem ivOrFirst₀_conj (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hx : x ∈ PX.smoothSet) (hx' : x' ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f).Nonempty)
    (A : ↥p.T ≃L[ℝ] ↥p'.T) (Γ : ↥p.K ≃L[ℝ] ↥p'.K)
    (Ah : ↥(p.ivPt b ht q₀).T ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').T)
    (Γh : ↥(p.ivPt b ht q₀).K ≃L[ℝ] ↥(p'.ivPt b' ht' q₀').K)
    (hA : ∀ v, p'.ivT b' ht' q₀' (Ah v) =
      (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (p.ivT b ht q₀ v))
    (hΓ : ∀ k, p'.ivK b' ht' q₀' (Γh k) = Γ (p.ivK b ht q₀ k))
    (hmem : ∀ S' ∈ p'.linSet f, ((Γ.symm : ↥p'.K →L[ℝ] ↥p.K) ∘L S' ∘L
      (A : ↥p.T →L[ℝ] ↥p'.T)) ∈ p.linSet f)
    (hmemh : ∀ S' ∈ (p'.ivPt b' ht' q₀').linSet (cubeLift (n := 1) f hf.isScSmooth.1),
      ((Γh.symm : ↥(p'.ivPt b' ht' q₀').K →L[ℝ] ↥(p.ivPt b ht q₀).K) ∘L S' ∘L
        (Ah : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p'.ivPt b' ht' q₀').T)) ∈
          (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (o : p.Or f hf) :
    (p.ivOrFirst₀ b ht q₀ hf hfc hx hne o).conj
        (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hfc) Ah Γh hmemh =
      p'.ivOrFirst₀ b' ht' q₀' hf hfc hx' hne'
        (o.conj (hC' := p'.isFredholm_of_mem_linSet hf) A Γ hmem) :=
  p.ivOrFirst₀_conj_aux p' b ht b' ht' q₀ q₀' hf hfc hx hx' hne hne' A Γ Ah Γh hA hΓ hmem hmemh o
    hne'.some_mem (hmem _ hne'.some_mem)
    (fun v => (Γ.apply_symm_apply (hne'.some (A v))).symm)

end ChartPoint

end Conj

/-! ### Local isomorphisms of the pull-back bundle that are products near a point -/

section Germ

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace StrongBundle.LocalIso

variable {U U' : Set ((Fin 1 → unitInterval) × X)} {U₀ U₀' : Set X}

/-- **A local strong bundle isomorphism of the pull-back bundle over `[0, 1] × X` that is the
product `id × L₀` near `z'`**: on an open `N ∋ z'` the base map is `(s, y) ↦ (s, ϕ₀(y))`, and on
the fibre over `z'` the bundle map is that of `L₀`. -/
structure IsIntervalProductAt (L : LocalIso (ivBundle B) (ivBundle B) U U')
    (L₀ : LocalIso B B U₀ U₀') (z' : (Fin 1 → unitInterval) × X) : Prop where
  exists_nhds : ∃ N : Set ((Fin 1 → unitInterval) × X), IsOpen N ∧ z' ∈ N ∧ N ⊆ U ∧
    (∀ y ∈ N, y.2 ∈ U₀) ∧ ∀ y ∈ N, L.ϕ y = (y.1, L₀.ϕ y.2)
  fiber : ∀ w : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X),
    pullbackProj P Prod.snd w = z' → (L.Φ w).1.2 = L₀.Φ w.1.2

variable {L : LocalIso (ivBundle B) (ivBundle B) U U'} {L₀ : LocalIso B B U₀ U₀'}
  {x x' : X} {t : Fin 1 → unitInterval}

/-- **The base derivative from a chart point carried by `L` to the product chart point over a
chart point carried by `L₀`** is the one from the original chart point to the original product
chart point, when `L` is `id × L₀` near `(t, x')`: the transition
`(χ × φ₀ ∘ ϕ₀) ∘ ϕ⁻¹ ∘ φ_a⁻¹` is `(χ × φ₀) ∘ φ_a⁻¹` near the point. -/
theorem baseDeriv_pullPt_ivPt (hL : IsIntervalProductAt L L₀ (t, x'))
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x)) (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (v : a.c.φ.model.E 0) :
    (L.pullPt a ha hz' hϕ).baseDeriv ((L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀') v =
      a.baseDeriv (a₀.ivPt b ht q₀) v := by
  obtain ⟨N, hNo, hzN, hNU, hNU₀, hNϕ⟩ := hL.exists_nhds
  set a' := L.pullPt a ha hz' hϕ with ha'
  set Q := a₀.ivPt b ht q₀ with hQ
  set Q' := (L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀' with hQ'
  obtain ⟨G, hGo, hG⟩ := a'.c.φ.exists_isOpen_image_eq (s := N ∩ a'.c.φ.source)
    inter_subset_right (hNo.inter a'.c.φ.isOpen_source)
  set R' := ((a.baseRet Q).restrict (a'.isOpen_overlapW Q')).restrict hGo with hR'
  have hV₁ : R'.U ⊆ (a.baseRet Q).U := fun u hu => hu.1.1
  have hV₃ : R'.U ⊆ (a'.baseRet Q').U := fun u hu => ⟨(a.baseRet_U_subset Q) hu.1.1, hu.1.2⟩
  have hzG : r a.c.R (a.c.φ.model.E.toBase 1 a.z) ∈ G := by
    rw [a.r_toBase_z]
    have : a'.c.φ (t, x') ∈ a'.c.φ '' (N ∩ a'.c.φ.source) := ⟨(t, x'), ⟨hzN, a'.mem_source⟩, rfl⟩
    rw [hG] at this
    have h' : a'.c.φ (t, x') = a.c.φ.model.E.toBase 1 a.z := a'.toBase_z.symm
    rw [h'] at this
    exact this.2
  have hzV : a.z ∈ a.c.φ.model.E.lvlSet R'.U 1 :=
    ⟨⟨a.z_mem_baseRet Q, (a'.z_mem_baseRet Q').2⟩, hzG⟩
  have hOO : a'.c.φ.model.O = a.c.φ.model.O := L.transportChart_model_O a.c ha
  have heq : EqOn (a'.c.φ.transition Q'.c.φ ∘ a'.baseRet Q')
      (a.c.φ.transition Q.c.φ ∘ a.baseRet Q) R'.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a'.exists_eq_of_mem_baseRet Q' (hV₃ hu)
    have hrG : r a.c.R u ∈ a'.c.φ.model.O ∩ G :=
      ⟨hOO ▸ a.c.r_mem_O ((a.baseRet_U_subset Q) hu.1.1), hu.2⟩
    rw [← hG] at hrG
    obtain ⟨y₂, ⟨hy₂N, hy₂s⟩, hy₂u⟩ := hrG
    have hyy : y₂ = y := by
      have e : a'.c.φ y₂ = a'.c.φ y := hy₂u.trans hyu
      rw [← a'.c.φ.symm_apply_apply hy₂s, ← a'.c.φ.symm_apply_apply hy, e]
    subst hyy
    have hyu' : r a.c.R u = a.c.φ (L.ϕ y₂) := hyu
    change Q'.c.φ (L.g (a.c.φ.symm (r a.c.R u))) = Q.c.φ (a.c.φ.symm (r a.c.R u))
    rw [hyu', a.c.φ.symm_apply_apply hy.2, L.base.left_inv y₂ hy.1, hNϕ y₂ hy₂N]
    rfl
  exact congrArg (fun T : a.c.φ.model.E 0 →L[ℝ] Q.c.φ.model.E 0 => T v)
    (scDeriv_eq_of_eqOn_relOpen R'.relOpen (a'.isSc1_transition Q') (a.isSc1_transition Q) hV₃ hV₁
      heq hzV)

/-- **The fibre transition from a chart point carried by `L` to the product chart point over a
chart point carried by `L₀`** is the one from the original chart point to the original product
chart point, when on the fibre over `(t, x')` the bundle map of `L` is that of `L₀`. -/
theorem fiberMap_pullPt_ivPt (hL : IsIntervalProductAt L L₀ (t, x'))
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x)) (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) (k : a.c.F 0) :
    (L.pullPt a ha hz' hϕ).fiberMap ((L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀') k =
      a.fiberMap (a₀.ivPt b ht q₀) k := by
  set w : a.c.φ.model.E 0 × a.c.F 0 :=
    (a.c.φ.model.E.toBase 1 a.z, ρ a.c.R (a.c.φ.model.E.toBase 1 a.z) k) with hw
  have hwK : w ∈ a.c.toPartialEquiv.target := by
    rw [a.c.target_eq]; exact a.c.mem_K_ρ a.toBase_z_mem_O k
  have hsrc := a.c.toPartialEquiv.map_target hwK
  set y := a.c.toPartialEquiv.symm w with hy
  have hPy : pullbackProj P Prod.snd y = (t, x) := by
    have h1 := a.c.covers _ hsrc
    rw [a.c.toPartialEquiv.right_inv hwK] at h1
    have h2 : a.c.φ.model.E.toBase 1 a.z = a.c.φ (pullbackProj P Prod.snd y) := h1
    rw [a.c.source_eq] at hsrc
    rw [a.toBase_z] at h2
    rw [← a.c.φ.symm_apply_apply hsrc, ← h2, a.c.φ.symm_apply_apply a.mem_source]
  have hU' : pullbackProj P Prod.snd y ∈ U' := by rw [hPy]; exact ha a.mem_source
  have hPΨ : pullbackProj P Prod.snd (L.Ψ y) = (t, x') := by
    rw [L.covers_inv _ hU', hPy, ← hϕ, L.base.left_inv _ hz']
  have hfib := hL.fiber (L.Ψ y) hPΨ
  rw [L.zero.right_inv _ hU'] at hfib
  change (a₀.c (L₀.Φ (L.Ψ y).1.2)).2 = (a₀.c y.1.2).2
  rw [← hfib]

/-- The map `T_{(t,x)} → T_{(t,x')}` of `L` between the product chart points is the identity of
`ℝ × T_zO` when `L` is `id × L₀` near `(t, x')`. -/
theorem coe_morT_ivPt (hL : IsIntervalProductAt L L₀ (t, x'))
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x)) (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (v : ↥(a₀.ivPt b ht q₀).T) :
    (Subtype.val (L.morT (a₀.ivPt b ht q₀) ((L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀') a ha hz' hϕ
      v) : (Fin 1 → ℝ) × a₀.c.φ.model.E 0) = Subtype.val v := by
  rw [morT_apply]
  have h1 := baseDeriv_pullPt_ivPt hL a ha hz' hϕ a₀ ha₀ hx' hϕ₀ b ht q₀ q₀'
    (Subtype.val ((a₀.ivPt b ht q₀).transferT a v))
  have h2 := congrArg Subtype.val (((a₀.ivPt b ht q₀).transferT_trans_apply a
    (a₀.ivPt b ht q₀) v).trans ((a₀.ivPt b ht q₀).transferT_self_apply v))
  exact h1.trans h2

/-- The map `Ŷ_{(t,x)} → Ŷ_{(t,x')}` of `L` between the product chart points is the identity
of `K_z` when on the fibre over `(t, x')` the bundle map of `L` is that of `L₀`. -/
theorem coe_morK_ivPt (hL : IsIntervalProductAt L L₀ (t, x'))
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x)) (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀')
    (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x) (b : Fin 1 → Bool) (ht : t ∈ (chart b).source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (k : ↥(a₀.ivPt b ht q₀).K) :
    (Subtype.val (L.morK (a₀.ivPt b ht q₀) ((L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀') a ha hz' hϕ
      k) : a₀.c.F 0) = Subtype.val k := by
  rw [morK_apply]
  have h1 := fiberMap_pullPt_ivPt hL a ha hz' hϕ a₀ ha₀ hx' hϕ₀ b ht q₀ q₀'
    (Subtype.val ((a₀.ivPt b ht q₀).transferK a k))
  have h2 := congrArg Subtype.val (((a₀.ivPt b ht q₀).transferK_trans_apply a
    (a₀.ivPt b ht q₀) k).trans ((a₀.ivPt b ht q₀).transferK_self_apply k))
  exact h1.trans h2

/-- **The orientation map of `L = id × L₀` carries `e ∧ o` to `e ∧ (L₀)_* o`, in the product
chart points over a chart point `a₀` inside the target of `L₀` and its carried chart point.** -/
theorem orVia_ivPt_ivOrFirst₀ (hL : IsIntervalProductAt L L₀ (t, x'))
    (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x))
    (hlin : (L.pullPt a ha hz' hϕ).linSet (cubeLift (n := 1) f hf.isScSmooth.1) =
      a.linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀') (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x)
    (hlin₀ : (L₀.pullPt a₀ ha₀ hx' hϕ₀).linSet f = a₀.linSet f)
    (hxs : x ∈ PX.smoothSet) (hx's : x' ∈ PX.smoothSet) (b : Fin 1 → Bool)
    (ht : t ∈ (chart b).source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne : (a₀.linSet f).Nonempty) (hne' : ((L₀.pullPt a₀ ha₀ hx' hϕ₀).linSet f).Nonempty)
    (o : a₀.Or f hf) :
    L.orVia hfc (a₀.ivPt b ht q₀) ((L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀') a ha hz' hϕ hlin
        (prod_cube_mem_smoothSet_iff.2 hxs) (prod_cube_mem_smoothSet_iff.2 hx's)
        (a₀.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) =
      (L₀.pullPt a₀ ha₀ hx' hϕ₀).ivOrFirst₀ b ht q₀' hf hfc hx's hne'
        (L₀.orPull hf a₀ ha₀ hx' hϕ₀ hlin₀ o) := by
  rw [orVia_apply]
  refine ChartPoint.ivOrFirst₀_conj a₀ (L₀.pullPt a₀ ha₀ hx' hϕ₀) b ht b ht q₀ q₀' hf hfc hxs
    hx's hne hne' (L₀.castT a₀ ha₀ hx' hϕ₀) (L₀.castK a₀ ha₀ hx' hϕ₀) _ _ (fun v => ?_)
    (fun k => ?_) (castT_mem hlin₀) _ o
  · have h := coe_morT_ivPt hL a ha hz' hϕ a₀ ha₀ hx' hϕ₀ b ht q₀ q₀' v
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact congrArg Prod.snd h
    · exact congrArg (fun y : (Fin 1 → ℝ) × a₀.c.φ.model.E 0 => ivSign b • y.1) h
  · exact Subtype.ext (coe_morK_ivPt hL a ha hz' hϕ a₀ ha₀ hx' hϕ₀ b ht q₀ q₀' k)

/-- **The orientation map of `L = id × L₀` carries `e ∧ o` to `e ∧ (L₀)_* o`** (the second
clause of Definition 12.5.4 for `õ`, in chart points): for chart points `p` at `x`, `p'` at
`x'` and any chart points `q` at `(t, x)`, `q'` at `(t, x')`, the orientation map of `L` carries
`e ∧ o`, made over `p` and read in `q`, to `e ∧ (L₀)_* o`, made over `p'` and read in `q'`. -/
theorem orVia_ivOrFirst₀ (hL : IsIntervalProductAt L L₀ (t, x'))
    (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (q : ChartPoint (ivBundle B) (t, x)) (q' : ChartPoint (ivBundle B) (t, x'))
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x))
    (hlin : (L.pullPt a ha hz' hϕ).linSet (cubeLift (n := 1) f hf.isScSmooth.1) =
      a.linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (p : ChartPoint B x) (p' : ChartPoint B x')
    (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀') (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x)
    (hlin₀ : (L₀.pullPt a₀ ha₀ hx' hϕ₀).linSet f = a₀.linSet f)
    (hxs : x ∈ PX.smoothSet) (hx's : x' ∈ PX.smoothSet) (b : Fin 1 → Bool)
    (ht : t ∈ (chart b).source)
    (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne : (p.linSet f).Nonempty) (hne' : (p'.linSet f).Nonempty) (o : p.Or f hf) :
    L.orVia hfc q q' a ha hz' hϕ hlin (prod_cube_mem_smoothSet_iff.2 hxs)
        (prod_cube_mem_smoothSet_iff.2 hx's)
        ((p.ivPt b ht q₀).orTransfer q hfc (prod_cube_mem_smoothSet_iff.2 hxs)
          (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o)) =
      (p'.ivPt b ht q₀').orTransfer q' hfc (prod_cube_mem_smoothSet_iff.2 hx's)
        (p'.ivOrFirst₀ b ht q₀' hf hfc hx's hne'
          (L₀.orVia hf p p' a₀ ha₀ hx' hϕ₀ hlin₀ hxs hx's o)) := by
  have hzs : ((t, x) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  have hz's : ((t, x') : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hx's
  have hneA : (a₀.linSet f).Nonempty := p.nonempty_linSet_transfer a₀ hf hxs hne
  have hneA' : ((L₀.pullPt a₀ ha₀ hx' hϕ₀).linSet f).Nonempty := hlin₀ ▸ hneA
  set Q := a₀.ivPt b ht q₀ with hQ
  set Q' := (L₀.pullPt a₀ ha₀ hx' hϕ₀).ivPt b ht q₀' with hQ'
  set a' := L.pullPt a ha hz' hϕ with ha'
  have core := orVia_ivPt_ivOrFirst₀ hL hf hfc a ha hz' hϕ hlin a₀ ha₀ hx' hϕ₀ hlin₀ hxs hx's b
    ht q₀ q₀' hneA hneA' (p.orTransfer a₀ hf hxs o)
  -- the left-hand side through `Q` and `Q'`
  have eL1 : q.orTransfer a hfc hzs ((p.ivPt b ht q₀).orTransfer q hfc hzs
      (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o)) =
      Q.orTransfer a hfc hzs
        (a₀.ivOrFirst₀ b ht q₀ hf hfc hxs hneA (p.orTransfer a₀ hf hxs o)) := by
    rw [← p.orTransfer_ivPt_ivOrFirst₀ a₀ b ht b ht q₀ q₀ hf hfc hxs hne hneA o]
    exact (DFunLike.congr_fun ((p.ivPt b ht q₀).orTransfer_trans q a hfc hzs) _).trans
      (DFunLike.congr_fun ((p.ivPt b ht q₀).orTransfer_trans Q a hfc hzs) _).symm
  have eL2 : ∀ W : a'.Or (cubeLift (n := 1) f hf.isScSmooth.1) hfc,
      a'.orTransfer q' hfc hz's W = Q'.orTransfer q' hfc hz's (a'.orTransfer Q' hfc hz's W) :=
    fun W => (DFunLike.congr_fun (a'.orTransfer_trans Q' q' hfc hz's) W).symm
  have eR : p'.ivOrFirst₀ b ht q₀' hf hfc hx's hne'
      (L₀.orVia hf p p' a₀ ha₀ hx' hϕ₀ hlin₀ hxs hx's o) =
      Q'.orTransfer (p'.ivPt b ht q₀') hfc hz's ((L₀.pullPt a₀ ha₀ hx' hϕ₀).ivOrFirst₀ b ht q₀' hf
        hfc hx's hneA' (L₀.orPull hf a₀ ha₀ hx' hϕ₀ hlin₀ (p.orTransfer a₀ hf hxs o))) :=
    ((L₀.pullPt a₀ ha₀ hx' hϕ₀).orTransfer_ivPt_ivOrFirst₀ p' b ht b ht q₀' q₀' hf hfc hx's
      hneA' hne' _).symm
  rw [eR]
  refine Eq.trans ?_ (DFunLike.congr_fun (Q'.orTransfer_trans (p'.ivPt b ht q₀') q' hfc hz's)
    _).symm
  change a'.orTransfer q' hfc hz's (L.orPull hfc a ha hz' hϕ hlin (q.orTransfer a hfc hzs _)) = _
  rw [eL1, eL2]
  exact congrArg (Q'.orTransfer q' hfc hz's) core

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

/-- **`(t, x) ↦ e ∧ o_x` read in the product chart point over any chart point `p₀` of `X` at
`x`** and any chart `χ_b` of `[0, 1]` at `t`: it is `e ∧ (o_x read in p₀)`. -/
theorem ivFirstFun_orTransfer (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (t : Fin 1 → unitInterval) {x : X} (hxs : x ∈ PX.smoothSet) (p₀ : ChartPoint B x)
    (b : Fin 1 → Bool) (hb : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne : (p₀.linSet f).Nonempty) :
    (chartPtOf (orChart (ivBundle B) (t, x)) (isChart_orChart (t, x)) (mem_orChart (t, x))
        (prod_cube_mem_smoothSet_iff.2 hxs)).orTransfer (p₀.ivPt b hb q₀) hfc
        (prod_cube_mem_smoothSet_iff.2 hxs)
        (ivFirstFun hf hfc hsec o (t, x) (prod_cube_mem_smoothSet_iff.2 hxs)) =
      p₀.ivOrFirst₀ b hb q₀ hf hfc hxs hne
        ((chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs).orTransfer p₀ hf hxs
          (o x hxs)) := by
  have hz : ((t, x) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  have hne₀ := ChartPoint.linSet_nonempty (chartPtOf (orChart B x) (isChart_orChart x)
    (mem_orChart x) hxs) hf hxs hsec
  set C₂ := chartPtOf (B := ivBundle B) (ivChart (corner t) (orChart B x)
    (cubeLift (n := 1) f hf.isScSmooth.1 (t, x))) (isChart_ivChart _ (isChart_orChart x) _)
    (mem_ivChart_source _ (mem_orChart x) (mem_chart_corner t)) hz with hC₂
  have h3 := ChartPoint.orTransfer_trans
    (chartPtOf (orChart (ivBundle B) (t, x)) (isChart_orChart (t, x)) (mem_orChart (t, x)) hz)
    C₂ (p₀.ivPt b hb q₀) hfc hz
  have h2 := ivOrLift_orTransfer (corner t) b (isChart_orChart x) p₀.isChart (mem_orChart x)
    p₀.mem_source _ (exists_lift_of_smooth (orChart B x) (mem_orChart x) hxs).choose_spec
    p₀.z p₀.toBase_z (mem_chart_corner t) hb (cubeLift (n := 1) f hf.isScSmooth.1 (t, x)) q₀
    (mem_ivChart_source _ (mem_orChart x) (mem_chart_corner t)) _
    (exists_lift_of_smooth (ivChart (corner t) (orChart B x)
      (cubeLift (n := 1) f hf.isScSmooth.1 (t, x)))
      (mem_ivChart_source _ (mem_orChart x) (mem_chart_corner t)) hz).choose_spec
    (ivChart_lift_eq (corner t) _
      (exists_lift_of_smooth (orChart B x) (mem_orChart x) hxs).choose_spec t _ _
      (exists_lift_of_smooth (ivChart (corner t) (orChart B x)
        (cubeLift (n := 1) f hf.isScSmooth.1 (t, x)))
        (mem_ivChart_source _ (mem_orChart x) (mem_chart_corner t)) hz).choose_spec)
    (p₀.ivPt b hb q₀).mem_source ((chart b t : Fin 1 → ℝ), p₀.z) (p₀.ivPt b hb q₀).toBase_z rfl
    hf hfc hxs hne₀ hne (o x hxs)
  refine (DFunLike.congr_fun h3 _).symm.trans ?_
  refine (congrArg (C₂.orTransfer (p₀.ivPt b hb q₀) hfc hz) (Equiv.apply_symm_apply _ _)).trans ?_
  exact h2

namespace StrongBundle.LocalIso

variable {U U' : Set ((Fin 1 → unitInterval) × X)} {U₀ U₀' : Set X}
  {L : LocalIso (ivBundle B) (ivBundle B) U U'} {L₀ : LocalIso B B U₀ U₀'}
  {x x' : X} {t : Fin 1 → unitInterval}

/-- **The orientation map of `L = id × L₀` carries `(e ∧ o)_{(t, x)}` to `(e ∧ o)_{(t, x')}`**
for a family `o` with `(L₀)_* o_x = o_{x'}`, in the chosen chart points. -/
theorem orVia_ivFirstFun (hL : IsIntervalProductAt L L₀ (t, x'))
    (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (a : ChartPoint (ivBundle B) (t, x)) (ha : a.c.φ.source ⊆ U') (hz' : (t, x') ∈ U)
    (hϕ : L.ϕ (t, x') = (t, x))
    (hlin : (L.pullPt a ha hz' hϕ).linSet (cubeLift (n := 1) f hf.isScSmooth.1) =
      a.linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (a₀ : ChartPoint B x) (ha₀ : a₀.c.φ.source ⊆ U₀') (hx' : x' ∈ U₀) (hϕ₀ : L₀.ϕ x' = x)
    (hlin₀ : (L₀.pullPt a₀ ha₀ hx' hϕ₀).linSet f = a₀.linSet f)
    (hxs : x ∈ PX.smoothSet) (hx's : x' ∈ PX.smoothSet)
    (hinv : L₀.orVia hf (chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs)
      (chartPtOf (orChart B x') (isChart_orChart x') (mem_orChart x') hx's) a₀ ha₀ hx' hϕ₀ hlin₀
      hxs hx's (o x hxs) = o x' hx's) :
    L.orVia hfc
        (chartPtOf (orChart (ivBundle B) (t, x)) (isChart_orChart (t, x)) (mem_orChart (t, x))
          (prod_cube_mem_smoothSet_iff.2 hxs))
        (chartPtOf (orChart (ivBundle B) (t, x')) (isChart_orChart (t, x')) (mem_orChart (t, x'))
          (prod_cube_mem_smoothSet_iff.2 hx's)) a ha hz' hϕ hlin
        (prod_cube_mem_smoothSet_iff.2 hxs) (prod_cube_mem_smoothSet_iff.2 hx's)
        (ivFirstFun hf hfc hsec o (t, x) (prod_cube_mem_smoothSet_iff.2 hxs)) =
      ivFirstFun hf hfc hsec o (t, x') (prod_cube_mem_smoothSet_iff.2 hx's) := by
  have hzs : ((t, x) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hxs
  have hz's : ((t, x') : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    prod_cube_mem_smoothSet_iff.2 hx's
  set p := chartPtOf (orChart B x) (isChart_orChart x) (mem_orChart x) hxs with hp
  set p' := chartPtOf (orChart B x') (isChart_orChart x') (mem_orChart x') hx's with hp'
  set q := chartPtOf (orChart (ivBundle B) (t, x)) (isChart_orChart (t, x)) (mem_orChart (t, x))
    hzs with hq
  set q' := chartPtOf (orChart (ivBundle B) (t, x')) (isChart_orChart (t, x'))
    (mem_orChart (t, x')) hz's with hq'
  have hne := p.linSet_nonempty hf hxs hsec
  have hne' := p'.linSet_nonempty hf hx's hsec
  have q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) :=
    cubeLift (n := 1) f hf.isScSmooth.1 (t, x)
  have e1 := ivFirstFun_orTransfer hf hfc hsec o t hxs p (corner t) (mem_chart_corner t) q₀ hne
  have e2 := ivFirstFun_orTransfer hf hfc hsec o t hx's p' (corner t) (mem_chart_corner t) q₀
    hne'
  rw [p.orTransfer_self hf hxs] at e1
  rw [p'.orTransfer_self hf hx's] at e2
  have e1' : ivFirstFun hf hfc hsec o (t, x) hzs =
      (p.ivPt (corner t) (mem_chart_corner t) q₀).orTransfer q hfc hzs
        (p.ivOrFirst₀ (corner t) (mem_chart_corner t) q₀ hf hfc hxs hne (o x hxs)) := by
    exact ((DFunLike.congr_fun (q.orTransfer_trans (p.ivPt (corner t) (mem_chart_corner t) q₀) q
      hfc hzs) _).trans (DFunLike.congr_fun (q.orTransfer_self hfc hzs) _)).symm.trans
      (congrArg ((p.ivPt (corner t) (mem_chart_corner t) q₀).orTransfer q hfc hzs) e1)
  have e2' : ivFirstFun hf hfc hsec o (t, x') hz's =
      (p'.ivPt (corner t) (mem_chart_corner t) q₀).orTransfer q' hfc hz's
        (p'.ivOrFirst₀ (corner t) (mem_chart_corner t) q₀ hf hfc hx's hne' (o x' hx's)) := by
    exact ((DFunLike.congr_fun (q'.orTransfer_trans (p'.ivPt (corner t) (mem_chart_corner t) q₀)
      q' hfc hz's) _).trans (DFunLike.congr_fun (q'.orTransfer_self hfc hz's) _)).symm.trans
      (congrArg ((p'.ivPt (corner t) (mem_chart_corner t) q₀).orTransfer q' hfc hz's) e2)
  rw [e1', e2', ← hinv]
  exact orVia_ivOrFirst₀ hL hf hfc q q' a ha hz' hϕ hlin p p' a₀ ha₀ hx' hϕ₀ hlin₀ hxs hx's
    (corner t) (mem_chart_corner t) q₀ q₀ hne hne' (o x hxs)

end StrongBundle.LocalIso

end Family

end Polyfold
