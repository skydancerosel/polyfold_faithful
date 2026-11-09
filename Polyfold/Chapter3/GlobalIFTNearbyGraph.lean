import Polyfold.Chapter3.GlobalIFTFull
import Polyfold.Chapter2.TameInvariance

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.6.8 (preprint 3.54) (1) at the nearby zeros**: the derivative identities in the chart at `x₀` needed to
pass from the graph description of the solution set (`theorem_3_6_8_graph_wholeChart`) to the intrinsic
linearization `Tf̃(z₀) = Dg(z₀)|_{T_{z₀}O}` at a zero `z₀ = ϕ(y)` of the filled section `g`.

# Derivative identities at the nearby zeros

## The text, paraphrased

(Proof of Theorem 3.6.8 (preprint 3.54), (4)) "For every `y ∈ V` satisfying `f(y) = 0`, so that `ψ ∘ ϕ(y) = v + σ(v)`,
the kernel `ker f'(y)` is in good position to the partial cone `C_yX ⊆ T_yX`, and `f'(y)` is
surjective.  Property (4) follows from Corollary 3.41 and from Lemma 3.55."

## What is formalized

The general identities, at a level-`1` point `z₀₁ ∈ U₁` rather than at `0`:

* `Polyfold.scDeriv_eq_of_eqOn_nhds_at`: two sc¹-derivatives at a point `x ∈ C₁` of maps that
  agree near `x` in `C` coincide (uniqueness within the quadrant on level `1`, then density).
* `Polyfold.IsStrongBundleMap.scDeriv_fiber_at`, `scDeriv_fiber_comp_at`: the linearization of the
  fibre part `(u, k) ↦ (Ψ(u, k))₂` of a strong bundle map at `(u₀, 0)` is `k ↦ Γ(u₀)k`, and
  `D(u ↦ Γ(u)k(u))(u₀) = Γ(u₀)Dk(u₀)` when `k(u₀) = 0`.
* `Polyfold.IsStrongBundleIso.scDeriv_pushforward_at`: the chain rule
  `D(Ψ_*g)(ψ(u₀)) = Γ(u₀) ∘ Dg(u₀) ∘ Dψ⁻¹(ψ(u₀))` at a zero `u₀` of `g`, and
  `ker Dg(u₀) = Dψ⁻¹(ψ u₀)(ker D(Ψ_*g)(ψ u₀))` (`ker_scDeriv_eq_map`).
* `Polyfold.scDeriv_mem_partialQuadrantAtWith_iff`: `Dψ⁻¹(z)` carries the partial quadrant
  `C'_z` onto `C_{ψ⁻¹ z}` (the one-sided sign argument, `IsSc1With.mapsTo_partialQuadrant`,
  applied to `ψ⁻¹` and to `ψ`).
* `Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed`: if a `C¹`-map `Θ₁ : V → E₁` has
  `ρ ∘ ι ∘ Θ₁ = ι ∘ Θ₁` for an sc¹-map `ρ` (a retraction onto `O`, the curve lies in `O`), then
  `Dρ(Θ₁ v)` fixes the derivative of `ι ∘ Θ₁`, which therefore takes values in `range Dρ(Θ₁ v)` —
  the tangent vectors of curves in `O` lie in `T_{z₀}O`.
* `Polyfold.StabilityData.graphSpace_eq_ker_Dfs'`: **`N_v = ker D(h + s)(v + σ(v))`** for the
  solution graph of Theorem 3.5.11 (preprint 3.47): `N_v ⊆ ker` by differentiating `(h + s)(w + σ(w)) = 0` along
  `V` with the `C¹`-lift `σ₁ : V₁ → E₁` (`h + s` is differentiable on level `1` only), and
  equality by `dim N_v = dim K = ind D(h + s)(v + σ v) = dim ker` (both operators surjective).

## What the text leaves implicit, and the choices made (the findings)

* **`N_v = ker D(h + t)(z)`** (Finding 91 (a)): the text passes from Lemma 3.6.9 (preprint 3.55) (about the tangent
  space `N_v` of the graph) to "`ker f'(y)` is in good position" without comment.  The inclusion
  needs the `C¹`-lift of `σ` to level `1`; the equality is the dimension count through the index
  `n − N` of Corollary 3.5.3 (preprint 3.41).
* **The tangent vectors of the solution set lie in `T_{z₀}O`**: the zeros of `g` near `0` lie in
  `O` (condition (2) of Definition 3.1.4 (preprint 3.4)), so the solution graph, read in `E` through `ψ⁻¹`, is a
  `C¹` family of points of `O` and its tangent vectors are fixed by `Dr(z₀)`.  This is the
  replacement, at the nearby zero `z₀`, for the filler condition (3) that gave `ker Dg(0) ⊆ T₀O`
  at the centre (`IsFillerOf.ker_deriv_le_range`), which is not available at `z₀ ≠ 0`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach}

/-! ### Uniqueness of the derivative at a level-`1` point for maps agreeing nearby -/

section DerivEq

variable {C : Set (E 0)}

/-- Two derivatives at a point `x ∈ C₁` (in the sense of the sc¹-structures, `E₁ → F₀` composed
with the inclusion) of maps `f₁`, `f₂` that agree on a relatively open neighbourhood of `x` in `C`
on level `1` coincide: uniqueness of the derivative within the quadrant on level `1`, then density
of `E₁` in `E₀` (`scDeriv_eq_of_eqOn_nhds` at a general point). -/
theorem scDeriv_eq_of_eqOn_nhds_at (hC : IsQuadrantLike E C) {S₁ S₂ : Set (E 1)}
    {f₁ f₂ : E 0 → F 0} {D₁ D₂ : E 0 →L[ℝ] F 0} {x : E 1}
    (h₁ : HasFDerivWithinAt (f₁ ∘ E.toBase 1) (D₁.comp (E.toBase 1)) S₁ x)
    (h₂ : HasFDerivWithinAt (f₂ ∘ E.toBase 1) (D₂.comp (E.toBase 1)) S₂ x)
    {W₁ : Set (E 1)} (hW : IsOpen W₁) (hx : x ∈ W₁) (hS₁ : W₁ ∩ E.lvlSet C 1 ⊆ S₁)
    (hS₂ : W₁ ∩ E.lvlSet C 1 ⊆ S₂) (hxC : x ∈ E.lvlSet C 1)
    (heq : ∀ y ∈ W₁ ∩ E.lvlSet C 1, f₁ (E.toBase 1 y) = f₂ (E.toBase 1 y)) : D₁ = D₂ := by
  have hxS : x ∈ W₁ ∩ E.lvlSet C 1 := ⟨hx, hxC⟩
  have huniq : UniqueDiffWithinAt ℝ (W₁ ∩ E.lvlSet C 1) x := hC.uniqueDiffWithinAt hW hxS
  have h₁' : HasFDerivWithinAt (f₁ ∘ E.toBase 1) (D₁.comp (E.toBase 1)) (W₁ ∩ E.lvlSet C 1) x :=
    h₁.mono hS₁
  have h₂' : HasFDerivWithinAt (f₁ ∘ E.toBase 1) (D₂.comp (E.toBase 1)) (W₁ ∩ E.lvlSet C 1) x :=
    (h₂.mono hS₂).congr (fun y hy => heq y hy) (heq x hxS)
  have hcomp : D₁.comp (E.toBase 1) = D₂.comp (E.toBase 1) := huniq.eq h₁' h₂'
  have hdense : DenseRange (E.toBase 1) := E.denseRange_incl 0
  ext y
  have := hdense.equalizer D₁.continuous D₂.continuous (by
    ext z
    exact congrArg (fun L : E 1 →L[ℝ] F 0 => L z) hcomp)
  exact congrFun this y

end DerivEq

/-! ### The fibre derivative of a strong bundle map at a point `(u₀, 0)` -/

namespace IsStrongBundleMap

variable {C : Set (E 0)} {U : Set (E 0)} {U' : Set (E' 0)} {Ψ : E 0 × F 0 → E' 0 × F' 0}
  (hΨ : IsStrongBundleMap U U' Ψ)
include hΨ

/-- **The linearization of `Γ(u)k` at `(u₀, 0)`**, `u₀ ∈ U₁`: `D(pr_{F'} ∘ Ψ)(u₀, 0)(h, k) = Γ(u₀)k`
(`scDeriv_fiber_zero` at a general base point: the fibre direction is the linear map `Γ(u₀)`,
the base direction vanishes because `Γ(u)0 = 0`). -/
theorem scDeriv_fiber_at (hU : IsRelOpenInQuadrant E C U) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1)
    (h : E 0) (k : F 0) :
    scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) ((u₁, 0) : (E.prod F) 1) (h, k) =
      hΨ.fiberCLM hu₁ k := by
  set D := scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) ((u₁, 0) : (E.prod F) 1) with hD
  have hu₀ : E.toBase 1 u₁ ∈ U := hu₁
  have h01 : ((u₁, 0) : (E.prod F) 1) ∈ (E.prod F).lvlSet (U ×ˢ univ) 1 := by
    rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]; exact ⟨hu₀, mem_univ _⟩
  have hder := (hΨ.fiber_isSc1 hU).isSc1With_scDeriv.hasFDerivWithinAt _ h01
  -- the fibre direction
  have hinr : D.comp (ContinuousLinearMap.inr ℝ (E 0) (F 0)) = hΨ.fiberCLM hu₁ := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := F)
    have hmaps : MapsTo (fun k₁ : F 1 => ((u₁, k₁) : (E.prod F) 1)) univ
        ((E.prod F).lvlSet (U ×ˢ univ) 1) := by
      intro k₁ _
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]; exact ⟨hu₀, mem_univ _⟩
    have haff : HasFDerivWithinAt (fun k₁ : F 1 => ((u₁, k₁) : (E.prod F) 1))
        (ContinuousLinearMap.inr ℝ (E 1) (F 1)) univ 0 := by
      have := ((ContinuousLinearMap.inr ℝ (E 1) (F 1)).hasFDerivAt (x := (0 : F 1))).const_add
        ((u₁, 0) : (E.prod F) 1)
      refine this.hasFDerivWithinAt.congr (fun k₁ _ => ?_) ?_
      · simp
      · simp
    have h1 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          fun k₁ : F 1 => ((u₁, k₁) : (E.prod F) 1))
        ((D.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inr ℝ (E 1) (F 1))) univ 0 := by
      have h0' : (fun k₁ : F 1 => ((u₁, k₁) : (E.prod F) 1)) 0 = (u₁, 0) := by simp
      have := HasFDerivWithinAt.comp (0 : F 1) (h0' ▸ hder) haff hmaps
      exact this
    have h2 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          fun k₁ : F 1 => ((u₁, k₁) : (E.prod F) 1))
        ((hΨ.fiberCLM hu₁).comp (F.toBase 1)) univ 0 := by
      have : (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          fun k₁ : F 1 => ((u₁, k₁) : (E.prod F) 1)) = fun k₁ => hΨ.fiberCLM hu₁ (F.toBase 1 k₁) := by
        funext k₁
        simp only [Function.comp_apply]
        change (Ψ ((E.prod F).toBase 1 (u₁, k₁))).2 = _
        rw [ScBanach.prod_toBase]
        rfl
      rw [this]
      exact ((hΨ.fiberCLM hu₁).comp (F.toBase 1)).hasFDerivAt.hasFDerivWithinAt
    have huniq := uniqueDiffWithinAt_univ.eq h1 h2
    ext k₁
    have := congrArg (fun T : F 1 →L[ℝ] F' 0 => T k₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  -- the base direction
  have hinl : D.comp (ContinuousLinearMap.inl ℝ (E 0) (F 0)) = 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have hmaps : MapsTo ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)) (E.lvlSet U 1)
        ((E.prod F).lvlSet (U ×ˢ univ) 1) := by
      intro w₁ hw₁
      change ((w₁, (0 : F 1)) : (E.prod F) 1) ∈ _
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]; exact ⟨hw₁, mem_univ _⟩
    have h1 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        ((D.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (E.lvlSet U 1) u₁ :=
      HasFDerivWithinAt.comp (f := ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) u₁ hder
        (ContinuousLinearMap.inl ℝ (E 1) (F 1)).hasFDerivWithinAt hmaps
    have hzero : ∀ w₁ ∈ E.lvlSet U 1,
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) w₁ = 0 := by
      intro w₁ hw₁
      simp only [Function.comp_apply, ContinuousLinearMap.inl_apply]
      change (Ψ ((E.prod F).toBase 1 (w₁, (0 : F 1)))).2 = 0
      rw [ScBanach.prod_toBase, map_zero]
      exact (hΨ.fiber_linear _ hw₁).map_zero
    have h2 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (0 : E 1 →L[ℝ] F' 0) (E.lvlSet U 1) u₁ :=
      (hasFDerivWithinAt_const (0 : F' 0) u₁ (E.lvlSet U 1)).congr hzero (hzero u₁ hu₁)
    have huniq := (hU.isScDomain.uniqueDiffWithinAt 1 u₁ hu₁).eq h1 h2
    ext w₁
    have := congrArg (fun T : E 1 →L[ℝ] F' 0 => T w₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, zero_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  have hhk : ((h, k) : (E.prod F) 0) = ContinuousLinearMap.inl ℝ (E 0) (F 0) h +
      ContinuousLinearMap.inr ℝ (E 0) (F 0) k := by simp
  rw [hhk, map_add]
  have e1 := congrArg (fun T : E 0 →L[ℝ] F' 0 => T h) hinl
  have e2 := congrArg (fun T : F 0 →L[ℝ] F' 0 => T k) hinr
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at e1 e2
  rw [e1, e2, zero_add]

/-- **The derivative of `u ↦ Γ(u)k(u)` at a zero `u₀ ∈ U₁` of `k`**: `Γ(u₀)Dk(u₀)`
(`scDeriv_fiber_comp` at a general base point). -/
theorem scDeriv_fiber_comp_at (hU : IsRelOpenInQuadrant E C U) {k : E 0 → F 0}
    (hk : IsScSmooth U k) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) (hk0 : k (E.toBase 1 u₁) = 0) :
    scDeriv U (fun u => (Ψ (u, k u)).2) u₁ = (hΨ.fiberCLM hu₁).comp (scDeriv U k u₁) := by
  have hUF := (hU.prod_univ F).isScDomain
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 u₁ hu₁
  have hid : IsSc1 U (_root_.id : E 0 → E 0) := (isScSmooth_id hU.isScDomain).isSc1
  set Dk := scDeriv U k u₁ with hDk
  have hpair : IsSc1 U (scPair (_root_.id : E 0 → E 0) k) :=
    (IsSck.scPair (k := 1) hU.isScDomain (isScSmooth_id hU.isScDomain 1) (hk 1)).1
  have hmaps : MapsTo (scPair (_root_.id : E 0 → E 0) k) U (U ×ˢ univ) := fun u hu =>
    ⟨hu, mem_univ _⟩
  have hDpair : scDeriv U (scPair (_root_.id : E 0 → E 0) k) u₁ =
      (ContinuousLinearMap.id ℝ (E 0)).prod Dk := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have h1 := hpair.isSc1With_scDeriv.hasFDerivWithinAt u₁ hu₁
    have hDid : scDeriv U (_root_.id : E 0 → E 0) u₁ = ContinuousLinearMap.id ℝ (E 0) :=
      IsSc1.scDeriv_eqOn (isSc1With_id U) (hU.isScDomain.uniqueDiffWithinAt 1) hu₁
    have h2 := (hid.isSc1With_scDeriv.hasFDerivWithinAt u₁ hu₁).prodMk
      (hk.isSc1.isSc1With_scDeriv.hasFDerivWithinAt u₁ hu₁)
    rw [hDid] at h2
    rw [ContinuousLinearMap.prod_comp']
    exact huniq.eq h1 h2
  have hlev : levelMap (scPair (_root_.id : E 0 → E 0) k) 1 u₁ = ((u₁, 0) : (E.prod F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    show ((E.toBase 1 u₁, (0 : F 0)) : (E.prod F) 0) = (E.toBase 1 u₁, k (E.toBase 1 u₁))
    rw [hk0]
  have hcomp : scDeriv U ((fun p : (E.prod F) 0 => (Ψ p).2) ∘ scPair (_root_.id : E 0 → E 0) k) u₁ =
      (hΨ.fiberCLM hu₁).comp Dk := by
    ext h
    have := scDeriv_comp_apply' hU (hU.prod_univ F) hpair (hΨ.fiber_isSc1 hU) hmaps hu₁ h
    rw [hlev, hDpair] at this
    rw [← this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    exact hΨ.scDeriv_fiber_at hU hu₁ _ _
  exact hcomp

end IsStrongBundleMap

/-! ### The derivative of the push-forward at a zero -/

namespace IsStrongBundleIso

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0} (hΨ : IsStrongBundleIso U U' Ψ Ψ')
include hΨ

/-- `ψ'₁(ψ₁(u₁)) = u₁` on level `1`. -/
lemma levelMap_base_base (hU : IsRelOpenInQuadrant E C U) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) :
    levelMap (IsStrongBundleMap.base Ψ') 1 (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) = u₁ :=
  levelMap_comp_eq_self ((hΨ.toFun.base_isScSmooth hU).isSc1.isSc0) hu₁ fun _ hu => hΨ.base_base hu

/-- `ψ₁(u₁) ∈ U'₁` for `u₁ ∈ U₁`. -/
lemma levelMap_base_mem (hU : IsRelOpenInQuadrant E C U) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) :
    levelMap (IsStrongBundleMap.base Ψ) 1 u₁ ∈ E'.lvlSet U' 1 :=
  (hΨ.toFun.base_isScSmooth hU).isSc1.isSc0.levelMap_mapsTo (fun _ hu => hΨ.toFun.base_mem hu) 1
    hu₁

/-- `ι(ψ₁(u₁)) = ψ(ι u₁)`. -/
lemma toBase_levelMap_base (hU : IsRelOpenInQuadrant E C U) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) :
    E'.toBase 1 (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) =
      IsStrongBundleMap.base Ψ (E.toBase 1 u₁) :=
  (hΨ.toFun.base_isScSmooth hU).isSc1.isSc0.toBase_levelMap hu₁

/-- **The chain rule for the push-forward at a zero `u₀ ∈ U₁` of `g`**:
`D(Ψ_*g)(ψ(u₀)) = Γ(u₀) ∘ Dg(u₀) ∘ Dψ⁻¹(ψ(u₀))` (the text's `Ψ_*(g) = h + t` differentiated at
`z = ψ(z₀)`; `IsStrongBundleIso.pushforward_linearization_wholeChart` at a general zero). -/
theorem scDeriv_pushforward_at (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    {g : E 0 → F 0} (hg : IsScSmooth U g) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1)
    (hg0 : g (E.toBase 1 u₁) = 0) (x : E' 0) :
    scDeriv U' (pushforward Ψ Ψ' g) (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) x =
      hΨ.toFun.fiberCLM hu₁ (scDeriv U g u₁
        (scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) x)) := by
  have hUF := (hU.prod_univ F).isScDomain
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  have hpairsm : IsScSmooth U (scPair (_root_.id : E 0 → E 0) g) :=
    (isScSmooth_id hU.isScDomain).scPair hU.isScDomain hg
  have hκsm : IsScSmooth U fun u => (Ψ (u, g u)).2 :=
    (IsScSmooth.comp hU.isScDomain hUF (hΨ.toFun.isScSmooth_zero.snd hUF) hpairsm
      fun u hu => ⟨hu, mem_univ _⟩).congr hU.isScDomain fun _ _ => rfl
  have hpush : pushforward Ψ Ψ' g = (fun u => (Ψ (u, g u)).2) ∘ ψ' := rfl
  have hz₁ : levelMap ψ 1 u₁ ∈ E'.lvlSet U' 1 := hΨ.levelMap_base_mem hU hu₁
  have hchain := scDeriv_comp_apply' hU' hU hψ'sm.isSc1 hκsm.isSc1 hψ'U hz₁ x
  rw [hΨ.levelMap_base_base hU hu₁, hΨ.toFun.scDeriv_fiber_comp_at hU hg hu₁ hg0] at hchain
  rw [hpush, ← hchain]
  rfl

/-- `Dψ⁻¹(ψ(u₀)) ∘ Dψ(u₀) = 1` and `Dψ(u₀) ∘ Dψ⁻¹(ψ(u₀)) = 1` on level `0`. -/
lemma scDeriv_base_inv_base (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁)
      (scDeriv U (IsStrongBundleMap.base Ψ) u₁ v) = v :=
  scDeriv_comp_eq_self hU hU' (hΨ.toFun.base_isScSmooth hU).isSc1
    (hΨ.invFun.base_isScSmooth hU').isSc1 (fun _ hu => hΨ.toFun.base_mem hu)
    (fun _ hu => hΨ.base_base hu) hu₁ v

lemma scDeriv_base_base_inv (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) (w : E' 0) :
    scDeriv U (IsStrongBundleMap.base Ψ) u₁
      (scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) w) = w := by
  have := scDeriv_comp_eq_self hU' hU (hΨ.invFun.base_isScSmooth hU').isSc1
    (hΨ.toFun.base_isScSmooth hU).isSc1 (fun _ hu => hΨ.invFun.base_mem hu)
    (fun _ hu => hΨ.base_base' hu) (hΨ.levelMap_base_mem hU hu₁) w
  rwa [hΨ.levelMap_base_base hU hu₁] at this

/-- `Dψ⁻¹(ψ(u₀)) : E'₀ ≃ E₀`, with inverse `Dψ(u₀)`. -/
def derivInvEquiv (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) : E' 0 ≃L[ℝ] E 0 :=
  ContinuousLinearEquiv.equivOfInverse
    (scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁))
    (scDeriv U (IsStrongBundleMap.base Ψ) u₁) (hΨ.scDeriv_base_base_inv hU hU' hu₁)
    (hΨ.scDeriv_base_inv_base hU hU' hu₁)

@[simp] lemma derivInvEquiv_apply (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1) (w : E' 0) :
    hΨ.derivInvEquiv hU hU' hu₁ w =
      scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) w := rfl

/-- `Γ(u₀) : F₀ → F'₀` is injective (its inverse is the fibre map of `Ψ'` at `ψ(u₀)`). -/
lemma fiberCLM_injective {u : E 0} (hu : u ∈ U) : Injective (hΨ.toFun.fiberCLM hu) := by
  intro k k' hkk'
  have h1 : Ψ (u, k) = Ψ (u, k') := by
    rw [hΨ.toFun.apply_eq hu k, hΨ.toFun.apply_eq hu k']
    exact Prod.ext rfl hkk'
  have h2 := congrArg Prod.snd (hΨ.left_inv (u, k) ⟨hu, mem_univ _⟩)
  have h3 := congrArg Prod.snd (hΨ.left_inv (u, k') ⟨hu, mem_univ _⟩)
  rw [h1] at h2
  exact h2.symm.trans h3

/-- **`ker Dg(u₀) = Dψ⁻¹(ψ u₀)(ker D(Ψ_*g)(ψ u₀))`** at a zero `u₀ ∈ U₁` of `g`. -/
theorem ker_scDeriv_eq_map (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    {g : E 0 → F 0} (hg : IsScSmooth U g) {u₁ : E 1} (hu₁ : u₁ ∈ E.lvlSet U 1)
    (hg0 : g (E.toBase 1 u₁) = 0) :
    LinearMap.ker (scDeriv U g u₁ : E 0 →ₗ[ℝ] F 0) =
      (LinearMap.ker (scDeriv U' (pushforward Ψ Ψ' g) (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) :
        E' 0 →ₗ[ℝ] F' 0)).map
        (scDeriv U' (IsStrongBundleMap.base Ψ') (levelMap (IsStrongBundleMap.base Ψ) 1 u₁) :
          E' 0 →ₗ[ℝ] E 0) := by
  ext v
  rw [Submodule.mem_map, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hv
    refine ⟨scDeriv U (IsStrongBundleMap.base Ψ) u₁ v, ?_, hΨ.scDeriv_base_inv_base hU hU' hu₁ v⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΨ.scDeriv_pushforward_at hU hU' hg hu₁ hg0,
      hΨ.scDeriv_base_inv_base hU hU' hu₁, hv, map_zero]
  · rintro ⟨w, hw, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      hΨ.scDeriv_pushforward_at hU hU' hg hu₁ hg0] at hw
    exact (map_eq_zero_iff _ (hΨ.fiberCLM_injective hu₁)).1 hw

end IsStrongBundleIso

/-! ### `Dψ⁻¹(z)` carries `C'_z` onto `C_{ψ⁻¹(z)}` -/

section Sign

variable {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
  {U' : Set (E' 0)} {ψ : E 0 → E' 0} {ψ' : E' 0 → E 0}

/-- **The partial quadrants at corresponding points are carried by the derivative** of an
sc-diffeomorphism `ψ : U → U'` with inverse `ψ'`: for `z ∈ U'₁`,
`x ∈ C'_z ↔ Dψ'(z)x ∈ C_{ψ'(z)}` (the one-sided sign argument `IsSc1With.mapsTo_partialQuadrant`
for `ψ'` at `z` and for `ψ` at `ψ'(z)`; `scDeriv_mem_iff_of_inverse` at a general point). -/
theorem scDeriv_mem_partialQuadrantAtWith_iff
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hψ : IsScSmooth U ψ) (hψ' : IsScSmooth U' ψ') (hψU : MapsTo ψ U U') (hψ'U : MapsTo ψ' U' U)
    (hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u') {z : E' 1} (hz : z ∈ E'.lvlSet U' 1) (x : E' 0) :
    x ∈ partialQuadrantAtWith T' (E'.toBase 1 z) ↔
      scDeriv U' ψ' z x ∈ partialQuadrantAtWith T (ψ' (E'.toBase 1 z)) := by
  have hU'C : U' ⊆ C' := by obtain ⟨O, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have hUC : U ⊆ C := by obtain ⟨O, -, rfl⟩ := hU.relOpen; exact inter_subset_right
  have hfwd := hψ'.isSc1.isSc1With_scDeriv.mapsTo_partialQuadrant T' hT' T hT hU'
    (fun u hu => hUC (hψ'U hu)) hz
  have hw : levelMap ψ' 1 z ∈ E.lvlSet U 1 := hψ'.isSc1.isSc0.levelMap_mapsTo hψ'U 1 hz
  have hbwd := hψ.isSc1.isSc1With_scDeriv.mapsTo_partialQuadrant T hT T' hT' hU
    (fun u hu => hU'C (hψU hu)) hw
  have htb : E.toBase 1 (levelMap ψ' 1 z) = ψ' (E'.toBase 1 z) := hψ'.isSc1.isSc0.toBase_levelMap hz
  rw [htb, hψ'ψ _ hz] at hbwd
  refine ⟨fun hx => hfwd hx, fun hx => ?_⟩
  have := hbwd hx
  rwa [scDeriv_comp_eq_self hU' hU hψ'.isSc1 hψ.isSc1 hψ'U hψ'ψ hz x] at this

end Sign

/-! ### Tangent vectors of a `C¹` family of points of a retract lie in `T_{z₀}O` -/

section Fixed

variable {C : Set (E 0)} {U : Set (E 0)} {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Let `ρ : U → E₀` be sc¹ and `Θ₁ : N → E₁` differentiable at `v` within `V` with
`Θ₁(V) ⊆ U₁` and `ρ(ι Θ₁ w) = ι Θ₁ w` for `w ∈ V` (the points `ι Θ₁ w` lie in the fixed-point
set of `ρ`).  Then `Dρ(Θ₁ v)` fixes every `ι (DΘ₁(v) n)`: the tangent vectors of the family lie
in `range Dρ(Θ₁ v)`.  (For `ρ = r` the retraction onto `O`: the tangent vectors of a `C¹`-family
of points of `O` lie in `T_{z₀}O`.) -/
theorem scDeriv_apply_toBase_deriv_eq_of_fixed {ρ : E 0 → E 0}
    (hρ : IsSc1 U ρ) {Θ₁ : N → E 1} {L₁ : N →L[ℝ] E 1} {V : Set N} {v : N}
    (hΘ : HasFDerivWithinAt Θ₁ L₁ V v) (huniq : UniqueDiffWithinAt ℝ V v) (hv : v ∈ V)
    (hΘU : MapsTo Θ₁ V (E.lvlSet U 1))
    (hfix : ∀ w ∈ V, ρ (E.toBase 1 (Θ₁ w)) = E.toBase 1 (Θ₁ w)) (m : N) :
    scDeriv U ρ (Θ₁ v) (E.toBase 1 (L₁ m)) = E.toBase 1 (L₁ m) := by
  have hρd := hρ.isSc1With_scDeriv.hasFDerivWithinAt (Θ₁ v) (hΘU hv)
  have h1 : HasFDerivWithinAt ((ρ ∘ E.toBase 1) ∘ Θ₁)
      (((scDeriv U ρ (Θ₁ v)).comp (E.toBase 1)).comp L₁) V v :=
    HasFDerivWithinAt.comp v hρd hΘ hΘU
  have h2 : HasFDerivWithinAt ((ρ ∘ E.toBase 1) ∘ Θ₁) ((E.toBase 1).comp L₁) V v := by
    refine ((E.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt v hΘ).congr (fun w hw => ?_) ?_
    · exact hfix w hw
    · exact hfix v hv
  have := huniq.eq h1 h2
  exact congrArg (fun T : N →L[ℝ] E 0 => T m) this

end Fixed

/-! ### The dimension of the graph of a map into a complement

(`finrank_ker_eq_fredholmIndex_of_surjective`, `dim ker u = ind u` for a surjective Fredholm
operator, is in `GlobalIFT.lean`.) -/

section Finrank

/-- The graph `{n + L n}` of `L : N → V` with values in a complement `P` of `N` has the dimension
of `N`. -/
theorem finrank_graphSpace_of_compl {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {N : Submodule ℝ V} [FiniteDimensional ℝ N] {P : Submodule ℝ V} (hNP : Disjoint N P)
    (L : N →L[ℝ] V) (hLP : ∀ w, L w ∈ P) : finrank ℝ (graphSpace N L) = finrank ℝ N := by
  set A : N →ₗ[ℝ] V := N.subtype + (L : N →ₗ[ℝ] V) with hAdef
  have hAinj : Injective A := by
    intro w₁ w₂ hw
    have hw' : (w₁ : V) + L w₁ = (w₂ : V) + L w₂ := hw
    have h1 : (w₁ : V) - w₂ = L w₂ - L w₁ := by
      rw [sub_eq_sub_iff_add_eq_add, hw', add_comm]
    have hmemN : (w₁ : V) - w₂ ∈ N := N.sub_mem w₁.2 w₂.2
    have hmemP : (w₁ : V) - w₂ ∈ P := by rw [h1]; exact P.sub_mem (hLP w₂) (hLP w₁)
    have : (w₁ : V) - w₂ = 0 := (Submodule.disjoint_def.1 hNP) _ hmemN hmemP
    exact Subtype.ext (sub_eq_zero.1 this)
  have hrange : LinearMap.range A = graphSpace N L := by
    ext x
    rw [LinearMap.mem_range, mem_graphSpace]
    rfl
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj hAinj

end Finrank

/-! ### Unique differentiability of relatively open subsets of `N ∩ C` -/

section UniqueDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- A relatively open subset `V = O ∩ (N ∩ C)` of the cone `N ∩ C` of a subspace `N` in good
position to `C = C̃ ⊕ W` has unique differentiability at each of its points. -/
theorem uniqueDiffWithinAt_relOpen_cone (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {N : Submodule ℝ (P × W 0)} (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) N)
    {V : Set N} (hVrel : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) {v : N}
    (hv : v ∈ V) : UniqueDiffWithinAt ℝ V v := by
  obtain ⟨O, hO, rfl⟩ := hVrel
  have hCt0 : Convex ℝ Ct := by
    have h := hC.isQuadrantLike.convex 0
    rwa [ScBanach.const_lvlSet] at h
  have hconv : Convex ℝ (Subtype.val ⁻¹' (Ct ×ˢ univ) : Set N) :=
    (hCt0.prod convex_univ).linear_preimage N.subtype
  rw [inter_comm]
  exact (uniqueDiffWithinAt_convex hconv hpos.interior_nonempty (subset_closure hv.2)).inter
    (hO.mem_nhds hv.1)

omit [FiniteDimensional ℝ P] in
/-- Two relatively open neighbourhoods `V₁ ⊆ V` of `0` in `N ∩ C` satisfy `V₁ = V ∩ O₁`. -/
theorem relOpen_cone_inter {N : Submodule ℝ (P × W 0)} {V V₁ : Set N}
    (hVrel : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ))
    {O₁ : Set N} (hV₁ : V₁ = O₁ ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) (hV₁V : V₁ ⊆ V) :
    V₁ = V ∩ O₁ := by
  obtain ⟨O, -, rfl⟩ := hVrel
  ext w
  constructor
  · intro hw; exact ⟨hV₁V hw, (hV₁ ▸ hw : w ∈ O₁ ∩ _).1⟩
  · rintro ⟨hwV, hwO₁⟩; rw [hV₁]; exact ⟨hwO₁, hwV.2⟩

end UniqueDiff

/-! ### The derivative of a map with a `C¹`-lift to level `1` -/

section LiftDeriv

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- If `σ₁ : V₁ → E₁` is differentiable at `v` within `V₁` and `ι ∘ σ₁ = σ` on `V₁`, then
`Dσ(v) = ι ∘ Dσ₁(v)` (within `V₁`, and within any `V ⊇ V₁` with `V₁ = V ∩ O₁`, `O₁` open). -/
theorem fderivWithin_eq_toBase_comp {σ : N → E 0} {σ₁ : N → E 1} {V V₁ O₁ : Set N} (hO₁ : IsOpen O₁)
    (hV₁V : V₁ = V ∩ O₁) {v : N} (hv : v ∈ V₁) (huniq : UniqueDiffWithinAt ℝ V₁ v)
    (hσ₁ : DifferentiableWithinAt ℝ σ₁ V₁ v) (hσ₁eq : ∀ y ∈ V₁, E.toBase 1 (σ₁ y) = σ y) :
    fderivWithin ℝ σ V v = (E.toBase 1).comp (fderivWithin ℝ σ₁ V₁ v) := by
  have h1 : HasFDerivWithinAt (E.toBase 1 ∘ σ₁) ((E.toBase 1).comp (fderivWithin ℝ σ₁ V₁ v)) V₁ v :=
    (E.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt v hσ₁.hasFDerivWithinAt
  have h2 : HasFDerivWithinAt σ ((E.toBase 1).comp (fderivWithin ℝ σ₁ V₁ v)) V₁ v :=
    h1.congr (fun w hw => (hσ₁eq w hw).symm) (hσ₁eq v hv).symm
  have h3 := h2.fderivWithin huniq
  have h4 : fderivWithin ℝ σ V₁ v = fderivWithin ℝ σ V v := by
    rw [hV₁V]; exact fderivWithin_inter (hO₁.mem_nhds (hV₁V ▸ hv : v ∈ V ∩ O₁).2)
  rw [← h4, h3]

end LiftDeriv

/-! ### Good position inside a subspace containing the kernel -/

section GoodIn

variable {C : Set (E 0)}

/-- If `N` is in good position to `C` in `E₀` and `N ⊆ T`, then `N` is in good position to `C`
inside `T` (Definition 3.1.24 (preprint 3.21) in `T`, `IsInGoodPositionIn`): a good complement `P` of `N` in `E₀`
restricts to the good complement `P ∩ T` of `N` in `T`, with the same constant. -/
theorem IsInGoodPosition.isInGoodPositionIn_of_le {N : Submodule ℝ (E 0)}
    (h : IsInGoodPosition E C N) {T : Submodule ℝ (E 0)} (hNT : N ≤ T) :
    IsInGoodPositionIn E T C N := by
  obtain ⟨hint, P, hPc, ε, hε, hgood⟩ := h
  refine ⟨hNT, hint, P ⊓ T, inf_le_right, ?_, ?_, ε, hε, fun x hx p hp hle => hgood x hx p hp.1 hle⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxN, hxP, -⟩
    exact (Submodule.disjoint_def.1 hPc.disjoint) x hxN hxP
  · apply le_antisymm
    · exact sup_le hNT inf_le_right
    · intro x hxT
      have hx : x ∈ N ⊔ P := by rw [hPc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨n, hn, p, ⟨hp, ?_⟩, rfl⟩
      have : (n + p) - n ∈ T := T.sub_mem hxT (hNT hn)
      rwa [add_sub_cancel_left] at this

end GoodIn

/-! ### The tangent space of the solution graph is the kernel of `D(h + s)(v + σ(v))` -/

namespace StabilityData

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q] (𝒮 : StabilityData Ct W) {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}

/-- **`N_v ⊆ ker D(h + s)(v + σ(v))`**: for the solution graph `σ : V → E₀` of Theorem 3.5.11 (preprint 3.47) with
the `C¹`-lift `σ₁ : V₁ → E₁` (`ι ∘ σ₁ = σ` on the relatively open `V₁ ⊆ V`), at `v ∈ V₁` with
`x₁ = v + σ₁(v) ∈ U₁`: differentiating `(h + s)(w + σ(w)) = 0` along `V₁` at `v` gives
`D(h + s)(x₁)(n + Dσ(v)n) = 0` for `n ∈ K` (`h + s` is differentiable on level `1` only, which is
why the lift is needed). -/
theorem graphSpace_le_ker_Dfs' (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hf : IsBasicGerm Ct 𝒮.G f B)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)))
    {V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))}
    (hVrel : ∃ O, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ))
    {σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0}
    (hsol : ∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0)
    {V₁ : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))} {O₁ : Set _} (hO₁ : IsOpen O₁)
    (hV₁ : V₁ = O₁ ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) (hV₁V : V₁ ⊆ V)
    {σ₁ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd P W) 1}
    (hσ₁ : ContDiffOn ℝ 1 σ₁ V₁)
    (hσ₁eq : ∀ y ∈ V₁, (ScBanach.paramProd P W).toBase 1 (σ₁ y) = σ y)
    {v : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)} (hv : v ∈ V₁)
    {x₁ : (ScBanach.paramProd P W) 1} (hx₁ : (ScBanach.paramProd P W).toBase 1 x₁ = (v : P × W 0) + σ v)
    (hx₁G : x₁ ∈ 𝒮.G.U 1) :
    graphSpace (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) (fderivWithin ℝ σ V v) ≤
      LinearMap.ker (𝒮.Dfs' f x₁ : P × W 0 →ₗ[ℝ] Q × W 0) := by
  classical
  have hKs : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) ≤ (ScBanach.paramProd P W).smooth :=
    𝒮.ker_Dfs_le_smooth hC hf
  have : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hC hf).1.finite_ker
  -- the lift of `(LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))` to level `1` and the lifted graph map `Γ₁ = lift + σ₁`
  set lift : (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) →L[ℝ] (ScBanach.paramProd P W) 1 := (ScBanach.paramProd P W).finLift hKs 1 with hliftdef
  have hlift : ∀ w : (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)), (ScBanach.paramProd P W).toBase 1 (lift w) = w := fun w => (ScBanach.paramProd P W).toBase_finLift hKs 1 w
  set Γ₁ : (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) → (ScBanach.paramProd P W) 1 := fun w => lift w + σ₁ w with hΓ₁def
  have hΓ₁ : ∀ w ∈ V₁, (ScBanach.paramProd P W).toBase 1 (Γ₁ w) = (w : P × W 0) + σ w := fun w hw => by
    simp only [hΓ₁def, map_add, hlift, hσ₁eq w hw]
  have hΓ₁v : Γ₁ v = x₁ := (ScBanach.paramProd P W).toBase_injective 1 (by rw [hΓ₁ v hv, hx₁])
  have hV₁V' : V₁ = V ∩ O₁ := relOpen_cone_inter hVrel hV₁ hV₁V
  have huniq : UniqueDiffWithinAt ℝ V₁ v := uniqueDiffWithinAt_relOpen_cone hC hpos ⟨O₁, hO₁, hV₁⟩ hv
  -- derivatives of `σ₁` and `Γ₁` within `V₁`
  have hσ₁d : HasFDerivWithinAt σ₁ (fderivWithin ℝ σ₁ V₁ v) V₁ v :=
    (hσ₁.differentiableOn one_ne_zero v hv).hasFDerivWithinAt
  set L₁ : (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) →L[ℝ] (ScBanach.paramProd P W) 1 := lift + fderivWithin ℝ σ₁ V₁ v with hL₁def
  have hΓ₁d : HasFDerivWithinAt Γ₁ L₁ V₁ v := lift.hasFDerivWithinAt.add hσ₁d
  -- `ι ∘ Dσ₁(v) = Dσ(v)`
  have hDσ : fderivWithin ℝ σ V v = ((ScBanach.paramProd P W).toBase 1).comp (fderivWithin ℝ σ₁ V₁ v) := by
    have h1 : HasFDerivWithinAt ((ScBanach.paramProd P W).toBase 1 ∘ σ₁) (((ScBanach.paramProd P W).toBase 1).comp (fderivWithin ℝ σ₁ V₁ v))
        V₁ v := ((ScBanach.paramProd P W).toBase 1).hasFDerivAt.comp_hasFDerivWithinAt v hσ₁d
    have h2 : HasFDerivWithinAt σ (((ScBanach.paramProd P W).toBase 1).comp (fderivWithin ℝ σ₁ V₁ v)) V₁ v :=
      h1.congr (fun w hw => (hσ₁eq w hw).symm) (hσ₁eq v hv).symm
    have h3 := h2.fderivWithin huniq
    have h4 : fderivWithin ℝ σ V₁ v = fderivWithin ℝ σ V v := by
      rw [hV₁V']; exact fderivWithin_inter (hO₁.mem_nhds (hV₁V' ▸ hv : v ∈ V ∩ O₁).2)
    rw [← h4, h3]
  -- the composite `(h + s) ∘ ι ∘ Γ₁` vanishes on `V₁` and is differentiable at `v`
  have hfs := (𝒮.isSc1GermWith_Dfs' hC.isQuadrantLike hf.isScSmooth).hasFDerivWithinAt x₁ hx₁G
  obtain ⟨Og₁, hOg₁, hGeq₁⟩ := 𝒮.G.relOpen 1
  have hx₁Og : x₁ ∈ Og₁ := (hGeq₁ ▸ hx₁G : x₁ ∈ Og₁ ∩ _).1
  have hΓ₁cont : ContinuousWithinAt Γ₁ V₁ v := hΓ₁d.continuousWithinAt
  have hnhds : Γ₁ ⁻¹' Og₁ ∈ 𝓝[V₁] v := hΓ₁cont (hOg₁.mem_nhds (hΓ₁v ▸ hx₁Og))
  have hmaps : MapsTo Γ₁ (V₁ ∩ Γ₁ ⁻¹' Og₁) (𝒮.G.U 1) := by
    rintro w ⟨hwV₁, hwO⟩
    rw [hGeq₁]
    refine ⟨hwO, ?_⟩
    rw [ScBanach.mem_lvlSet, hΓ₁ w hwV₁]
    exact 𝒮.G.U_subset 0 (hsol w (hV₁V hwV₁)).1
  have hfs' : HasFDerivWithinAt (𝒮.fsum f ∘ (ScBanach.paramProd P W).toBase 1)
      ((𝒮.Dfs' f x₁).comp ((ScBanach.paramProd P W).toBase 1)) (𝒮.G.U 1) (Γ₁ v) := by
    rw [hΓ₁v]; exact hfs
  have hcomp : HasFDerivWithinAt ((𝒮.fsum f ∘ (ScBanach.paramProd P W).toBase 1) ∘ Γ₁)
      (((𝒮.Dfs' f x₁).comp ((ScBanach.paramProd P W).toBase 1)).comp L₁) V₁ v := by
    have h := HasFDerivWithinAt.comp v hfs' (hΓ₁d.mono inter_subset_left) hmaps
    exact h.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hnhds)
  have hzero : HasFDerivWithinAt ((𝒮.fsum f ∘ (ScBanach.paramProd P W).toBase 1) ∘ Γ₁) (0 : (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) →L[ℝ] Q × W 0) V₁ v := by
    refine (hasFDerivWithinAt_const (0 : Q × W 0) v V₁).congr (fun w hw => ?_) ?_
    · simp only [Function.comp_apply]; rw [hΓ₁ w hw]; exact (hsol w (hV₁V hw)).2
    · simp only [Function.comp_apply]; rw [hΓ₁ v hv]; exact (hsol v (hV₁V hv)).2
  have hD0 := huniq.eq hcomp hzero
  -- conclusion
  rintro _ ⟨n, rfl⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have := congrArg (fun T : (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) →L[ℝ] Q × W 0 => T n) hD0
  simp only [ContinuousLinearMap.comp_apply, zero_apply, hL₁def, add_apply, map_add, hlift] at this
  simp only [hDσ, LinearMap.add_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, map_add]
  exact this

/-- **`N_v = ker D(h + s)(v + σ(v))`**: equality by the dimension count
`dim N_v = dim (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) = ind D(h + s)(0) = ind D(h + s)(x₁) = dim ker D(h + s)(x₁)`, the two operators
being surjective (Corollary 3.5.3 (preprint 3.41)). -/
theorem graphSpace_eq_ker_Dfs' (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hf : IsBasicGerm Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f))
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)))
    {Y : Submodule ℝ (P × W 0)}
    (hY : IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) Y)
    (hYc : IsClosed (Y : Set (P × W 0)))
    {V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))}
    (hVrel : ∃ O, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ))
    {σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0} (hσY : ∀ y, σ y ∈ Y)
    (hσC : ContDiffOn ℝ 1 σ V)
    (hsol : ∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0)
    {V₁ : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))} {O₁ : Set _} (hO₁ : IsOpen O₁)
    (hV₁ : V₁ = O₁ ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) (hV₁V : V₁ ⊆ V)
    {σ₁ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd P W) 1}
    (hσ₁ : ContDiffOn ℝ 1 σ₁ V₁)
    (hσ₁eq : ∀ y ∈ V₁, (ScBanach.paramProd P W).toBase 1 (σ₁ y) = σ y)
    {v : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)} (hv : v ∈ V₁)
    {x₁ : (ScBanach.paramProd P W) 1} (hx₁ : (ScBanach.paramProd P W).toBase 1 x₁ = (v : P × W 0) + σ v)
    (hx₁G : x₁ ∈ 𝒮.G.U 1) (hF : IsFredholm (𝒮.Dfs' f x₁))
    (hind : fredholmIndex (𝒮.Dfs' f x₁) = finrank ℝ P - finrank ℝ Q)
    (hsurj' : Surjective (𝒮.Dfs' f x₁)) :
    graphSpace (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) (fderivWithin ℝ σ V v) =
      LinearMap.ker (𝒮.Dfs' f x₁ : P × W 0 →ₗ[ℝ] Q × W 0) := by
  classical
  have : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hC hf).1.finite_ker
  have : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs' f x₁ : P × W 0 →ₗ[ℝ] Q × W 0)) := hF.finite_ker
  have hle := 𝒮.graphSpace_le_ker_Dfs' hC hf hpos hVrel hsol hO₁ hV₁ hV₁V hσ₁ hσ₁eq hv hx₁ hx₁G
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  -- `Dσ(v)` takes values in `Y`
  have hvV : v ∈ V := hV₁V hv
  have hLY : ∀ w : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0), fderivWithin ℝ σ V v w ∈ Y := fun w =>
    fderivWithin_mem_of_mapsTo (hσC.differentiableOn one_ne_zero v hvV).hasFDerivWithinAt
      (uniqueDiffWithinAt_relOpen_cone hC hpos hVrel hvV) hYc (fun x _ => hσY x) hvV w
  rw [finrank_graphSpace_of_compl hY.isCompl.disjoint _ hLY]
  -- the two dimension counts
  have h1 := finrank_ker_eq_fredholmIndex_of_surjective (𝒮.isFredholm_Dfs hC hf).1 hsurj
  have h2 := finrank_ker_eq_fredholmIndex_of_surjective hF hsurj'
  rw [(𝒮.isFredholm_Dfs hC hf).2] at h1
  rw [hind] at h2
  exact_mod_cast h1.trans h2.symm

end StabilityData

/-! ### Theorem 3.6.8 (preprint 3.54), the graph description, in the chart with the filler data exposed -/

section ChartGraph

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.6.8 (preprint 3.54), the graph description (3) of the solution set, in the chart with the filler
data exposed** (the body of `theorem_3_6_8_graph_wholeChart` with the data of Definition 3.6.6 (preprint 3.53) as hypotheses):
`g` a filled version of `f̂` at the zero `0` with `(f̂, 0)` in good position, `t₀` the sc⁺-section
with `g − t₀` conjugated to the basic germ `h` by `Ψ` (base map `ψ`, inverse `ψ'`), the
retraction tame (`(1 − Dr(0))E ⊆ E₀`).  Then there are the data `𝒮` of Theorem 3.4.2 (preprint 3.38) (germ `G`)
and the basic germ `h' = h + (t_{ℝᴺ}, 0)` with `𝒮.fsum h' = Ψ_*(g)` on `U' ∩ W'`, `W'` an open
neighbourhood of `0`; `D(𝒮.fsum h')(0)` surjective with kernel `K` in good position; the data
`Yc`, `V'`, `σ` of Theorem 3.5.11 (preprint 3.47) (`Yc` closed, `σ` with `C^k`-lifts); an open neighbourhood `N₁`
of `0` on which the identities of the filler and of the conjugation hold and `ψ'(U' ∩ W') ⊆ N₁`;
and an open neighbourhood `N₂ ⊆ N₁` of `0` such that `ψ(U ∩ N₂) ⊆ G₀ ∩ W'`, every zero of `g`
in `U ∩ N₂` lies in `O`, `g(u) = 0 ↔ 𝒮.fsum h'(ψ u) = 0` on `O ∩ N₂`, and
`ψ({u ∈ O ∩ N₂ | g(u) = 0}) = {v + σ(v) | v ∈ V'}`. -/
theorem theorem_3_6_8_chart_graph_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0U : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0U fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {t₀ : E 0 → F 1} (ht₀ : IsScSmooth (F := F.shift) U t₀) (ht₀0 : F.toBase 1 (t₀ 0) = g 0)
    {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {W : ScBanach} {Ct : Set Pn} {U' : Set ((ScBanach.paramProd Pn W) 0)}
    {Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0}
    {Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0}
    {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)} {h : Pn × W 0 → Q × W 0}
    {Bc : Pn × W 0 → W 0} (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0) (hG : G.U 0 ⊆ U')
    (hh : IsBasicGerm Ct G h Bc)
    (hev : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U →
      (Ψ (u, g u - F.toBase 1 (t₀ u))).2 = h (IsStrongBundleMap.base Ψ u))
    {n : ℕ} {Wc : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wc))
    (hT : C = T 0 ⁻¹' quadrant n Wc 0)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    (hgp : IsGoodPositionAt hU hR h0U g) :
    ∃ (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0) (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0)
      (W' : Set ((ScBanach.paramProd Pn W) 0)) (N₁ N₂ : Set (E 0)),
      𝒮.G = G ∧ IsBasicGerm Ct 𝒮.G h' Bc ∧ Surjective (𝒮.Dfs h') ∧
      IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∧
      IsOpen W' ∧ (0 : (ScBanach.paramProd Pn W) 0) ∈ W' ∧
      (∀ u' ∈ U' ∩ W', 𝒮.fsum h' u' = pushforward Ψ Ψ' g u') ∧
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      (∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V' ∧
      (∀ y, σ y ∈ Yc) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V' ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V' 0 = 0 ∧
      (∀ y ∈ V', (y : Pn × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum h' ((y : Pn × W 0) + σ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
        (∃ O : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
          IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V' ∧
        ∃ σk : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd Pn W) k,
          ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd Pn W).toBase k (σk y) = σ y) ∧
      IsOpen N₁ ∧ (0 : E 0) ∈ N₁ ∧
      (∀ u ∈ N₁, (u ∈ r R '' U → fb u = g u) ∧
        (u ∈ U → g u = ρ R (r R u) (g u) → u ∈ r R '' U) ∧
        (u ∈ U → (Ψ (u, g u - F.toBase 1 (t₀ u))).2 = h (IsStrongBundleMap.base Ψ u))) ∧
      (∀ u' ∈ U' ∩ W', IsStrongBundleMap.base Ψ' u' ∈ N₁) ∧
      IsOpen N₂ ∧ (0 : E 0) ∈ N₂ ∧ N₂ ⊆ N₁ ∧
      (∀ u ∈ U ∩ N₂, IsStrongBundleMap.base Ψ u ∈ 𝒮.G.U 0 ∧
        IsStrongBundleMap.base Ψ u ∈ U' ∩ W') ∧
      (∀ u ∈ U ∩ N₂, g u = 0 → u ∈ r R '' U) ∧
      (∀ u ∈ r R '' U ∩ N₂, g u = 0 ↔ 𝒮.fsum h' (IsStrongBundleMap.base Ψ u) = 0) ∧
      IsStrongBundleMap.base Ψ '' {u ∈ r R '' U ∩ N₂ | g u = 0} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' := by
  classical
  -- notation
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  set sb : E 0 → F 0 := fun u => F.toBase 1 (t₀ u) with hsbdef
  have hOU : r R '' U ⊆ U := fun z hz => mem_U_of_mem_O hR hz
  have hC'q : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0U
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0U hψ0
  have hψsc : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sc : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψ'cont : ContinuousOn ψ' U' := hψ'sc.isSc1.isSc0.continuousOn_base
  have hψcont : ContinuousOn ψ U := hψsc.isSc1.isSc0.continuousOn_base
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  -- the neighbourhood `N₁` of `0` where the identities of the filler and the conjugation hold
  have hN₀ : ∀ᶠ u in 𝓝 (0 : E 0), (u ∈ r R '' U → fb u = g u) ∧
      (u ∈ U → g u = ρ R (r R u) (g u) → u ∈ r R '' U) ∧
      (u ∈ U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := by
    have h1 := hfill.filler.eq_on
    have h2 := hfill.filler.mem_of_fixed
    refine (h1.and (h2.and hev)).mono fun u hu => ⟨hu.1, hu.2.1, fun huU => ?_⟩
    exact hu.2.2 huU
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hN₀
  have hN₁ : ∀ u ∈ N₁, (u ∈ r R '' U → fb u = g u) ∧
      (u ∈ U → g u = ρ R (r R u) (g u) → u ∈ r R '' U) ∧
      (u ∈ U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := fun u hu => hN₁sub hu
  have hgO : ∀ u ∈ U, u ∈ N₁ → g u = 0 → u ∈ r R '' U := fun u hu huN hgu =>
    (hN₁ u huN).2.1 hu (by
      rw [hgu]
      exact ((ρ_isLinear hR (r_mem hR hu)).map_zero).symm)
  have hg0 : g 0 = 0 := by rw [← (hN₁ 0 h0N₁).1 h0O, hfb0]
  have ht00 : t₀ 0 = 0 := by
    apply F.toBase_injective 1
    rw [ht₀0, hg0, map_zero]
  -- the push-forward sc⁺-germ `t = Ψ[1]_*(t₀)` on `E'`
  set t : (ScBanach.paramProd Pn W) 0 → (ScBanach.paramProd Q W).shift 0 :=
    fun u' => (shiftFiber Ψ (ψ' u', t₀ (ψ' u'))).2 with htdef
  have htsc : IsScSmooth (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) U' t := by
    have hpair : IsScSmooth (E := ScBanach.paramProd Pn W) (F := E.prod F.shift) U'
        (scPair (F := E) (G := F.shift) ψ' (fun u' => t₀ (ψ' u'))) := by
      refine hψ'sc.scPair hU'.isScDomain ?_
      exact IsScSmooth.comp hU'.isScDomain hU.isScDomain ht₀ hψ'sc fun u' hu' =>
        hΨ.invFun.base_mem hu'
    have hUF := (hU.prod_univ F.shift).isScDomain
    have hmaps : MapsTo (scPair (F := E) (G := F.shift) ψ' (fun u' => t₀ (ψ' u'))) U'
        (U ×ˢ univ) := fun u' hu' =>
      ⟨hΨ.invFun.base_mem hu', mem_univ _⟩
    have := IsScSmooth.comp hU'.isScDomain hUF hΨ.toFun.isScSmooth_one hpair hmaps
    exact (this.snd hU'.isScDomain).congr hU'.isScDomain fun _ _ => rfl
  have hGsub : ∀ m, G.U m ⊆ (ScBanach.paramProd Pn W).lvlSet U' m := fun m z hz =>
    hG (G.toBase_mem hz)
  have htG : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) G t :=
    (htsc.isScSmoothGerm hC'q hU'.relOpen h0U').mono hC'q hGsub
  have ht0 : t 0 = 0 := by
    simp only [htdef, hψ'0, ht00]
    unfold shiftFiber
    simp only [map_zero]
    rw [hΨ.toFun.snd_zero h0U]
    have := Function.leftInverse_invFun ((ScBanach.paramProd Q W).toBase_injective 1) 0
    rw [map_zero] at this
    exact this
  -- the key identity: for `u ∈ U ∩ N₁`, `Ψ_*(g)(ψ u) = h(ψ u) + ι t(ψ u)`
  have hkey : ∀ u ∈ U, u ∈ N₁ →
      pushforward Ψ Ψ' g (ψ u) = h (ψ u) + (ScBanach.paramProd Q W).toBase 1 (t (ψ u)) := by
    intro u hu huN
    have e1 : t (ψ u) = (shiftFiber Ψ (u, t₀ u)).2 := by
      simp only [htdef]; rw [hψψ' u hu]
    have e2 : (ScBanach.paramProd Q W).toBase 1 (shiftFiber Ψ (u, t₀ u)).2 = (Ψ (u, sb u)).2 :=
      hΨ.toFun.toBase_shiftFiber_snd (p := (u, t₀ u)) hu
    have e3 : h (ψ u) = (Ψ (u, g u - sb u)).2 := ((hN₁ u huN).2.2 hu).symm
    rw [e1, e2, e3, hΨ.toFun.snd_sub hu, sub_add_cancel]
    show (Ψ (ψ' (ψ u), g (ψ' (ψ u)))).2 = (Ψ (u, g u)).2
    rw [hψψ' u hu]
  -- the basic germ `h' = h + (t_{ℝᴺ}, 0)` and the data of Theorem 3.4.2 (preprint 3.38) with `s = t_W`
  set h' : Pn × W 0 → Q × W 0 := fun x => h x + ScBanach.qPartOp Q W 0 (t x) with hh'def
  have hh' : IsBasicGerm Ct G h' Bc :=
    { isScSmooth := by
        have hq : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := ScBanach.paramProd Q W) G
            (ScBanach.qPartOp Q W 0 ∘ t) :=
          fun k => IsSckGerm.operator_comp hC'q (ScBanach.qPartOp Q W) (htG k)
        have hp : IsScSmoothGerm (E := ScBanach.paramProd Pn W)
            (F := (ScBanach.paramProd Q W).prod (ScBanach.paramProd Q W)) G
            (pairMap (F := ScBanach.paramProd Q W) (G := ScBanach.paramProd Q W) h
              (ScBanach.qPartOp Q W 0 ∘ t)) :=
          IsScSmoothGerm.pair (F := ScBanach.paramProd Q W) (G := ScBanach.paramProd Q W) hC'q
            hh.isScSmooth hq
        intro k
        exact (IsSckGerm.operator_comp hC'q (ScBanach.paramProd Q W).addOp (hp k)).congr hC'q
          fun x _ => rfl
      f_zero := by
        show h 0 + ScBanach.qPartOp Q W 0 (t 0) = 0
        rw [hh.f_zero, ht0, map_zero, add_zero]
      snd_eq := fun x hx => by
        show (h x + ScBanach.qPartOp Q W 0 (t x)).2 = x.2 - Bc x
        rw [Prod.snd_add, hh.snd_eq x hx, ScBanach.qPartOp_apply, add_zero]
      contraction := hh.contraction }
  have hsW : IsScSmoothGerm (E := ScBanach.paramProd Pn W) (F := W.shift) G
      (fun x => (t x).2) := fun k =>
    (IsSckGerm.operator_comp hC'q (ScBanach.wPartOp Q W) (htG k)).congr hC'q fun _ _ => rfl
  have hsW0 : ((t 0).2 : W 1) = 0 := by rw [ht0]; rfl
  obtain ⟨𝒮, h𝒮G, h𝒮s⟩ := StabilityData.exists_of_scPlus hsW hsW0
  have hh'𝒮 : IsBasicGerm Ct 𝒮.G h' Bc := by rw [h𝒮G]; exact hh'
  have hfsum : ∀ x, 𝒮.fsum h' x = h x + (ScBanach.paramProd Q W).toBase 1 (t x) := fun x => by
    rw [StabilityData.fsum_apply, h𝒮s, ScBanach.paramProd_toBase]
    change h x + ((t x).1, (0 : W 0)) + ((0 : Q), W.toBase 1 (t x).2) = h x + ((t x).1, W.toBase 1 (t x).2)
    rw [add_assoc]
    congr 1
    ext <;> simp
  -- the push-forward: surjective Fredholm linearization with kernel in good position
  have hconj' : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (t₀ u) :=
    ⟨Pn, Q, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance,
      W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩
  obtain ⟨hpush, -, hsurjP, -, hposP⟩ := theorem_3_6_8_pushforward_wholeChart hU hR h0U h0O hfill hfb0 hfK ht₀
    ht₀0 hconj' T hT hK hgp hU' hΨ hψ0
  -- `D(𝒮.fsum h')(0) = D(Ψ_*g)(0)`: the two maps agree near `0`
  have hW' : ∀ᶠ u' in 𝓝 (0 : (ScBanach.paramProd Pn W) 0), u' ∈ U' → ψ' u' ∈ N₁ := by
    have h1 : Tendsto ψ' (𝓝[U'] 0) (𝓝 0) := by
      have := hψ'cont 0 h0U'
      rwa [ContinuousWithinAt, hψ'0] at this
    exact eventually_nhdsWithin_iff.1 (h1 (hN₁open.mem_nhds h0N₁))
  obtain ⟨W', hW'sub, hW'open, h0W'⟩ := mem_nhds_iff.1 hW'
  obtain ⟨Uo, hUo, hU'eq⟩ := hU'.relOpen
  obtain ⟨Og, hOg, hGeq⟩ := G.relOpen 0
  obtain ⟨Og₁, hOg₁, hGeq₁⟩ := G.relOpen 1
  have hGmem : ∀ u', u' ∈ G.U 0 ↔ u' ∈ Og ∧ u' ∈ Ct ×ˢ univ := fun u' => by
    rw [hGeq]; rfl
  have hagree : ∀ u' ∈ U', u' ∈ W' → 𝒮.fsum h' u' = pushforward Ψ Ψ' g u' := by
    intro u' hu' huW
    have hu := hΨ.invFun.base_mem hu'
    rw [hfsum, ← hψ'ψ u' hu', hkey (ψ' u') hu (hW'sub huW hu')]
  have hDeq : 𝒮.Dfs h' = scDeriv U' (pushforward Ψ Ψ' g) 0 := by
    have hfs1 := (𝒮.fsum_isScSmoothGerm (hCt.isQuadrantLike) (h𝒮G ▸ hh'.isScSmooth) 1).1
      |>.isSc1GermWith_scDerivGerm
    have h₁ := hfs1.hasFDerivWithinAt 0 (𝒮.G.zero_mem 1)
    have h₂ := hpush.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0
      (by rw [ScBanach.mem_lvlSet, map_zero]; exact h0U')
    refine scDeriv_eq_of_eqOn_nhds hC'q h₁ h₂
      (W₁ := (ScBanach.paramProd Pn W).lvlSet (W' ∩ Uo) 1 ∩ Og₁)
      (((ScBanach.paramProd Pn W).isOpen_lvlSet (hW'open.inter hUo) 1).inter hOg₁)
      ⟨by rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨h0W', hU'eq ▸ h0U' |>.1⟩,
        (hGeq₁ ▸ G.zero_mem 1 : (0 : (ScBanach.paramProd Pn W) 1) ∈ Og₁ ∩ _).1⟩
      ?_ ?_ (by rw [ScBanach.mem_lvlSet, map_zero]; exact hU'C h0U') ?_
    · rintro x ⟨⟨-, hxOg⟩, hxC⟩
      rw [h𝒮G, hGeq₁]; exact ⟨hxOg, hxC⟩
    · rintro x ⟨⟨hxW, -⟩, hxC⟩
      rw [ScBanach.mem_lvlSet, hU'eq]
      exact ⟨(hxW : _ ∈ W' ∩ Uo).2, hxC⟩
    · rintro x ⟨⟨hxW, -⟩, hxC⟩
      have hxU' : (ScBanach.paramProd Pn W).toBase 1 x ∈ U' := by
        rw [hU'eq]; exact ⟨(hxW : _ ∈ W' ∩ Uo).2, hxC⟩
      exact hagree _ hxU' (hxW : _ ∈ W' ∩ Uo).1
  have hsurj : Surjective (𝒮.Dfs h') := by rw [hDeq]; exact hsurjP
  have hpos : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
      (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) := by rw [hDeq]; exact hposP
  -- Theorem 3.5.11 (preprint 3.47) for `h + t`
  obtain ⟨Yc, V₀, σ, hYc, hYcc, hV₀rel, hV₀0, hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, U'', hU''o,
    h0U'', hU''⟩ := theorem_3_5_11_closed hCt 𝒮 hh'𝒮 hsurj hpos
  -- the open set `Ω = U'' ∩ W'` of `E'` and the shrunken `V'`
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set ((ScBanach.paramProd Pn W) 0), Ω = U'' ∩ W' := ⟨_, rfl⟩
  have hΩo : IsOpen Ω := hΩdef ▸ hU''o.inter hW'open
  have h0Ω : (0 : (ScBanach.paramProd Pn W) 0) ∈ Ω := hΩdef ▸ ⟨h0U'', h0W'⟩
  have hΩW' : ∀ z ∈ Ω, z ∈ W' := fun z hz => (hΩdef ▸ hz : z ∈ U'' ∩ W').2
  have hΩU'' : ∀ z ∈ Ω, z ∈ U'' := fun z hz => (hΩdef ▸ hz : z ∈ U'' ∩ W').1
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0,
    Γ = fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v :=
    ⟨_, rfl⟩
  have hΓ : ∀ v, Γ v = (v : Pn × W 0) + σ v := fun v => by rw [hΓdef]
  have hΓcont : ContinuousOn Γ V₀ := by
    rw [hΓdef]; exact continuous_subtype_val.continuousOn.add hσC.continuousOn
  obtain ⟨O₁, hO₁, hO₁eq⟩ := (continuousOn_iff'.1 hΓcont) Ω hΩo
  obtain ⟨V', hV'def⟩ : ∃ V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
    V' = V₀ ∩ O₁ := ⟨_, rfl⟩
  have hV'sub : V' ⊆ V₀ := hV'def ▸ inter_subset_left
  have hV'Ω : ∀ v ∈ V', Γ v ∈ Ω := fun v hv => by
    have : v ∈ O₁ ∩ V₀ := ⟨(hV'def ▸ hv : v ∈ V₀ ∩ O₁).2, (hV'def ▸ hv : v ∈ V₀ ∩ O₁).1⟩
    rw [← hO₁eq] at this
    exact this.1
  have hmemV' : ∀ v ∈ V₀, Γ v ∈ Ω → v ∈ V' := fun v hv hΩv => by
    have : v ∈ Γ ⁻¹' Ω ∩ V₀ := ⟨hΩv, hv⟩
    rw [hO₁eq] at this
    rw [hV'def]; exact ⟨hv, this.1⟩
  have hV'rel : ∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ) := by
    obtain ⟨O₀, hO₀, hV₀⟩ := hV₀rel
    refine ⟨O₀ ∩ O₁, hO₀.inter hO₁, ?_⟩
    rw [hV'def, hV₀]
    ext v; simp only [mem_inter_iff]; tauto
  have h0V' : (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ V' :=
    hmemV' 0 hV₀0 (by rw [hΓ, Submodule.coe_zero, hσ0, add_zero]; exact h0Ω)
  -- the neighbourhood `N₂` of `0` in `E`: `N₁ ∩ (ψ⁻¹(Ω ∩ Og) relative to U)`
  obtain ⟨O₂, hO₂, hO₂eq⟩ := (continuousOn_iff'.1 hψcont) (Ω ∩ Og) (hΩo.inter hOg)
  obtain ⟨N₂, hN₂def⟩ : ∃ N₂ : Set (E 0), N₂ = N₁ ∩ O₂ := ⟨_, rfl⟩
  have hN₂o : IsOpen N₂ := hN₂def ▸ hN₁open.inter hO₂
  have h0O₂ : (0 : E 0) ∈ O₂ := by
    have : (0 : E 0) ∈ ψ ⁻¹' (Ω ∩ Og) ∩ U :=
      ⟨by rw [mem_preimage, hψ0]; exact ⟨h0Ω, ((hGmem 0).1 (G.zero_mem 0)).1⟩, h0U⟩
    rw [hO₂eq] at this; exact this.1
  have h0N₂ : (0 : E 0) ∈ N₂ := hN₂def ▸ ⟨h0N₁, h0O₂⟩
  have hN₂N₁ : N₂ ⊆ N₁ := hN₂def ▸ inter_subset_left
  have hN₂ψ : ∀ u ∈ U, u ∈ N₂ → ψ u ∈ Ω ∧ ψ u ∈ Og := fun u hu huN => by
    have : u ∈ O₂ ∩ U := ⟨(hN₂def ▸ huN : u ∈ N₁ ∩ O₂).2, hu⟩
    rw [← hO₂eq] at this
    exact this.1
  have hmemN₂ : ∀ u ∈ U, u ∈ N₁ → ψ u ∈ Ω → ψ u ∈ Og → u ∈ N₂ := fun u hu huN hΩ hOg => by
    have : u ∈ ψ ⁻¹' (Ω ∩ Og) ∩ U := ⟨⟨hΩ, hOg⟩, hu⟩
    rw [hO₂eq] at this
    rw [hN₂def]; exact ⟨huN, this.1⟩
  -- for `u ∈ U ∩ N₂`: `ψ u ∈ G.U 0`, and the zeros
  have hN₂G : ∀ u ∈ U, u ∈ N₂ → ψ u ∈ G.U 0 := fun u hu huN =>
    (hGmem _).2 ⟨(hN₂ψ u hu huN).2, hU'C (hψU' hu)⟩
  have hzero : ∀ u ∈ r R '' U, u ∈ N₂ → (g u = 0 ↔ 𝒮.fsum h' (ψ u) = 0) := by
    intro u huO huN
    have huU : u ∈ U := hOU huO
    rw [hfsum, ← hkey _ huU (hN₂N₁ huN)]
    show g u = 0 ↔ (Ψ (ψ' (ψ u), g (ψ' (ψ u)))).2 = 0
    rw [hψψ' _ huU]
    exact (hΨ.snd_eq_zero_iff huU).symm
  -- `Dσ(0) = 0` on the smaller `V'`
  have hDσ' : fderivWithin ℝ σ V' 0 = 0 := by
    have hd : HasFDerivWithinAt σ (0 : _ →L[ℝ] Pn × W 0) V₀ 0 := by
      have := (hσC.differentiableOn one_ne_zero 0 hV₀0).hasFDerivWithinAt
      rwa [hDσ] at this
    have huniq : UniqueDiffWithinAt ℝ V' 0 := uniqueDiffWithinAt_relOpen_cone hCt hpos hV'rel h0V'
    exact (hd.mono hV'sub).fderivWithin huniq
  -- the `C^k` lifts on the smaller `V'`
  have hlift' : ∀ k : ℕ, 1 ≤ k → ∃ Vk : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
      (∃ O : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)),
        IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
      (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ Vk ∧ Vk ⊆ V' ∧
      ∃ σk : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → (ScBanach.paramProd Pn W) k,
        ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, (ScBanach.paramProd Pn W).toBase k (σk y) = σ y := by
    intro k hk
    obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, h0k, hVkV₀, σk, hσk, hσkeq⟩ := hlift k hk
    refine ⟨Vk ∩ O₁, ⟨Ok ∩ O₁, hOk.inter hO₁, ?_⟩, ⟨h0k, (hV'def ▸ h0V' : (0 : _) ∈ V₀ ∩ O₁).2⟩,
      fun y hy => ?_, σk, hσk.mono inter_subset_left, fun y hy => hσkeq y hy.1⟩
    · rw [hVk, inter_right_comm]
    · rw [hV'def]; exact ⟨hVkV₀ hy.1, hy.2⟩
  refine ⟨𝒮, h', Yc, V', σ, W', N₁, N₂, h𝒮G, hh'𝒮, hsurj, hpos, hW'open, h0W',
    fun u' hu' => hagree u' hu'.1 hu'.2, hYc, hYcc, hV'rel, h0V', hσY, hσ1, hσC.mono hV'sub, hσ0,
    hDσ', fun y hy => hsol y (hV'sub hy), hlift', hN₁open, h0N₁, hN₁,
    fun u' hu' => hW'sub hu'.2 hu'.1, hN₂o, h0N₂, hN₂N₁,
    fun u hu => ⟨h𝒮G ▸ hN₂G u hu.1 hu.2, hψU' hu.1, hΩW' _ (hN₂ψ u hu.1 hu.2).1⟩,
    fun u hu hgu => hgO u hu.1 (hN₂N₁ hu.2) hgu, fun u hu => hzero u hu.1 hu.2, ?_⟩
  -- the graph description
  ext z
  constructor
  · rintro ⟨u, ⟨⟨huO, huN⟩, hgu⟩, rfl⟩
    have huU : u ∈ U := hOU huO
    have hz0 : 𝒮.fsum h' (ψ u) = 0 := (hzero u huO huN).1 hgu
    obtain ⟨v, hv, hveq⟩ := hU'' (ψ u) ⟨hΩU'' _ (hN₂ψ u huU huN).1, h𝒮G ▸ hN₂G u huU huN⟩ hz0
    refine ⟨v, hmemV' v hv ?_, hveq.symm⟩
    rw [hΓ, ← hveq]; exact (hN₂ψ u huU huN).1
  · rintro ⟨v, hv, rfl⟩
    have hvV₀ : v ∈ V₀ := hV'sub hv
    obtain ⟨hzG, hz0⟩ := hsol v hvV₀
    have hzG' : (v : Pn × W 0) + σ v ∈ G.U 0 := h𝒮G ▸ hzG
    have hzU' : (v : Pn × W 0) + σ v ∈ U' := hG hzG'
    have hvΩ : (v : Pn × W 0) + σ v ∈ Ω := hΓ v ▸ hV'Ω v hv
    have huN : ψ' ((v : Pn × W 0) + σ v) ∈ N₁ := hW'sub (hΩW' _ hvΩ) hzU'
    have huU : ψ' ((v : Pn × W 0) + σ v) ∈ U := hΨ.invFun.base_mem hzU'
    have hgu : g (ψ' ((v : Pn × W 0) + σ v)) = 0 := by
      have h1 := hkey _ huU huN
      rw [hψ'ψ _ hzU', ← hfsum, hz0] at h1
      have h2 : (Ψ (ψ' ((v : Pn × W 0) + σ v), g (ψ' ((v : Pn × W 0) + σ v)))).2 = 0 := by
        exact h1
      exact (hΨ.snd_eq_zero_iff huU).1 h2
    have huO : ψ' ((v : Pn × W 0) + σ v) ∈ r R '' U := hgO _ huU huN hgu
    refine ⟨ψ' ((v : Pn × W 0) + σ v), ⟨⟨huO, hmemN₂ _ huU huN ?_ ?_⟩, hgu⟩, hψ'ψ _ hzU'⟩
    · rw [hψ'ψ _ hzU']; exact hvΩ
    · rw [hψ'ψ _ hzU']; exact ((hGmem _).1 hzG').1

end ChartGraph

end Polyfold
