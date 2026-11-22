import Polyfold.Chapter4.TangentWhitneySum
import Polyfold.Chapter8.TangentLocal
import Polyfold.Chapter2.TangentMapLinear

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 195, and
Part II, §8.1, pp. 349–353: the Whitney sum `⊕ₖ Tf` of a map sc-smooth on an open set and of a
local sc-diffeomorphism.  Numbers and pages are the 2021 text's.

# `⊕ₖ Tf` on open sets and for local sc-diffeomorphisms

## The text, paraphrased

(p. 195) The Whitney sum `TX ⊕ ⋯ ⊕ TX → X¹` is an sc-smooth bundle.  (§8.1) For an ep-groupoid
the structure maps of the tangent ep-groupoid are the tangents `Ts`, `Tt` of the local
sc-diffeomorphisms `s`, `t`, and `Ts : TU(φ) → TU(x)` is an sc-diffeomorphism.  The same holds
for `k` copies of the tangent: this is what the transition sets `M(⊕ᵏ TΨ, ⊕ᵏ TΨ')` of
Proposition 17.6.1 use.

## What is formalized (namespace `Polyfold.MPolyfold`)

* `whitneyPreimage U` (`p⁻¹(U¹) ⊆ ⊕ₖ TX`), `whitneyMapOn hf v₀` (`⊕ₖ Tf` on `p⁻¹(U¹)` for `f`
  sc-smooth on `U`, junk `v₀` elsewhere), `isScSmoothOn_whitneyMapOn`, `whitneyMapOn_eqOn`
  (on `p⁻¹(U¹)` it is `⊕ₖ Tf` of a globally sc-smooth `f`).
* **`IsScDiffeoOn.whitney`**: an sc-diffeomorphism `f : U → V` with inverse `g` gives the
  sc-diffeomorphism `⊕ₖ Tf : p⁻¹(U¹) → p⁻¹(V¹)` with inverse `⊕ₖ Tg`.
* **`IsLocalScDiffeo.whitneyMapOf`**: `⊕ₖ Tf` of a local sc-diffeomorphism is a local
  sc-diffeomorphism.
* The fibres: `whitneyFiberMap hf hxy` (`⊕ₖ Tf : p⁻¹(x) → p⁻¹(y)` for `f(x) = y`, a linear map,
  `(Tf)ᵏ` under `p⁻¹(x) ≅ (T_xX)ᵏ`), `coe_whitneyFiberMap_apply`, and
  **`IsLocalScDiffeo.bijective_whitneyFiberMap`**: for a local sc-diffeomorphism it is a linear
  isomorphism of the fibres, so `⊕ₖ Tf` is a local bundle isomorphism covering `f¹`.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y} {k : ℕ}

variable (P k) in
/-- `p⁻¹(U¹) ⊆ ⊕ₖ TX`. -/
def whitneyPreimage (U : Set X) : Set (P.WhitneySum k) :=
  {v | P.levelVal 1 (whitneyProj v) ∈ U}

lemma isOpen_whitneyPreimage {U : Set X} (hU : IsOpen U) : IsOpen (P.whitneyPreimage k U) :=
  hU.preimage ((continuous_levelVal 1).comp continuous_whitneyProj)

lemma whitneyVec_mem_tangentPreimage {U : Set X} {v : P.WhitneySum k}
    (hv : v ∈ P.whitneyPreimage k U) (i : Fin k) : whitneyVec v i ∈ P.tangentPreimage U := by
  change P.levelVal 1 (P.tangentProj (whitneyVec v i)) ∈ U
  rw [tangentProj_whitneyVec]; exact hv

section On

open scoped Classical

variable {f : X → Y} {U : Set X}

/-- **`⊕ₖ Tf` on `p⁻¹(U¹)`** for `f` sc-smooth on the open set `U` (junk value `v₀` elsewhere). -/
def whitneyMapOn (hf : P.IsScSmoothOn Q f U) (v₀ : Q.WhitneySum k) (v : P.WhitneySum k) :
    Q.WhitneySum k :=
  if hv : v ∈ P.whitneyPreimage k U then
    whitneyMk (Q.levelMk 1 (f (P.levelVal 1 (whitneyProj v)))
        (hf.mapsTo_levelSet 1 ⟨hv, P.levelVal_mem _⟩))
      (fun i => tangentMapOn hf (whitneyVec v i)) fun i => level_ext (by
        rw [levelVal_tangentProj_tangentMapOn hf (whitneyVec_mem_tangentPreimage hv i),
          tangentProj_whitneyVec, levelVal_levelMk])
  else v₀

variable (hf : P.IsScSmoothOn Q f U) (v₀ : Q.WhitneySum k)

lemma levelVal_whitneyProj_whitneyMapOn {v : P.WhitneySum k} (hv : v ∈ P.whitneyPreimage k U) :
    Q.levelVal 1 (whitneyProj (whitneyMapOn hf v₀ v)) = f (P.levelVal 1 (whitneyProj v)) := by
  rw [whitneyMapOn, dif_pos hv]; rfl

lemma whitneyVec_whitneyMapOn {v : P.WhitneySum k} (hv : v ∈ P.whitneyPreimage k U)
    (i : Fin k) : whitneyVec (whitneyMapOn hf v₀ v) i = tangentMapOn hf (whitneyVec v i) := by
  rw [whitneyMapOn, dif_pos hv]; rfl

/-- `⊕ₖ Tf` maps `p⁻¹(U¹)` into `p⁻¹(V¹)` when `f(U) ⊆ V`. -/
lemma whitneyMapOn_mapsTo {V : Set Y} (hfUV : MapsTo f U V) :
    MapsTo (whitneyMapOn hf v₀) (P.whitneyPreimage k U) (Q.whitneyPreimage k V) := fun v hv => by
  change Q.levelVal 1 (whitneyProj (whitneyMapOn hf v₀ v)) ∈ V
  rw [levelVal_whitneyProj_whitneyMapOn hf v₀ hv]; exact hfUV hv

/-- **`⊕ₖ Tf` is sc-smooth on `p⁻¹(U¹)`**. -/
theorem isScSmoothOn_whitneyMapOn :
    (P.whitneyPolyfold k).IsScSmoothOn (Q.whitneyPolyfold k) (whitneyMapOn hf v₀)
      (P.whitneyPreimage k U) := by
  have hUo := isOpen_whitneyPreimage (P := P) (k := k) hf.isOpen
  let f₁ : P.Level 1 → Q.Level 1 := fun x =>
    if hx : P.levelVal 1 x ∈ U then Q.levelMk 1 (f (P.levelVal 1 x))
      (hf.mapsTo_levelSet 1 ⟨hx, P.levelVal_mem _⟩) else whitneyProj v₀
  have hf₁ : P.shift.IsScSmoothOn Q.shift f₁ {x | P.levelVal 1 x ∈ U} :=
    hf.levelOne fun x hx => by simp only [f₁, dif_pos hx, levelVal_levelMk]
  refine isScSmoothOn_whitneyLift ?_ fun i => ?_
  · have h := IsScSmoothOn.comp (g := f₁) hf₁
      ((isScSmoothMap_whitneyProj (P := P) (k := k)).mono hUo (subset_univ _)) fun v hv => hv
    refine h.congr fun v hv => level_ext ?_
    change Q.levelVal 1 (f₁ (whitneyProj v)) = _
    rw [levelVal_whitneyProj_whitneyMapOn hf v₀ hv]
    simp only [f₁, dif_pos (show P.levelVal 1 (whitneyProj v) ∈ U from hv), levelVal_levelMk]
  · have h := IsScSmoothOn.comp (g := tangentMapOn hf) (tangentMapOn_isScSmoothOn hf)
      ((isScSmoothMap_whitneyVec (P := P) (k := k) i).mono hUo (subset_univ _))
      fun v hv => whitneyVec_mem_tangentPreimage hv i
    exact h.congr fun v hv => (whitneyVec_whitneyMapOn hf v₀ hv i).symm

/-- On `p⁻¹(U¹)`, `whitneyMapOn` of a globally sc-smooth `f` is `⊕ₖ Tf`. -/
theorem whitneyMapOn_eqOn (hf' : P.IsScSmoothMap Q f) :
    EqOn (whitneyMapOn hf v₀) (whitneyMapOf (k := k) hf') (P.whitneyPreimage k U) :=
  fun v hv => whitneySum_ext (level_ext (levelVal_whitneyProj_whitneyMapOn hf v₀ hv)) fun i => by
    rw [whitneyVec_whitneyMapOn hf v₀ hv, whitneyVec_whitneyMapOf,
      tangentMapOn_eq_tangentMap hf' hf (whitneyVec_mem_tangentPreimage hv i)]

end On

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- **The Whitney sum of an sc-diffeomorphism between open sets**: `⊕ₖ Tf : p⁻¹(U¹) → p⁻¹(V¹)` is
an sc-diffeomorphism with inverse `⊕ₖ Tg`. -/
theorem IsScDiffeoOn.whitney (h : P.IsScDiffeoOn Q f g U V) (v₀ : Q.WhitneySum k)
    (w₀ : P.WhitneySum k) :
    (P.whitneyPolyfold k).IsScDiffeoOn (Q.whitneyPolyfold k) (whitneyMapOn h.isScSmoothOn v₀)
      (whitneyMapOn h.isScSmoothOn_inv w₀) (P.whitneyPreimage k U) (Q.whitneyPreimage k V) where
  isScSmoothOn := isScSmoothOn_whitneyMapOn h.isScSmoothOn v₀
  isScSmoothOn_inv := isScSmoothOn_whitneyMapOn h.isScSmoothOn_inv w₀
  mapsTo := whitneyMapOn_mapsTo h.isScSmoothOn v₀ h.mapsTo
  mapsTo_inv := whitneyMapOn_mapsTo h.isScSmoothOn_inv w₀ h.mapsTo_inv
  left_inv v hv := by
    have hv' := whitneyMapOn_mapsTo h.isScSmoothOn v₀ h.mapsTo hv
    refine whitneySum_ext (level_ext ?_) fun i => ?_
    · rw [levelVal_whitneyProj_whitneyMapOn _ _ hv', levelVal_whitneyProj_whitneyMapOn _ _ hv,
        h.left_inv _ hv]
    · rw [whitneyVec_whitneyMapOn _ _ hv', whitneyVec_whitneyMapOn _ _ hv]
      have h1 := tangentMapOn_comp h.isScSmoothOn_inv h.isScSmoothOn h.mapsTo
        (whitneyVec_mem_tangentPreimage hv i)
      rw [Function.comp_apply] at h1
      rw [← h1]
      exact tangentMapOn_eqOn_id _ (fun x hx => h.left_inv x hx)
        (whitneyVec_mem_tangentPreimage hv i)
  right_inv w hw := by
    have hw' := whitneyMapOn_mapsTo h.isScSmoothOn_inv w₀ h.mapsTo_inv hw
    refine whitneySum_ext (level_ext ?_) fun i => ?_
    · rw [levelVal_whitneyProj_whitneyMapOn _ _ hw', levelVal_whitneyProj_whitneyMapOn _ _ hw,
        h.right_inv _ hw]
    · rw [whitneyVec_whitneyMapOn _ _ hw', whitneyVec_whitneyMapOn _ _ hw]
      have h1 := tangentMapOn_comp h.isScSmoothOn h.isScSmoothOn_inv h.mapsTo_inv
        (whitneyVec_mem_tangentPreimage hw i)
      rw [Function.comp_apply] at h1
      rw [← h1]
      exact tangentMapOn_eqOn_id _ (fun y hy => h.right_inv y hy)
        (whitneyVec_mem_tangentPreimage hw i)

/-- **The Whitney sum of a local sc-diffeomorphism is a local sc-diffeomorphism**: on `p⁻¹(U¹)`,
for a sheet `f : U → V` with inverse `g`, `⊕ₖ Tf` is the sc-diffeomorphism with inverse `⊕ₖ Tg`. -/
theorem IsLocalScDiffeo.whitneyMapOf (hf : P.IsLocalScDiffeo Q f) :
    (P.whitneyPolyfold k).IsLocalScDiffeo (Q.whitneyPolyfold k)
      (MPolyfold.whitneyMapOf (k := k) hf.isScSmoothMap) := fun v => by
  obtain ⟨U, V, g, hx, hd⟩ := hf (P.levelVal 1 (whitneyProj v))
  exact ⟨P.whitneyPreimage k U, Q.whitneyPreimage k V, whitneyMapOn hd.isScSmoothOn_inv v, hx,
    (hd.whitney (MPolyfold.whitneyMapOf hf.isScSmoothMap v) v).congr_left
      (whitneyMapOn_eqOn hd.isScSmoothOn _ hf.isScSmoothMap)⟩

/-! ### `⊕ₖ Tf` on the fibres -/

section Fibre

variable {f : X → Y} {x : P.Level 1} {y : Q.Level 1}

/-- **`⊕ₖ Tf` on the fibre over `x`**, `f(x) = y`: the linear map `p⁻¹(x) → p⁻¹(y)` which is
`(Tf)ᵏ` under `p⁻¹(x) ≅ (T_xX)ᵏ`. -/
def whitneyFiberMap (hf : P.IsScSmoothMap Q f) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    whitneyFiber k x →ₗ[ℝ] whitneyFiber k y :=
  (whitneyFiberLinearEquiv y).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i => (tangentMapCLM hf hxy : P.tangentFiber x →ₗ[ℝ] Q.tangentFiber y) ∘ₗ
      LinearMap.proj i) ∘ₗ (whitneyFiberLinearEquiv x).toLinearMap

/-- `⊕ₖ Tf` on the fibre is the restriction of `⊕ₖ Tf`. -/
theorem coe_whitneyFiberMap_apply (hf : P.IsScSmoothMap Q f)
    (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) (v : whitneyFiber k x) :
    (whitneyFiberMap hf hxy v : Q.WhitneySum k) = whitneyMapOf hf v.1 := by
  have hv : whitneyProj v.1 = x := v.2
  refine whitneySum_ext (level_ext ?_) fun i => ?_
  · change Q.levelVal 1 y = f (P.levelVal 1 (whitneyProj v.1))
    rw [hv, hxy]
  · change ((tangentMapCLM hf hxy (whitneyFiberEquiv x v i) : Q.TangentSpace)) = _
    rw [tangentMapCLM_apply, whitneyVec_whitneyMapOf]
    rfl

/-- **`⊕ₖ Tf` of a local sc-diffeomorphism is a linear isomorphism on the fibres**: with
`IsLocalScDiffeo.whitneyMapOf`, `⊕ₖ Tf` is a local bundle isomorphism covering `f¹`. -/
theorem IsLocalScDiffeo.bijective_whitneyFiberMap (hf : P.IsLocalScDiffeo Q f)
    (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    Bijective (whitneyFiberMap (k := k) hf.isScSmoothMap hxy) := by
  have hT : Bijective (tangentMapCLM hf.isScSmoothMap hxy) := by
    have hb := hf.bijOn_tangentFiber x y hxy
    refine ⟨fun a b hab => Subtype.ext (hb.injOn a.2 b.2 ?_), fun β => ?_⟩
    · have h := congrArg Subtype.val hab
      rwa [tangentMapCLM_apply, tangentMapCLM_apply] at h
    · obtain ⟨a, ha, hab⟩ := hb.surjOn β.2
      exact ⟨⟨a, ha⟩, Subtype.ext ((tangentMapCLM_apply _ _ _).trans hab)⟩
  have hpi : Bijective fun (α : Fin k → P.tangentFiber x) i =>
      tangentMapCLM hf.isScSmoothMap hxy (α i) :=
    ⟨fun a b hab => funext fun i => hT.1 (congrFun hab i), fun β =>
      ⟨fun i => (hT.2 (β i)).choose, funext fun i => (hT.2 (β i)).choose_spec⟩⟩
  exact (whitneyFiberLinearEquiv y).symm.bijective.comp
    (hpi.comp (whitneyFiberLinearEquiv x).bijective)

end Fibre

end MPolyfold

end Polyfold
