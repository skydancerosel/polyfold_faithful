import Polyfold.Chapter4.ScFormsWedge2021
import Polyfold.Chapter4.ScFormsSquare2021
import Polyfold.Chapter4.ScFormsLower2021
import Polyfold.Chapter7.TangentMorphismLinear
import Polyfold.Chapter7.Zhou
import Polyfold.Chapter8.TangentEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2,
pp. 372–373: **Definition 8.2.1** (2017: Definition 8.2), the directed system and the direct
limit `Ω*_{ep,∞}(X)`, the exterior derivative `d[ω] = [dω]` with `d ∘ d = 0`, and
**Definition 8.2.2** (2017: Definition 8.3), the sc-de Rham complex of an ep-groupoid
(gap G.74).  Numbers and pages are the 2021 text's.

# Sc-differential forms on ep-groupoids

## The text, paraphrased

(Definition 8.2.1) An sc-differential `k`-form on the ep-groupoid `(X, 𝐗)` is an
sc-differential `k`-form `ω` on the object M-polyfold `X` (§4.4) such that
`(Tφ)^*ω_y = ω_x` for every morphism `φ : x → y` in `𝐗₁`, with `Tφ : T_xX → T_yX` the tangent
of `φ` (Definition 7.1.4).  They form the vector space `Ωᵏ_ep(X)`.  A form on `Xⁱ` is a form on
`Xⁱ⁺¹`; `Ω*_{ep,∞}(X)` is the direct limit of the directed system `Ω*_ep(Xⁱ) → Ω*_ep(Xᵏ)`,
`i ≤ k`, of the pull-backs by the inclusions.  Two forms `ω_i`, `ω_k` represent the same element
iff their pull-backs to some `Xˡ`, `l ≥ i, k`, agree.  `d[ω] := [dω]`, with `dω` the exterior
derivative on the object M-polyfold; `dω` is compatible with the morphisms (`f^*dω = df^*ω = dω`
for `f = t ∘ (s|𝐔(φ₀))⁻¹`), and `d ∘ d = 0`.  (Definition 8.2.2) `(Ω*_{ep,∞}(X), d)` is the
sc-de Rham complex of the ep-groupoid `X`.

## What is formalized

Namespace `Polyfold.EpGroupoid` (an ep-groupoid `X`, unbundled):
* `IsMorCompatible X k ω`: **the condition `(Tφ)^*ω_y = ω_x`** of Definition 8.2.1, for every
  `φ ∈ 𝐗₁` and `x, y ∈ X¹` over `s(φ)`, `t(φ)`, with `Tφ` the bounded linear isomorphism
  `tangentMorCLE` of Chapter 7.
* **`epForms X k : Submodule ℝ _`, the vector space `Ωᵏ_ep(X)`** (Definition 8.2.1): the
  families `ω` with `ω ∈ Ωᵏ(X)` (Part I's `MPolyfold.scForms`, Definition 4.4.1) and
  `IsMorCompatible X k ω`; `epForms_le_scForms`.
* `isMorCompatible_iff_formPullback`: `ω` is compatible with the morphisms iff
  **`s^*ω = t^*ω`** on the morphism M-polyfold `𝐗` (pull-backs by the sc-smooth maps
  `s, t : 𝐗 → X`, Part I's `formPullback`).  All closure properties follow from this form.
* `formLower_mem_epForms` (**a form on `X` is a form on `X¹`**), `extD_mem_epForms`
  (**`dω` is compatible with the morphisms**: `Ωᵏ_ep(X) → Ωᵏ⁺¹_ep(X¹)`),
  `formWedge_mem_epForms`, `constForm_mem_epForms` (witness: the constant `0`-forms).
* `formPullback_mem_epForms`: for an sc-smooth functor `F : X → Y`, `F^*` maps `Ωᵏ_ep(Y)` to
  `Ωᵏ_ep(X)`; `formPullback_eq_of_natTrans`: naturally equivalent functors (Definition 8.1.13)
  have the same pull-back on `Ωᵏ_ep`.

Namespace `Polyfold.EP` (a bundled ep-groupoid `A`, with the index lifts `A.lift i = Xⁱ`):
* `epForms A k i = Ωᵏ_ep(Xⁱ)`, `epFormsStep`, `epFormsMap` (the directed system,
  `directedSystem_epForms`), **`epFormsInfty A k = Ωᵏ_{ep,∞}(X)`** (Mathlib's
  `Module.DirectLimit`), `epFormsInftyOf` (the class `[ω]`), `epFormsInftyOf_epFormsMap`,
  `exists_epFormsInftyOf_eq` (every class has a representative on some `Xⁱ`) and
  **`epFormsInftyOf_eq_iff`** (two forms on `Xⁱ`, `Xʲ` represent the same class iff their
  pull-backs to some `Xˡ`, `l ≥ i, j`, agree).
* `epFormsD : Ωᵏ_ep(Xⁱ) → Ωᵏ⁺¹_ep(Xⁱ⁺¹)`, **`epFormsInftyD : Ωᵏ_{ep,∞}(X) → Ωᵏ⁺¹_{ep,∞}(X)`**
  with `epFormsInftyD_of` (`d[ω] = [dω]`) and **`epFormsInftyD_comp_epFormsInftyD`**
  (`d ∘ d = 0`).
* **Definition 8.2.2**: `epFormsInftyGraded A = Ω*_{ep,∞}(X) = ⊕ₖ Ωᵏ_{ep,∞}(X)`,
  `epFormsInftyGradedD` with `epFormsInftyGradedD_comp_self`; `epDeRham A k`, its cohomology
  `ker d / im d` (the same as a cochain complex of real vector spaces: `epDeRhamComplex`, in
  `EpFormsObj.lean`).
* `epFormsToForms`: the inclusion `Ωᵏ_ep(Xⁱ) → Ωᵏ(Xⁱ)` into the forms of the object M-polyfold
  of `Xⁱ`, commuting with the steps and with `d`.

## The reading

* "An sc-smooth map `⊕ₖ TX → ℝ`, linear in each argument and skew-symmetric" is Part I's
  Definition 4.4.1 (`MPolyfold.scForms`), as the text says ("already introduced in Section 4.4").
* `X^i` is Chapter 7's index lift (`EP.lift`), an ep-groupoid by Proposition 7.3.9; `Ωᵏ_ep(Xⁱ)`
  is Definition 8.2.1 for this ep-groupoid, so the compatibility on level `i` is with the
  morphisms of `(Xⁱ)` on level `1`, i.e. of `𝐗_{i+1}`.
* The text proves that `dω` is compatible with the morphisms through the local
  sc-diffeomorphisms `f = t ∘ (s|𝐔(φ₀))⁻¹` and `f^* ∘ d = d ∘ f^*`.  Here the same naturality of
  `d` (Part I's `extD_formPullback`) is applied to the global sc-smooth maps `s, t : 𝐗 → X`:
  `s^*dω = d s^*ω = d t^*ω = t^*dω`.
* The text writes `T_yY` for `T_yX` in Definition 8.2.1 (a reading point).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u v

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  {k l : ℕ}

/-! ### Definition 8.2.1 -/

/-- **2021 Definition 8.2.1 (2017: 8.2), the compatibility with morphisms**:
`(Tφ)^*ω_y = ω_x` for every morphism `φ : x → y` in `𝐗₁`, with `Tφ : T_xX → T_yX` the bounded
linear isomorphism of Definition 7.1.4 (`tangentMorCLE`). -/
def IsMorCompatible (k : ℕ)
    (ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) : Prop :=
  ∀ (φ : Mor) (hφ : φ ∈ X.PMor.levelSet 1) (x y : X.PObj.Level 1)
    (hx : X.PObj.levelVal 1 x = X.src φ) (hy : X.PObj.levelVal 1 y = X.tgt φ),
    (ω y).compLinearMap (X.tangentMorCLE hφ hx hy).toLinearEquiv.toLinearMap = ω x

/-- The compatibility with morphisms, evaluated: `ω_y(Tφ a₁, …, Tφ a_k) = ω_x(a₁, …, a_k)`. -/
theorem IsMorCompatible.apply {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : X.IsMorCompatible k ω) {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {x y : X.PObj.Level 1}
    (hx : X.PObj.levelVal 1 x = X.src φ) (hy : X.PObj.levelVal 1 y = X.tgt φ)
    (a : Fin k → X.PObj.tangentFiber x) :
    ω y (fun i => X.tangentMorCLE hφ hx hy (a i)) = ω x a :=
  congrArg (fun η : X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ => η a) (h φ hφ x y hx hy)

/-- **Compatibility with morphisms is `s^*ω = t^*ω`** on the morphism M-polyfold `𝐗`: since
`Tφ ∘ Ts = Tt` on `T_φ𝐗` (Remark 8.1.10) and `Ts : T_φ𝐗 → T_{s(φ)}X` is onto. -/
theorem isMorCompatible_iff_formPullback
    {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} :
    X.IsMorCompatible k ω ↔
      formPullback X.isScSmoothMap_src ω = formPullback X.isScSmoothMap_tgt ω := by
  constructor
  · intro h
    funext φ₁
    ext α
    have hx : X.PObj.levelVal 1 (liftLevelOneMap X.isScSmoothMap_src φ₁) =
        X.src (X.PMor.levelVal 1 φ₁) := MPolyfold.levelVal_levelMk _ _ _
    have hy : X.PObj.levelVal 1 (liftLevelOneMap X.isScSmoothMap_tgt φ₁) =
        X.tgt (X.PMor.levelVal 1 φ₁) := MPolyfold.levelVal_levelMk _ _ _
    have hc := h.apply X (X.PMor.levelVal_mem φ₁) hx hy
      (fun i => tangentFiberMap X.isScSmoothMap_src φ₁ (α i))
    rw [formPullback_apply, formPullback_apply, ← hc]
    congr 1
    funext i
    apply Subtype.ext
    refine (X.tangentMorCLE_apply (X.PMor.levelVal_mem φ₁) hx hy _).trans ?_
    rw [coe_tangentFiberMap_apply, coe_tangentFiberMap_apply]
    have h1 := X.tangentMor_tSrc (α i).1
    rw [tBase, show X.PMor.tangentProj (α i).1 = φ₁ from (α i).2] at h1
    exact h1
  · intro h φ hφ x y hx hy
    ext a
    have hex : ∀ i, ∃ v, X.PMor.tangentProj v = X.PMor.levelMk 1 φ hφ ∧ X.tSrc v = (a i).1 :=
      fun i => X.exists_tSrc_eq (φ := X.PMor.levelMk 1 φ hφ) (by
        rw [show X.PObj.tangentProj (a i).1 = x from (a i).2, hx, MPolyfold.levelVal_levelMk])
    choose v hv hva using hex
    let α : Fin k → X.PMor.tangentFiber (X.PMor.levelMk 1 φ hφ) := fun i => ⟨v i, hv i⟩
    have h1 := formPullback_eq X.isScSmoothMap_src ω α (y := x)
      (by rw [MPolyfold.levelVal_levelMk, hx]) a (fun i => hva i)
    have h2 := formPullback_eq X.isScSmoothMap_tgt ω α (y := y)
      (by rw [MPolyfold.levelVal_levelMk, hy]) (fun i => X.tangentMorCLE hφ hx hy (a i))
      (fun i => by
        rw [tangentMorCLE_apply, ← hva i]
        have h3 := X.tangentMor_tSrc (v i)
        rw [tBase, hv i, MPolyfold.levelVal_levelMk] at h3
        exact h3.symm)
    rw [h] at h1
    exact h2.symm.trans h1

/-- **2021 Definition 8.2.1 (2017: 8.2): the vector space `Ωᵏ_ep(X)`** of sc-differential
`k`-forms on the ep-groupoid `X`: the sc-differential `k`-forms on the object M-polyfold
(Definition 4.4.1) compatible with the morphisms. -/
def epForms (k : ℕ) :
    Submodule ℝ (∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) where
  carrier := {ω | ω ∈ X.PObj.scForms k ∧ X.IsMorCompatible k ω}
  add_mem' {ω τ} hω hτ := ⟨(X.PObj.scForms k).add_mem hω.1 hτ.1,
    X.isMorCompatible_iff_formPullback.2 (by
      rw [formPullback_add, formPullback_add, X.isMorCompatible_iff_formPullback.1 hω.2,
        X.isMorCompatible_iff_formPullback.1 hτ.2])⟩
  zero_mem' := ⟨(X.PObj.scForms k).zero_mem, X.isMorCompatible_iff_formPullback.2 rfl⟩
  smul_mem' c {ω} hω := ⟨(X.PObj.scForms k).smul_mem c hω.1,
    X.isMorCompatible_iff_formPullback.2 (by
      rw [formPullback_smul, formPullback_smul, X.isMorCompatible_iff_formPullback.1 hω.2])⟩

lemma mem_epForms {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} :
    ω ∈ X.epForms k ↔ ω ∈ X.PObj.scForms k ∧ X.IsMorCompatible k ω := Iff.rfl

lemma mem_epForms_iff_formPullback
    {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} :
    ω ∈ X.epForms k ↔ ω ∈ X.PObj.scForms k ∧
      formPullback X.isScSmoothMap_src ω = formPullback X.isScSmoothMap_tgt ω :=
  and_congr_right fun _ => X.isMorCompatible_iff_formPullback

/-- `Ωᵏ_ep(X) ⊆ Ωᵏ(X)`. -/
theorem epForms_le_scForms (k : ℕ) : X.epForms k ≤ X.PObj.scForms k := fun _ h => h.1

/-- **Witness**: the constant `0`-forms are sc-differential forms on the ep-groupoid. -/
theorem constForm_mem_epForms (c : ℝ) : X.PObj.constForm c ∈ X.epForms 0 :=
  ⟨constForm_mem_scForms c, fun _ _ _ _ _ _ => by ext a; rfl⟩

/-! ### Forms on `X` are forms on `X¹`; `d`; the wedge product -/

/-- **2021 p. 372: a form on `X` is also a form on `X¹`** (the step of the directed system):
the pull-back by the inclusion `X¹ → X` maps `Ωᵏ_ep(X)` to `Ωᵏ_ep(X¹)`. -/
theorem formLower_mem_epForms {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ X.epForms k) : formLower ω ∈ X.liftOne.epForms k := by
  refine ⟨formLower_mem_scForms hω.1, X.liftOne.isMorCompatible_iff_formPullback.2 ?_⟩
  have hs := formLower_formPullback X.isScSmoothMap_src (f₁ := X.liftOne.src) (fun _ => rfl)
    X.liftOne.isScSmoothMap_src ω
  have ht := formLower_formPullback X.isScSmoothMap_tgt (f₁ := X.liftOne.tgt) (fun _ => rfl)
    X.liftOne.isScSmoothMap_tgt ω
  exact hs.trans ((congrArg formLower (X.isMorCompatible_iff_formPullback.1 hω.2)).trans ht.symm)

/-- **2021 p. 373: `dω` is compatible with the morphisms**: the exterior derivative of the
object M-polyfold maps `Ωᵏ_ep(X)` to `Ωᵏ⁺¹_ep(X¹)`. -/
theorem extD_mem_epForms {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ X.epForms k) : extD ω ∈ X.liftOne.epForms (k + 1) := by
  refine ⟨extD_mem_scForms hω.1, X.liftOne.isMorCompatible_iff_formPullback.2 ?_⟩
  have hs := extD_formPullback X.isScSmoothMap_src hω.1
  have ht := extD_formPullback X.isScSmoothMap_tgt hω.1
  have hs' := formPullback_congr (isScSmoothMap_liftLevelOneMap X.isScSmoothMap_src)
    X.liftOne.isScSmoothMap_src (fun _ => rfl) (extD ω)
  have ht' := formPullback_congr (isScSmoothMap_liftLevelOneMap X.isScSmoothMap_tgt)
    X.liftOne.isScSmoothMap_tgt (fun _ => rfl) (extD ω)
  exact hs'.symm.trans (hs.symm.trans
    ((congrArg extD (X.isMorCompatible_iff_formPullback.1 hω.2)).trans (ht.trans ht')))

/-- The wedge product of sc-differential forms on the ep-groupoid is one. -/
theorem formWedge_mem_epForms {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    {τ : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ}
    (hω : ω ∈ X.epForms k) (hτ : τ ∈ X.epForms l) : formWedge ω τ ∈ X.epForms (k + l) :=
  ⟨formWedge_mem_scForms hω.1 hτ.1, X.isMorCompatible_iff_formPullback.2 (by
    rw [formPullback_formWedge, formPullback_formWedge,
      X.isMorCompatible_iff_formPullback.1 hω.2, X.isMorCompatible_iff_formPullback.1 hτ.2])⟩

/-! ### Pull-back by sc-smooth functors -/

section Functor

variable {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X}
  {Y : EpGroupoid Obj' Mor'}

/-- **The pull-back of a form on an ep-groupoid by an sc-smooth functor** `F : X → Y` is a form
on the ep-groupoid `X`: `F^* : Ωᵏ_ep(Y) → Ωᵏ_ep(X)`, `F^*ω = ω ∘ ⊕ₖ TF` on objects. -/
theorem formPullback_mem_epForms (F : EpFunctor X Y)
    {ω : ∀ y : Y.PObj.Level 1, Y.PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ Y.epForms k) :
    formPullback F.isScSmoothMap_obj ω ∈ X.epForms k := by
  refine ⟨formPullback_mem_scForms _ hω.1, X.isMorCompatible_iff_formPullback.2 ?_⟩
  have hs : formPullback X.isScSmoothMap_src (formPullback F.isScSmoothMap_obj ω) =
      formPullback F.isScSmoothMap_mor (formPullback Y.isScSmoothMap_src ω) :=
    (formPullback_comp F.isScSmoothMap_obj X.isScSmoothMap_src ω).symm.trans
      ((formPullback_congr _ (Y.isScSmoothMap_src.comp F.isScSmoothMap_mor)
        (fun φ => (F.src_mor φ).symm) ω).trans
        (formPullback_comp Y.isScSmoothMap_src F.isScSmoothMap_mor ω))
  have ht : formPullback X.isScSmoothMap_tgt (formPullback F.isScSmoothMap_obj ω) =
      formPullback F.isScSmoothMap_mor (formPullback Y.isScSmoothMap_tgt ω) :=
    (formPullback_comp F.isScSmoothMap_obj X.isScSmoothMap_tgt ω).symm.trans
      ((formPullback_congr _ (Y.isScSmoothMap_tgt.comp F.isScSmoothMap_mor)
        (fun φ => (F.tgt_mor φ).symm) ω).trans
        (formPullback_comp Y.isScSmoothMap_tgt F.isScSmoothMap_mor ω))
  rw [hs, ht, Y.isMorCompatible_iff_formPullback.1 hω.2]

/-- **Naturally equivalent functors (Definition 8.1.13) induce the same pull-back** of forms on
ep-groupoids: `F^*ω = τ^*s^*ω = τ^*t^*ω = G^*ω` for a natural transformation `τ : F → G`. -/
theorem formPullback_eq_of_natTrans {F G : EpFunctor X Y} (τ : EpNatTrans F G)
    {ω : ∀ y : Y.PObj.Level 1, Y.PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ Y.epForms k) :
    formPullback F.isScSmoothMap_obj ω = formPullback G.isScSmoothMap_obj ω := by
  have hF := (formPullback_congr F.isScSmoothMap_obj
    (Y.isScSmoothMap_src.comp τ.isScSmoothMap_app) (fun x => (τ.src_app x).symm) ω).trans
    (formPullback_comp Y.isScSmoothMap_src τ.isScSmoothMap_app ω)
  have hG := (formPullback_congr G.isScSmoothMap_obj
    (Y.isScSmoothMap_tgt.comp τ.isScSmoothMap_app) (fun x => (τ.tgt_app x).symm) ω).trans
    (formPullback_comp Y.isScSmoothMap_tgt τ.isScSmoothMap_app ω)
  rw [hF, hG, Y.isMorCompatible_iff_formPullback.1 hω.2]

end Functor

end EpGroupoid

/-! ### The directed system and `Ω*_{ep,∞}(X)` -/

namespace EP

variable (A : EP.{u}) (k : ℕ)

/-- `Ωᵏ_ep(Xⁱ)`, the sc-differential `k`-forms on the index lift `Xⁱ` of the ep-groupoid
(2021 p. 372). -/
abbrev epForms (i : ℕ) := (A.lift i).X.epForms k

/-- `Ωᵏ_ep(Xⁱ)` is an additive group (stated directly, as in Part I). -/
instance addCommGroup_epForms (j i : ℕ) : AddCommGroup (A.epForms j i) :=
  Submodule.addCommGroup _

/-- The pull-back `Ωᵏ_ep(Xⁱ) → Ωᵏ_ep(Xⁱ⁺¹)` along the inclusion `Xⁱ⁺¹ → Xⁱ` (2021 p. 372: a form
on `Xⁱ` is a form on `Xⁱ⁺¹`). -/
def epFormsStep (i : ℕ) : A.epForms k i →ₗ[ℝ] A.epForms k (i + 1) :=
  LinearMap.codRestrict (A.epForms k (i + 1))
    ((MPolyfold.formLowerₗ (A.lift i).X.PObj k).domRestrict (A.epForms k i))
    fun ω => (A.lift i).X.formLower_mem_epForms ω.2

lemma coe_epFormsStep (i : ℕ) (ω : A.epForms k i) :
    (A.epFormsStep k i ω).1 = formLower ω.1 := rfl

/-- **The directed system `ι_{i,j} : Ω*_ep(Xⁱ) → Ω*_ep(Xʲ)`, `i ≤ j`** (2021 p. 372). -/
def epFormsMap (i j : ℕ) (h : i ≤ j) : A.epForms k i →ₗ[ℝ] A.epForms k j :=
  Nat.leRecOn (C := fun j => A.epForms k i →ₗ[ℝ] A.epForms k j) h
    (fun {n} g => (A.epFormsStep k n).comp g) LinearMap.id

lemma epFormsMap_self (i : ℕ) : A.epFormsMap k i i le_rfl = LinearMap.id :=
  Nat.leRecOn_self _

lemma epFormsMap_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) :
    A.epFormsMap k i (j + 1) h' = (A.epFormsStep k j).comp (A.epFormsMap k i j h) :=
  Nat.leRecOn_succ h _

lemma epFormsMap_comp {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    (A.epFormsMap k j l hjl).comp (A.epFormsMap k i j hij) =
      A.epFormsMap k i l (hij.trans hjl) := by
  induction l, hjl using Nat.le_induction with
  | base => rw [epFormsMap_self]; rfl
  | succ l hjl ih =>
    rw [epFormsMap_succ A k hjl, epFormsMap_succ A k (hij.trans hjl), LinearMap.comp_assoc, ih]

instance directedSystem_epForms :
    DirectedSystem (fun i => ↥(A.epForms k i)) fun i j h => ⇑(A.epFormsMap k i j h) where
  map_self i ω := by rw [epFormsMap_self]; rfl
  map_map _ _ _ hij hjk ω := LinearMap.congr_fun (A.epFormsMap_comp k hij hjk) ω

/-- **2021 p. 372 (Definition 8.2.1 ff.): `Ωᵏ_{ep,∞}(X)`**, the direct limit of the directed
system `Ωᵏ_ep(Xⁱ)`; a real vector space. -/
abbrev epFormsInfty : Type _ :=
  Module.DirectLimit (fun i => ↥(A.epForms k i)) (A.epFormsMap k)

/-- `Ωᵏ_{ep,∞}(X)` is an additive group (stated directly, as in Part I). -/
instance addCommGroup_epFormsInfty (j : ℕ) : AddCommGroup (A.epFormsInfty j) :=
  Module.DirectLimit.addCommGroup _ _

/-- The class `[ω] ∈ Ωᵏ_{ep,∞}(X)` of a form `ω ∈ Ωᵏ_ep(Xⁱ)`. -/
abbrev epFormsInftyOf (i : ℕ) : A.epForms k i →ₗ[ℝ] A.epFormsInfty k :=
  Module.DirectLimit.of ℝ ℕ (fun i => ↥(A.epForms k i)) (A.epFormsMap k) i

/-- A form and its pull-back to `Xʲ` have the same class. -/
theorem epFormsInftyOf_epFormsMap {i j : ℕ} (h : i ≤ j) (ω : A.epForms k i) :
    A.epFormsInftyOf k j (A.epFormsMap k i j h ω) = A.epFormsInftyOf k i ω :=
  Module.DirectLimit.of_f

/-- **2021 p. 372: every element of `Ωᵏ_{ep,∞}(X)` is represented by a form on some `Xⁱ`.** -/
theorem exists_epFormsInftyOf_eq (a : A.epFormsInfty k) :
    ∃ (i : ℕ) (ω : A.epForms k i), A.epFormsInftyOf k i ω = a :=
  Module.DirectLimit.exists_of a

/-- **2021 pp. 372–373: `ω_i` and `ω_j` represent the same element of `Ωᵏ_{ep,∞}(X)` iff their
pull-backs to some `Xˡ`, `l ≥ i, j`, agree.** -/
theorem epFormsInftyOf_eq_iff {i j : ℕ} (ω : A.epForms k i) (τ : A.epForms k j) :
    A.epFormsInftyOf k i ω = A.epFormsInftyOf k j τ ↔
      ∃ (l : ℕ) (hi : i ≤ l) (hj : j ≤ l), A.epFormsMap k i l hi ω = A.epFormsMap k j l hj τ := by
  constructor
  · intro h
    have h' : A.epFormsInftyOf k (max i j) (A.epFormsMap k i _ (le_max_left i j) ω) =
        A.epFormsInftyOf k (max i j) (A.epFormsMap k j _ (le_max_right i j) τ) := by
      rw [epFormsInftyOf_epFormsMap, epFormsInftyOf_epFormsMap, h]
    obtain ⟨l, hl, e⟩ := Module.DirectLimit.exists_eq_of_of_eq h'
    refine ⟨l, (le_max_left i j).trans hl, (le_max_right i j).trans hl, ?_⟩
    have e1 := LinearMap.congr_fun (A.epFormsMap_comp k (le_max_left i j) hl) ω
    have e2 := LinearMap.congr_fun (A.epFormsMap_comp k (le_max_right i j) hl) τ
    exact e1.symm.trans (e.trans e2)
  · rintro ⟨l, hi, hj, e⟩
    rw [← A.epFormsInftyOf_epFormsMap k hi ω, ← A.epFormsInftyOf_epFormsMap k hj τ, e]

/-! ### The exterior derivative on `Ω*_{ep,∞}(X)` -/

/-- `d : Ωᵏ_ep(Xⁱ) → Ωᵏ⁺¹_ep(Xⁱ⁺¹)`, the exterior derivative of the object M-polyfold of `Xⁱ`
(2021 p. 373). -/
def epFormsD (i : ℕ) : A.epForms k i →ₗ[ℝ] A.epForms (k + 1) (i + 1) where
  toFun ω := ⟨extD ω.1, (A.lift i).X.extD_mem_epForms ω.2⟩
  map_add' ω τ := Subtype.ext (extD_add ω.2.1 τ.2.1)
  map_smul' c ω := Subtype.ext (extD_smul c ω.2.1)

lemma coe_epFormsD (i : ℕ) (ω : A.epForms k i) : (A.epFormsD k i ω).1 = extD ω.1 := rfl

/-- `d` commutes with the steps of the directed system. -/
theorem epFormsD_epFormsStep (i : ℕ) (ω : A.epForms k i) :
    A.epFormsD k (i + 1) (A.epFormsStep k i ω) =
      A.epFormsStep (k + 1) (i + 1) (A.epFormsD k i ω) :=
  Subtype.ext (MPolyfold.extD_formLower ω.2.1)

/-- `d` commutes with the maps of the directed system. -/
theorem epFormsD_epFormsMap {i j : ℕ} (h : i ≤ j) (ω : A.epForms k i) :
    A.epFormsD k j (A.epFormsMap k i j h ω) =
      A.epFormsMap (k + 1) (i + 1) (j + 1) (Nat.succ_le_succ h) (A.epFormsD k i ω) := by
  induction j, h using Nat.le_induction with
  | base => rw [epFormsMap_self, epFormsMap_self]; rfl
  | succ j hij ih =>
    rw [epFormsMap_succ A k hij, LinearMap.comp_apply, epFormsD_epFormsStep, ih,
      epFormsMap_succ A (k + 1) (Nat.succ_le_succ hij), LinearMap.comp_apply]

/-- **2021 p. 373: the exterior derivative `d[ω] := [dω]` on `Ωᵏ_{ep,∞}(X)`.** -/
def epFormsInftyD : A.epFormsInfty k →ₗ[ℝ] A.epFormsInfty (k + 1) :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.epForms k i)) (A.epFormsMap k)
    (fun i => (A.epFormsInftyOf (k + 1) (i + 1)).comp (A.epFormsD k i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [epFormsD_epFormsMap, epFormsInftyOf_epFormsMap]

/-- `d[ω] = [dω]`. -/
theorem epFormsInftyD_of (i : ℕ) (ω : A.epForms k i) :
    A.epFormsInftyD k (A.epFormsInftyOf k i ω) =
      A.epFormsInftyOf (k + 1) (i + 1) (A.epFormsD k i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-- **2021 p. 373 (and Theorem 11.2.1 (1)): `d ∘ d = 0` on `Ω*_{ep,∞}(X)`.** -/
theorem epFormsInftyD_comp_epFormsInftyD :
    (A.epFormsInftyD (k + 1)).comp (A.epFormsInftyD k) = 0 := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  have h : A.epFormsD (k + 1) (i + 1) (A.epFormsD k i ω) = 0 :=
    Subtype.ext (MPolyfold.extD_extD ω.2.1)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [epFormsInftyD_of, epFormsInftyD_of, h, map_zero]

theorem epFormsInftyD_epFormsInftyD (a : A.epFormsInfty k) :
    A.epFormsInftyD (k + 1) (A.epFormsInftyD k a) = 0 :=
  LinearMap.congr_fun (A.epFormsInftyD_comp_epFormsInftyD k) a

/-! ### Definition 8.2.2: the sc-de Rham complex -/

/-- `Ω*_{ep,∞}(X) = ⊕ₖ Ωᵏ_{ep,∞}(X)`. -/
abbrev epFormsInftyGraded : Type _ := DirectSum ℕ fun k => A.epFormsInfty k

/-- `d` on `Ω*_{ep,∞}(X)`, of degree `+1`. -/
def epFormsInftyGradedD : A.epFormsInftyGraded →ₗ[ℝ] A.epFormsInftyGraded :=
  DirectSum.toModule ℝ ℕ _ fun j =>
    (DirectSum.lof ℝ ℕ (fun j => A.epFormsInfty j) (j + 1)).comp (A.epFormsInftyD j)

theorem epFormsInftyGradedD_lof (j : ℕ) (ω : A.epFormsInfty j) :
    A.epFormsInftyGradedD (DirectSum.lof ℝ ℕ (fun j => A.epFormsInfty j) j ω) =
      DirectSum.lof ℝ ℕ (fun j => A.epFormsInfty j) (j + 1) (A.epFormsInftyD j ω) :=
  DirectSum.toModule_lof ℝ _ _

/-- **2021 Definition 8.2.2 (2017: 8.3): the sc-de Rham complex `(Ω*_{ep,∞}(X), d)` of the
ep-groupoid `X`**: `d ∘ d = 0` on the graded vector space `Ω*_{ep,∞}(X)`. -/
theorem epFormsInftyGradedD_comp_self :
    A.epFormsInftyGradedD.comp A.epFormsInftyGradedD = 0 := by
  refine DirectSum.linearMap_ext ℝ fun j => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [epFormsInftyGradedD_lof, epFormsInftyGradedD_lof, A.epFormsInftyD_epFormsInftyD j ω,
    map_zero]

/-- `im d` in degree `k` (`0` in degree `0`). -/
def epFormsInftyDRange : ∀ j : ℕ, Submodule ℝ (A.epFormsInfty j)
  | 0 => ⊥
  | j + 1 => LinearMap.range (A.epFormsInftyD j)

/-- `im d ⊆ ker d`. -/
theorem epFormsInftyDRange_le_ker :
    ∀ j : ℕ, A.epFormsInftyDRange j ≤ LinearMap.ker (A.epFormsInftyD j)
  | 0 => bot_le
  | j + 1 => by
    rintro _ ⟨ω, rfl⟩
    exact A.epFormsInftyD_epFormsInftyD j ω

/-- The cohomology `ker d / im d` of the sc-de Rham complex of the ep-groupoid in degree `k`. -/
abbrev epDeRham : Type _ :=
  LinearMap.ker (A.epFormsInftyD k) ⧸
    (A.epFormsInftyDRange k).comap (LinearMap.ker (A.epFormsInftyD k)).subtype

/-! ### The forms of the object M-polyfold -/

/-- The inclusion `Ωᵏ_ep(Xⁱ) → Ωᵏ(Xⁱ)` into the sc-differential forms of the object M-polyfold
of `Xⁱ`. -/
def epFormsToForms (i : ℕ) : A.epForms k i →ₗ[ℝ] (A.lift i).X.PObj.scForms k :=
  Submodule.inclusion ((A.lift i).X.epForms_le_scForms k)

theorem epFormsToForms_injective (i : ℕ) : Injective (A.epFormsToForms k i) :=
  Submodule.inclusion_injective _

lemma coe_epFormsToForms (i : ℕ) (ω : A.epForms k i) : (A.epFormsToForms k i ω).1 = ω.1 := rfl

end EP

end Polyfold
