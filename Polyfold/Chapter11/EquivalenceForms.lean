import Polyfold.Chapter11.FormDescent
import Polyfold.Chapter8.EpForms
import Polyfold.Chapter10.WeakFibredProductTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §11.2,
pp. 527–529: **Lemma 11.2.2** (2017: Lemma 11.1), **Definition 11.2.3** (2017: Definition 11.2)
and **Lemma 11.2.4 (3)** (2017: Lemma 11.2) on one level (gap G.129).  Numbers and pages are the
2021 text's.

# The push-forward of sc-differential forms along an equivalence

## The text, paraphrased

(Lemma 11.2.2) For an equivalence `F : X → Y`, a form `ω` on `X`, `y ∈ Y₁`, morphisms
`ψ : F(x) → y`, `ψ' : F(x') → y` and `l_j ∈ T_xX`, `l'_j ∈ T_{x'}X` with
`Tψ(TF(x) l_j) = Tψ'(TF(x') l'_j)`: `ω_x(l₁, …, l_k) = ω_{x'}(l'₁, …, l'_k)`.
(Definition 11.2.3) `(F_*ω)_y(h₁, …, h_k) = ω_x(l₁, …, l_k)` for `h_j = Tψ(TF(x) l_j)`; it is
sc-smooth, being locally the pull-back by the inverse of the local sc-diffeomorphism `ψ̂ ∘ F`
(11.4).  (Lemma 11.2.4 (3)) `F_* F^*ω = ω` and `F^* F_*τ = τ`.

## What is formalized

For ep-groupoids `X`, `Y` and an sc-smooth functor `F : X → Y`
(`ω` a form on `X` means `ω ∈ Ωᵏ_ep(X) = EpGroupoid.epForms X k`):
* `EpFunctor.eq_of_tangentMap_eq`: for `F` full and a local sc-diffeomorphism on objects, a
  form `η` of the ep-groupoid `X` takes the same values on vectors over `x`, `x'` with
  `F(x) = F(x')` and the same images under `TF` (Lemma 11.2.2 for `ψ = ψ' = 1`).
* `EpFunctor.exists_epForms_formPullback_eq_of_surjective`: for `F` full, a local
  sc-diffeomorphism and surjective on objects, every `η ∈ Ωᵏ_ep(X)` is `F^*τ` for a
  `τ ∈ Ωᵏ_ep(Y)`.
* **`EpFunctor.IsEquivalence.bijective_formPullback`: for an equivalence `F`,
  `F^* : Ωᵏ_ep(Y) → Ωᵏ_ep(X)` is a bijection**; `formPullbackEquiv` is this linear isomorphism
  and **`EpFunctor.IsEquivalence.formPush = F_* : Ωᵏ_ep(X) → Ωᵏ_ep(Y)`** its inverse
  (Definition 11.2.3), with `formPullback_formPush` (`F^* F_*ω = ω`) and
  `formPush_formPullback` (`F_* F^*τ = τ`): Lemma 11.2.4 (3).
* **`definition_11_2_3`: `(F_*ω)_y(Tψ(TF(x) l₁), …, Tψ(TF(x) l_k)) = ω_x(l₁, …, l_k)`** for
  every `x ∈ X₁`, `ψ : F(x) → y` in `𝐘₁` and `l_j ∈ T_xX` — the text's defining formula; with
  the surjectivity `exists_lift_tangent` (every `h₁, …, h_k ∈ T_yY` are of this form) it
  determines `F_*ω`.
* **`lemma_11_2_2`**: the text's statement, for `ω ∈ Ωᵏ_ep(X)`.

## The reading

* The text defines `F_*ω` by the formula and then proves that it is well defined, sc-smooth and
  inverse to `F^*`.  Here `F_*` is defined as the inverse of the bijection `F^*`, and the
  text's formula is the theorem `definition_11_2_3`; the two definitions agree by that theorem
  and `exists_lift_tangent`.
* The bijectivity of `F^*` is proved through the weak fibred product `A = X ×_Y Y` of `F` and
  `1_Y` (Theorem 10.2.2): its objects are the triples `(x, ψ, y)`, `ψ : F(x) → y`, of the
  text's definition, `π_Y : A → Y` is an equivalence which is surjective on objects, and
  `F ∘ π_X ≃ π_Y`.  The form `F_*ω` is the descent of `π_X^*ω` along `π_Y`; sc-smoothness is
  the text's (11.4) (`MPolyfold.isScForm_of_formPullback`).

No hypothesis is added.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u v w

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {k : ℕ}

/-! ### Functoriality of the pull-back: `s^* F^* = F^* s^*` -/

theorem formPullback_src_comm (F : EpFunctor X Y)
    (ω : ∀ y : Y.PObj.Level 1, Y.PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback X.isScSmoothMap_src (formPullback F.isScSmoothMap_obj ω) =
      formPullback F.isScSmoothMap_mor (formPullback Y.isScSmoothMap_src ω) :=
  (formPullback_comp F.isScSmoothMap_obj X.isScSmoothMap_src ω).symm.trans
    ((formPullback_congr _ (Y.isScSmoothMap_src.comp F.isScSmoothMap_mor)
      (fun φ => (F.src_mor φ).symm) ω).trans
      (formPullback_comp Y.isScSmoothMap_src F.isScSmoothMap_mor ω))

theorem formPullback_tgt_comm (F : EpFunctor X Y)
    (ω : ∀ y : Y.PObj.Level 1, Y.PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback X.isScSmoothMap_tgt (formPullback F.isScSmoothMap_obj ω) =
      formPullback F.isScSmoothMap_mor (formPullback Y.isScSmoothMap_tgt ω) :=
  (formPullback_comp F.isScSmoothMap_obj X.isScSmoothMap_tgt ω).symm.trans
    ((formPullback_congr _ (Y.isScSmoothMap_tgt.comp F.isScSmoothMap_mor)
      (fun φ => (F.tgt_mor φ).symm) ω).trans
      (formPullback_comp Y.isScSmoothMap_tgt F.isScSmoothMap_mor ω))

/-- `(G ∘ F)^* = F^* ∘ G^*` on families, for sc-smooth functors. -/
theorem formPullback_comp_functor {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj'']
    [ParacompactSpace Obj''] [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
    {Z : EpGroupoid Obj'' Mor''} (G : EpFunctor Y Z) (F : EpFunctor X Y)
    (ω : ∀ z : Z.PObj.Level 1, Z.PObj.tangentFiber z [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback (G.comp F).isScSmoothMap_obj ω =
      formPullback F.isScSmoothMap_obj (formPullback G.isScSmoothMap_obj ω) :=
  formPullback_comp G.isScSmoothMap_obj F.isScSmoothMap_obj ω

/-! ### Lemma 11.2.2 for units -/

/-- A tangent vector of `𝐘` over a unit has `Tt = Ts`. -/
theorem _root_.Polyfold.EpGroupoid.tTgt_eq_tSrc_of_tBase_unit (Y : EpGroupoid Obj' Mor')
    {u : Y.PMor.TangentSpace} {y : Obj'} (hu : Y.tBase u = Y.unit y) : Y.tTgt u = Y.tSrc u := by
  have hb : Y.tBase u = Y.unit (Y.PObj.levelVal 1 (Y.PObj.tangentProj (Y.tSrc u))) := by
    rw [Y.levelVal_tangentProj_tSrc, hu, Y.src_unit]
  have h := Y.tUnit_eq hb rfl
  rw [← h, Y.tTgt_tUnit, Y.tSrc_tUnit]

/-- **Lemma 11.2.2 for `ψ = ψ' = 1`**: for a full functor `F` which is a local
sc-diffeomorphism on objects, a family `η` compatible with the morphisms of `X` takes the same
values on vectors over `x`, `x'` with `F(x) = F(x')` and the same images under `TF`. -/
theorem eq_of_tangentMap_eq (F : EpFunctor X Y) (hfull : F.toFunctor.Full)
    (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {η : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hη : X.IsMorCompatible k η) (x x' : X.PObj.Level 1)
    (hxx : F.obj (X.PObj.levelVal 1 x) = F.obj (X.PObj.levelVal 1 x'))
    (α : Fin k → X.PObj.tangentFiber x) (α' : Fin k → X.PObj.tangentFiber x')
    (h : ∀ i, MPolyfold.tangentMap F.isScSmoothMap_obj (α i).1 =
      MPolyfold.tangentMap F.isScSmoothMap_obj (α' i).1) : η x α = η x' α' := by
  obtain ⟨m, hms, hmt, hme⟩ := (F.full_iff.1 hfull) (X.PObj.levelVal 1 x) (X.PObj.levelVal 1 x')
    (Y.unit (F.obj (X.PObj.levelVal 1 x))) (Y.src_unit _) ((Y.tgt_unit _).trans hxx)
  have hm1 : m ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff m 1).1 (hms ▸ MPolyfold.levelVal_mem x)
  rw [← hη.apply X hm1 hms.symm hmt.symm α]
  congr 1
  funext i
  apply Subtype.ext
  rw [X.tangentMorCLE_apply]
  have hai : X.PObj.levelVal 1 (X.PObj.tangentProj (α i).1) = X.src m := by
    rw [show X.PObj.tangentProj (α i).1 = x from (α i).2, hms]
  obtain ⟨v, hvb, hvs⟩ := X.exists_tSrc_eq' hm1 hai
  have h1 : X.tangentMor m (α i).1 = X.tTgt v := by
    rw [← hvb, ← hvs]; exact X.tangentMor_tSrc v
  rw [h1]
  have hmem : X.tTgt v ∈ X.PObj.tangentFiber x' := by
    change X.PObj.tangentProj (X.tTgt v) = x'
    apply MPolyfold.level_ext
    rw [X.levelVal_tangentProj_tTgt, hvb, hmt]
  refine hF.injOn_tangentFiber x' hmem (α' i).2 ?_
  have hu : Y.tBase (MPolyfold.tangentMap F.isScSmoothMap_mor v) =
      Y.unit (F.obj (X.PObj.levelVal 1 x)) := by
    rw [Y.tBase_tangentMap]
    exact (congrArg F.mor hvb).trans hme
  have e1 : MPolyfold.tangentMap F.isScSmoothMap_obj (X.tTgt v) =
      Y.tTgt (MPolyfold.tangentMap F.isScSmoothMap_mor v) :=
    MPolyfold.tangentMap_tangentMap_comm F.isScSmoothMap_obj X.isScSmoothMap_tgt
      Y.isScSmoothMap_tgt F.isScSmoothMap_mor (funext fun φ => (F.tgt_mor φ).symm) v
  have e2 : MPolyfold.tangentMap F.isScSmoothMap_obj (X.tSrc v) =
      Y.tSrc (MPolyfold.tangentMap F.isScSmoothMap_mor v) :=
    MPolyfold.tangentMap_tangentMap_comm F.isScSmoothMap_obj X.isScSmoothMap_src
      Y.isScSmoothMap_src F.isScSmoothMap_mor (funext fun φ => (F.src_mor φ).symm) v
  exact (e1.trans ((Y.tTgt_eq_tSrc_of_tBase_unit hu).trans e2.symm)).trans
    ((congrArg _ hvs).trans (h i))

/-! ### Descent along a full functor which is surjective on objects -/

/-- A full functor which is surjective on objects is surjective on morphisms. -/
theorem surjective_mor_of_full (F : EpFunctor X Y) (hfull : F.toFunctor.Full)
    (hs : Surjective F.obj) : Surjective F.mor := fun ψ => by
  obtain ⟨x, hx⟩ := hs (Y.src ψ)
  obtain ⟨x', hx'⟩ := hs (Y.tgt ψ)
  obtain ⟨φ, -, -, hφ⟩ := (F.full_iff.1 hfull) x x' ψ hx.symm hx'.symm
  exact ⟨φ, hφ⟩

/-- **Descent of forms**: for a full sc-smooth functor `F : X → Y` which is a surjective local
sc-diffeomorphism on objects, every sc-differential form of the ep-groupoid `X` is the
pull-back of an sc-differential form of the ep-groupoid `Y`. -/
theorem exists_epForms_formPullback_eq_of_surjective (F : EpFunctor X Y)
    (hfull : F.toFunctor.Full) (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) (hs : Surjective F.obj)
    {η : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hη : η ∈ X.epForms k) :
    ∃ τ ∈ Y.epForms k, formPullback F.isScSmoothMap_obj τ = η := by
  have e : formPullback F.isScSmoothMap_obj (formDescend hF hs η) = η :=
    formPullback_formDescend hF hs F.isScSmoothMap_obj (F.eq_of_tangentMap_eq hfull hF hη.2)
  refine ⟨formDescend hF hs η, ⟨isScForm_of_formPullback hF hs F.isScSmoothMap_obj ?_,
    Y.isMorCompatible_iff_formPullback.2 ?_⟩, e⟩
  · rw [e]; exact hη.1
  · refine formPullback_injective_of_isLocalScDiffeo (F.isLocalScDiffeo_mor hF)
      (F.surjective_mor_of_full hfull hs) F.isScSmoothMap_mor ?_
    rw [← F.formPullback_src_comm, ← F.formPullback_tgt_comm, e]
    exact X.isMorCompatible_iff_formPullback.1 hη.2

/-! ### Equivalences: `F^*` is a bijection -/

namespace IsEquivalence

open WeakFibredProduct

variable {F : EpFunctor X Y} (hF : F.IsEquivalence)

include hF in
/-- For an equivalence `F` and a form `τ` of the ep-groupoid `Y`: `π_X^* F^* τ = π_Y^* τ` on
the weak fibred product `X ×_Y Y` of `F` and `1_Y`. -/
theorem formPullback_projLeft_formPullback
    {τ : ∀ y : Y.PObj.Level 1, Y.PObj.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ} (hτ : τ ∈ Y.epForms k) :
    formPullback (projLeft F (EpFunctor.id Y)
        (Admissible.of_isEquivalence_left hF)).isScSmoothMap_obj
        (formPullback F.isScSmoothMap_obj τ) =
      formPullback (projRight F (EpFunctor.id Y)
        (Admissible.of_isEquivalence_left hF)).isScSmoothMap_obj τ := by
  have h1 := EpGroupoid.formPullback_eq_of_natTrans
    (natTrans F (EpFunctor.id Y) (Admissible.of_isEquivalence_left hF)) hτ
  rw [formPullback_comp_functor] at h1
  exact h1.trans (formPullback_congr _ _ (fun _ => rfl) τ)

include hF in
/-- **For an equivalence `F : X → Y`, the pull-back `F^* : Ωᵏ_ep(Y) → Ωᵏ_ep(X)` is injective.** -/
theorem injOn_formPullback :
    InjOn (formPullback (k := k) F.isScSmoothMap_obj) (Y.epForms k : Set _) := by
  intro τ hτ τ' hτ' h
  have hadm : Admissible F (EpFunctor.id Y) := Admissible.of_isEquivalence_left hF
  have hP := isEquivalence_projRight (G := EpFunctor.id Y) hF hadm
  have hsurj : Surjective (projRight F (EpFunctor.id Y) hadm).obj := fun y => by
    obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
    exact ⟨WeakFibredProduct.Obj.mk F (EpFunctor.id Y) x ψ y hs ht, rfl⟩
  refine formPullback_injective_of_isLocalScDiffeo hP.isLocalScDiffeo_obj hsurj
    (projRight F (EpFunctor.id Y) hadm).isScSmoothMap_obj ?_
  rw [← hF.formPullback_projLeft_formPullback hτ, ← hF.formPullback_projLeft_formPullback hτ', h]

include hF in
/-- **For an equivalence `F : X → Y`, every form of the ep-groupoid `X` is `F^*τ`** for a form
`τ` of the ep-groupoid `Y` (the existence of the push-forward, Definition 11.2.3). -/
theorem exists_formPullback_eq
    {ω : ∀ x : X.PObj.Level 1, X.PObj.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ X.epForms k) :
    ∃ τ ∈ Y.epForms k, formPullback F.isScSmoothMap_obj τ = ω := by
  have hadm : Admissible F (EpFunctor.id Y) := Admissible.of_isEquivalence_left hF
  have hP := isEquivalence_projRight (G := EpFunctor.id Y) hF hadm
  have hsurj : Surjective (projRight F (EpFunctor.id Y) hadm).obj := fun y => by
    obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
    exact ⟨WeakFibredProduct.Obj.mk F (EpFunctor.id Y) x ψ y hs ht, rfl⟩
  have hL : (epGroupoid F (EpFunctor.id Y) hadm).PObj.IsLocalScDiffeo X.PObj
      (projLeft F (EpFunctor.id Y) hadm).obj :=
    isLocalScDiffeo_x hadm (IsEquivalence.id (X := Y)).isLocalScDiffeo_obj
  have hLsurj : Surjective (projLeft F (EpFunctor.id Y) hadm).obj := fun x =>
    ⟨WeakFibredProduct.Obj.mk F (EpFunctor.id Y) x (Y.unit (F.obj x)) (F.obj x) (Y.src_unit _) (Y.tgt_unit _), rfl⟩
  obtain ⟨τ, hτ, he⟩ := exists_epForms_formPullback_eq_of_surjective
    (projRight F (EpFunctor.id Y) hadm) hP.full hP.isLocalScDiffeo_obj hsurj
    (EpGroupoid.formPullback_mem_epForms (projLeft F (EpFunctor.id Y) hadm) hω)
  refine ⟨τ, hτ, formPullback_injective_of_isLocalScDiffeo hL hLsurj
    (projLeft F (EpFunctor.id Y) hadm).isScSmoothMap_obj ?_⟩
  rw [hF.formPullback_projLeft_formPullback hτ, he]

/-- **`F^* : Ωᵏ_ep(Y) → Ωᵏ_ep(X)`** as a linear map, for an sc-smooth functor. -/
def _root_.Polyfold.EpFunctor.formPullbackLin (F : EpFunctor X Y) (k : ℕ) :
    Y.epForms k →ₗ[ℝ] X.epForms k :=
  LinearMap.codRestrict (X.epForms k)
    ((formPullbackₗ k F.isScSmoothMap_obj).domRestrict (Y.epForms k))
    fun ω => EpGroupoid.formPullback_mem_epForms F ω.2

@[simp] theorem _root_.Polyfold.EpFunctor.coe_formPullbackLin (F : EpFunctor X Y) (k : ℕ)
    (τ : Y.epForms k) : (F.formPullbackLin k τ).1 = formPullback F.isScSmoothMap_obj τ.1 := rfl

include hF in
/-- **For an equivalence `F : X → Y`, `F^* : Ωᵏ_ep(Y) → Ωᵏ_ep(X)` is a bijection.** -/
theorem bijective_formPullback (k : ℕ) : Bijective (F.formPullbackLin k) :=
  ⟨fun τ τ' h => Subtype.ext (hF.injOn_formPullback τ.2 τ'.2 (congrArg Subtype.val h)),
    fun ω => by
      obtain ⟨τ, hτ, he⟩ := hF.exists_formPullback_eq ω.2
      exact ⟨⟨τ, hτ⟩, Subtype.ext he⟩⟩

/-- The linear isomorphism `F^* : Ωᵏ_ep(Y) ≃ Ωᵏ_ep(X)` of an equivalence. -/
def formPullbackEquiv (k : ℕ) : Y.epForms k ≃ₗ[ℝ] X.epForms k :=
  LinearEquiv.ofBijective (F.formPullbackLin k) (hF.bijective_formPullback k)

/-- **2021 Definition 11.2.3, p. 528 (2017: Definition 11.2): the push-forward
`F_* : Ωᵏ_ep(X) → Ωᵏ_ep(Y)`** of sc-differential forms by an equivalence `F : X → Y`, here the
inverse of the bijection `F^*`; the text's defining formula is `definition_11_2_3`. -/
def formPush (k : ℕ) : X.epForms k →ₗ[ℝ] Y.epForms k := (hF.formPullbackEquiv k).symm.toLinearMap

/-- **2021 Lemma 11.2.4 (3), p. 528: `F^* F_*ω = ω`.** -/
theorem formPullback_formPush (ω : X.epForms k) :
    F.formPullbackLin k (hF.formPush k ω) = ω :=
  (hF.formPullbackEquiv k).apply_symm_apply ω

/-- **2021 Lemma 11.2.4 (3), p. 528: `F_* F^*τ = τ`.** -/
theorem formPush_formPullback (τ : Y.epForms k) :
    hF.formPush k (F.formPullbackLin k τ) = τ :=
  (hF.formPullbackEquiv k).symm_apply_apply τ

/-- `F_*ω = τ` iff `F^*τ = ω`. -/
theorem formPush_eq_iff (ω : X.epForms k) (τ : Y.epForms k) :
    hF.formPush k ω = τ ↔ F.formPullbackLin k τ = ω :=
  (hF.formPullbackEquiv k).symm_apply_eq.trans eq_comm

/-- **2021 Definition 11.2.3, p. 528 (2017: Definition 11.2), the defining formula of the
push-forward**: for `x ∈ X₁`, a morphism `ψ : F(x) → y` in `𝐘₁` and `l₁, …, l_k ∈ T_xX`,
`(F_*ω)_y(Tψ(TF(x) l₁), …, Tψ(TF(x) l_k)) = ω_x(l₁, …, l_k)`. -/
theorem definition_11_2_3 (ω : X.epForms k) {x : X.PObj.Level 1} {y : Y.PObj.Level 1}
    {ψ : Mor'} (hψ : ψ ∈ Y.PMor.levelSet 1)
    (hs : Y.PObj.levelVal 1 (liftLevelOneMap F.isScSmoothMap_obj x) = Y.src ψ)
    (ht : Y.PObj.levelVal 1 y = Y.tgt ψ) (l : Fin k → X.PObj.tangentFiber x) :
    (hF.formPush k ω).1 y (fun j => Y.tangentMorCLE hψ hs ht
      (tangentFiberMap F.isScSmoothMap_obj x (l j))) = ω.1 x l := by
  rw [(hF.formPush k ω).2.2.apply Y hψ hs ht]
  have h := congrArg (fun η : X.epForms k => η.1 x l) (hF.formPullback_formPush ω)
  exact h

include hF in
/-- Every `h₁, …, h_k ∈ T_yY`, `y ∈ Y₁`, are `Tψ(TF(x) l_j)` for some `x ∈ X₁`, a morphism
`ψ : F(x) → y` in `𝐘₁` and `l_j ∈ T_xX` (the choice made in Definition 11.2.3; `F` is
essentially surjective and `Tψ`, `TF(x)` are isomorphisms). -/
theorem exists_lift_tangent (y : Y.PObj.Level 1) (h : Fin k → Y.PObj.tangentFiber y) :
    ∃ (x : X.PObj.Level 1) (ψ : Mor') (hψ : ψ ∈ Y.PMor.levelSet 1)
      (hs : Y.PObj.levelVal 1 (liftLevelOneMap F.isScSmoothMap_obj x) = Y.src ψ)
      (ht : Y.PObj.levelVal 1 y = Y.tgt ψ) (l : Fin k → X.PObj.tangentFiber x),
      ∀ j, Y.tangentMorCLE hψ hs ht (tangentFiberMap F.isScSmoothMap_obj x (l j)) = h j := by
  obtain ⟨x₀, ψ, hs, ht⟩ := hF.exists_iso (Y.PObj.levelVal 1 y)
  have hψ : ψ ∈ Y.PMor.levelSet 1 :=
    (Y.mem_levelSet_tgt_iff ψ 1).1 (ht ▸ MPolyfold.levelVal_mem y)
  have hx₀ : x₀ ∈ X.PObj.levelSet 1 :=
    (hF.isLocalScDiffeo_obj.mem_levelSet_iff x₀ 1).1 (hs ▸ (Y.mem_levelSet_src_iff ψ 1).2 hψ)
  have hs' : Y.PObj.levelVal 1 (liftLevelOneMap F.isScSmoothMap_obj (X.PObj.levelMk 1 x₀ hx₀)) =
      Y.src ψ := hs.symm
  have hxy : F.obj (X.PObj.levelVal 1 (X.PObj.levelMk 1 x₀ hx₀)) =
      Y.PObj.levelVal 1 (liftLevelOneMap F.isScSmoothMap_obj (X.PObj.levelMk 1 x₀ hx₀)) := rfl
  refine ⟨X.PObj.levelMk 1 x₀ hx₀, ψ, hψ, hs', ht.symm, fun j =>
    (hF.isLocalScDiffeo_obj.tangentFiberEquiv hxy).symm
      ((Y.tangentMorCLE hψ hs' ht.symm).symm (h j)), fun j => ?_⟩
  have e : tangentFiberMap F.isScSmoothMap_obj (X.PObj.levelMk 1 x₀ hx₀)
      ((hF.isLocalScDiffeo_obj.tangentFiberEquiv hxy).symm
        ((Y.tangentMorCLE hψ hs' ht.symm).symm (h j))) =
      (Y.tangentMorCLE hψ hs' ht.symm).symm (h j) :=
    Subtype.ext ((coe_tangentFiberMap_apply _ _).trans
      (hF.isLocalScDiffeo_obj.tangentMap_tangentFiberEquiv_symm hxy _))
  rw [e, ContinuousLinearEquiv.apply_symm_apply]

include hF in
/-- **2021 Lemma 11.2.2, p. 527 (2017: Lemma 11.1)**: for an equivalence `F : X → Y`, an
sc-differential form `ω` on the ep-groupoid `X`, `y ∈ Y₁`, morphisms `ψ : F(x) → y` and
`ψ' : F(x') → y` in `𝐘₁` with `x, x' ∈ X₁`, and `l_j ∈ T_xX`, `l'_j ∈ T_{x'}X` with
`Tψ(TF(x) l_j) = Tψ'(TF(x') l'_j)`: `ω_x(l₁, …, l_k) = ω_{x'}(l'₁, …, l'_k)`. -/
theorem lemma_11_2_2 (ω : X.epForms k) {x x' : X.PObj.Level 1} {y : Y.PObj.Level 1}
    {ψ ψ' : Mor'} (hψ : ψ ∈ Y.PMor.levelSet 1) (hψ' : ψ' ∈ Y.PMor.levelSet 1)
    (hs : Y.PObj.levelVal 1 (liftLevelOneMap F.isScSmoothMap_obj x) = Y.src ψ)
    (ht : Y.PObj.levelVal 1 y = Y.tgt ψ)
    (hs' : Y.PObj.levelVal 1 (liftLevelOneMap F.isScSmoothMap_obj x') = Y.src ψ')
    (ht' : Y.PObj.levelVal 1 y = Y.tgt ψ')
    (l : Fin k → X.PObj.tangentFiber x) (l' : Fin k → X.PObj.tangentFiber x')
    (h : ∀ j, Y.tangentMorCLE hψ hs ht (tangentFiberMap F.isScSmoothMap_obj x (l j)) =
      Y.tangentMorCLE hψ' hs' ht' (tangentFiberMap F.isScSmoothMap_obj x' (l' j))) :
    ω.1 x l = ω.1 x' l' := by
  rw [← hF.definition_11_2_3 ω hψ hs ht l, ← hF.definition_11_2_3 ω hψ' hs' ht' l']
  exact congrArg _ (funext h)

end IsEquivalence

end EpFunctor

end Polyfold
