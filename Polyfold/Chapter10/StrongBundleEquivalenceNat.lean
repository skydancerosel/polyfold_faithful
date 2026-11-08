import Polyfold.Chapter10.StrongBundleEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.4 "Strong Bundles and Equivalences" (pp. 502–503; 2017: pp. 362–364):
**Definition 10.4.8, Remark 10.4.9, Definitions 10.4.10, 10.4.11** (2017: Definition 10.11,
Remark 10.4, Definitions 10.12, 10.13).  Numbers and pages are the 2021 text's, the 2017 ones in
parentheses.  Definition 10.4.1 and the results 10.4.2–10.4.5 are in
`StrongBundleEquivalence.lean`.

# Natural equivalences of strong bundle functors; the category `SEP`

## The text, paraphrased

(Definition 10.4.8, p. 502 (2017: Definition 10.11)) Strong bundle functors `Φ`, `Ψ` are naturally
equivalent, `Φ ≃ Ψ`, if there is a natural transformation `T` assigning to `w` a morphism
`T(w) : Φ(w) → Ψ(w)` of `W'`, with `T(w') ∘ Φ(h) = Ψ(h) ∘ T(w)` for `h : w → w'`, and a natural
transformation `τ : ϕ → ψ` with `τ ∘ P = P' ∘ T`.  (Remark 10.4.9, p. 502 (2017: Remark 10.4))
`τ` is sc-smooth by definition, and nothing is asked of `T`; but `T(w) = (τ(P(w)), Φ(w))` and
`Ψ(w) = μ'(τ(P(w)), Φ(w))` (10.23), so `Ψ` and `T` are determined by `Φ` and `τ`, and `T` is an
sc-smooth strong bundle map.  (Definition 10.4.10, p. 503 (2017: Definition 10.12)) Equivalently,
a natural transformation is a strong bundle map `T : W → 𝐗' ₛ×_{P'} W'` covering a natural
transformation `τ`, of the form `T(w) = (τ(P(w)), Φ(w))`, with `Ψ(w) = μ'(τ(P(w)), Φ(w))`.
(p. 503) `Φ ≃ Ψ` implies `|Φ| = |Ψ|`.  (Definition 10.4.11, p. 503 (2017: Definition 10.13)) The
category `SEP` has the strong bundles over ep-groupoids as objects and the strong bundle functors
as morphisms, with the distinguished class `F` of strong bundle equivalences.

## What is formalized

* `EpStrongBundle.StrongBundleNatTrans` and `StrongBundleNatEquiv` (**Definition 10.4.8**), with
  the witness `StrongBundleNatTrans.refl`.
* **Remark 10.4.9**: `StrongBundleNatTrans.T_val`, `T_eq`, `obj_eq` ((10.23)), `unique`,
  `unique_functor` (`Ψ` and `T` are determined by `Φ` and `τ`), `isStrongBundleMap_T` (`T` is a
  strong bundle map covering `τ`, on `[0]` and `[1]`).
* `EpStrongBundle.IsStrongBundleNatTransMap` (**Definition 10.4.10**) and the equivalence with
  Definition 10.4.8: `StrongBundleNatTrans.isStrongBundleNatTransMap` and
  `IsStrongBundleNatTransMap.toNatTrans`.
* `StrongBundleNatTrans.orbitMap_eq`, `StrongBundleNatEquiv.orbitMap_eq` (`Φ ≃ Ψ ⇒ |Φ| = |Ψ|`).
* `SEP` with `LargeCategory SEP` (**Definition 10.4.11**), `SEP.equivalences` (the class `F`, a
  multiplicative `MorphismProperty`), the forgetful functor `SEP.toEP` with
  `toEP_map_mem_equivalences`.
* `EpStrongBundle.isStrongBundleEquivalence_of_inverse`: isomorphisms of strong bundles over
  ep-groupoids are strong bundle equivalences (used for the witnesses), with
  `EpFunctor.isEquivalence_of_inverse` and `StrongBundle.isStrongBundleIsoOn_univ_of_inverse`.

## What the text leaves implicit, and the choices made

* In Definition 10.4.8, `T` is data `W → 𝐖'` (a function, no smoothness) and `τ` is an
  `EpNatTrans` (Definition 10.1.4, sc-smooth); "`P' ∘ T`" is the projection functor on morphisms,
  `(φ, w') ↦ φ`.  The morphisms of `W'` are pairs `(φ, w') : w' → μ'(φ, w')`, so
  `T(w) : Φ(w) → Ψ(w)` reads `T(w).2 = Φ(w)`, `μ'(T(w)) = Ψ(w)`.
* Definition 10.4.10 ⇒ 10.4.8 needs `Φ` and `Ψ` to be strong bundle functors (for the naturality of
  `T`), as the text's setting assumes.
* In `SEP` the morphisms are the strong bundle functors `(ϕ, Φ)` (both components; `Φ` determines
  `ϕ` only on the image of `P`).

## Not formalized

* Nothing of Remark 10.4.9 and Definitions 10.4.8, 10.4.10, 10.4.11 is left out.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Global strong bundle isomorphisms -/

section IsoUniv

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'}

/-- Two mutually inverse strong bundle maps `Φ`, `Ψ` covering mutually inverse sc-smooth `f`, `g`
make `Φ : Y → Y'` a strong bundle isomorphism over `X` (`U = X`, `U' = X'`). -/
theorem isStrongBundleIsoOn_univ_of_inverse {f : X → X'} {g : X' → X} {Φ : Y → Y'} {Ψ : Y' → Y}
    (h : B.IsStrongBundleMap B' f Φ) (h' : B'.IsStrongBundleMap B g Ψ)
    (hf : PX.IsScSmoothMap PX' f) (hg : PX'.IsScSmoothMap PX g) (hfg : ∀ x, g (f x) = x)
    (hgf : ∀ x', f (g x') = x') (hΦΨ : ∀ y, Ψ (Φ y) = y) (hΨΦ : ∀ y', Φ (Ψ y') = y') :
    B.IsStrongBundleIsoOn B' h univ univ where
  isScDiffeoOn_base :=
    ⟨g, hf, hg, mapsTo_univ _ _, mapsTo_univ _ _, fun x _ => hfg x, fun x _ => hgf x⟩
  isScDiffeoOn_zero := ⟨Ψ, by
    rw [preimage_univ, preimage_univ]
    exact ⟨h.isScSmoothMap, h'.isScSmoothMap, mapsTo_univ _ _, mapsTo_univ _ _,
      fun y _ => hΦΨ y, fun y _ => hΨΦ y⟩⟩
  isScDiffeoOn_one := ⟨oneRestrict B' B Ψ h'.mapsTo_oneSet, by
    rw [preimage_univ, preimage_univ]
    exact ⟨h.isScSmoothMap_one, h'.isScSmoothMap_one, mapsTo_univ _ _, mapsTo_univ _ _,
      fun a _ => B.oneVal_injective (by rw [oneVal_oneRestrict, oneVal_oneRestrict, hΦΨ]),
      fun a _ => B'.oneVal_injective (by rw [oneVal_oneRestrict, oneVal_oneRestrict, hΨΦ])⟩⟩

end StrongBundle

end IsoUniv

/-! ### Isomorphisms of ep-groupoids are equivalences -/

section EpIso

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}

/-- An sc-smooth functor with an inverse sc-smooth functor is an equivalence (Definition 10.1.1,
via Lemma 10.1.2). -/
theorem EpFunctor.isEquivalence_of_inverse {F : EpFunctor X Y} {G : EpFunctor Y X}
    (h₁ : ∀ x, G.obj (F.obj x) = x) (h₂ : ∀ y, F.obj (G.obj y) = y)
    (h₃ : ∀ φ, G.mor (F.mor φ) = φ) (h₄ : ∀ ψ, F.mor (G.mor ψ) = ψ) : F.IsEquivalence :=
  F.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' _ _ he =>
        (h₃ φ).symm.trans ((congrArg G.mor he).trans (h₃ φ'))
      full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht =>
        ⟨G.mor ψ, by rw [G.src_mor, hs, h₁], by rw [G.tgt_mor, ht, h₁], h₄ ψ⟩
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y =>
        ⟨G.obj y, Y.unit y, by rw [Y.src_unit, h₂], Y.tgt_unit y⟩ }
    fun x => ⟨univ, univ, G.obj, mem_univ x, ⟨F.isScSmoothMap_obj, G.isScSmoothMap_obj,
      mapsTo_univ _ _, mapsTo_univ _ _, fun x _ => h₁ x, fun y _ => h₂ y⟩⟩

end EpIso

section Functors

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

namespace EpStrongBundle

/-- **Isomorphisms of strong bundles over ep-groupoids are strong bundle equivalences**: strong
bundle maps `Φ : W → W'` covering `ϕ` and `Ψ : W' → W` covering `ψ` (Definition 8.3.2), mutually
inverse and with `ϕ`, `ψ` mutually inverse, make the strong bundle functor of `Φ`
(`IsMap.liftFunctor`) a strong bundle equivalence (Definition 10.4.1, with `U = X`). -/
theorem isStrongBundleEquivalence_of_inverse {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X}
    {Φ : W → W'} {Ψ : W' → W} (hΦ : E.IsMap E' ϕ Φ) (hΨ : E'.IsMap E ψ Ψ)
    (hϕψ : ∀ x, ψ.obj (ϕ.obj x) = x) (hψϕ : ∀ x', ϕ.obj (ψ.obj x') = x')
    (hϕψm : ∀ φ, ψ.mor (ϕ.mor φ) = φ) (hψϕm : ∀ φ', ϕ.mor (ψ.mor φ') = φ')
    (hΦΨ : ∀ w, Ψ (Φ w) = w) (hΨΦ : ∀ w', Φ (Ψ w') = w') :
    E.IsStrongBundleEquivalence E' ϕ hΦ.liftFunctor := by
  have hm₁ : ∀ q, liftMor ψ hΨ.isStrongBundleMap.covers (liftMor ϕ hΦ.isStrongBundleMap.covers q) =
      q := fun q => Subtype.ext (Prod.ext (hϕψm _) (hΦΨ _))
  have hm₂ : ∀ q', liftMor ϕ hΦ.isStrongBundleMap.covers
      (liftMor ψ hΨ.isStrongBundleMap.covers q') = q' := fun q' =>
    Subtype.ext (Prod.ext (hψϕm _) (hΨΦ _))
  have hS₁ := hΦ.isStrongBundleFunctor_liftFunctor
  have hS₂ := hΨ.isStrongBundleFunctor_liftFunctor
  have hc : ∀ {Y₁ Y₂ : Type u} [TopologicalSpace Y₁] [TopologicalSpace Y₂] (g : Y₁ → Y₂),
      ContinuousOn g univ → Continuous g := fun g hg => continuousOn_univ.1 hg
  refine ⟨hS₁, EpFunctor.isEquivalence_of_inverse (G := ψ) hϕψ hψϕ hϕψm hψϕm,
    EpFunctor.isEquivalence_of_inverse (G := hΨ.liftFunctor) hΦΨ hΨΦ hm₁ hm₂, ?_,
    fun x => ⟨univ, univ, mem_univ x, StrongBundle.isStrongBundleIsoOn_univ_of_inverse
      hΦ.isStrongBundleMap hΨ.isStrongBundleMap ϕ.isScSmoothMap_obj ψ.isScSmoothMap_obj hϕψ hψϕ
      hΦΨ hΨΦ⟩,
    fun φ => ⟨univ, univ, mem_univ φ, StrongBundle.isStrongBundleIsoOn_univ_of_inverse
      hS₁.isStrongBundleMap_mor hS₂.isStrongBundleMap_mor ϕ.isScSmoothMap_mor ψ.isScSmoothMap_mor
      hϕψm hψϕm hm₁ hm₂⟩⟩
  have hl : ∀ a, E'.oneOrbitMap E hΨ.liftFunctor hS₂.isStrongBundleMap_obj.mapsTo_oneSet
      (E.oneOrbitMap E' hΦ.liftFunctor hS₁.isStrongBundleMap_obj.mapsTo_oneSet a) = a := fun a =>
    Quotient.inductionOn a fun w => congrArg (Quotient.mk _)
      (B.oneVal_injective (by
        rw [StrongBundle.oneVal_oneRestrict, StrongBundle.oneVal_oneRestrict]; exact hΦΨ _))
  have hr : ∀ a, E.oneOrbitMap E' hΦ.liftFunctor hS₁.isStrongBundleMap_obj.mapsTo_oneSet
      (E'.oneOrbitMap E hΨ.liftFunctor hS₂.isStrongBundleMap_obj.mapsTo_oneSet a) = a := fun a =>
    Quotient.inductionOn a fun w => congrArg (Quotient.mk _)
      (B'.oneVal_injective (by
        rw [StrongBundle.oneVal_oneRestrict, StrongBundle.oneVal_oneRestrict]; exact hΨΦ _))
  exact (Homeomorph.mk ⟨_, _, hl, hr⟩
    (continuous_oneOrbitMap (hc _ hS₁.isStrongBundleMap_obj.isScSmoothMap_one.continuousOn))
    (continuous_oneOrbitMap
      (hc _ hS₂.isStrongBundleMap_obj.isScSmoothMap_one.continuousOn))).isHomeomorph

/-! ### Definition 10.4.8: natural equivalences of strong bundle functors -/

variable (E E') in
/-- **2021 Definition 10.4.8, p. 502 (2017: Definition 10.11)**: a natural transformation between
the strong bundle functors `Φ, Ψ : (W, 𝐖) → (W', 𝐖')` (covering `ϕ, ψ : X → X'`): a morphism
`T(w) : Φ(w) → Ψ(w)` of `(W', 𝐖')` for every `w`, natural (`T(w') ∘ Φ(h) = Ψ(h) ∘ T(w)` for
`h : w → w'`), together with a natural transformation `τ : ϕ → ψ` (Definition 10.1.4, sc-smooth)
with `τ(P(w)) = P(T(w))`, `P` the projection functor on morphisms.  No smoothness of `T` is
required (Remark 10.4.9 derives it). -/
structure StrongBundleNatTrans (ϕ ψ : EpFunctor X X')
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) where
  /-- The morphism `T(w) : Φ(w) → Ψ(w)` of `(W', 𝐖')`. -/
  T : W → pullbackSpace P' X'.src
  src_T : ∀ w, E'.toEpGroupoid.src (T w) = Φ.obj w
  tgt_T : ∀ w, E'.toEpGroupoid.tgt (T w) = Ψ.obj w
  naturality : ∀ q : pullbackSpace P X.src,
    E'.toEpGroupoid.comp (T (E.toEpGroupoid.tgt q)) (Φ.mor q) =
      E'.toEpGroupoid.comp (Ψ.mor q) (T (E.toEpGroupoid.src q))
  /-- The natural transformation `τ : ϕ → ψ` of the underlying functors. -/
  τ : EpNatTrans ϕ ψ
  app_P : ∀ w, τ.app (P w) = (T w : Mor' × W').1

variable (E E') in
/-- **2021 Definition 10.4.8**: `Φ ≃ Ψ`, the strong bundle functors are naturally equivalent. -/
def StrongBundleNatEquiv (ϕ ψ : EpFunctor X X') (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) :
    Prop :=
  Nonempty (E.StrongBundleNatTrans E' ϕ ψ Φ Ψ)

namespace StrongBundleNatTrans

variable {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ)

/-- **(10.23)**, first half (Remark 10.4.9, p. 502): `T(w) = (τ(P(w)), Φ(w))`. -/
theorem T_val (w : W) : (θ.T w : Mor' × W') = (θ.τ.app (P w), Φ.obj w) :=
  Prod.ext (θ.app_P w).symm (θ.src_T w)

theorem mem (w : W) : (θ.τ.app (P w), Φ.obj w) ∈ pullbackSpace P' X'.src :=
  θ.T_val w ▸ (θ.T w).2

theorem T_eq (w : W) : θ.T w = ⟨(θ.τ.app (P w), Φ.obj w), θ.mem w⟩ := Subtype.ext (θ.T_val w)

/-- **(10.23)**, second half: `Ψ(w) = μ'(τ(P(w)), Φ(w))`. -/
theorem obj_eq (w : W) : Ψ.obj w = E'.μ ⟨(θ.τ.app (P w), Φ.obj w), θ.mem w⟩ :=
  (θ.tgt_T w).symm.trans (congrArg E'.μ (θ.T_eq w))

/-- **Remark 10.4.9**: `Ψ` (on objects) and `T` are determined by `Φ` and `τ`. -/
theorem unique {Ψ₁ Ψ₂ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (θ₁ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₁) (θ₂ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₂)
    (hτ : θ₁.τ.app = θ₂.τ.app) : Ψ₁.obj = Ψ₂.obj ∧ θ₁.T = θ₂.T := by
  have hT : θ₁.T = θ₂.T := funext fun w => Subtype.ext (by rw [θ₁.T_val, θ₂.T_val, hτ])
  refine ⟨funext fun w => ?_, hT⟩
  rw [← θ₁.tgt_T, ← θ₂.tgt_T, hT]

/-- **Remark 10.4.9**: if `Ψ₁`, `Ψ₂` are strong bundle functors covering `ψ`, then the functor
`Ψ` itself is determined by `Φ` and `τ`. -/
theorem unique_functor {Ψ₁ Ψ₂ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h₁ : E.IsStrongBundleFunctor E' ψ Ψ₁) (h₂ : E.IsStrongBundleFunctor E' ψ Ψ₂)
    (θ₁ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₁) (θ₂ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₂)
    (hτ : θ₁.τ.app = θ₂.τ.app) : Ψ₁ = Ψ₂ := by
  have h := (unique θ₁ θ₂ hτ).1
  refine EpFunctor.ext h (funext fun q => Subtype.ext ?_)
  rw [h₁.mor_val, h₂.mor_val, h]

/-- **Remark 10.4.9**: `T : W → 𝐗' ₛ×_{P'} W'` is a strong bundle map covering `τ : X → 𝐗'`
(linear on the fibres, sc-smooth on `[0]` and `[1]`), by (10.23) and the universal properties of
the pull-back. -/
theorem isStrongBundleMap_T (hΦ : E.IsStrongBundleFunctor E' ϕ Φ) :
    B.IsStrongBundleMap (B'.pullback X'.isScSmoothMap_src) θ.τ.app θ.T where
  covers w := (θ.app_P w).symm
  fiber_linear x := by
    let L : P ⁻¹' {x} →ₗ[ℝ] pullbackProj P' X'.src ⁻¹' {θ.τ.app x} :=
      ((pullbackFiberLinearEquiv P' X'.src (θ.τ.app x)).symm.toLinearMap).comp
        ((fiberCast P' (θ.τ.src_app x).symm).comp
          (hΦ.isStrongBundleMap_obj.fiber_linear x).mk')
    have hL : fiberRestrict P (pullbackProj P' X'.src) θ.τ.app θ.T (fun w => (θ.app_P w).symm) x =
        L := by
      funext v
      apply Subtype.ext; apply Subtype.ext
      have hv : P (v : W) = x := v.2
      change (θ.T v : Mor' × W') = ((L v : pullbackSpace P' X'.src) : Mor' × W')
      rw [θ.T_val, hv]
      change (θ.τ.app x, Φ.obj v) = (θ.τ.app x,
        ((fiberCast P' (θ.τ.src_app x).symm _ : P' ⁻¹' {X'.src (θ.τ.app x)}) : W'))
      rw [fiberCast_val]
      rfl
    rw [hL]; exact L.isLinear
  isScSmoothMap := by
    have hT : θ.T = pullbackPair P' X'.src (θ.τ.app ∘ P) Φ.obj θ.mem :=
      funext fun w => θ.T_eq w
    rw [hT]
    exact B'.isScSmoothMap_pullbackPair X'.isScSmoothMap_src
      (θ.τ.isScSmoothMap_app.comp B.isScSmoothMap_proj) hΦ.isStrongBundleMap_obj.isScSmoothMap _
  mapsTo_oneSet w hw := by
    rw [B'.mem_oneSet_pullback_iff X'.isScSmoothMap_src, θ.T_val]
    exact hΦ.isStrongBundleMap_obj.mapsTo_oneSet hw
  isScSmoothMap_one := by
    refine B'.isScSmoothMap_to_pullback_one X'.isScSmoothMap_src ?_ ?_
    · refine MPolyfold.IsScSmoothOn.congr (θ.τ.isScSmoothMap_app.comp B.isScSmoothMap_proj1)
        fun a _ => ?_
      change θ.τ.app (P (B.oneVal a)) = (θ.T (B.oneVal a) : Mor' × W').1
      rw [θ.T_val]
    · refine MPolyfold.IsScSmoothOn.congr hΦ.isStrongBundleMap_obj.isScSmoothMap_one
        fun a _ => B'.oneVal_injective ?_
      change Φ.obj (B.oneVal a) = (θ.T (B.oneVal a) : Mor' × W').2
      rw [θ.T_val]

include θ in
/-- **`Φ ≃ Ψ` implies `|Φ| = |Ψ| : |W| → |W'|`** (p. 503). -/
theorem orbitMap_eq : Φ.orbitMap = Ψ.orbitMap :=
  orbitMap_eq_of_forall_exists fun w => ⟨θ.T w, θ.src_T w, θ.tgt_T w⟩

end StrongBundleNatTrans

/-- `Φ ≃ Ψ ⇒ |Φ| = |Ψ|` (p. 503). -/
theorem StrongBundleNatEquiv.orbitMap_eq {ϕ ψ : EpFunctor X X'}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.StrongBundleNatEquiv E' ϕ ψ Φ Ψ) :
    Φ.orbitMap = Ψ.orbitMap :=
  h.some.orbitMap_eq

/-- **Witness for Definition 10.4.8**: `Φ ≃ Φ`, with `T(w) = 1_{Φ(w)}` and `τ = 1_ϕ`. -/
def StrongBundleNatTrans.refl {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hΦ : E.IsStrongBundleFunctor E' ϕ Φ) : E.StrongBundleNatTrans E' ϕ ϕ Φ Φ where
  T w := E'.toEpGroupoid.unit (Φ.obj w)
  src_T w := E'.toEpGroupoid.src_unit _
  tgt_T w := E'.toEpGroupoid.tgt_unit _
  naturality q := by
    rw [← Φ.tgt_mor, ← Φ.src_mor, E'.toEpGroupoid.unit_comp, E'.toEpGroupoid.comp_unit]
  τ := EpNatTrans.refl ϕ
  app_P w := by
    rw [EpNatTrans.refl_app, ← hΦ.isStrongBundleMap_obj.covers]
    rfl

/-! ### Definition 10.4.10 -/

variable (E E') in
/-- **2021 Definition 10.4.10, p. 503 (2017: Definition 10.12)**: a natural transformation
between the strong bundle functors `Φ`, `Ψ` (covering `ϕ`, `ψ`) as a strong bundle map
`T : W → 𝐗' ₛ×_{P'} W'` covering a natural transformation `τ : ϕ → ψ`, of the form
`T(w) = (τ(P(w)), Φ(w))`, with `Ψ(w) = μ'(τ(P(w)), Φ(w))`. -/
structure IsStrongBundleNatTransMap {ϕ ψ : EpFunctor X X'}
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (τ : EpNatTrans ϕ ψ)
    (T : W → pullbackSpace P' X'.src) : Prop where
  T_val : ∀ w, (T w : Mor' × W') = (τ.app (P w), Φ.obj w)
  isStrongBundleMap : B.IsStrongBundleMap (B'.pullback X'.isScSmoothMap_src) τ.app T
  obj_eq : ∀ w, Ψ.obj w = E'.μ (T w)

/-- **Definition 10.4.8 ⇒ Definition 10.4.10** (Remark 10.4.9). -/
theorem StrongBundleNatTrans.isStrongBundleNatTransMap {ϕ ψ : EpFunctor X X'}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ)
    (hΦ : E.IsStrongBundleFunctor E' ϕ Φ) : E.IsStrongBundleNatTransMap E' Φ Ψ θ.τ θ.T :=
  ⟨θ.T_val, θ.isStrongBundleMap_T hΦ, fun w => (θ.tgt_T w).symm⟩

/-- **Definition 10.4.10 ⇒ Definition 10.4.8**: for strong bundle functors `Φ`, `Ψ` covering `ϕ`,
`ψ`, the data of Definition 10.4.10 are a natural transformation in the sense of Definition 10.4.8
(naturality of `T` is the naturality of `τ`). -/
def IsStrongBundleNatTransMap.toNatTrans {ϕ ψ : EpFunctor X X'}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {τ : EpNatTrans ϕ ψ}
    {T : W → pullbackSpace P' X'.src} (hT : E.IsStrongBundleNatTransMap E' Φ Ψ τ T)
    (hΦ : E.IsStrongBundleFunctor E' ϕ Φ) (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) :
    E.StrongBundleNatTrans E' ϕ ψ Φ Ψ where
  T := T
  src_T w := congrArg Prod.snd (hT.T_val w)
  tgt_T w := (hT.obj_eq w).symm
  naturality q := by
    have hL : (T (E.μ q) : Mor' × W').2 = E'.μ (Φ.mor q) := by
      rw [hT.T_val]; exact (Φ.tgt_mor q).symm
    have hR : (Ψ.mor q : Mor' × W').2 = E'.μ (T (q : Mor × W).2) :=
      (Ψ.src_mor q).trans (hT.obj_eq _)
    have e₁ : (E'.toEpGroupoid.comp (T (E.toEpGroupoid.tgt q)) (Φ.mor q) : Mor' × W') =
        (X'.comp (T (E.μ q) : Mor' × W').1 (Φ.mor q : Mor' × W').1, (Φ.mor q : Mor' × W').2) :=
      morComp_val hL
    have e₂ : (E'.toEpGroupoid.comp (Ψ.mor q) (T (E.toEpGroupoid.src q)) : Mor' × W') =
        (X'.comp (Ψ.mor q : Mor' × W').1 (T (q : Mor × W).2 : Mor' × W').1,
          (T (q : Mor × W).2 : Mor' × W').2) :=
      morComp_val hR
    refine Subtype.ext (e₁.trans (Eq.trans ?_ e₂.symm))
    have hq : P (q : Mor × W).2 = X.src (q : Mor × W).1 := q.2
    rw [hT.T_val, hT.T_val, hΦ.mor_val, hΨ.mor_val, E.P_μ, hq]
    exact Prod.ext (τ.naturality _) rfl
  τ := τ
  app_P w := (congrArg Prod.fst (hT.T_val w)).symm

/-! ### Definition 10.4.11: the category `SEP` -/

end EpStrongBundle

end Functors

/-- A bundled strong bundle over an ep-groupoid, an object of the category `SEP`
(2021 Definition 10.4.11). -/
structure SEP : Type (u + 1) where
  /-- The object set of the base. -/
  Obj : Type u
  /-- The morphism set of the base. -/
  Mor : Type u
  [instTopObj : TopologicalSpace Obj]
  [instT2Obj : T2Space Obj]
  [instParaObj : ParacompactSpace Obj]
  [instTopMor : TopologicalSpace Mor]
  [instT2Mor : T2Space Mor]
  [instParaMor : ParacompactSpace Mor]
  /-- The base ep-groupoid. -/
  X : EpGroupoid Obj Mor
  /-- The total space. -/
  W : Type u
  [instTopW : TopologicalSpace W]
  [instT2W : T2Space W]
  [instParaW : ParacompactSpace W]
  /-- The projection. -/
  P : W → Obj
  [instAdd : ∀ x, AddCommGroup (P ⁻¹' {x})]
  [instModule : ∀ x, Module ℝ (P ⁻¹' {x})]
  /-- The strong bundle `P : W → X`. -/
  B : StrongBundle X.PObj P
  /-- The strong bundle over the ep-groupoid, `(P, μ)`. -/
  E : EpStrongBundle X B

attribute [instance] SEP.instTopObj SEP.instT2Obj SEP.instParaObj SEP.instTopMor SEP.instT2Mor
  SEP.instParaMor SEP.instTopW SEP.instT2W SEP.instParaW SEP.instAdd SEP.instModule

namespace SEP

instance (A : SEP.{u}) : ParacompactSpace (pullbackSpace A.P A.X.src) :=
  A.B.paracompactSpace_pullback A.X.PMor A.X.src

/-- A morphism of `SEP`: a strong bundle functor `Φ` covering `ϕ` (Definition 8.3.3). -/
structure Hom (A A' : SEP.{u}) where
  /-- The underlying functor of the base ep-groupoids. -/
  ϕ : EpFunctor A.X A'.X
  /-- The functor `(W, 𝐖) → (W', 𝐖')`. -/
  Φ : EpFunctor A.E.toEpGroupoid A'.E.toEpGroupoid
  isStrongBundleFunctor : A.E.IsStrongBundleFunctor A'.E ϕ Φ

theorem Hom.ext' {A A' : SEP.{u}} {F G : Hom A A'} (h₁ : F.ϕ = G.ϕ) (h₂ : F.Φ = G.Φ) : F = G := by
  cases F; cases G; cases h₁; cases h₂; rfl

/-- **2021 Definition 10.4.11, p. 503 (2017: Definition 10.13)**: the category `SEP` of strong
bundles over ep-groupoids and strong bundle functors. -/
instance : LargeCategory SEP.{u} where
  Hom := Hom
  id A := ⟨EpFunctor.id A.X, EpFunctor.id A.E.toEpGroupoid, A.E.isStrongBundleFunctor_id⟩
  comp F G := ⟨G.ϕ.comp F.ϕ, G.Φ.comp F.Φ, G.isStrongBundleFunctor.comp F.isStrongBundleFunctor⟩
  id_comp _ := Hom.ext' (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)
  comp_id _ := Hom.ext' (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)
  assoc _ _ _ := Hom.ext' (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

/-- **2021 Definition 10.4.11**: the distinguished class `F` of strong bundle equivalences
(Definition 10.4.1) among the morphisms of `SEP`; it contains the identities and is closed under
composition. -/
def equivalences : MorphismProperty SEP.{u} := fun A A' F =>
  A.E.IsStrongBundleEquivalence A'.E (Hom.ϕ F) (Hom.Φ F)

instance : equivalences.{u}.IsMultiplicative where
  id_mem A := EpStrongBundle.isStrongBundleEquivalence_id A.E
  comp_mem _ _ hF hG := EpStrongBundle.IsStrongBundleEquivalence.comp hG hF

/-- The forgetful functor `SEP → EP`, `(P, μ) ↦ X`, `(ϕ, Φ) ↦ ϕ`; it maps `F` into `E`. -/
def toEP : SEP.{u} ⥤ EP.{u} where
  obj A := ⟨A.Obj, A.Mor, A.X⟩
  map F := Hom.ϕ F
  map_id _ := rfl
  map_comp _ _ := rfl

theorem toEP_map_mem_equivalences {A A' : SEP.{u}} {F : A ⟶ A'} (hF : equivalences F) :
    EP.equivalences (toEP.map F) :=
  hF.isEquivalence_base

end SEP

end Polyfold
