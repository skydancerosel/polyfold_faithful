import Polyfold.Chapter8.Basic

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: the claim after **Definition 8.1** (p. 267) that natural equivalence of sc-smooth
functors is an equivalence relation.  There is no 2014 preprint of Part II; numbers and pages are
the 2017 text's.  The definitions (`EpNatTrans`, `EpFunctor.NaturallyEquivalent`) are in
`Polyfold/Chapter8/Basic.lean`.

# Natural transformations of sc-smooth functors

## The text, paraphrased

(Definition 8.1, pp. 266–267) Two sc-smooth functors `F, G : X → Y` are naturally equivalent,
`F ≃ G`, if there is an sc-smooth map `τ : X → 𝐘` with `τ(x) : F(x) → G(x)` and
`τ(x') ∘ F(h) = G(h) ∘ τ(x)` for every morphism `h : x → x'`; `τ : F → G` is a natural
transformation.  (p. 267) "The relation `F ≃ G` between sc-smooth functors `F, G : X → Y` of
ep-groupoids is an equivalence relation."  The text gives no proof.

## What is formalized

* `EpNatTrans.refl F` (`x ↦ 1_{F(x)}`), `EpNatTrans.symm` (`x ↦ τ(x)⁻¹`) and `EpNatTrans.trans`
  (`x ↦ τ'(x) ∘ τ(x)`), with `refl_app`, `symm_app`, `trans_app`.
* **The claim of p. 267**: `EpFunctor.naturallyEquivalent_equivalence :
  Equivalence EpFunctor.NaturallyEquivalent`, with `EpFunctor.NaturallyEquivalent.refl`, `.symm`,
  `.trans`.
* Whiskering (not in the text): `EpNatTrans.whiskerLeft` (`τ ∘ E : F ∘ E → G ∘ E`, `w ↦ τ(E w)`)
  and `EpNatTrans.whiskerRight` (`K ∘ τ : K ∘ F → K ∘ G`, `x ↦ K(τ(x))`), and the corresponding
  `EpFunctor.NaturallyEquivalent.comp_left`, `.comp_right`.

## What the text leaves implicit, and the choices made

* **Sc-smoothness of `x ↦ τ'(x) ∘ τ(x)`** is the only point that is not pure groupoid algebra.  The
  composition `m` is sc-smooth on the fibred product `𝐘 ₛ×ₜ 𝐘` (Definition 7.3 (4)); we use
  Chapter 7's equivalent sheet form (`EpGroupoid.isScSmoothCompSheet`): near `x₀` take a sheet
  `W ∋ τ'(x₀)` of `s` with inverse `σ`; for `x ∈ τ'⁻¹(W)`, `τ'(x) = σ(s τ'(x)) = σ(G x) =
  σ(t τ(x))`, so `τ'(x) ∘ τ(x) = m(σ(t ψ), ψ)` at `ψ = τ(x)`, an sc-smooth map composed with the
  sc-smooth `τ`.  Sc-smoothness is local (`MPolyfold.IsScSmoothOn.of_locally`).
* The inverse `x ↦ τ(x)⁻¹` is sc-smooth since `ι` is (Definition 7.3 (2)); its naturality is the
  inverse of the naturality square of `h⁻¹`.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v w

section NatTrans

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

namespace EpNatTrans

/-- The identity natural transformation `1_F : F → F`, `x ↦ 1_{F(x)}`. -/
def refl (F : EpFunctor X Y) : EpNatTrans F F where
  app x := Y.unit (F.obj x)
  isScSmoothMap_app := Y.isScSmoothMap_unit.comp F.isScSmoothMap_obj
  src_app x := Y.src_unit _
  tgt_app x := Y.tgt_unit _
  naturality h := by
    rw [GroupoidStr.unit_comp_of_eq (G := Y.toGroupoidStr) (F.tgt_mor h),
      GroupoidStr.comp_unit_of_eq (G := Y.toGroupoidStr) (F.src_mor h)]

@[simp]
theorem refl_app (F : EpFunctor X Y) (x : Obj) : (refl F).app x = Y.unit (F.obj x) := rfl

variable {F G H : EpFunctor X Y}

/-- The inverse natural transformation `τ⁻¹ : G → F`, `x ↦ τ(x)⁻¹`. -/
def symm (τ : EpNatTrans F G) : EpNatTrans G F where
  app x := Y.inv (τ.app x)
  isScSmoothMap_app := Y.isScSmoothMap_inv.comp τ.isScSmoothMap_app
  src_app x := (Y.src_inv _).trans (τ.tgt_app x)
  tgt_app x := (Y.tgt_inv _).trans (τ.src_app x)
  naturality h := by
    -- the inverse of the naturality square of `h⁻¹`
    have hn := τ.naturality (X.inv h)
    rw [X.tgt_inv, X.src_inv, GroupoidFunctor.mor_inv, GroupoidFunctor.mor_inv] at hn
    have h1 : Y.src (τ.app (X.src h)) = Y.tgt (Y.inv (F.mor h)) := by
      rw [τ.src_app, Y.tgt_inv, F.src_mor]
    have h2 : Y.src (Y.inv (G.mor h)) = Y.tgt (τ.app (X.tgt h)) := by
      rw [τ.tgt_app, Y.src_inv, G.tgt_mor]
    have hi := congrArg Y.inv hn
    rw [GroupoidStr.inv_comp_rev h1, GroupoidStr.inv_comp_rev h2, GroupoidStr.inv_inv,
      GroupoidStr.inv_inv] at hi
    exact hi.symm

@[simp]
theorem symm_app (τ : EpNatTrans F G) (x : Obj) : τ.symm.app x = Y.inv (τ.app x) := rfl

/-- **`x ↦ τ'(x) ∘ τ(x)` is sc-smooth**, by condition (4) of Definition 7.3 in the sheet form. -/
theorem isScSmoothMap_comp_app (τ : EpNatTrans F G) (τ' : EpNatTrans G H) :
    X.PObj.IsScSmoothMap Y.PMor fun x => Y.comp (τ'.app x) (τ.app x) := by
  have hc' : Continuous τ'.app := continuousOn_univ.1 τ'.isScSmoothMap_app.continuousOn
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x₀ _ => ?_
  obtain ⟨W, V, σ, hW, hd⟩ := Y.isLocalScDiffeo_src (τ'.app x₀)
  have hU : IsOpen (τ'.app ⁻¹' W) := hd.isScSmoothOn.isOpen.preimage hc'
  have hmaps : MapsTo τ.app (τ'.app ⁻¹' W) (Y.tgt ⁻¹' V) := fun x hx => by
    change Y.tgt (τ.app x) ∈ V
    rw [τ.tgt_app, ← τ'.src_app]
    exact hd.mapsTo hx
  refine ⟨τ'.app ⁻¹' W, hU, hW, subset_univ _, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (Y.isScSmoothCompSheet σ W V hd)
    (τ.isScSmoothMap_app.mono hU (subset_univ _)) hmaps).congr fun x hx => ?_
  simp only [Function.comp_apply]
  rw [τ.tgt_app, ← τ'.src_app, hd.left_inv _ hx]

/-- The composite natural transformation `τ' ∘ τ : F → H`, `x ↦ τ'(x) ∘ τ(x)`. -/
def trans (τ : EpNatTrans F G) (τ' : EpNatTrans G H) : EpNatTrans F H where
  app x := Y.comp (τ'.app x) (τ.app x)
  isScSmoothMap_app := isScSmoothMap_comp_app τ τ'
  src_app x := by
    rw [Y.src_comp _ _ ((τ'.src_app x).trans (τ.tgt_app x).symm), τ.src_app]
  tgt_app x := by
    rw [Y.tgt_comp _ _ ((τ'.src_app x).trans (τ.tgt_app x).symm), τ'.tgt_app]
  naturality h := by
    have e₁ : Y.src (τ'.app (X.tgt h)) = Y.tgt (τ.app (X.tgt h)) := by
      rw [τ'.src_app, τ.tgt_app]
    have e₂ : Y.src (τ.app (X.tgt h)) = Y.tgt (F.mor h) := by rw [τ.src_app, F.tgt_mor]
    have e₃ : Y.src (τ'.app (X.tgt h)) = Y.tgt (G.mor h) := by rw [τ'.src_app, G.tgt_mor]
    have e₄ : Y.src (G.mor h) = Y.tgt (τ.app (X.src h)) := by rw [G.src_mor, τ.tgt_app]
    have e₅ : Y.src (H.mor h) = Y.tgt (τ'.app (X.src h)) := by rw [H.src_mor, τ'.tgt_app]
    have e₆ : Y.src (τ'.app (X.src h)) = Y.tgt (τ.app (X.src h)) := by
      rw [τ'.src_app, τ.tgt_app]
    rw [Y.comp_assoc _ _ _ e₁ e₂, τ.naturality h, ← Y.comp_assoc _ _ _ e₃ e₄, τ'.naturality h,
      Y.comp_assoc _ _ _ e₅ e₆]

@[simp]
theorem trans_app (τ : EpNatTrans F G) (τ' : EpNatTrans G H) (x : Obj) :
    (τ.trans τ').app x = Y.comp (τ'.app x) (τ.app x) := rfl

end EpNatTrans

namespace EpFunctor

theorem NaturallyEquivalent.refl (F : EpFunctor X Y) : F.NaturallyEquivalent F :=
  ⟨EpNatTrans.refl F⟩

theorem NaturallyEquivalent.symm {F G : EpFunctor X Y} (h : F.NaturallyEquivalent G) :
    G.NaturallyEquivalent F :=
  let ⟨τ⟩ := h
  ⟨τ.symm⟩

theorem NaturallyEquivalent.trans {F G H : EpFunctor X Y} (h : F.NaturallyEquivalent G)
    (h' : G.NaturallyEquivalent H) : F.NaturallyEquivalent H :=
  let ⟨τ⟩ := h
  let ⟨τ'⟩ := h'
  ⟨τ.trans τ'⟩

/-- **The claim after Definition 8.1** (p. 267): the relation `F ≃ G` between sc-smooth functors
`F, G : X → Y` is an equivalence relation. -/
theorem naturallyEquivalent_equivalence :
    Equivalence (EpFunctor.NaturallyEquivalent (X := X) (Y := Y)) :=
  ⟨NaturallyEquivalent.refl, NaturallyEquivalent.symm, NaturallyEquivalent.trans⟩

end EpFunctor

end NatTrans

/-! ### Whiskering -/

section Whisker

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']

namespace EpNatTrans

/-- **Whiskering on the left**: for `E : W → X` and `τ : F → G`, the natural transformation
`F ∘ E → G ∘ E`, `w ↦ τ(E(w))`. -/
def whiskerLeft {W : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'}
    {Y : EpGroupoid Obj'' Mor''} (E : EpFunctor W X) {F G : EpFunctor X Y}
    (τ : EpNatTrans F G) : EpNatTrans (F.comp E) (G.comp E) where
  app w := τ.app (E.obj w)
  isScSmoothMap_app := τ.isScSmoothMap_app.comp E.isScSmoothMap_obj
  src_app w := τ.src_app (E.obj w)
  tgt_app w := τ.tgt_app (E.obj w)
  naturality h := by
    have hn := τ.naturality (E.mor h)
    rw [E.tgt_mor, E.src_mor] at hn
    exact hn

/-- **Whiskering on the right**: for `τ : F → G` and `K : Y → Z`, the natural transformation
`K ∘ F → K ∘ G`, `x ↦ K(τ(x))`. -/
def whiskerRight {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    {Z : EpGroupoid Obj'' Mor''} {F G : EpFunctor X Y} (τ : EpNatTrans F G)
    (K : EpFunctor Y Z) : EpNatTrans (K.comp F) (K.comp G) where
  app x := K.mor (τ.app x)
  isScSmoothMap_app := K.isScSmoothMap_mor.comp τ.isScSmoothMap_app
  src_app x := by
    change Z.src (K.mor (τ.app x)) = K.obj (F.obj x)
    rw [K.src_mor, τ.src_app]
  tgt_app x := by
    change Z.tgt (K.mor (τ.app x)) = K.obj (G.obj x)
    rw [K.tgt_mor, τ.tgt_app]
  naturality h := by
    change Z.comp (K.mor (τ.app (X.tgt h))) (K.mor (F.mor h)) =
      Z.comp (K.mor (G.mor h)) (K.mor (τ.app (X.src h)))
    rw [← K.mor_comp _ _ (by rw [τ.src_app, F.tgt_mor]), τ.naturality h,
      K.mor_comp _ _ (by rw [G.src_mor, τ.tgt_app])]

end EpNatTrans

namespace EpFunctor

theorem NaturallyEquivalent.comp_left {W : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'}
    {Y : EpGroupoid Obj'' Mor''} (E : EpFunctor W X) {F G : EpFunctor X Y}
    (h : F.NaturallyEquivalent G) : (F.comp E).NaturallyEquivalent (G.comp E) :=
  let ⟨τ⟩ := h
  ⟨τ.whiskerLeft E⟩

theorem NaturallyEquivalent.comp_right {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    {Z : EpGroupoid Obj'' Mor''} {F G : EpFunctor X Y} (h : F.NaturallyEquivalent G)
    (K : EpFunctor Y Z) : (K.comp F).NaturallyEquivalent (K.comp G) :=
  let ⟨τ⟩ := h
  ⟨τ.whiskerRight K⟩

end EpFunctor

end Whisker

end Polyfold
