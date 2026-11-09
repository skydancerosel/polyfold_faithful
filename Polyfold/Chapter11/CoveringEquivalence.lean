import Polyfold.Chapter10.WeakFibredProductTheorem
import Polyfold.Chapter8.GeometricLift
import Polyfold.Chapter8.NonVacuityBundle
import Mathlib.CategoryTheory.Action

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.6 "Coverings and Equivalences" (pp. 549–555; 2017: pp. 401–405):
**Lemma 11.6.1** (new in the 2021 edition), **Lemma 11.6.2** (2017: Lemma 11.8), **Lemma 11.6.3**
(2017: Lemma 11.9), **Definition 11.6.4** (2017: Definition 11.6) and **Definition 11.6.5**
(2017: Definition 11.7).  Theorem 11.6.6 is in `CoveringEquivalenceTheorem.lean`, Definition
11.6.7 and Proposition 11.6.8 in `CoveringEquivalenceDiagram.lean`.

# Proper coverings: fibres, translation groupoids, functors and natural transformations

## The text, paraphrased

A proper covering functor `F : Y → X` (Definition 8.5.1) is on objects a surjective local
sc-diffeomorphism with finite, evenly covered fibres, and `α : 𝐘 → 𝐗 ×_{s,F} Y, ψ ↦ (F(ψ), s(ψ))`
is an sc-diffeomorphism.

(Lemma 11.6.1, p. 549) On morphisms `F` is a surjective local sc-diffeomorphism.

(Lemma 11.6.2, p. 551) For an object `x` of `X` the isotropy group `G_x` acts on `Y_x = F⁻¹(x)`
by `g ∗ y = t(α⁻¹(g, y))`, and the full subcategory `Y(x)` on `Y_x` is identified with the
translation groupoid `G_x ⋉ Y_x`, by the identity on objects and by `α` on morphisms.

(Lemma 11.6.3, p. 551) A morphism `φ : x → x'` induces the bijection `B_φ(y) = t(α⁻¹(φ, y))` from
`Y_x` to `Y_{x'}`, equivariant along `g ↦ φ ∘ g ∘ φ⁻¹`, and an equivalence
`φ̃ : G_x ⋉ Y_x → G_{x'} ⋉ Y_{x'}`, `(g, y) ↦ (φ ∘ g ∘ φ⁻¹, B_φ(y))`, bijective on objects and
on morphisms.

(Definition 11.6.4, p. 553) An sc-smooth functor `(Ψ, Φ) : F → F'` between proper coverings is a
pair of sc-smooth functors with `Φ ∘ F = F' ∘ Ψ`; it is an equivalence if `Ψ` and `Φ` are
equivalences of ep-groupoids and `Ψ : Y(x) → Y'(Φ(x))` is bijective on objects for every `x`.

(Definition 11.6.5, p. 554) A natural transformation `(ζ, ξ) → (ζ', ξ')` is a pair `(τ_Y, τ_X)`
of natural transformations `ζ → ζ'`, `ξ → ξ'` with `τ_X ∘ F = F' ∘ τ_Y`.

## What is formalized

* **Lemma 11.6.1**: `EpFunctor.IsProperCovering.lemma_11_6_1`.
* The lift `α⁻¹`: `IsProperCovering.lift` (`mor_lift`, `src_lift`, `eq_lift`, `obj_tgt_lift`),
  and `existsUnique_lift_tgt` (unique lifts with prescribed target).
* **Lemma 11.6.2**: `IsProperCovering.Fiber hF x` (`Y_x`, a type synonym of `F.obj ⁻¹' {x}`) with
  the action `instMulActionFiber` of `X.Isotropy x` (`smul_val_of`: `g ∗ y = t(ψ)` for the lift
  `ψ`); `FiberFull x` (`Y(x)`, Chapter 8's `GroupoidStr.FullOb`), `Translation x` (Mathlib's
  `ActionCategory`), the functor `toTranslation`, and `lemma_11_6_2`: the action formula, the
  identity on objects, `α` on morphisms, bijective on objects, full, faithful, an equivalence.
* **Lemma 11.6.3**: `transportFiber φ` (`B_φ`), `bijective_transportFiber`,
  `transportFiber_smul` (equivariance along `conjIsotropy`), `translationMap φ` (`φ̃`), and
  `lemma_11_6_3`.
* **Definition 11.6.4**: `ProperCoveringHom F F'` (1), with `id`, `comp`, `mapsTo_fiber`;
  `ProperCoveringHom.IsFiberBijective` and `ProperCoveringHom.IsEquivalence` (2), with
  `IsEquivalence.id`, `IsEquivalence.comp`.
* **`isFiberBijective_of_isEquivalence`, `isEquivalence_iff`: the fibre condition of Definition
  11.6.4 (2) follows from the other two.**  If `Ψ` and `Φ` are equivalences of ep-groupoids, then
  `Ψ` maps `F⁻¹(x)` bijectively onto `F'⁻¹(Φ(x))` for every `x` (injectivity from faithfulness of
  `Φ` and unique lifting along `F`; surjectivity from essential surjectivity of `Ψ`, fullness of
  `Φ` and unique lifting along `F'`).  The text's remark after the definition treats the fibre
  bijection as singling out a subclass of the functors of (1); within (2) it is automatic.
* **Definition 11.6.5**: `ProperCoveringHom.NatTrans` (with `naturality_F`, the commutative
  diagram after the definition), `refl`, `symm`, `trans`, `whiskerLeft`, `whiskerRight`;
  `NaturallyEquivalent`, an equivalence relation (`naturallyEquivalent_equivalence`) compatible
  with composition on both sides (`NaturallyEquivalent.comp_left`, `.comp_right`).
* Witnesses (namespace `Polyfold.CoveringEquivalence.Examples`): `nonempty_fiber_id` (the
  identity of the pair groupoid of `ℤ`, a proper covering with nonempty fibres, so Lemmas 11.6.2
  and 11.6.3 apply); `pairToPointCovering` (Definition 11.6.4 (1)) and
  `isEquivalence_pairToPointCovering` (Definition 11.6.4 (2), Chapter 10's equivalence
  `pairToPoint`, which has no inverse functor); `naturallyEquivalent_pairToPointCovering`.

## What the text leaves implicit, and the choices made

* "Naturally identified" in Lemma 11.6.2 is read as a functor `Y(x) ⥤ G_x ⋉ Y_x` which is the
  identity on objects (a bijection), `α` on morphisms, full and faithful, hence an equivalence of
  categories.  `Y(x)` is the full subcategory of the groupoid structure of `Y` on `Y_x`; its
  topology plays no part in the lemma.  Likewise `φ̃` of Lemma 11.6.3 is a functor of translation
  groupoids, bijective on objects, full and faithful.
* `G_x` is `X.Isotropy x`, the group of morphisms `x → x`; `φ ∘ g ∘ φ⁻¹` is `conjIsotropy φ g`.
* Natural transformations of ep-groupoids are Chapter 8's `EpNatTrans` (sc-smooth, natural); in
  a groupoid every natural transformation is invertible (`NatTrans.symm`).  The identity
  `τ_X ∘ F = F' ∘ τ_Y` is read objectwise: `τ_X(F(y)) = F'(τ_Y(y))`.
* "sc-smooth functor" is the repository's `EpFunctor` (sc-smooth on objects and morphisms).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u v

section Lift

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}

namespace EpFunctor.IsProperCovering

variable (hF : F.IsProperCovering)
include hF

/-- **2021 Lemma 11.6.1, p. 549 (new in the 2021 edition)**: on morphisms a proper covering
functor `F : Y → X` is a surjective local sc-diffeomorphism. -/
theorem lemma_11_6_1 : Surjective F.mor ∧ Y.PMor.IsLocalScDiffeo X.PMor F.mor := by
  refine ⟨fun φ => ?_, F.isLocalScDiffeo_mor hF.isLocalScDiffeo⟩
  obtain ⟨y, hy⟩ := hF.surjective (X.src φ)
  obtain ⟨ψ, ⟨hψ, -⟩, -⟩ := hF.existsUnique_lift (φ := φ) (y := y) hy.symm
  exact ⟨ψ, hψ⟩

/-- `α⁻¹(φ, y)`. -/
def lift (φ : MorX) (y : ObjY) (h : X.src φ = F.obj y) : MorY :=
  (hF.existsUnique_lift h).exists.choose

variable {φ : MorX} {y : ObjY} (h : X.src φ = F.obj y)

theorem mor_lift : F.mor (hF.lift φ y h) = φ := (hF.existsUnique_lift h).exists.choose_spec.1

theorem src_lift : Y.src (hF.lift φ y h) = y := (hF.existsUnique_lift h).exists.choose_spec.2

theorem eq_lift {ψ : MorY} (hm : F.mor ψ = φ) (hs : Y.src ψ = y) : ψ = hF.lift φ y h :=
  (hF.existsUnique_lift h).unique ⟨hm, hs⟩ ⟨hF.mor_lift h, hF.src_lift h⟩

theorem obj_tgt_lift : F.obj (Y.tgt (hF.lift φ y h)) = X.tgt φ := by
  rw [← F.tgt_mor, hF.mor_lift]

omit h in
theorem existsUnique_lift_tgt (h : X.tgt φ = F.obj y) :
    ∃! ψ : MorY, F.mor ψ = φ ∧ Y.tgt ψ = y := by
  have h' : X.src (X.inv φ) = F.obj y := by rw [X.src_inv, h]
  refine ⟨Y.inv (hF.lift _ y h'), ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · rw [GroupoidFunctor.mor_inv, hF.mor_lift, GroupoidStr.inv_inv]
  · rw [Y.tgt_inv, hF.src_lift]
  · have : Y.inv ψ = hF.lift _ y h' :=
      hF.eq_lift h' (by rw [GroupoidFunctor.mor_inv, hψ.1]) (by rw [Y.src_inv, hψ.2])
    rw [← this, GroupoidStr.inv_inv]

end EpFunctor.IsProperCovering

/-! ### The action of `G_x` on `Y_x` -/

namespace EpFunctor.IsProperCovering

/-- `Y_x = F⁻¹(x)` as a type carrying the action of `G_x` (a type synonym, so that the action,
which depends on `hF`, is an instance). -/
def Fiber (_hF : F.IsProperCovering) (x : ObjX) : Type u := ↥(F.obj ⁻¹' {x})

namespace Fiber

variable {hF : F.IsProperCovering} {x : ObjX}

/-- The point of `Y`. -/
def val (a : hF.Fiber x) : ObjY := Subtype.val (p := fun y => y ∈ F.obj ⁻¹' {x}) a

theorem obj_val (a : hF.Fiber x) : F.obj a.val = x :=
  Subtype.property (p := fun y => y ∈ F.obj ⁻¹' {x}) a

/-- A point of `F⁻¹(x)` as a point of `Y_x`. -/
def mk (y : ObjY) (hy : F.obj y = x) : hF.Fiber x := (⟨y, hy⟩ : ↥(F.obj ⁻¹' {x}))

@[simp] theorem val_mk (y : ObjY) (hy : F.obj y = x) : (mk (hF := hF) y hy).val = y := rfl

@[ext] theorem ext {a b : hF.Fiber x} (h : a.val = b.val) : a = b := Subtype.ext h

end Fiber

variable (hF : F.IsProperCovering)
include hF
variable (x : ObjX)

/-- **(11.15)**: `g * y := t(α⁻¹(g, y))`. -/
def fiberSMul (g : X.Isotropy x) (a : hF.Fiber x) : hF.Fiber x :=
  Fiber.mk (Y.tgt (hF.lift g.val a.val (g.src_val.trans a.obj_val.symm)))
    ((hF.obj_tgt_lift _).trans g.tgt_val)

theorem fiberSMul_val_of {g : X.Isotropy x} {a : hF.Fiber x} {ψ : MorY} (hm : F.mor ψ = g.val)
    (hs : Y.src ψ = a.val) : (hF.fiberSMul x g a).val = Y.tgt ψ :=
  congrArg Y.tgt (hF.eq_lift (g.src_val.trans a.obj_val.symm) hm hs).symm

/-- **The action of `G_x` on `Y_x`** (2021 p. 550): `1 * y = y` and
`(g₂ ∘ g₁) * y = g₂ * (g₁ * y)`. -/
instance instMulActionFiber : MulAction (X.Isotropy x) (hF.Fiber x) where
  smul := hF.fiberSMul x
  one_smul a := by
    refine Fiber.ext ?_
    change (hF.fiberSMul x 1 a).val = a.val
    rw [hF.fiberSMul_val_of x (ψ := Y.unit a.val)
      (by rw [F.mor_unit, a.obj_val]; rfl) (Y.src_unit _), Y.tgt_unit]
  mul_smul g₂ g₁ a := by
    refine Fiber.ext ?_
    change (hF.fiberSMul x (g₂ * g₁) a).val = (hF.fiberSMul x g₂ (hF.fiberSMul x g₁ a)).val
    set ψ₁ := hF.lift g₁.val a.val (g₁.src_val.trans a.obj_val.symm) with hψ₁
    have h₂ : X.src g₂.val = F.obj (Y.tgt ψ₁) := by
      rw [hF.obj_tgt_lift, g₂.src_val, g₁.tgt_val]
    set ψ₂ := hF.lift g₂.val (Y.tgt ψ₁) h₂
    have hc : Y.src ψ₂ = Y.tgt ψ₁ := hF.src_lift h₂
    rw [hF.fiberSMul_val_of x (ψ := Y.comp ψ₂ ψ₁)
      (by rw [F.mor_comp _ _ hc, hF.mor_lift, hF.mor_lift]; rfl)
      (by rw [Y.src_comp _ _ hc, hF.src_lift]),
      Y.tgt_comp _ _ hc,
      hF.fiberSMul_val_of x (a := hF.fiberSMul x g₁ a) (ψ := ψ₂) (hF.mor_lift h₂) hc]

theorem smul_val_of {g : X.Isotropy x} {a : hF.Fiber x} {ψ : MorY} (hm : F.mor ψ = g.val)
    (hs : Y.src ψ = a.val) : (g • a).val = Y.tgt ψ :=
  hF.fiberSMul_val_of x hm hs

/-! ### Lemma 11.6.2 -/

/-- `Y(x)`, the full subcategory of `Y` on `Y_x = F⁻¹(x)` (Chapter 8's `FiberCat`, in any
universe). -/
abbrev FiberFull : Type u := Y.toGroupoidStr.FullOb (F.obj ⁻¹' {x})

/-- `G_x ⋉ Y_x`, the translation groupoid (Mathlib's action category). -/
abbrev Translation : Type u := ActionCategory (X.Isotropy x) (hF.Fiber x)

/-- The group element of a morphism `(g, y)` of `G_x ⋉ Y_x`. -/
def homVal {p q : hF.Translation x} (f : p ⟶ q) : X.Isotropy x := f.val

theorem homVal_smul {p q : hF.Translation x} (f : p ⟶ q) : hF.homVal x f • p.back = q.back :=
  f.2

theorem homVal_comp {p q r : hF.Translation x} (f : p ⟶ q) (g : q ⟶ r) :
    hF.homVal x (f ≫ g) = hF.homVal x g * hF.homVal x f := rfl

theorem homVal_id (p : hF.Translation x) : hF.homVal x (𝟙 p) = 1 := rfl

theorem hom_ext' {p q : hF.Translation x} {f g : p ⟶ q} (h : hF.homVal x f = hF.homVal x g) :
    f = g := Subtype.ext h

omit hF in
/-- `F(ψ) ∈ G_x` for a morphism `ψ` of `Y(x)`. -/
def isoOf {a b : FiberFull (F := F) x} (ψ : a ⟶ b) : X.Isotropy x :=
  ⟨F.mor ψ.1, by rw [F.src_mor, show Y.src ψ.1 = a.val from ψ.2.1]; exact a.mem,
    by rw [F.tgt_mor, show Y.tgt ψ.1 = b.val from ψ.2.2]; exact b.mem⟩

omit hF in
@[simp] theorem isoOf_val {a b : FiberFull (F := F) x} (ψ : a ⟶ b) : (isoOf x ψ).val = F.mor ψ.1 :=
  rfl

/-- The point `a ∈ Y(x)` as an object of `G_x ⋉ Y_x`. -/
def toTranslationObj (a : FiberFull (F := F) x) : hF.Translation x :=
  ActionCategory.objEquiv _ _ (Fiber.mk a.val a.mem)

/-- **The identification `Y(x) → G_x ⋉ Y_x`** of Lemma 11.6.2: the identity on objects and
`ψ ↦ (F(ψ), s(ψ))` (the map `α`) on morphisms. -/
def toTranslation : FiberFull (F := F) x ⥤ hF.Translation x where
  obj a := hF.toTranslationObj x a
  map {a b} ψ := ⟨isoOf x ψ, Fiber.ext (by
    change (isoOf x ψ • Fiber.mk (hF := hF) a.val a.mem).val = b.val
    rw [hF.smul_val_of x (a := Fiber.mk a.val a.mem) (ψ := ψ.1) rfl ψ.2.1]
    exact ψ.2.2)⟩
  map_id a := Subtype.ext (GroupoidStr.Isotropy.ext (by
    change F.mor (Y.unit a.val) = X.unit x
    rw [F.mor_unit, show F.obj a.val = x from a.mem]))
  map_comp {a b c} γ ψ := Subtype.ext (GroupoidStr.Isotropy.ext (by
    change F.mor (Y.comp ψ.1 γ.1) = X.comp (F.mor ψ.1) (F.mor γ.1)
    exact F.mor_comp _ _ (ψ.2.1.trans γ.2.2.symm)))

@[simp] theorem toTranslation_obj_back (a : FiberFull (F := F) x) :
    ((hF.toTranslation x).obj a).back = Fiber.mk a.val a.mem := rfl

@[simp] theorem toTranslation_map_val {a b : FiberFull (F := F) x} (ψ : a ⟶ b) :
    hF.homVal x ((hF.toTranslation x).map ψ) = isoOf x ψ := rfl

theorem bijective_toTranslation_obj : Bijective (hF.toTranslation x).obj := by
  change Bijective ((ActionCategory.objEquiv _ _) ∘ fun a : FiberFull (F := F) x =>
    (Fiber.mk (hF := hF) a.val a.mem))
  refine (ActionCategory.objEquiv _ _).bijective.comp
    ⟨fun a b h => GroupoidStr.FullOb.ext (congrArg Fiber.val h), fun c => ⟨⟨c.val, c.obj_val⟩, ?_⟩⟩
  exact Fiber.ext rfl

theorem faithful_toTranslation : (hF.toTranslation x).Faithful where
  map_injective {a b} ψ ψ' h := by
    have h1 : F.mor ψ.1 = F.mor ψ'.1 :=
      congrArg (fun g : X.Isotropy x => g.val) (congrArg Subtype.val h)
    have h2 : X.src (F.mor ψ.1) = F.obj a.val := by
      rw [F.src_mor, show Y.src ψ.1 = a.val from ψ.2.1]
    exact Subtype.ext ((hF.existsUnique_lift h2).unique ⟨rfl, ψ.2.1⟩ ⟨h1.symm, ψ'.2.1⟩)

theorem full_toTranslation : (hF.toTranslation x).Full where
  map_surjective {a b} g := by
    have hg : hF.homVal x g • Fiber.mk (hF := hF) a.val a.mem = Fiber.mk b.val b.mem :=
      hF.homVal_smul x g
    have h : X.src (hF.homVal x g).val = F.obj a.val :=
      (hF.homVal x g).src_val.trans (show F.obj a.val = x from a.mem).symm
    have ht : Y.tgt (hF.lift _ a.val h) = b.val := by
      have := congrArg Fiber.val hg
      rwa [hF.smul_val_of x (a := Fiber.mk a.val a.mem) (hF.mor_lift h) (hF.src_lift h)] at this
    exact ⟨⟨hF.lift _ a.val h, hF.src_lift h, ht⟩,
      Subtype.ext (GroupoidStr.Isotropy.ext (hF.mor_lift h))⟩

/-- **2021 Lemma 11.6.2, p. 551 (2017: Lemma 11.8, p. 402)**: for a proper covering functor
`F : Y → X` and `x ∈ X`, `g * y := t(α⁻¹(g, y))` is an action of `G_x` on `Y_x = F⁻¹(x)`
(`instMulActionFiber`), and the full subcategory `Y(x)` on `Y_x` is identified with the
translation groupoid `G_x ⋉ Y_x` by the functor `toTranslation`, which is the identity on objects
and `α : ψ ↦ (F(ψ), s(ψ))` on morphisms: it is bijective on objects, full and faithful (an
isomorphism of categories), in particular an equivalence. -/
theorem lemma_11_6_2 :
    (∀ (g : X.Isotropy x) (a : hF.Fiber x),
      (g • a).val = Y.tgt (hF.lift g.val a.val (g.src_val.trans a.obj_val.symm))) ∧
    (∀ a : FiberFull (F := F) x, ((hF.toTranslation x).obj a).back = Fiber.mk a.val a.mem) ∧
    (∀ {a b : FiberFull (F := F) x} (ψ : a ⟶ b),
      (hF.homVal x ((hF.toTranslation x).map ψ)).val = F.mor ψ.1) ∧
    Bijective (hF.toTranslation x).obj ∧ (hF.toTranslation x).Full ∧
    (hF.toTranslation x).Faithful ∧ (hF.toTranslation x).IsEquivalence := by
  have hfull := hF.full_toTranslation x
  have hfaith := hF.faithful_toTranslation x
  refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, hF.bijective_toTranslation_obj x, hfull,
    hfaith, { essSurj := ⟨fun c => ?_⟩ }⟩
  obtain ⟨a, ha⟩ := (hF.bijective_toTranslation_obj x).2 c
  exact ⟨a, ⟨eqToIso ha⟩⟩

/-! ### Lemma 11.6.3 -/

/-- `B_φ(y) = t(ψ)` with `F(ψ) = φ`, `s(ψ) = y`, for `φ : x → x'` (stated with `s(φ) = x`,
`t(φ) = x'` as hypotheses). -/
def transportFiber (φ : MorX) {x x' : ObjX} (hs : X.src φ = x) (ht : X.tgt φ = x')
    (a : hF.Fiber x) : hF.Fiber x' :=
  Fiber.mk (Y.tgt (hF.lift φ a.val (hs.trans a.obj_val.symm))) ((hF.obj_tgt_lift _).trans ht)

theorem transportFiber_val_of {φ : MorX} {x x' : ObjX} (hs : X.src φ = x) (ht : X.tgt φ = x')
    {a : hF.Fiber x} {ψ : MorY} (hm : F.mor ψ = φ) (hsψ : Y.src ψ = a.val) :
    (hF.transportFiber φ hs ht a).val = Y.tgt ψ :=
  congrArg Y.tgt (hF.eq_lift (hs.trans a.obj_val.symm) hm hsψ).symm

theorem transportFiber_inv_transportFiber {φ : MorX} {x x' : ObjX} (hs : X.src φ = x)
    (ht : X.tgt φ = x') (a : hF.Fiber x) :
    hF.transportFiber (X.inv φ) ((X.src_inv φ).trans ht) ((X.tgt_inv φ).trans hs)
      (hF.transportFiber φ hs ht a) = a := by
  refine Fiber.ext ?_
  set ψ := hF.lift φ a.val (hs.trans a.obj_val.symm)
  rw [hF.transportFiber_val_of _ _ (ψ := Y.inv ψ) (by rw [GroupoidFunctor.mor_inv, hF.mor_lift])
    (by rw [Y.src_inv]; rfl), Y.tgt_inv, hF.src_lift]

/-- `B_φ` is a bijection (inverse `B_{φ⁻¹}`). -/
theorem bijective_transportFiber {φ : MorX} {x x' : ObjX} (hs : X.src φ = x)
    (ht : X.tgt φ = x') : Bijective (hF.transportFiber φ hs ht) := by
  refine ⟨Function.LeftInverse.injective (hF.transportFiber_inv_transportFiber hs ht), fun b => ?_⟩
  refine ⟨hF.transportFiber (X.inv φ) ((X.src_inv φ).trans ht) ((X.tgt_inv φ).trans hs) b, ?_⟩
  have := hF.transportFiber_inv_transportFiber (φ := X.inv φ) ((X.src_inv φ).trans ht)
    ((X.tgt_inv φ).trans hs) b
  simp only [GroupoidStr.inv_inv] at this
  exact this

/-- **(11.16) and the equivariance of `B_φ`**: `B_φ(g * y) = γ_φ(g) * B_φ(y)` with
`γ_φ(g) = φ ∘ g ∘ φ⁻¹` (`EpGroupoid.conjIsotropy`). -/
theorem transportFiber_smul (φ : MorX) (g : X.Isotropy (X.src φ)) (a : hF.Fiber (X.src φ)) :
    hF.transportFiber φ rfl rfl (g • a) = X.conjIsotropy φ g • hF.transportFiber φ rfl rfl a := by
  refine Fiber.ext ?_
  set ψ₂ := hF.lift g.val a.val (g.src_val.trans a.obj_val.symm)
  have h₁ : X.src φ = F.obj (Y.tgt ψ₂) := by rw [hF.obj_tgt_lift, g.tgt_val]
  set ψ₁ := hF.lift φ (Y.tgt ψ₂) h₁
  set ψ₅ := hF.lift φ a.val a.obj_val.symm
  have h₄ : X.src (X.conjIsotropy φ g).val = F.obj (Y.tgt ψ₅) := by
    rw [(X.conjIsotropy φ g).src_val, hF.obj_tgt_lift]
  set ψ₄ := hF.lift _ (Y.tgt ψ₅) h₄
  have c₁ : Y.src ψ₁ = Y.tgt ψ₂ := hF.src_lift h₁
  have c₄ : Y.src ψ₄ = Y.tgt ψ₅ := hF.src_lift h₄
  have hga : (g • a).val = Y.tgt ψ₂ := hF.smul_val_of _ (hF.mor_lift _) (hF.src_lift _)
  have e₁ : (hF.transportFiber φ rfl rfl (g • a)).val = Y.tgt ψ₁ :=
    hF.transportFiber_val_of rfl rfl (hF.mor_lift h₁) (c₁.trans hga.symm)
  have e₂ : (X.conjIsotropy φ g • hF.transportFiber φ rfl rfl a).val = Y.tgt ψ₄ :=
    hF.smul_val_of _ (hF.mor_lift h₄) (by rw [c₄]; rfl)
  rw [e₁, e₂]
  -- `ψ₁ ∘ ψ₂` and `ψ₄ ∘ ψ₅` both lift `φ ∘ g` at `y`
  have hy : X.src (X.comp φ g.val) = F.obj a.val := by
    rw [X.src_comp _ _ (g.tgt_val.symm), g.src_val, a.obj_val]
  have hA : Y.comp ψ₁ ψ₂ = hF.lift _ a.val hy :=
    hF.eq_lift hy (by rw [F.mor_comp _ _ c₁, hF.mor_lift, hF.mor_lift])
      (by rw [Y.src_comp _ _ c₁, hF.src_lift])
  have hB : Y.comp ψ₄ ψ₅ = hF.lift _ a.val hy := by
    refine hF.eq_lift hy ?_ (by rw [Y.src_comp _ _ c₄, hF.src_lift])
    rw [F.mor_comp _ _ c₄, hF.mor_lift, hF.mor_lift, EpGroupoid.conjIsotropy_val]
    have := GroupoidStr.comp_inv_cancel_right (G := X.toGroupoidStr) (φ := X.inv φ)
      (ψ := X.comp φ g.val) (by rw [X.tgt_inv, X.src_comp _ _ g.tgt_val.symm, g.src_val])
    rwa [GroupoidStr.inv_inv] at this
  have := congrArg Y.tgt (hA.trans hB.symm)
  rwa [Y.tgt_comp _ _ c₁, Y.tgt_comp _ _ c₄] at this

/-- **The functor `φ̃ : G_x ⋉ Y_x → G_{x'} ⋉ Y_{x'}`, `(g, y) ↦ (φ ∘ g ∘ φ⁻¹, B_φ(y))`**
(Lemma 11.6.3). -/
def translationMap (φ : MorX) : hF.Translation (X.src φ) ⥤ hF.Translation (X.tgt φ) where
  obj p := ActionCategory.objEquiv _ _ (hF.transportFiber φ rfl rfl p.back)
  map {p q} f := ⟨X.conjIsotropy φ (hF.homVal _ f), by
    change X.conjIsotropy φ (hF.homVal _ f) • hF.transportFiber φ rfl rfl p.back =
      hF.transportFiber φ rfl rfl q.back
    rw [← hF.transportFiber_smul, hF.homVal_smul]⟩
  map_id p := Subtype.ext (map_one (X.conjIsotropy φ))
  map_comp f g := Subtype.ext (map_mul (X.conjIsotropy φ) (hF.homVal _ g) (hF.homVal _ f))

@[simp] theorem translationMap_obj_back (φ : MorX) (p : hF.Translation (X.src φ)) :
    ((hF.translationMap φ).obj p).back = hF.transportFiber φ rfl rfl p.back := rfl

@[simp] theorem translationMap_map_val (φ : MorX) {p q : hF.Translation (X.src φ)} (f : p ⟶ q) :
    hF.homVal _ ((hF.translationMap φ).map f) = X.conjIsotropy φ (hF.homVal _ f) := rfl

/-- **2021 Lemma 11.6.3, p. 551 (2017: Lemma 11.9, p. 403)**: a morphism `φ : x → x'` of `X`
induces the bijection `B_φ : Y_x → Y_{x'}`, `B_φ(y) = t(ψ)` for `F(ψ) = φ`, `s(ψ) = y`,
equivariant for `γ_φ(g) = φ ∘ g ∘ φ⁻¹`, and the functor `φ̃ : G_x ⋉ Y_x → G_{x'} ⋉ Y_{x'}`,
`(g, y) ↦ (φ ∘ g ∘ φ⁻¹, B_φ(y))`, is bijective on objects and on morphisms (full and faithful), an
equivalence of translation groupoids. -/
theorem lemma_11_6_3 (φ : MorX) :
    Bijective (hF.transportFiber φ rfl rfl) ∧
    (∀ (g : X.Isotropy (X.src φ)) (a : hF.Fiber (X.src φ)),
      hF.transportFiber φ rfl rfl (g • a) = X.conjIsotropy φ g • hF.transportFiber φ rfl rfl a) ∧
    Bijective (hF.translationMap φ).obj ∧ (hF.translationMap φ).Full ∧
    (hF.translationMap φ).Faithful ∧ (hF.translationMap φ).IsEquivalence := by
  have hB := hF.bijective_transportFiber (φ := φ) rfl rfl
  have hobj : Bijective (hF.translationMap φ).obj := by
    change Bijective ((ActionCategory.objEquiv _ _) ∘ (hF.transportFiber φ rfl rfl) ∘
      (ActionCategory.objEquiv _ _).symm)
    exact (ActionCategory.objEquiv _ _).bijective.comp
      (hB.comp (ActionCategory.objEquiv _ _).symm.bijective)
  have hfaith : (hF.translationMap φ).Faithful :=
    ⟨fun {p q} f f' h => hF.hom_ext' _ ((X.conjIsotropy φ).injective
      (congrArg (hF.homVal _) h))⟩
  have hfull : (hF.translationMap φ).Full := by
    refine ⟨fun {p q} h => ?_⟩
    have hh : hF.homVal _ h • hF.transportFiber φ rfl rfl p.back =
      hF.transportFiber φ rfl rfl q.back := hF.homVal_smul _ h
    refine ⟨⟨(X.conjIsotropy φ).symm (hF.homVal _ h), hB.1 ?_⟩,
      hF.hom_ext' _ ((X.conjIsotropy φ).apply_symm_apply _)⟩
    change hF.transportFiber φ rfl rfl ((X.conjIsotropy φ).symm (hF.homVal _ h) • p.back) =
      hF.transportFiber φ rfl rfl q.back
    rw [hF.transportFiber_smul, MulEquiv.apply_symm_apply, hh]
  refine ⟨hB, hF.transportFiber_smul φ, hobj, hfull, hfaith, { essSurj := ⟨fun c => ?_⟩ }⟩
  obtain ⟨a, ha⟩ := hobj.2 c
  exact ⟨a, ⟨eqToIso ha⟩⟩

end EpFunctor.IsProperCovering

end Lift

/-! ### Definitions 11.6.4 and 11.6.5 -/

section CoveringHom

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {ObjY MorY : Type u₁} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type u₂} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type u₃} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type u₄} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type u₅} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type u₆} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}

/-- **2021 Definition 11.6.4 (1), p. 553 (2017: Definition 11.6, p. 404)**: an sc-smooth functor
`(Ψ, Φ) : F → F'` between (proper covering) functors `F : Y → X`, `F' : Y' → X'`: sc-smooth
functors `Ψ : Y → Y'`, `Φ : X → X'` with `Φ ∘ F = F' ∘ Ψ` (on objects and on morphisms). -/
structure ProperCoveringHom (F : EpFunctor Y X) (F' : EpFunctor Y' X') where
  /-- `Ψ : Y → Y'`. -/
  Ψ : EpFunctor Y Y'
  /-- `Φ : X → X'`. -/
  Φ : EpFunctor X X'
  comm_obj : ∀ y, Φ.obj (F.obj y) = F'.obj (Ψ.obj y)
  comm_mor : ∀ ψ, Φ.mor (F.mor ψ) = F'.mor (Ψ.mor ψ)

namespace ProperCoveringHom

variable {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}

theorem ext {Γ Γ' : ProperCoveringHom F F'} (hΨ : Γ.Ψ = Γ'.Ψ) (hΦ : Γ.Φ = Γ'.Φ) : Γ = Γ' := by
  cases Γ; cases Γ'; cases hΨ; cases hΦ; rfl

/-- `Ψ` maps `Y_x = F⁻¹(x)` into `Y'_{Φ(x)}`: it induces `Y(x) → Y'(Φ(x))` (2021 p. 553). -/
theorem mapsTo_fiber (Γ : ProperCoveringHom F F') (x : ObjX) :
    MapsTo Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x}) := fun y hy => by
  change F'.obj (Γ.Ψ.obj y) = Γ.Φ.obj x
  rw [← Γ.comm_obj, show F.obj y = x from hy]

variable (F) in
/-- The identity `(1_Y, 1_X) : F → F`. -/
def id : ProperCoveringHom F F := ⟨EpFunctor.id Y, EpFunctor.id X, fun _ => rfl, fun _ => rfl⟩

/-- The composition `(Ψ₂ ∘ Ψ₁, Φ₂ ∘ Φ₁)`. -/
def comp (Γ₂ : ProperCoveringHom F' F'') (Γ₁ : ProperCoveringHom F F') :
    ProperCoveringHom F F'' where
  Ψ := Γ₂.Ψ.comp Γ₁.Ψ
  Φ := Γ₂.Φ.comp Γ₁.Φ
  comm_obj y := by
    change Γ₂.Φ.obj (Γ₁.Φ.obj (F.obj y)) = F''.obj (Γ₂.Ψ.obj (Γ₁.Ψ.obj y))
    rw [Γ₁.comm_obj, Γ₂.comm_obj]
  comm_mor ψ := by
    change Γ₂.Φ.mor (Γ₁.Φ.mor (F.mor ψ)) = F''.mor (Γ₂.Ψ.mor (Γ₁.Ψ.mor ψ))
    rw [Γ₁.comm_mor, Γ₂.comm_mor]

@[simp] theorem comp_Ψ (Γ₂ : ProperCoveringHom F' F'') (Γ₁ : ProperCoveringHom F F') :
    (Γ₂.comp Γ₁).Ψ = Γ₂.Ψ.comp Γ₁.Ψ := rfl
@[simp] theorem comp_Φ (Γ₂ : ProperCoveringHom F' F'') (Γ₁ : ProperCoveringHom F F') :
    (Γ₂.comp Γ₁).Φ = Γ₂.Φ.comp Γ₁.Φ := rfl

/-- `Ψ : Y(x) → Y'(Φ(x))` is a bijection on objects for every `x` (the subclass noted after
Definition 11.6.4, p. 553). -/
def IsFiberBijective (Γ : ProperCoveringHom F F') : Prop :=
  ∀ x, BijOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x})

/-- **2021 Definition 11.6.4 (2), p. 553 (2017: Definition 11.6, p. 404)**: an equivalence
between proper covering functors is an sc-smooth functor `(Ψ, Φ) : F → F'` with `Ψ` and `Φ`
equivalences of ep-groupoids and `Ψ : Y(x) → Y'(Φ(x))` a bijection on objects for every `x`. -/
structure IsEquivalence (Γ : ProperCoveringHom F F') : Prop where
  isEquivalence_Ψ : Γ.Ψ.IsEquivalence
  isEquivalence_Φ : Γ.Φ.IsEquivalence
  isFiberBijective : Γ.IsFiberBijective

theorem IsEquivalence.id : (ProperCoveringHom.id F).IsEquivalence :=
  ⟨EpFunctor.IsEquivalence.id Y, EpFunctor.IsEquivalence.id X, fun x => by
    change BijOn _root_.id (F.obj ⁻¹' {x}) (F.obj ⁻¹' {x})
    exact bijOn_id _⟩

theorem IsEquivalence.comp {Γ₂ : ProperCoveringHom F' F''} {Γ₁ : ProperCoveringHom F F'}
    (h₂ : Γ₂.IsEquivalence) (h₁ : Γ₁.IsEquivalence) : (Γ₂.comp Γ₁).IsEquivalence :=
  ⟨h₂.isEquivalence_Ψ.comp h₁.isEquivalence_Ψ, h₂.isEquivalence_Φ.comp h₁.isEquivalence_Φ,
    fun x => (h₂.isFiberBijective (Γ₁.Φ.obj x)).comp (h₁.isFiberBijective x)⟩

/-- **The fibre condition of Definition 11.6.4 (2) follows from the others**: if `F` and `F'` are
proper covering functors and `Ψ`, `Φ` are equivalences, then `Ψ : Y_x → Y'_{Φ(x)}` is a bijection
(injective: a `ψ : y₁ → y₂` with `Ψ(ψ) = 1` has `F(ψ) = 1_x` since `Φ` is faithful, so `ψ = 1`
by unique lifting; surjective: for `χ : Ψ(y) → y'` with `y' ∈ Y'_{Φ(x)}` lift a preimage
`φ : F(y) → x` of `F'(χ)` at `y`). -/
theorem isFiberBijective_of_isEquivalence (hF : F.IsProperCovering) (hF' : F'.IsProperCovering)
    (Γ : ProperCoveringHom F F') (hΨ : Γ.Ψ.IsEquivalence) (hΦ : Γ.Φ.IsEquivalence) :
    Γ.IsFiberBijective := by
  intro x
  refine ⟨Γ.mapsTo_fiber x, fun y₁ hy₁ y₂ hy₂ he => ?_, fun y' hy' => ?_⟩
  · have hy₁ : F.obj y₁ = x := hy₁
    have hy₂ : F.obj y₂ = x := hy₂
    obtain ⟨ψ, hψs, hψt, hψ⟩ := hΨ.exists_mor_eq (x := y₁) (x' := y₂)
      (ψ := Y'.unit (Γ.Ψ.obj y₁)) (Y'.src_unit _) ((Y'.tgt_unit _).trans he)
    have hFψ : F.mor ψ = X.unit x := by
      refine hΦ.mor_injective (by rw [F.src_mor, hψs, hy₁, X.src_unit])
        (by rw [F.tgt_mor, hψt, hy₂, X.tgt_unit]) ?_
      rw [Γ.comm_mor, hψ, F'.mor_unit, Γ.Φ.mor_unit, ← Γ.comm_obj, hy₁]
    have h₀ : X.src (X.unit x) = F.obj y₁ := by rw [X.src_unit, hy₁]
    have : ψ = Y.unit y₁ :=
      (hF.existsUnique_lift h₀).unique ⟨hFψ, hψs⟩
        ⟨by rw [F.mor_unit, hy₁], Y.src_unit _⟩
    rw [← hψt, this, Y.tgt_unit]
  · have hy' : F'.obj y' = Γ.Φ.obj x := hy'
    obtain ⟨y, χ, hχs, hχt⟩ := hΨ.exists_iso y'
    obtain ⟨φ, hφs, hφt, hφ⟩ := hΦ.exists_mor_eq (x := F.obj y) (x' := x) (ψ := F'.mor χ)
      (by rw [F'.src_mor, hχs, Γ.comm_obj]) (by rw [F'.tgt_mor, hχt, hy'])
    have h₀ : X.src φ = F.obj y := hφs
    set ψ := hF.lift φ y h₀
    refine ⟨Y.tgt ψ, (hF.obj_tgt_lift h₀).trans hφt, ?_⟩
    have : Γ.Ψ.mor ψ = χ :=
      (hF'.existsUnique_lift (φ := F'.mor χ) (y := Γ.Ψ.obj y) (by rw [F'.src_mor, hχs])).unique
        ⟨by rw [← Γ.comm_mor, hF.mor_lift, hφ], by rw [Γ.Ψ.src_mor, hF.src_lift]⟩ ⟨rfl, hχs⟩
    rw [← Γ.Ψ.tgt_mor, this, hχt]

/-- Definition 11.6.4 (2) for proper covering functors is "`Ψ` and `Φ` are equivalences". -/
theorem isEquivalence_iff (hF : F.IsProperCovering) (hF' : F'.IsProperCovering)
    (Γ : ProperCoveringHom F F') :
    Γ.IsEquivalence ↔ Γ.Ψ.IsEquivalence ∧ Γ.Φ.IsEquivalence :=
  ⟨fun h => ⟨h.isEquivalence_Ψ, h.isEquivalence_Φ⟩, fun h =>
    ⟨h.1, h.2, isFiberBijective_of_isEquivalence hF hF' Γ h.1 h.2⟩⟩

/-- **2021 Definition 11.6.5, p. 554 (2017: Definition 11.7, p. 405)**: a natural transformation
`τ : (ζ, ξ) → (ζ', ξ')` of functors `F → F'` between proper coverings: natural transformations
`τ_Y : ζ → ζ'`, `τ_X : ξ → ξ'` with `τ_X ∘ F = F' ∘ τ_Y` (11.20). -/
structure NatTrans (Γ Γ' : ProperCoveringHom F F') where
  /-- `τ_Y : ζ → ζ'`. -/
  τY : EpNatTrans Γ.Ψ Γ'.Ψ
  /-- `τ_X : ξ → ξ'`. -/
  τX : EpNatTrans Γ.Φ Γ'.Φ
  comm : ∀ y, τX.app (F.obj y) = F'.mor (τY.app y)

/-- Two functors between proper coverings are naturally equivalent, `Γ ≃ Γ'`, if there is a
natural transformation `Γ → Γ'` (as for ep-groupoids, Definition 10.1.4). -/
def NaturallyEquivalent (Γ Γ' : ProperCoveringHom F F') : Prop := Nonempty (NatTrans Γ Γ')

namespace NatTrans

variable {Γ Γ' Γ'' : ProperCoveringHom F F'}

/-- **The diagram after Definition 11.6.5** (p. 555): applying `F'` to the naturality square of
`τ_Y` at `ψ : y₁ → y₂` and using (11.20) gives `τ_X(x₂) ∘ ξ(F(ψ)) = ξ'(F(ψ)) ∘ τ_X(x₁)`,
`xᵢ = F(yᵢ)`. -/
theorem naturality_F (τ : NatTrans Γ Γ') (ψ : MorY) :
    X'.comp (τ.τX.app (F.obj (Y.tgt ψ))) (Γ.Φ.mor (F.mor ψ)) =
      X'.comp (Γ'.Φ.mor (F.mor ψ)) (τ.τX.app (F.obj (Y.src ψ))) := by
  have h := congrArg F'.mor (τ.τY.naturality ψ)
  rw [F'.mor_comp _ _ (by rw [τ.τY.src_app, Γ.Ψ.tgt_mor]),
    F'.mor_comp _ _ (by rw [Γ'.Ψ.src_mor, τ.τY.tgt_app])] at h
  rw [τ.comm, τ.comm, Γ.comm_mor, Γ'.comm_mor]
  exact h

variable (Γ) in
/-- The identity natural transformation. -/
def refl : NatTrans Γ Γ where
  τY := EpNatTrans.refl Γ.Ψ
  τX := EpNatTrans.refl Γ.Φ
  comm y := by
    change X'.unit (Γ.Φ.obj (F.obj y)) = F'.mor (Y'.unit (Γ.Ψ.obj y))
    rw [F'.mor_unit, Γ.comm_obj]

/-- The inverse natural transformation `τ⁻¹`. -/
def symm (τ : NatTrans Γ Γ') : NatTrans Γ' Γ where
  τY := τ.τY.symm
  τX := τ.τX.symm
  comm y := by
    change X'.inv (τ.τX.app (F.obj y)) = F'.mor (Y'.inv (τ.τY.app y))
    rw [GroupoidFunctor.mor_inv, τ.comm]

/-- The composite `τ' ∘ τ`. -/
def trans (τ : NatTrans Γ Γ') (τ' : NatTrans Γ' Γ'') : NatTrans Γ Γ'' where
  τY := τ.τY.trans τ'.τY
  τX := τ.τX.trans τ'.τX
  comm y := by
    change X'.comp (τ'.τX.app (F.obj y)) (τ.τX.app (F.obj y)) =
      F'.mor (Y'.comp (τ'.τY.app y) (τ.τY.app y))
    rw [F'.mor_comp _ _ (by rw [τ'.τY.src_app, τ.τY.tgt_app]), τ.comm, τ'.comm]

end NatTrans

/-- Whiskering on the left: `τ ∘ Λ : Γ ∘ Λ → Γ' ∘ Λ`. -/
def NatTrans.whiskerLeft {Γ Γ' : ProperCoveringHom F' F''} (τ : NatTrans Γ Γ')
    (Λ : ProperCoveringHom F F') : NatTrans (Γ.comp Λ) (Γ'.comp Λ) where
  τY := τ.τY.whiskerLeft Λ.Ψ
  τX := τ.τX.whiskerLeft Λ.Φ
  comm y := by
    change τ.τX.app (Λ.Φ.obj (F.obj y)) = F''.mor (τ.τY.app (Λ.Ψ.obj y))
    rw [Λ.comm_obj, τ.comm]

/-- Whiskering on the right: `Λ ∘ τ : Λ ∘ Γ → Λ ∘ Γ'`. -/
def NatTrans.whiskerRight {Γ Γ' : ProperCoveringHom F F'} (τ : NatTrans Γ Γ')
    (Λ : ProperCoveringHom F' F'') : NatTrans (Λ.comp Γ) (Λ.comp Γ') where
  τY := τ.τY.whiskerRight Λ.Ψ
  τX := τ.τX.whiskerRight Λ.Φ
  comm y := by
    change Λ.Φ.mor (τ.τX.app (F.obj y)) = F''.mor (Λ.Ψ.mor (τ.τY.app y))
    rw [τ.comm, Λ.comm_mor]

theorem naturallyEquivalent_equivalence :
    Equivalence (NaturallyEquivalent (F := F) (F' := F')) :=
  ⟨fun Γ => ⟨NatTrans.refl Γ⟩, fun ⟨τ⟩ => ⟨τ.symm⟩, fun ⟨τ⟩ ⟨τ'⟩ => ⟨τ.trans τ'⟩⟩

theorem NaturallyEquivalent.comp_left {Γ Γ' : ProperCoveringHom F' F''}
    (h : Γ.NaturallyEquivalent Γ') (Λ : ProperCoveringHom F F') :
    (Γ.comp Λ).NaturallyEquivalent (Γ'.comp Λ) :=
  let ⟨τ⟩ := h
  ⟨τ.whiskerLeft Λ⟩

theorem NaturallyEquivalent.comp_right {Γ Γ' : ProperCoveringHom F F'}
    (h : Γ.NaturallyEquivalent Γ') (Λ : ProperCoveringHom F' F'') :
    (Λ.comp Γ).NaturallyEquivalent (Λ.comp Γ') :=
  let ⟨τ⟩ := h
  ⟨τ.whiskerRight Λ⟩

end ProperCoveringHom

end CoveringHom


/-! ### Witnesses -/

namespace CoveringEquivalence.Examples

open EpGroupoid.Examples

/-- **Witness for Lemmas 11.6.2 and 11.6.3**: the identity of the pair groupoid of `ℤ` is a
proper covering (`EpFunctor.isProperCovering_id`) whose fibres `Y_x = {x}` are nonempty. -/
theorem nonempty_fiber_id (x : ℤ) :
    Nonempty ((EpFunctor.isProperCovering_id (X := pairEpGroupoid)).Fiber x) :=
  ⟨EpFunctor.IsProperCovering.Fiber.mk x rfl⟩

/-- **Witness for Definition 11.6.4 (1)**: `(pairToPoint, pairToPoint)`, from the identity
covering of the pair groupoid of `ℤ` to the identity covering of the point. -/
def pairToPointCovering :
    ProperCoveringHom (EpFunctor.id pairEpGroupoid) (EpFunctor.id pointEpGroupoid) :=
  ⟨pairToPoint, pairToPoint, fun _ => rfl, fun _ => rfl⟩

/-- **Witness for Definition 11.6.4 (2)**: `pairToPointCovering` is an equivalence of proper
coverings, although `pairToPoint` has no inverse functor (`not_exists_leftInverse_pairToPoint`). -/
theorem isEquivalence_pairToPointCovering : pairToPointCovering.IsEquivalence :=
  (ProperCoveringHom.isEquivalence_iff EpFunctor.isProperCovering_id
    EpFunctor.isProperCovering_id _).2 ⟨isEquivalence_pairToPoint, isEquivalence_pairToPoint⟩

/-- **Witness for Definition 11.6.5**: the identity natural transformation of
`pairToPointCovering`. -/
theorem naturallyEquivalent_pairToPointCovering :
    pairToPointCovering.NaturallyEquivalent pairToPointCovering :=
  ⟨ProperCoveringHom.NatTrans.refl _⟩

end CoveringEquivalence.Examples

end Polyfold
