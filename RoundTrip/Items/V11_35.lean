import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_35

/-! Round trip for V11_35 (2021 Lemma 11.6.3, pp. 551–552; 2017: Lemma 11.9: a morphism
`φ : x → x'` gives an equivariant bijection `B_φ : Y_x → Y_{x'}` and an isomorphism
`φ̃ : G_x ⋉ Y_x → G_{x'} ⋉ Y_{x'}`).

The item lists the definitions `transportFiber` (`B_φ`), `translationMap` (`φ̃`) and
`EpGroupoid.conjIsotropy` (`g ↦ φ ∘ g ∘ φ⁻¹`, a `MulEquiv`), as vocabulary, and five theorems; `A`
is the conjunction of their types, universes at `0`: `lemma_11_6_3`, `transportFiber_val_of`,
`transportFiber_inv_transportFiber`, `bijective_transportFiber`, `transportFiber_smul`.

Bridges (proved below without the item's theorems): `B`'s chosen lift `alphaInvB F φ y` is the
project's `lift` (`eq_lift`, Lemma 11.6.1's item, not this one), so `B`'s `transportB F φ y` is
`(transportFiber φ _ _ y).val`, `B`'s `smulB F g y` is `(g • y).val`, and `B`'s
`conjB X φ g = φ ∘ (g ∘ φ⁻¹)` is `(conjIsotropy φ g).val = (φ ∘ g) ∘ φ⁻¹` (associativity).

* `A_to_B`: `B_φ` bijective from `bijective_transportFiber` (with `transportFiber_val_of` for the
  bridge); `c_φ` bijective, unital and multiplicative from the `MulEquiv` structure of the
  definition `conjIsotropy`; equivariance from `transportFiber_smul`; `φ̃` bijective on
  `G_x × Y_x` by `Set.BijOn.prodMap`.
* `B_to_A`: `bijective_transportFiber` and `transportFiber_smul` from `B`;
  `transportFiber_val_of` and `transportFiber_inv_transportFiber` are statements about arbitrary
  lifts and `B_{φ⁻¹}`, not consequences of `B`, re-proved outright (two and four lines, from
  `eq_lift`); `lemma_11_6_3` from these (the project's argument: `φ̃` is bijective on objects,
  faithful and full since `conjIsotropy` is a `MulEquiv`).

Harness: `lemma_11_6_3`'s statement mentions `translationMap`, whose proof field (in `map`) uses
the banned `transportFiber_smul` (and through it `transportFiber_val_of`).  So plain `#rt_check` fails on both directions (recorded with
`#guard_msgs`) and `#rt_check_soft` passes. -/

namespace RoundTrip.V11_35
open Polyfold CategoryTheory Function

/-- The project's statement (universes at `0`), one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3.{0, 0}
def A2 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of.{0, 0}
def A3 : Prop :=
  type_of% @Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber.{0, 0}
def A4 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber.{0, 0}
def A5 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.transportFiber_smul.{0, 0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.transportFiber_smul.{0, 0}⟩

/-! ### Bridges between `B`'s notions and the project's -/

section Bridge

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}

open EpFunctor.IsProperCovering

/-- `B`'s chosen `α⁻¹(φ, y)` is a lift. -/
theorem alphaInvB_spec (hF : F.IsProperCovering) {φ : MorX} {y : ObjY}
    (h : X.src φ = F.obj y) : F.mor (alphaInvB F φ y) = φ ∧ Y.src (alphaInvB F φ y) = y := by
  have hex : ∃ ψ : MorY, F.mor ψ = φ ∧ Y.src ψ = y := (hF.existsUnique_lift h).exists
  unfold alphaInvB
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- `B`'s chosen `α⁻¹(φ, y)` is the project's `lift`. -/
theorem alphaInvB_eq_lift (hF : F.IsProperCovering) {φ : MorX} {y : ObjY}
    (h : X.src φ = F.obj y) : alphaInvB F φ y = hF.lift φ y h :=
  hF.eq_lift h (alphaInvB_spec hF h).1 (alphaInvB_spec hF h).2

/-- `B`'s `B_φ` is the project's `transportFiber`. -/
theorem transportB_eq (hF : F.IsProperCovering) {φ : MorX} {x x' : ObjX} (hs : X.src φ = x)
    (ht : X.tgt φ = x') (a : hF.Fiber x) :
    transportB F φ a.val = (hF.transportFiber φ hs ht a).val := by
  unfold transportB
  rw [alphaInvB_eq_lift hF (hs.trans a.obj_val.symm)]
  rfl

/-- `B`'s action is the project's. -/
theorem smulB_eq (hF : F.IsProperCovering) {x : ObjX} (g : X.Isotropy x) (a : hF.Fiber x) :
    smulB F g.val a.val = (g • a).val := by
  unfold smulB
  rw [alphaInvB_eq_lift hF (g.src_val.trans a.obj_val.symm)]
  rfl

omit [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY] [TopologicalSpace MorY]
  [T2Space MorY] [ParacompactSpace MorY] in
/-- `B`'s conjugation is the project's. -/
theorem conjB_eq (X : EpGroupoid ObjX MorX) (φ : MorX) (g : X.Isotropy (X.src φ)) :
    conjB X φ g.val = (X.conjIsotropy φ g).val := by
  rw [EpGroupoid.conjIsotropy_val,
    X.comp_assoc _ _ _ g.tgt_val.symm (g.src_val.trans (X.tgt_inv φ).symm)]
  rfl

end Bridge

open EpFunctor.IsProperCovering in
theorem A_to_B : A → B := by
  rintro ⟨-, h2, -, h4, h5⟩
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ x x' hs ht
  subst hs; subst ht
  -- `B_φ` through `transportFiber_val_of`
  have htr : ∀ (y : ObjY) (hy : F.obj y = X.src φ),
      transportB F φ y = (hF.transportFiber φ rfl rfl (Fiber.mk y hy)).val := fun y hy =>
    (h2 hF rfl rfl (a := Fiber.mk y hy) (alphaInvB_spec hF hy.symm).1
      (alphaInvB_spec hF hy.symm).2).symm
  have hconj : ∀ (g : MorX) (hg : g ∈ isoB X (X.src φ)),
      conjB X φ g = (X.conjIsotropy φ ⟨g, hg.1, hg.2⟩).val := fun g hg =>
    conjB_eq X φ ⟨g, hg.1, hg.2⟩
  have hbij := h4 hF (φ := φ) rfl rfl
  -- `B_φ : Y_x → Y_{x'}` is a bijection
  have hB1 : Set.BijOn (transportB F φ) (F.obj ⁻¹' {X.src φ}) (F.obj ⁻¹' {X.tgt φ}) := by
    refine ⟨fun y hy => ?_, fun y hy y' hy' he => ?_, fun y' hy' => ?_⟩
    · rw [htr y hy]; exact Fiber.obj_val _
    · rw [htr y hy, htr y' hy'] at he
      exact congrArg Fiber.val (hbij.1 (Fiber.ext he))
    · obtain ⟨a, ha⟩ := hbij.2 (Fiber.mk y' hy')
      refine ⟨a.val, a.obj_val, ?_⟩
      rw [htr a.val a.obj_val]
      exact congrArg Fiber.val ha
  -- `c_φ : G_x → G_{x'}` is a bijection (the `MulEquiv` `conjIsotropy`)
  have hB2 : Set.BijOn (conjB X φ) (isoB X (X.src φ)) (isoB X (X.tgt φ)) := by
    refine ⟨fun g hg => ?_, fun g hg g' hg' he => ?_, fun g' hg' => ?_⟩
    · rw [hconj g hg]
      exact ⟨(X.conjIsotropy φ _).src_val, (X.conjIsotropy φ _).tgt_val⟩
    · rw [hconj g hg, hconj g' hg'] at he
      exact congrArg GroupoidStr.Isotropy.val
        ((X.conjIsotropy φ).injective (GroupoidStr.Isotropy.ext he))
    · let k := (X.conjIsotropy φ).symm ⟨g', hg'.1, hg'.2⟩
      refine ⟨k.val, ⟨k.src_val, k.tgt_val⟩, ?_⟩
      rw [hconj k.val ⟨k.src_val, k.tgt_val⟩]
      exact congrArg GroupoidStr.Isotropy.val ((X.conjIsotropy φ).apply_symm_apply _)
  refine ⟨hB1, hB2, ?_, ?_, ?_, hB2.prodMap hB1⟩
  · -- `c_φ(1_x) = 1_{x'}`
    rw [hconj (X.unit _) ⟨X.src_unit _, X.tgt_unit _⟩]
    change (X.conjIsotropy φ 1).val = _
    rw [map_one]
    rfl
  · -- `c_φ(g' ∘ g) = c_φ(g') ∘ c_φ(g)`
    intro g hg g' hg'
    have hc : X.comp g' g ∈ isoB X (X.src φ) :=
      ⟨(X.src_comp _ _ (hg'.1.trans hg.2.symm)).trans hg.1,
        (X.tgt_comp _ _ (hg'.1.trans hg.2.symm)).trans hg'.2⟩
    rw [hconj _ hc, hconj g' hg', hconj g hg]
    change (X.conjIsotropy φ ((⟨g', hg'.1, hg'.2⟩ : X.Isotropy (X.src φ)) * ⟨g, hg.1, hg.2⟩)).val = _
    rw [map_mul]
    rfl
  · -- equivariance: `transportFiber_smul`
    intro g hg y hy
    have e1 : smulB F g y =
        ((⟨g, hg.1, hg.2⟩ : X.Isotropy (X.src φ)) • Fiber.mk (hF := hF) y hy).val :=
      smulB_eq hF ⟨g, hg.1, hg.2⟩ (Fiber.mk y hy)
    rw [e1, htr _ (Fiber.obj_val _), htr y hy, hconj g hg,
      smulB_eq hF (X.conjIsotropy φ _) (hF.transportFiber φ rfl rfl (Fiber.mk y hy))]
    exact congrArg Fiber.val (h5 hF φ _ _)

open EpFunctor.IsProperCovering in
theorem B_to_A : B → A := by
  intro hB
  -- outright (a statement about arbitrary lifts)
  have hA2 : A2 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ x x' hs ht a ψ hm hsψ
    exact congrArg Y.tgt (hF.eq_lift (hs.trans a.obj_val.symm) hm hsψ).symm
  -- outright (`B_{φ⁻¹}` is the inverse)
  have hA3 : A3 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ x x' hs ht a
    refine Fiber.ext ?_
    have hm : F.mor (Y.inv (hF.lift φ a.val (hs.trans a.obj_val.symm))) = X.inv φ := by
      rw [GroupoidFunctor.mor_inv, hF.mor_lift]
    have hsψ : Y.src (Y.inv (hF.lift φ a.val (hs.trans a.obj_val.symm))) =
        (hF.transportFiber φ hs ht a).val := by
      rw [Y.src_inv]; rfl
    rw [hA2 hF ((X.src_inv φ).trans ht) ((X.tgt_inv φ).trans hs) hm hsψ, Y.tgt_inv, hF.src_lift]
  -- `B_φ` is bijective: from `B`
  have hA4 : A4 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ x x' hs ht
    have hb := (hB ObjY MorY ObjX MorX Y X F hF φ x x' hs ht).1
    refine ⟨fun a b he => Fiber.ext (hb.2.1 a.obj_val b.obj_val ?_), fun c => ?_⟩
    · rw [transportB_eq hF hs ht a, transportB_eq hF hs ht b, he]
    · obtain ⟨y, hy, hyc⟩ := hb.2.2 c.obj_val
      refine ⟨Fiber.mk y hy, Fiber.ext ?_⟩
      rw [← transportB_eq hF hs ht]
      exact hyc
  -- equivariance: from `B`
  have hA5 : A5 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ g a
    have hb := (hB ObjY MorY ObjX MorX Y X F hF φ _ _ rfl rfl).2.2.2.2.1 g.val
      ⟨g.src_val, g.tgt_val⟩ a.val a.obj_val
    refine Fiber.ext ?_
    have e1 : (hF.transportFiber φ rfl rfl (g • a)).val =
        transportB F φ (smulB F g.val a.val) := by
      rw [smulB_eq hF g a]; exact (transportB_eq hF rfl rfl (g • a)).symm
    have e2 : (X.conjIsotropy φ g • hF.transportFiber φ rfl rfl a).val =
        smulB F (conjB X φ g.val) (transportB F φ a.val) := by
      rw [conjB_eq, transportB_eq hF rfl rfl a, smulB_eq hF]
    rw [e1, e2]
    exact hb
  -- Lemma 11.6.3 (the project's argument, with `hA4`, `hA5`)
  have hA1 : A1 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ
    have hB' := hA4 hF (φ := φ) rfl rfl
    have hobj : Bijective (hF.translationMap φ).obj := by
      change Bijective ((ActionCategory.objEquiv _ _) ∘ (hF.transportFiber φ rfl rfl) ∘
        (ActionCategory.objEquiv _ _).symm)
      exact (ActionCategory.objEquiv _ _).bijective.comp
        (hB'.comp (ActionCategory.objEquiv _ _).symm.bijective)
    have hfaith : (hF.translationMap φ).Faithful :=
      ⟨fun {p q} f f' h => hF.hom_ext' _ ((X.conjIsotropy φ).injective
        (congrArg (hF.homVal _) h))⟩
    have hfull : (hF.translationMap φ).Full := by
      refine ⟨fun {p q} h => ?_⟩
      have hh : hF.homVal _ h • hF.transportFiber φ rfl rfl p.back =
        hF.transportFiber φ rfl rfl q.back := hF.homVal_smul _ h
      refine ⟨⟨(X.conjIsotropy φ).symm (hF.homVal _ h), hB'.1 ?_⟩,
        hF.hom_ext' _ ((X.conjIsotropy φ).apply_symm_apply _)⟩
      change hF.transportFiber φ rfl rfl ((X.conjIsotropy φ).symm (hF.homVal _ h) • p.back) =
        hF.transportFiber φ rfl rfl q.back
      rw [hA5 hF φ, MulEquiv.apply_symm_apply, hh]
    refine ⟨hB', hA5 hF φ, hobj, hfull, hfaith, { essSurj := ⟨fun c => ?_⟩ }⟩
    obtain ⟨a, ha⟩ := hobj.2 c
    exact ⟨a, ⟨eqToIso ha⟩⟩
  exact ⟨hA1, hA2, hA3, hA4, hA5⟩

/-! ### Harness checks

`A1` (`lemma_11_6_3`) contains `translationMap`, whose proof field (the `map` field's proof that
`φ̃(g, y)` has the right target) uses the banned `transportFiber_smul` (and, through its proof, the
banned `transportFiber_val_of`).  So every term mentioning
`A` reaches it and plain `#rt_check` fails on both directions; `#rt_check_soft` passes. -/

/--
error: rt_check FAIL: RoundTrip.V11_35.A_to_B uses [Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
 Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_35.A_to_B [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]

/--
error: rt_check FAIL: RoundTrip.V11_35.B_to_A uses [Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
 Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_35.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]

#rt_check_soft RoundTrip.V11_35.A_to_B [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]
#rt_check_soft RoundTrip.V11_35.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]
#rt_overlap RoundTrip.V11_35.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_val_of,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_inv_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber,
  Polyfold.EpFunctor.IsProperCovering.transportFiber_smul]

end RoundTrip.V11_35
