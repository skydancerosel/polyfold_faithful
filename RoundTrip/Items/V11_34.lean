import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_34

/-! Round trip for V11_34 (2021 Lemma 11.6.2, p. 551, and the action (11.15), p. 550; 2017:
Lemma 11.8: `G_x` acts on `Y_x` by `g * y = t(α⁻¹(g, y))`, and `Y(x) ≅ G_x ⋉ Y_x`).

The item lists the definitions `Fiber`, `Fiber.val`, `Fiber.mk`, `fiberSMul`,
`instMulActionFiber`, `FiberFull`, `Translation`, `toTranslation` (vocabulary) and six theorems;
`A` is the conjunction of their types, universes at `0` (`B` lives in `Type`): `lemma_11_6_2`,
`fiberSMul_val_of`, `smul_val_of` (the action is `t` of the unique lift),
`bijective_toTranslation_obj`, `full_toTranslation`, `faithful_toTranslation`.

* `A_to_B`: (0) is the non-item Chapter 8 lemma `IsProperCovering.existsUnique_lift`.  The bridge:
  `B`'s chosen `α⁻¹(g, y)` is a lift, so `smul_val_of` (from `A`) identifies `B`'s `smulB F g y`
  with the project's `(g • y).val`; then (1) is the `MulAction` structure of `A`'s
  `instMulActionFiber` (`Fiber.obj_val`, `one_smul`, `mul_smul`).  (2): targets from
  `smul_val_of`; injectivity from `faithful_toTranslation`; surjectivity from
  `full_toTranslation` and the third conjunct of `lemma_11_6_2` (`α` on morphisms); units and
  composition are the functor laws of `F` (`F.mor_unit`, `F.mor_comp`).
* `B_to_A`: `fiberSMul_val_of` and `smul_val_of` from `B` (0) (unique lifting identifies the
  project's `lift` with any lift); `faithful_toTranslation` from `B` (2) injectivity;
  `full_toTranslation` from `B` (2) surjectivity and `smul_val_of`; `lemma_11_6_2` from these
  (its first three conjuncts are `rfl`, the equivalence from full, faithful and bijective on
  objects).  `bijective_toTranslation_obj` is about the project's encoding of objects
  (`ActionCategory.objEquiv ∘ Fiber.mk`) and is re-proved outright (two lines).

Harness: `A`'s statement mentions `instMulActionFiber` (in `g • a`) and `toTranslation`, whose proof
fields use the banned `fiberSMul_val_of` and `smul_val_of`.  So plain `#rt_check` fails on both
directions (recorded with `#guard_msgs`), and `#rt_check_soft` passes. -/

namespace RoundTrip.V11_34
open Polyfold CategoryTheory Function

/-- The project's statement (universes at `0`), one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2.{0, 0}
def A2 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of.{0, 0}
def A3 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.smul_val_of.{0, 0}
def A4 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj.{0, 0}
def A5 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.full_toTranslation.{0, 0}
def A6 : Prop := type_of% @Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation.{0, 0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.smul_val_of.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.full_toTranslation.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation.{0, 0}⟩

open EpFunctor.IsProperCovering in
theorem A_to_B : A → B := by
  rintro ⟨h1, -, h3, -, h5, h6⟩
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
  -- (0) unique lifting (Chapter 8)
  have h0 : ∀ (φ : MorX) (y : ObjY), X.src φ = F.obj y →
      ∃! ψ : MorY, F.mor ψ = φ ∧ Y.src ψ = y := fun φ y h => hF.existsUnique_lift h
  -- `B`'s chosen `α⁻¹(φ, y)` is a lift
  have hα : ∀ (φ : MorX) (y : ObjY), X.src φ = F.obj y →
      F.mor (alphaInvB F φ y) = φ ∧ Y.src (alphaInvB F φ y) = y := by
    intro φ y h
    have hex : ∃ ψ : MorY, F.mor ψ = φ ∧ Y.src ψ = y := (h0 φ y h).exists
    unfold alphaInvB
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  -- the bridge: `B`'s `g * y` is the project's `g • y`
  have hbridge : ∀ (x : ObjX) (g : MorX) (hg : g ∈ isoB X x) (y : ObjY) (hy : y ∈ F.obj ⁻¹' {x}),
      smulB F g y = ((⟨g, hg.1, hg.2⟩ : X.Isotropy x) • (Fiber.mk (hF := hF) y hy)).val := by
    intro x g hg y hy
    have h : X.src g = F.obj y := hg.1.trans (show F.obj y = x from hy).symm
    exact (h3 hF x (g := ⟨g, hg.1, hg.2⟩) (a := Fiber.mk y hy) (hα g y h).1 (hα g y h).2).symm
  refine ⟨h0, fun x => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- (1) `g * y ∈ Y_x`
    intro g hg y hy
    rw [hbridge x g hg y hy]
    exact Fiber.obj_val _
  · -- (1) `1_x * y = y`
    intro y hy
    rw [hbridge x (X.unit x) ⟨X.src_unit x, X.tgt_unit x⟩ y hy]
    change ((1 : X.Isotropy x) • Fiber.mk (hF := hF) y hy).val = y
    rw [one_smul]
    rfl
  · -- (1) `(g ∘ h) * y = g * (h * y)`
    intro g hg h hh y hy
    have hgh : X.comp g h ∈ isoB X x :=
      ⟨(X.src_comp _ _ (hg.1.trans hh.2.symm)).trans hh.1,
        (X.tgt_comp _ _ (hg.1.trans hh.2.symm)).trans hg.2⟩
    rw [hbridge x _ hgh y hy, hbridge x h hh y hy, hbridge x g hg _ (Fiber.obj_val _)]
    change (((⟨g, hg.1, hg.2⟩ : X.Isotropy x) * ⟨h, hh.1, hh.2⟩) •
      Fiber.mk (hF := hF) y hy).val = _
    rw [mul_smul]
    rfl
  · -- (2) `ψ : y → y'` goes to `(F ψ, y) : y → F(ψ) * y = y'`
    intro ψ hs ht
    have hmem : F.mor ψ ∈ isoB X x := ⟨by rw [F.src_mor, hs], by rw [F.tgt_mor, ht]⟩
    refine ⟨hmem, ?_⟩
    rw [hbridge x (F.mor ψ) hmem (Y.src ψ) hs]
    exact (h3 hF x (g := ⟨F.mor ψ, hmem.1, hmem.2⟩) (a := Fiber.mk (Y.src ψ) hs) rfl rfl).symm
  · -- (2) injective on morphisms: `faithful_toTranslation`
    intro ψ ψ' hs ht hs' ht' hm hsrc
    have htgt : Y.tgt ψ = Y.tgt ψ' := by
      have e : ∀ χ : MorY, ∀ (hs : F.obj (Y.src χ) = x) (ht : F.obj (Y.tgt χ) = x),
          Y.tgt χ = smulB F (F.mor χ) (Y.src χ) := by
        intro χ hs ht
        have hmem : F.mor χ ∈ isoB X x := ⟨by rw [F.src_mor, hs], by rw [F.tgt_mor, ht]⟩
        rw [hbridge x (F.mor χ) hmem (Y.src χ) hs]
        exact (h3 hF x (g := ⟨F.mor χ, hmem.1, hmem.2⟩) (a := Fiber.mk (Y.src χ) hs) rfl rfl).symm
      rw [e ψ hs ht, e ψ' hs' ht', hm, hsrc]
    let a : FiberFull (F := F) x := ⟨Y.src ψ, hs⟩
    let b : FiberFull (F := F) x := ⟨Y.tgt ψ, ht⟩
    let m : a ⟶ b := ⟨ψ, rfl, rfl⟩
    let m' : a ⟶ b := ⟨ψ', hsrc.symm, htgt.symm⟩
    have hmap : (hF.toTranslation x).map m = (hF.toTranslation x).map m' :=
      Subtype.ext (GroupoidStr.Isotropy.ext (((h1 hF x).2.2.1 m).trans
        (hm.trans ((h1 hF x).2.2.1 m').symm)))
    exact congrArg (fun f : a ⟶ b => f.1) ((h6 hF x).map_injective hmap)
  · -- (2) surjective on morphisms: `full_toTranslation`
    intro g hg y hy
    let gI : X.Isotropy x := ⟨g, hg.1, hg.2⟩
    let a : FiberFull (F := F) x := ⟨y, hy⟩
    let b : FiberFull (F := F) x := ⟨(gI • Fiber.mk (hF := hF) y hy).val, Fiber.obj_val _⟩
    let f : (hF.toTranslation x).obj a ⟶ (hF.toTranslation x).obj b := ⟨gI, rfl⟩
    obtain ⟨m, hmf⟩ := (h5 hF x).map_surjective f
    refine ⟨m.1, ?_, m.2.1, ?_⟩
    · rw [show Y.tgt m.1 = b.val from m.2.2]
      exact Fiber.obj_val _
    · have := (h1 hF x).2.2.1 m
      rw [hmf] at this
      exact this.symm
  · -- (2) units: the functor law of `F`
    intro y hy
    rw [F.mor_unit, show F.obj y = x from hy]
  · -- (2) composition: the functor law of `F`
    intro ψ ψ' _ _ hc _
    exact ⟨F.mor_comp _ _ hc, Y.src_comp _ _ hc⟩

open EpFunctor.IsProperCovering in
theorem B_to_A : B → A := by
  intro hB
  -- the action is `t` of a lift (from `B` (0): any lift is the project's `lift`)
  have hA2 : A2 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x g a ψ hm hs
    have h : X.src g.val = F.obj a.val := g.src_val.trans a.obj_val.symm
    exact congrArg Y.tgt (((hB ObjY MorY ObjX MorX Y X F hF).1 g.val a.val h).unique
      ⟨hF.mor_lift h, hF.src_lift h⟩ ⟨hm, hs⟩)
  have hA3 : A3 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x g a ψ hm hs
    exact hA2 hF x hm hs
  -- bijective on objects (outright: the project's encoding of objects)
  have hA4 : A4 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    change Bijective ((ActionCategory.objEquiv _ _) ∘ fun a : FiberFull (F := F) x =>
      (Fiber.mk (hF := hF) a.val a.mem))
    refine (ActionCategory.objEquiv _ _).bijective.comp
      ⟨fun a b h => GroupoidStr.FullOb.ext (congrArg Fiber.val h),
        fun c => ⟨⟨c.val, c.obj_val⟩, Fiber.ext rfl⟩⟩
  -- full, from `B` (2) surjectivity
  have hA5 : A5 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    obtain ⟨-, hBx⟩ := hB ObjY MorY ObjX MorX Y X F hF
    obtain ⟨-, -, -, -, -, hsurj, -, -⟩ := hBx x
    refine ⟨fun {a b} g => ?_⟩
    have hg : hF.homVal x g • Fiber.mk (hF := hF) a.val a.mem = Fiber.mk b.val b.mem :=
      hF.homVal_smul x g
    obtain ⟨ψ, -, hψs, hψm⟩ := hsurj (hF.homVal x g).val
      ⟨(hF.homVal x g).src_val, (hF.homVal x g).tgt_val⟩ a.val a.mem
    have ht : Y.tgt ψ = b.val := by
      have := congrArg Fiber.val hg
      rwa [hA3 hF x (a := Fiber.mk a.val a.mem) hψm hψs] at this
    exact ⟨⟨ψ, hψs, ht⟩, Subtype.ext (GroupoidStr.Isotropy.ext hψm)⟩
  -- faithful, from `B` (2) injectivity
  have hA6 : A6 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    obtain ⟨-, hBx⟩ := hB ObjY MorY ObjX MorX Y X F hF
    obtain ⟨-, -, -, -, hinj, -, -, -⟩ := hBx x
    refine ⟨fun {a b} ψ ψ' h => ?_⟩
    have hm : F.mor ψ.1 = F.mor ψ'.1 :=
      congrArg (fun g : X.Isotropy x => g.val) (congrArg Subtype.val h)
    have hs : Y.src ψ.1 = a.val := ψ.2.1
    have ht : Y.tgt ψ.1 = b.val := ψ.2.2
    have hs' : Y.src ψ'.1 = a.val := ψ'.2.1
    have ht' : Y.tgt ψ'.1 = b.val := ψ'.2.2
    exact Subtype.ext (hinj ψ.1 ψ'.1 (by rw [hs]; exact a.mem) (by rw [ht]; exact b.mem)
      (by rw [hs']; exact a.mem) (by rw [ht']; exact b.mem) hm (hs.trans hs'.symm))
  have hA1 : A1 := by
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF x
    have hfull := hA5 hF x
    have hfaith := hA6 hF x
    refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, hA4 hF x, hfull, hfaith,
      { essSurj := ⟨fun c => ?_⟩ }⟩
    obtain ⟨a, ha⟩ := (hA4 hF x).2 c
    exact ⟨a, ⟨eqToIso ha⟩⟩
  exact ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩

/-! ### Harness checks

The statements `A1`, `A3` contain `g • a`, i.e. the instance `instMulActionFiber`, whose proof
fields (`one_smul`, `mul_smul`) use the banned `fiberSMul_val_of`; `A1`, `A4`–`A6` contain
`toTranslation`, whose proof field (in `map`) uses the banned `smul_val_of`.  So every term
mentioning `A` reaches them and plain `#rt_check` fails on both directions; `#rt_check_soft`
passes. -/

/--
error: rt_check FAIL: RoundTrip.V11_34.A_to_B uses [Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of, Polyfold.EpFunctor.IsProperCovering.smul_val_of]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_34.A_to_B [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2,
  Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of,
  Polyfold.EpFunctor.IsProperCovering.smul_val_of,
  Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj,
  Polyfold.EpFunctor.IsProperCovering.full_toTranslation,
  Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation]

/--
error: rt_check FAIL: RoundTrip.V11_34.B_to_A uses [Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of, Polyfold.EpFunctor.IsProperCovering.smul_val_of]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_34.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2,
  Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of,
  Polyfold.EpFunctor.IsProperCovering.smul_val_of,
  Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj,
  Polyfold.EpFunctor.IsProperCovering.full_toTranslation,
  Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation]

#rt_check_soft RoundTrip.V11_34.A_to_B [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2,
  Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of,
  Polyfold.EpFunctor.IsProperCovering.smul_val_of,
  Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj,
  Polyfold.EpFunctor.IsProperCovering.full_toTranslation,
  Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation]
#rt_check_soft RoundTrip.V11_34.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2,
  Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of,
  Polyfold.EpFunctor.IsProperCovering.smul_val_of,
  Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj,
  Polyfold.EpFunctor.IsProperCovering.full_toTranslation,
  Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation]
#rt_overlap RoundTrip.V11_34.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2,
  Polyfold.EpFunctor.IsProperCovering.fiberSMul_val_of,
  Polyfold.EpFunctor.IsProperCovering.smul_val_of,
  Polyfold.EpFunctor.IsProperCovering.bijective_toTranslation_obj,
  Polyfold.EpFunctor.IsProperCovering.full_toTranslation,
  Polyfold.EpFunctor.IsProperCovering.faithful_toTranslation]

end RoundTrip.V11_34
