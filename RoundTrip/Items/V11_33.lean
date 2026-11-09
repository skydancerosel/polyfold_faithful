import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_33

/-! Round trip for V11_33 (2021 Lemma 11.6.1, p. 549: a proper covering functor is a surjective
local sc-diffeomorphism on morphisms).

The item lists the definition `IsProperCovering.lift` (`α⁻¹`, vocabulary) and six theorems; `A`
is the conjunction of their types, universes at `0` (`B` lives in `Type`): `lemma_11_6_1` (the
lemma), `mor_lift`, `src_lift`, `eq_lift`, `obj_tgt_lift` (the defining properties of the chosen
lift `α⁻¹(φ, y)`) and `existsUnique_lift_tgt` (unique lifts with prescribed target).

* `A_to_B`: `B` is `lemma_11_6_1` (same binders, up to the order of explicit arguments).
* `B_to_A`: `lemma_11_6_1` from `B`.  The five lift lemmas are not consequences of `B` (`B` says
  nothing about lifts); they are re-proved outright from the non-item Chapter 8 lemma
  `IsProperCovering.existsUnique_lift` (unique lifting with prescribed source, which is how
  `lift` is defined), as in the project. -/

namespace RoundTrip.V11_33
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsProperCovering.lemma_11_6_1.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.mor_lift.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.src_lift.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.eq_lift.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.obj_tgt_lift.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.existsUnique_lift_tgt.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.lemma_11_6_1.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.mor_lift.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.src_lift.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.eq_lift.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.obj_tgt_lift.{0, 0},
    @Polyfold.EpFunctor.IsProperCovering.existsUnique_lift_tgt.{0, 0}⟩

theorem A_to_B : A → B := by
  intro hA ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
  exact hA.1 hF

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Lemma 11.6.1, from `B`
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF
    exact hB ObjY MorY ObjX MorX Y X F hF
  · -- `F(α⁻¹(φ, y)) = φ` (outright: `lift` is a choice from `existsUnique_lift`)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ y h
    exact (hF.existsUnique_lift h).exists.choose_spec.1
  · -- `s(α⁻¹(φ, y)) = y` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ y h
    exact (hF.existsUnique_lift h).exists.choose_spec.2
  · -- uniqueness (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ y h ψ hm hs
    exact (hF.existsUnique_lift h).unique ⟨hm, hs⟩ (hF.existsUnique_lift h).exists.choose_spec
  · -- `F(t(α⁻¹(φ, y))) = t(φ)` (outright)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ y h
    change F.obj (Y.tgt (hF.existsUnique_lift h).exists.choose) = X.tgt φ
    rw [← F.tgt_mor, (hF.existsUnique_lift h).exists.choose_spec.1]
  · -- unique lifts with prescribed target (outright: invert a lift of `φ⁻¹`)
    intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F hF φ y h
    have h' : X.src (X.inv φ) = F.obj y := by rw [X.src_inv, h]
    obtain ⟨χ, ⟨hχm, hχs⟩, hχu⟩ := hF.existsUnique_lift h'
    refine ⟨Y.inv χ, ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · rw [GroupoidFunctor.mor_inv, hχm, GroupoidStr.inv_inv]
    · rw [Y.tgt_inv, hχs]
    · have : Y.inv ψ = χ :=
        hχu _ ⟨by rw [GroupoidFunctor.mor_inv, hψ.1], by rw [Y.src_inv, hψ.2]⟩
      rw [← this, GroupoidStr.inv_inv]

#rt_check RoundTrip.V11_33.A_to_B [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_1,
  Polyfold.EpFunctor.IsProperCovering.mor_lift, Polyfold.EpFunctor.IsProperCovering.src_lift,
  Polyfold.EpFunctor.IsProperCovering.eq_lift, Polyfold.EpFunctor.IsProperCovering.obj_tgt_lift,
  Polyfold.EpFunctor.IsProperCovering.existsUnique_lift_tgt]
#rt_check RoundTrip.V11_33.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_1,
  Polyfold.EpFunctor.IsProperCovering.mor_lift, Polyfold.EpFunctor.IsProperCovering.src_lift,
  Polyfold.EpFunctor.IsProperCovering.eq_lift, Polyfold.EpFunctor.IsProperCovering.obj_tgt_lift,
  Polyfold.EpFunctor.IsProperCovering.existsUnique_lift_tgt]
#rt_overlap RoundTrip.V11_33.B_to_A [Polyfold.EpFunctor.IsProperCovering.lemma_11_6_1,
  Polyfold.EpFunctor.IsProperCovering.mor_lift, Polyfold.EpFunctor.IsProperCovering.src_lift,
  Polyfold.EpFunctor.IsProperCovering.eq_lift, Polyfold.EpFunctor.IsProperCovering.obj_tgt_lift,
  Polyfold.EpFunctor.IsProperCovering.existsUnique_lift_tgt]

end RoundTrip.V11_33
