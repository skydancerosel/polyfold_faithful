import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_23

/-! Round trip for V8_23 (Definition 8.3.2 = 2017 Definition 8.5: strong bundle maps between
strong bundles over ep-groupoids).

The item lists the definition `EpStrongBundle.IsMap` (vocabulary) and the non-vacuity theorem
`EpStrongBundle.isMap_id` (the identity of `W` is a strong bundle map covering the identity
functor).  `A` is the type of `isMap_id`, universes at `0`.

`B` says (a) `IsMap E E' φ Φ ↔ IsMapB E E' φ Φ` (B's literal reading: an `IsStrongBundleMap`
covering `φ.obj` plus `Φ(μ(γ, w)) = μ'(φ(γ), Φ(w))`, the membership of `(φ γ, Φ w)` in the fibred
product passed as a hypothesis) and (b) the well-definedness remark.

* `A_to_B`: `B` is proved outright (`B_holds`): (a) is a repackaging of the two fields of the
  structure `IsMap` (the membership proofs agree by proof irrelevance), (b) is
  `covers` + `φ.src_mor`.  The hypothesis `A` is not used (it says nothing about the definition).
* `B_to_A`: the backward half of (a) applied to the identity, with
  `StrongBundle.IsStrongBundleMap.id` (Part II infrastructure, not an item theorem) and `rfl`. -/

namespace RoundTrip.V8_23
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop := type_of% @Polyfold.EpStrongBundle.isMap_id.{0, 0}

theorem A_holds : A := @Polyfold.EpStrongBundle.isMap_id.{0, 0}

/-- `B` holds outright: the project's `IsMap` is B's `IsMapB`. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' E E' φ Φ
  refine ⟨⟨fun h => ⟨h.isStrongBundleMap, fun γ w hw _ => h.map_μ γ w hw⟩,
    fun h => ⟨h.1, fun γ w hw => h.2 γ w hw _⟩⟩, fun hΦ γ w hw => ?_⟩
  rw [hΦ.covers w, hw, φ.src_mor γ]

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E
  exact ((hB Obj Mor X W P B Obj Mor X W P B E E (EpFunctor.id X) id).1).2
    ⟨StrongBundle.IsStrongBundleMap.id B, fun _ _ _ _ => rfl⟩

#rt_check RoundTrip.V8_23.A_to_B [Polyfold.EpStrongBundle.isMap_id]
#rt_check RoundTrip.V8_23.B_to_A [Polyfold.EpStrongBundle.isMap_id]
#rt_overlap RoundTrip.V8_23.B_to_A [Polyfold.EpStrongBundle.isMap_id]

end RoundTrip.V8_23
