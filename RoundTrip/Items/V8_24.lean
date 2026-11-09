import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_24

/-! Round trip for V8_24 (Definition 8.3.3 = 2017 Definition 8.6: strong bundle functors).

The item lists the definition `EpStrongBundle.IsStrongBundleFunctor` (vocabulary) and three
theorems; `A` is the conjunction of their types, universe at `0`:
`IsStrongBundleFunctor.projFunctor_comp` (`(P', π₁) ∘ Φ = φ ∘ (P, π₁)`),
`IsStrongBundleFunctor.mor_val` (`Φ(γ, w) = (φ(γ), Φ(w))`) and `isStrongBundleFunctor_id`.

`B` says (a) for an `EpFunctor` `Φ`, `IsStrongBundleFunctor E E' φ Φ` iff its underlying functor
satisfies B's `IsSBFunctorB` (strong bundle maps on objects and on morphisms, plus the two
covering squares written out), and (b) every groupoid functor satisfying `IsSBFunctorB` underlies
an `EpFunctor`.

* `A_to_B`: `B` holds outright (`B_holds`): (a) is a repackaging (the squares are the `covers`
  fields; B's `hs`, `hs'` and the project's `X.isScSmoothMap_src` agree by proof irrelevance),
  (b) takes the sc-smoothness fields of the two strong bundle maps (`E.toEpGroupoid.PObj` and
  `PMor` are `B.toMPolyfold0` and `(B.pullback _).toMPolyfold0` by `rfl`).  `A` is not used.
* `B_to_A`: all three conjuncts from (a): the covering squares give `projFunctor_comp`
  (`EpFunctor.ext`) and, with `Φ.src_mor`, `mor_val`; the backward half of (a) with
  `StrongBundle.IsStrongBundleMap.id` gives `isStrongBundleFunctor_id`. -/

namespace RoundTrip.V8_24
open Polyfold

/-- The project's statement (universe at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.IsStrongBundleFunctor.projFunctor_comp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsStrongBundleFunctor.mor_val.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isStrongBundleFunctor_id.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.IsStrongBundleFunctor.projFunctor_comp.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleFunctor.mor_val.{0},
    @Polyfold.EpStrongBundle.isStrongBundleFunctor_id.{0}⟩

/-- `B` holds outright. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    hs hs' E E' φ
  refine ⟨fun Φ => ⟨fun h => ⟨h.isStrongBundleMap_obj, h.isStrongBundleMap_mor,
    h.isStrongBundleMap_obj.covers, h.isStrongBundleMap_mor.covers⟩,
    fun h => ⟨h.1, h.2.1⟩⟩, fun Φ h => ?_⟩
  exact ⟨{ toGroupoidFunctor := Φ
           isScSmoothMap_obj := h.1.isScSmoothMap
           isScSmoothMap_mor := h.2.1.isScSmoothMap }, rfl⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' φ Φ h
    have h' := ((hB Obj Mor X W P B Obj' Mor' X' W' P' B' X.isScSmoothMap_src
      X'.isScSmoothMap_src E E' φ).1 Φ).1 h
    exact EpFunctor.ext (funext h'.2.2.1) (funext h'.2.2.2)
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' φ Φ h q
    have h' := ((hB Obj Mor X W P B Obj' Mor' X' W' P' B' X.isScSmoothMap_src
      X'.isScSmoothMap_src E E' φ).1 Φ).1 h
    exact Prod.ext (h'.2.2.2 q) (Φ.src_mor q)
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E
    exact ((hB Obj Mor X W P B Obj Mor X W P B X.isScSmoothMap_src X.isScSmoothMap_src E E
      (EpFunctor.id X)).1 (EpFunctor.id E.toEpGroupoid)).2
      ⟨StrongBundle.IsStrongBundleMap.id B, StrongBundle.IsStrongBundleMap.id _,
        fun _ => rfl, fun _ => rfl⟩

#rt_check RoundTrip.V8_24.A_to_B [Polyfold.EpStrongBundle.IsStrongBundleFunctor.projFunctor_comp,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.mor_val,
  Polyfold.EpStrongBundle.isStrongBundleFunctor_id]
#rt_check RoundTrip.V8_24.B_to_A [Polyfold.EpStrongBundle.IsStrongBundleFunctor.projFunctor_comp,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.mor_val,
  Polyfold.EpStrongBundle.isStrongBundleFunctor_id]
#rt_overlap RoundTrip.V8_24.B_to_A [Polyfold.EpStrongBundle.IsStrongBundleFunctor.projFunctor_comp,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.mor_val,
  Polyfold.EpStrongBundle.isStrongBundleFunctor_id]

end RoundTrip.V8_24
