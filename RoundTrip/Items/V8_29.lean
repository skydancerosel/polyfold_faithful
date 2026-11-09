import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_29

/-! Round trip for V8_29 (Proposition 8.2 of the 2017 text, 2021: Proposition 8.5.2: the composite
of two proper covering functors is a proper covering functor).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `EpFunctor.IsProperCovering.evenlyCovered_comp` (property (2) of `F ∘ H`),
`EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp` (property (3) of `F ∘ H`) and
`EpFunctor.IsProperCovering.proposition_8_5_2` (the proposition).

* `A → B`: `B` is literally the third conjunct (with the arguments in another order).
* `B → A`: `proposition_8_5_2` is `B`; `evenlyCovered_comp` and `isScDiffeo_fibredMap_comp` are the
  fields `evenlyCovered`, `isScDiffeo_fibredMap` of the proper covering `F ∘ H` that `B`
  provides. -/

namespace RoundTrip.V8_29
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.IsProperCovering.evenlyCovered_comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.IsProperCovering.proposition_8_5_2.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.IsProperCovering.evenlyCovered_comp.{0, 0, 0},
    @Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp.{0, 0, 0},
    @Polyfold.EpFunctor.IsProperCovering.proposition_8_5_2.{0, 0, 0}⟩

theorem A_to_B : A → B := by
  intro hA ObjX MorX ObjY MorY ObjZ MorZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z F H hF hH
  exact hA.2.2 hF hH

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ Y X Z F H hF hH x
    exact (hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F H hF hH).evenlyCovered x
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ Y X Z F H hF hH
    exact (hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F H hF hH).isScDiffeo_fibredMap
  · intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ Y X Z F H hF hH
    exact hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F H hF hH

#rt_check RoundTrip.V8_29.A_to_B [Polyfold.EpFunctor.IsProperCovering.evenlyCovered_comp,
  Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp,
  Polyfold.EpFunctor.IsProperCovering.proposition_8_5_2]
#rt_check RoundTrip.V8_29.B_to_A [Polyfold.EpFunctor.IsProperCovering.evenlyCovered_comp,
  Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp,
  Polyfold.EpFunctor.IsProperCovering.proposition_8_5_2]
#rt_overlap RoundTrip.V8_29.B_to_A [Polyfold.EpFunctor.IsProperCovering.evenlyCovered_comp,
  Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp,
  Polyfold.EpFunctor.IsProperCovering.proposition_8_5_2]

end RoundTrip.V8_29
