import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_26

set_option maxSynthPendingDepth 3

/-! Round trip for V17_26 (2021 Proposition 17.1.23, p. 758: (ZHOU) implies (LUC), (SLUC), (LR),
(SLR)).

`A` is the conjunction of the types of `proposition_17_1_23`, `IsZhou.model`, `IsLR.model`, all at
universe `0` (`B` is stated for `GCT.{0}`).  The main conjunct is `proposition_17_1_23`, which is
`B` verbatim.  `IsZhou.model` and `IsLR.model` (a property of one model holds for every model) do
not follow from `B`; in `B_to_A` they are re-proved from the non-item lemma
`HasModelProperty.forall` (generalized isomorphism `f_{Ψ,Ψ'}` and Theorem 10.3.21). -/

namespace RoundTrip.V17_26
open Polyfold Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.IsZhou.model.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.IsLR.model.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23.{0},
    @Polyfold.GCT.PolyfoldConstruction.IsZhou.model.{0},
    @Polyfold.GCT.PolyfoldConstruction.IsLR.model.{0}⟩

theorem A_to_B : A → B := fun hA _ S h => hA.1 S h

theorem B_to_A : B → A := fun hB =>
  ⟨fun S h => hB _ S h,
    fun h c => h.forall isGenIsoInvariant_isZhou c,
    fun h c => h.forall isGenIsoInvariant_isLR c⟩

/-- The main conjunct alone. -/
theorem main_to_B : type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23.{0} → B :=
  fun h _ S hz => h S hz

theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23.{0} :=
  fun hB {C} S h => hB C S h

#rt_check RoundTrip.V17_26.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23,
  Polyfold.GCT.PolyfoldConstruction.IsZhou.model, Polyfold.GCT.PolyfoldConstruction.IsLR.model]
#rt_check RoundTrip.V17_26.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23,
  Polyfold.GCT.PolyfoldConstruction.IsZhou.model, Polyfold.GCT.PolyfoldConstruction.IsLR.model]
#rt_check RoundTrip.V17_26.main_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23,
  Polyfold.GCT.PolyfoldConstruction.IsZhou.model, Polyfold.GCT.PolyfoldConstruction.IsLR.model]
#rt_check RoundTrip.V17_26.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23,
  Polyfold.GCT.PolyfoldConstruction.IsZhou.model, Polyfold.GCT.PolyfoldConstruction.IsLR.model]
#rt_overlap RoundTrip.V17_26.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_23,
  Polyfold.GCT.PolyfoldConstruction.IsZhou.model, Polyfold.GCT.PolyfoldConstruction.IsLR.model]

end RoundTrip.V17_26
