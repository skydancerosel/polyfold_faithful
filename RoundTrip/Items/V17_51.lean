import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_51

set_option maxSynthPendingDepth 3

/-! Round trip for V17_51 (2021 Proposition 17.2.14, pp. 776–781: the natural topology on
`M(TΨ₁, TΨ₂)` is metrizable, `s, t` local homeomorphisms, `ι` a homeomorphism, `u, m`
continuous).

`A` is the conjunction of the types of `proposition_17_2_14_src_tgt`, `metrizableSpace_TTrM` and
`proposition_17_2_14`, universe `0` (`B` uses `GCT.{0}`); `tangentTrHomeomorph` is vocabulary.

Pure glue in both directions: `B`'s `natTop` (the `⨆` of the coinduced topologies of the maps
(17.42)) is definitionally the project's `tangentTrTopology` (`chartTopology` of the same family),
`NT = TTr = TTrM`, `B`'s fibred product `{p // s p.1 = t p.2}` is `↥(fibredProduct s t)` with the
same subspace topology, and `B`'s `mul` is `TransitionSet.mul` up to the proof of composability.
-/

namespace RoundTrip.V17_51
open Polyfold GCT.PolyfoldConstruction Topology

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt.{0},
    @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14.{0}⟩

theorem main_to_B :
    (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14.{0}) → B := by
  intro h C S hU
  exact ⟨fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).1, fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).2.1,
    fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).2.2.1, fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).2.2.2.1,
    fun Ψ => (h hU Ψ Ψ Ψ).2.2.2.2.1, fun Ψ₁ Ψ₂ Ψ₃ => (h hU Ψ₁ Ψ₂ Ψ₃).2.2.2.2.2⟩

theorem A_to_B : A → B := fun h => main_to_B h.2.2

theorem B_to_main : B →
    (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14.{0}) := by
  intro hB C S hU Ψ₁ Ψ₂ Ψ₃
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB C S hU
  exact ⟨h1 Ψ₁ Ψ₂, h2 Ψ₁ Ψ₂, h3 Ψ₁ Ψ₂, h4 Ψ₁ Ψ₂, h5 Ψ₁, h6 Ψ₁ Ψ₂ Ψ₃⟩

theorem B_to_A : B → A := by
  intro hB
  exact ⟨fun {_ _} hU Ψ₁ Ψ₂ => ⟨(B_to_main hB hU Ψ₁ Ψ₂ Ψ₁).2.1,
      (B_to_main hB hU Ψ₁ Ψ₂ Ψ₁).2.2.1⟩,
    fun {_ _} hU Ψ₁ Ψ₂ => (B_to_main hB hU Ψ₁ Ψ₂ Ψ₁).1, B_to_main hB⟩

#rt_check RoundTrip.V17_51.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14]
#rt_check RoundTrip.V17_51.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14]
#rt_check RoundTrip.V17_51.main_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14]
#rt_check RoundTrip.V17_51.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14]
#rt_overlap RoundTrip.V17_51.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14_src_tgt,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_TTrM,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_14]

end RoundTrip.V17_51
