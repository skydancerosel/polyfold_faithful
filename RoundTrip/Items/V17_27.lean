import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_27

set_option maxSynthPendingDepth 3

/-! Round trip for V17_27 (2021 Proposition 17.1.24, p. 758: if `C` has one of (LR), (SLR),
(LUC), (SLUC), (ZHOU), every model `X_Ψ` has it).

`A` is the conjunction of the types of `proposition_17_1_24` (fixed covering family `c`, the five
implications) and `HasModelProperty.forall` (the same for any property invariant under
generalized isomorphisms), at universe `0` (`B` is stated for `GCT.{0}`).  The main conjunct is
`proposition_17_1_24`; it and `B` differ only in the place of `∀ c` (inside each implication in
`B`, outside the conjunction in `A`).  `HasModelProperty.forall` (general invariant `P`) does not
follow from `B`, which names five properties; in `B_to_A` it is re-proved outright, as in the
project: the comparison `f_{Ψ₀,Ψ}` is a generalized isomorphism (`isGeneralizedIso_comparison`,
not an item theorem here). -/

namespace RoundTrip.V17_27
open Polyfold Polyfold.GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24.{0},
    @Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall.{0}⟩

theorem A_to_B : A → B := fun hA _ S =>
  ⟨fun h c => (hA.1 S c).1 h, fun h c => (hA.1 S c).2.1 h, fun h c => (hA.1 S c).2.2.1 h,
    fun h c => (hA.1 S c).2.2.2.1 h, fun h c => (hA.1 S c).2.2.2.2 h⟩

/-- `HasModelProperty.forall`, re-proved (the project's proof). -/
theorem hasModelProperty_forall' {C : GCT.{0}} {S : C.PolyfoldConstruction} {P : EP.{0} → Prop}
    (hP : IsGenIsoInvariant P) (h : S.HasModelProperty P) (c : S.CoveringFamily) :
    P (S.modelEP c.Ψ) := by
  obtain ⟨c₀, h₀⟩ := h
  exact (hP (S.isGeneralizedIso_comparison c₀ c)).1 h₀

theorem B_to_A : B → A := fun hB =>
  ⟨fun {C} S c => ⟨fun h => (hB C S).1 h c, fun h => (hB C S).2.1 h c,
      fun h => (hB C S).2.2.1 h c, fun h => (hB C S).2.2.2.1 h c, fun h => (hB C S).2.2.2.2 h c⟩,
    fun hP h c => hasModelProperty_forall' hP h c⟩

/-- The main conjunct alone. -/
theorem main_to_B : type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24.{0} → B :=
  fun h _ S => ⟨fun hh c => (h S c).1 hh, fun hh c => (h S c).2.1 hh,
    fun hh c => (h S c).2.2.1 hh, fun hh c => (h S c).2.2.2.1 hh, fun hh c => (h S c).2.2.2.2 hh⟩

theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24.{0} :=
  fun hB {C} S c => ⟨fun h => (hB C S).1 h c, fun h => (hB C S).2.1 h c,
    fun h => (hB C S).2.2.1 h c, fun h => (hB C S).2.2.2.1 h c, fun h => (hB C S).2.2.2.2 h c⟩

#rt_check RoundTrip.V17_27.A_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24,
  Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall]
#rt_check RoundTrip.V17_27.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24,
  Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall]
#rt_check RoundTrip.V17_27.main_to_B [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24,
  Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall]
#rt_check RoundTrip.V17_27.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24,
  Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall]
#rt_overlap RoundTrip.V17_27.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_1_24,
  Polyfold.GCT.PolyfoldConstruction.HasModelProperty.forall]

end RoundTrip.V17_27
