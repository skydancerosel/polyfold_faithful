import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_88

set_option maxSynthPendingDepth 3

/-! Round trip for V19_88 (2021 Definition 19.7.27 and Theorem 19.7.28, p. 928).

* `A`: the types of `definition_19_7_27`, `theorem_19_7_28_one_hyp`, `_two_hyp`, `_three_hyp`
  (universe `0`); the five `CoveringBasicConstruction.to…/of…` definitions are vocabulary.
* All three `_hyp` theorems assume `Bh.IsCompatible` (every top target map `t̂` continuous), the
  project's added hypothesis; `B` does not assume it.  `A_to_B` is therefore not proved; under
  `IsCompatible` the conclusion of `B` follows from `A` (`A_to_B_of_compatible`: `T_{|A|}` of `B`
  is `generateFrom` of the project's `natTopA`, equal to it; the structure is
  `toProperPolyfoldCoveringStructure`, its members are the `toProperCoveringUniformizer Ψ̂`).
* `B_to_A` is not proved: `B` gives the conjunct `theorem_19_7_28_two_hyp` (`B_to_two`), but
  `definition_19_7_27`, `theorem_19_7_28_one_hyp` and `theorem_19_7_28_three_hyp` describe the
  project's particular structure (`hatPolyfold`, `toProperPolyfoldCoveringStructure`), while `B`
  only asserts that some structure exists whose members match `F̂` in `Ψ` and in the image of
  objects. -/

namespace RoundTrip.V19_88
open Polyfold GroupoidalCategory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @CoveringBasicConstruction.definition_19_7_27.{0}) ∧
  (type_of% @CoveringBasicConstruction.theorem_19_7_28_one_hyp.{0}) ∧
  (type_of% @CoveringBasicConstruction.theorem_19_7_28_two_hyp.{0}) ∧
  (type_of% @CoveringBasicConstruction.theorem_19_7_28_three_hyp.{0})

theorem A_holds : A :=
  ⟨@CoveringBasicConstruction.definition_19_7_27.{0},
   @CoveringBasicConstruction.theorem_19_7_28_one_hyp.{0},
   @CoveringBasicConstruction.theorem_19_7_28_two_hyp.{0},
   @CoveringBasicConstruction.theorem_19_7_28_three_hyp.{0}⟩

theorem hasClassUniformizers_of_toBasic {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)
    (h : Bh.toBasic.U.HasClassUniformizers) : Bh.HasClassUniformizers := fun z => by
  obtain ⟨β, hβ, Ψ, Ψh, hΨh, -⟩ := h z
  exact ⟨β, hβ, Ψh, hΨh⟩

/-- `B`'s conclusion under the project's added hypothesis `IsCompatible`, from `A`. -/
theorem A_to_B_of_compatible (hA : A) :
    ∀ (A B : GroupoidalCategory.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr),
    IsFiniteToOneCovering P →
    ∀ (Bh : CoveringBasicConstruction P), Bh.IsCompatible →
    ∀ (hB : Bh.toBasic.U.HasClassUniformizers)
      (hm : @TopologicalSpace.MetrizableSpace B.OrbitSpace (Bh.toBasic.natTop hB)),
      ∃ hA : @TopologicalSpace.MetrizableSpace A.OrbitSpace (topA Bh),
        @GroupoidFunctor.IsProperCoveringGCT (GA Bh hA) (Bh.toBasic.toGCTOfMetrizable hB hm) P ∧
        ∃ S : @ProperPolyfoldCoveringStructure (GA Bh hA)
            (Bh.toBasic.toGCTOfMetrizable hB hm) P,
          S.SB = BasicConstruction.toPolyfoldConstruction hm ∧
          (∀ (β : B.Obj), ∀ Ψh ∈ Bh.hatU.F β, ∃ U ∈ S.toC.F β,
            U.Ψ = Ψh.Ψ ∧ Set.range U.hat.obj = Set.range Ψh.hat.obj) ∧
          (∀ (β : B.Obj), ∀ U ∈ S.toC.F β, ∃ Ψh ∈ Bh.hatU.F β,
            U.Ψ = Ψh.Ψ ∧ Set.range U.hat.obj = Set.range Ψh.hat.obj) := by
  intro A B P hP Bh hC hB hm
  have hU := hasClassUniformizers_of_toBasic Bh hB
  obtain ⟨-, -, -, -, hmA, -, hprop⟩ := hA.2.2.1 Bh hP hC hU hm
  obtain ⟨hmem, hSB, -, -⟩ := hA.2.2.2 Bh hP hC hU hm
  have ht : topA Bh = Bh.natTopA hP hC hU :=
    TopologicalSpace.generateFrom_setOfPred_isOpen (Bh.natTopA hP hC hU)
  -- generalize the topology, then substitute `T_{|A|}`
  suffices key : ∀ (t : TopologicalSpace A.OrbitSpace) (ht : t = Bh.natTopA hP hC hU)
      (hA' : @TopologicalSpace.MetrizableSpace A.OrbitSpace t),
      @GroupoidFunctor.IsProperCoveringGCT (@GCT.mk A t hA')
          (Bh.toBasic.toGCTOfMetrizable hB hm) P ∧
        ∃ S : @ProperPolyfoldCoveringStructure (@GCT.mk A t hA')
            (Bh.toBasic.toGCTOfMetrizable hB hm) P,
          S.SB = BasicConstruction.toPolyfoldConstruction hm ∧
          (∀ (β : B.Obj), ∀ Ψh ∈ Bh.hatU.F β, ∃ U ∈ S.toC.F β,
            U.Ψ = Ψh.Ψ ∧ Set.range U.hat.obj = Set.range Ψh.hat.obj) ∧
          (∀ (β : B.Obj), ∀ U ∈ S.toC.F β, ∃ Ψh ∈ Bh.hatU.F β,
            U.Ψ = Ψh.Ψ ∧ Set.range U.hat.obj = Set.range Ψh.hat.obj) by
    exact ⟨ht ▸ hmA, key _ ht _⟩
  intro t ht hA'
  subst ht
  refine ⟨hprop, Bh.toProperPolyfoldCoveringStructure hP hC hU hm, hSB, ?_, ?_⟩
  · intro β Ψh hΨh
    exact ⟨Bh.toProperCoveringUniformizer hP hC hU hm Ψh hΨh, (hmem β _).2 ⟨Ψh, hΨh, rfl⟩,
      rfl, rfl⟩
  · intro β U hU'
    obtain ⟨Ψh, hΨh, rfl⟩ := (hmem β U).1 hU'
    exact ⟨Ψh, hΨh, rfl, rfl⟩

/-- `B` gives the conjunct `theorem_19_7_28_two_hyp` of `A` (the GCTs and the proper covering
functor); the other conjuncts concern the project's particular constructions. -/
theorem B_to_two : B → type_of% @CoveringBasicConstruction.theorem_19_7_28_two_hyp.{0} := by
  intro hB A B P Bh hP hC hU hm
  obtain ⟨hA', hprop, -⟩ := hB A B P hP Bh hU.toBasic hm
  have ht : topA Bh = Bh.natTopA hP hC hU :=
    TopologicalSpace.generateFrom_setOfPred_isOpen (Bh.natTopA hP hC hU)
  suffices key : ∀ (t : TopologicalSpace A.OrbitSpace) (ht : t = Bh.natTopA hP hC hU)
      (hA' : @TopologicalSpace.MetrizableSpace A.OrbitSpace t),
      @GroupoidFunctor.IsProperCoveringGCT (@GCT.mk A t hA')
          (Bh.toBasic.toGCTOfMetrizable hU.toBasic hm) P →
      @TopologicalSpace.MetrizableSpace _ (Bh.natTopA hP hC hU) ∧
      @GroupoidFunctor.IsProperCoveringGCT (Bh.gctA hP hC hU hm) (Bh.gctB hU hm) P by
    obtain ⟨h1, h2⟩ := key _ ht hA' hprop
    exact ⟨rfl, rfl, rfl, rfl, h1, hm, h2⟩
  intro t ht hA' h
  subst ht
  exact ⟨hA', h⟩

#rt_check RoundTrip.V19_88.B_to_two [Polyfold.GroupoidalCategory.CoveringBasicConstruction.definition_19_7_27, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_one_hyp, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_two_hyp, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_three_hyp]
#rt_overlap RoundTrip.V19_88.B_to_two [Polyfold.GroupoidalCategory.CoveringBasicConstruction.definition_19_7_27, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_one_hyp, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_two_hyp, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_three_hyp]
#rt_check RoundTrip.V19_88.A_to_B_of_compatible [Polyfold.GroupoidalCategory.CoveringBasicConstruction.definition_19_7_27, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_one_hyp, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_two_hyp, Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_28_three_hyp]

end RoundTrip.V19_88
