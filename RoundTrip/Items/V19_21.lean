import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_21

set_option maxSynthPendingDepth 3

/-! Round trip for V19_21 (2021 Proposition 19.3.7, p. 877: `Ψ̄ : G × O → M(Ψ, Ψ)` is a
homeomorphism).  Universes at `0`.  `A` = `proposition_19_3_7` (for a basic construction, on
`B.M Ψ Ψ = B.rep.Tr Ψ Ψ`) ∧ `hatHomeomorph_apply` (the definitional formula of the vocabulary's
`hatHomeomorph`).  `B` is stated for every uniformizer construction and every transition data
`F` (not only representatives of a basic construction). -/

namespace RoundTrip.V19_21
open Polyfold Polyfold.GroupoidalCategory

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply.{0}⟩

/-- From the main conjunct: every transition data `F` represents the basic construction
`(U, ⟦F⟧)`, and `T^F_{Ψ,Ψ}` agrees with the topology of `B.M Ψ Ψ` (`trHomeomorph`). -/
theorem main_A_to_B
    (hA : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7.{0}) :
    B := by
  intro C U F Ψ
  let Bc : C.BasicConstruction := ⟨U, ⟦F⟧⟩
  obtain ⟨e, he⟩ := hA Bc Ψ
  exact ⟨e.trans (Bc.trHomeomorph (F := F) rfl Ψ Ψ).symm, fun p => he p⟩

theorem A_to_B : A → B := fun hA => main_A_to_B hA.1

theorem main_B_to_A (hB : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7.{0} := by
  intro C Bc Ψ
  exact hB C Bc.U Bc.rep Ψ

/-- The second conjunct is definitional (`rfl`); it does not use `B`. -/
theorem B_to_A : B → A := fun hB => ⟨main_B_to_A hB, by intros; rfl⟩

#rt_check RoundTrip.V19_21.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply]
#rt_check RoundTrip.V19_21.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply]
#rt_check RoundTrip.V19_21.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply]
#rt_check RoundTrip.V19_21.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply]
#rt_overlap RoundTrip.V19_21.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_7,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.hatHomeomorph_apply]

end RoundTrip.V19_21
