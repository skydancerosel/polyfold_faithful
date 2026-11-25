import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_18

set_option maxSynthPendingDepth 3

/-! Round trip for V19_18 (2021 Proposition 19.3.4, p. 874; 2017: Proposition 19.1: the germs
`F_h` are open embeddings and `T_{Ψ,Ψ'}` is Hausdorff).

The item lists the definition `sheet` (vocabulary) and the theorems
`BasicConstruction.proposition_19_3_4` (for a representative `F` of `B.𝓕`, images and the
Hausdorff property in `B.M = B.rep.Tr`), `proposition_19_3_4_topology` (`T^F` has the axioms of a
topology) and the transition-data lemmas `isOpen_image_map`, `continuousOn_map`,
`isOpenEmbedding_restrict_map` (arbitrary `F`).  Universes at `0`.

* `A_to_B`: (1), (2) are the transition-data conjuncts; Hausdorff is stated in `A` only for
  `B.M`, so take the basic construction `⟨U, ⟦F⟧⟩` and transport along `trHomeomorph` (the
  identity, `T^F = T^{rep}` by Lemma 19.3.1).
* `B_to_A`: everything from `B` (transported along `trHomeomorph` for `proposition_19_3_4`),
  except `proposition_19_3_4_topology`, which is the axioms of the instance `F.Tr` (true by
  construction, proved without `B`). -/

namespace RoundTrip.V19_18
open Polyfold GroupoidalCategory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map.{0}⟩

/-- The main conjunct `proposition_19_3_4`. -/
def Amain : Prop :=
  type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4.{0}

/-- Hausdorff for every `F`, from the main conjunct (for `⟨U, ⟦F⟧⟩`). -/
theorem t2_of_main (hP : Amain) {C : GroupoidalCategory.{0}} {U : C.UniformizerConstruction}
    (F : U.TransitionData) (Ψ Ψ' : U.Unif) : T2Space (F.Tr Ψ Ψ') := by
  let Bc : C.BasicConstruction := ⟨U, ⟦F⟧⟩
  have hF : (⟦F⟧ : Bc.U.TransitionConstruction) = Bc.𝓕 := rfl
  have := (@hP C Bc F hF Ψ Ψ').2.2
  exact (Bc.trHomeomorph hF Ψ Ψ').isEmbedding.t2Space

theorem A_to_B : A → B := by
  rintro ⟨hP, -, himg, -, hemb⟩
  intro C U F Ψ Ψ'
  exact ⟨fun h W hWs hW => @himg C U F Ψ Ψ' h W hW hWs, fun h => @hemb C U F Ψ Ψ' h,
    t2_of_main hP F Ψ Ψ'⟩

/-- `main ⇒ B`: transport along `trHomeomorph`. -/
theorem main_to_B : Amain → B := by
  intro hP C U F Ψ Ψ'
  let Bc : C.BasicConstruction := ⟨U, ⟦F⟧⟩
  have hF : (⟦F⟧ : Bc.U.TransitionConstruction) = Bc.𝓕 := rfl
  have T := Bc.trHomeomorph hF Ψ Ψ'
  obtain ⟨h1, h2, -⟩ := @hP C Bc F hF Ψ Ψ'
  refine ⟨fun h W hWs hW => ?_, fun h => ?_, t2_of_main hP F Ψ Ψ'⟩
  · have := (h1 h W hW hWs).preimage (Bc.trHomeomorph hF Ψ Ψ').continuous
    exact this
  · exact (Bc.trHomeomorph hF Ψ Ψ').symm.isOpenEmbedding.comp (h2 h).2

/-- `B ⇒ main`. -/
theorem B_to_main : B → Amain := by
  intro hB C Bc F hF Ψ Ψ'
  obtain ⟨h1, h2, -⟩ := hB C Bc.U F Ψ Ψ'
  refine ⟨fun h W hW hWs => ?_, fun h => ⟨?_, ?_⟩, (hB C Bc.U Bc.rep Ψ Ψ').2.2⟩
  · exact (h1 h W hWs hW).preimage (Bc.trHomeomorph hF Ψ Ψ').symm.continuous
  · exact continuousOn_iff_continuous_domRestrict.2
      ((Bc.trHomeomorph hF Ψ Ψ').continuous.comp (h2 h).continuous)
  · exact (Bc.trHomeomorph hF Ψ Ψ').isOpenEmbedding.comp (h2 h)

theorem B_to_A : B → A := by
  intro hB
  refine ⟨B_to_main hB, fun {C} Bc F Ψ Ψ' => ?_, fun {C} {U} F Ψ Ψ' h W hW hWs =>
    (hB C U F Ψ Ψ').1 h W hWs hW, fun {C} {U} F Ψ Ψ' h => ?_,
    fun {C} {U} F Ψ Ψ' h => (hB C U F Ψ Ψ').2.1 h⟩
  · -- the axioms of the instance `F.Tr Ψ Ψ'` (no use of `B`)
    exact ⟨isOpen_univ (X := F.Tr Ψ Ψ'), fun W₁ W₂ h₁ h₂ => IsOpen.inter (X := F.Tr Ψ Ψ') h₁ h₂,
      fun S hS => isOpen_sUnion (X := F.Tr Ψ Ψ') hS⟩
  · exact continuousOn_iff_continuous_domRestrict.2 ((hB C U F Ψ Ψ').2.1 h).continuous

#rt_check RoundTrip.V19_18.A_to_B [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map]
#rt_check RoundTrip.V19_18.B_to_A [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map]
#rt_overlap RoundTrip.V19_18.B_to_A [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map]
#rt_check RoundTrip.V19_18.main_to_B [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map]
#rt_check RoundTrip.V19_18.B_to_main [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_4_topology,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpen_image_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuousOn_map,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isOpenEmbedding_restrict_map]

end RoundTrip.V19_18
