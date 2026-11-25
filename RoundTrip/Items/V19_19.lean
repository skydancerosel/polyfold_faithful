import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_19

set_option maxSynthPendingDepth 3

/-! Round trip for V19_19 (2021 Proposition 19.3.5, p. 875; 2017: Proposition 19.2: the structure
maps `s`, `t`, `u`, `m`, `ι` of the transition sets).

The item lists the definitions `invHomeomorph`, `FibProd`, `mulMap` (vocabulary) and the theorems
`BasicConstruction.proposition_19_3_5` (for the representative `B.rep` of a basic construction) and
the transition-data lemmas `isLocalHomeomorph_src`, `isLocalHomeomorph_tgt`, `continuous_unit`,
`continuous_mulMap` (for arbitrary transition data `F`).  Universes at `0`.

* `A_to_B`: (1)–(3), (5) are the transition-data conjuncts.  For `ι` (only stated for `B.rep` in
  `A`) take the basic construction `⟨U, ⟦F⟧⟩`; its `M(Ψ, Ψ')` carries the same topology as
  `F.Tr Ψ Ψ'` (`trHomeomorph`, from Lemma 19.3.1), so conjugating `A`'s homeomorphism gives one on
  `F.Tr`.
* `B_to_A`: `B` for `F := B.rep` gives `proposition_19_3_5`; the other conjuncts are `B` itself. -/

namespace RoundTrip.V19_19
open Polyfold GroupoidalCategory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hP, hs, ht, hu, hm⟩
  intro C U F
  refine ⟨fun Ψ Ψ' => ⟨@hs C U F Ψ Ψ', @ht C U F Ψ Ψ'⟩, fun Ψ => @hu C U F Ψ,
    fun Ψ Ψ' Ψ'' => @hm C U F Ψ Ψ' Ψ'', fun Ψ Ψ' => ?_⟩
  let Bc : C.BasicConstruction := ⟨U, ⟦F⟧⟩
  have hF : (⟦F⟧ : Bc.U.TransitionConstruction) = Bc.𝓕 := rfl
  obtain ⟨e, he⟩ := (@hP C Bc Ψ Ψ' Ψ).2.2.2.1
  refine ⟨((Bc.trHomeomorph hF Ψ Ψ').trans e).trans (Bc.trHomeomorph hF Ψ' Ψ).symm,
    fun h => ?_⟩
  exact he h

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {C} Bc Ψ Ψ' Ψ'' => ?_, fun {C} {U} F Ψ Ψ' => ((hB C U F).1 Ψ Ψ').1,
    fun {C} {U} F Ψ Ψ' => ((hB C U F).1 Ψ Ψ').2, fun {C} {U} F Ψ => (hB C U F).2.1 Ψ,
    fun {C} {U} F {Ψ Ψ' Ψ''} => (hB C U F).2.2.1 Ψ Ψ' Ψ''⟩
  obtain ⟨h1, h2, h3, h4⟩ := hB C Bc.U Bc.rep
  obtain ⟨e, he⟩ := h4 Ψ Ψ'
  exact ⟨(h1 Ψ Ψ').1, (h1 Ψ Ψ').2, h2 Ψ, ⟨e, fun a => he a⟩, h3 Ψ Ψ' Ψ''⟩

#rt_check RoundTrip.V19_19.A_to_B [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap]
#rt_check RoundTrip.V19_19.B_to_A [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap]
#rt_overlap RoundTrip.V19_19.B_to_A [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap]

/-! ### The main conjunct `proposition_19_3_5` alone -/

/-- The main conjunct: Proposition 19.3.5 for the representative of a basic construction. -/
def Amain : Prop :=
  type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5.{0}

/-- `main ⇒ B`: transport along `trHomeomorph` (the identity, `T^F = T^{rep}` by Lemma 19.3.1). -/
theorem main_to_B : Amain → B := by
  intro hP C U F
  let Bc : C.BasicConstruction := ⟨U, ⟦F⟧⟩
  have hF : (⟦F⟧ : Bc.U.TransitionConstruction) = Bc.𝓕 := rfl
  let T := fun Ψ Ψ' => Bc.trHomeomorph hF Ψ Ψ'
  refine ⟨fun Ψ Ψ' => ⟨?_, ?_⟩, fun Ψ => ?_, fun Ψ Ψ' Ψ'' => ?_, fun Ψ Ψ' => ?_⟩
  · exact (@hP C Bc Ψ Ψ' Ψ).1.comp (T Ψ Ψ').isLocalHomeomorph
  · exact (@hP C Bc Ψ Ψ' Ψ).2.1.comp (T Ψ Ψ').isLocalHomeomorph
  · exact (T Ψ Ψ).symm.continuous.comp (@hP C Bc Ψ Ψ Ψ).2.2.1
  · have hc := (@hP C Bc Ψ Ψ' Ψ'').2.2.2.2
    let φ : F.FibProd Ψ Ψ' Ψ'' → Bc.rep.FibProd Ψ Ψ' Ψ'' := fun p => ⟨(T Ψ' Ψ'' p.1.1, T Ψ Ψ' p.1.2), p.2⟩
    have hφ : Continuous φ :=
      ((((T Ψ' Ψ'').continuous.comp continuous_fst).prodMk
        ((T Ψ Ψ').continuous.comp continuous_snd)).comp continuous_subtype_val).subtype_mk _
    exact (T Ψ Ψ'').symm.continuous.comp (hc.comp hφ)
  · obtain ⟨e, he⟩ := (@hP C Bc Ψ Ψ' Ψ).2.2.2.1
    exact ⟨((T Ψ Ψ').trans e).trans (T Ψ' Ψ).symm, fun h => he h⟩

/-- `B ⇒ main`. -/
theorem B_to_main : B → Amain := by
  intro hB C Bc Ψ Ψ' Ψ''
  obtain ⟨h1, h2, h3, h4⟩ := hB C Bc.U Bc.rep
  obtain ⟨e, he⟩ := h4 Ψ Ψ'
  exact ⟨(h1 Ψ Ψ').1, (h1 Ψ Ψ').2, h2 Ψ, ⟨e, fun a => he a⟩, h3 Ψ Ψ' Ψ''⟩

#rt_check RoundTrip.V19_19.main_to_B [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap]
#rt_check RoundTrip.V19_19.B_to_main [
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_3_5,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_src,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isLocalHomeomorph_tgt,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_unit,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.continuous_mulMap]

end RoundTrip.V19_19
