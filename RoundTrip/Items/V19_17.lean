import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_17

set_option maxSynthPendingDepth 3

/-! Round trip for V19_17 (2021 Theorem 19.3.3, p. 873; 2017: Theorem 19.2: the transition sets
`M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`).

The item lists `BasicConstruction.theorem_19_3_3` (for `B.M = B.rep.Tr`) and the transition-data
lemmas `t2Space`, `regularSpace`, `exists_isOpen_metrizableSpace` (arbitrary `F`).  Universes at
`0`.

* `A_to_B`: for a representative `F` of `B.𝓕`, the separation and local metrizability are the
  transition-data conjuncts; the structure maps and `Ψ̄` come from `theorem_19_3_3` for `B.rep`,
  transported to `F.Tr` along `trHomeomorph` (the identity; `T^F = T^{rep}` by Lemma 19.3.1).
* `B_to_A`: `theorem_19_3_3` is `B` at `F := B.rep`; the transition-data lemmas are `B` for the
  basic construction `⟨U, ⟦F⟧⟩`. -/

namespace RoundTrip.V19_17
open Polyfold GroupoidalCategory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace.{0}⟩

/-- The main conjunct `theorem_19_3_3`. -/
def Amain : Prop :=
  type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3.{0}

/-- The structure-map clauses of `B`, from the main conjunct (transport along `trHomeomorph`). -/
theorem maps_of_main (hP : Amain) {C : GroupoidalCategory.{0}} (Bc : C.BasicConstruction)
    (F : Bc.U.TransitionData) (hF : (⟦F⟧ : Bc.U.TransitionConstruction) = Bc.𝓕) :
    (∀ Ψ Ψ' : Bc.U.Unif,
      IsLocalHomeomorph (fun h : F.Tr Ψ Ψ' =>
        (GroupoidStr.TransitionSet.src (h : (Ψ : C.Uniformizer).Trans Ψ') :
          (Ψ : C.Uniformizer).O)) ∧
      IsLocalHomeomorph (fun h : F.Tr Ψ Ψ' =>
        (GroupoidStr.TransitionSet.tgt (h : (Ψ : C.Uniformizer).Trans Ψ') :
          (Ψ' : C.Uniformizer).O))) ∧
    (∀ Ψ : Bc.U.Unif,
      Continuous (fun o : (Ψ : C.Uniformizer).O =>
        F.toTr (GroupoidStr.TransitionSet.unit o : (Ψ : C.Uniformizer).Trans Ψ))) ∧
    (∀ Ψ Ψ' Ψ'' : Bc.U.Unif, Continuous (F.mulMap Ψ Ψ' Ψ'')) ∧
    (∀ Ψ Ψ' : Bc.U.Unif, ∃ e : F.Tr Ψ Ψ' ≃ₜ F.Tr Ψ' Ψ,
      ∀ h : (Ψ : C.Uniformizer).Trans Ψ',
        e (F.toTr h) = F.toTr (GroupoidStr.TransitionSet.inv h)) ∧
    (∀ Ψ : Bc.U.Unif, ∃ e : (Ψ : C.Uniformizer).G × (Ψ : C.Uniformizer).O ≃ₜ F.Tr Ψ Ψ,
      ∀ p, e p = F.toTr ((Ψ : C.Uniformizer).hat p)) := by
  let T := fun Ψ Ψ' => Bc.trHomeomorph hF Ψ Ψ'
  refine ⟨fun Ψ Ψ' => ⟨?_, ?_⟩, fun Ψ => ?_, fun Ψ Ψ' Ψ'' => ?_, fun Ψ Ψ' => ?_, fun Ψ => ?_⟩
  · exact (@hP C Bc Ψ Ψ' Ψ).2.2.2.1.comp (T Ψ Ψ').isLocalHomeomorph
  · exact (@hP C Bc Ψ Ψ' Ψ).2.2.2.2.1.comp (T Ψ Ψ').isLocalHomeomorph
  · exact (T Ψ Ψ).symm.continuous.comp (@hP C Bc Ψ Ψ Ψ).2.2.2.2.2.1
  · have hc := (@hP C Bc Ψ Ψ' Ψ'').2.2.2.2.2.2.2.1
    let φ : F.FibProd Ψ Ψ' Ψ'' → Bc.rep.FibProd Ψ Ψ' Ψ'' :=
      fun p => ⟨(T Ψ' Ψ'' p.1.1, T Ψ Ψ' p.1.2), p.2⟩
    have hφ : Continuous φ :=
      ((((T Ψ' Ψ'').continuous.comp continuous_fst).prodMk
        ((T Ψ Ψ').continuous.comp continuous_snd)).comp continuous_subtype_val).subtype_mk _
    exact (T Ψ Ψ'').symm.continuous.comp (hc.comp hφ)
  · obtain ⟨e, he⟩ := (@hP C Bc Ψ Ψ' Ψ).2.2.2.2.2.2.1
    exact ⟨((T Ψ Ψ').trans e).trans (T Ψ' Ψ).symm, fun h => he h⟩
  · obtain ⟨e, he⟩ := (@hP C Bc Ψ Ψ Ψ).2.2.2.2.2.2.2.2
    exact ⟨e.trans (T Ψ Ψ).symm, fun p => he p⟩

/-- Local metrizability moves along a homeomorphism. -/
theorem locMetr_transport {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (T : X ≃ₜ Y)
    (hY : ∀ y : Y, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ TopologicalSpace.MetrizableSpace W) (x : X) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ TopologicalSpace.MetrizableSpace W := by
  obtain ⟨W, hW, hxW, hm⟩ := hY (T x)
  refine ⟨T ⁻¹' W, hW.preimage T.continuous, hxW, ?_⟩
  have he : Topology.IsEmbedding (fun p : T ⁻¹' W => (⟨T p, p.2⟩ : W)) :=
    (T.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
  exact he.metrizableSpace

theorem A_to_B : A → B := by
  rintro ⟨hP, h2, h3, h4⟩
  intro C Bc F hF
  exact ⟨fun Ψ Ψ' => ⟨@h3 C Bc.U F Ψ Ψ', @h2 C Bc.U F Ψ Ψ', @h4 C Bc.U F Ψ Ψ'⟩,
    maps_of_main hP Bc F hF⟩

/-- `main ⇒ B`: everything transported along `trHomeomorph`. -/
theorem main_to_B : Amain → B := by
  intro hP C Bc F hF
  refine ⟨fun Ψ Ψ' => ?_, maps_of_main hP Bc F hF⟩
  obtain ⟨hr, ht, hm, -⟩ := @hP C Bc Ψ Ψ' Ψ
  let T := Bc.trHomeomorph hF Ψ Ψ'
  exact ⟨T.isEmbedding.isInducing.regularSpace, T.isEmbedding.t2Space,
    locMetr_transport T hm⟩

/-- `B ⇒ main`. -/
theorem B_to_main : B → Amain := by
  intro hB C Bc Ψ Ψ' Ψ''
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB C Bc Bc.rep Bc.mk_rep
  obtain ⟨e, he⟩ := h5 Ψ Ψ'
  obtain ⟨e', he'⟩ := h6 Ψ
  exact ⟨(h1 Ψ Ψ').1, (h1 Ψ Ψ').2.1, (h1 Ψ Ψ').2.2, (h2 Ψ Ψ').1, (h2 Ψ Ψ').2, h3 Ψ,
    ⟨e, fun a => he a⟩, h4 Ψ Ψ' Ψ'', ⟨e', fun x => he' x⟩⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨B_to_main hB, fun {C} {U} F Ψ Ψ' => ?_, fun {C} {U} F Ψ Ψ' => ?_,
    fun {C} {U} F Ψ Ψ' => ?_⟩ <;>
  · let Bc : C.BasicConstruction := ⟨U, ⟦F⟧⟩
    have := (hB C Bc F rfl).1 Ψ Ψ'
    first | exact this.2.1 | exact this.1 | exact this.2.2

#rt_check RoundTrip.V19_17.A_to_B [
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace]
#rt_check RoundTrip.V19_17.B_to_A [
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace]
#rt_overlap RoundTrip.V19_17.B_to_A [
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace]
#rt_check RoundTrip.V19_17.main_to_B [
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace]
#rt_check RoundTrip.V19_17.B_to_main [
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_3_3,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.t2Space,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.regularSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_isOpen_metrizableSpace]

end RoundTrip.V19_17
