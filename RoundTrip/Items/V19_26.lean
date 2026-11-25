import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_26

set_option maxSynthPendingDepth 3

/-! Round trip for V19_26 (2021 Proposition 19.4.4, p. 883: under properness every `T_{Ψ,Ψ'}` is
metrizable).  Universes at `0` (the abstract sheet lemmas at `.{0, 0}`).  `A` =
`proposition_19_4_4` (`hB`, (v2) ⇒ `B.M Ψ Ψ'` metrizable) ∧ `metrizableSpace_M` (no properness) ∧
`TransitionData.metrizableSpace` (every transition data, no properness) ∧ `exists_nbhd_eq_map` ∧
`metrizableSpace_of_isLocalHomeomorph_of_finiteSheets` ∧
`paracompactSpace_of_isLocalHomeomorph_of_finiteSheets`.  `B`: for every representative `F`, (v1)
for `F` ⇒ every `F.Tr Ψ Ψ'` metrizable (no `HasClassUniformizers`).

* `A_to_B`: from `TransitionData.metrizableSpace` (properness is not needed).
* `main_B_to_A` (`B ⇒ proposition_19_4_4`): (v2) ⇒ (v1) (`proposition_19_4_2_one_iff_two`, outside
  this item), `F = B.rep`.
* `main_A_to_B_of_hB`: `proposition_19_4_4 ⇒ B` for basic constructions with
  `HasClassUniformizers`; without it `proposition_19_4_4` does not apply (its hypothesis `hB`).
* `B ⇒ A` is not proved: `metrizableSpace_M`, `TransitionData.metrizableSpace` assert metrizability
  without properness, and `exists_nbhd_eq_map` and the two sheet lemmas are proof steps; `B`, which
  assumes (v1), gives none of them. -/

namespace RoundTrip.V19_26
open Polyfold Polyfold.GroupoidalCategory Filter Topology

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.metrizableSpace_M.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.metrizableSpace.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_nbhd_eq_map.{0}) ∧
  (type_of% @Polyfold.Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets.{0, 0}) ∧
  (type_of% @Polyfold.Chapter19.paracompactSpace_of_isLocalHomeomorph_of_finiteSheets.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.metrizableSpace_M.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.metrizableSpace.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_nbhd_eq_map.{0},
    @Polyfold.Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets.{0, 0},
    @Polyfold.Chapter19.paracompactSpace_of_isLocalHomeomorph_of_finiteSheets.{0, 0}⟩

theorem topology_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    (Ψ Ψ' : B.U.Unif) : F.topology Ψ Ψ' = B.rep.topology Ψ Ψ' :=
  TopologicalSpace.ext (funext fun _ => propext (B.isOpen_M_iff hF).symm)

theorem tendsto_iff_of_eq {X : Type} {t₁ t₂ : TopologicalSpace X} (h : t₁ = t₂) (f : ℕ → X)
    (x : X) : @Tendsto ℕ X f atTop (@nhds X t₁ x) ↔ @Tendsto ℕ X f atTop (@nhds X t₂ x) := by
  subst h; rfl

theorem V1_iff {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕) :
    V1 F ↔ B.PropernessV1 := by
  constructor
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs p hp => ?_⟩
    obtain ⟨φ, x, hφ, hx⟩ := hW Ψ' h hs ⟨p, hp⟩
    exact ⟨φ, hφ, x, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).1 hx⟩
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs ⟨p, hp⟩ => ?_⟩
    obtain ⟨φ, hφ, x, hx⟩ := hW Ψ' h hs p hp
    exact ⟨φ, x, hφ, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).2 hx⟩

/-- `A ⇒ B`, from the conjunct `TransitionData.metrizableSpace` (the hypotheses `⟦F⟧ = 𝓕` and (v1)
are not needed). -/
theorem A_to_B : A → B := fun hA _ _ F _ _ Ψ Ψ' => hA.2.2.1 F Ψ Ψ'

/-- The main conjunct gives `B` for basic constructions with `HasClassUniformizers`. -/
theorem main_A_to_B_of_hB
    (hA : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4.{0})
    (C : GroupoidalCategory.{0}) (B : C.BasicConstruction) (F : B.U.TransitionData)
    (hB : B.U.HasClassUniformizers)
    (hF : Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F =
      B.𝓕)
    (hv : V1 F) (Ψ Ψ' : B.U.Unif) : TopologicalSpace.MetrizableSpace (F.Tr Ψ Ψ') := by
  rw [V1_iff B hF, B.proposition_19_4_2_one_iff_two hB] at hv
  have := hA B hB hv Ψ Ψ'
  exact (B.trHomeomorph hF Ψ Ψ').isEmbedding.metrizableSpace

theorem main_B_to_A (hB' : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4.{0} := by
  intro C B hB hv Ψ Ψ'
  exact hB' C B B.rep B.mk_rep ((V1_iff B B.mk_rep).2 ((B.proposition_19_4_2_one_iff_two hB).2 hv))
    Ψ Ψ'

#rt_check RoundTrip.V19_26.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4,
  Polyfold.GroupoidalCategory.BasicConstruction.metrizableSpace_M,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.metrizableSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_nbhd_eq_map,
  Polyfold.Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets,
  Polyfold.Chapter19.paracompactSpace_of_isLocalHomeomorph_of_finiteSheets]
#rt_check RoundTrip.V19_26.main_A_to_B_of_hB [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4,
  Polyfold.GroupoidalCategory.BasicConstruction.metrizableSpace_M,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.metrizableSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_nbhd_eq_map,
  Polyfold.Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets,
  Polyfold.Chapter19.paracompactSpace_of_isLocalHomeomorph_of_finiteSheets]
#rt_check RoundTrip.V19_26.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4,
  Polyfold.GroupoidalCategory.BasicConstruction.metrizableSpace_M,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.metrizableSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_nbhd_eq_map,
  Polyfold.Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets,
  Polyfold.Chapter19.paracompactSpace_of_isLocalHomeomorph_of_finiteSheets]
#rt_overlap RoundTrip.V19_26.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_4,
  Polyfold.GroupoidalCategory.BasicConstruction.metrizableSpace_M,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.metrizableSpace,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.exists_nbhd_eq_map,
  Polyfold.Chapter19.metrizableSpace_of_isLocalHomeomorph_of_finiteSheets,
  Polyfold.Chapter19.paracompactSpace_of_isLocalHomeomorph_of_finiteSheets]

end RoundTrip.V19_26
