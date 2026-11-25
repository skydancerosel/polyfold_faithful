import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_33

set_option maxSynthPendingDepth 3

/-! Round trip for V19_33 (2021 Theorem 19.5.3, p. 888).  Universes at `0`.

* (1): `B` reads "properness" as (v1) (`PropernessV1`), the project's `theorem_19_5_3_one` as (v2)
  (`PropernessV2 hB`); they are equivalent under `HasClassUniformizers` by the non-item
  `proposition_19_4_2_one_iff_two`.
* (2): `A` speaks of the specific `toPolyfoldConstruction hm`; `B` asks for some natural structure
  (uniformizer sets those of `F`, `M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`) tame for tame domains.
  `A_to_B`: `toPolyfoldConstruction` is natural (`natural_toPolyfoldConstruction`, definitional
  plus Lemma 19.3.1), tameness from `theorem_19_5_3_two`.  `B_to_A`: (1) from `B`; in (2) the
  tameness of `toPolyfoldConstruction` from `B`'s tame natural structure (same uniformizer sets);
  the rest of (2) (the defining equalities, covering, Lemma 17.1.9 for `Ψ̂`, tameness of `M` and of
  the models) and the side lemmas are re-proved outright from non-item lemmas. -/

namespace RoundTrip.V19_33
open Polyfold Polyfold.GroupoidalCategory Set
open Polyfold.GroupoidalCategory.BasicConstruction

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison.{0},
    @Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold.{0}⟩

/-- The project's `(F, M)` is natural in `B`'s sense. -/
theorem natural_toPolyfoldConstruction {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers)
    (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB)) :
    IsNaturalStructure B hB hm (toPolyfoldConstruction hm) := by
  refine ⟨fun α Ψ => Iff.rfl, fun α Ψ hΨ => ⟨toLocalUniformizer hm hΨ, hΨ, rfl⟩,
    fun Ψ Ψ' hΨ hΨ' F hF => ?_⟩
  show B.rep.topology _ _ = _
  exact TopologicalSpace.ext (UniformizerConstruction.TransitionData.lemma_19_3_1
    (Quotient.exact (B.mk_rep.trans hF.symm)) ⟨Ψ.1.toUniformizer, hΨ⟩ ⟨Ψ'.1.toUniformizer, hΨ'⟩)

theorem main_A_to_B
    (h1 : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one.{0})
    (h2 : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two.{0}) : B := by
  intro C B hB
  refine ⟨fun hv h => h1 B hB ((B.proposition_19_4_2_one_iff_two hB).1 hv) h, fun hm => ?_⟩
  refine ⟨toPolyfoldConstruction hm, natural_toPolyfoldConstruction B hB hm, fun ht => ?_⟩
  exact ((h2 hm).2.2.2.2 fun Ψ => ht Ψ.2.choose Ψ.1 Ψ.2.choose_spec).1

theorem A_to_B (hA : A) : B := main_A_to_B hA.1 hA.2.1

/-! ### `B ⇒ A` -/

section Copies
variable {C : GroupoidalCategory.{0}} {B : C.BasicConstruction} {hB : B.U.HasClassUniformizers}
  (hm : @TopologicalSpace.MetrizableSpace C.OrbitSpace (B.natTop hB))

theorem hasCovering' : (toPolyfoldConstruction hm).HasCoveringUniformizers := by
  refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
  obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
  refine ⟨⟨toLocalUniformizer hm hΨ, α, hΨ⟩, ?_⟩
  obtain ⟨-, hz⟩ := B.theorem_19_2_2_three hB hΨ
  rw [← hα]
  exact hz

theorem continuous_hat' (Ψ : (toPolyfoldConstruction hm).Unif) :
    Continuous ((toPolyfoldConstruction hm).hat Ψ) :=
  (B.rep.hatHomeomorph (toUnif hm Ψ)).continuous

theorem isTame_transPolyfold' {U : C.UniformizerConstruction} (F : U.TransitionData)
    (Ψ Ψ' : U.Unif) (hO : Ψ.1.P.IsTame) : (F.transPolyfold Ψ Ψ').IsTame :=
  (F.isLocalScDiffeo_src Ψ Ψ').isTame hO

theorem isEquivalence_modelFunctor' (c : (toPolyfoldConstruction hm).CoveringFamily) :
    ((toPolyfoldConstruction hm).modelFunctor c.Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph ((toPolyfoldConstruction hm).modelFunctor c.Ψ).orbitMap :=
  (toPolyfoldConstruction hm).lemma_17_1_15 c

theorem isGeneralizedIso_comparison' (c c' : (toPolyfoldConstruction hm).CoveringFamily) :
    EPLocalization.EPLoc.IsGeneralizedIso ((toPolyfoldConstruction hm).comparison c c') :=
  ((toPolyfoldConstruction hm).theorem_17_1_18 c c' c').1

/-- Theorem 19.5.3 (2) for `toPolyfoldConstruction`; the tameness of `(F, M)` is taken from `B`'s
natural structure (same uniformizer sets). -/
theorem two' (hB' : RoundTrip.V19_33.B) :
    type_of% (@Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two.{0} C B hB hm) := by
  refine ⟨fun α Ψ => ⟨fun h => ⟨toLocalUniformizer hm h, h, rfl⟩, ?_⟩, fun _ _ => rfl,
    hasCovering' hm,
    fun Ψ => ((toPolyfoldConstruction hm).lemma_17_1_9_of_continuous Ψ (continuous_hat' hm Ψ)).1,
    fun ht => ?_⟩
  · rintro ⟨Ψ', h, rfl⟩
    exact h
  obtain ⟨P, ⟨hPF, -, -⟩, hPT⟩ := (hB' C B hB).2 hm
  have hPT' := hPT fun α Ψ hΨ => ht ⟨Ψ, α, hΨ⟩
  have hT : (toPolyfoldConstruction hm).IsTame := fun α Ψ' h => hPT' α Ψ' ((hPF α Ψ').2 h)
  exact ⟨hT, fun Ψ Ψ' => isTame_transPolyfold' B.rep _ _ (ht (toUnif hm Ψ)),
    fun c => (toPolyfoldConstruction hm).isTame_modelEpGroupoid c.Ψ hT⟩

end Copies

theorem B_to_one (hB' : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one.{0} :=
  fun B hB hv h => (hB' _ B hB).1 ((B.proposition_19_4_2_one_iff_two hB).2 hv) h

/-- `B ⇒` the two main conjuncts (Theorem 19.5.3 (1) and (2)). -/
theorem main_B_to_A (hB' : B) :
    (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one.{0}) ∧
      (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two.{0}) :=
  ⟨B_to_one hB', fun hm => two' hm hB'⟩

theorem B_to_A (hB' : B) : A :=
  ⟨B_to_one hB', fun hm => two' hm hB', @continuous_hat', @hasCovering',
    @isEquivalence_modelFunctor', @isGeneralizedIso_comparison', @isTame_transPolyfold'⟩

#rt_check RoundTrip.V19_33.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two,
  Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat,
  Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction,
  Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor,
  Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold]
#rt_check RoundTrip.V19_33.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two,
  Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat,
  Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction,
  Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor,
  Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold]
#rt_check RoundTrip.V19_33.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two,
  Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat,
  Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction,
  Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor,
  Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold]
#rt_check RoundTrip.V19_33.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two,
  Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat,
  Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction,
  Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor,
  Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold]
#rt_overlap RoundTrip.V19_33.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two,
  Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat,
  Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction,
  Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor,
  Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold]
#rt_overlap RoundTrip.V19_33.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_3_two,
  Polyfold.GroupoidalCategory.BasicConstruction.continuous_hat,
  Polyfold.GroupoidalCategory.BasicConstruction.hasCoveringUniformizers_toPolyfoldConstruction,
  Polyfold.GroupoidalCategory.BasicConstruction.isEquivalence_modelFunctor,
  Polyfold.GroupoidalCategory.BasicConstruction.isGeneralizedIso_comparison,
  Polyfold.GroupoidalCategory.UniformizerConstruction.TransitionData.isTame_transPolyfold]

end RoundTrip.V19_33
