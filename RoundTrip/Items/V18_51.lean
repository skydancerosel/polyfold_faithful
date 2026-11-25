import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_51

set_option maxSynthPendingDepth 3

/-! Round trip for V18_51 (2021 Theorem 18.6.1, pp. 860–861; 2017: Theorem 18.8: the perturbation
theorem).

The item lists the definitions `IsTransversalIn`, `IsInGeneralPositionIn`, `IsTransversalFunctor`,
`IsInGeneralPositionFunctor`, `IsContinuousFunctionFunctor` (vocabulary) and sixteen theorems:
`theorem_18_6_1_existence`, `exists_push_of_model`, `theorem_18_6_1_structurable`,
`theorem_18_6_1_in_particular`, `theorem_18_6_1` (all in a covering model `c`),
`theorem_18_6_1_modelFree`, `theorem_18_6_1_in_particular_modelFree`, the model-independence
lemmas `isTransversalIn_iff`, `isInGeneralPositionIn_iff`, `isTransversalFunctor_iff_forall`,
`isInGeneralPositionFunctor_iff_forall`, and the example witnesses on the reflection bundle and the
half-space reflection.  `A` is their conjunction at universe `0`.

## Comparison

The closest conjunct to `B` is `theorem_18_6_1_modelFree` (same standing hypothesis
`HasStrongBundleUniformizers`, (3), (4) model-free).  Against it:

* **Hypotheses of `A` that `B` lacks.**  (i) `hfT : Q.IsScFredholmSectionFunctorTame f` (every
  representative has germ data in tame charts, Definition 3.6.4 tame form); the project carries it
  as a standing reading and has no lemma deriving it from `IsScFredholmSectionFunctor f` and
  `S.IsTame`.  (ii) `hN : Q.IsAuxNormFunctor N` (an auxiliary norm in every covering model,
  Lemma 18.1.8's right side, with continuity of `N` on `W_{0,1}`), where `B` has the printed
  Definition 18.1.7, `Q.IsAuxNormBook N`, which does not ask for continuity; the project shows
  `IsAuxNormIn ⇒ IsAuxNormBook` and that the converse does not hold
  (`lemma_18_1_8_book_without_continuity`).  Both extra hypotheses are satisfiable (the witnesses).
* **Conclusions.**  `A` says `Λ ∘ f` is tame in the model sense (`IsTameModel`, Definition
  17.5.3 (2)); `B` in the uniformizer sense (`IsTameSubcategory`, Definition 17.5.4 (3)).  They
  agree under `HasUniformizers` (`definition_17_5_4_three`), which follows from
  `HasStrongBundleUniformizers`.  `IsScPlusMultisectionFunctor` follows from structurability.

So `B ⇒ main` is proved (`B_to_main`), and `main ⇒ B` holds once the two extra hypotheses are
added to `B` (`main_to_B_tame`); without them `A_to_B` is not available.  The full `A` also
contains the "in particular" for every `Λ` with `N(Λ) ≤ 1`, `|dom-supp(Λ)| ⊆ U` and (4),
model-specific lemmas (`IsTransversalIn` in a given model `c`, without `HasStrongBundleUniformizers`)
and concrete witnesses, none of which follows from `B`'s single existence statement. -/

namespace RoundTrip.V18_51
open Polyfold GCT.VectorBundle GCT.VectorBundle.StrongPolyfoldBundleConstruction

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_existence.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_push_of_model.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_structurable.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular_modelFree.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalIn_iff.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionIn_iff.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalFunctor_iff_forall.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionFunctor_iff_forall.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_witness) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_modelFree_witness) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_isContinuousFunctionFunctor_one) ∧
  (type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_witness_boundary) ∧
  (type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_modelFree_witness_boundary)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_existence.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_push_of_model.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_structurable.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular_modelFree.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalIn_iff.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionIn_iff.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalFunctor_iff_forall.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionFunctor_iff_forall.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_witness,
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_modelFree_witness,
    @Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_isContinuousFunctionFunctor_one,
    @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_witness_boundary,
    @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_modelFree_witness_boundary⟩

/-- The main conjunct: Theorem 18.6.1, model-free form. -/
def Amain : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree.{0}

/-- `F̄(α) ≠ ∅` gives `F(α) ≠ ∅`. -/
theorem hasUniformizers_of {C : GCT.{0}} {S : C.PolyfoldConstruction} {V : C.VectorBundle}
    {Q : V.StrongPolyfoldBundleConstruction S} (hF : Q.HasStrongBundleUniformizers) :
    S.HasUniformizers :=
  fun α => ⟨_, Q.base_mem α _ (Q.refBundleUnif_mem (hF α))⟩

/-- **`B ⇒ main`**: apply `B` with the printed form of the auxiliary norm (implied by the model
form) and turn uniformizer-tameness into model-tameness (`definition_17_5_4_three`). -/
theorem B_to_main : B → Amain := by
  intro hB C V S Q hF hT hbump f hf hfT hS N hN U hcc h hh hh01
  obtain ⟨Λ, -, h1, h2, h3, h4, hK, hTame, hBr, hStr⟩ :=
    hB C S V Q hF hT hbump f hf hS N U (hN (Q.refCoveringFamily hF)).isAuxNormBook hcc h hh hh01
  refine ⟨Λ, hStr, h1, h2, h3, h4, hBr, hK, ⟨(Q.refCoveringFamily hF).base, ?_⟩⟩
  exact (Polyfold.GCT.PolyfoldConstruction.definition_17_5_4_three (hasUniformizers_of hF)
    (isFunctorial_comp_sectionFunctor f hStr.1) _).1 hTame

/-- `B` with the two hypotheses of `A` that `B` lacks: tame germ data `hfT` and the model form
`IsAuxNormFunctor` of the auxiliary norm. -/
def Btame : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S),
    Q.HasStrongBundleUniformizers → S.IsTame → S.AdmitsModelBumpFunctions →
    ∀ (f : V.SectionFunctor), Q.IsScFredholmSectionFunctor f →
      Q.IsScFredholmSectionFunctorTame f → f.HasCompactModuliSpace →
    ∀ (N : V.EObj → ENNReal) (U : Set C.toGroupoidStr.OrbitSpace),
      Q.IsAuxNormFunctor N → f.ControlsCompactness N U →
    ∀ (h : C.Obj → ℝ), S.IsContinuousFunctionFunctor h → (∀ α, 0 < h α ∧ h α ≤ 1) →
    ∃ Λ : V.EObj → ℚ≥0,
      Q.IsScPlusMultisectionFunctor Λ ∧
      (∀ α, GCT.VectorBundle.pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧
      GCT.VectorBundle.orbitDomSupp Λ ⊆ U ∧
      Q.IsTransversalFunctor f Λ ∧
      Q.IsInGeneralPositionFunctor f Λ ∧
      C.IsCompactBranched (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) ∧
      S.IsTameSubcategory (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) ∧
      S.IsBranchedSubcategory (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) ∧
      Q.IsStructurableFunctor Λ

/-- **`main ⇒ B` with `hfT` and `IsAuxNormFunctor` added**: the only gap is these two
hypotheses. -/
theorem main_to_B_tame : Amain → Btame := by
  intro hM C S V Q hF hT hbump f hf hfT hS N U hN hcc h hh hh01
  obtain ⟨Λ, hStr, h1, h2, h3, h4, hBr, hK, c, hTv⟩ :=
    @hM C V S Q hF hT hbump f hf hfT hS N hN U hcc h hh hh01
  refine ⟨Λ, hStr.isScPlusMultisectionFunctor, h1, h2, h3, h4, hK, ?_, hBr, hStr⟩
  exact (Polyfold.GCT.PolyfoldConstruction.definition_17_5_4_three (hasUniformizers_of hF)
    (isFunctorial_comp_sectionFunctor f hStr.1) _).2 hTv

#rt_check RoundTrip.V18_51.B_to_main [
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_existence,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_push_of_model,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_structurable,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular_modelFree,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalIn_iff,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionIn_iff,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalFunctor_iff_forall,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionFunctor_iff_forall,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_modelFree_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_isContinuousFunctionFunctor_one,
  Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_witness_boundary,
  Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_modelFree_witness_boundary]
#rt_check RoundTrip.V18_51.main_to_B_tame [
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_existence,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_push_of_model,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_structurable,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular_modelFree,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalIn_iff,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionIn_iff,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalFunctor_iff_forall,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionFunctor_iff_forall,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_modelFree_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_isContinuousFunctionFunctor_one,
  Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_witness_boundary,
  Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_modelFree_witness_boundary]
#rt_overlap RoundTrip.V18_51.B_to_main [
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_existence,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.exists_push_of_model,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_structurable,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_modelFree,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1_in_particular_modelFree,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalIn_iff,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionIn_iff,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isTransversalFunctor_iff_forall,
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isInGeneralPositionFunctor_iff_forall,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_6_1_modelFree_witness,
  Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_isContinuousFunctionFunctor_one,
  Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_witness_boundary,
  Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_6_1_modelFree_witness_boundary]

end RoundTrip.V18_51
