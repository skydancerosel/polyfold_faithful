import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_28

set_option maxSynthPendingDepth 3

/-! Round trip for V18_28 (2021 Theorem 18.2.6, p. 851; 2017: Theorem 18.4: extending a
neighbourhood of `|∂C|` controlling compactness).

`A` is the conjunction of `theorem_18_2_6.{0}`, `mem_boundary_model_iff.{0}` and the three
witnesses (`reflection_boundarySet`, `theorem_18_2_6_witness`, `theorem_18_2_6_witness_boundary`).

* `B_to_A`: `B`'s hypotheses are among `theorem_18_2_6`'s, so `B` gives it; the other conjuncts
  are re-proved with their own proofs (`theorem_18_2_6` replaced by `B`).
* `A_to_B` is not proved: `theorem_18_2_6` assumes in addition `F̄(α) ≠ ∅`, `S.IsTame` and
  `f.HasCompactModuliSpace`.  `A_to_Bplus`: `A` gives `B` with these three hypotheses added.
-/
namespace RoundTrip.V18_28
open Polyfold GCT.VectorBundle GCT.VectorBundle.StrongPolyfoldBundleConstruction

def A : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_6.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.mem_boundary_model_iff.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_boundarySet ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_2_6_witness ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_2_6_witness_boundary

theorem A_holds : A :=
  ⟨@theorem_18_2_6.{0}, @mem_boundary_model_iff.{0}, @ReflectionBundle.reflection_boundarySet,
   @ReflectionBundle.theorem_18_2_6_witness,
   @HalfSpaceReflection.theorem_18_2_6_witness_boundary⟩

/-- `B` with `F̄(α) ≠ ∅`, `S.IsTame` and `|S_f|` compact added. -/
def Bplus : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
    Q.HasStrongBundleUniformizers → S.IsTame → f.HasCompactModuliSpace →
    Q.IsScFredholmSectionFunctor f → Q.HasReflexiveFibers → Q.HasReflexiveLocalCompactness f →
    ∀ N : V.EObj → ENNReal, Q.IsReflexiveAuxNormFunctor N →
    ∀ Ub : Set C.toGroupoidStr.OrbitSpace,
      (∃ W : Set C.toGroupoidStr.OrbitSpace, IsOpen W ∧
        Ub = W ∩ C.toGroupoidStr.π '' S.boundarySet) →
      C.toGroupoidStr.π '' (f.zeroSet ∩ S.boundarySet) ⊆ Ub →
      IsCompact (closure (Ub ∩ f.sublevel N 1)) →
      ∃ U : Set C.toGroupoidStr.OrbitSpace, f.ControlsCompactness N U ∧
        U ∩ C.toGroupoidStr.π '' S.boundarySet = Ub

theorem A_to_Bplus : A → Bplus := by
  rintro ⟨h, -⟩ C S V Q f hF hT hS hf hB hlc N hN Ub hUb hSUb hc
  obtain ⟨U, h1, h2⟩ := h Q f hF hT hB hN hf hS hlc hUb hSUb hc
  exact ⟨U, h2, h1⟩

theorem B_to_main : B → type_of% @theorem_18_2_6.{0} := by
  intro hB C V S Q f _ _ hBf N hN hf _ hlc Ub hUb hSUb hc
  obtain ⟨U, h1, h2⟩ := hB C S V Q f hf hBf hlc N hN Ub hUb hSUb hc
  exact ⟨U, h2, h1⟩

section
open Polyfold.GCT.VectorBundle.ReflectionBundle Polyfold.GCT.VectorBundle.HalfSpaceReflection
  Polyfold.GCT.PolyfoldConstruction Polyfold.HalfSpaceBundle Set

theorem B_to_A : B → A := by
  intro hB
  have h6 : type_of% @theorem_18_2_6.{0} := B_to_main hB
  have hrb : reflectionConstruction.boundarySet = ∅ := by
    refine eq_empty_of_forall_notMem fun α (hα : 1 ≤ reflectionConstruction.degIndex α) => ?_
    rw [reflectionConstruction.definition_17_1_30 (α := α) (Ψ := GCT.LocalUniformizer.reflection) rfl
      (q := α) rfl] at hα
    have := rnPolyfold_degIndex 1 α
    change 1 ≤ (rnPolyfold 1).degIndex α at hα
    omega
  refine ⟨h6, ?_, hrb, ?_, ?_⟩
  · intro C V S Q c x
    change 1 ≤ (S.modelEP (Q.modelBase c.Ψ)).X.PObj.degIndex x ↔
      (S.modelFunctor (Q.modelBase c.Ψ)).obj x ∈
        C.toGroupoidStr.π ⁻¹' (C.toGroupoidStr.π '' S.boundarySet)
    rw [S.isSaturated_boundarySet, ← degIndex_modelFunctor_obj]
    rfl
  · obtain ⟨N, hN⟩ := reflQ_exists_isReflexiveAuxNormFunctor
    refine ⟨N, hN, reflectionConstruction_isTame, reflQ_hasReflexiveFibers,
      isScFredholmSectionFunctor_reflDiag, reflDiag_hasCompactModuliSpace,
      reflDiag_hasReflexiveLocalCompactness, ?_⟩
    refine h6 reflQ reflDiag reflQ_hasStrongBundleUniformizers
      reflectionConstruction_isTame reflQ_hasReflexiveFibers hN isScFredholmSectionFunctor_reflDiag
      reflDiag_hasCompactModuliSpace reflDiag_hasReflexiveLocalCompactness
      ⟨∅, isOpen_empty, (empty_inter _).symm⟩ ?_ ?_
    · rw [hrb, inter_empty, image_empty]
    · rw [empty_inter, closure_empty]
      exact isCompact_empty
  · obtain ⟨N, hN⟩ := halfQ.exists_isReflexiveAuxNormFunctor halfQ_hasStrongBundleUniformizers
      halfQ_hasReflexiveFibers
    refine ⟨N, hN, halfS_isTame, halfQ_hasReflexiveFibers, isScFredholmSectionFunctor_halfF,
      halfF_hasCompactModuliSpace, halfF_hasReflexiveLocalCompactness, topPoint_mem_halfUb, ?_⟩
    refine h6 halfQ halfF halfQ_hasStrongBundleUniformizers halfS_isTame
      halfQ_hasReflexiveFibers hN isScFredholmSectionFunctor_halfF halfF_hasCompactModuliSpace
      halfF_hasReflexiveLocalCompactness ⟨halfW', isOpen_halfW', rfl⟩
      zeroSet_boundary_subset_halfUb ?_
    refine isCompact_closedBallH.closure_of_subset (inter_subset_left.trans
      (inter_subset_left.trans (image_mono fun x hx =>
        show ‖(x : Pm 1)‖ ≤ 2 from le_of_lt hx)))

end

#rt_check RoundTrip.V18_28.B_to_A [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_6, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.mem_boundary_model_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_boundarySet, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_2_6_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_2_6_witness_boundary]
#rt_check RoundTrip.V18_28.B_to_main [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_6, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.mem_boundary_model_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_boundarySet, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_2_6_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_2_6_witness_boundary]
#rt_check RoundTrip.V18_28.A_to_Bplus [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_6, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.mem_boundary_model_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_boundarySet, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_2_6_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_2_6_witness_boundary]
#rt_overlap RoundTrip.V18_28.B_to_A [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_6, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.mem_boundary_model_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflection_boundarySet, Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_2_6_witness, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_2_6_witness_boundary]

end RoundTrip.V18_28
