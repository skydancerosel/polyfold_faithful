import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_21

set_option maxSynthPendingDepth 3

/-! Round trip for V18_21 (2021 Theorem 18.1.12, p. 848; 2017: Theorem 18.2: existence and
extension of auxiliary norms).

`A` is the conjunction of the types of the item's fifteen theorems (`IsBoundaryAuxNormIn`,
`IsReflexiveBoundaryAuxNormIn` are vocabulary), the four general ones at universe `0`.

* `A_to_B`: (2), (3) and the reflexive (3) from `theorem_18_1_12_two`, `_three`,
  `_three_reflexive` (with no covering family, `IsReflexiveAuxNormFunctor` is vacuous and
  `0 ≤ N ≤ ⊤` does it).  (1) of `B` has no hypothesis `F̄(α) ≠ ∅`, while `theorem_18_1_12_one`
  assumes it; `B`'s (1) is proved from a covering family directly (Theorem 12.2.2 in the model,
  pushed forward: the argument of `exists_isAuxNormFunctor`), or vacuously when there is none.
* `B_to_A`: (1) through the reference covering family and `IsAuxNormIn.isAuxNormDirect`
  (Lemma 18.1.8); (2), (3) directly; the witnesses re-proved with their own proofs, the item's
  theorems replaced by `B`'s clauses.
-/
namespace RoundTrip.V18_21
open Polyfold GCT.VectorBundle GCT.VectorBundle.StrongPolyfoldBundleConstruction
open scoped ENNReal

def A : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormDirect ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormBook ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflPair_hasReflexivePieces ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_two ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_witness_boundary ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.isAuxNormFunctor_halfNorm

theorem A_holds : A :=
  ⟨@theorem_18_1_12_one.{0}, @theorem_18_1_12_two.{0}, @theorem_18_1_12_three.{0},
   @theorem_18_1_12_three_reflexive.{0},
   @ReflectionBundle.reflQ_exists_isAuxNormDirect,
   @ReflectionBundle.reflQ_exists_isAuxNormBook,
   @ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect,
   @ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff,
   @ReflectionBundle.reflPair_hasReflexivePieces,
   @ReflectionBundle.reflQ_theorem_18_1_12_two,
   @ReflectionBundle.reflQ_theorem_18_1_12_three,
   @ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive,
   @HalfSpaceReflection.theorem_18_1_12_three_witness_boundary,
   @HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary,
   @HalfSpaceReflection.isAuxNormFunctor_halfNorm⟩

/-- `B`'s (1), with no hypothesis: from a covering family (Theorem 12.2.2 in its model), or
vacuously. -/
theorem exists_auxNorm {C : GCT.{0}} {S : C.PolyfoldConstruction} {V : C.VectorBundle}
    (Q : V.StrongPolyfoldBundleConstruction S) : ∃ N : V.EObj → ENNReal, Q.IsAuxNormFunctor N := by
  by_cases h : Nonempty Q.BundleCoveringFamily
  · obtain ⟨c⟩ := h
    obtain ⟨N', hN'⟩ := (Q.modelSEP c.Ψ).E.theorem_12_2_2 (hasParacompactOrbitSpace_model c)
    exact ⟨_, (Q.isAuxNormFunctor_iff_model c).2 (isAuxNormIn_pushNormFun c.cover hN')⟩
  · exact ⟨0, fun c => (h ⟨c⟩).elim⟩

theorem A_to_B : A → B := by
  rintro ⟨-, h2, h3, h3r, -⟩ C S V Q
  refine ⟨exists_auxNorm Q, fun hB N hN => ?_, fun hT N ⟨c, hc⟩ => h3 c hT hc,
    fun hT hB N ⟨c, hc⟩ => h3r c hT hB hc⟩
  by_cases h : Nonempty Q.BundleCoveringFamily
  · obtain ⟨c⟩ := h
    exact h2 c hB hN
  · exact ⟨0, ⊤, fun c => (h ⟨c⟩).elim, fun c => (h ⟨c⟩).elim,
      fun e => ⟨bot_le, le_top⟩⟩

section
open Polyfold.GCT.VectorBundle.ReflectionBundle Polyfold.GCT.VectorBundle.HalfSpaceReflection Polyfold.GCT.PolyfoldConstruction

theorem B_to_A : B → A := by
  intro hB
  have h1 : type_of% @theorem_18_1_12_one.{0} := by
    intro C V S Q hF
    obtain ⟨N, hN⟩ := (hB C S V Q).1
    exact ⟨N, (hN (Q.refCoveringFamily hF)).isAuxNormDirect⟩
  have h2 : type_of% @theorem_18_1_12_two.{0} :=
    fun {C V S Q} _ hBf {N'} hN' => (hB C S V Q).2.1 hBf N' hN'
  have h3 : type_of% @theorem_18_1_12_three.{0} :=
    fun {C V S Q} c hT {N} hN => (hB C S V Q).2.2.1 hT N ⟨c, hN⟩
  have h3r : type_of% @theorem_18_1_12_three_reflexive.{0} :=
    fun {C V S Q} c hT hBf {N} hN => (hB C S V Q).2.2.2 hT hBf N ⟨c, hN⟩
  have w1 : ∃ N : reflV.EObj → ℝ≥0∞, reflQ.IsAuxNormDirect N :=
    h1 reflQ_hasStrongBundleUniformizers
  have w9 : reflQ.HasReflexivePieces reflPair :=
    fun _ => StrongBundle.hasReflexiveFibers_of_atlas fun c hc => by
      obtain ⟨a, rfl⟩ := hc
      exact isReflexive_of_finiteDimensional (F := Fin 1 → ℝ)
  refine ⟨h1, h2, h3, h3r, w1, ?_, ?_, ?_, w9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := w1
    exact ⟨N, hN.toIsAuxNormBook⟩
  · obtain ⟨N, hN⟩ := reflQ_exists_isReflexiveAuxNormFunctor
    exact ⟨N, hN.isReflexiveAuxNormDirect reflPair⟩
  · intro N
    exact reflQ.isReflexiveAuxNormDirect_iff_hyp reflPair w9
  · obtain ⟨N', hN'⟩ := reflQ_exists_isAuxNormFunctor
    exact ⟨N', hN', reflQ_hasReflexiveFibers,
      h2 reflPair reflQ_hasReflexiveFibers hN'⟩
  · obtain ⟨N, hN⟩ := reflQ_exists_isAuxNormFunctor
    have hb := (hN reflPair).isBoundaryAuxNormIn
    exact ⟨reflectionConstruction_isTame, N, hb,
      h3 reflPair reflectionConstruction_isTame hb⟩
  · obtain ⟨N, hN⟩ := reflQ_exists_isReflexiveAuxNormFunctor
    have hb := (hN reflPair).isReflexiveBoundaryAuxNormIn
    exact ⟨N, hb, h3r reflPair reflectionConstruction_isTame reflQ_hasReflexiveFibers hb⟩
  · have hb : halfQ.IsBoundaryAuxNormIn halfSingle (boundaryOnly halfNorm) :=
      isAuxNormIn_halfNorm.isBoundaryAuxNormIn.congr_boundary fun e he => boundaryOnly_of_mem _ he
    obtain ⟨Ñ, hÑ, hÑe⟩ := h3 halfSingle halfS_isTame hb
    refine ⟨halfS_isTame, corner_mem_boundarySet, hb, not_isAuxNormFunctor_boundaryOnly _, Ñ,
      hÑ, hÑe, fun α hα w => ?_⟩
    rw [hÑe _ hα, boundaryOnly_of_mem _ hα, halfNorm_objMk]
  · obtain ⟨N, hN⟩ := halfQ.exists_isReflexiveAuxNormFunctor halfQ_hasStrongBundleUniformizers
      halfQ_hasReflexiveFibers
    have hb : halfQ.IsReflexiveBoundaryAuxNormIn halfSingle (boundaryOnly N) :=
      (hN halfSingle).isReflexiveBoundaryAuxNormIn.congr_boundary fun e he =>
        boundaryOnly_of_mem _ he
    exact ⟨halfS_isTame, halfQ_hasReflexiveFibers, corner_mem_boundarySet, N, hN, hb,
      not_isAuxNormFunctor_boundaryOnly _, h3r halfSingle halfS_isTame halfQ_hasReflexiveFibers hb⟩
  · exact (halfQ.isAuxNormFunctor_iff_model halfSingle).2 isAuxNormIn_halfNorm

end

/-- Main conjunct `theorem_18_1_12_two` against `B`'s (2). -/
theorem main_to_B2 :
    type_of% @theorem_18_1_12_two.{0} →
    ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
      (Q : V.StrongPolyfoldBundleConstruction S),
      (Q.HasReflexiveFibers → ∀ N : V.EObj → ENNReal, Q.IsAuxNormFunctor N →
        ∃ N₁ N₂ : V.EObj → ENNReal, Q.IsReflexiveAuxNormFunctor N₁ ∧
          Q.IsReflexiveAuxNormFunctor N₂ ∧ ∀ e : V.EObj, N₁ e ≤ N e ∧ N e ≤ N₂ e) := by
  intro h2 C S V Q hB N hN
  by_cases h : Nonempty Q.BundleCoveringFamily
  · obtain ⟨c⟩ := h
    exact h2 c hB hN
  · exact ⟨0, ⊤, fun c => (h ⟨c⟩).elim, fun c => (h ⟨c⟩).elim,
      fun e => ⟨bot_le, le_top⟩⟩

theorem B2_to_main :
    (∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
      (Q : V.StrongPolyfoldBundleConstruction S),
      (Q.HasReflexiveFibers → ∀ N : V.EObj → ENNReal, Q.IsAuxNormFunctor N →
        ∃ N₁ N₂ : V.EObj → ENNReal, Q.IsReflexiveAuxNormFunctor N₁ ∧
          Q.IsReflexiveAuxNormFunctor N₂ ∧ ∀ e : V.EObj, N₁ e ≤ N e ∧ N e ≤ N₂ e)) →
    type_of% @theorem_18_1_12_two.{0} :=
  fun h {C V S Q} _ hBf {N'} hN' => h C S V Q hBf N' hN'

#rt_check RoundTrip.V18_21.A_to_B [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormBook, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflPair_hasReflexivePieces, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_two, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.isAuxNormFunctor_halfNorm]
#rt_check RoundTrip.V18_21.B_to_A [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormBook, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflPair_hasReflexivePieces, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_two, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.isAuxNormFunctor_halfNorm]
#rt_check RoundTrip.V18_21.main_to_B2 [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormBook, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflPair_hasReflexivePieces, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_two, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.isAuxNormFunctor_halfNorm]
#rt_check RoundTrip.V18_21.B2_to_main [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormBook, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflPair_hasReflexivePieces, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_two, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.isAuxNormFunctor_halfNorm]
#rt_overlap RoundTrip.V18_21.B_to_A [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_one, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_two, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three, Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isAuxNormBook, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_exists_isReflexiveAuxNormDirect, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_isReflexiveAuxNormDirect_iff, Polyfold.GCT.VectorBundle.ReflectionBundle.reflPair_hasReflexivePieces, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_two, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three, Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_theorem_18_1_12_three_reflexive, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_1_12_three_reflexive_witness_boundary, Polyfold.GCT.VectorBundle.HalfSpaceReflection.isAuxNormFunctor_halfNorm]

end RoundTrip.V18_21
