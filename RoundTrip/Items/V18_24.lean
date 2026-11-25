import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_24

set_option maxSynthPendingDepth 3

/-! Round trip for V18_24 (2021 Theorem 18.2.2, p. 850; 2017: Theorem 18.3: compact moduli
space ⇔ proper ⇔ proper`<∞`).

`A` is the conjunction of `theorem_18_2_2.{0}` and the four witnesses on the reflection and
half-space bundles.

* `B_to_A`: `theorem_18_2_2` from `B` (its extra hypothesis `HasStrongBundleUniformizers` is not
  needed); the witnesses with their own proofs, `theorem_18_2_2` replaced by `B`.
* `A_to_B` is not proved: `theorem_18_2_2` assumes `F̄(α) ≠ ∅` for every `α`, `B` does not.
  `A_to_Bhf`: `A` gives `B` with that hypothesis added.
-/
namespace RoundTrip.V18_24
open Polyfold GCT.VectorBundle GCT.VectorBundle.StrongPolyfoldBundleConstruction

def A : Prop :=
  type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_2.{0} ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_hasCompactModuliSpace ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProper ∧
  type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProperLtInfty ∧
  type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfF_hasCompactModuliSpace

theorem A_holds : A :=
  ⟨@theorem_18_2_2.{0}, @ReflectionBundle.reflDiag_hasCompactModuliSpace,
   @ReflectionBundle.reflDiag_isProper, @ReflectionBundle.reflDiag_isProperLtInfty,
   @HalfSpaceReflection.halfF_hasCompactModuliSpace⟩

/-- `B` with the standing hypothesis `F̄(α) ≠ ∅` added. -/
def Bhf : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor),
    Q.HasStrongBundleUniformizers → Q.IsScFredholmSectionFunctor f →
      (f.HasCompactModuliSpace ↔ Q.IsProper f) ∧ (f.HasCompactModuliSpace ↔ Q.IsProperLtInfty f)

theorem A_to_Bhf : A → Bhf := by
  rintro ⟨h, -⟩ C S V Q f hF hf
  have t := h Q f hF hf
  exact ⟨t.out 0 1, t.out 0 2⟩

theorem Bhf_to_main : Bhf → type_of% @theorem_18_2_2.{0} := by
  intro hB C V S Q f hF hf
  obtain ⟨h12, h13⟩ := hB C S V Q f hF hf
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := h13
  tfae_finish

theorem B_to_Bhf : B → Bhf := fun h C S V Q f _ hf => h C S V Q f hf

section
open Polyfold.GCT.VectorBundle.ReflectionBundle Polyfold.GCT.VectorBundle.HalfSpaceReflection
  Polyfold.GCT.PolyfoldConstruction Polyfold.HalfSpaceBundle Set

theorem B_to_A : B → A := by
  intro hB
  have hm : reflDiag.HasCompactModuliSpace := by
    unfold SectionFunctor.HasCompactModuliSpace
    rw [reflDiag_zeroSet, image_singleton]
    exact isCompact_singleton
  have hpair := hB _ _ _ reflQ reflDiag isScFredholmSectionFunctor_reflDiag
  refine ⟨Bhf_to_main (B_to_Bhf hB), hm, hpair.1.1 hm, hpair.2.1 hm, ?_⟩
  unfold SectionFunctor.HasCompactModuliSpace
  rw [halfF_zeroSet]
  exact ((quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.isCompact_preimage
    isCompact_halfDiscMap_zero).image continuous_quot_mk

end

#rt_check RoundTrip.V18_24.B_to_A [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_2, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_hasCompactModuliSpace, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProper, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProperLtInfty, Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfF_hasCompactModuliSpace]
#rt_check RoundTrip.V18_24.A_to_Bhf [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_2, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_hasCompactModuliSpace, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProper, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProperLtInfty, Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfF_hasCompactModuliSpace]
#rt_check RoundTrip.V18_24.Bhf_to_main [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_2, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_hasCompactModuliSpace, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProper, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProperLtInfty, Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfF_hasCompactModuliSpace]
#rt_overlap RoundTrip.V18_24.B_to_A [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_2_2, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_hasCompactModuliSpace, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProper, Polyfold.GCT.VectorBundle.ReflectionBundle.reflDiag_isProperLtInfty, Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfF_hasCompactModuliSpace]

end RoundTrip.V18_24
