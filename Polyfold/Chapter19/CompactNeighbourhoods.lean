import Polyfold.Chapter19.PolyfoldStructureGCT
import Polyfold.Chapter19.TopologyLemmasTwo
import Polyfold.Chapter19.MetrizabilityExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5: **Remark 19.5.4** (p. 888).  Numbers and pages are the 2021 text's.

# Metrizable neighbourhoods of compact sets in `|S|`

## The text, paraphrased

(Remark 19.5.4) In applications one first obtains the natural topology `T` of `|S|` and the
natural topologies of the transition sets; `T` is locally metrizable.  After checking the
properness condition for `(F, 𝓕)` one concludes that `T` is completely regular, Hausdorff and
locally metrizable.  These facts imply that a given compact `K ⊂ |S|` has an open neighbourhood
`U = U(K)` which is paracompact and hence metrizable.  If `T` is also second countable, `T` is
metrizable and there is an associated polyfold construction `(F, M)`; the same holds if `T` is
paracompact.  If all uniformizers of `F` are tame, the polyfold construction is tame.

## What is formalized (namespace `Polyfold.GroupoidalCategory.BasicConstruction`)

* **`remark_19_5_4`**: under the properness condition (v2), `T` is Hausdorff and completely regular
  (Proposition 19.4.5), locally metrizable (Theorem 19.2.2 (5)), every compact `K` has an open
  metrizable and paracompact neighbourhood (`Chapter19.exists_isOpen_metrizableSpace_of_isCompact`),
  and if `T` is second countable or paracompact it is metrizable and the polyfold construction
  `(F, M)` of Theorem 19.5.3 (2) is tame when all uniformizers of `F` are.
* `reflectionBasic_remark_19_5_4`: the hypothesis holds for the reflection `ℤ/2 ⋉ ℝ` (isotropy
  `ℤ/2` at `0`), so every compact subset of its orbit space has such a neighbourhood.

## Reading

* "The properness condition" for `T` is read as (v2) for `(F, 𝓕)` (`PropernessV2`, Definition
  19.4.1 (2)), as in Theorem 19.5.3 (1).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

namespace BasicConstruction

variable (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers)

/-- **2021 Remark 19.5.4, p. 888**: under the properness condition, the natural topology `T` is
Hausdorff, completely regular and locally metrizable; every compact `K ⊂ |S|` has an open
neighbourhood `U(K)` which is paracompact and metrizable; and if `T` is second countable or
paracompact, it is metrizable, and the associated polyfold construction `(F, M)` is tame when
every uniformizer of `F` has a tame domain. -/
theorem remark_19_5_4 (hv : B.PropernessV2 hB) :
    @T2Space _ (B.natTop hB) ∧ @CompletelyRegularSpace _ (B.natTop hB) ∧
      (∀ z : C.OrbitSpace, ∃ W : Set C.OrbitSpace, IsOpen[B.natTop hB] W ∧ z ∈ W ∧
        @MetrizableSpace W (@instTopologicalSpaceSubtype _ _ (B.natTop hB))) ∧
      (∀ K : Set C.OrbitSpace, @IsCompact _ (B.natTop hB) K →
        ∃ U : Set C.OrbitSpace, IsOpen[B.natTop hB] U ∧ K ⊆ U ∧
          @MetrizableSpace U (@instTopologicalSpaceSubtype _ _ (B.natTop hB)) ∧
          @ParacompactSpace U (@instTopologicalSpaceSubtype _ _ (B.natTop hB))) ∧
      ((@SecondCountableTopology _ (B.natTop hB) ∨ @ParacompactSpace _ (B.natTop hB)) →
        ∃ hm : @MetrizableSpace C.OrbitSpace (B.natTop hB),
          (∀ Ψ : B.U.Unif, Ψ.1.P.IsTame) → (toPolyfoldConstruction hm).IsTame) := by
  let _inst := B.natTop hB
  obtain ⟨h2, h3⟩ := B.proposition_19_4_5 hB hv
  refine ⟨h2, h3, B.theorem_19_2_2_five hB, fun K hK => ?_, fun h => ?_⟩
  · exact Chapter19.exists_isOpen_metrizableSpace_of_isCompact (B.theorem_19_2_2_five hB) hK
  · have hm := B.theorem_19_5_3_one hB hv h
    exact ⟨hm, fun ht => ((theorem_19_5_3_two hm).2.2.2.2 ht).1⟩

end BasicConstruction

/-- **Remark 19.5.4 in a non-degenerate case**: the reflection basic construction `ℤ/2 ⋉ ℝ`
(isotropy `ℤ/2` at the fixed point `0`) satisfies the properness condition, so every compact
subset of its orbit space has an open metrizable, paracompact neighbourhood. -/
theorem reflectionBasic_remark_19_5_4 :
    reflectionBasic.PropernessV2 reflectionBasic_hB ∧
      ∀ K, @IsCompact _ (reflectionBasic.natTop reflectionBasic_hB) K →
        ∃ U, IsOpen[reflectionBasic.natTop reflectionBasic_hB] U ∧ K ⊆ U ∧
          @MetrizableSpace U (@instTopologicalSpaceSubtype _ _
            (reflectionBasic.natTop reflectionBasic_hB)) ∧
          @ParacompactSpace U (@instTopologicalSpaceSubtype _ _
            (reflectionBasic.natTop reflectionBasic_hB)) :=
  ⟨reflectionBasic_propernessV2,
    (reflectionBasic.remark_19_5_4 reflectionBasic_hB reflectionBasic_propernessV2).2.2.2.1⟩

end GroupoidalCategory

end Polyfold
