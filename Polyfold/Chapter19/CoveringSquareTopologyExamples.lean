import Polyfold.Chapter19.CoveringSquareTopology
import Polyfold.Chapter19.CoveringSquareExamples

/-!
# Witnesses for the topology of `|E_A|`, `|E_B|` and Theorem 19.8.22 (HWZ 2021 §19.8, pp. 956–957)

Witnesses for 2021 Definition 19.8.20, Lemma 19.8.21 and Theorem 19.8.22, pp. 956–957, on the
square basic construction `absSqBasic` of `reflAbsSquare` (the reflection bundle pulled back
along the two-sheeted covering `absCovP`), whose member `absSquareU 0` has a non-injective
`Ξ : Ŵ → W` and a non-trivial `ℤ/2`-action on `W` (`absSquareU_nondegenerate`).

## What is formalized

* `absSqBasic_isCompatible`: the underlying covering basic construction of `absSqBasic` satisfies
  `IsCompatible` (transported from `absFt_isCompatible`).
* **`absSqBasic_hypotheses`**: all hypotheses of `lemma_19_8_21_hyp` and
  `theorem_19_8_22_topology_hyp` hold for `absSqBasic` (coherence, `IsCompatible`, class
  uniformizers, metrizable `T_{|B|}`), with the non-degenerate member `absSquareU 0 ∈ F̃(0)`.
* **`absSqBasic_lemma_19_8_21`** (Lemma 19.8.21 for `absSqBasic`), **`absSqBasic_theorem_19_8_22`**
  (the formalized parts of Theorem 19.8.22 for `absSqBasic`, at the member `absSquareU 0`).
* `absFt_metrizableSpace_natTopEB`: Theorem 19.8.6 (5) for `|E_B|` on `absFt` (`T̄_B` is
  metrizable and `|P_B|` is continuous).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

/-- **`IsCompatible` for `absSqBasic`** (the reading of the top target maps `t̂` used in
§19.7): transported from `absFt_isCompatible` along `absSqFt.toPullback = absFt`. -/
theorem absSqBasic_isCompatible :
    (absSqBasic.Ft.toPullback.toCBC absSqBasic.T.𝓕).IsCompatible := by
  have key : ∀ (F : PullbackUniformizerConstruction absCovP reflBan) (h : absFt = F),
      (F.toCBC (h ▸ absFtTransition : F.PullbackTransitionConstruction).𝓕).IsCompatible := by
    rintro _ rfl
    exact absFt_isCompatible
  exact key _ absSqFt_toPullback.symm

/-- The member `absSquareU 0` of `F̃(0)` for `absSqBasic`. -/
def absSqUnif₀ : absSqBasic.Ft.Unif := ⟨0, absSquareU 0, rfl⟩

/-- **The hypotheses of `lemma_19_8_21_hyp` and `theorem_19_8_22_topology_hyp` hold for
`absSqBasic`**, whose member `absSquareU 0 ∈ F̃(0)` has a non-injective `Ξ` and a non-trivial
`ℤ/2`-action on the fibres of `W`. -/
theorem absSqBasic_hypotheses :
    absSqBasic.Ft.toPullback.IsCoherent absSqBasic.T.𝓕 ∧
      (absSqBasic.Ft.toPullback.toCBC absSqBasic.T.𝓕).IsCompatible ∧
      (absSqBasic.Ft.toPullback.toCBC absSqBasic.T.𝓕).HasClassUniformizers ∧
      @MetrizableSpace _ ((absSqBasic.Ft.toPullback.toCBC absSqBasic.T.𝓕).toBasic.natTop
        absSqBasic.T.hasClassUniformizers.toBasic) ∧
      absSquareU 0 ∈ absSqBasic.Ft.F 0 ∧ ¬ Injective (absSquareU 0).K.Ξ ∧
      ∃ (g : (absSquareU 0).Ψh.Ψ.G) (w : (absSquareU 0).K.W), g • w ≠ w :=
  ⟨absSqBasic.T.isCoherent, absSqBasic_isCompatible, absSqBasic.T.hasClassUniformizers,
    absSqBasic.T.metrizable, rfl, absSquareU_nondegenerate⟩

/-- **2021 Lemma 19.8.21, p. 956, for `absSqBasic`**: `T̄_A` (Definition 19.8.20) is a
metrizable topology on `|E_A|` and `|P_A|` is continuous. -/
theorem absSqBasic_lemma_19_8_21 :
    (absSqBasic.Ft.NatOpenEA ∅ ∧ absSqBasic.Ft.NatOpenEA univ ∧
      (∀ W₁ W₂, absSqBasic.Ft.NatOpenEA W₁ → absSqBasic.Ft.NatOpenEA W₂ →
        absSqBasic.Ft.NatOpenEA (W₁ ∩ W₂)) ∧
      ∀ T : Set (Set reflAbsSquare.μA.cat.OrbitSpace), (∀ W ∈ T, absSqBasic.Ft.NatOpenEA W) →
        absSqBasic.Ft.NatOpenEA (⋃₀ T)) ∧
    @MetrizableSpace _ (absSqBasic.Ft.natTopEA absSqBasic.T.𝓕 absSqBasic.T.isCoherent
      absSqBasic_isCompatible absSqBasic.T.hasClassUniformizers) ∧
    Continuous[absSqBasic.Ft.natTopEA absSqBasic.T.𝓕 absSqBasic.T.isCoherent
      absSqBasic_isCompatible absSqBasic.T.hasClassUniformizers,
      (absSqBasic.Ft.toPullback.toCBC absSqBasic.T.𝓕).natTopA
        reflAbsSquare.isFiniteToOneCovering absSqBasic_isCompatible
        absSqBasic.T.hasClassUniformizers] reflAbsSquare.μA.orbitProj :=
  absSqBasic.Ft.lemma_19_8_21_hyp absSqBasic.T.𝓕 absSqBasic.T.isCoherent absSqBasic_isCompatible
    absSqBasic.T.hasClassUniformizers absSqBasic.T.metrizable

/-- **2021 Theorem 19.8.22, p. 956, for `absSqBasic` at the member `absSquareU 0`**: `|A|`,
`|E_B|`, `|E_A|` are metrizable, `p̂` over `p` is a proper strong bundle covering square, and the
source and target maps of `M(Γ̂, Γ̂)` are local strong bundle isomorphisms. -/
theorem absSqBasic_theorem_19_8_22 :
    @MetrizableSpace _ ((absSqBasic.Ft.toPullback.toCBC absSqBasic.T.𝓕).natTopA
      reflAbsSquare.isFiniteToOneCovering absSqBasic_isCompatible
      absSqBasic.T.hasClassUniformizers) ∧
    @MetrizableSpace _ (absSqBasic.Ft.toPullback.natTopEB absSqBasic.T.𝓕 absSqBasic.T.isCoherent
      absSqBasic.T.hasClassUniformizers) ∧
    @MetrizableSpace _ (absSqBasic.Ft.natTopEA absSqBasic.T.𝓕 absSqBasic.T.isCoherent
      absSqBasic_isCompatible absSqBasic.T.hasClassUniformizers) ∧
    IsProperStrongBundleCoveringSquare (absSqBasic.Ft.bundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.toPullback.bundleG absSqBasic.T.𝓕 absSqUnif₀.toPU absSqUnif₀.toPU)
      (absSqBasic.Ft.toPullback.pBmap absSqBasic.T.𝓕 absSqUnif₀.toPU absSqUnif₀.toPU)
      (absSqBasic.Ft.pbarSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀) ∧
    (∀ a, ∃ (U : Set (absSqBasic.Ft.toPullback.MHatB absSqBasic.T.𝓕 absSqUnif₀.toPU
        absSqUnif₀.toPU)) (U' : Set absSqUnif₀.toPU.x.Ψh.ObjE), a ∈ U ∧
      (absSqBasic.Ft.bundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀).IsStrongBundleIsoOn
        absSqUnif₀.x.K.BWh (absSqBasic.Ft.isStrongBundleMap_tgtSq absSqBasic.T.𝓕 absSqUnif₀
          absSqUnif₀ absSqBasic.T.isCoherent absSqBasic_isCompatible) U U') ∧
    ∀ k, ∃ (U : Set (absSqBasic.Ft.toPullback.MBase absSqBasic.T.𝓕 absSqUnif₀.toPU
        absSqUnif₀.toPU)) (U' : Set absSqUnif₀.toPU.x.Ψh.Ψ.O), k ∈ U ∧
      (absSqBasic.Ft.toPullback.bundleG absSqBasic.T.𝓕 absSqUnif₀.toPU
        absSqUnif₀.toPU).IsStrongBundleIsoOn absSqUnif₀.toPU.x.bun.bundle
        (absSqBasic.Ft.toPullback.isStrongBundleMap_tgtGmap absSqBasic.T.𝓕 absSqUnif₀.toPU
          absSqUnif₀.toPU absSqBasic.T.isCoherent) U U' := by
  obtain ⟨h1, h2, h3, h4⟩ := absSqBasic.Ft.theorem_19_8_22_topology_hyp absSqBasic.T.𝓕
    absSqBasic.T.isCoherent absSqBasic_isCompatible absSqBasic.T.hasClassUniformizers
    absSqBasic.T.metrizable
  obtain ⟨h5, -, h6, -, h7⟩ := h4 absSqUnif₀ absSqUnif₀
  exact ⟨h1, h2, h3, h5, h6, h7⟩

/-- **2021 Theorem 19.8.6 (5) for `|E_B|` on `absFt`**: `T̄_B` (Definition 19.6.7 for
`(F̄, 𝓕)`) is metrizable and `|P_B| : |E_B| → |B|` is continuous. -/
theorem absFt_metrizableSpace_natTopEB :
    @MetrizableSpace _ (absFt.natTopEB absFtTransition.𝓕 absFt_isCoherent
      absFtTransition.hasClassUniformizers) ∧
    Continuous[absFt.natTopEB absFtTransition.𝓕 absFt_isCoherent
      absFtTransition.hasClassUniformizers, (absFt.toCBC absFtTransition.𝓕).toBasic.natTop
      absFtTransition.hasClassUniformizers.toBasic] reflBan.orbitProj :=
  ⟨absFt.metrizableSpace_natTopEB absFtTransition.𝓕 absFt_isCoherent
    absFtTransition.hasClassUniformizers absFtTransition.metrizable,
    absFt.continuous_orbitProjB absFtTransition.𝓕 absFt_isCoherent
      absFtTransition.hasClassUniformizers⟩

end GroupoidalCategory

end Polyfold
