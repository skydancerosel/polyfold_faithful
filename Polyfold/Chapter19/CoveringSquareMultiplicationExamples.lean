import Polyfold.Chapter19.CoveringSquareMultiplication
import Polyfold.Chapter19.CoveringSquareTopologyExamples

/-!
# Witnesses for the structure maps of Theorem 19.8.22 (HWZ 2021 §19.8, pp. 955–957)

Witnesses for the inversion, unit and multiplication parts of 2021 Theorem 19.8.22
(pp. 956–957; diagrams (19.98)–(19.100), p. 955) on the square basic construction `absSqBasic`
of `reflAbsSquare`, at its member `absSquareU 0`, which has a non-injective `Ξ : Ŵ → W` and a
non-trivial `ℤ/2`-action on `W` (`absSquareU_nondegenerate`). The hypotheses `IsCoherent` and
`IsCompatible` of `theorem_19_8_22_inv_hyp` and `isStrongBundleMap_mul_and_faces` hold there
(`absSqBasic_hypotheses`).

## What is formalized

* **`absSqBasic_theorem_19_8_22_structure`**: for `absSqBasic` at `absSquareU 0`, the inversion of
  `M(Γ̂, Γ̂)` is a strong bundle isomorphism covering `ι̂`, the unit `Ŵ → M(Γ̂, Γ̂)` and the
  multiplication `M(Γ̂, Γ̂) ₛ×ₜ M(Γ̂, Γ̂) → M(Γ̂, Γ̂)` are strong bundle maps covering `û` and `m̂`,
  and the multiplication is the composition on the fibred product.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

/-- **2021 Theorem 19.8.22, pp. 956–957, the structure maps, for `absSqBasic` at the member
`absSquareU 0`** (non-injective `Ξ`, non-trivial `ℤ/2`-action): the inversion
`ι : M(Γ̂, Γ̂) → M(Γ̂, Γ̂)` is a strong bundle isomorphism covering `ι̂`, the unit
`u : Ŵ → M(Γ̂, Γ̂)` is a strong bundle map covering `û`, the multiplication on
`M(Γ̂, Γ̂) ₛ×ₜ M(Γ̂, Γ̂)` is a strong bundle map covering `m̂`, and it is the composition
`(h', h) ↦ h' ∘ h`. -/
theorem absSqBasic_theorem_19_8_22_structure :
    (absSqBasic.Ft.bundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀).IsStrongBundleIso
      (absSqBasic.Ft.bundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.invH absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.invSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.invH absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.invSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀) ∧
    absSqUnif₀.x.K.BWh.IsStrongBundleMap
      (absSqBasic.Ft.bundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.unitH absSqBasic.T.𝓕 absSqUnif₀)
      (absSqBasic.Ft.unitSq absSqBasic.T.𝓕 absSqUnif₀) ∧
    (absSqBasic.Ft.mulBundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀
      absSqBasic_isCompatible).IsStrongBundleMap
      (absSqBasic.Ft.bundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.mulH absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.mulSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀) ∧
    (∀ q, absSqBasic.Ft.mulSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀
      (absSqBasic.Ft.toFPSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀ q) =
        (TransitionSet.comp q.1.1.toTrans q.1.2.toTrans
          (TransitionSet.mor_composable_of_src_eq_tgt q.2) :
          absSqBasic.Ft.MSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀)) ∧
    ¬ Injective (absSquareU 0).K.Ξ ∧
    ∃ (g : (absSquareU 0).Ψh.Ψ.G) (w : (absSquareU 0).K.W), g • w ≠ w :=
  ⟨absSqBasic.Ft.isStrongBundleIso_invSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀
      absSqBasic.T.isCoherent absSqBasic_isCompatible,
    absSqBasic.Ft.isStrongBundleMap_unitSq absSqBasic.T.𝓕 absSqUnif₀,
    absSqBasic.Ft.isStrongBundleMap_mulSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀
      absSqBasic_isCompatible,
    absSqBasic.Ft.mulSq_toFPSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀,
    absSquareU_nondegenerate⟩

end GroupoidalCategory

end Polyfold
