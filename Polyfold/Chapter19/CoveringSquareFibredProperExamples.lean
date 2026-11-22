import Polyfold.Chapter19.CoveringSquareFibredProper
import Polyfold.Chapter19.CoveringSquareTopologyExamples
import Polyfold.Chapter19.CoveringPolyfoldExamples

/-!
# Witness for the fibred-product square of Theorem 19.8.22 (HWZ 2021 §19.8, pp. 955–957)

2021 Theorem 19.8.22 (pp. 956–957) for the square basic construction `absSqBasic` of
`reflAbsSquare` (Definition 19.8.15), at its member `absSquareU 0`: `Ξ : Ŵ → W` is two-to-one and
`ℤ/2` acts non-trivially on `W` (`absSquareU_nondegenerate`), and `IsCompatible` holds
(`absSqBasic_isCompatible`).

## What is formalized

* `absSqUnif₀_fiber_ncard`: the fibre of `τ̂` over the centre has two points.
* **`absSqBasic_theorem_19_8_22_fibredProper`**: `SquareBasicConstruction.theorem_19_8_22_hyp`
  applies to `absSqBasic`; the fibred-product square `p̂ ₛ×ₜ p̂` over `p ₛ×ₜ p` at `absSquareU 0` is
  a proper strong bundle covering square whose base map has a fibre with two points (over the pair
  of units at the centre), so it is not a trivial (one-sheeted) covering.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

/-- The fibre `τ̂⁻¹(o₀)` of the proper covering model of `absSquareU 0` over its centre has two
points (the two sheets `{±1} × ℝ`). -/
theorem absSqUnif₀_fiber_ncard : absSqUnif₀.x.Ψh.model.fiber.ncard = 2 := by
  have h := absBasic_covering_polyfold_nondegenerate.2.2.2.2.2.2.1
  change (absCU 0).model.fiber.ncard = 2 at h
  change (absPU 0).Ψh.model.fiber.ncard = 2
  rw [absPU_Ψh]
  exact h

/-- The pair of units `(1_{o₀}, 1_{o₀}) ∈ M(Ψ, Ψ) ₛ×ₜ M(Ψ, Ψ)` at the centre `o₀` of
`absSquareU 0`. -/
def absSqUnitPair : absSqBasic.Ft.toPullback.BFP absSqBasic.T.𝓕 absSqUnif₀.toPU absSqUnif₀.toPU
    absSqUnif₀.toPU :=
  ⟨(absSqBasic.Ft.toPullback.unitB absSqBasic.T.𝓕 absSqUnif₀.toPU absSqUnif₀.x.Ψh.model.pt,
    absSqBasic.Ft.toPullback.unitB absSqBasic.T.𝓕 absSqUnif₀.toPU absSqUnif₀.x.Ψh.model.pt), rfl⟩

/-- **2021 Theorem 19.8.22, pp. 956–957, the multiplication square for `absSqBasic`**: the
theorem applies (`SquareBasicConstruction.theorem_19_8_22_hyp` with `absSqBasic_isCompatible`); at
the member `absSquareU 0` (non-injective `Ξ`, non-trivial `ℤ/2`-action) the square
`p̂ ₛ×ₜ p̂ : M(Γ̂, Γ̂) ₛ×ₜ M(Γ̂, Γ̂) → M(Γ, Γ) ₛ×ₜ M(Γ, Γ)` over `p ₛ×ₜ p` is a proper strong
bundle covering square, and the fibre of `p ₛ×ₜ p` over the pair of units at the centre has two
points. -/
theorem absSqBasic_theorem_19_8_22_fibredProper :
    IsProperStrongBundleCoveringSquare
      (absSqBasic.Ft.mulBundleSq absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀
        absSqBasic_isCompatible)
      (absSqBasic.Ft.toPullback.mulBundleG absSqBasic.T.𝓕 absSqUnif₀.toPU absSqUnif₀.toPU
        absSqUnif₀.toPU)
      (absSqBasic.Ft.pFP absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀)
      (absSqBasic.Ft.pbarFP absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀) ∧
    (absSqBasic.Ft.pFP absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀ ⁻¹' {absSqUnitPair}).ncard
      = 2 ∧
    ¬ Injective (absSquareU 0).K.Ξ ∧
    ∃ (g : (absSquareU 0).Ψh.Ψ.G) (w : (absSquareU 0).K.W), g • w ≠ w :=
  ⟨((absSqBasic.theorem_19_8_22_hyp absSqBasic_isCompatible).2.2.2 absSqUnif₀ absSqUnif₀
      absSqUnif₀).2.2.2.2,
    (absSqBasic.Ft.ncard_pFP_fiber absSqBasic.T.𝓕 absSqUnif₀ absSqUnif₀ absSqUnif₀
      absSqUnitPair).trans absSqUnif₀_fiber_ncard,
    absSquareU_nondegenerate⟩

end GroupoidalCategory

end Polyfold
