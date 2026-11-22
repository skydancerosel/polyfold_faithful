import Polyfold.Chapter17.ProperCoveringModel
import Polyfold.Chapter19.CoveringOrbitCounterexample

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", with **Definition 17.8.4** (p. 831): the covering functor
`absP : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ` of `CoveringOrbitCounterexample.lean` is a connected proper
covering model.

# `absP` is a proper covering model

## What is formalized

* `absP_eq_sheetFunctor`: `absP` is Chapter 17's sheet functor `sheetFunctor` for `S = ℤˣ`.
* **`absP_properCoveringModel`**: `absP` is a proper ep-groupoid covering model (Definition 17.8.4)
  with distinguished point `ō = 0`, sheets `U(i, 0) = {i} × ℝ` (`absP_properCoveringModel_U`).
* `absP_properCoveringModel_connected`: the model is connected (`ℝ` is connected);
  `absP_properCoveringModel_fiber`: `τ̂⁻¹(0) = ℤˣ × {0}`, two points.
* `absP_isProperCovering_of_model`: Remark 17.8.5 recovers `absP_isProperCovering`.

## Readings

* None beyond those of `Polyfold/Chapter17/ProperCoveringModel.lean`.
-/

open Set

noncomputable section

namespace Polyfold

namespace Chapter19

open EpGroupoid EpGroupoid.Examples

/-- `absP` is the sheet functor `G ⋉ (S × O) → G ⋉ O` of Chapter 17 for `G = S = ℤˣ`, `O = ℝ`. -/
theorem absP_eq_sheetFunctor : absP = sheetFunctor isScSmoothMap_units_smul ℤˣ := rfl

/-- **`absP : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ` is a proper covering model** (Definition 17.8.4) with
distinguished point `ō = 0`. -/
def absP_properCoveringModel : ProperCoveringModel (hP := isScSmoothMap_units_smul) absP :=
  sheetModel isScSmoothMap_units_smul ℤˣ 0 units_smul_zero_rn

theorem absP_properCoveringModel_pt : absP_properCoveringModel.pt = 0 := rfl

theorem absP_properCoveringModel_U (y : ℤˣ × (Fin 1 → ℝ)) :
    absP_properCoveringModel.U y = {y.1} ×ˢ univ := rfl

/-- The model `absP` is connected. -/
theorem absP_properCoveringModel_connected : absP_properCoveringModel.Connected :=
  (inferInstance : ConnectedSpace (Fin 1 → ℝ))

/-- `τ̂⁻¹(0) = ℤˣ × {0}`, two points. -/
theorem absP_properCoveringModel_fiber :
    absP_properCoveringModel.fiber = univ ×ˢ {0} ∧ absP_properCoveringModel.fiber.ncard = 2 :=
  ⟨sheetModel_fiber isScSmoothMap_units_smul ℤˣ 0 units_smul_zero_rn,
    sheetModel_units_nontrivial.1⟩

/-- Remark 17.8.5 recovers that `absP` is a proper covering functor (Definition 8.5.1). -/
theorem absP_isProperCovering_of_model : absP.IsProperCovering :=
  absP_properCoveringModel.isProperCovering (by
    rw [absP_properCoveringModel_fiber.1]
    exact finite_univ.prod (finite_singleton _))

end Chapter19

end Polyfold
