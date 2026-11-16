import Polyfold.Chapter3.ParamPerturbation

/-!
# Sc-smooth maps preserve smooth points

An sc-smooth map sends smooth points to smooth points. The sc-homotopies are in
`Chapter6/ScHomotopy.lean`.
-/

open Set Filter Topology Function
open scoped ContDiff
noncomputable section
namespace Polyfold
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **The values of an sc-smooth map `ℝⁿ → X` are smooth points.** -/
theorem mem_smoothSet_of_isScSmoothMap {n : ℕ} {γ : (Fin n → ℝ) → X}
    (hγ : (rnPolyfold n).IsScSmoothMap PX γ) (p : Fin n → ℝ) : γ p ∈ PX.smoothSet :=
  mem_iInter.2 fun m => hγ.mapsTo_levelSet m (by rw [rnPolyfold_levelSet]; exact mem_univ p)

end Polyfold
end
