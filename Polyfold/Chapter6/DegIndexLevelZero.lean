import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter4.Submanifolds

/-!
# The degeneracy index on Euclidean space

The degeneracy index on `ℝⁿ` and on the whole space, and interior points of index zero. The
level-zero results are in `Chapter9/GeneralLevelZero.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Filter Topology Module
noncomputable section
namespace Polyfold
universe u
namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
section Chart
variable {φ : MChart X} (hφ : P.IsChart φ)
include hφ

/-- The chart sc⁺-retraction `t` of the proof of Theorem 4.18 (`exists_chartRetraction`), with
`t(U) = φ(W ∩ A)`. -/
theorem exists_plusRetraction {A : Set X} (d : P.SubmanifoldData A) {x : X} (hxA : x ∈ A)
    (hxV : x ∈ d.V) :
    ∃ t : ScRetraction φ.model.E φ.model.C,
      t.retract = φ '' (d.toSubData.shrink φ ∩ A) ∧ t.IsScPlus := by
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hφ (P.levelMk 1 x (d.mem_levelSet_one hxA hxV)) R hR
  exact ⟨t, ht, htp⟩

end Chart

/-- A point of a partial quadrant with degeneracy index `0` (Definition 1.23) is an interior
point. -/
theorem _root_.Polyfold.mem_interior_of_degIndex_eq_zero {E : ScBanach} {C : Set (E 0)}
    (hC : IsPartialQuadrant E C) {x : E 0} (hx : x ∈ C) (h0 : Polyfold.degIndex E C x = 0) :
    x ∈ interior C := by
  obtain ⟨n, W, T, hT⟩ := hC
  rw [Polyfold.degIndex_eq T hT hx, degIndexWith, quadrantDeg, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff] at h0
  have hxq : ∀ i, 0 ≤ (T 0 x).1 i := by rw [hT] at hx; exact hx
  rw [mem_interior]
  refine ⟨{y | ∀ i, 0 < (T 0 y).1 i}, fun y hy => ?_, ?_,
    fun i => lt_of_le_of_ne (hxq i) (Ne.symm (h0 (Finset.mem_univ i)))⟩
  · rw [hT]; exact fun i => (hy i).le
  · have : {y : E 0 | ∀ i, 0 < (T 0 y).1 i} = ⋂ i, {y | 0 < (T 0 y).1 i} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_fst.comp (T 0).continuous))

/-- The degeneracy index of every point of `E` in the partial quadrant `E` is `0`. -/
theorem _root_.Polyfold.degIndex_univ (E : ScBanach) (y : E 0) :
    Polyfold.degIndex E univ y = 0 := by
  let T : ScIso E ((ScBanach.const (Fin 0 → ℝ)).prod E) :=
    { lvl := fun m => (ContinuousLinearEquiv.uniqueProd ℝ (E m) (Fin 0 → ℝ)).symm
      incl_comm := fun m x => Prod.ext (funext fun i => i.elim0) rfl }
  have hT : (univ : Set (E 0)) = T 0 ⁻¹' quadrant 0 E 0 := by ext; simp [quadrant]
  rw [Polyfold.degIndex_eq T hT (mem_univ y), degIndexWith, quadrantDeg]
  simp

/-- **The condition `d_X = 0` can be met**: every point of `ℝᵐ` has degeneracy index `0`. -/
theorem degIndex_rn {m : ℕ} (x : Fin m → ℝ) : (rnPolyfold m).degIndex x = 0 :=
  Nat.le_zero.1 (((rnPolyfold m).degIndex_le (isChart_rnChart 0) (mem_univ x)).trans
    (le_of_eq (Polyfold.degIndex_univ _ _)))

end MPolyfold
end Polyfold
end
