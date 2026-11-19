import Polyfold.Chapter2.LevelPolyfold

/-!
# Density of smooth points

The predicate `DenseSmooth`: the smooth points of an M-polyfold are dense. Its use in the Zhou
argument is in `Chapter7/Zhou.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Function Topology Filter
noncomputable section
namespace Polyfold
universe u
namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The Part I fact that `X_∞` is dense in every `X_m` (2021 p. 289; point G.73), as a hypothesis. -/
def DenseSmooth : Prop := ∀ m, Dense {y : P.Level m | P.levelVal m y ∈ P.smoothSet}

variable {P}

/-- `X_∞` is dense in `X`. -/
theorem DenseSmooth.dense (h : P.DenseSmooth) : Dense P.smoothSet := by
  refine dense_iff_inter_open.2 fun W hW ⟨w, hw⟩ => ?_
  have hw0 : w ∈ P.levelSet 0 := by rw [levelSet_zero]; exact mem_univ w
  obtain ⟨y, hyW, hy⟩ := dense_iff_inter_open.1 (h 0) _ (hW.preimage (continuous_levelVal 0))
    ⟨P.levelMk 0 w hw0, hw⟩
  exact ⟨_, hyW, hy⟩

end MPolyfold
end Polyfold
end
