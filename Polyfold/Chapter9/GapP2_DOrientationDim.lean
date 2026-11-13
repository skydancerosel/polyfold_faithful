import Polyfold.Chapter9.GapP2_DSheetMeasure
import Polyfold.Chapter9.GeneralBoundaryPoints

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, **Lemma 9.3.4**, p. 423 (2017: Lemma 9.10, p. 311).

# Lemma 9.3.4 for an `n`-dimensional `Θ`, for arbitrary orientations

`lemma_9_3_4_general` (`Chapter9/GeneralBoundaryPoints.lean`) compares two `n`-dimensional
orientations (`IsOrientationOfDim`: the local representations (9.9) can be taken with
`n`-dimensional sheets).  For an `n`-dimensional `Θ` every orientation is of this kind, since
every local branching structure of `Θ` has `n`-dimensional sheets
(`LocalBranchingStructure.isOfDim_of_isNDimensional`).

* `IsOrientation.isOrientationOfDim`: an orientation of an `n`-dimensional `Θ` is an
  `n`-dimensional orientation.
* `lemma_9_3_4_of_isNDimensional`: **Lemma 9.3.4** for an `n`-dimensional branched
  ep⁺-subgroupoid: two orientations (Definition 9.3.2) which agree at the good points are the
  same.  Without sheets of one dimension the lemma does not hold as we read it
  (`lemma_9_3_4_mixed_dim`).
-/

universe u

namespace Polyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- **Every orientation of an `n`-dimensional `Θ` is `n`-dimensional**: the sheets of the oriented
local branching structures of Definition 9.3.2 have dimension `n`. -/
theorem IsOrientation.isOrientationOfDim {n : ℕ} (hn : X.IsNDimensional Θ n)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (h : X.IsOrientation Θ T) :
    X.IsOrientationOfDim Θ n T :=
  ⟨h, fun x hx => by
    obtain ⟨B, hB⟩ := h.locallyOriented x hx
    exact ⟨B, fun i => (B.isSubmanifoldOfDim i).eq_of_hasDimAt
      ((B.toLocalBranchingStructure.isOfDim_of_isNDimensional hn i).2 x (B.mem_M i)), hB⟩⟩

/-- **Lemma 9.3.4, 2021 p. 423 (2017: Lemma 9.10, p. 311)**, for an `n`-dimensional branched
ep⁺-subgroupoid `Θ` of an arbitrary ep-groupoid: two orientations `T̂¹`, `T̂²` of `Θ`
(Definition 9.3.2) which agree at the good points agree at every smooth point.  The text does not
say that `Θ` has one dimension; without it the lemma does not hold as we read it
(`lemma_9_3_4_mixed_dim`). -/
theorem lemma_9_3_4_of_isNDimensional (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    (hn : X.IsNDimensional Θ n) {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ}
    (h₁ : X.IsOrientation Θ T₁) (h₂ : X.IsOrientation Θ T₂)
    (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) : ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  lemma_9_3_4_general hΘ (h₁.isOrientationOfDim hn) (h₂.isOrientationOfDim hn) hagree

end EpGroupoid

end Polyfold
