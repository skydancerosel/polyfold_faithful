import Polyfold.Chapter9.SheetNullBridge
import Polyfold.Chapter9.SheetMeasure
import Polyfold.Chapter9.BoundaryStratumDense

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.5, Definition 9.5.14, p. 448 (2017: Definition 9.17, p. 327), with Definition 9.4.5, p. 431.

# The boundary of a tame sheet is not an `(n-1)`-dimensional null set

For the σ-algebra `L(∂S)` the text uses the sets of `(n-1)`-dimensional measure zero in the
boundaries `∂Mᵢ` of the sheets of a tame branching structure of dimension `n`.  The project reads
"`(n-1)`-dimensional measure zero" in the M-polyfold charts of the ambient space, with the
`(n-1)`-dimensional Hausdorff measure of the level-`0` norm (`MPolyfold.IsHNull (n-1)`,
`Chapter9/SheetNull`).  A null-set system needs that a nonempty `∂M` is not null.

## What is formalized

* `not_hNull_of_lipschitzOn_ball`: a set with a Lipschitz image in `ℝᵐ` containing a ball is not
  `m`-null.
* `MPolyfold.CornerCoords.not_hNull_chart_coord_eq_zero`: in corner coordinates `κ` of dimension
  `m + 1`, near a point whose only vanishing coordinate is the `i`-th, the chart image of
  `{κᵢ = 0}` is not `m`-null (it is an open piece of a coordinate hyperplane).
* `MPolyfold.HasCornerStructureOfDim.not_isHNull_boundary`: for `Q` with a corner structure of
  dimension `n`, a nonempty `∂Q = {d_Q ≥ 1}` is not `(n-1)`-null.
* `MPolyfold.not_isHNull_submanifoldBoundary` (**the statement for the sheets**): for an
  `n`-dimensional submanifold `M` of an M-polyfold with tame induced structure, a nonempty `∂M`
  is not `(n-1)`-null.  No hypothesis on `n` (for `n = 0` the boundary is empty).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace
open scoped NNReal ENNReal

noncomputable section

namespace Polyfold

universe u

/-- **A set over a ball of `ℝᵐ` is not `m`-null**: if a map `f`, Lipschitz on `S`, has
`f(S) ⊇ B(c, ρ)` in `ℝᵐ`, then the `m`-dimensional Hausdorff measure of `S` is not `0`. -/
theorem not_hNull_of_lipschitzOn_ball {E : Type*} [EMetricSpace E] {m : ℕ}
    {f : E → Fin m → ℝ} {K : ℝ≥0} {S : Set E} (hf : LipschitzOnWith K f S) {c : Fin m → ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) (h : ball c ρ ⊆ f '' S) : ¬ HNull (m : ℝ) S := by
  intro hS
  have h1 := hNull_iff.1 ((hS.image_lipschitzOn (Nat.cast_nonneg m) hf).mono h)
  have e : (μH[(m : ℝ)] : Measure (Fin m → ℝ)) = volume := by
    have := hausdorffMeasure_pi_real (ι := Fin m)
    rwa [Fintype.card_fin] at this
  rw [e] at h1
  exact (isOpen_ball.measure_pos volume (nonempty_ball.2 hρ)).ne' h1

namespace MPolyfold

section Corner

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}

/-- The points near `a` whose coordinates other than the `i`-th are positive form an open set. -/
theorem isOpen_setOf_forall_ne_pos {m : ℕ} (i : Fin m) :
    IsOpen {v : Fin m → ℝ | ∀ l, l ≠ i → 0 < v l} := by
  have : {v : Fin m → ℝ | ∀ l, l ≠ i → 0 < v l} = ⋂ l, {v | l ≠ i → 0 < v l} := by
    ext v; simp
  rw [this]
  refine isOpen_iInter_of_finite fun l => ?_
  by_cases hl : l = i
  · simp [hl]
  · simpa [hl] using isOpen_lt continuous_const (continuous_apply l)

/-- The coordinates other than the `i`-th of a chart value, as a map `E₀ → ℝᵐ`. -/
def CornerCoords.dropCoord {m : ℕ} (κ : CornerCoords Q (m + 1)) (i : Fin (m + 1))
    (e : κ.χ.model.E 0) : Fin m → ℝ := fun j => (κ.Ψ e + κ.c) (i.succAbove j)

theorem CornerCoords.dropCoord_apply {m : ℕ} (κ : CornerCoords Q (m + 1)) (i : Fin (m + 1))
    (z : Z) (j : Fin m) : κ.dropCoord i (κ.χ z) j = κ.coord z (i.succAbove j) := rfl

theorem CornerCoords.lipschitzWith_dropCoord {m : ℕ} (κ : CornerCoords Q (m + 1))
    (i : Fin (m + 1)) :
    LipschitzWith ‖(κ.Ψ : κ.χ.model.E 0 →L[ℝ] (Fin (m + 1) → ℝ))‖₊ (κ.dropCoord i) := by
  refine LipschitzWith.of_dist_le_mul fun e e' => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro j
  have h1 : dist (κ.dropCoord i e j) (κ.dropCoord i e' j) = |κ.Ψ (e - e') (i.succAbove j)| := by
    simp only [dropCoord, Pi.add_apply, Real.dist_eq, map_sub, Pi.sub_apply]
    congr 1; ring
  rw [h1, dist_eq_norm, coe_nnnorm]
  exact (abs_apply_le_norm_pi _ _).trans
    ((κ.Ψ : κ.χ.model.E 0 →L[ℝ] (Fin (m + 1) → ℝ)).le_opNorm _)

/-- **An open piece of a coordinate hyperplane is not `m`-null** (Definition 9.5.14, 2021
p. 448): in corner coordinates `κ` of dimension `m + 1`, if `y` has `κᵢ(y) = 0` and all other
coordinates positive, the chart image of `{z | κᵢ(z) = 0}` is not an `m`-dimensional null set. -/
theorem CornerCoords.not_hNull_chart_coord_eq_zero {m : ℕ} (κ : CornerCoords Q (m + 1))
    {y : Z} (hy : y ∈ κ.s) {i : Fin (m + 1)} (hi : κ.coord y i = 0)
    (hl : ∀ l ≠ i, 0 < κ.coord y l) :
    ¬ HNull (m : ℝ) (κ.χ '' {z | z ∈ κ.s ∧ κ.coord z i = 0}) := by
  have hU : IsOpen (κ.W ∩ {v : Fin (m + 1) → ℝ | ∀ l, l ≠ i → 0 < v l}) :=
    κ.isOpen_W.inter (isOpen_setOf_forall_ne_pos i)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU (κ.coord y) ⟨κ.coord_mem_W hy, hl⟩
  refine not_hNull_of_lipschitzOn_ball (κ.lipschitzWith_dropCoord i).lipschitzOnWith
    (c := fun j => κ.coord y (i.succAbove j)) hr fun u hu => ?_
  set v : Fin (m + 1) → ℝ := i.insertNth (0 : ℝ) u with hv
  have hvi : v i = 0 := by rw [hv, Fin.insertNth_apply_same]
  have hvj : ∀ j, v (i.succAbove j) = u j := fun j => by
    rw [hv, Fin.insertNth_apply_succAbove]
  have hvb : v ∈ ball (κ.coord y) r := by
    rw [mem_ball, dist_pi_lt_iff hr]
    intro l
    rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
    · rw [hvi, hi, dist_self]; exact hr
    · rw [hvj]; exact (dist_pi_lt_iff hr).1 (mem_ball.1 hu) j
  obtain ⟨hvW, hvpos⟩ := hball hvb
  have hv0 : ∀ l, 0 ≤ v l := fun l => by
    by_cases h : l = i
    · rw [h, hvi]
    · exact (hvpos l h).le
  obtain ⟨z, hz, hzv⟩ := κ.exists_coord_eq hvW hv0
  refine ⟨κ.χ z, ⟨z, ⟨hz, by rw [hzv, hvi]⟩, rfl⟩, funext fun j => ?_⟩
  rw [κ.dropCoord_apply, hzv, hvj]

/-- **The boundary of a manifold with corners is not `(n-1)`-null** (Definition 9.5.14, 2021
p. 448): for `Q` with a corner structure of dimension `n`, if `∂Q = {d_Q ≥ 1}` is nonempty, it
does not have `(n-1)`-dimensional measure zero. -/
theorem HasCornerStructureOfDim.not_isHNull_boundary {n : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) {x : Z} (hx : 1 ≤ Q.degIndex x) :
    ¬ Q.IsHNull (n - 1) {z | 1 ≤ Q.degIndex z} := by
  obtain ⟨κ, hxκ⟩ := hcs.exists_cornerCoords x
  have hpos : 0 < (Finset.univ.filter fun j => κ.coord x j = 0).card := by
    rw [← κ.degIndex_eq_card hxκ]; exact hx
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  obtain ⟨y, -, hys, hyi, hyl⟩ :=
    κ.exists_coord_one_zero isOpen_univ (mem_univ x) hxκ (Finset.mem_filter.1 hi).2
  cases n with
  | zero => exact i.elim0
  | succ m =>
    intro h
    have := κ.isCornerChart.finiteDimensional
    refine κ.not_hNull_chart_coord_eq_zero hys hyi hyl
      (h κ.χ κ.isChart _ (fun z hz => ?_) (fun z hz => κ.s_subset hz.1)
        (IsSeparable.of_separableSpace _))
    change 1 ≤ Q.degIndex z
    rw [κ.degIndex_eq_card hz.1]
    exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz.2⟩⟩

end Corner

section Sheet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The trace of `∂M` on the sub-M-polyfold `M` is `{d_M ≥ 1}`. -/
theorem preimage_submanifoldBoundary {M : Set X} (hM : P.IsSmoothSubmanifold M) :
    letI := P.paracompactSpace_subtype M
    (Subtype.val ⁻¹' P.submanifoldBoundary M : Set M) =
      {a | 1 ≤ (subPolyfold hM.isSubMPolyfold).degIndex a} := by
  ext a
  exact mem_submanifoldBoundary_iff_subDegIndex hM a.2

theorem submanifoldBoundary_subset (M : Set X) : P.submanifoldBoundary M ⊆ M :=
  fun _ ⟨_, hy, _⟩ => hy

/-- **Definition 9.5.14, 2021 p. 448 (2017: Definition 9.17) — the boundary of a tame sheet is
not a null set**: for an `n`-dimensional submanifold `M` of an M-polyfold with tame induced
structure (a sheet of a tame branching structure, Definition 9.3.6), a nonempty boundary
`∂M = {d_M ≥ 1}` does not have `(n-1)`-dimensional measure zero (Definition 9.4.5 in dimension
`n - 1`, read in the M-polyfold charts).  So the `(n-1)`-dimensional null sets form a null-set
system on the boundaries of the sheets. -/
theorem not_isHNull_submanifoldBoundary {M : Set X} {n : ℕ} (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (hne : (P.submanifoldBoundary M).Nonempty) :
    ¬ P.IsHNull (n - 1) (P.submanifoldBoundary M) := by
  have := P.paracompactSpace_subtype M
  have hcs := hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  obtain ⟨y, hy⟩ := hne
  have hyM : y ∈ M := submanifoldBoundary_subset M hy
  intro h
  have h1 := (isHNull_iff_subPolyfold hM.1 (submanifoldBoundary_subset M) (n - 1)).1 h
  rw [preimage_submanifoldBoundary hM.1] at h1
  exact hcs.not_isHNull_boundary (x := ⟨y, hyM⟩)
    ((mem_submanifoldBoundary_iff_subDegIndex hM.1 hyM).1 hy) h1

end Sheet

end MPolyfold

end Polyfold
