import Polyfold.Chapter9.SheetEssential
import Polyfold.Chapter9.MathlibFormsBridge2021
import Polyfold.Chapter4.SubmanifoldNearInterior

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Definition 9.4.5, p. 431 (2017: Definition 9.13): measure zero in a tame sheet `Mᵢ`, a
smooth manifold with boundary with corners.

# The two readings of Definition 9.4.5 agree on tame sheets

Definition 9.4.5 asks that `ϕ(U ∩ K)` be a Lebesgue null set for the smooth charts
`ϕ : Mᵢ ⊇ U → [0, ∞)ᵏ × ℝⁿ⁻ᵏ` of `Mᵢ`.  For a tame sheet these charts exist in the project: the
corner charts of its induced structure (`cornerChartedSpace`, `Chapter9/MathlibManifoldBridge`),
with Mathlib's Lebesgue measure (`Polyfold.IsMeasureZero`).  For a general sheet the project reads
the definition in the M-polyfold charts of the ambient space, with the `n`-dimensional Hausdorff
measure of the level-`0` norm (`MPolyfold.IsHNull`, `Chapter9/SheetNull`).

## What is formalized

* `hNull_iff_volume_euclidean`: on `ℝⁿ` (Euclidean norm) the `n`-dimensional Hausdorff null sets
  are the Lebesgue null sets (both measures are Haar measures).
* `hNull_image_affine_iff`: affine isomorphisms preserve `d`-null sets.
* `MPolyfold.isHNull_iff_isMeasureZero_cornerChartedSpace`: on an M-polyfold `Q` with a corner
  structure of dimension `n` (a tame sheet with its induced structure), `Q.IsHNull n C` iff `C`
  has measure zero in the Mathlib manifold `Q` (Definition 9.4.5 in the corner charts).
* `MPolyfold.isHNull_iff_subPolyfold`: for a smooth submanifold `A` of an M-polyfold `X` and
  `C ⊆ A`, measure zero read in the charts of `X` is measure zero read in the charts of the
  induced structure of `A`.
* `MPolyfold.isHNull_iff_isMeasureZero_sheet` (**the comparison**): for an `n`-dimensional
  submanifold `A` with tame induced structure (a sheet of a tame branching structure, Definition
  9.3.6) and `C ⊆ A`: `P.IsHNull n C` iff `C` has Lebesgue measure zero in every smooth chart of
  the manifold with corners `A`, as Definition 9.4.5 is printed.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace Manifold WithLp
open scoped NNReal ENNReal

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-- **On `ℝⁿ` the `n`-dimensional Hausdorff null sets are the Lebesgue null sets** (both are Haar
measures, hence mutually absolutely continuous). -/
theorem hNull_iff_volume_euclidean {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n))) :
    HNull (n : ℝ) T ↔ volume T = 0 := by
  rw [hNull_iff]
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hH : (μH[(n : ℝ)] : Measure (EuclideanSpace ℝ (Fin n))).IsAddHaarMeasure := by
    have := isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℝ (Fin n))
    rwa [hfr] at this
  exact ⟨fun h => Measure.absolutelyContinuous_isAddHaarMeasure volume μH[(n : ℝ)] h,
    fun h => Measure.absolutelyContinuous_isAddHaarMeasure μH[(n : ℝ)] volume h⟩

/-- **Affine isomorphisms preserve `d`-null sets.** -/
theorem hNull_image_affine_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (b : F) {d : ℝ} (hd : 0 ≤ d)
    (S : Set E) : HNull d ((fun v => L v + b) '' S) ↔ HNull d S := by
  constructor
  · refine HNull.of_image_antilipschitzOn (K := ‖(L.symm : F →L[ℝ] E)‖₊) hd fun a _ a' _ => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub, coe_nnnorm]
    have h := (L.symm : F →L[ℝ] E).le_opNorm (L (a - a'))
    simpa using h
  · intro h
    refine h.image_lipschitzOn (K := ‖(L : E →L[ℝ] F)‖₊) hd
      (LipschitzWith.of_dist_le_mul fun a a' => ?_).lipschitzOnWith
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub, coe_nnnorm]
    exact (L : E →L[ℝ] F).le_opNorm _

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {n : ℕ}

/-- In corner coordinates `κ`, the extended Mathlib chart is an affine isomorphism of the
M-polyfold chart `χ`: null sets correspond. -/
theorem CornerCoords.hNull_chart_iff_volume (κ : CornerCoords P n) {D : Set X} (hD : D ⊆ κ.s) :
    HNull (n : ℝ) (κ.χ '' D) ↔ volume (κ.toQuadrantChart.extend (𝓠 n) '' D) = 0 := by
  set L : κ.χ.model.E 0 ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    κ.Ψ.trans (EuclideanSpace.equiv (Fin n) ℝ).symm with hL
  have himg : κ.toQuadrantChart.extend (𝓠 n) '' D =
      (fun v => L v + toLp 2 κ.c) '' (κ.χ '' D) := by
    rw [image_image]
    refine image_congr fun x hx => ?_
    rw [κ.extend_eq_toLp_coord (hD hx)]
    rfl
  rw [himg, ← hNull_iff_volume_euclidean, hNull_image_affine_iff L _ (Nat.cast_nonneg n)]

/-- **Definition 9.4.5 in the two readings, on an M-polyfold with a corner structure**: for `Q`
with a corner structure of dimension `n`, a set has `n`-dimensional measure zero in the
M-polyfold charts (`IsHNull`) iff it has Lebesgue measure zero in the smooth charts of the
manifold with corners `Q` (`IsMeasureZero`, charts of `cornerChartedSpace`). -/
theorem isHNull_iff_isMeasureZero_cornerChartedSpace (h : P.HasCornerStructureOfDim n)
    (C : Set X) :
    letI := P.cornerChartedSpace h
    P.IsHNull n C ↔ IsMeasureZero (𝓠 n) C := by
  let _ := P.cornerChartedSpace h
  have hman := P.isManifold_cornerChartedSpace h
  constructor
  · intro hC
    refine isMeasureZero_of_forall_mem fun z hz => ?_
    obtain ⟨κ, hzκ⟩ := h.exists_cornerCoords z
    refine ⟨κ.toQuadrantChart, IsManifold.subset_maximalAtlas ⟨κ, rfl⟩, hzκ, ?_⟩
    have hsub : κ.s ∩ C ⊆ κ.s := inter_subset_left
    change volume (κ.toQuadrantChart.extend (𝓠 n) '' (κ.s ∩ C)) = 0
    rw [← κ.hNull_chart_iff_volume hsub]
    have := κ.isCornerChart.finiteDimensional
    exact hC κ.χ κ.isChart _ inter_subset_right (inter_subset_left.trans κ.s_subset)
      (IsSeparable.of_separableSpace _)
  · intro hC
    refine isHNull_of_forall_exists_chart h.hasCornerStructure.isSmoothSubmanifold_univ
      (subset_univ C) fun z hz => ?_
    obtain ⟨κ, hzκ⟩ := h.exists_cornerCoords z
    refine ⟨κ.χ, κ.isChart, κ.s_subset hzκ, κ.s, κ.isOpen_s, hzκ, ?_⟩
    have hsub : C ∩ κ.s ∩ κ.χ.source ⊆ κ.s := fun w hw => hw.1.2
    rw [κ.hNull_chart_iff_volume hsub]
    refine measure_mono_null (image_mono fun w hw => ?_)
      (hC κ.toQuadrantChart (IsManifold.subset_maximalAtlas ⟨κ, rfl⟩))
    exact ⟨hw.1.2, hw.1.1⟩

/-- **Measure zero in the charts of `X` and in the charts of the induced structure of `A`**: for a
smooth finite-dimensional submanifold `A` and `C ⊆ A`, `C` has `n`-dimensional measure zero in
`X` iff its trace has `n`-dimensional measure zero in the sub-M-polyfold `A` (whose charts are
the restrictions `φ|_{W ∩ A}`; chart independence on both sides). -/
theorem isHNull_iff_subPolyfold {A C : Set X} (hA : P.IsSmoothSubmanifold A) (hC : C ⊆ A)
    [ParacompactSpace A] (n : ℕ) :
    P.IsHNull n C ↔ (subPolyfold hA.isSubMPolyfold).IsHNull n (Subtype.val ⁻¹' C) := by
  constructor
  · intro h
    refine isHNull_of_forall_exists_chart hA.isSmoothSubmanifold_univ_subPolyfold
      (subset_univ _) fun z hz => ?_
    obtain ⟨φ, hφ, hzφ⟩ := P.exists_isChart_mem_source z.1
    set d := (hA.data z.2).toSubData with hd
    have hzV := hA.mem_data_V z.2
    obtain ⟨δ, hδ, hsep⟩ := isSeparable_chart_ball hφ hA z.2 hzφ
    obtain ⟨V', hV', hVe⟩ := exists_isOpen_chartBall φ A z.1 δ
    have hzV' : z.1 ∈ V' := by
      have : z.1 ∈ chartBall φ A z.1 δ := ⟨⟨z.2, hzφ⟩, by rw [sub_self, norm_zero]; exact hδ⟩
      rw [hVe] at this
      exact this.2
    refine ⟨subChart d hφ z, subPolyfold_isChart hA.isSubMPolyfold d hφ z,
      d.mem_shrink φ z.2 hzV hzφ, Subtype.val ⁻¹' V', hV'.preimage continuous_subtype_val,
      hzV', ?_⟩
    set S : Set A := Subtype.val ⁻¹' C ∩ Subtype.val ⁻¹' V' ∩ (subChart d hφ z).source with hS
    have hDC : Subtype.val '' S ⊆ C := by
      rintro _ ⟨a, ha, rfl⟩; exact ha.1.1
    have hDφ : Subtype.val '' S ⊆ φ.source := by
      rintro _ ⟨a, ha, rfl⟩; exact d.shrink_subset_source φ ha.2
    have hDsep : IsSeparable (φ '' (Subtype.val '' S)) := by
      refine hsep.mono (image_mono ?_)
      rintro _ ⟨a, ha, rfl⟩
      rw [hVe]; exact ⟨a.2, ha.1.2⟩
    refine (h φ hφ _ hDC hDφ hDsep).mono ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a.1, ⟨a, ha, rfl⟩, rfl⟩
  · intro h
    refine isHNull_of_forall_exists_chart hA hC fun z hz => ?_
    have hzA := hC hz
    obtain ⟨φ, hφ, hzφ⟩ := P.exists_isChart_mem_source z
    set d := (hA.data hzA).toSubData with hd
    have hzV := hA.mem_data_V hzA
    obtain ⟨δ, hδ, hsep⟩ := isSeparable_chart_ball hφ hA hzA hzφ
    obtain ⟨V', hV', hVe⟩ := exists_isOpen_chartBall φ A z δ
    have hzV' : z ∈ V' := by
      have : z ∈ chartBall φ A z δ := ⟨⟨hzA, hzφ⟩, by rw [sub_self, norm_zero]; exact hδ⟩
      rw [hVe] at this
      exact this.2
    refine ⟨φ, hφ, hzφ, d.shrink φ ∩ V', (d.isOpen_shrink φ).inter hV',
      ⟨d.mem_shrink φ hzA hzV hzφ, hzV'⟩, ?_⟩
    set ψ := subChart d hφ ⟨z, hzA⟩ with hψ
    set S : Set A := {a | a.1 ∈ C ∧ a.1 ∈ d.shrink φ ∩ V'} with hS
    have hsepS : IsSeparable (ψ '' S) := by
      refine hsep.mono ?_
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.1, by rw [hVe]; exact ⟨a.2, ha.2.2⟩, rfl⟩
    have h1 := h ψ (subPolyfold_isChart hA.isSubMPolyfold d hφ _) S (fun a ha => ha.1)
      (fun a ha => ha.2.1) hsepS
    refine h1.mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hC hw.1.1⟩, ⟨hw.1.1, hw.1.2⟩, rfl⟩

/-- **Definition 9.4.5, 2021 p. 431, as printed, for a tame sheet**: let `A` be an
`n`-dimensional submanifold of an M-polyfold whose induced structure is tame (a sheet of a tame
branching structure, Definition 9.3.6), a smooth manifold with boundary with corners
(`cornerChartedSpace`).  A set `C ⊆ A` has `n`-dimensional measure zero in the M-polyfold charts
of the ambient space (`IsHNull`) iff `ϕ(U ∩ C)` is a Lebesgue null set for every smooth chart
`ϕ` of `A` (`IsMeasureZero`). -/
theorem isHNull_iff_isMeasureZero_sheet {A C : Set X} (hA : P.IsSubmanifoldOfDim A n)
    (ht : P.HasTameInducedStructure A) (hC : C ⊆ A) [ParacompactSpace A] :
    letI := (subPolyfold hA.1.isSubMPolyfold).cornerChartedSpace
      (hA.hasCornerStructureOfDim_of_hasTameInducedStructure ht)
    P.IsHNull n C ↔ IsMeasureZero (𝓠 n) (Subtype.val ⁻¹' C : Set A) :=
  (isHNull_iff_subPolyfold hA.1 hC n).trans
    (isHNull_iff_isMeasureZero_cornerChartedSpace _ _)

end MPolyfold

end Polyfold
