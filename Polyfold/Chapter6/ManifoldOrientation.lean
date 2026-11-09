import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Orientations of finite-dimensional manifolds with corners in Mathlib's language, for the natural
orientation of the solution set in Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*
(Springer 2021), **Theorem 6.6.18** (p. 275; preprint Theorem 6.41) (gap G.67).  Mathlib has no
orientations of manifolds; this file supplies the two usual forms, for any model with corners
`I : ModelWithCorners ℝ E H` with `E` finite-dimensional and any charted space `M` on `H`.

# Oriented atlases and continuous tangent orientations

## The notions

* `chartChangeDeriv I e e' x`: the derivative at `x` of the chart change `e' ∘ e⁻¹`, read in `E`
  (`fderivWithin` within `range I`, unique there; for the charts `chartAt` it is Mathlib's
  `tangentCoordChange`, `tangentCoordChange_eq_chartChangeDeriv`).  For charts of the maximal
  atlas: `chartChangeDeriv_self`, the chain rule `chartChangeDeriv_comp`, invertibility
  (`det_chartChangeDeriv_ne_zero`) and continuity (`continuousOn_chartChangeDeriv`,
  `eventually_det_chartChangeDeriv_pos_iff`: the sign of the determinant is locally constant).
* `signMap A o`: the action of an invertible endomorphism `A` of `E` on the orientations of `E`
  (`o` if `det A > 0`, `-o` if `det A < 0`); it is `Orientation.map` (`map_eq_signMap`).
* **Oriented atlas** (`IsOrientedAtlas I n A`): a family `A` of charts of the maximal `C^n` atlas
  covering `M` whose chart changes have `det D(e' ∘ e⁻¹) > 0` at every point of the overlaps.  This
  is the form in which top-degree forms are integrated.
* **Continuous tangent orientation** (`TangentOrientation I M k`,
  `TangentOrientation.IsContinuous`): an orientation `o x` of every tangent space
  `TangentSpace I x` (Mathlib's `T_xM = E`, read in the chart `chartAt H x`), such that its
  reading `orientationIn e y (o y)` in every chart `e` of the maximal atlas is locally constant
  on `e.source`.
* From an atlas to the tangent orientation: `IsOrientedAtlas.tangentOrientation hA ρ` (`ρ` an
  orientation of `E`): the orientation of `T_xM` read as `ρ` in the charts of `A`
  (`orientationIn_tangentOrientation`); it is continuous (`isContinuous_tangentOrientation`).
* Back: for a continuous tangent orientation `o`, the charts in which `o` reads as `ρ` everywhere
  (`positiveCharts`) have positive chart changes (`det_pos_of_mem_positiveCharts`); if they cover
  `M` they are an oriented atlas inducing `o` (`isOrientedAtlas_positiveCharts`,
  `tangentOrientation_positiveCharts`).
* Continuity is local: `TangentOrientation.isContinuous_of_forall` (locally constant in one chart
  at every point suffices).
* `derivIn I e h x`: the tangent map of `h : M → F` at `x` read in the chart `e`, with the chain
  rule `derivIn_comp_chartChangeDeriv`; it identifies `T_xM` with its image when `M` sits in `F`.

## Remarks on the choices

* The model space `E` has no preferred orientation in general, so an oriented atlas induces a
  tangent orientation only together with an orientation `ρ` of `E` (for `ℝⁿ` the standard one).
* The two forms are not equivalent for every model.  With the quadrant model `[0,∞)ⁿ` and
  `n = 1`, the interval `[0, 1]` has no oriented atlas at all (a chart at `0` is increasing, a
  chart at `1` decreasing), although its tangent spaces carry the two continuous orientations; and
  for `n = 0` every atlas is oriented (the `0 × 0` determinant is `1`) while a tangent orientation
  is a sign at every point.  The tangent orientation is therefore the primary notion here; the
  positive charts cover `M` as soon as the model has an orientation-reversing chart change near
  every point (for the quadrant `[0,∞)ⁿ`, `n ≥ 2`: a transposition of two coordinates).
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### The derivative of a chart change -/

section ChartChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The derivative of the chart change** `e' ∘ e⁻¹` at `x`, read in `E`: the derivative within
`range I` of `I ∘ e' ∘ e⁻¹ ∘ I⁻¹` at `I(e(x))`. -/
def chartChangeDeriv (e e' : OpenPartialHomeomorph M H) (x : M) : E →L[ℝ] E :=
  fderivWithin ℝ (I.extendCoordChange e e') (range I) (e.extend I x)

/-- For the charts of the atlas, `chartChangeDeriv` is Mathlib's `tangentCoordChange`. -/
theorem tangentCoordChange_eq_chartChangeDeriv [IsManifold I 1 M] (x y z : M) :
    tangentCoordChange I x y z = chartChangeDeriv I (chartAt H x) (chartAt H y) z := rfl

variable {I}

omit [ChartedSpace H M] in
/-- `D(e ∘ e⁻¹) = id` on `e.source`. -/
theorem chartChangeDeriv_self {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    chartChangeDeriv I e e x = ContinuousLinearMap.id ℝ E := by
  unfold chartChangeDeriv
  rw [Filter.EventuallyEq.fderivWithin_eq (f := id), fderivWithin_id]
  · exact I.uniqueDiffWithinAt_image
  · filter_upwards [e.extend_target_mem_nhdsWithin hx] with y hy
    exact (e.extend I).right_inv hy
  · simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      e.extend_left_inv hx, id]

variable {n : WithTop ℕ∞} {e e' e'' : OpenPartialHomeomorph M H} {x : M}

/-- The chart change is differentiable within `range I`, with derivative `chartChangeDeriv`. -/
theorem hasFDerivWithinAt_chartChangeDeriv (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    HasFDerivWithinAt (I.extendCoordChange e e') (chartChangeDeriv I e e' x) (range I)
      (e.extend I x) :=
  ((I.contDiffWithinAt_extendCoordChange' he he' hx hx').differentiableWithinAt
    hn).hasFDerivWithinAt

/-- **The chain rule for chart changes**: `D(e'' ∘ e'⁻¹) ∘ D(e' ∘ e⁻¹) = D(e'' ∘ e⁻¹)` at a point
of the three domains. -/
theorem chartChangeDeriv_comp_apply (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (he'' : e'' ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hx'' : x ∈ e''.source) (v : E) :
    chartChangeDeriv I e' e'' x (chartChangeDeriv I e e' x v) = chartChangeDeriv I e e'' x v := by
  unfold chartChangeDeriv
  rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
  · have := e.extend_preimage_mem_nhds (I := I) hx (e'.extend_source_mem_nhds (I := I) hx')
    filter_upwards [nhdsWithin_le_nhds this] with y hy
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [(e'.extend I).left_inv hy]
  · simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx, e'.extend_left_inv hx']
  · exact (I.contDiffWithinAt_extendCoordChange' he' he'' hx' hx'').differentiableWithinAt hn
  · exact (I.contDiffWithinAt_extendCoordChange' he he' hx hx').differentiableWithinAt hn
  · intro y _; exact mem_range_self _
  · exact I.uniqueDiffWithinAt_image
  · simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx]

/-- The chain rule, as an equality of linear maps. -/
theorem chartChangeDeriv_comp (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (he'' : e'' ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (hx'' : x ∈ e''.source) :
    (chartChangeDeriv I e' e'' x).comp (chartChangeDeriv I e e' x) = chartChangeDeriv I e e'' x :=
  ContinuousLinearMap.ext (chartChangeDeriv_comp_apply hn he he' he'' hx hx' hx'')

/-- `D(e ∘ e'⁻¹) ∘ D(e' ∘ e⁻¹) = id`. -/
theorem chartChangeDeriv_comp_self (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (chartChangeDeriv I e' e x).comp (chartChangeDeriv I e e' x) = ContinuousLinearMap.id ℝ E := by
  rw [chartChangeDeriv_comp hn he he' he hx hx' hx, chartChangeDeriv_self hx]

/-- `det D(e ∘ e'⁻¹) · det D(e' ∘ e⁻¹) = 1`. -/
theorem det_chartChangeDeriv_mul (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (chartChangeDeriv I e' e x).det * (chartChangeDeriv I e e' x).det = 1 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ← LinearMap.det_comp,
    ← ContinuousLinearMap.toLinearMap_comp, chartChangeDeriv_comp_self hn he he' hx hx',
    ContinuousLinearMap.coe_id, LinearMap.det_id]

/-- **The chart changes are invertible**: `det D(e' ∘ e⁻¹) ≠ 0`. -/
theorem det_chartChangeDeriv_ne_zero [FiniteDimensional ℝ E] (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) : (chartChangeDeriv I e e' x).det ≠ 0 :=
  right_ne_zero_of_mul_eq_one (det_chartChangeDeriv_mul hn he he' hx hx')

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **The derivative of a chart change is continuous** on the overlap (for a `C¹` atlas). -/
theorem continuousOn_chartChangeDeriv (hn : 1 ≤ n) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) :
    ContinuousOn (chartChangeDeriv I e e') (e.source ∩ e'.source) := by
  have hsub : (I.extendCoordChange e e').source ⊆ range I := by
    rw [I.extendCoordChange_source]; exact image_subset_range _ _
  have h1 : ContinuousOn (fderivWithin ℝ (I.extendCoordChange e e') (range I))
      (I.extendCoordChange e e').source := by
    intro p hp
    refine ((ContDiffWithinAt.fderivWithin_right (m := 0) ?_ I.uniqueDiffOn (by simpa using hn)
      (hsub hp)).mono hsub).continuousWithinAt
    exact (I.contDiffOn_extendCoordChange he he' p hp).mono_of_mem_nhdsWithin
      (I.extendCoordChange_source_mem_nhdsWithin hp)
  refine h1.comp (e.continuousOn_extend.mono ?_) ?_
  · rw [e.extend_source]; exact inter_subset_left
  · exact mapsTo_iff_image_subset.2 (e.extend_image_source_inter e' (I := I)).subset

/-- **The sign of `det D(e' ∘ e⁻¹)` is locally constant** on the overlap. -/
theorem eventually_det_chartChangeDeriv_pos_iff (hn : 1 ≤ n)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ y ∈ e'.source ∧
      (0 < (chartChangeDeriv I e e' y).det ↔ 0 < (chartChangeDeriv I e e' x).det) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hnhds : e.source ∩ e'.source ∈ 𝓝 x :=
    inter_mem (e.open_source.mem_nhds hx) (e'.open_source.mem_nhds hx')
  have hc : ContinuousAt (fun y => (chartChangeDeriv I e e' y).det) x :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_chartChangeDeriv hn he he')).continuousAt hnhds
  have hne := det_chartChangeDeriv_ne_zero hn0 he he' hx hx'
  rcases hne.lt_or_gt with hneg | hpos
  · filter_upwards [hnhds, hc.eventually (gt_mem_nhds hneg)] with y hy hy'
    exact ⟨hy.1, hy.2, iff_of_false (not_lt.2 hy'.le) (not_lt.2 hneg.le)⟩
  · filter_upwards [hnhds, hc.eventually (lt_mem_nhds hpos)] with y hy hy'
    exact ⟨hy.1, hy.2, iff_of_true hy' hpos⟩

/-! ### The derivative of a map read in a chart -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (I) in
/-- **The tangent map of `h : M → F` at `x`, read in the chart `e`**: the derivative within
`range I` of `h ∘ (e.extend I)⁻¹` at `e.extend I x` (Mathlib's `mfderiv` in the chart `e`). -/
def derivIn (e : OpenPartialHomeomorph M H) (h : M → F) (x : M) : E →L[ℝ] F :=
  fderivWithin ℝ (h ∘ (e.extend I).symm) (range I) (e.extend I x)

omit [FiniteDimensional ℝ E] in
/-- **The chain rule for the tangent map read in two charts**:
`T_e h(x) = T_{e'} h(x) ∘ D(e' ∘ e⁻¹)(x)`, if `h` is differentiable in the chart `e'`. -/
theorem derivIn_comp_chartChangeDeriv (hn : n ≠ 0) (he : e ∈ IsManifold.maximalAtlas I n M)
    (he' : e' ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    {h : M → F}
    (hd : DifferentiableWithinAt ℝ (h ∘ (e'.extend I).symm) (range I) (e'.extend I x)) :
    (derivIn I e' h x).comp (chartChangeDeriv I e e' x) = derivIn I e h x := by
  have hfx : I.extendCoordChange e e' (e.extend I x) = e'.extend I x := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx]
  have hmaps : MapsTo (I.extendCoordChange e e') (range I) (range I) := fun y _ => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  unfold derivIn chartChangeDeriv
  rw [← hfx] at hd ⊢
  rw [← fderivWithin_comp _ hd
    ((I.contDiffWithinAt_extendCoordChange' he he' hx hx').differentiableWithinAt hn) hmaps
    I.uniqueDiffWithinAt_image]
  refine Filter.EventuallyEq.fderivWithin_eq ?_ ?_
  · have := e.extend_preimage_mem_nhds (I := I) hx (e'.extend_source_mem_nhds (I := I) hx')
    filter_upwards [nhdsWithin_le_nhds this] with y hy
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [(e'.extend I).left_inv hy]
  · simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hx, e'.extend_left_inv hx']

end ChartChange

/-! ### Orientations moved by an invertible endomorphism -/

section SignMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {ι : Type*}

/-- **The action of an endomorphism `A` on the orientations of `E`**: `A_* o = o` if
`det A > 0` and `-o` otherwise (for invertible `A` this is `Orientation.map`, `map_eq_signMap`). -/
def signMap (A : E →L[ℝ] E) (o : Orientation ℝ E ι) : Orientation ℝ E ι :=
  if 0 < A.det then o else -o

theorem signMap_of_pos {A : E →L[ℝ] E} (h : 0 < A.det) (o : Orientation ℝ E ι) :
    signMap A o = o :=
  if_pos h

theorem signMap_of_neg {A : E →L[ℝ] E} (h : A.det < 0) (o : Orientation ℝ E ι) :
    signMap A o = -o :=
  if_neg (not_lt.2 h.le)

theorem signMap_id (o : Orientation ℝ E ι) : signMap (ContinuousLinearMap.id ℝ E) o = o :=
  signMap_of_pos (by simp [ContinuousLinearMap.det]) o

theorem signMap_neg (A : E →L[ℝ] E) (o : Orientation ℝ E ι) : signMap A (-o) = -signMap A o := by
  unfold signMap; split_ifs <;> rfl

/-- `B_* (A_* o) = (B A)_* o` for invertible `A`, `B`. -/
theorem signMap_signMap {A B : E →L[ℝ] E} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (o : Orientation ℝ E ι) : signMap B (signMap A o) = signMap (B.comp A) o := by
  have hdet : (B.comp A).det = B.det * A.det := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  rcases hA.lt_or_gt with hA' | hA' <;> rcases hB.lt_or_gt with hB' | hB'
  · rw [signMap_of_neg hA', signMap_neg, signMap_of_neg hB', neg_neg o,
      signMap_of_pos (by rw [hdet]; exact mul_pos_of_neg_of_neg hB' hA')]
  · rw [signMap_of_neg hA', signMap_neg, signMap_of_pos hB',
      signMap_of_neg (by rw [hdet]; exact mul_neg_of_pos_of_neg hB' hA')]
  · rw [signMap_of_pos hA', signMap_of_neg hB',
      signMap_of_neg (by rw [hdet]; exact mul_neg_of_neg_of_pos hB' hA')]
  · rw [signMap_of_pos hA', signMap_of_pos hB',
      signMap_of_pos (by rw [hdet]; exact mul_pos hB' hA')]

/-- `signMap` depends only on the sign of the determinant. -/
theorem signMap_congr {A B : E →L[ℝ] E} (h : 0 < A.det ↔ 0 < B.det) (o : Orientation ℝ E ι) :
    signMap A o = signMap B o := by
  unfold signMap
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.1 h1) h2
  · exact absurd (h.2 h2) h1
  · rfl

/-- `signMap A` is injective. -/
theorem signMap_injective {A : E →L[ℝ] E} : Function.Injective (signMap (ι := ι) A) := by
  intro o o' h
  unfold signMap at h
  split_ifs at h
  · exact h
  · exact neg_injective h

/-- An orientation is not moved to its opposite by a map with positive determinant, and vice
versa: `A_* o = o` iff `det A > 0` (`Module.Ray.ne_neg_self`). -/
theorem signMap_eq_self_iff {A : E →L[ℝ] E} (o : Orientation ℝ E ι) :
    signMap A o = o ↔ 0 < A.det := by
  unfold signMap
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (Module.Ray.ne_neg_self o).symm h

variable [FiniteDimensional ℝ E] [Fintype ι]

/-- **`signMap` is `Orientation.map`**: for a linear automorphism `f` of `E` with underlying map
`A` (and `ι` of cardinality `dim E`), `f_* o = signMap A o`. -/
theorem map_eq_signMap (f : E ≃ₗ[ℝ] E) {A : E →L[ℝ] E} (hfA : ∀ v, f v = A v)
    (h : Fintype.card ι = finrank ℝ E) (o : Orientation ℝ E ι) :
    Orientation.map ι f o = signMap A o := by
  have hdet : LinearMap.det (f : E →ₗ[ℝ] E) = A.det := by
    rw [ContinuousLinearMap.det]
    congr 1
    exact LinearMap.ext hfA
  unfold signMap
  split_ifs with hpos
  · exact (o.map_eq_iff_det_pos f h).2 (hdet ▸ hpos)
  · have hne : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0 :=
      (LinearEquiv.isUnit_det' f).ne_zero
    exact (o.map_eq_neg_iff_det_neg f h).2 (lt_of_le_of_ne (not_lt.1 (hdet ▸ hpos)) hne)

end SignMap

/-! ### Tangent orientations and oriented atlases -/

section Orientations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ)

/-- **A pointwise orientation of the tangent spaces** of `M`: an orientation of every
`TangentSpace I x` (Mathlib's `T_xM = E`, the tangent vectors read in the chart `chartAt H x`),
with `k` vectors (`k = dim E` for it to be one of two). -/
abbrev TangentOrientation : Type _ := (x : M) → Orientation ℝ (TangentSpace I x) (Fin k)

variable {I M k}

/-- `T_xM = E` (Mathlib's identification by definition): an orientation of `T_xM` as one of `E`,
the tangent vectors being read in the chart `chartAt H x`. -/
def tangentOrToModel {x : M} (o : Orientation ℝ (TangentSpace I x) (Fin k)) :
    Orientation ℝ E (Fin k) := o

/-- The inverse of `tangentOrToModel`. -/
def modelOrToTangent (x : M) (o : Orientation ℝ E (Fin k)) :
    Orientation ℝ (TangentSpace I x) (Fin k) := o

@[simp] theorem tangentOrToModel_modelOrToTangent (x : M) (o : Orientation ℝ E (Fin k)) :
    tangentOrToModel (modelOrToTangent (I := I) x o) = o := rfl

theorem tangentOrToModel_injective (x : M) :
    Function.Injective (tangentOrToModel (I := I) (x := x) (k := k)) := fun _ _ h => h

/-- **An orientation of `T_xM` read in a chart `e` at `x`**: its image under the derivative of the
chart change from `chartAt H x` to `e`. -/
def orientationIn (e : OpenPartialHomeomorph M H) (x : M)
    (o : Orientation ℝ (TangentSpace I x) (Fin k)) : Orientation ℝ E (Fin k) :=
  signMap (chartChangeDeriv I (chartAt H x) e x) (tangentOrToModel o)

variable (I) in
/-- **A continuous tangent orientation**: in every chart `e` of the maximal `C^n` atlas, the
orientations `o y` read in `e` are locally constant on `e.source`. -/
def TangentOrientation.IsContinuous (n : WithTop ℕ∞) (o : TangentOrientation I M k) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas I n M, ∀ x ∈ e.source,
    ∀ᶠ y in 𝓝 x, orientationIn e y (o y) = orientationIn e x (o x)

variable (I) in
/-- **An oriented atlas**: a family `A` of charts of the maximal `C^n` atlas, covering `M`, whose
chart changes have positive Jacobian determinant `det D(I ∘ e' ∘ e⁻¹ ∘ I⁻¹) > 0` (the derivative
within `range I`) at every point of every overlap. -/
structure IsOrientedAtlas (n : WithTop ℕ∞) (A : Set (OpenPartialHomeomorph M H)) : Prop where
  subset_maximalAtlas : A ⊆ IsManifold.maximalAtlas I n M
  covers : ∀ x : M, ∃ e ∈ A, x ∈ e.source
  det_pos : ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source, 0 < (chartChangeDeriv I e e' x).det

/-- In the chart at `x`, `o` reads as itself. -/
theorem orientationIn_chartAt (x : M) (o : Orientation ℝ (TangentSpace I x) (Fin k)) :
    orientationIn (chartAt H x) x o = tangentOrToModel o := by
  unfold orientationIn
  rw [chartChangeDeriv_self (mem_chart_source H x)]
  exact signMap_id _

namespace IsOrientedAtlas

variable {n : WithTop ℕ∞} {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A)

/-- A chart of the oriented atlas at `x`. -/
def chartOf (x : M) : OpenPartialHomeomorph M H := (hA.covers x).choose

theorem chartOf_mem (x : M) : hA.chartOf x ∈ A := (hA.covers x).choose_spec.1

theorem mem_chartOf_source (x : M) : x ∈ (hA.chartOf x).source := (hA.covers x).choose_spec.2

/-- **The tangent orientation of an oriented atlas** `A`, for an orientation `ρ` of the model
space `E`: the orientation of `T_xM` which reads as `ρ` in the charts of `A`
(`orientationIn_tangentOrientation`). -/
def tangentOrientation (ρ : Orientation ℝ E (Fin k)) : TangentOrientation I M k :=
  fun x => modelOrToTangent x (signMap (chartChangeDeriv I (hA.chartOf x) (chartAt H x) x) ρ)

end IsOrientedAtlas

variable [FiniteDimensional ℝ E] {n : WithTop ℕ∞} [IsManifold I n M]

/-- **Reading in two charts**: the reading of `o` in `e'` is the image of its reading in `e` under
`D(e' ∘ e⁻¹)`. -/
theorem orientationIn_chartChange (hn : n ≠ 0) {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) (o : Orientation ℝ (TangentSpace I x) (Fin k)) :
    orientationIn e' x o = signMap (chartChangeDeriv I e e' x) (orientationIn e x o) := by
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := n) x
  have hxc := mem_chart_source H x
  unfold orientationIn
  rw [signMap_signMap (det_chartChangeDeriv_ne_zero hn hc he hxc hx)
    (det_chartChangeDeriv_ne_zero hn he he' hx hx'), chartChangeDeriv_comp hn hc he he' hxc hx hx']

namespace IsOrientedAtlas

variable {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A)

include hA in
/-- The orientation `ρ` moved from a chart `e` of `A` to any chart `e'` at `x`. -/
theorem tangentOrientation_eq (hn : n ≠ 0) (ρ : Orientation ℝ E (Fin k))
    {e : OpenPartialHomeomorph M H} (he : e ∈ A) {x : M} (hx : x ∈ e.source) :
    tangentOrToModel (hA.tangentOrientation ρ x) =
      signMap (chartChangeDeriv I e (chartAt H x) x) ρ := by
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := n) x
  have hxc := mem_chart_source H x
  have h₀ := hA.subset_maximalAtlas (hA.chartOf_mem x)
  have he' := hA.subset_maximalAtlas he
  have hx₀ := hA.mem_chartOf_source x
  unfold tangentOrientation
  rw [tangentOrToModel_modelOrToTangent, ← chartChangeDeriv_comp hn h₀ he' hc hx₀ hx hxc,
    ← signMap_signMap (det_chartChangeDeriv_ne_zero hn h₀ he' hx₀ hx)
      (det_chartChangeDeriv_ne_zero hn he' hc hx hxc),
    signMap_of_pos (hA.det_pos _ (hA.chartOf_mem x) e he x ⟨hx₀, hx⟩)]

/-- **In every chart of the oriented atlas, the tangent orientation reads as `ρ`.** -/
theorem orientationIn_tangentOrientation (hn : n ≠ 0) (ρ : Orientation ℝ E (Fin k))
    {e : OpenPartialHomeomorph M H} (he : e ∈ A) {x : M} (hx : x ∈ e.source) :
    orientationIn e x (hA.tangentOrientation ρ x) = ρ := by
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := n) x
  have hxc := mem_chart_source H x
  have he' := hA.subset_maximalAtlas he
  unfold orientationIn
  rw [hA.tangentOrientation_eq hn ρ he hx,
    signMap_signMap (det_chartChangeDeriv_ne_zero hn he' hc hx hxc)
      (det_chartChangeDeriv_ne_zero hn hc he' hxc hx),
    chartChangeDeriv_comp_self hn he' hc hx hxc, signMap_id]

/-- **An oriented atlas induces a continuous tangent orientation**: in a chart `e` of the maximal
atlas, near `x`, the tangent orientation reads as `D(e ∘ e₀⁻¹)_* ρ` for a chart `e₀` of `A` at
`x`, whose sign is locally constant (`eventually_det_chartChangeDeriv_pos_iff`). -/
theorem isContinuous_tangentOrientation (hn : 1 ≤ n) (ρ : Orientation ℝ E (Fin k)) :
    (hA.tangentOrientation ρ).IsContinuous I n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  intro e he x hx
  set e₀ := hA.chartOf x
  have h₀ := hA.subset_maximalAtlas (hA.chartOf_mem x)
  have hx₀ := hA.mem_chartOf_source x
  have key : ∀ y ∈ e₀.source, y ∈ e.source →
      orientationIn e y (hA.tangentOrientation ρ y) = signMap (chartChangeDeriv I e₀ e y) ρ := by
    intro y hy₀ hy
    have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := n) y
    have hyc := mem_chart_source H y
    unfold orientationIn
    rw [hA.tangentOrientation_eq hn0 ρ (hA.chartOf_mem x) hy₀,
      signMap_signMap (det_chartChangeDeriv_ne_zero hn0 h₀ hc hy₀ hyc)
        (det_chartChangeDeriv_ne_zero hn0 hc he hyc hy),
      chartChangeDeriv_comp hn0 h₀ hc he hy₀ hyc hy]
  filter_upwards [eventually_det_chartChangeDeriv_pos_iff hn h₀ he hx₀ hx] with y hy
  rw [key y hy.1 hy.2.1, key x hx₀ hx]
  exact signMap_congr hy.2.2 ρ

end IsOrientedAtlas

/-- **Continuity is local in the charts**: a tangent orientation which, near every point `x`,
reads locally constant in one chart `e₀` of the maximal atlas at `x` is continuous (the readings
in another chart differ by the sign of `det D(e ∘ e₀⁻¹)`, which is locally constant). -/
theorem TangentOrientation.isContinuous_of_forall (hn : 1 ≤ n) {o : TangentOrientation I M k}
    (h : ∀ x : M, ∃ e₀ ∈ IsManifold.maximalAtlas I n M, x ∈ e₀.source ∧
      ∀ᶠ y in 𝓝 x, orientationIn e₀ y (o y) = orientationIn e₀ x (o x)) :
    o.IsContinuous I n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  intro e he x hx
  obtain ⟨e₀, he₀, hx₀, hev⟩ := h x
  filter_upwards [hev, eventually_det_chartChangeDeriv_pos_iff hn he₀ he hx₀ hx] with y hy hy'
  rw [orientationIn_chartChange hn0 he₀ he hy'.1 hy'.2.1,
    orientationIn_chartChange hn0 he₀ he hx₀ hx, hy]
  exact signMap_congr hy'.2.2 _

/-! ### From a continuous tangent orientation to an oriented atlas -/

variable (I n) in
/-- **The positive charts** of a tangent orientation `o` for an orientation `ρ` of `E`: the
charts of the maximal atlas in which `o` reads as `ρ` at every point. -/
def positiveCharts (o : TangentOrientation I M k) (ρ : Orientation ℝ E (Fin k)) :
    Set (OpenPartialHomeomorph M H) :=
  {e | e ∈ IsManifold.maximalAtlas I n M ∧ ∀ x ∈ e.source, orientationIn e x (o x) = ρ}

/-- **The chart changes between positive charts have positive determinant.** -/
theorem det_pos_of_mem_positiveCharts (hn : n ≠ 0) {o : TangentOrientation I M k}
    {ρ : Orientation ℝ E (Fin k)} {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ positiveCharts I n o ρ) (he' : e' ∈ positiveCharts I n o ρ) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) : 0 < (chartChangeDeriv I e e' x).det := by
  have h := orientationIn_chartChange hn he.1 he'.1 hx hx' (o x)
  rw [he.2 x hx, he'.2 x hx'] at h
  exact (signMap_eq_self_iff ρ).1 h.symm

/-- **The positive charts form an oriented atlas** as soon as they cover `M`. -/
theorem isOrientedAtlas_positiveCharts (hn : n ≠ 0) {o : TangentOrientation I M k}
    {ρ : Orientation ℝ E (Fin k)} (hcov : ∀ x : M, ∃ e ∈ positiveCharts I n o ρ, x ∈ e.source) :
    IsOrientedAtlas I n (positiveCharts I n o ρ) where
  subset_maximalAtlas _ he := he.1
  covers := hcov
  det_pos _ he _ he' _ hx := det_pos_of_mem_positiveCharts hn he he' hx.1 hx.2

/-- **The oriented atlas of positive charts induces `o` back.** -/
theorem tangentOrientation_positiveCharts (hn : n ≠ 0) {o : TangentOrientation I M k}
    {ρ : Orientation ℝ E (Fin k)} (hcov : ∀ x : M, ∃ e ∈ positiveCharts I n o ρ, x ∈ e.source) :
    (isOrientedAtlas_positiveCharts hn hcov).tangentOrientation ρ = o := by
  funext x
  set hA := isOrientedAtlas_positiveCharts hn hcov
  have he := hA.chartOf_mem x
  have hx := hA.mem_chartOf_source x
  have h1 := hA.orientationIn_tangentOrientation hn ρ he hx
  have h2 := he.2 x hx
  exact tangentOrToModel_injective x (signMap_injective (h1.trans h2.symm))

end Orientations

end Polyfold
