import Polyfold.Chapter9.GapP2_E3_GraphChart
import Polyfold.Chapter9.GapP2_E3_ChartVec
import Polyfold.Chapter9.GapP2_DSheetNullBridge
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# Coordinates of a graph chart

For a graph chart `c` of a submanifold `N` (`MPolyfold.GraphChart`): the coordinate
`c.coord = p ∘ φ : N → ℝⁿ`, a homeomorphism onto the measurable set `c.dom` with inverse `c.q`;
the frame `c.tvec y` of `T_yN` (the tangent vectors with chart vectors `L_y e₁, …, L_y eₙ`); the
restriction of `c` to an open piece `N ∩ V`; the sets of `n`-dimensional measure zero in `N`
(Definition 9.4.5, `MPolyfold.IsHNull`) are those with Lebesgue null coordinate image; the
coordinate image of a measurable subset of `N` is Lebesgue measurable.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped NNReal symmDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

namespace GraphChart

variable {n : ℕ} {N : Set X} (c : P.GraphChart n N)

/-- The coordinate `p ∘ φ` of the graph chart. -/
def coord (y : X) : EuclideanSpace ℝ (Fin n) := c.p (c.φ y)

/-- The coordinate image `p(φ(N)) ⊆ ℝⁿ`. -/
def dom : Set (EuclideanSpace ℝ (Fin n)) := c.coord '' N

theorem measurableSet_dom' : MeasurableSet c.dom := c.measurableSet_dom

theorem q_coord' {y : X} (hy : y ∈ N) : c.q (c.coord y) = y := c.q_coord y hy

theorem injOn_coord : InjOn c.coord N := fun y hy y' hy' h => by
  rw [← c.q_coord' hy, ← c.q_coord' hy', h]

theorem q_mem {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ c.dom) : c.q u ∈ N := by
  obtain ⟨y, hy, rfl⟩ := hu
  rw [c.q_coord' hy]; exact hy

theorem coord_q {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ c.dom) : c.coord (c.q u) = u := by
  obtain ⟨y, hy, rfl⟩ := hu
  rw [c.q_coord' hy]

theorem coord_mem_dom {y : X} (hy : y ∈ N) : c.coord y ∈ c.dom := mem_image_of_mem _ hy

theorem image_q_coord_image {A : Set X} (hA : A ⊆ N) : c.q '' (c.coord '' A) = A := by
  rw [image_image]
  exact (image_congr fun y hy => c.q_coord' (hA hy)).trans (image_id' A)

theorem continuousOn_coord : ContinuousOn c.coord N :=
  c.p.continuous.comp_continuousOn (c.φ.continuousOn_toFun.mono c.subset_source)

theorem continuousOn_q : ContinuousOn c.q c.dom := by
  rintro _ ⟨y, hy, rfl⟩
  have h1 : ContinuousWithinAt (fun u => c.φ (c.q u)) c.dom (c.coord y) :=
    (c.hasFDerivWithinAt y hy).continuousWithinAt
  have hO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y (c.subset_source hy)
  have h2 : ContinuousWithinAt c.φ.symm c.φ.model.O (c.φ (c.q (c.coord y))) := by
    rw [c.q_coord' hy]; exact c.φ.continuousOn_invFun (c.φ y) hO
  have h3 : ContinuousWithinAt (c.φ.symm ∘ fun u => c.φ (c.q u)) c.dom (c.coord y) :=
    ContinuousWithinAt.comp (g := c.φ.symm) (f := fun u => c.φ (c.q u)) h2 h1
      fun u hu => c.φ.mapsTo_model _ (c.subset_source (c.q_mem hu))
  refine h3.congr (fun u hu => ?_) ?_
  · exact (c.φ.symm_apply_apply (c.subset_source (c.q_mem hu))).symm
  · exact (c.φ.symm_apply_apply (c.subset_source (c.q_mem (c.coord_mem_dom hy)))).symm

/-- The standard basis vector `eᵢ` of `ℝⁿ`. -/
abbrev bvec (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)

theorem sum_smul_bvec (v : EuclideanSpace ℝ (Fin n)) : ∑ i, v i • bvec i = v := by
  ext k
  simp [bvec, Finset.sum_apply, Pi.single_apply]

open Classical in
/-- **The frame of `T_yN` of the graph chart**: the tangent vector over `y` whose chart vector is
`L_y eᵢ`. -/
def tvec (y : X) (i : Fin n) : P.TangentSpace :=
  haveI := nonempty_tangentSpace P y
  Classical.epsilon fun α => P.levelVal 1 (P.tangentProj α) = y ∧
    chartVec c.isChart α = c.L y (bvec i)

theorem tvec_spec {y : X} (hy : y ∈ N) (i : Fin n) :
    c.tvec y i ∈ P.submanifoldTangent N y ∧ chartVec c.isChart (c.tvec y i) = c.L y (bvec i) := by
  have hmem : c.L y (bvec i) ∈ P.chartTangent c.isChart N y := by
    rw [← c.range_L y hy]; exact mem_range_self _
  obtain ⟨α, hα, hαv⟩ := hmem
  have hex : ∃ α, P.levelVal 1 (P.tangentProj α) = y ∧
      chartVec c.isChart α = c.L y (bvec i) := ⟨α, hα.1, hαv⟩
  have := nonempty_tangentSpace P y
  have hs := Classical.epsilon_spec hex
  have heq : c.tvec y i = α :=
    chartVec_injOn c.isChart (c.subset_source hy) hs.1 hα.1 (hs.2.trans hαv.symm)
  rw [heq]
  exact ⟨hα, hαv⟩

theorem tvec_mem {y : X} (hy : y ∈ N) (i : Fin n) : c.tvec y i ∈ P.submanifoldTangent N y :=
  (c.tvec_spec hy i).1

theorem chartVec_tvec {y : X} (hy : y ∈ N) (i : Fin n) :
    chartVec c.isChart (c.tvec y i) = c.L y (bvec i) := (c.tvec_spec hy i).2

theorem L_injective {y : X} (hy : y ∈ N) : Injective (c.L y) :=
  LeftInverse.injective (g := c.p) (c.p_L y hy)

theorem L_apply {y : X} (hy : y ∈ N) (v : EuclideanSpace ℝ (Fin n)) :
    c.L y v = ∑ i, v i • chartVec c.isChart (c.tvec y i) := by
  conv_lhs => rw [← sum_smul_bvec v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, c.chartVec_tvec hy]

theorem linearIndependent_chartVec_tvec {y : X} (hy : y ∈ N) :
    LinearIndependent ℝ fun i => chartVec c.isChart (c.tvec y i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : c.L y (∑ i, g i • bvec i) = 0 := by
    rw [map_sum, ← hg]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, c.chartVec_tvec hy]
  have h2 := c.L_injective hy (h1.trans (map_zero _).symm)
  have h3 := congrFun (congrArg (fun v : EuclideanSpace ℝ (Fin n) => (v : Fin n → ℝ)) h2) i
  simpa [bvec, Finset.sum_apply, Pi.single_apply] using h3

/-- A vector of the chart image of `T_yN` is `L_y` of its projection. -/
theorem L_p_of_mem {y : X} (hy : y ∈ N) {w : c.φ.model.E 0}
    (hw : w ∈ P.chartTangent c.isChart N y) : c.L y (c.p w) = w := by
  rw [← c.range_L y hy] at hw
  obtain ⟨v, rfl⟩ := hw
  rw [c.p_L y hy]

/-- **The restriction of a graph chart to an open piece `N ∩ V`.** -/
def restrict {V : Set X} (hV : IsOpen V) : P.GraphChart n (N ∩ V) where
  φ := c.φ
  isChart := c.isChart
  subset_source := inter_subset_left.trans c.subset_source
  p := c.p
  q := c.q
  q_coord y hy := c.q_coord y hy.1
  L := c.L
  measurableSet_dom := by
    have hrel : ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧
        c.q ⁻¹' V ∩ c.dom = O ∩ c.dom := by
      obtain ⟨O, hO, hOe⟩ := (continuousOn_iff'.1 c.continuousOn_q) V hV
      exact ⟨O, hO, hOe⟩
    obtain ⟨O, hO, hOe⟩ := hrel
    have : (fun y => c.p (c.φ y)) '' (N ∩ V) = O ∩ c.dom := by
      rw [← hOe]
      ext u
      constructor
      · rintro ⟨y, ⟨hy, hyV⟩, rfl⟩
        refine ⟨?_, c.coord_mem_dom hy⟩
        change c.q (c.coord y) ∈ V
        rw [c.q_coord' hy]; exact hyV
      · rintro ⟨huV, hu⟩
        exact ⟨c.q u, ⟨c.q_mem hu, huV⟩, c.coord_q hu⟩
    rw [this]
    exact hO.measurableSet.inter c.measurableSet_dom
  p_L y hy := c.p_L y hy.1
  range_L y hy := by
    rw [c.range_L y hy.1]
    exact ((chartTangent_eq_iff c.isChart (c.subset_source hy.1)).2
      (submanifoldTangent_inter_isOpen hV hy.2)).symm
  hasFDerivWithinAt y hy := (c.hasFDerivWithinAt y hy.1).mono (image_mono inter_subset_left)
  continuousOn_L := c.continuousOn_L.mono inter_subset_left

@[simp] theorem restrict_coord {V : Set X} (hV : IsOpen V) : (c.restrict hV).coord = c.coord := rfl

@[simp] theorem restrict_q {V : Set X} (hV : IsOpen V) : (c.restrict hV).q = c.q := rfl

@[simp] theorem restrict_tvec {V : Set X} (hV : IsOpen V) : (c.restrict hV).tvec = c.tvec := rfl

theorem restrict_dom_subset {V : Set X} (hV : IsOpen V) : (c.restrict hV).dom ⊆ c.dom :=
  image_mono inter_subset_left

/-! ### Null sets -/

/-- A subset of `N` of `n`-dimensional measure zero has a Lebesgue null coordinate image. -/
theorem volume_coord_image_eq_zero {A : Set X} (hA : A ⊆ N) (h : P.IsHNull n A) :
    volume (c.coord '' A) = 0 := by
  have hsep : TopologicalSpace.IsSeparable (c.φ '' A) := by
    have h1 : c.φ '' A = (fun u => c.φ (c.q u)) '' (c.coord '' A) := by
      rw [image_image]
      exact image_congr fun y hy => (congrArg c.φ (c.q_coord' (hA hy))).symm
    rw [h1]
    have hc : ContinuousOn (fun u => c.φ (c.q u)) (c.coord '' A) := fun u hu =>
      (ContinuousWithinAt.mono (by
        obtain ⟨y, hy, rfl⟩ := hu
        exact (c.hasFDerivWithinAt y (hA hy)).continuousWithinAt) (image_mono hA))
    rw [← Set.range_domRestrict]
    exact TopologicalSpace.isSeparable_range (continuousOn_iff_continuous_domRestrict.1 hc)
  have h1 := h c.φ c.isChart A subset_rfl (hA.trans c.subset_source) hsep
  have h2 := h1.image_lipschitzOn (Nat.cast_nonneg n) (c.p.lipschitz.lipschitzOnWith (s := c.φ '' A))
  rw [image_image] at h2
  exact (hNull_iff_volume_euclidean _).1 h2

/-- A subset of `N` with Lebesgue null coordinate image has `n`-dimensional measure zero. -/
theorem isHNull_of_volume_coord_image (hN : P.IsSmoothSubmanifold N) {A : Set X} (hA : A ⊆ N)
    (h : volume (c.coord '' A) = 0) : P.IsHNull n A := by
  refine isHNull_of_forall_exists_chart hN hA fun z hz =>
    ⟨c.φ, c.isChart, c.subset_source (hA hz), univ, isOpen_univ, mem_univ z, ?_⟩
  have h1 : c.φ '' (A ∩ univ ∩ c.φ.source) ⊆ (fun u => c.φ (c.q u)) '' (c.coord '' A) := by
    rintro _ ⟨y, ⟨⟨hy, -⟩, -⟩, rfl⟩
    exact ⟨c.coord y, mem_image_of_mem _ hy, congrArg c.φ (c.q_coord' (hA hy))⟩
  refine HNull.mono ?_ h1
  refine hNull_image_of_pointwise_lipschitz (Nat.cast_nonneg n) ?_
    (TopologicalSpace.IsSeparable.of_separableSpace _) ((hNull_iff_volume_euclidean _).2 h)
  rintro _ ⟨y, hy, rfl⟩
  have hd := ((c.hasFDerivWithinAt y (hA hy)).mono (image_mono hA)).isBigO_sub
  obtain ⟨C, hC⟩ := hd.bound
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hC
  refine ⟨⟨|C|, abs_nonneg C⟩, δ, hδ, fun b hb hbd => ?_⟩
  have this : ‖c.φ (c.q b) - c.φ (c.q (c.coord y))‖ ≤ C * ‖b - c.coord y‖ := hball ⟨hbd, hb⟩
  rw [dist_eq_norm, dist_eq_norm]
  exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))

/-! ### Measurable sets -/

/-- The coordinate image of the trace on `N` of a Borel set is measurable. -/
theorem measurableSet_coord_image_borel {B : Set X} (hB : MeasurableSet[borel X] B) :
    MeasurableSet (c.coord '' (B ∩ N)) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have hr : Continuous (c.dom.domRestrict c.q) := continuousOn_iff_continuous_domRestrict.1
    c.continuousOn_q
  have hm : MeasurableSet (c.dom.domRestrict c.q ⁻¹' B) := hr.measurable hB
  have h := c.measurableSet_dom'.subtype_image hm
  convert h using 1
  ext u
  constructor
  · rintro ⟨y, ⟨hyB, hy⟩, rfl⟩
    refine ⟨⟨c.coord y, c.coord_mem_dom hy⟩, ?_, rfl⟩
    change c.q (c.coord y) ∈ B
    rw [c.q_coord' hy]; exact hyB
  · rintro ⟨⟨v, hv⟩, hvB, rfl⟩
    exact ⟨c.q v, ⟨hvB, c.q_mem hv⟩, c.coord_q hv⟩

/-- **The coordinate image of a measurable subset of `N`** (a Borel set modified by a set of
`n`-dimensional measure zero) **is Lebesgue measurable.** -/
theorem nullMeasurableSet_coord_image {A B : Set X} (hB : MeasurableSet[borel X] B)
    (h : P.IsHNull n ((A ∩ N) ∆ (B ∩ N))) : NullMeasurableSet (c.coord '' (A ∩ N)) volume := by
  have h0 := c.volume_coord_image_eq_zero
    (fun y hy => by rcases hy with hy | hy <;> exact hy.1.2) h
  have hsub : (c.coord '' (B ∩ N)) ∆ (c.coord '' (A ∩ N)) ⊆
      c.coord '' ((A ∩ N) ∆ (B ∩ N)) := by
    rintro u (⟨⟨y, hy, rfl⟩, hn⟩ | ⟨⟨y, hy, rfl⟩, hn⟩)
    · exact ⟨y, Or.inr ⟨hy, fun hc => hn ⟨y, hc, rfl⟩⟩, rfl⟩
    · exact ⟨y, Or.inl ⟨hy, fun hc => hn ⟨y, hc, rfl⟩⟩, rfl⟩
  exact (c.measurableSet_coord_image_borel hB).nullMeasurableSet.congr
    (measure_symmDiff_eq_zero_iff.1 (measure_mono_null hsub h0))

end GraphChart

end MPolyfold

end Polyfold
