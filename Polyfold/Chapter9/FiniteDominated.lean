import Polyfold.Chapter9.MultiChartIntegration
import Polyfold.Chapter9.IntegralCovering

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorem 9.5.4 (p. 438), gap G.107.  Numbers and pages are the 2021
text's.

# Sheets dominated by finitely many one-chart sheets lie in the class `F.msheets`

Let `N` be an `n`-dimensional submanifold and `S m` (`m ∈ ℕ`) sheets of the class `F.sheets`
covering `N`.  Then:

* `chartAbs_eq_of_borel`: on a Borel set `A ⊆ M ∩ M'` of two `n`-dimensional sheets the
  integrals `∫_A |ω|` in graph charts of `M` and of `M'` agree (the tangent spaces differ only on
  a set of measure zero, `isNull_tangent_ne`, and `chartAbs_congr` applies off it);
* `exists_chartCover`: `N` has a countable chart cover (`N` is Lindelöf, being covered by
  countably many pieces homeomorphic to subsets of `ℝⁿ`);
* `isFinite_of_dominated`: every chart cover `D` of `N` is finite (`∑ₖ ∫_{P k} |ω| < ∞`) as soon
  as `∑ₘ ∫_{R m} |ω| < ∞` for the disjointed pieces `R m = S m \ ⋃_{j<m} S j` (a double series
  of nonnegative terms, `∫_{P k ∩ R m} |ω|` computed in the chart of `N ∩ V k` or of `S m`);
* `msheets_of_list`: a nonempty `n`-dimensional submanifold covered by a finite list of sheets
  of `F.sheets` is in `F.msheets`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {F : X.FormEval n Ω}

namespace FormEval

/-- Removing a set of measure zero does not change the coordinate image up to a null set. -/
theorem coord_image_diff_ae {N : Set Obj} (c : X.PObj.GraphChart n N) {A Z : Set Obj}
    (hZ : X.PObj.IsHNull n (Z ∩ N)) :
    c.coord '' ((A \ Z) ∩ N) =ᵐ[volume] c.coord '' (A ∩ N) := by
  have h0 := c.volume_coord_image_eq_zero inter_subset_right hZ
  refine ae_eq_set.2 ⟨?_, measure_mono_null ?_ h0⟩
  · rw [sdiff_eq_empty.2 (image_mono (inter_subset_inter_left N sdiff_subset)), measure_empty]
  · rintro _ ⟨⟨y, hy, rfl⟩, hn⟩
    refine ⟨y, ⟨?_, hy.2⟩, rfl⟩
    by_contra hyZ
    exact hn ⟨y, ⟨⟨hy.1, hyZ⟩, hy.2⟩, rfl⟩

/-- `∫_A |ω|` does not change when a set of measure zero is removed from `A`. -/
theorem chartAbs_diff_null {N : Set Obj} (c : X.PObj.GraphChart n N) (ω : Ω) {A Z : Set Obj}
    (hZ : X.PObj.IsHNull n (Z ∩ N)) : F.chartAbs c ω (A \ Z) = F.chartAbs c ω A := by
  unfold chartAbs
  exact setIntegral_congr_set (coord_image_diff_ae c hZ)

/-- **`∫_A |ω|` in graph charts of two `n`-dimensional sheets agrees on a common Borel set**:
the tangent spaces differ only on a set of measure zero. -/
theorem chartAbs_eq_of_borel {M M' : Set Obj} (hM : X.PObj.IsSubmanifoldOfDim M n)
    (hM' : X.PObj.IsSubmanifoldOfDim M' n) (c : X.PObj.GraphChart n M)
    (c' : X.PObj.GraphChart n M') (ω : Ω) {A : Set Obj} (hA : A ⊆ M ∩ M')
    (hAb : MeasurableSet[borel Obj] A) : F.chartAbs c ω A = F.chartAbs c' ω A := by
  set Z : Set Obj := {y | y ∈ M ∩ M' ∧
    X.PObj.submanifoldTangent M y ≠ X.PObj.submanifoldTangent M' y} with hZdef
  have hZ : X.PObj.IsHNull n (Z ∩ M) := isNull_tangent_ne hM hM'
  have hZ' : X.PObj.IsHNull n (Z ∩ M') := by
    refine MPolyfold.IsHNull.mono (isNull_tangent_ne hM' hM) ?_
    rintro y ⟨⟨⟨hy, hy'⟩, hne⟩, -⟩
    exact ⟨⟨⟨hy', hy⟩, fun h => hne h.symm⟩, hy'⟩
  have hAM : A ∩ M = A := inter_eq_left.2 fun y hy => (hA hy).1
  have hAZM : (A \ Z) ∩ M = A \ Z := inter_eq_left.2 fun y hy => (hA hy.1).1
  have hnm : NullMeasurableSet (c.coord '' (A \ Z)) volume := by
    have h := (c.measurableSet_coord_image_borel hAb).nullMeasurableSet (μ := volume)
    rw [hAM] at h
    have he := coord_image_diff_ae (A := A) c hZ
    rw [hAZM, hAM] at he
    exact h.congr he.symm
  rw [← chartAbs_diff_null c ω hZ, ← chartAbs_diff_null c' ω hZ']
  refine F.chartAbs_congr hM hM' c c' ω (fun y hy => hA hy.1) hnm fun y hy => ?_
  by_contra hne
  exact hy.2 ⟨hA hy.1, hne⟩

theorem chartAbs_empty {N : Set Obj} (c : X.PObj.GraphChart n N) (ω : Ω) :
    F.chartAbs c ω ∅ = 0 := by
  unfold chartAbs
  rw [empty_inter, image_empty, Measure.restrict_empty, integral_zero_measure]

/-- **A countable chart cover** of an `n`-dimensional submanifold covered by countably many sheets
of the class `F.sheets`. -/
theorem exists_chartCover {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n) (hne : N.Nonempty)
    {S : ℕ → Set Obj} (hS : ∀ m, S m ∈ F.sheets) (hcov : N ⊆ ⋃ m, S m) :
    Nonempty (F.ChartCover N) := by
  have hL : IsLindelof N := by
    have e : N = ⋃ m, N ∩ S m := by
      rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
    rw [e]
    refine isLindelof_iUnion fun m => ?_
    have := hereditarilyLindelofSpace (chart (hS m))
    have h := (HereditarilyLindelofSpace.isLindelof
      (Subtype.val ⁻¹' N : Set (S m))).image continuous_subtype_val
    rwa [Subtype.image_preimage_coe, inter_comm] at h
  choose Vf hVo hyV hVs using fun y : N => exists_mem_sheets (F := F) hN y.2
  obtain ⟨r, hrc, hr⟩ := hL.elim_countable_subcover Vf hVo
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyV _⟩)
  have hrne : r.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz, -⟩ := mem_iUnion₂.1 (hr hy)
    exact ⟨z, hz⟩
  obtain ⟨f, hf⟩ := hrc.exists_eq_range hrne
  exact ⟨{ V := fun k => Vf (f k)
           isOpen := fun k => hVo _
           cover := fun y hy => by
             obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hr hy)
             rw [hf] at hz
             obtain ⟨k, rfl⟩ := hz
             exact mem_iUnion.2 ⟨k, hyz⟩
           mem := fun k => hVs _ }⟩

/-- **Domination**: a chart cover of `N` is finite if `N` is covered by sheets `S m` of
`F.sheets` whose disjointed pieces carry summable integrals of `|ω|`. -/
theorem isFinite_of_dominated {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    (D : F.ChartCover N) {S : ℕ → Set Obj} (hS : ∀ m, S m ∈ F.sheets) (hcov : N ⊆ ⋃ m, S m)
    (hsum : ∀ ω, Summable fun m => F.chartAbs (chart (hS m)) ω (disjointed S m)) :
    D.IsFinite := by
  intro ω
  let _ : MeasurableSpace Obj := borel Obj
  have hNb : MeasurableSet N := hN.1.measurableSet_borel
  have hRb : ∀ m, MeasurableSet (disjointed S m) :=
    MeasurableSet.disjointed fun m => (hS m).1.1.measurableSet_borel
  have hPRb : ∀ k m, MeasurableSet (D.P k ∩ disjointed S m) := fun k m =>
    (D.measurableSet_P hNb k).inter (hRb m)
  set a : ℕ → ℕ → ℝ := fun k m => F.chartAbs (chart (D.mem k)) ω (D.P k ∩ disjointed S m)
    with ha_def
  set b : ℕ → ℕ → ℝ := fun m k => F.chartAbs (chart (hS m)) ω (D.P k ∩ disjointed S m)
    with hb_def
  have hab : ∀ k m, a k m = b m k := fun k m =>
    chartAbs_eq_of_borel (D.mem k).1 (hS m).1 _ _ ω
      (fun y hy => ⟨D.P_subset k hy.1, disjointed_subset S m hy.2⟩) (hPRb k m)
  have ha : ∀ k, HasSum (a k) (F.chartAbs (chart (D.mem k)) ω (D.P k)) := fun k => by
    have h := F.chartAbs_hasSum (chart (D.mem k)) ω (integrableOn_chart (D.mem k) ω)
      (fun m => D.P k ∩ disjointed S m)
      (fun m => ((chart (D.mem k)).measurableSet_coord_image_borel (hPRb k m)).nullMeasurableSet)
      (fun i j hij => (disjoint_disjointed S hij).mono inter_subset_right inter_subset_right)
    have e : (⋃ m, D.P k ∩ disjointed S m) = D.P k := by
      rw [← inter_iUnion, iUnion_disjointed]
      exact inter_eq_left.2 fun y hy => hcov (D.P_subset k hy).1
    rw [e] at h
    exact h
  have hb : ∀ m, HasSum (b m) (F.chartAbs (chart (hS m)) ω (⋃ k, D.P k ∩ disjointed S m)) :=
    fun m => F.chartAbs_hasSum (chart (hS m)) ω (integrableOn_chart (hS m) ω)
      (fun k => D.P k ∩ disjointed S m)
      (fun k => ((chart (hS m)).measurableSet_coord_image_borel (hPRb k m)).nullMeasurableSet)
      (fun i j hij => (D.disjoint_P hij).mono inter_subset_left inter_subset_left)
  have hble : ∀ m, F.chartAbs (chart (hS m)) ω (⋃ k, D.P k ∩ disjointed S m) ≤
      F.chartAbs (chart (hS m)) ω (disjointed S m) := fun m =>
    F.chartAbs_mono _ ω (integrableOn_chart (hS m) ω) fun y hy => by
      obtain ⟨k, hk⟩ := mem_iUnion.1 hy.1
      exact hk.2
  have hb0 : 0 ≤ fun p : ℕ × ℕ => b p.1 p.2 := fun p => F.chartAbs_nonneg _ ω _
  have hbs : Summable fun p : ℕ × ℕ => b p.1 p.2 := by
    refine (summable_prod_of_nonneg hb0).2 ⟨fun m => (hb m).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k => hb0 (m, k))
      (fun m => ?_) (hsum ω)
    rw [(hb m).tsum_eq]
    exact hble m
  have has : Summable fun p : ℕ × ℕ => a p.1 p.2 := by
    have e : (fun p : ℕ × ℕ => a p.1 p.2) = (fun p : ℕ × ℕ => b p.1 p.2) ∘ Prod.swap := by
      funext p; exact hab p.1 p.2
    rw [e]
    exact (Equiv.prodComm ℕ ℕ).summable_iff.2 hbs
  have ha0 : 0 ≤ fun p : ℕ × ℕ => a p.1 p.2 := fun p => F.chartAbs_nonneg _ ω _
  refine (((summable_prod_of_nonneg ha0).1 has).2).congr fun k => ?_
  exact (ha k).tsum_eq

/-- **A submanifold dominated by countably many one-chart sheets is in `F.msheets`.** -/
theorem msheets_of_dominated {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hne : N.Nonempty) {S : ℕ → Set Obj} (hS : ∀ m, S m ∈ F.sheets) (hcov : N ⊆ ⋃ m, S m)
    (hsum : ∀ ω, Summable fun m => F.chartAbs (chart (hS m)) ω (disjointed S m)) :
    N ∈ F.msheets := by
  obtain ⟨D⟩ := exists_chartCover hN hne hS hcov
  exact ⟨hN, D, isFinite_of_dominated hN D hS hcov hsum⟩

/-- **A nonempty `n`-dimensional submanifold covered by a finite list of sheets of `F.sheets`
is in the class `F.msheets`.** -/
theorem msheets_of_list {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n) (hne : N.Nonempty)
    {L : List (Set Obj)} (hL : ∀ s ∈ L, s ∈ F.sheets) (hcov : N ⊆ ⋃ s ∈ L, s) :
    N ∈ F.msheets := by
  have hL0 : 0 < L.length := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨s, hs, -⟩ := mem_iUnion₂.1 (hcov hy)
    exact List.length_pos_of_mem hs
  set s₀ := L[0]'hL0 with hs₀
  set S : ℕ → Set Obj := fun m => L.getD m s₀ with hSdef
  have hS : ∀ m, S m ∈ F.sheets := fun m => by
    by_cases hm : m < L.length
    · change L.getD m s₀ ∈ F.sheets
      rw [List.getD_eq_getElem _ _ hm]; exact hL _ (List.getElem_mem _)
    · change L.getD m s₀ ∈ F.sheets
      rw [List.getD_eq_default _ _ (not_lt.1 hm)]; exact hL _ (List.getElem_mem _)
  have hcov' : N ⊆ ⋃ m, S m := fun y hy => by
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 (hcov hy)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hs
    refine mem_iUnion.2 ⟨j, ?_⟩
    change y ∈ L.getD j s₀
    rw [List.getD_eq_getElem _ _ hj]; exact hys
  refine msheets_of_dominated hN hne hS hcov' fun ω =>
    summable_of_ne_finset_zero (s := Finset.range L.length) fun m hm => ?_
  have hm' : L.length ≤ m := by simpa using hm
  have hR : disjointed S m = ∅ := by
    refine eq_empty_of_forall_notMem fun y hy => ?_
    rw [disjointed_eq_inter_compl] at hy
    have hS0 : S m = S 0 := by
      change L.getD m s₀ = L.getD 0 s₀
      rw [List.getD_eq_default _ _ hm', List.getD_eq_getElem _ _ hL0]
    have hyS : y ∈ S 0 := hS0 ▸ hy.1
    exact mem_iInter₂.1 hy.2 0 (lt_of_lt_of_le hL0 hm') hyS
  rw [hR]
  exact chartAbs_empty _ ω

end FormEval

end EpGroupoid

end Polyfold
