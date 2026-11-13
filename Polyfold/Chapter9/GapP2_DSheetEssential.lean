import Polyfold.Chapter9.GapP2_DSheetChartChange
import Polyfold.Chapter9.BranchingGeometryMeasure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Lemmas 9.4.4 and 9.4.6, p. 431 (2017: Lemmas 9.13, 9.14, p. 317), for the sheets of a
general M-polyfold.

# Lemma 9.4.6 for submanifolds of an M-polyfold, and the sheet geometry of §9.4

Definition 9.4.1 is read in M-polyfold charts (`chartEssentialSet`,
`Chapter9/SheetEssentialChart2021.lean`, which has Lemma 9.4.4 in this reading), and Definition
9.4.5 as `n`-dimensional measure zero in M-polyfold charts (`IsHNull`,
`Chapter9/GapP2_DSheetNull.lean`).  Both readings are independent of the chart
(`Chapter9/GapP2_DSheetChartChange.lean`).

## What is formalized

* `MPolyfold.exists_mem_tangentConeAt_proj`: near a point of a smooth submanifold, every limit
  direction of the tangent projection `p(φ(A))` of a set `A ⊆ M` is the projection of a limit
  direction of `φ(A)` (the chords of `M` at `w` are close to the finite-dimensional `T_wM`, so
  the rescaled chords have convergent subsequences).
* `MPolyfold.exists_hNull_chart_not_isRelTangentFull`: in a chart, near a point of an
  `n`-dimensional `M`, the points `z ∈ K` with `T_z^K M ≠ T_zM` form an `n`-null set (their
  tangent projections are points of `p(φ(K))` where the tangent cone does not span, a Lebesgue
  null set by the density theorem, `addHaar_setOf_span_tangentConeAt_ne_top`).
* `MPolyfold.isHNull_setOf_not_isRelTangentFull` and **Lemma 9.4.6**
  (`MPolyfold.lemma_9_4_6_chart`): for `K ⊆ M`, `M` an `n`-dimensional submanifold of an
  M-polyfold, the non-essential points `K ∖ K^e` have `n`-dimensional measure zero.
* `MPolyfold.sheetGeometry n`, `MPolyfold.sheetMeasureGeometry n`: the `SheetGeometry` and
  `SheetMeasureGeometry` of §9.4, §9.5 for the class of `n`-dimensional submanifolds of an
  arbitrary M-polyfold, with no hypothesis.  Its fields are Lemma 9.4.4 (`lemma_9_4_4_chart`),
  Lemma 9.4.6, the note of Definition 9.4.7, and the properties of the null sets.

## Relation to the text

Lemmas 9.4.4 and 9.4.6 are stated in the text for the sheets of a local branching structure.  For
sheets of one dimension they hold as stated, in this reading.  For sheets of different dimensions
Lemma 9.4.4 does not hold as we read it (`lemma_9_4_4_mixed_dim`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace Submodule
open scoped NNReal ENNReal

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Limit directions of the tangent projection lift**: let `A ⊆ M` lie in the domain of a chart
`φ`, and let `p` be continuous linear into a normed space `N`, expanding up to the factor `2` on
`φ(A)`.  Then every vector of the tangent cone of `p(φ(A))` at `p(φ(w))`, `w ∈ A`, is `p(v')` for
a vector `v'` of the tangent cone of `φ(A)` at `φ(w)`.  (For `a_k ∈ A` with
`c_k (p φ(a_k) − p φ(w)) → v`, the vectors `c_k (φ(a_k) − φ(w))` are bounded and close to the
finite-dimensional `T_wM`, so a subsequence converges.) -/
theorem exists_mem_tangentConeAt_proj {φ : MChart X} (hφ : P.IsChart φ) {M : Set X}
    (hM : P.IsSmoothSubmanifold M) {A : Set X} (hAM : A ⊆ M ∩ φ.source) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] (p : φ.model.E 0 →L[ℝ] N)
    (hhalf : ∀ a ∈ A, ∀ b ∈ A, dist (φ a) (φ b) ≤ (2 : ℝ≥0) * dist (p (φ a)) (p (φ b)))
    {w : X} (hw : w ∈ A) {v : N}
    (hv : v ∈ tangentConeAt ℝ ((fun e => p e) '' (φ '' A)) (p (φ w))) :
    ∃ v' ∈ tangentConeAt ℝ (φ '' A) (φ w), p v' = v := by
  classical
  obtain ⟨c, dN, hd0, hds, hcd⟩ := mem_tangentConeAt_iff_exists_seq.1 hv
  -- points of `A` over the sequence
  have hex : ∀ k, ∃ a ∈ A, (p (φ w) + dN k ∈ (fun e => p e) '' (φ '' A) →
      p (φ a) = p (φ w) + dN k) := fun k => by
    by_cases hk : p (φ w) + dN k ∈ (fun e => p e) '' (φ '' A)
    · obtain ⟨_, ⟨a, ha, rfl⟩, hpa⟩ := hk
      exact ⟨a, ha, fun _ => hpa⟩
    · exact ⟨w, hw, fun h => (hk h).elim⟩
  choose a haA ha using hex
  set e : ℕ → φ.model.E 0 := fun k => φ (a k) - φ w with hedef
  have hpe : ∀ᶠ k in atTop, p (e k) = dN k := by
    filter_upwards [hds] with k hk
    rw [hedef]
    change p (φ (a k) - φ w) = dN k
    rw [map_sub, ha k hk, add_sub_cancel_left]
  have hnorm : ∀ᶠ k in atTop, ‖e k‖ ≤ 2 * ‖dN k‖ := by
    filter_upwards [hpe] with k hk
    have h := hhalf (a k) (haA k) w hw
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_ofNat] at h
    rw [← hk]
    exact h
  have he0 : Tendsto e atTop (𝓝 0) := by
    refine squeeze_zero_norm' hnorm ?_
    have := (tendsto_norm_zero.comp hd0).const_mul 2
    simpa using this
  -- the rescaled chords are bounded
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hcd).exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ ⟨0, rfl⟩)
  have hce : ∀ᶠ k in atTop, ‖c k • e k‖ ≤ 2 * B := by
    filter_upwards [hnorm] with k hk
    rw [norm_smul]
    calc ‖c k‖ * ‖e k‖ ≤ ‖c k‖ * (2 * ‖dN k‖) := by gcongr
      _ = 2 * ‖c k • dN k‖ := by rw [norm_smul]; ring
      _ ≤ 2 * B := by gcongr; exact hB _ ⟨k, rfl⟩
  -- the tangent space at `w`
  have hwM := (hAM hw).1
  have hwφ := (hAM hw).2
  obtain ⟨Nw, hfin, pw, hNw, hpw⟩ := exists_proj_chartTangent hφ hM hwM hwφ
  set y : ℕ → Nw := fun k => pw (c k • e k) with hydef
  have hfreq : ∃ᶠ k in atTop, y k ∈ closedBall (0 : Nw) (‖pw‖ * (2 * B)) := by
    refine Eventually.frequently ?_
    filter_upwards [hce] with k hk
    rw [mem_closedBall, dist_zero_right]
    exact (pw.le_opNorm _).trans (by gcongr)
  obtain ⟨yl, -, θ, hθ, hlim⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall hfreq
  -- the remainder tends to `0`
  have hrem : Tendsto (fun k => c k • e k - (y k : φ.model.E 0)) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hε' : 0 < ε / (2 * B + 1) := by positivity
    obtain ⟨δ, hδ, happ⟩ := exists_proj_approx hφ hM hwM hwφ hNw pw hpw hε'
    have hsmall : ∀ᶠ k in atTop, ‖e k‖ < δ :=
      (tendsto_norm_zero.comp he0).eventually (gt_mem_nhds hδ)
    filter_upwards [hce, hsmall] with k hk hks
    have h := happ (a k) (hAM (haA k)) w (hAM hw) hks (by rw [sub_self, norm_zero]; exact hδ)
    have e1 : c k • e k - (y k : φ.model.E 0) = c k • (e k - (pw (e k) : φ.model.E 0)) := by
      have e2 : (y k : φ.model.E 0) = c k • (pw (e k) : φ.model.E 0) := by
        change ((pw (c k • e k) : Nw) : φ.model.E 0) = _
        rw [map_smul]
        rfl
      rw [e2, ← smul_sub]
    rw [e1, norm_smul]
    calc ‖c k‖ * ‖e k - (pw (e k) : φ.model.E 0)‖
        ≤ ‖c k‖ * (ε / (2 * B + 1) * ‖e k‖) := by gcongr
      _ = ε / (2 * B + 1) * ‖c k • e k‖ := by rw [norm_smul]; ring
      _ ≤ ε / (2 * B + 1) * (2 * B) := by gcongr
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  -- the limit direction
  have hθt : Tendsto θ atTop atTop := hθ.tendsto_atTop
  have hlim' : Tendsto (fun k => c (θ k) • e (θ k)) atTop (𝓝 (yl : φ.model.E 0)) := by
    have h1 := (hrem.comp hθt).add ((continuous_subtype_val.tendsto yl).comp hlim)
    rw [zero_add] at h1
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply, sub_add_cancel]
  refine ⟨yl, mem_tangentConeAt_of_seq atTop (fun k => c (θ k)) (fun k => e (θ k))
    (he0.comp hθt) (Eventually.of_forall fun k => ?_) hlim', ?_⟩
  · rw [hedef]
    change φ w + (φ (a (θ k)) - φ w) ∈ φ '' A
    rw [add_sub_cancel]
    exact ⟨a (θ k), haA _, rfl⟩
  · have h1 : Tendsto (fun k => p (c (θ k) • e (θ k))) atTop (𝓝 (p yl)) :=
      (p.continuous.tendsto _).comp hlim'
    have h2 : Tendsto (fun k => p (c (θ k) • e (θ k))) atTop (𝓝 v) := by
      refine (hcd.comp hθt).congr' ?_
      filter_upwards [hθt.eventually hpe] with k hk
      simp only [Function.comp_apply]
      rw [map_smul, hk]
    exact tendsto_nhds_unique h1 h2

/-- **The points with `T_z^K M ≠ T_zM` are null in a chart** (the core of Lemma 9.4.6): for
`K ⊆ M`, `M` of dimension `n`, a chart `φ` at `x ∈ M`, and a small neighbourhood `V` of `x`, the
chart image of `{z ∈ K | T_z^K M ≠ T_zM} ∩ V` has `n`-dimensional Hausdorff measure `0`. -/
theorem exists_hNull_chart_not_isRelTangentFull {M K : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (hKM : K ⊆ M) {x : X} (hx : x ∈ M) {φ : MChart X}
    (hφ : P.IsChart φ) (hxφ : x ∈ φ.source) :
    ∃ V, IsOpen V ∧ x ∈ V ∧
      HNull (n : ℝ) (φ '' ({z | z ∈ K ∧ ¬ P.IsRelTangentFull M K z} ∩ V ∩ φ.source)) := by
  obtain ⟨N, hfin, p, hN, hp⟩ := exists_proj_chartTangent hφ hM.1 hx hxφ
  have hn : finrank ℝ N = n := finrank_chartTangent hφ (hM.2 x hx) hM.1 hxφ hN
  obtain ⟨δ, hδ, hhalf⟩ := exists_half_approx hφ hM.1 hx hxφ hN p hp
  obtain ⟨V, hV, hVe⟩ := exists_isOpen_chartBall φ M x δ
  have hxV : x ∈ V := by
    have : x ∈ chartBall φ M x δ := ⟨⟨hx, hxφ⟩, by rw [sub_self, norm_zero]; exact hδ⟩
    rw [hVe] at this
    exact this.2
  refine ⟨V, hV, hxV, ?_⟩
  set A : Set X := K ∩ chartBall φ M x δ with hA
  have hAM : A ⊆ M ∩ φ.source := fun a ha => ha.2.1
  have hAhalf : ∀ a ∈ A, ∀ b ∈ A, dist (φ a) (φ b) ≤ (2 : ℝ≥0) * dist (p (φ a)) (p (φ b)) :=
    fun a ha b hb => hhalf a ha.2.1 b hb.2.1 ha.2.2 hb.2.2
  set Z : Set X := {z | z ∈ K ∧ ¬ P.IsRelTangentFull M K z} with hZ
  have hZA : Z ∩ V ∩ φ.source ⊆ A := fun z hz =>
    ⟨hz.1.1.1, by rw [hVe]; exact ⟨hKM hz.1.1.1, hz.1.2⟩⟩
  refine HNull.of_image_antilipschitzOn (f := fun e => p e) (K := 2) (Nat.cast_nonneg n) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hAhalf a (hZA ha) b (hZA hb)
  -- the image lies in the points where the tangent cone of `p(φ(A))` does not span
  set S : Set N := (fun e => p e) '' (φ '' A) with hS
  have hbad : HNull (n : ℝ) {u | u ∈ S ∧ span ℝ (tangentConeAt ℝ S u) ≠ ⊤} := by
    let _ : MeasurableSpace N := borel N
    have : BorelSpace N := ⟨rfl⟩
    rw [← hn]
    exact hNull_iff.2 (addHaar_setOf_span_tangentConeAt_ne_top μH[(finrank ℝ N : ℝ)] S)
  refine hbad.mono ?_
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  have hzA : z ∈ A := hZA hz
  have hzK : z ∈ K := hz.1.1.1
  have hzM : z ∈ M := hKM hzK
  have hzφ : z ∈ φ.source := hz.2
  refine ⟨⟨φ z, ⟨z, hzA, rfl⟩, rfl⟩, fun htop => hz.1.1.2 ?_⟩
  -- `T_z^K M = T_zM` in the chart `φ`
  refine isRelTangentFull_of_chart hM.1 hKM hzK hφ hzφ ?_
  obtain ⟨Nz, hNz, hfinz⟩ := exists_submodule_chartTangent hφ hM.1 hzM hzφ
  have hnz : finrank ℝ Nz = n := finrank_chartTangent hφ (hM.2 z hzM) hM.1 hzφ hNz
  have hle : P.chartRelTangent hφ K z ≤ Nz := chartRelTangent_le hM.1 hKM hzK hφ hzφ hNz
  have hfinrel : FiniteDimensional ℝ (P.chartRelTangent hφ K z) :=
    Submodule.finiteDimensional_of_le hle
  have hmap : (⊤ : Submodule ℝ N) ≤
      (P.chartRelTangent hφ K z).map (p : φ.model.E 0 →ₗ[ℝ] N) := by
    rw [← htop]
    refine span_le.2 fun v hv => ?_
    obtain ⟨v', hv', hpv⟩ := exists_mem_tangentConeAt_proj hφ hM.1 hAM p hAhalf hzA hv
    refine ⟨v', subset_span (tangentConeAt_mono (image_mono fun a ha => ?_) hv'), hpv⟩
    exact ⟨ha.1, ha.2.1.2⟩
  have hge : finrank ℝ Nz ≤ finrank ℝ (P.chartRelTangent hφ K z) := by
    rw [hnz, ← hn, ← finrank_top ℝ N]
    exact (Submodule.finrank_mono hmap).trans (Submodule.finrank_map_le _ _)
  rw [← hNz, Submodule.eq_of_le_of_finrank_le hle hge]

/-- **The points of `K` with `T_z^K M ≠ T_zM` have measure zero** (Definition 9.4.5 in
M-polyfold charts, all charts), for `K ⊆ M` and `M` an `n`-dimensional submanifold. -/
theorem isHNull_setOf_not_isRelTangentFull {M K : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (hKM : K ⊆ M) :
    P.IsHNull n {z | z ∈ K ∧ ¬ P.IsRelTangentFull M K z} := by
  refine isHNull_of_forall_exists_chart hM.1 (fun z hz => hKM hz.1) fun z hz => ?_
  obtain ⟨φ, hφ, hzφ⟩ := P.exists_isChart_mem_source z
  obtain ⟨V, hV, hzV, hnull⟩ :=
    exists_hNull_chart_not_isRelTangentFull hM hKM (hKM hz.1) hφ hzφ
  exact ⟨φ, hφ, hzφ, V, hV, hzV, hnull⟩

/-- The non-essential points of `K` are among the points with `T_z^K M ≠ T_zM`. -/
theorem diff_chartEssentialSet_subset (M K : Set X) :
    K \ P.chartEssentialSet M K ⊆ {z | z ∈ K ∧ ¬ P.IsRelTangentFull M K z} := fun z hz =>
  ⟨hz.1, fun h => hz.2 ⟨hz.1, fun _ => z, fun _ => ⟨hz.1, h⟩, tendsto_const_nhds⟩⟩

/-- **Lemma 9.4.6, 2021 p. 431 (2017: Lemma 9.14, p. 317)**, for submanifolds of an M-polyfold:
for every subset `K` of an `n`-dimensional submanifold `M`, the non-essential points
`K^{ne} = K ∖ K^e` (Definition 9.4.1 in M-polyfold charts, `chartEssentialSet`) have measure
zero (Definition 9.4.5 in M-polyfold charts, `IsHNull`).  The text states it for
`K = K(i, i') = Mᵢ ∩ Mᵢ'`. -/
theorem lemma_9_4_6_chart {M K : Set X} {n : ℕ} (hM : P.IsSubmanifoldOfDim M n) (hKM : K ⊆ M) :
    P.IsHNull n (K \ P.chartEssentialSet M K) :=
  (isHNull_setOf_not_isRelTangentFull hM hKM).mono (diff_chartEssentialSet_subset M K)

/-! ### The sheet geometry of §9.4 for the `n`-dimensional submanifolds -/

variable (P) in
/-- **The geometry of §9.4 for the `n`-dimensional submanifolds of an M-polyfold**, with no
hypothesis: essential points are those of Definition 9.4.1 in M-polyfold charts, the sets of
measure zero those of Definition 9.4.5 in M-polyfold charts; the fields are Lemma 9.4.4
(`lemma_9_4_4_chart`), the note of Definition 9.4.7
(`submanifoldTangent_eq_of_mem_chartEssentialSet`), Lemma 9.4.6 (`lemma_9_4_6_chart`), and "a
nonempty sheet is not null in itself" (`not_isHNull_of_hasDimAt`). -/
def sheetGeometry (n : ℕ) : P.SheetGeometry {N : Set X | P.IsSubmanifoldOfDim N n} where
  ess N K := P.chartEssentialSet N K
  ess_subset N K := chartEssentialSet_subset N K
  ess_self _ hN := chartEssentialSet_self hN.1
  ess_comm _ hN _ hN' := lemma_9_4_4_chart hN hN'
  submanifoldTangent_eq _ hN _ hN' _ hz :=
    submanifoldTangent_eq_of_mem_chartEssentialSet hN hN' hz
  IsNull N A := P.IsHNull n (A ∩ N)
  isNull_empty N := (P.sheetNullSets n).isNull_empty N
  isNull_mono h hA := (P.sheetNullSets n).isNull_mono h hA
  isNull_union h h' := (P.sheetNullSets n).isNull_union h h'
  not_isNull_self N hN hne := (P.sheetNullSets n).not_isNull_self N hN hne
  isNull_diff_ess _ hN N' _ :=
    (lemma_9_4_6_chart hN (inter_subset_left (t := N'))).mono inter_subset_left

variable (P) in
/-- **The measure geometry of §9.5 for the `n`-dimensional submanifolds of an M-polyfold**: the
`SheetGeometry` above, whose null sets are closed under countable unions, local, and the same on
the overlap of two sheets. -/
def sheetMeasureGeometry (n : ℕ) :
    P.SheetMeasureGeometry {N : Set X | P.IsSubmanifoldOfDim N n} where
  toSheetGeometry := P.sheetGeometry n
  isNull_iUnion h := (P.sheetNullSets n).isNull_iUnion h
  isNull_of_local N hN A h := (P.sheetNullSets n).isNull_of_local N hN A h
  isNull_transfer N hN N' hN' C hC h := (P.sheetNullSets n).isNull_transfer N hN N' hN' C hC h

theorem sheetMeasureGeometry_toSheetNullSets (n : ℕ) :
    (P.sheetMeasureGeometry n).toSheetNullSets = P.sheetNullSets n := rfl

end MPolyfold

end Polyfold
