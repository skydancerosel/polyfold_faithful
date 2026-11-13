import Polyfold.Chapter9.SheetEssentialChart2021
import Polyfold.Chapter9.Measure
import Polyfold.Chapter9.GeneralBoundaryPoints

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Definition 9.4.5, p. 431, and §9.5, Definition 9.5.1, p. 437 (2017: Definitions 9.13 and
9.15), for submanifolds of a general M-polyfold.

# Sets of measure zero in the sheets of an M-polyfold

Definition 9.4.5 asks that `ϕ(U ∩ K)` be a Lebesgue null set for the smooth charts `ϕ` of a sheet
`Mᵢ`.  The sheets of an M-polyfold carry no manifold charts of their own in this project, so the
notion was an abstract system (`SheetNullSets`, `Chapter9/Measure.lean`).  Here it is a concrete
one, read in the M-polyfold charts `ψ` of the ambient space: the `n`-dimensional Hausdorff
measure, for the level-`0` norm, of the chart image is `0`.  On an `n`-dimensional sheet the chart
image is locally a bi-Lipschitz copy of a subset of `ℝⁿ` (the tangent projection, 2021 Lemmas
9.2.10, 9.2.11), where the `n`-dimensional Hausdorff measure is a Lebesgue measure; so these are
the Lebesgue null sets of Definition 9.4.5.

## What is formalized

* `HNull d s`: the `d`-dimensional Hausdorff measure of `s` is `0` (the Borel σ-algebra is chosen
  inside the definition; `hNull_iff`), with `HNull.mono`, `hNull_iUnion`,
  `HNull.image_lipschitzOn`, `HNull.of_image_antilipschitzOn`, and the positivity
  `not_hNull_of_ball_subset` (a set whose image under a continuous linear map to an
  `n`-dimensional space contains a ball is not `n`-null).
* `MPolyfold.IsHNull n C` (**Definition 9.4.5** in M-polyfold charts): for every chart `ψ` and
  every `D ⊆ C` in its domain with separable chart image, `HNull n (ψ '' D)`.  It is a σ-ideal
  (`IsHNull.mono`, `isHNull_iUnion`) and local (`isHNull_of_local`).
* `MPolyfold.exists_half_approx`: near a point `x` of a smooth submanifold `M`, the tangent
  projection `p` onto `T_xM` satisfies `‖(ψa − ψb) − p(ψa − ψb)‖ ≤ ½ ‖ψa − ψb‖` on `M`
  (so it is injective with Lipschitz inverse there).
* `MPolyfold.not_isHNull_of_hasDimAt`: a smooth submanifold of dimension `n` at one of its points
  is not `n`-null (the tangent projection of `M` near `x` contains a ball of `T_xM`:
  `exists_graph_unif_chart`, `exists_small_cone`).
* `MPolyfold.sheetNullSets n`: the `SheetNullSets` of the class of `n`-dimensional submanifolds,
  with no hypothesis; Definition 9.5.1, Lemma 9.5.2 and Definition 9.5.3 of
  `Chapter9/Measure.lean` apply to it.

## The choices made

* Separable pieces: `E₀` need not be separable, and the Hausdorff measure of a non-separable set
  is `∞`; the sheets are locally separable (`isSeparable_chart_ball`), so nothing is lost.
* The definition does not mention the sheet: for sheets of one dimension the transfer property
  of Lemma 9.5.2 (two sheets induce the same null sets on their overlap) is then immediate.  The
  content is that a sheet is not null in itself, which needs the dimension of the sheet to be
  `n`; across dimensions the transfer does not hold as we read it (`isNull_transfer_mixed_dim`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace
open scoped NNReal ENNReal

noncomputable section

namespace Polyfold

universe u

/-! ### Hausdorff null sets -/

section HNull

variable {E : Type*} [EMetricSpace E]

/-- **The `d`-dimensional Hausdorff measure of `s` is zero** (for the Borel σ-algebra of `E`,
chosen here so that no `MeasurableSpace` instance on `E` is needed). -/
def HNull (d : ℝ) (s : Set E) : Prop :=
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  μH[d] s = 0

theorem hNull_iff [MeasurableSpace E] [BorelSpace E] {d : ℝ} {s : Set E} :
    HNull d s ↔ μH[d] s = 0 := by
  obtain rfl : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  rfl

theorem HNull.mono {d : ℝ} {s t : Set E} (h : HNull d t) (hst : s ⊆ t) : HNull d s := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact measure_mono_null hst (hNull_iff.1 h) |> hNull_iff.2

theorem hNull_empty (d : ℝ) : HNull d (∅ : Set E) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact hNull_iff.2 measure_empty

theorem hNull_iUnion {ι : Type*} [Countable ι] {d : ℝ} {s : ι → Set E}
    (h : ∀ i, HNull d (s i)) : HNull d (⋃ i, s i) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact hNull_iff.2 (measure_iUnion_null fun i => hNull_iff.1 (h i))

/-- Lipschitz images of `d`-null sets are `d`-null. -/
theorem HNull.image_lipschitzOn {F : Type*} [EMetricSpace F] {K : ℝ≥0} {f : E → F} {s : Set E}
    {d : ℝ} (hd : 0 ≤ d) (hf : LipschitzOnWith K f s) (h : HNull d s) : HNull d (f '' s) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  refine hNull_iff.2 (le_antisymm ((hf.hausdorffMeasure_image_le hd).trans ?_) bot_le)
  rw [hNull_iff.1 h, mul_zero]

end HNull

section Antilipschitz

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- A map that is expanding up to a factor on `s` has a Lipschitz inverse on `f '' s`. -/
theorem exists_lipschitzOn_inverse [Nonempty E] {f : E → F} {s : Set E} {K : ℝ≥0}
    (hf : ∀ a ∈ s, ∀ b ∈ s, dist a b ≤ K * dist (f a) (f b)) :
    ∃ g : F → E, LipschitzOnWith K g (f '' s) ∧ g '' (f '' s) = s := by
  classical
  refine ⟨Function.invFunOn f s, LipschitzOnWith.of_dist_le_mul ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := Function.invFunOn_mem (f := f) (s := s) ⟨a, ha, rfl⟩
    have h2 := Function.invFunOn_mem (f := f) (s := s) ⟨b, hb, rfl⟩
    have h := hf _ h1 _ h2
    rwa [Function.invFunOn_eq (f := f) ⟨a, ha, rfl⟩,
      Function.invFunOn_eq (f := f) ⟨b, hb, rfl⟩] at h
  · refine subset_antisymm ?_ fun a ha => ⟨f a, ⟨a, ha, rfl⟩, ?_⟩
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact Function.invFunOn_mem (f := f) (s := s) ⟨a, ha, rfl⟩
    · have h1 := Function.invFunOn_mem (f := f) (s := s) ⟨a, ha, rfl⟩
      have h := hf _ h1 a ha
      rw [Function.invFunOn_eq (f := f) ⟨a, ha, rfl⟩, dist_self, mul_zero] at h
      exact dist_le_zero.1 h

/-- If `f` is expanding up to a factor on `s` and `f '' s` is `d`-null, then `s` is `d`-null. -/
theorem HNull.of_image_antilipschitzOn {f : E → F} {s : Set E} {K : ℝ≥0} {d : ℝ} (hd : 0 ≤ d)
    (hf : ∀ a ∈ s, ∀ b ∈ s, dist a b ≤ K * dist (f a) (f b)) (h : HNull d (f '' s)) :
    HNull d s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, -⟩
  · exact hNull_empty d
  have : Nonempty E := ⟨a₀⟩
  obtain ⟨g, hg, hgs⟩ := exists_lipschitzOn_inverse hf
  have := h.image_lipschitzOn hd hg
  rwa [hgs] at this

/-- If `f` is expanding up to a factor on `s` and `f '' s` is separable, then `s` is separable. -/
theorem isSeparable_of_antilipschitzOn {f : E → F} {s : Set E} {K : ℝ≥0}
    (hf : ∀ a ∈ s, ∀ b ∈ s, dist a b ≤ K * dist (f a) (f b)) (h : IsSeparable (f '' s)) :
    IsSeparable s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, -⟩
  · exact (countable_empty).isSeparable
  have : Nonempty E := ⟨a₀⟩
  obtain ⟨g, hg, hgs⟩ := exists_lipschitzOn_inverse hf
  have := h.separableSpace
  have hc : Continuous fun q : ↥(f '' s) => g q :=
    hg.continuousOn.comp_continuous continuous_subtype_val fun q => q.2
  have hr : range (fun q : ↥(f '' s) => g q) = g '' (f '' s) := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩; exact ⟨q.1, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨⟨q, hq⟩, rfl⟩
  rw [← hgs, ← hr]
  exact isSeparable_range hc

end Antilipschitz

section Positive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A set over a ball of an `n`-dimensional space is not `n`-null**: if the image of `S` under
`e ↦ p(e − x₀)`, `p` continuous linear onto a finite-dimensional `N`, contains a ball of `N`,
then the `dim N`-dimensional Hausdorff measure of `S` is not `0`.  (On `N` this Hausdorff measure
is a Haar measure, positive on balls, and `p` is Lipschitz.) -/
theorem not_hNull_of_ball_subset (N : Submodule ℝ E) [FiniteDimensional ℝ N] (p : E →L[ℝ] N)
    (x₀ : E) {S : Set E} {c : N} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ball c ρ ⊆ (fun e => p (e - x₀)) '' S) : ¬ HNull (finrank ℝ N : ℝ) S := by
  intro hS
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hf : LipschitzWith ‖p‖₊ fun e => p (e - x₀) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, coe_nnnorm]
      exact p.le_opNorm _
  have h1 := hf.hausdorffMeasure_image_le (d := (finrank ℝ N : ℝ)) (Nat.cast_nonneg _) S
  rw [hNull_iff.1 hS, mul_zero] at h1
  have h2 : μH[(finrank ℝ N : ℝ)] (ball c ρ) = 0 :=
    le_antisymm ((measure_mono h).trans h1) bot_le
  exact (Metric.isOpen_ball.measure_pos _ (nonempty_ball.2 hρ)).ne' h2

end Positive

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-! ### Definition 9.4.5 in M-polyfold charts -/

variable (P) in
/-- **Measure zero of dimension `n`** (Definition 9.4.5, 2021 p. 431, read in the M-polyfold
charts of the ambient space): for every chart `ψ` and every `D ⊆ C` in the domain of `ψ` whose
chart image is separable, the `n`-dimensional Hausdorff measure of `ψ(D)` in `E₀` is `0`. -/
def IsHNull (n : ℕ) (C : Set X) : Prop :=
  ∀ ψ : MChart X, P.IsChart ψ → ∀ D : Set X, D ⊆ C → D ⊆ ψ.source → IsSeparable (ψ '' D) →
    HNull (n : ℝ) (ψ '' D)

theorem IsHNull.mono {n : ℕ} {C C' : Set X} (h : P.IsHNull n C') (hC : C ⊆ C') :
    P.IsHNull n C := fun ψ hψ D hD hDψ hsep => h ψ hψ D (hD.trans hC) hDψ hsep

theorem isHNull_empty (n : ℕ) : P.IsHNull n ∅ := fun ψ _ D hD _ _ => by
  rw [subset_empty_iff.1 hD, image_empty]
  exact hNull_empty _

theorem isHNull_iUnion {ι : Type*} [Countable ι] {n : ℕ} {C : ι → Set X}
    (h : ∀ i, P.IsHNull n (C i)) : P.IsHNull n (⋃ i, C i) := fun ψ hψ D hD hDψ hsep => by
  have hD' : D = ⋃ i, D ∩ C i := by rw [← inter_iUnion]; exact (inter_eq_left.2 hD).symm
  rw [hD', image_iUnion]
  exact hNull_iUnion fun i => h i ψ hψ _ inter_subset_right (inter_subset_left.trans hDψ)
    (hsep.mono (image_mono inter_subset_left))

theorem IsHNull.union {n : ℕ} {C C' : Set X} (h : P.IsHNull n C) (h' : P.IsHNull n C') :
    P.IsHNull n (C ∪ C') := by
  rw [union_eq_iUnion]
  exact isHNull_iUnion fun b => by cases b <;> assumption

/-- **Measure zero is local**: a set that is `n`-null near each of its points is `n`-null.  (A
piece with separable chart image is covered by countably many of the neighbourhoods.) -/
theorem isHNull_of_local {n : ℕ} {C : Set X}
    (h : ∀ z ∈ C, ∃ V, IsOpen V ∧ z ∈ V ∧ P.IsHNull n (C ∩ V)) : P.IsHNull n C := by
  intro ψ hψ D hD hDψ hsep
  choose V hV hzV hnull using h
  set S' := ψ '' D with hS'
  have := hsep.separableSpace
  have : SecondCountableTopology S' := UniformSpace.secondCountable_of_separable S'
  have hsO : S' ⊆ ψ.model.O := by
    rintro _ ⟨k, hk, rfl⟩; exact ψ.mapsTo_model k (hDψ hk)
  have hcont : Continuous fun q : S' => ψ.symm q :=
    ψ.continuousOn_invFun.comp_continuous continuous_subtype_val fun q => hsO q.2
  let W : ↥D → Set S' := fun z => (fun q : S' => ψ.symm q) ⁻¹' V z.1 (hD z.2)
  have hW : ∀ z, IsOpen (W z) := fun z => (hV z.1 (hD z.2)).preimage hcont
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable W hW
  have : Countable ↥T := hT.to_subtype
  have hcover : S' ⊆ ⋃ z : ↥T, ψ '' (D ∩ V z.1.1 (hD z.1.2)) := by
    rintro _ ⟨w, hw, rfl⟩
    have hmem : (⟨ψ w, ⟨w, hw, rfl⟩⟩ : S') ∈ ⋃ z, W z := by
      refine mem_iUnion.2 ⟨⟨w, hw⟩, ?_⟩
      change ψ.symm (ψ w) ∈ V w (hD hw)
      rw [ψ.symm_apply_apply (hDψ hw)]
      exact hzV w (hD hw)
    rw [← hTU] at hmem
    obtain ⟨z, hzT, hz⟩ := mem_iUnion₂.1 hmem
    change ψ.symm (ψ w) ∈ V z.1 (hD z.2) at hz
    rw [ψ.symm_apply_apply (hDψ hw)] at hz
    exact mem_iUnion.2 ⟨⟨z, hzT⟩, w, ⟨hw, hz⟩, rfl⟩
  refine (hNull_iUnion fun z : ↥T => ?_).mono hcover
  exact hnull z.1.1 (hD z.1.2) ψ hψ _ (fun w hw => ⟨hD hw.1, hw.2⟩)
    (inter_subset_left.trans hDψ) (hsep.mono (image_mono inter_subset_left))

/-! ### The tangent projection near a point of a submanifold -/

/-- A continuous projection `p : E₀ → N` onto the chart image `N` of `T_xM`. -/
theorem exists_proj_chartTangent {ψ : MChart X} (hψ : P.IsChart ψ) {M : Set X}
    (hM : P.IsSmoothSubmanifold M) {x : X} (hx : x ∈ M) (hxψ : x ∈ ψ.source) :
    ∃ (N : Submodule ℝ (ψ.model.E 0)) (_ : FiniteDimensional ℝ N) (p : ψ.model.E 0 →L[ℝ] N),
      (N : Set (ψ.model.E 0)) = P.chartTangent hψ M x ∧ ∀ v : N, p v = v := by
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hψ hM hx hxψ
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional N
  exact ⟨N, hfin, p, hN, hp⟩

/-- **Chords of `M` near `x` are close to `T_xM`**: for a projection `p` onto the chart image `N`
of `T_xM` and `ε > 0`, `‖(ψa − ψb) − p(ψa − ψb)‖ ≤ ε ‖ψa − ψb‖` for `a`, `b ∈ M` near `x`
(`IsGraphChartAt.approx`, i.e. `ScRetraction.exists_approx`). -/
theorem exists_proj_approx {ψ : MChart X} (hψ : P.IsChart ψ) {M : Set X}
    (hM : P.IsSmoothSubmanifold M) {x : X} (hx : x ∈ M) (hxψ : x ∈ ψ.source)
    {N : Submodule ℝ (ψ.model.E 0)} (hN : (N : Set (ψ.model.E 0)) = P.chartTangent hψ M x)
    (p : ψ.model.E 0 →L[ℝ] N) (hp : ∀ v : N, p v = v) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ M ∩ ψ.source, ∀ b ∈ M ∩ ψ.source, ‖ψ a - ψ x‖ < δ → ‖ψ b - ψ x‖ < δ →
      ‖(ψ a - ψ b) - (p (ψ a - ψ b) : ψ.model.E 0)‖ ≤ ε * ‖ψ a - ψ b‖ := by
  set Q : ψ.model.E 0 →L[ℝ] ψ.model.E 0 := N.subtypeL.comp p with hQ
  have hpos : 0 < 1 + ‖Q‖ := by positivity
  obtain ⟨δ, hδ, happ⟩ := (isGraphChartAt_goodDirections hψ hM hx hxψ).approx (ε / (1 + ‖Q‖))
    (by positivity)
  refine ⟨δ, hδ, fun a ha b hb haδ hbδ => ?_⟩
  obtain ⟨v, hv, hest⟩ := happ a ha b hb haδ hbδ
  rw [← hN] at hv
  have hQv : Q v = v := by
    change ((p v : N) : ψ.model.E 0) = v
    exact congrArg Subtype.val (hp ⟨v, hv⟩)
  set dd := ψ a - ψ b with hdd
  have e1 : dd - (p dd : ψ.model.E 0) = (dd - v) - Q (dd - v) := by
    have e0 : Q (dd - v) = Q dd - v := by rw [map_sub, hQv]
    rw [e0]; change dd - Q dd = _; abel
  rw [e1]
  calc ‖(dd - v) - Q (dd - v)‖ ≤ ‖dd - v‖ + ‖Q (dd - v)‖ := norm_sub_le _ _
    _ ≤ ‖dd - v‖ + ‖Q‖ * ‖dd - v‖ := by gcongr; exact Q.le_opNorm _
    _ = (1 + ‖Q‖) * ‖dd - v‖ := by ring
    _ ≤ (1 + ‖Q‖) * (ε / (1 + ‖Q‖) * ‖dd‖) := by gcongr
    _ = ε * ‖dd‖ := by field_simp

/-- **The tangent projection is injective with Lipschitz inverse on `M` near `x`**:
`‖ψa − ψb‖ ≤ 2 ‖p(ψa) − p(ψb)‖` for `a`, `b ∈ M` with `‖ψa − ψx‖, ‖ψb − ψx‖ < δ`. -/
theorem exists_half_approx {ψ : MChart X} (hψ : P.IsChart ψ) {M : Set X}
    (hM : P.IsSmoothSubmanifold M) {x : X} (hx : x ∈ M) (hxψ : x ∈ ψ.source)
    {N : Submodule ℝ (ψ.model.E 0)} (hN : (N : Set (ψ.model.E 0)) = P.chartTangent hψ M x)
    (p : ψ.model.E 0 →L[ℝ] N) (hp : ∀ v : N, p v = v) :
    ∃ δ > 0, ∀ a ∈ M ∩ ψ.source, ∀ b ∈ M ∩ ψ.source, ‖ψ a - ψ x‖ < δ → ‖ψ b - ψ x‖ < δ →
      dist (ψ a) (ψ b) ≤ (2 : ℝ≥0) * dist (p (ψ a)) (p (ψ b)) := by
  obtain ⟨δ, hδ, happ⟩ := exists_proj_approx hψ hM hx hxψ hN p hp (ε := 1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun a ha b hb haδ hbδ => ?_⟩
  have h := happ a ha b hb haδ hbδ
  have h1 : ‖ψ a - ψ b‖ ≤ ‖(ψ a - ψ b) - (p (ψ a - ψ b) : ψ.model.E 0)‖ +
      ‖(p (ψ a - ψ b) : ψ.model.E 0)‖ := by
    simpa using norm_add_le ((ψ a - ψ b) - (p (ψ a - ψ b) : ψ.model.E 0)) (p (ψ a - ψ b))
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_ofNat]
  have h2 : ‖(p (ψ a - ψ b) : ψ.model.E 0)‖ = ‖p (ψ a - ψ b)‖ := rfl
  linarith

/-- The chart ball of radius `δ` of `M` around `x`. -/
def chartBall (ψ : MChart X) (M : Set X) (x : X) (δ : ℝ) : Set X :=
  {a | a ∈ M ∩ ψ.source ∧ ‖ψ a - ψ x‖ < δ}

omit [T2Space X] [ParacompactSpace X] in
theorem chartBall_subset (ψ : MChart X) (M : Set X) (x : X) (δ : ℝ) :
    chartBall ψ M x δ ⊆ M ∩ ψ.source := fun _ h => h.1

omit [T2Space X] [ParacompactSpace X] in
/-- The chart balls of `M` are relatively open: `chartBall ψ M x δ = M ∩ V` with `V` open. -/
theorem exists_isOpen_chartBall (ψ : MChart X) (M : Set X) (x : X) (δ : ℝ) :
    ∃ V, IsOpen V ∧ chartBall ψ M x δ = M ∩ V := by
  have hc : ContinuousOn (fun a => ‖ψ a - ψ x‖) ψ.source :=
    (ψ.continuousOn_toFun.sub continuousOn_const).norm
  obtain ⟨V, hV, hVe⟩ := (_root_.continuousOn_iff'.1 hc) (Iio δ) isOpen_Iio
  refine ⟨V ∩ ψ.source, hV.inter ψ.isOpen_source, ?_⟩
  ext a
  constructor
  · rintro ⟨⟨haM, haψ⟩, had⟩
    have : a ∈ (fun a => ‖ψ a - ψ x‖) ⁻¹' Iio δ ∩ ψ.source := ⟨had, haψ⟩
    rw [hVe] at this
    exact ⟨haM, this.1, haψ⟩
  · rintro ⟨haM, haV, haψ⟩
    have : a ∈ V ∩ ψ.source := ⟨haV, haψ⟩
    rw [← hVe] at this
    exact ⟨⟨haM, haψ⟩, this.1⟩

/-- **The sheets are locally separable in every chart**: the chart image of a small chart ball of
`M` is separable (it is bi-Lipschitz to a subset of the finite-dimensional `T_xM`). -/
theorem isSeparable_chart_ball {ψ : MChart X} (hψ : P.IsChart ψ) {M : Set X}
    (hM : P.IsSmoothSubmanifold M) {x : X} (hx : x ∈ M) (hxψ : x ∈ ψ.source) :
    ∃ δ > 0, IsSeparable (ψ '' chartBall ψ M x δ) := by
  obtain ⟨N, hfin, p, hN, hp⟩ := exists_proj_chartTangent hψ hM hx hxψ
  obtain ⟨δ, hδ, hhalf⟩ := exists_half_approx hψ hM hx hxψ hN p hp
  refine ⟨δ, hδ, isSeparable_of_antilipschitzOn (f := fun e => p e) (K := 2) ?_
    (IsSeparable.of_separableSpace _)⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact hhalf a ha.1 b hb.1 ha.2 hb.2

/-! ### A sheet is not null in itself -/

/-- **An `n`-dimensional submanifold is not `n`-null** (the field `not_isNull_self` of
`SheetNullSets`): if `M` has dimension `n` at `x`, then `M` does not have `n`-dimensional measure
zero.  In a chart at `x` the tangent projection of a small chart ball of `M` contains a ball of
`T_xM` around `t h₁`, `h₁` an admissible direction (2021 Lemmas 9.2.9–9.2.11, uniformly in the
direction: `exists_small_cone`, `exists_graph_unif_chart`). -/
theorem not_isHNull_of_hasDimAt {M : Set X} (hM : P.IsSmoothSubmanifold M) {x : X} {n : ℕ}
    (hx : P.HasDimAt M x n) : ¬ P.IsHNull n M := by
  intro hnull
  have hxM : x ∈ M := hx.1
  obtain ⟨ψ, hψ, hxψ⟩ := P.exists_isChart_mem_source x
  obtain ⟨N, hfin, p, hN, hp⟩ := exists_proj_chartTangent hψ hM hxM hxψ
  have hn : finrank ℝ N = n := finrank_chartTangent hψ hx hM hxψ hN
  obtain ⟨δ, hδ, hhalf⟩ := exists_half_approx hψ hM hxM hxψ hN p hp
  have hsep : IsSeparable (ψ '' chartBall ψ M x δ) := by
    refine isSeparable_of_antilipschitzOn (f := fun e => p e) (K := 2) ?_
      (IsSeparable.of_separableSpace _)
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hhalf a ha.1 b hb.1 ha.2 hb.2
  have h0 := hnull ψ hψ _ ((chartBall_subset ψ M x δ).trans inter_subset_left)
    ((chartBall_subset ψ M x δ).trans inter_subset_right) hsep
  -- the admissible direction and the graph over a ball around it
  set Q : ψ.model.E 0 →L[ℝ] ψ.model.E 0 := N.subtypeL.comp p with hQ
  have hQT : ∀ v, Q v ∈ P.chartTangent hψ M x := fun v => by
    rw [← hN]; exact (p v).2
  have hQid : ∀ v ∈ P.chartTangent hψ M x, Q v = v := fun v hv => by
    rw [← hN] at hv
    exact congrArg Subtype.val (hp ⟨v, hv⟩)
  obtain ⟨h₁, hh₁, r, hr, s, hs, hsmall, hcone⟩ := exists_small_cone hψ hM hxM hxψ
  obtain ⟨t₀, ht₀, hgr⟩ := exists_graph_unif_chart hψ hM hxM hxψ Q hQT hQid
    (r := r / 2) (s := s) (by positivity) hs (ε := 1) one_pos
  set t : ℝ := min t₀ (δ / 2) / 2 with ht
  have htpos : 0 < t := by positivity
  have htt₀ : t < t₀ := by
    have := min_le_left t₀ (δ / 2); rw [ht]; linarith [lt_min ht₀ (by positivity : 0 < δ / 2)]
  have htδ : 2 * t < δ := by
    have := min_le_right t₀ (δ / 2); rw [ht]; linarith [lt_min ht₀ (by positivity : 0 < δ / 2)]
  rw [← hN] at hh₁
  refine not_hNull_of_ball_subset N p (ψ x) (c := t • (⟨h₁, hh₁⟩ : N)) (ρ := t * (r / 2))
    (by positivity) ?_ (hn ▸ h0)
  intro u hu
  rw [mem_ball, dist_eq_norm] at hu
  -- the direction `h = t⁻¹ u`
  set h : ψ.model.E 0 := t⁻¹ • (u : ψ.model.E 0) with hh
  have hhN : h ∈ P.chartTangent hψ M x := by
    rw [← hN]; exact N.smul_mem _ u.2
  have hth : t • h = u := by rw [hh, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
  have hd : ‖h - h₁‖ < r / 2 := by
    have e : h - h₁ = t⁻¹ • ((u : ψ.model.E 0) - t • h₁) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
    have hu' : ‖(u : ψ.model.E 0) - t • h₁‖ < t * (r / 2) := hu
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 htpos.le), inv_mul_lt_iff₀ htpos]
    exact hu'
  have hh1 : ‖h‖ ≤ 1 := by
    calc ‖h‖ = ‖(h - h₁) + h₁‖ := by rw [sub_add_cancel]
      _ ≤ ‖h - h₁‖ + ‖h₁‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  have hcone' : ∀ h' ∈ P.chartTangent hψ M x, ‖h' - h‖ ≤ r / 2 → ψ x + s • h' ∈ ψ.model.C :=
    fun h' hh' hd' => hcone h' hh' (by
      calc ‖h' - h₁‖ = ‖(h' - h) + (h - h₁)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖h' - h‖ + ‖h - h₁‖ := norm_add_le _ _
        _ ≤ r := by linarith)
  obtain ⟨a, ha, hQa, hest⟩ := hgr h hhN hh1 hcone' t htpos htt₀
  rw [hth] at hQa hest
  refine ⟨ψ a, ⟨a, ⟨ha, ?_⟩, rfl⟩, Subtype.ext hQa⟩
  have hunorm : ‖(u : ψ.model.E 0)‖ ≤ t := by
    rw [← hth, norm_smul, Real.norm_of_nonneg htpos.le]
    nlinarith
  calc ‖ψ a - ψ x‖ = ‖((ψ a - ψ x) - u) + u‖ := by rw [sub_add_cancel]
    _ ≤ ‖(ψ a - ψ x) - u‖ + ‖(u : ψ.model.E 0)‖ := norm_add_le _ _
    _ ≤ 1 * t + t := by linarith
    _ < δ := by linarith

/-! ### The null sets of the `n`-dimensional sheets -/

variable (P) in
/-- **The sets of measure zero in the `n`-dimensional submanifolds of an M-polyfold**
(Definition 9.4.5, used in Definition 9.5.1): `A` has measure zero in the sheet `N` if `A ∩ N`
has `n`-dimensional measure zero (`IsHNull`).  A `SheetNullSets` with no hypothesis: σ-ideal,
local, the same on the overlap of two sheets, and a nonempty sheet is not null in itself
(`not_isHNull_of_hasDimAt`). -/
def sheetNullSets (n : ℕ) : SheetNullSets {N : Set X | P.IsSubmanifoldOfDim N n} where
  IsNull N A := P.IsHNull n (A ∩ N)
  isNull_empty N := by rw [empty_inter]; exact isHNull_empty n
  isNull_mono h hA := h.mono (inter_subset_inter_left _ hA)
  isNull_iUnion h := by rw [iUnion_inter]; exact isHNull_iUnion h
  isNull_of_local N _ A h := isHNull_of_local fun z hz => by
    obtain ⟨V, hV, hzV, hn⟩ := h z hz.1
    exact ⟨V, hV, hzV, hn.mono fun w hw => ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩⟩
  isNull_transfer N _ N' _ C hC h := by
    have e : C ∩ N' = C ∩ N := by
      rw [inter_eq_left.2 fun w hw => (hC hw).2, inter_eq_left.2 fun w hw => (hC hw).1]
    rw [e]; exact h
  not_isNull_self N hN hne h := by
    obtain ⟨x, hx⟩ := hne
    rw [inter_self] at h
    exact not_isHNull_of_hasDimAt hN.1 (hN.2 x hx) h

theorem sheetNullSets_isNull_iff {n : ℕ} {N A : Set X} :
    (P.sheetNullSets n).IsNull N A ↔ P.IsHNull n (A ∩ N) := Iff.rfl

end MPolyfold

end Polyfold
