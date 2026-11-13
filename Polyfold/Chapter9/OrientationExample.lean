import Polyfold.Chapter9.OrientationBasic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations": **Example 9.3.5** (2021 p. 425; 2017: Example 9.1).
Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# Orientations of graphs in `ℝ²`, and Example 9.3.5

## The text, paraphrased

Take a smooth `β⁺⁺ ≥ 0`, positive off `0`, flat at `0`; `β⁻⁻ = -β⁺⁺`; `β⁺⁻ = β⁺⁺` on `s ≤ 0`,
`= β⁻⁻` on `s > 0`, and `β⁻⁺` similarly, with graphs `G^{±±}`.  The numbers of points of
`{G⁺⁺, G⁻⁻}` and of `{G⁺⁻, G⁻⁺}` over each point of `ℝ²` agree; this defines `Θ`.  Orienting
`G⁺⁺`, `G⁺⁻` by `(1, 0)` and `G⁻⁻`, `G⁻⁺` by `(-1, 0)` at `(0, 0)` gives two orientations, which
coincide at `(0, 0)` but are otherwise different; there are four possibilities to orient; and
the second structure cannot necessarily be oriented to coincide with the first.

## What is formalized

* Oriented lines and graphs: `lineFrames`, `isChartOrientation_lineFrames`,
  `chartVec_image_graph2` (the chart image of `T_z graph(β)` is `ℝ (1, β'(z₀))`),
  `graphOrientation hβ ε` (the orientation `ε (1, β')`), `graphOrientation_tangent_eq`/`_ne`.
* The example: `betaPP` (`e(s) + e(-s)`, `e = expNegInvGlue`), `betaMM`, `betaPM`, `betaMP`;
  `example_9_3_5_count`, `example935Theta`, `example935Theta_isBranched`; the orientations
  `exampleT1`, `exampleT2` (`orientedLift1/2_isOrientation`, given independence); the frames at
  the origin `example_9_3_5_frames_origin`; and the bundle `example_9_3_5`: they coincide at
  `(0, 0)` (`example_9_3_5_eq_origin`), differ at `(s, β⁺⁺(s))`, `s > 0`
  (`example_9_3_5_ne_of_pos`), and no signs for the second structure reproduce `T̂¹` near
  `(0, 0)` (`example_9_3_5_cannot_coincide`).

## Statements that do not hold as we read them

* "otherwise different": `example_9_3_5_eq_of_neg` (they also coincide wherever `x < 0`, where
  `G⁺⁻ = G⁺⁺` and `G⁻⁺ = G⁻⁻` with the same orientations).
* "four different possibilities": the four sign choices of the first structure are different
  (`orientedLift1_injective`) and `T̂²` is none of them (`exampleT2_ne_orientedLift1`); with
  fractional weights there are infinitely many (as in Remark 9.3.3).

## Not formalized, and why

* A classification of all orientations of `Θ` is not in this file; since 2026-11-12 it is
  `example_9_3_5_classification` (`GapP2_D2Example935Class.lean`: a three-parameter rational
  family, infinitely many, the six sign orientations being the integral ones).  The last claim
  is proved for the orientations `± (1, β')` of the second structure.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X} (hφ : P.IsChart φ)

/-- **Orientations of a line**: in dimension `1`, the positive frames for the orientation of a
basis `b₀` are the positive multiples of `b₀`. -/
theorem chartFrames_orientation_fin_one (L : Set P.TangentSpace) (N : Submodule ℝ (φ.model.E 0))
    (b₀ : Basis (Fin 1) ℝ N) :
    chartFrames hφ L N b₀.orientation =
      {a | a 0 ∈ L ∧ ∃ c : ℝ, 0 < c ∧ chartVec hφ (a 0) = c • (b₀ 0 : φ.model.E 0)} := by
  ext a
  constructor
  · rintro ⟨ha, b, hb, hbo⟩
    refine ⟨ha 0, b₀.repr (b 0) 0, ?_, ?_⟩
    · have := (b₀.orientation_eq_iff_det_pos b).1 hbo.symm
      rwa [Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply] at this
    · rw [← hb 0]
      conv_lhs => rw [← b₀.sum_repr (b 0)]
      simp
  · rintro ⟨ha, c, hc, hca⟩
    refine ⟨fun i => by rw [Subsingleton.elim i 0]; exact ha,
      b₀.unitsSMul fun _ => Units.mk0 c hc.ne', fun i => ?_, ?_⟩
    · rw [Subsingleton.elim i 0, Basis.unitsSMul_apply, hca]
      simp [Units.smul_def]
    · rw [Basis.orientation_unitsSMul]
      apply Module.Ray.units_smul_of_pos
      simp [hc]

/-- The frames of a line `L` positive for `ε w`: those whose chart vector is `c ε w`, `c > 0`. -/
def lineFrames (L : Set P.TangentSpace) (w : φ.model.E 0) (ε : ℝ) :
    Set (Fin 1 → P.TangentSpace) :=
  {a | a 0 ∈ L ∧ ∃ c : ℝ, 0 < c ∧ chartVec hφ (a 0) = (c * ε) • w}

/-- **The orientation `ε w` of a line**: if the chart image of `L` is the line `ℝ w`, `w ≠ 0`,
the frames positive for `ε w` (`ε ≠ 0`) orient `L` in the chart `φ`. -/
theorem isChartOrientation_lineFrames {L : Set P.TangentSpace} {w : φ.model.E 0} (hw : w ≠ 0)
    {ε : ℝ} (hε : ε ≠ 0) (hL : chartVec hφ '' L = (span ℝ {w} : Set (φ.model.E 0))) :
    IsChartOrientation hφ ⟨1, L, lineFrames hφ L w ε⟩ := by
  have hli : LinearIndependent ℝ (fun _ : Fin 1 => ε • w) :=
    linearIndependent_unique_iff.2 (smul_ne_zero hε hw)
  refine ⟨span ℝ (range fun _ : Fin 1 => ε • w), ?_,
    FiniteDimensional.span_of_finite ℝ (finite_range _), ?_, (Basis.span hli).orientation, ?_⟩
  · rw [range_const, span_singleton_smul_eq (Ne.isUnit hε)]
    exact hL.symm
  · change finrank ℝ (span ℝ (range fun _ : Fin 1 => ε • w)) = 1
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  · change lineFrames hφ L w ε = chartFrames hφ L _ _
    rw [chartFrames_orientation_fin_one]
    ext a
    simp only [lineFrames, mem_ofPred_eq, Basis.span_apply, smul_smul]

end MPolyfold

/-! ### Graphs in `ℝ²` and their orientations -/

section Graph

open MPolyfold

/-- The chart `rnChart 2 0` of `ℝ²` (the identity). -/
abbrev idChart2 : (rnPolyfold 2).IsChart (rnChart 2 0) := isChart_rnChart 0

/-- The direction `(1, β'(s))` of the graph of `β` over `s = z₀`. -/
def graphDirR (β : ℝ → ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ := ![1, deriv β (z 0)]

/-- `(1, β'(z₀))` as a vector of the chart model `E₀ = ℝ²` of `rnChart 2 0`. -/
def graphDir (β : ℝ → ℝ) (z : Fin 2 → ℝ) : (rnChart 2 0).model.E 0 := graphDirR β z

theorem graphDir_ne_zero (β : ℝ → ℝ) (z : Fin 2 → ℝ) : graphDir β z ≠ 0 := by
  intro h
  have h' : graphDirR β z = 0 := h
  have := congrFun h' 0
  simp [graphDirR] at this

/-- **The tangent line of a graph**: for `z` on the graph of a `C^∞` function `β`, the chart
vectors of `T_z(graph β)` (in the chart `id` of `ℝ²`) form the line spanned by `(1, β'(z₀))`
(Remark 4.14 with the retraction `(s, t) ↦ (s, β(s))`). -/
theorem chartVec_image_graph2' {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {z : Fin 2 → ℝ}
    (hz : z ∈ graph2 β) :
    chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent (graph2 β) z =
      (span ℝ {graphDirR β z} : Set (Fin 2 → ℝ)) := by
  have hφ := idChart2
  have hs := contDiff_graphRetraction hβ
  let d : (rnPolyfold 2).SubmanifoldData (graph2 β) :=
    ⟨univ, graphRetraction β, isOpen_univ,
      rnPolyfold_isScPlusRetractionOn_univ hs (graphRetraction_idem β),
      by rw [image_univ, range_graphRetraction, inter_univ]⟩
  rw [chartVec_image_submanifoldTangent hφ d hz (mem_univ z) (mem_univ z)]
  have hU := rn_relOpen_univ 2
  let R : ScRetraction (rnSc 2) univ := ⟨univ, graphRetraction β, hU, mapsTo_univ _ _,
    IsScSmooth.of_contDiffOn_finiteDimensional hU.isScDomain hs.contDiffOn,
    fun r _ => graphRetraction_idem β r⟩
  have hR : R.retract = graph2 β := by
    change graphRetraction β '' univ = _
    rw [image_univ, range_graphRetraction]
  have hshrink : d.toSubData.shrink (rnChart 2 0) = univ :=
    eq_univ_of_forall fun r => ⟨⟨mem_univ _, mem_univ _⟩, mem_univ _, mem_univ _⟩
  have hset : (rnChart 2 0) '' (d.toSubData.shrink (rnChart 2 0) ∩ graph2 β) = R.retract := by
    rw [hshrink, univ_inter, hR]
    exact (image_congr fun r _ => by rw [rnChart_apply, sub_zero]; rfl).trans (image_id _)
  have hz1 : z ∈ (rnPolyfold 2).levelSet 1 := by rw [rnPolyfold_levelSet]; exact mem_univ z
  have hl : (rnChart 2 0).model.E.toBase 1 (levelLift (rnChart 2 0) 1 z) = rnChart 2 0 z :=
    (rnPolyfold 2).toBase_levelLift hφ (mem_univ z) hz1
  have hl' : levelLift (rnChart 2 0) 1 z = (show (rnChart 2 0).model.E 1 from z) := by
    rw [rnChart_apply, sub_zero] at hl
    exact (ScBanach.const_toBase (Fin 2 → ℝ) 1 _).symm.trans hl
  have hzR : (z : (rnSc 2) 1) ∈ (rnSc 2).lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase, hR]; exact hz
  have hd : HasFDerivWithinAt (graphRetraction β)
      (scDeriv (E := rnSc 2) (F := rnSc 2) univ (graphRetraction β) z) univ z :=
    hasFDerivWithinAt_scDeriv_const' (V := Fin 2 → ℝ) (F := rnSc 2) (U := univ)
      (f := graphRetraction β) R.isSc1 (mem_univ z)
  have hfd : fderiv ℝ (graphRetraction β) z =
      scDeriv (E := rnSc 2) (F := rnSc 2) univ (graphRetraction β) z :=
    (hasFDerivWithinAt_univ.1 hd).fderiv
  have hrange : LinearMap.range ((fderiv ℝ (graphRetraction β) z : (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) :
      (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) = span ℝ {graphDirR β z} := by
    rw [(hasFDerivAt_graphRetraction hβ z).fderiv]
    ext v
    rw [LinearMap.mem_range, mem_span_singleton]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w 0, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨fun _ => c, rfl⟩
  rw [hl']
  erw [hset, tangentSpace_eq_range R hzR, ← hfd]
  rw [← hrange]
  rfl

/-- The chart image of `T_z(graph β)` in the chart model: the line `ℝ (1, β'(z₀))`. -/
theorem chartVec_image_graph2 {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {z : Fin 2 → ℝ}
    (hz : z ∈ graph2 β) :
    chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent (graph2 β) z =
      (span ℝ {graphDir β z} : Set ((rnChart 2 0).model.E 0)) := by
  rw [chartVec_image_graph2' hβ hz, span_singleton_eq_range, span_singleton_eq_range]
  rfl

/-- The frames of `T_z(graph β)` positive for the orientation `ε · (1, β'(z₀))`: those whose
chart vector is `c ε (1, β'(z₀))`, `c > 0`. -/
def graphFrames (β : ℝ → ℝ) (ε : ℝ) (z : Fin 2 → ℝ) :
    Set (Fin 1 → (rnPolyfold 2).TangentSpace) :=
  lineFrames idChart2 ((rnPolyfold 2).submanifoldTangent (graph2 β) z) (graphDir β z) ε

theorem isOrientedAt_graphFrames {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {ε : ℝ} (hε : ε ≠ 0)
    {z : Fin 2 → ℝ} (hz : z ∈ graph2 β) :
    (rnPolyfold 2).IsOrientedAt z
      ⟨1, (rnPolyfold 2).submanifoldTangent (graph2 β) z, graphFrames β ε z⟩ :=
  ⟨fun _ hα => hα.1, rnChart 2 0, idChart2, mem_univ z,
    isChartOrientation_lineFrames idChart2 (graphDir_ne_zero β z) hε (chartVec_image_graph2 hβ hz)⟩

/-- `z ↦ (1, β'(z₀))` is continuous (into the chart model). -/
theorem continuous_graphDir {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    Continuous (graphDir β) := by
  have h : Continuous (graphDirR β) := by
    refine continuous_pi fun j => ?_
    fin_cases j
    · simpa [graphDirR] using continuous_const
    · change Continuous fun a : Fin 2 → ℝ => deriv β (a 0)
      exact (hβ.continuous_deriv (by simp)).comp (continuous_apply 0)
  exact h

/-- **The orientation `ε · (1, β'(s))` of the graph of `β`** (`ε ≠ 0`), continuous since `β'` is. -/
def graphOrientation {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (ε : ℝ) (hε : ε ≠ 0) :
    (rnPolyfold 2).SubmanifoldOrientation (graph2 β) 1 where
  frames := graphFrames β ε
  isOrientedAt _ hz := isOrientedAt_graphFrames hβ hε hz
  continuous _ z hz := by
    have hlift : ∀ z' ∈ graph2 β, ∃ α ∈ (rnPolyfold 2).submanifoldTangent (graph2 β) z',
        chartVec idChart2 α = ε • graphDir β z' := fun z' hz' => by
      have : ε • graphDir β z' ∈ chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent
          (graph2 β) z' := by
        rw [chartVec_image_graph2 hβ hz']
        exact smul_mem _ _ (mem_span_singleton_self _)
      exact this
    obtain ⟨α₀, -, -⟩ := hlift z hz
    have : Nonempty (rnPolyfold 2).TangentSpace := ⟨α₀⟩
    choose! e he1 he2 using hlift
    refine ⟨rnChart 2 0, idChart2, univ, isOpen_univ, mem_univ z, subset_univ _,
      fun z' _ => e z', fun z' hz' => ⟨he1 z' hz'.1, 1, one_pos, by rw [he2 z' hz'.1, one_mul]⟩,
      ?_⟩
    have hc : Continuous fun z' : Fin 2 → ℝ => fun _ : Fin 1 => ε • graphDir β z' :=
      continuous_pi fun _ => (continuous_graphDir hβ).const_smul ε
    exact hc.continuousOn.congr fun z' hz' => funext fun _ => he2 z' hz'.1

theorem graphOrientation_tangent {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (ε : ℝ) (hε : ε ≠ 0)
    (z : Fin 2 → ℝ) : (graphOrientation hβ ε hε).tangent z =
      ⟨1, (rnPolyfold 2).submanifoldTangent (graph2 β) z, graphFrames β ε z⟩ := rfl

/-- At a common point of two graphs with the same slope, the tangent sets agree. -/
theorem submanifoldTangent_graph2_eq {β β' : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ' : ContDiff ℝ ∞ β') {z : Fin 2 → ℝ} (hz : z ∈ graph2 β) (hz' : z ∈ graph2 β')
    (hd : deriv β (z 0) = deriv β' (z 0)) :
    (rnPolyfold 2).submanifoldTangent (graph2 β) z =
      (rnPolyfold 2).submanifoldTangent (graph2 β') z := by
  refine ((chartVec_injOn idChart2 (mem_univ z)).image_eq_image_iff (fun α hα => hα.1)
    (fun α hα => hα.1)).1 ?_
  rw [chartVec_image_graph2 hβ hz, chartVec_image_graph2 hβ' hz', graphDir, graphDir,
    graphDirR, graphDirR, hd]

/-- **Equal oriented tangents** of two graphs through `z` with the same slope and the same sign. -/
theorem graphOrientation_tangent_eq {β β' : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ' : ContDiff ℝ ∞ β') {ε : ℝ} (hε : ε ≠ 0) {z : Fin 2 → ℝ} (hz : z ∈ graph2 β)
    (hz' : z ∈ graph2 β') (hd : deriv β (z 0) = deriv β' (z 0)) :
    (graphOrientation hβ ε hε).tangent z = (graphOrientation hβ' ε hε).tangent z := by
  rw [graphOrientation_tangent, graphOrientation_tangent]
  have hT := submanifoldTangent_graph2_eq hβ hβ' hz hz' hd
  simp only [graphFrames, graphDir, graphDirR, hT, hd]

/-- **Opposite orientations differ**: `(T_z graph β, +) ≠ (T_z graph β, -)`. -/
theorem graphOrientation_tangent_ne {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {z : Fin 2 → ℝ}
    (hz : z ∈ graph2 β) :
    (graphOrientation hβ 1 one_ne_zero).tangent z ≠
      (graphOrientation hβ (-1) (neg_ne_zero.2 one_ne_zero)).tangent z := by
  rw [graphOrientation_tangent, graphOrientation_tangent]
  intro h
  simp only [MPolyfold.OrTangent.mk.injEq, heq_eq_eq, true_and] at h
  have hmem : graphDir β z ∈ chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent
      (graph2 β) z := by
    rw [chartVec_image_graph2 hβ hz]
    exact mem_span_singleton_self _
  obtain ⟨α, hα, hαv⟩ := hmem
  have h1 : (fun _ : Fin 1 => α) ∈ graphFrames β 1 z := ⟨hα, 1, one_pos, by rw [hαv, one_mul,
    one_smul]⟩
  rw [h] at h1
  obtain ⟨-, c, hc, hcv⟩ := h1
  rw [hαv] at hcv
  have h2 : (1 + c) • graphDir β z = 0 := by
    rw [add_smul, one_smul]
    nth_rewrite 1 [hcv]
    rw [mul_neg_one, neg_smul, neg_add_cancel]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · linarith
  · exact graphDir_ne_zero β z h3

end Graph

/-! ### Example 9.3.5 -/

section Example935

open MPolyfold EpGroupoid

/-- `β⁺⁺(s) = e(s) + e(-s)`, `e = expNegInvGlue`: smooth, positive for `s ≠ 0`, `β⁺⁺(0) = 0`. -/
def betaPP (s : ℝ) : ℝ := expNegInvGlue s + expNegInvGlue (-s)

/-- `β⁻⁻ = -β⁺⁺`. -/
def betaMM (s : ℝ) : ℝ := -betaPP s

/-- `β⁺⁻(s) = e(-s) - e(s)`: `β⁺⁺` for `s ≤ 0`, `β⁻⁻` for `s > 0`. -/
def betaPM (s : ℝ) : ℝ := expNegInvGlue (-s) - expNegInvGlue s

/-- `β⁻⁺ = -β⁺⁻`: `β⁻⁻` for `s ≤ 0`, `β⁺⁺` for `s > 0`. -/
def betaMP (s : ℝ) : ℝ := -betaPM s

theorem contDiff_expNegInvGlue_neg : ContDiff ℝ ∞ fun s : ℝ => expNegInvGlue (-s) :=
  expNegInvGlue.contDiff.comp contDiff_neg

theorem contDiff_betaPP : ContDiff ℝ ∞ betaPP :=
  expNegInvGlue.contDiff.add contDiff_expNegInvGlue_neg

theorem contDiff_betaMM : ContDiff ℝ ∞ betaMM := contDiff_betaPP.neg

theorem contDiff_betaPM : ContDiff ℝ ∞ betaPM :=
  contDiff_expNegInvGlue_neg.sub expNegInvGlue.contDiff

theorem contDiff_betaMP : ContDiff ℝ ∞ betaMP := contDiff_betaPM.neg

theorem betaPP_pos {s : ℝ} (hs : s ≠ 0) : 0 < betaPP s := by
  rcases lt_or_gt_of_ne hs with h | h
  · exact add_pos_of_nonneg_of_pos (expNegInvGlue.nonneg s)
      (expNegInvGlue.pos_of_pos (neg_pos.2 h))
  · exact add_pos_of_pos_of_nonneg (expNegInvGlue.pos_of_pos h) (expNegInvGlue.nonneg _)

theorem betaPP_zero : betaPP 0 = 0 := by simp [betaPP]

theorem betaPM_of_nonpos {s : ℝ} (hs : s ≤ 0) : betaPM s = betaPP s := by
  simp [betaPM, betaPP, expNegInvGlue.zero_of_nonpos hs]

theorem betaPM_of_pos {s : ℝ} (hs : 0 < s) : betaPM s = betaMM s := by
  simp [betaPM, betaMM, betaPP, expNegInvGlue.zero_of_nonpos (neg_nonpos.2 hs.le)]

theorem betaMP_of_nonpos {s : ℝ} (hs : s ≤ 0) : betaMP s = betaMM s := by
  rw [betaMP, betaMM, betaPM_of_nonpos hs]

theorem betaMP_of_pos {s : ℝ} (hs : 0 < s) : betaMP s = betaPP s := by
  rw [betaMP, betaPM_of_pos hs, betaMM, neg_neg]

theorem deriv_expNegInvGlue_zero : deriv expNegInvGlue 0 = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun x => by
    rw [expNegInvGlue.zero]; exact expNegInvGlue.nonneg x)

theorem deriv_betaPP_zero : deriv betaPP 0 = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun x => by
    rw [betaPP_zero]; exact add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _))

theorem deriv_betaMM_zero : deriv betaMM 0 = 0 := by
  change deriv (-betaPP) 0 = 0
  rw [deriv.neg, deriv_betaPP_zero, neg_zero]

theorem deriv_betaPM_zero : deriv betaPM 0 = 0 := by
  have h1 : DifferentiableAt ℝ (fun s : ℝ => expNegInvGlue (-s)) 0 :=
    (contDiff_expNegInvGlue_neg.differentiable (by simp)).differentiableAt
  have h2 : DifferentiableAt ℝ expNegInvGlue 0 :=
    (expNegInvGlue.contDiff (n := ⊤).differentiable (by simp)).differentiableAt
  change deriv ((fun s => expNegInvGlue (-s)) - expNegInvGlue) 0 = 0
  rw [deriv_sub h1 h2, deriv_comp_neg, neg_zero, deriv_expNegInvGlue_zero, neg_zero, sub_zero]

theorem deriv_betaMP_zero : deriv betaMP 0 = 0 := by
  change deriv (-betaPM) 0 = 0
  rw [deriv.neg, deriv_betaPM_zero, neg_zero]

/-- The graphs `G⁺⁺` (`true`) and `G⁻⁻` (`false`): the first local branching structure. -/
def beta1 (b : Bool) : ℝ → ℝ := cond b betaPP betaMM

/-- The graphs `G⁺⁻` (`true`) and `G⁻⁺` (`false`): the second local branching structure. -/
def beta2 (b : Bool) : ℝ → ℝ := cond b betaPM betaMP

theorem contDiff_beta1 : ∀ b, ContDiff ℝ ∞ (beta1 b)
  | true => contDiff_betaPP
  | false => contDiff_betaMM

theorem contDiff_beta2 : ∀ b, ContDiff ℝ ∞ (beta2 b)
  | true => contDiff_betaPM
  | false => contDiff_betaMP

/-- The sign `+1` (`true`) or `-1` (`false`). -/
def boolSign (b : Bool) : ℝ := cond b 1 (-1)

theorem boolSign_ne_zero : ∀ b, boolSign b ≠ 0
  | true => one_ne_zero
  | false => neg_ne_zero.2 one_ne_zero

open scoped Classical in
/-- **The functor `Θ` of Example 9.3.5**: `Θ(x, y) = |{i ∈ {++, --} | (x, y) ∈ Gᵢ}|`. -/
def example935Theta : (Fin 2 → ℝ) → ℚ := fun y => ∑ b with y ∈ graph2 (beta1 b), (1 : ℚ)

open scoped Classical in
/-- **The count identity of Example 9.3.5**: `|{i ∈ {++, --} | (x, y) ∈ Gᵢ}| =
|{j ∈ {+-, -+} | (x, y) ∈ Gⱼ}|` for all `(x, y) ∈ ℝ²`. -/
theorem example_9_3_5_count (y : Fin 2 → ℝ) :
    (∑ b with y ∈ graph2 (beta1 b), (1 : ℚ)) = ∑ b with y ∈ graph2 (beta2 b), (1 : ℚ) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_bool, Fintype.sum_bool]
  by_cases hs : y 0 ≤ 0
  · have h1 : y ∈ graph2 (beta2 true) ↔ y ∈ graph2 (beta1 true) := by
      change y 1 = betaPM (y 0) ↔ y 1 = betaPP (y 0)
      rw [betaPM_of_nonpos hs]
    have h2 : y ∈ graph2 (beta2 false) ↔ y ∈ graph2 (beta1 false) := by
      change y 1 = betaMP (y 0) ↔ y 1 = betaMM (y 0)
      rw [betaMP_of_nonpos hs]
    by_cases ha : y ∈ graph2 (beta1 true) <;> by_cases hb : y ∈ graph2 (beta1 false) <;>
      simp [ha, hb, h1, h2]
  · have hs' : 0 < y 0 := lt_of_not_ge hs
    have h1 : y ∈ graph2 (beta2 true) ↔ y ∈ graph2 (beta1 false) := by
      change y 1 = betaPM (y 0) ↔ y 1 = betaMM (y 0)
      rw [betaPM_of_pos hs']
    have h2 : y ∈ graph2 (beta2 false) ↔ y ∈ graph2 (beta1 true) := by
      change y 1 = betaMP (y 0) ↔ y 1 = betaPP (y 0)
      rw [betaMP_of_pos hs']
    by_cases ha : y ∈ graph2 (beta1 true) <;> by_cases hb : y ∈ graph2 (beta1 false) <;>
      simp [ha, hb, h1, h2]

open scoped Classical in
/-- `Θ` is also `|{j ∈ {+-, -+} | (x, y) ∈ Gⱼ}|`. -/
theorem example935Theta_eq_two :
    example935Theta = fun y => ∑ b with y ∈ graph2 (beta2 b), (1 : ℚ) :=
  funext example_9_3_5_count

/-- **`Θ` is a branched ep⁺-subgroupoid** of the trivial ep-groupoid of `ℝ²`, of dimension `1`. -/
theorem example935Theta_isBranched :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid example935Theta :=
  isBranchedEpSubgroupoid_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => (rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b)).1)
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous)

theorem example935Theta_isNDimensional :
    (trivial (rnPolyfold 2)).IsNDimensional example935Theta 1 :=
  isNDimensional_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous)

/-- The orientations `ε(b) · (1, β'(s))` of the graphs of the first structure. -/
def orient1 (ε : Bool → Bool) (b : Bool) :
    (rnPolyfold 2).SubmanifoldOrientation (graph2 (beta1 b)) 1 :=
  graphOrientation (contDiff_beta1 b) (boolSign (ε b)) (boolSign_ne_zero _)

/-- The orientations `ε(b) · (1, β'(s))` of the graphs of the second structure. -/
def orient2 (ε : Bool → Bool) (b : Bool) :
    (rnPolyfold 2).SubmanifoldOrientation (graph2 (beta2 b)) 1 :=
  graphOrientation (contDiff_beta2 b) (boolSign (ε b)) (boolSign_ne_zero _)

/-- The oriented lift `∑ T_y(Gᵢ, ±)` of the first structure, signs `ε`. -/
def orientedLift1 (ε : Bool → Bool) : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ :=
  orientedSumRn (fun b => graph2 (beta1 b)) (fun _ => 1) (orient1 ε)

/-- The oriented lift `∑ T_y(Gⱼ, ±)` of the second structure, signs `ε`. -/
def orientedLift2 (ε : Bool → Bool) : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ :=
  orientedSumRn (fun b => graph2 (beta2 b)) (fun _ => 1) (orient2 ε)

/-- **The text's first orientation `T̂¹`**: `G⁺⁺` oriented by `(1, 0)` at `(0, 0)`, `G⁻⁻` by
`(-1, 0)`. -/
def exampleT1 := orientedLift1 id

/-- **The text's second orientation `T̂²`**: `G⁺⁻` oriented by `(1, 0)` at `(0, 0)`, `G⁻⁺` by
`(-1, 0)`. -/
def exampleT2 := orientedLift2 id

theorem orientedLift1_isOrientation
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (orientedLift1 ε) :=
  isOrientation_sum_rn (fun b => graph2 (beta1 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b))
    (fun b => isClosed_graph2 (contDiff_beta1 b).continuous) (orient1 ε) hind

theorem orientedLift2_isOrientation
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta)
    (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (orientedLift2 ε) :=
  isOrientation_sum_rn' (fun b => graph2 (beta2 b)) (fun _ => 1) (fun _ => one_pos)
    (fun b => rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta2 b))
    (fun b => isClosed_graph2 (contDiff_beta2 b).continuous) (orient2 ε)
    example935Theta_eq_two hind

open scoped Classical in
theorem orientedSumRn_bool {M : Bool → Set (Fin 2 → ℝ)} {dim : Bool → ℕ}
    (o : ∀ b, (rnPolyfold 2).SubmanifoldOrientation (M b) (dim b)) (σ : Bool → ℚ)
    (z : Fin 2 → ℝ) :
    orientedSumRn M σ o z =
      (if z ∈ M true then Finsupp.single ((o true).tangent z) (σ true) else 0) +
        (if z ∈ M false then Finsupp.single ((o false).tangent z) (σ false) else 0) := by
  rw [orientedSumRn, Finset.sum_filter, Fintype.sum_bool]

theorem mem_graph2_iff {β : ℝ → ℝ} {z : Fin 2 → ℝ} : z ∈ graph2 β ↔ z 1 = β (z 0) := Iff.rfl

theorem orientedSumRn_bool_true {M : Bool → Set (Fin 2 → ℝ)} {dim : Bool → ℕ}
    (o : ∀ b, (rnPolyfold 2).SubmanifoldOrientation (M b) (dim b)) (σ : Bool → ℚ)
    {z : Fin 2 → ℝ} (ht : z ∈ M true) (hf : z ∉ M false) :
    orientedSumRn M σ o z = Finsupp.single ((o true).tangent z) (σ true) := by
  rw [orientedSumRn_bool, if_pos ht, if_neg hf, add_zero]

theorem orientedSumRn_bool_false {M : Bool → Set (Fin 2 → ℝ)} {dim : Bool → ℕ}
    (o : ∀ b, (rnPolyfold 2).SubmanifoldOrientation (M b) (dim b)) (σ : Bool → ℚ)
    {z : Fin 2 → ℝ} (ht : z ∉ M true) (hf : z ∈ M false) :
    orientedSumRn M σ o z = Finsupp.single ((o false).tangent z) (σ false) := by
  rw [orientedSumRn_bool, if_neg ht, if_pos hf, zero_add]

theorem deriv_eq_of_eqOn_Ioi {f g : ℝ → ℝ} (h : ∀ t, 0 < t → f t = g t) {s : ℝ} (hs : 0 < s) :
    deriv f s = deriv g s :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioi_mem_nhds hs) fun t ht => h t ht)

theorem deriv_eq_of_eqOn_Iio {f g : ℝ → ℝ} (h : ∀ t, t < 0 → f t = g t) {s : ℝ} (hs : s < 0) :
    deriv f s = deriv g s :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Iio_mem_nhds hs) fun t ht => h t ht)

/-- Opposite signs give different oriented tangents. -/
theorem graphOrientation_tangent_ne' {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {b b' : Bool}
    (h : b ≠ b') {z : Fin 2 → ℝ} (hz : z ∈ graph2 β) :
    (graphOrientation hβ (boolSign b) (boolSign_ne_zero b)).tangent z ≠
      (graphOrientation hβ (boolSign b') (boolSign_ne_zero b')).tangent z := by
  cases b <;> cases b' <;> simp at h
  · exact (graphOrientation_tangent_ne hβ hz).symm
  · exact graphOrientation_tangent_ne hβ hz

theorem zero_mem_graph2_beta1 : ∀ b, (0 : Fin 2 → ℝ) ∈ graph2 (beta1 b)
  | true => by simp [mem_graph2_iff, beta1, betaPP_zero]
  | false => by simp [mem_graph2_iff, beta1, betaMM, betaPP_zero]

theorem zero_mem_graph2_beta2 : ∀ b, (0 : Fin 2 → ℝ) ∈ graph2 (beta2 b)
  | true => by simp [mem_graph2_iff, beta2, betaPM]
  | false => by simp [mem_graph2_iff, beta2, betaMP, betaPM]

theorem deriv_beta1_zero : ∀ b, deriv (beta1 b) 0 = 0
  | true => deriv_betaPP_zero
  | false => deriv_betaMM_zero

theorem deriv_beta2_zero : ∀ b, deriv (beta2 b) 0 = 0
  | true => deriv_betaPM_zero
  | false => deriv_betaMP_zero

/-- `e₁ = (1, 0)` in the chart model of `ℝ²`. -/
def horizontalVec : (rnChart 2 0).model.E 0 := (![1, 0] : Fin 2 → ℝ)

theorem graphDir_of_deriv_eq_zero {β : ℝ → ℝ} {z : Fin 2 → ℝ} (h : deriv β (z 0) = 0) :
    graphDir β z = horizontalVec := by
  change graphDirR β z = (![1, 0] : Fin 2 → ℝ)
  rw [graphDirR, h]

/-- **The orientations at `(0, 0)`** (Example 9.3.5): the positive frames of `G⁺⁺` (`b = true`)
and `G⁻⁻` (`b = false`) at the origin have chart vector a positive multiple of `(1, 0)`,
respectively `(-1, 0)`; likewise for `G⁺⁻` and `G⁻⁺`. -/
theorem example_9_3_5_frames_origin (b : Bool) :
    (∀ a ∈ (orient1 id b).frames 0, ∃ c : ℝ, 0 < c ∧
      chartVec idChart2 (a 0) = (c * boolSign b) • horizontalVec) ∧
    (∀ a ∈ (orient2 id b).frames 0, ∃ c : ℝ, 0 < c ∧
      chartVec idChart2 (a 0) = (c * boolSign b) • horizontalVec) := by
  refine ⟨fun a ⟨_, c, hc, hca⟩ => ⟨c, hc, ?_⟩, fun a ⟨_, c, hc, hca⟩ => ⟨c, hc, ?_⟩⟩
  · rw [hca, graphDir_of_deriv_eq_zero (deriv_beta1_zero b)]; rfl
  · rw [hca, graphDir_of_deriv_eq_zero (deriv_beta2_zero b)]; rfl

/-- **Example 9.3.5: the two orientations coincide at `(0, 0)`.** -/
theorem example_9_3_5_eq_origin : exampleT1 0 = exampleT2 0 := by
  rw [exampleT1, exampleT2, orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool,
    if_pos (zero_mem_graph2_beta1 true), if_pos (zero_mem_graph2_beta1 false),
    if_pos (zero_mem_graph2_beta2 true), if_pos (zero_mem_graph2_beta2 false)]
  congr 1
  · exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) true))
      (graphOrientation_tangent_eq (contDiff_beta1 true) (contDiff_beta2 true) (boolSign_ne_zero _)
        (zero_mem_graph2_beta1 true) (zero_mem_graph2_beta2 true)
        ((deriv_beta1_zero true).trans (deriv_beta2_zero true).symm))
  · exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
      (graphOrientation_tangent_eq (contDiff_beta1 false) (contDiff_beta2 false)
        (boolSign_ne_zero _)
        (zero_mem_graph2_beta1 false) (zero_mem_graph2_beta2 false)
        ((deriv_beta1_zero false).trans (deriv_beta2_zero false).symm))

/-- **Example 9.3.5, "otherwise different", does not hold as we read it**: the two orientations
also coincide at every point `(s, t)` with `s < 0` (there `G⁺⁻ = G⁺⁺` and `G⁻⁺ = G⁻⁻`, with the
same orientations). -/
theorem example_9_3_5_eq_of_neg {z : Fin 2 → ℝ} (hz : z 0 < 0) : exampleT1 z = exampleT2 z := by
  have h1 : z ∈ graph2 (beta2 true) ↔ z ∈ graph2 (beta1 true) := by
    change z 1 = betaPM (z 0) ↔ z 1 = betaPP (z 0)
    rw [betaPM_of_nonpos hz.le]
  have h2 : z ∈ graph2 (beta2 false) ↔ z ∈ graph2 (beta1 false) := by
    change z 1 = betaMP (z 0) ↔ z 1 = betaMM (z 0)
    rw [betaMP_of_nonpos hz.le]
  have d1 : deriv (beta1 true) (z 0) = deriv (beta2 true) (z 0) :=
    deriv_eq_of_eqOn_Iio (fun t ht => (betaPM_of_nonpos ht.le).symm) hz
  have d2 : deriv (beta1 false) (z 0) = deriv (beta2 false) (z 0) :=
    deriv_eq_of_eqOn_Iio (fun t ht => (betaMP_of_nonpos ht.le).symm) hz
  rw [exampleT1, exampleT2, orientedLift1, orientedLift2, orientedSumRn_bool, orientedSumRn_bool]
  congr 1
  · by_cases ha : z ∈ graph2 (beta1 true)
    · rw [if_pos ha, if_pos (h1.2 ha)]
      exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) true))
        (graphOrientation_tangent_eq (contDiff_beta1 true) (contDiff_beta2 true)
          (boolSign_ne_zero _)
          ha (h1.2 ha) d1)
    · rw [if_neg ha, if_neg fun h => ha (h1.1 h)]
  · by_cases ha : z ∈ graph2 (beta1 false)
    · rw [if_pos ha, if_pos (h2.2 ha)]
      exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
        (graphOrientation_tangent_eq (contDiff_beta1 false) (contDiff_beta2 false)
          (boolSign_ne_zero _)
          ha (h2.2 ha) d2)
    · rw [if_neg ha, if_neg fun h => ha (h2.1 h)]

/-- The point `(s, β⁺⁺(s))` of `G⁺⁺`. -/
def ptPP (s : ℝ) : Fin 2 → ℝ := ![s, betaPP s]

/-- The point `(s, β⁻⁻(s))` of `G⁻⁻`. -/
def ptMM (s : ℝ) : Fin 2 → ℝ := ![s, betaMM s]

theorem ptPP_mem (s : ℝ) : ptPP s ∈ graph2 (beta1 true) := by simp [mem_graph2_iff, ptPP, beta1]

theorem ptPP_not_mem {s : ℝ} (hs : s ≠ 0) : ptPP s ∉ graph2 (beta1 false) := by
  simp only [mem_graph2_iff, ptPP, beta1, cond_false, betaMM, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  intro h
  linarith [betaPP_pos hs]

theorem ptMM_mem (s : ℝ) : ptMM s ∈ graph2 (beta1 false) := by simp [mem_graph2_iff, ptMM, beta1]

theorem ptMM_not_mem {s : ℝ} (hs : s ≠ 0) : ptMM s ∉ graph2 (beta1 true) := by
  simp only [mem_graph2_iff, ptMM, beta1, cond_true, betaMM, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  intro h
  linarith [betaPP_pos hs]

theorem ptPP_mem_beta2 {s : ℝ} (hs : 0 < s) : ptPP s ∈ graph2 (beta2 false) ∧
    ptPP s ∉ graph2 (beta2 true) := by
  refine ⟨?_, ?_⟩
  · simp [mem_graph2_iff, ptPP, beta2, betaMP_of_pos hs]
  · simp only [mem_graph2_iff, ptPP, beta2, cond_true, Matrix.cons_val_one, Matrix.cons_val_zero,
      betaPM_of_pos hs, betaMM]
    intro h
    linarith [betaPP_pos hs.ne']

theorem ptPP_mem_beta2_of_neg {s : ℝ} (hs : s < 0) : ptPP s ∈ graph2 (beta2 true) ∧
    ptPP s ∉ graph2 (beta2 false) := by
  refine ⟨?_, ?_⟩
  · simp [mem_graph2_iff, ptPP, beta2, betaPM_of_nonpos hs.le]
  · simp only [mem_graph2_iff, ptPP, beta2, cond_false, Matrix.cons_val_one, Matrix.cons_val_zero,
      betaMP_of_nonpos hs.le, betaMM]
    intro h
    linarith [betaPP_pos hs.ne]

theorem ptMM_mem_beta2_of_neg {s : ℝ} (hs : s < 0) : ptMM s ∈ graph2 (beta2 false) ∧
    ptMM s ∉ graph2 (beta2 true) := by
  refine ⟨?_, ?_⟩
  · simp [mem_graph2_iff, ptMM, beta2, betaMP_of_nonpos hs.le]
  · simp only [mem_graph2_iff, ptMM, beta2, cond_true, Matrix.cons_val_one, Matrix.cons_val_zero,
      betaPM_of_nonpos hs.le, betaMM]
    intro h
    linarith [betaPP_pos hs.ne]

/-- At `(s, β⁺⁺(s))`, `s > 0`, the first structure gives `T(G⁺⁺, ε(true))`. -/
theorem orientedLift1_ptPP (ε : Bool → Bool) {s : ℝ} (hs : s ≠ 0) :
    orientedLift1 ε (ptPP s) = Finsupp.single ((orient1 ε true).tangent (ptPP s)) 1 :=
  orientedSumRn_bool_true _ _ (ptPP_mem s) (ptPP_not_mem hs)

theorem orientedLift1_ptMM (ε : Bool → Bool) {s : ℝ} (hs : s ≠ 0) :
    orientedLift1 ε (ptMM s) = Finsupp.single ((orient1 ε false).tangent (ptMM s)) 1 :=
  orientedSumRn_bool_false _ _ (ptMM_not_mem hs) (ptMM_mem s)

/-- On `s > 0`, `G⁻⁺ = G⁺⁺` near `(s, β⁺⁺(s))`: the second structure gives `T(G⁺⁺, δ(false))`. -/
theorem orientedLift2_ptPP_of_pos (δ : Bool → Bool) {s : ℝ} (hs : 0 < s) :
    orientedLift2 δ (ptPP s) =
      Finsupp.single ((graphOrientation contDiff_betaPP (boolSign (δ false))
        (boolSign_ne_zero _)).tangent
        (ptPP s)) 1 := by
  rw [orientedLift2, orientedSumRn_bool_false _ _ (ptPP_mem_beta2 hs).2 (ptPP_mem_beta2 hs).1]
  exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
    (graphOrientation_tangent_eq (contDiff_beta2 false) contDiff_betaPP (boolSign_ne_zero _)
      (ptPP_mem_beta2 hs).1 (ptPP_mem s)
      (deriv_eq_of_eqOn_Ioi (fun t ht => betaMP_of_pos ht) (by simpa [ptPP] using hs)))

/-- On `s < 0`, `G⁺⁻ = G⁺⁺`: the second structure gives `T(G⁺⁺, δ(true))` at `(s, β⁺⁺(s))`. -/
theorem orientedLift2_ptPP_of_neg (δ : Bool → Bool) {s : ℝ} (hs : s < 0) :
    orientedLift2 δ (ptPP s) =
      Finsupp.single ((graphOrientation contDiff_betaPP (boolSign (δ true))
        (boolSign_ne_zero _)).tangent
        (ptPP s)) 1 := by
  rw [orientedLift2, orientedSumRn_bool_true _ _ (ptPP_mem_beta2_of_neg hs).1
    (ptPP_mem_beta2_of_neg hs).2]
  exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) true))
    (graphOrientation_tangent_eq (contDiff_beta2 true) contDiff_betaPP (boolSign_ne_zero _)
      (ptPP_mem_beta2_of_neg hs).1 (ptPP_mem s)
      (deriv_eq_of_eqOn_Iio (fun t ht => betaPM_of_nonpos ht.le) (by simpa [ptPP] using hs)))

/-- On `s < 0`, `G⁻⁺ = G⁻⁻`: the second structure gives `T(G⁻⁻, δ(false))` at `(s, β⁻⁻(s))`. -/
theorem orientedLift2_ptMM_of_neg (δ : Bool → Bool) {s : ℝ} (hs : s < 0) :
    orientedLift2 δ (ptMM s) =
      Finsupp.single ((graphOrientation contDiff_betaMM (boolSign (δ false))
        (boolSign_ne_zero _)).tangent
        (ptMM s)) 1 := by
  rw [orientedLift2, orientedSumRn_bool_false _ _ (ptMM_mem_beta2_of_neg hs).2
    (ptMM_mem_beta2_of_neg hs).1]
  exact congrArg (fun g => Finsupp.single g ((fun _ => (1 : ℚ)) false))
    (graphOrientation_tangent_eq (contDiff_beta2 false) contDiff_betaMM (boolSign_ne_zero _)
      (ptMM_mem_beta2_of_neg hs).1 (ptMM_mem s)
      (deriv_eq_of_eqOn_Iio (fun t ht => betaMP_of_nonpos ht.le) (by simpa [ptMM] using hs)))

/-- **Example 9.3.5: the two orientations differ at every `(s, β⁺⁺(s))`, `s > 0`.** -/
theorem example_9_3_5_ne_of_pos {s : ℝ} (hs : 0 < s) :
    exampleT1 (ptPP s) ≠ exampleT2 (ptPP s) := by
  rw [exampleT1, exampleT2, orientedLift1_ptPP id hs.ne', orientedLift2_ptPP_of_pos id hs]
  intro h
  exact graphOrientation_tangent_ne' contDiff_betaPP (b := true) (b' := false) (by decide)
    (ptPP_mem s) ((Finsupp.single_left_inj one_ne_zero).1 h)

/-- **The sign choices of the first structure give four different orientations** (the text's
"four different possibilities to orient", Example 9.3.5). -/
theorem orientedLift1_injective : Function.Injective orientedLift1 := by
  intro ε ε' h
  funext b
  by_contra hb
  cases b
  · have h1 := congrFun h (ptMM 1)
    rw [orientedLift1_ptMM ε one_ne_zero, orientedLift1_ptMM ε' one_ne_zero] at h1
    exact graphOrientation_tangent_ne' (contDiff_beta1 false) hb (ptMM_mem 1)
      ((Finsupp.single_left_inj one_ne_zero).1 h1)
  · have h1 := congrFun h (ptPP 1)
    rw [orientedLift1_ptPP ε one_ne_zero, orientedLift1_ptPP ε' one_ne_zero] at h1
    exact graphOrientation_tangent_ne' (contDiff_beta1 true) hb (ptPP_mem 1)
      ((Finsupp.single_left_inj one_ne_zero).1 h1)

/-- **Example 9.3.5, "four different possibilities", does not hold as we read it**: the text's
second orientation `T̂²` is none of the four orientations of the first structure
(`orientedLift1_injective`), so `Θ` has at least five orientations with weights `1` (and infinitely
many with fractional weights, as in Remark 9.3.3). -/
theorem exampleT2_ne_orientedLift1 (ε : Bool → Bool) : exampleT2 ≠ orientedLift1 ε := by
  intro h
  have hp := congrFun h (ptPP 1)
  have hm := congrFun h (ptPP (-1))
  rw [exampleT2, orientedLift2_ptPP_of_pos id one_pos, orientedLift1_ptPP ε one_ne_zero] at hp
  rw [exampleT2, orientedLift2_ptPP_of_neg id (by norm_num),
    orientedLift1_ptPP ε (by norm_num)] at hm
  have hp' := (Finsupp.single_left_inj one_ne_zero).1 hp
  have hm' := (Finsupp.single_left_inj one_ne_zero).1 hm
  cases hε : ε true
  · exact graphOrientation_tangent_ne' contDiff_betaPP (b := true) (b' := false) (by decide)
      (ptPP_mem (-1)) (by rw [← hε]; exact hm')
  · exact graphOrientation_tangent_ne' contDiff_betaPP (b := false) (b' := true) (by decide)
      (ptPP_mem 1) (by rw [← hε]; exact hp')

/-- **Example 9.3.5, last claim**: no choice of signs `δ` orients the second structure
`G⁺⁻, G⁻⁺` so as to coincide with `T̂¹`, even near `(0, 0)`: for every `s > 0` they differ at
`(s, β⁺⁺(s))` or at `(-s, β⁻⁻(-s))`. -/
theorem example_9_3_5_cannot_coincide (δ : Bool → Bool) {s : ℝ} (hs : 0 < s) :
    orientedLift2 δ (ptPP s) ≠ exampleT1 (ptPP s) ∨
      orientedLift2 δ (ptMM (-s)) ≠ exampleT1 (ptMM (-s)) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  rw [orientedLift2_ptPP_of_pos δ hs, exampleT1, orientedLift1_ptPP id hs.ne'] at h1
  rw [orientedLift2_ptMM_of_neg δ (neg_neg_of_pos hs), exampleT1,
    orientedLift1_ptMM id (neg_ne_zero.2 hs.ne')] at h2
  have h1' := (Finsupp.single_left_inj one_ne_zero).1 h1
  have h2' := (Finsupp.single_left_inj one_ne_zero).1 h2
  cases hδ : δ false
  · rw [hδ] at h1'
    exact graphOrientation_tangent_ne' contDiff_betaPP (b := false) (b' := true) (by decide)
      (ptPP_mem s) h1'
  · rw [hδ] at h2'
    exact graphOrientation_tangent_ne' contDiff_betaMM (b := true) (b' := false) (by decide)
      (ptMM_mem (-s)) h2'

/-- **Example 9.3.5, 2021 p. 425 (2017: Example 9.1)**, the claims that hold as we read them:
`Θ` is a branched ep⁺-subgroupoid; `G⁺⁺, G⁻⁻` and `G⁺⁻, G⁻⁺`, oriented by `±(1, 0)` at `(0, 0)`,
give two orientations `T̂¹`, `T̂²` (given Theorem 9.2.1's independence for `Θ`), which coincide at
`(0, 0)` and differ at the points `(s, β⁺⁺(s))`, `s > 0`; and no orientation of the second
structure coincides with `T̂¹` near `(0, 0)`. -/
theorem example_9_3_5
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums example935Theta) :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid example935Theta ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT1 ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT2 ∧
    exampleT1 0 = exampleT2 0 ∧
    (∀ s : ℝ, 0 < s → exampleT1 (ptPP s) ≠ exampleT2 (ptPP s)) ∧
    ∀ (δ : Bool → Bool) (s : ℝ), 0 < s →
      orientedLift2 δ (ptPP s) ≠ exampleT1 (ptPP s) ∨
        orientedLift2 δ (ptMM (-s)) ≠ exampleT1 (ptMM (-s)) :=
  ⟨example935Theta_isBranched, orientedLift1_isOrientation hind id,
    orientedLift2_isOrientation hind id, example_9_3_5_eq_origin,
    fun _ hs => example_9_3_5_ne_of_pos hs, fun δ _ hs => example_9_3_5_cannot_coincide δ hs⟩

end Example935

end Polyfold
