import Polyfold.Chapter9.GapP2_E3_SheetIntegration
import Polyfold.Chapter9.GapP2_E3_GraphChartExists
import Polyfold.Chapter9.GapP2_E1_BranchedIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": **Theorems 9.5.4 and 9.5.5** (p. 438; 2017:
Theorems 9.2, 9.3) and **Definition 9.5.6** (p. 439) for the integrals of forms over oriented
sheets built in `GapP2_E3_SheetIntegration.lean` (gap G.107).  Numbers and pages are the 2021
text's.

# The covering hypothesis for the concrete integration, and Theorems 9.5.4, 9.5.5

## What is formalized

* `MPolyfold.exists_compact_nhds_submanifold`: an `n`-dimensional submanifold is locally
  compact (near a point it lies in a compact subset of itself).
* `FormEval.exists_mem_sheets`: every point of an `n`-dimensional submanifold `N` has an open
  neighbourhood `V` with `N ∩ V` in the class `F.sheets` (one graph chart, all forms absolutely
  integrable: the densities are continuous and the piece lies in a compact subset of `N`).
* `FormEval.hcov_of_tameOpen`, `FormEval.hcovEff_of_tameOpen`: if every point of `supp Θ` has an
  oriented tame structure of dimension `n` describing `T̂Θ`, then it has one whose sheets are in
  `F.sheets` (the given one restricted to a smaller neighbourhood with the natural action).
  The restriction of the sheets `Mᵢ ∩ V` must again have tame induced structures; this is the
  hypothesis `htame`.  It holds when `X` has no boundary (`hcov_of_degIndex_eq_zero`).
* `theorem_9_5_4_concrete`, `theorem_9_5_5_concrete`, `concreteBranchedIntegral`,
  `concreteBranchedIntegralEff`: E1's theorems and Definition 9.5.6 for
  `F.sheetIntegration hn`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped NNReal

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **An `n`-dimensional submanifold is locally compact**: every point has an open neighbourhood
`W` in the M-polyfold such that `N ∩ W` lies in a compact subset of `N`.  (In a chart, `N` is
closed in small closed balls, and a continuous linear map to `ℝⁿ` has a Lipschitz inverse on
it.) -/
theorem exists_compact_nhds_submanifold {N : Set X} {n : ℕ} (hN : P.IsSubmanifoldOfDim N n)
    {x : X} (hx : x ∈ N) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ K : Set X, IsCompact K ∧ N ∩ W ⊆ K ∧ K ⊆ N := by
  classical
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  set d := hN.1.data hx with hd
  have hxV : x ∈ d.V := hN.1.mem_data_V hx
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hx hxV
  obtain ⟨hz, hxt, -⟩ := chartTangent_eq_range hφ d ht hx hxV hxφ
  have hzt : φ.model.E.toBase 1 (levelLift φ 1 x) ∈ t.retract := by rw [hz]; exact hxt
  have hrank : ∀ a ∈ t.retract, finrank ℝ (LinearMap.range
      (scDeriv t.U t (t.plusLift a) : φ.model.E 0 →ₗ[ℝ] φ.model.E 0)) = n := by
    intro a ha
    rw [ht] at ha
    obtain ⟨y, ⟨hyW, hyN⟩, rfl⟩ := ha
    exact (hasDimAt_finrank hφ d ht hyN (d.toSubData.shrink_subset_V φ hyW)
      (d.toSubData.shrink_subset_source φ hyW)).unique (hN.2 y hyN)
  obtain ⟨p, Lf, δ₀, K, hδ₀, hlip, -, -⟩ := ScRetraction.exists_graphData htp hzt hrank
  obtain ⟨δc, hδc, hclosed⟩ := t.exists_isClosed_retract_inter_closedBall hzt
  rw [hz] at hlip hclosed
  set r := min δ₀ δc / 2 with hr
  have hmin : 0 < min δ₀ δc := lt_min hδ₀ hδc
  have hr0 : 0 < r := by positivity
  have hrδ₀ : r < δ₀ := by have := min_le_left δ₀ δc; linarith
  have hrδc : r ≤ δc := by have := min_le_right δ₀ δc; linarith
  set Kc := t.retract ∩ Metric.closedBall (φ x) r with hKc
  have hKcl : IsClosed Kc := hclosed r hrδc
  have hnear : ∀ a ∈ Kc, ‖a - φ x‖ < δ₀ := fun a ha => by
    have := ha.2
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    linarith
  have hlipK : ∀ a ∈ Kc, ∀ b ∈ Kc, dist a b ≤ K * dist (p a) (p b) := fun a ha b hb =>
    hlip a ha.1 b hb.1 (hnear a ha) (hnear b hb)
  have hpc : IsCompact (p '' Kc) := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_image_of_antilipschitzOn p hKcl hlipK) ?_
    exact (p.lipschitz.isBounded_image Metric.isBounded_closedBall).subset
      (image_mono inter_subset_right)
  have hinj : InjOn p Kc := fun a ha b hb h => by
    have h1 := hlipK a ha b hb
    rw [h, dist_self, mul_zero] at h1
    exact dist_le_zero.1 h1
  have : Nonempty (φ.model.E 0) := ⟨φ x⟩
  set g := Function.invFunOn p Kc with hg
  have hgl : ∀ a ∈ Kc, g (p a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
  have hgL : LipschitzOnWith K g (p '' Kc) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hgl a ha, hgl b hb]
    exact hlipK a ha b hb
  have hKcc : IsCompact Kc := by
    have h1 := hpc.image_of_continuousOn hgL.continuousOn
    have h2 : g '' (p '' Kc) = Kc := by
      rw [image_image]
      exact (image_congr hgl).trans (image_id' Kc)
    rwa [h2] at h1
  have hKcO : Kc ⊆ φ.model.O := by
    rintro a ⟨ha, -⟩
    rw [ht] at ha
    obtain ⟨y, ⟨hyW, -⟩, rfl⟩ := ha
    exact φ.mapsTo_model y (d.toSubData.shrink_subset_source φ hyW)
  have hKx : IsCompact (φ.symm '' Kc) :=
    hKcc.image_of_continuousOn (φ.continuousOn_invFun.mono hKcO)
  have hc : ContinuousOn (fun a => ‖φ a - φ x‖) φ.source :=
    (φ.continuousOn_toFun.sub continuousOn_const).norm
  obtain ⟨V', hV', hVe⟩ := (_root_.continuousOn_iff'.1 hc) (Iio r) isOpen_Iio
  have hxW : x ∈ d.toSubData.shrink φ := d.toSubData.mem_shrink φ hx hxV hxφ
  refine ⟨V' ∩ d.toSubData.shrink φ, hV'.inter (d.toSubData.isOpen_shrink φ), ⟨?_, hxW⟩,
    φ.symm '' Kc, hKx, ?_, ?_⟩
  · have : x ∈ (fun a => ‖φ a - φ x‖) ⁻¹' Iio r ∩ φ.source :=
      ⟨by change ‖φ x - φ x‖ < r; rw [sub_self, norm_zero]; exact hr0, hxφ⟩
    rw [hVe] at this
    exact this.1
  · rintro y ⟨hyN, hyV', hyW⟩
    have hyφ := d.toSubData.shrink_subset_source φ hyW
    have hy1 : y ∈ V' ∩ φ.source := ⟨hyV', hyφ⟩
    rw [← hVe] at hy1
    have hyr : ‖φ y - φ x‖ < r := hy1.1
    refine ⟨φ y, ⟨?_, ?_⟩, φ.symm_apply_apply hyφ⟩
    · rw [ht]; exact ⟨y, ⟨hyW, hyN⟩, rfl⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact hyr.le
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    rw [ht] at ha
    obtain ⟨y, ⟨hyW, hyN⟩, rfl⟩ := ha
    rw [φ.symm_apply_apply (d.toSubData.shrink_subset_source φ hyW)]
    exact hyN

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

/-- The density `y ↦ ω(c.tvec y)` of a graph chart is continuous on the sheet. -/
theorem continuousOn_ev_tvec {N : Set Obj} (hN : X.PObj.IsSmoothSubmanifold N)
    (c : X.PObj.GraphChart n N) (ω : Ω) : ContinuousOn (fun y => F.ev ω (c.tvec y)) N := by
  refine F.ev_continuousOn ω hN c.isChart (K := N) (fun y hy => ⟨hy, c.subset_source hy⟩) c.tvec
    (fun z hz i => c.tvec_mem hz i) ?_
  have h : ContinuousOn (fun z i => c.L z (MPolyfold.GraphChart.bvec i)) N :=
    continuousOn_pi.2 fun i => c.continuousOn_L.clm_apply continuousOn_const
  exact h.congr fun z hz => funext fun i => c.chartVec_tvec hz i

/-- **Every point of an `n`-dimensional submanifold has a neighbourhood in which the submanifold
is a sheet of the class `F.sheets`.** -/
theorem exists_mem_sheets {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n) {x : Obj}
    (hx : x ∈ N) : ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ F.sheets := by
  obtain ⟨V₀, hV₀, hxV₀, ⟨c₀⟩⟩ := MPolyfold.exists_graphChart hN hx
  obtain ⟨W, hW, hxW, Kx, hKx, hNW, hKxN⟩ := MPolyfold.exists_compact_nhds_submanifold hN hx
  obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hV₀.mem_nhds hxV₀)
  set V₁ := interior t ∩ W with hV₁
  have hV₁o : IsOpen V₁ := isOpen_interior.inter hW
  have hxV₁ : x ∈ V₁ := ⟨mem_interior_iff_mem_nhds.2 ht, hxW⟩
  set K' := Kx ∩ t with hK'
  have hK'c : IsCompact K' := hKx.inter_right htc
  have hK'N : K' ⊆ N ∩ V₀ := fun y hy => ⟨hKxN hy.1, htV hy.2⟩
  have hsub : (N ∩ V₀) ∩ V₁ ⊆ K' := fun y hy =>
    ⟨hNW ⟨hy.1.1, hy.2.2⟩, interior_subset hy.2.1⟩
  have hN₀ : X.PObj.IsSubmanifoldOfDim (N ∩ V₀) n := hN.inter_isOpen hV₀
  refine ⟨V₀ ∩ V₁, hV₀.inter hV₁o, ⟨hxV₀, hxV₁⟩, ?_⟩
  rw [← inter_assoc]
  refine ⟨hN₀.inter_isOpen hV₁o, c₀.restrict hV₁o, fun ω => ?_⟩
  have hcont := F.continuousOn_ev_tvec hN₀.1 c₀ ω
  obtain ⟨C, hC⟩ := hK'c.exists_bound_of_continuousOn (hcont.mono hK'N)
  have hdom : (c₀.restrict hV₁o).dom = c₀.coord '' ((N ∩ V₀) ∩ V₁) := rfl
  have hfin : volume (c₀.restrict hV₁o).dom ≠ ⊤ := by
    have hcK : IsCompact (c₀.coord '' K') :=
      hK'c.image_of_continuousOn (c₀.continuousOn_coord.mono hK'N)
    exact (lt_of_le_of_lt (measure_mono (hdom ▸ image_mono hsub)) hcK.measure_lt_top).ne
  have hq : ∀ u ∈ (c₀.restrict hV₁o).dom, c₀.q u ∈ (N ∩ V₀) ∩ V₁ := fun u hu =>
    (c₀.restrict hV₁o).q_mem hu
  have hco : ContinuousOn (fun u => F.ev ω (c₀.tvec (c₀.q u))) (c₀.restrict hV₁o).dom :=
    hcont.comp ((c₀.restrict hV₁o).continuousOn_q) fun u hu => (hq u hu).1
  have : IsFiniteMeasure (volume.restrict (c₀.restrict hV₁o).dom) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  refine Integrable.of_bound
    (hco.aestronglyMeasurable (c₀.restrict hV₁o).measurableSet_dom') C ?_
  refine (ae_restrict_iff' (c₀.restrict hV₁o).measurableSet_dom').2 (Eventually.of_forall ?_)
  intro u hu
  exact hC _ (hsub (hq u hu))

variable {F} {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

open scoped Classical in
/-- **An oriented tame structure restricted to a smaller neighbourhood with the natural action**
whose sheets are sheets of the class `F.sheets`; it describes the same `T̂Θ`, and its natural
representation is a restriction of the given one. -/
theorem exists_restrict_mem_sheets
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    {x : Obj} (C₀ : X.OrientedTameStructure n Θ x) (hC₀ : C₀.Represents T) :
    ∃ C : X.OrientedTameStructure n Θ x, (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧
      C.rep.U ⊆ C₀.rep.U ∧ C.rep.Φ = C₀.rep.Φ := by
  choose V hV hxV hVS using fun i =>
    F.exists_mem_sheets (C₀.isSubmanifoldOfDim i) (C₀.mem_M i)
  set W := ⋂ i, V i with hW
  have hWo : IsOpen W := isOpen_iInter_of_finite hV
  have hxW : x ∈ W := mem_iInter.2 hxV
  obtain ⟨R', hR'sub, hR'Φ, -⟩ := exists_naturalRep_shrink X C₀.rep hWo hxW
  have hsubU : R'.U ⊆ C₀.U := fun y hy => C₀.U_eq ▸ (hR'sub hy).2
  let C : X.OrientedTameStructure n Θ x :=
    { toLocalBranchingStructure :=
        C₀.toLocalBranchingStructure.restrict R'.isOpen_U R'.mem_U hsubU
      rep := R'
      U_eq := rfl
      hasPropernessProperty := C₀.hasPropernessProperty.mono R'.isOpen_U hsubU
      hasTameInducedStructure := fun i =>
        htame _ _ (C₀.isSmoothSubmanifold i) (C₀.hasTameInducedStructure i) R'.isOpen_U
      isSubmanifoldOfDim := fun i => (C₀.isSubmanifoldOfDim i).inter_isOpen R'.isOpen_U
      orient := fun i => (C₀.orient i).restrict R'.isOpen_U }
  refine ⟨C, fun i => ?_, fun y hy hys => ?_, fun y hy => (hR'sub hy).2, hR'Φ⟩
  · have e : C.M i = (C₀.M i ∩ V i) ∩ R'.U := by
      change C₀.M i ∩ R'.U = _
      rw [inter_assoc, inter_eq_right.2 fun y hy => mem_iInter.1 (hR'sub hy).1 i]
    rw [e]
    exact inter_mem_sheets (hVS i) R'.isOpen_U
  · have hyU' : y ∈ R'.U := hy
    rw [hC₀ y (hsubU hy) hys, C₀.orientedSum_eq_sum_ite, C.orientedSum_eq_sum_ite]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff : y ∈ C.M i ↔ y ∈ C₀.M i := ⟨fun h => h.1, fun h => ⟨h, hyU'⟩⟩
    have ht : (C.orient i).tangent y = (C₀.orient i).tangent y :=
      (C₀.orient i).restrict_tangent R'.isOpen_U hyU'
    by_cases h : y ∈ C₀.M i
    · rw [if_pos h, if_pos (hiff.2 h), ht]
      rfl
    · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

/-- **The covering hypothesis of Theorem 9.5.4 for the class `F.sheets`**, from oriented tame
structures describing `T̂Θ` at every point of `supp Θ`. -/
theorem hcov_of_tameOpen
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T := fun x hx => by
  obtain ⟨C₀, hC₀⟩ := hloc x hx
  obtain ⟨C, hS, hT, -⟩ := exists_restrict_mem_sheets (F := F) htame C₀ hC₀
  exact ⟨C, hS, hT⟩

/-- **The covering hypothesis of Theorem 9.5.5 for the class `F.sheets`.** -/
theorem hcovEff_of_tameOpen
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC := fun x hx => by
  obtain ⟨C₀, hC₀, hL⟩ := hloc x hx
  obtain ⟨C, hS, hT, hU, hΦ⟩ := exists_restrict_mem_sheets (F := F) htame C₀ hC₀
  refine ⟨C, hS, hT, fun g V hV hne hVU hid y hy => ?_⟩
  rw [hΦ] at hid ⊢
  exact hL g V hV hne (hVU.trans hU) hid y (hU hy)

/-- On an ep-groupoid whose object M-polyfold has no boundary, open pieces of submanifolds have
tame induced structures. -/
theorem tameOpen_of_degIndex_eq_zero (h0 : ∀ a : Obj, X.PObj.degIndex a = 0)
    (N V : Set Obj) (hN : X.PObj.IsSmoothSubmanifold N) (_ : X.PObj.HasTameInducedStructure N)
    (hV : IsOpen V) : X.PObj.HasTameInducedStructure (N ∩ V) :=
  MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero (hN.inter_isOpen hV) fun a _ => h0 a

/-- **The covering hypothesis of Theorem 9.5.4 when `X` has no boundary.** -/
theorem hcov_of_degIndex_eq_zero (h0 : ∀ a : Obj, X.PObj.degIndex a = 0)
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ F.sheets) ∧ C.Represents T :=
  hcov_of_tameOpen (tameOpen_of_degIndex_eq_zero h0) hloc

variable (F)

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2), for the integrals of
`GapP2_E3_SheetIntegration.lean`**: `Θ` a compact branched ep⁺-subgroupoid with an orientation
`T̂Θ = T` which is described near every point of its support by an oriented tame structure of
dimension `n ≥ 1`.  There is exactly one linear map `ω ↦ μ_ω` into the signed measures on
`(S, L(S))` with `μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for the oriented tame structures
describing `T̂Θ` whose sheets are in the class `F.sheets`, and the measurable `K ⊆ |U(x)|`. -/
theorem theorem_9_5_4_concrete (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.sheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.sheets) ∧ C.Represents T) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasure (F.sheetIntegration hn) ω (Subtype.val '' K) :=
  theorem_9_5_4 (F.sheetIntegration hn) hΘ hcpt hT (hcov_of_tameOpen htame hloc)

/-- **Theorem 9.5.5, 2021 p. 438 (2017: Theorem 9.3), for the integrals of
`GapP2_E3_SheetIntegration.lean`**: the same with the weights `1/♯G_x^eff`, for structures whose
`U(x)` has the property of Definition 7.2.18. -/
theorem theorem_9_5_5_concrete (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma F.sheetNull Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ F.sheets) ∧ C.Represents T ∧ C.rep.HasLUC) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma F.sheetNull Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = C.localMeasureEff (F.sheetIntegration hn) ω (Subtype.val '' K) :=
  theorem_9_5_5 (F.sheetIntegration hn) hΘ hcpt hT (hcovEff_of_tameOpen htame hloc)

/-- **Definition 9.5.6 (1), 2021 p. 439**, for the integrals of
`GapP2_E3_SheetIntegration.lean`: the branched integral `∫_Θ̂ ω = μ_ω(S)`. -/
def concreteBranchedIntegral (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x, C.Represents T) (ω : Ω) : ℝ :=
  branchedIntegral (F.sheetIntegration hn) hΘ hcpt hT (hcov_of_tameOpen htame hloc) ω

/-- **Definition 9.5.6 (2), 2021 p. 439**, for the integrals of
`GapP2_E3_SheetIntegration.lean`: the effective branched integral `∮_Θ̂ ω = μ_ω^eff(S)`. -/
def concreteBranchedIntegralEff (hn : 0 < n) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T)
    (htame : ∀ N V : Set Obj, X.PObj.IsSmoothSubmanifold N → X.PObj.HasTameInducedStructure N →
      IsOpen V → X.PObj.HasTameInducedStructure (N ∩ V))
    (hloc : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      C.Represents T ∧ C.rep.HasLUC) (ω : Ω) : ℝ :=
  branchedIntegralEff (F.sheetIntegration hn) hΘ hcpt hT (hcovEff_of_tameOpen htame hloc) ω

end FormEval

end EpGroupoid

end Polyfold
