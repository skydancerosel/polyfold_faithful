import Polyfold.Chapter9.GapP2_E3_GraphChart
import Polyfold.Chapter2.LocalTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107): every
`n`-dimensional submanifold of an M-polyfold is, near each of its points and in a chart of the
M-polyfold, a graph over `ℝⁿ` (`MPolyfold.exists_graphChart`).  Numbers and pages are the 2021
text's.

# Existence of graph charts

## What is formalized

* `ScRetraction.exists_graphData`: for an sc⁺-retraction `r` of constant rank `n` on its retract
  and a point `x₀ = ι z` of the retract, a continuous linear `p : E₀ → ℝⁿ` which is injective
  with Lipschitz inverse on the retract near `x₀`, and right inverses `L_a` of `p` with range
  `range Dr(â)`, continuous in `a`, such that the chords of the retract at `a` are
  `L_a(p(b − a))` up to `o(‖b − a‖)` (level-`0` norms).
* `MPolyfold.exists_graphChart`: an `n`-dimensional submanifold `N` has, near each point, an
  open piece `N ∩ V` with a graph chart (`MPolyfold.GraphChart`).

## The choices made

`p` is a projection onto `T_xN` (in the chart) followed by a linear isomorphism to `ℝⁿ`;
`L_a = A_a ∘ (p ∘ A_a)⁻¹` with `A_a = Dr(â)|_{T_xN}`, continuous in `a` in the operator norm
(Proposition 1.2.1 (1) for the lift `1₀¹ ∘ r`).  The coordinate image of `N ∩ V` is a countable
union of closed sets (the retract is closed in small closed balls, and `p` has a Lipschitz
inverse on it).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped NNReal

noncomputable section

namespace Polyfold

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}

/-- **The graph data of an sc⁺-retract of constant rank `n` near a point** (level-`0` norms). -/
theorem exists_graphData (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) {n : ℕ}
    (hn : ∀ a ∈ R.retract, finrank ℝ (LinearMap.range
      (scDeriv R.U R (R.plusLift a) : E 0 →ₗ[ℝ] E 0)) = n) :
    ∃ (p : E 0 →L[ℝ] EuclideanSpace ℝ (Fin n))
      (Lf : E 0 → EuclideanSpace ℝ (Fin n) →L[ℝ] E 0) (δ : ℝ) (K : ℝ≥0), 0 < δ ∧
      (∀ a ∈ R.retract, ∀ b ∈ R.retract, ‖a - E.toBase 1 z‖ < δ → ‖b - E.toBase 1 z‖ < δ →
        dist a b ≤ K * dist (p a) (p b)) ∧
      (∀ a ∈ R.retract, ‖a - E.toBase 1 z‖ < δ → (∀ v, p (Lf a v) = v) ∧
        range (Lf a) = range (scDeriv R.U R (R.plusLift a)) ∧
        ∀ ε > 0, ∃ δ' > 0, ∀ b ∈ R.retract, ‖b - a‖ < δ' →
          ‖(b - a) - Lf a (p (b - a))‖ ≤ ε * ‖b - a‖) ∧
      ContinuousOn Lf (R.retract ∩ Metric.ball (E.toBase 1 z) δ) := by
  classical
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  have hx₀U : E.toBase 1 z ∈ R.U := R.retract_subset hz
  set Q : E 0 →L[ℝ] E 0 := scDeriv R.U R z with hQ
  have hQQ : ∀ v, Q (Q v) = Q v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hz)
  set N₀ : Submodule ℝ (E 0) := LinearMap.range (Q : E 0 →ₗ[ℝ] E 0) with hN₀
  have hfin : FiniteDimensional ℝ N₀ := lemma_4_1_7_ii hR hz
  have hrank : finrank ℝ N₀ = n := by
    have := hn _ hz
    rwa [plusLift_toBase_of_mem_retract hz] at this
  obtain ⟨π, hπ⟩ := Submodule.ClosedComplemented.of_finiteDimensional N₀
  let e : N₀ ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hrank, finrank_euclideanSpace_fin])
  set p : E 0 →L[ℝ] EuclideanSpace ℝ (Fin n) := (e : N₀ →L[ℝ] _).comp π with hp
  set J : EuclideanSpace ℝ (Fin n) →L[ℝ] E 0 :=
    N₀.subtypeL.comp (e.symm : _ →L[ℝ] N₀) with hJ
  have hJmem : ∀ u, J u ∈ N₀ := fun u => (e.symm u).2
  have hpJ : ∀ u, p (J u) = u := fun u => by
    change e (π ((e.symm u : N₀) : E 0)) = u
    rw [hπ, e.apply_symm_apply]
  have hJp : ∀ v ∈ N₀, J (p v) = v := fun v hv => by
    change ((e.symm (e (π v)) : N₀) : E 0) = v
    rw [e.symm_apply_apply]
    exact congrArg Subtype.val (hπ ⟨v, hv⟩)
  have hQN : ∀ v ∈ N₀, Q v = v := by
    rintro _ ⟨w, rfl⟩; exact hQQ w
  have hQmem : ∀ v, Q v ∈ N₀ := fun v => ⟨v, rfl⟩
  -- the operators `G a = Dr(â) ∘ Dr(z)`, continuous in `a`
  set G : E 0 → E 0 →L[ℝ] E 0 := fun a =>
    (E.toBase 1).comp (((R.plusDeriv (R.plusLift a)).comp (E.toBase 1)).comp (R.plusDeriv z))
    with hG
  have hGapp : ∀ a ∈ R.U, ∀ v, G a v = scDeriv R.U R (R.plusLift a) (Q v) := fun a ha v => by
    change E.toBase 1 (R.plusDeriv (R.plusLift a) (E.toBase 1 (R.plusDeriv z v))) = _
    rw [toBase_plusDeriv hR (plusLift_mem_lvlSet hR ha), toBase_plusDeriv hR hzU]
  have hc1 := (continuousOn_plusDeriv hR).comp (continuousOn_plusLift hR)
    (fun x hx => plusLift_mem_lvlSet hR hx)
  have hGc : ContinuousOn G R.U :=
    continuousOn_const.clm_comp (hc1.clm_comp continuousOn_const)
  set A : E 0 → EuclideanSpace ℝ (Fin n) →L[ℝ] E 0 := fun a => (G a).comp J with hA
  have hAc : ContinuousOn A R.U := hGc.clm_comp continuousOn_const
  set B : E 0 → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun a => p.comp (A a) with hB
  have hBc : ContinuousOn B R.U := continuousOn_const.clm_comp hAc
  have hB0 : B (E.toBase 1 z) = 1 := by
    ext1 u
    change p (G (E.toBase 1 z) (J u)) = u
    rw [hGapp _ hx₀U, plusLift_toBase_of_mem_retract hz, hQN _ (hJmem u)]
    change p (Q (J u)) = u
    rw [hQN _ (hJmem u), hpJ]
  have hunit : {a | IsUnit (B a)} ∈ 𝓝[R.U] (E.toBase 1 z) := by
    refine hBc _ hx₀U (Units.isOpen.mem_nhds ?_)
    change IsUnit (B (E.toBase 1 z))
    rw [hB0]; exact isUnit_one
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhdsWithin_iff.1 hunit
  set ε₀ : ℝ := 1 / (2 * (1 + ‖J‖ * ‖p‖)) with hε₀
  have hpos : 0 < 1 + ‖J‖ * ‖p‖ := by positivity
  have hε₀pos : 0 < ε₀ := by positivity
  obtain ⟨δ₂, hδ₂, happ⟩ := exists_approx hR hz hε₀pos
  set Lf : E 0 → EuclideanSpace ℝ (Fin n) →L[ℝ] E 0 := fun a => (A a).comp (Ring.inverse (B a))
    with hLf
  have hU : ∀ a ∈ R.retract, ‖a - E.toBase 1 z‖ < min δ₁ δ₂ → IsUnit (B a) := fun a ha had =>
    hball ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le had (min_le_left _ _),
      R.retract_subset ha⟩
  have hpL : ∀ a ∈ R.retract, ‖a - E.toBase 1 z‖ < min δ₁ δ₂ → ∀ v, p (Lf a v) = v :=
    fun a ha had v => by
      change (B a * Ring.inverse (B a)) v = v
      rw [Ring.mul_inverse_cancel _ (hU a ha had)]; rfl
  have hrange : ∀ a ∈ R.retract, ‖a - E.toBase 1 z‖ < min δ₁ δ₂ →
      range (Lf a) = range (scDeriv R.U R (R.plusLift a)) := fun a ha had => by
    have haU := R.retract_subset ha
    have hιa : E.toBase 1 (R.plusLift a) ∈ R.retract := by
      rw [toBase_plusLift_of_mem_retract hR ha]; exact ha
    have := lemma_4_1_7_ii hR hιa
    have hle : LinearMap.range (Lf a : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E 0) ≤
        LinearMap.range (scDeriv R.U R (R.plusLift a) : E 0 →ₗ[ℝ] E 0) := by
      rintro _ ⟨v, rfl⟩
      exact ⟨Q (J (Ring.inverse (B a) v)), (hGapp a haU _).symm⟩
    have hinj : Function.Injective (Lf a : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E 0) :=
      Function.LeftInverse.injective (g := p) (hpL a ha had)
    have hfr : finrank ℝ (LinearMap.range (Lf a : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] E 0)) =
        finrank ℝ (LinearMap.range (scDeriv R.U R (R.plusLift a) : E 0 →ₗ[ℝ] E 0)) := by
      rw [LinearMap.finrank_range_of_inj hinj, hn a ha, finrank_euclideanSpace_fin]
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfr
    have := congrArg (fun S : Submodule ℝ (E 0) => (S : Set (E 0))) heq
    simpa [LinearMap.coe_range] using this
  refine ⟨p, Lf, min δ₁ δ₂, ⟨2 * ‖J‖, by positivity⟩, lt_min hδ₁ hδ₂, ?_, ?_, ?_⟩
  · intro a ha b hb had hbd
    have h := happ a ha b hb (lt_of_lt_of_le had (min_le_right _ _))
      (lt_of_lt_of_le hbd (min_le_right _ _))
    set w := a - b with hw
    change ‖w - Q w‖ ≤ ε₀ * ‖w‖ at h
    have h1 : Q w = J (p (Q w)) := (hJp _ (hQmem w)).symm
    have h2 : p (Q w) = p w - p (w - Q w) := by rw [p.map_sub w (Q w), sub_sub_cancel]
    have h3 : ‖p (Q w)‖ ≤ ‖p w‖ + ‖p‖ * (ε₀ * ‖w‖) := by
      rw [h2]
      calc ‖p w - p (w - Q w)‖ ≤ ‖p w‖ + ‖p (w - Q w)‖ := norm_sub_le _ _
        _ ≤ ‖p w‖ + ‖p‖ * ‖w - Q w‖ := by gcongr; exact p.le_opNorm _
        _ ≤ ‖p w‖ + ‖p‖ * (ε₀ * ‖w‖) := by gcongr
    have h4 : ‖Q w‖ ≤ ‖J‖ * (‖p w‖ + ‖p‖ * (ε₀ * ‖w‖)) := by
      rw [h1]
      exact (J.le_opNorm _).trans (by gcongr)
    have h5 : ‖w‖ ≤ ‖w - Q w‖ + ‖Q w‖ := by
      simpa using norm_add_le (w - Q w) (Q w)
    have h6 : ε₀ * (1 + ‖J‖ * ‖p‖) = 1 / 2 := by rw [hε₀]; field_simp
    have h7 : ‖w‖ ≤ 2 * ‖J‖ * ‖p w‖ := by
      have : ‖w‖ ≤ ε₀ * (1 + ‖J‖ * ‖p‖) * ‖w‖ + ‖J‖ * ‖p w‖ := by nlinarith
      rw [h6] at this; linarith
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact h7
  · intro a ha had
    refine ⟨hpL a ha had, hrange a ha had, fun ε hε => ?_⟩
    have hιa : E.toBase 1 (R.plusLift a) = a := toBase_plusLift_of_mem_retract hR ha
    have hιa' : E.toBase 1 (R.plusLift a) ∈ R.retract := by rw [hιa]; exact ha
    have hpos' : 0 < 1 + ‖Lf a‖ * ‖p‖ := by positivity
    obtain ⟨δ', hδ', happ'⟩ := exists_approx hR hιa' (ε := ε / (1 + ‖Lf a‖ * ‖p‖))
      (by positivity)
    rw [hιa] at happ'
    refine ⟨δ', hδ', fun b hb hbd => ?_⟩
    have h := happ' b hb a ha hbd (by rw [sub_self, norm_zero]; exact hδ')
    set w := b - a with hw
    set D := scDeriv R.U R (R.plusLift a) with hD
    have hDw : D w ∈ range (Lf a) := by rw [hrange a ha had]; exact ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hDw
    have h1 : Lf a (p (D w)) = D w := by rw [← hv, hpL a ha had]
    have h2 : w - Lf a (p w) = (w - D w) - Lf a (p (w - D w)) := by
      rw [p.map_sub w (D w), (Lf a).map_sub, h1]; abel
    rw [h2]
    calc ‖(w - D w) - Lf a (p (w - D w))‖ ≤ ‖w - D w‖ + ‖Lf a (p (w - D w))‖ := norm_sub_le _ _
      _ ≤ ‖w - D w‖ + ‖Lf a‖ * (‖p‖ * ‖w - D w‖) := by
          gcongr
          exact ((Lf a).le_opNorm _).trans (by gcongr; exact p.le_opNorm _)
      _ = (1 + ‖Lf a‖ * ‖p‖) * ‖w - D w‖ := by ring
      _ ≤ (1 + ‖Lf a‖ * ‖p‖) * (ε / (1 + ‖Lf a‖ * ‖p‖) * ‖w‖) := by gcongr
      _ = ε * ‖w‖ := by field_simp
  · rintro a ⟨ha, had⟩
    rw [Metric.mem_ball, dist_eq_norm] at had
    have haU := R.retract_subset ha
    have hsub : R.retract ∩ Metric.ball (E.toBase 1 z) (min δ₁ δ₂) ⊆ R.U := fun b hb =>
      R.retract_subset hb.1
    obtain ⟨u, hu⟩ := hU a ha had
    have hinv : ContinuousWithinAt (fun b => Ring.inverse (B b))
        (R.retract ∩ Metric.ball (E.toBase 1 z) (min δ₁ δ₂)) a := by
      have h1 := NormedRing.inverse_continuousAt u
      rw [hu] at h1
      exact h1.comp_continuousWithinAt ((hBc a haU).mono hsub)
    exact ((hAc a haU).mono hsub).clm_comp hinv

end ScRetraction

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The image of a closed complete set under a map with a Lipschitz inverse is closed. -/
theorem isClosed_image_of_antilipschitzOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] (p : E →L[ℝ] F) {s : Set E}
    (hs : IsClosed s) {K : ℝ≥0} (h : ∀ a ∈ s, ∀ b ∈ s, dist a b ≤ K * dist (p a) (p b)) :
    IsClosed (p '' s) := by
  have : CompleteSpace s := hs.isComplete.completeSpace_coe
  have ha : AntilipschitzWith K (fun a : s => p a) :=
    AntilipschitzWith.of_le_mul_dist fun a b => h a.1 a.2 b.1 b.2
  have hc : UniformContinuous (fun a : s => p a) :=
    p.uniformContinuous.comp uniformContinuous_subtype_val
  have := ha.isClosed_range hc
  rwa [show range (fun a : s => p a) = p '' s from by
    ext v; simp only [mem_range, Subtype.exists, exists_prop, mem_image]] at this

/-- **Graph charts exist** (for the integrals of §9.5, gap G.107): every point of an
`n`-dimensional submanifold `N` of an M-polyfold has an open neighbourhood `V` such that
`N ∩ V` has a graph chart: in a chart of the M-polyfold it is a graph over a subset of `ℝⁿ`,
with a parametrization differentiable for the level-`0` norm. -/
theorem exists_graphChart {N : Set X} {n : ℕ} (hN : P.IsSubmanifoldOfDim N n) {x : X}
    (hx : x ∈ N) : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Nonempty (P.GraphChart n (N ∩ V)) := by
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
  obtain ⟨p, Lf, δ₀, K, hδ₀, hlip, hloc, hcont⟩ := ScRetraction.exists_graphData htp hzt hrank
  obtain ⟨δc, hδc, hclosed⟩ := t.exists_isClosed_retract_inter_closedBall hzt
  rw [hz] at hlip hloc hcont hclosed
  set δ := min δ₀ δc with hδdef
  have hδ : 0 < δ := lt_min hδ₀ hδc
  have hc : ContinuousOn (fun a => ‖φ a - φ x‖) φ.source :=
    (φ.continuousOn_toFun.sub continuousOn_const).norm
  obtain ⟨V', hV', hVe⟩ := (_root_.continuousOn_iff'.1 hc) (Iio δ) isOpen_Iio
  set V := V' ∩ d.toSubData.shrink φ with hVdef
  have hVopen : IsOpen V := hV'.inter (d.toSubData.isOpen_shrink φ)
  have hmemV : ∀ y, y ∈ V ↔ y ∈ d.toSubData.shrink φ ∧ ‖φ y - φ x‖ < δ := by
    intro y
    constructor
    · rintro ⟨hy', hyW⟩
      have hyφ := d.toSubData.shrink_subset_source φ hyW
      have : y ∈ V' ∩ φ.source := ⟨hy', hyφ⟩
      rw [← hVe] at this
      exact ⟨hyW, this.1⟩
    · rintro ⟨hyW, hyd⟩
      have hyφ := d.toSubData.shrink_subset_source φ hyW
      have : y ∈ (fun a => ‖φ a - φ x‖) ⁻¹' Iio δ ∩ φ.source := ⟨hyd, hyφ⟩
      rw [hVe] at this
      exact ⟨this.1, hyW⟩
  have hxW : x ∈ d.toSubData.shrink φ := d.toSubData.mem_shrink φ hx hxV hxφ
  have hxVV : x ∈ V := (hmemV x).2 ⟨hxW, by rw [sub_self, norm_zero]; exact hδ⟩
  -- the points of `N ∩ V`
  have hpt : ∀ y ∈ N ∩ V, y ∈ φ.source ∧ y ∈ d.V ∧ φ y ∈ t.retract ∧ ‖φ y - φ x‖ < δ := by
    rintro y ⟨hyN, hyV⟩
    obtain ⟨hyW, hyd⟩ := (hmemV y).1 hyV
    refine ⟨d.toSubData.shrink_subset_source φ hyW, d.toSubData.shrink_subset_V φ hyW, ?_, hyd⟩
    rw [ht]; exact ⟨y, ⟨hyW, hyN⟩, rfl⟩
  have hδle : ∀ {r : ℝ}, r < δ → r < δ₀ := fun h => lt_of_lt_of_le h (min_le_left _ _)
  have hdist : ∀ y ∈ N ∩ V, ∀ y' ∈ N ∩ V, dist (φ y) (φ y') ≤ K * dist (p (φ y)) (p (φ y')) :=
    fun y hy y' hy' => hlip _ (hpt y hy).2.2.1 _ (hpt y' hy').2.2.1 (hδle (hpt y hy).2.2.2)
      (hδle (hpt y' hy').2.2.2)
  have hinj : InjOn (fun y => p (φ y)) (N ∩ V) := by
    intro y hy y' hy' h
    have h1 := hdist y hy y' hy'
    rw [show p (φ y) = p (φ y') from h, dist_self, mul_zero] at h1
    exact φ.toPartialEquiv.injOn (hpt y hy).1 (hpt y' hy').1 (dist_le_zero.1 h1)
  have himg : (fun y => p (φ y)) '' (N ∩ V) = p '' (t.retract ∩ Metric.ball (φ x) δ) := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ y, ⟨(hpt y hy).2.2.1, by rw [Metric.mem_ball, dist_eq_norm]; exact (hpt y hy).2.2.2⟩,
        rfl⟩
    · rintro ⟨a, ⟨ha, had⟩, rfl⟩
      rw [ht] at ha
      obtain ⟨y, ⟨hyW, hyN⟩, rfl⟩ := ha
      rw [Metric.mem_ball, dist_eq_norm] at had
      exact ⟨y, ⟨hyN, (hmemV y).2 ⟨hyW, had⟩⟩, rfl⟩
  have hmeas : MeasurableSet ((fun y => p (φ y)) '' (N ∩ V)) := by
    rw [himg]
    have hU : t.retract ∩ Metric.ball (φ x) δ =
        ⋃ k : ℕ, t.retract ∩ Metric.closedBall (φ x) (δ - 1 / ((k : ℝ) + 1)) := by
      ext a
      simp only [mem_inter_iff, Metric.mem_ball, mem_iUnion, Metric.mem_closedBall]
      constructor
      · rintro ⟨ha, had⟩
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 had)
        exact ⟨k, ha, by linarith⟩
      · rintro ⟨k, ha, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        exact ⟨ha, by linarith⟩
    rw [hU, image_iUnion]
    refine MeasurableSet.iUnion fun k => IsClosed.measurableSet ?_
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine isClosed_image_of_antilipschitzOn p
      (hclosed _ (by have := min_le_right δ₀ δc; linarith)) (K := K) fun a ha b hb => ?_
    have h1 : ∀ c ∈ t.retract ∩ Metric.closedBall (φ x) (δ - 1 / ((k : ℝ) + 1)),
        ‖c - φ x‖ < δ₀ := fun c hc => by
      have := hc.2
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      exact hδle (by linarith)
    exact hlip a ha.1 b hb.1 (h1 a ha) (h1 b hb)
  have : Nonempty X := ⟨x⟩
  have hq : ∀ y ∈ N ∩ V, Function.invFunOn (fun y => p (φ y)) (N ∩ V) (p (φ y)) = y :=
    fun y hy => hinj.leftInvOn_invFunOn hy
  refine ⟨V, hVopen, hxVV, ⟨{
    φ := φ
    isChart := hφ
    subset_source := fun y hy => (hpt y hy).1
    p := p
    q := Function.invFunOn (fun y => p (φ y)) (N ∩ V)
    q_coord := hq
    L := fun y => Lf (φ y)
    measurableSet_dom := hmeas
    p_L := fun y hy => (hloc _ (hpt y hy).2.2.1 (hδle (hpt y hy).2.2.2)).1
    range_L := fun y hy => ?_
    hasFDerivWithinAt := fun y hy => ?_
    continuousOn_L := ?_ }⟩⟩
  · obtain ⟨hyφ, hyV, hyt, hyd⟩ := hpt y hy
    have h1 := (chartTangent_eq_range hφ d ht hy.1 hyV hyφ).2.2
    rw [levelLift_eq_plusLift hφ d ht hy.1 hyV hyφ] at h1
    rw [(hloc _ hyt (hδle hyd)).2.1, ← h1]
    simp only [chartTangent, submanifoldTangent_inter_isOpen hVopen hy.2]
  · obtain ⟨hyφ, hyV, hyt, hyd⟩ := hpt y hy
    obtain ⟨-, -, happ⟩ := hloc _ hyt (hδle hyd)
    rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hK1 : (0 : ℝ) < K + 1 := by positivity
    obtain ⟨δ', hδ', happ'⟩ := happ (c / (K + 1)) (by positivity)
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (show 0 < δ' / (K + 1) by positivity))]
      with u hu hud
    obtain ⟨y', hy', rfl⟩ := hu
    simp only [hq y' hy', hq y hy]
    rw [Metric.mem_ball, dist_eq_norm] at hud
    have hKd := hdist y' hy' y hy
    rw [dist_eq_norm, dist_eq_norm] at hKd
    set a := φ y with ha
    set b := φ y' with hb
    have hKn : (0 : ℝ) ≤ K := K.2
    have hba : ‖b - a‖ < δ' := by
      calc ‖b - a‖ ≤ K * ‖p b - p a‖ := hKd
        _ ≤ (K + 1) * ‖p b - p a‖ := by gcongr; linarith
        _ < (K + 1) * (δ' / (K + 1)) := mul_lt_mul_of_pos_left hud hK1
        _ = δ' := by field_simp
    have h := happ' b (hpt y' hy').2.2.1 hba
    rw [map_sub] at h
    calc ‖b - a - Lf a (p b - p a)‖ ≤ c / (K + 1) * ‖b - a‖ := h
      _ ≤ c / (K + 1) * (K * ‖p b - p a‖) := by gcongr
      _ = c * (K / (K + 1)) * ‖p b - p a‖ := by ring
      _ ≤ c * 1 * ‖p b - p a‖ := by
          gcongr
          rw [div_le_one hK1]; linarith
      _ = c * ‖p b - p a‖ := by ring
  · refine hcont.comp (φ.continuousOn_toFun.mono fun y hy => (hpt y hy).1) fun y hy => ?_
    exact ⟨(hpt y hy).2.2.1, by
      rw [Metric.mem_ball, dist_eq_norm]; exact hδle (hpt y hy).2.2.2⟩

end MPolyfold

end Polyfold
