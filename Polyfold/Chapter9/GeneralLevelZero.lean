import Polyfold.Chapter9.OrientationRn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9: the level-`0` facts about finite-dimensional submanifolds used in Chapter 9,
for a **general M-polyfold**: **Remark 9.1.1** (p. 402, local constancy of `dim T_mM`),
**Lemmas 9.2.9–9.2.11** (pp. 414–417; 2017: Lemmas 9.6–9.8, the graph representation), the
invariance of domain in **Lemma 9.2.7 (2)** (p. 412; 2017: Lemma 9.5 (2), p. 300), and the
level-`1` continuity used in **Lemma 9.3.4** (p. 423; 2017: Lemma 9.10).  Numbers and pages are
the 2021 text's.

# Finite-dimensional submanifolds of a general M-polyfold at level `0`

## The text, paraphrased

(p. 414) Near a point `x = 0` of a submanifold `M` of the partial quadrant `C`, written as the
image of an sc⁺-retraction, the tangent space `L = T_0M` meets `C` in a set with interior in `L`
(Lemma 9.2.9), `M` is a graph `a + B(a)` over `L` on a cone in `L ∩ C` with `DB(0) = 0`
(Lemma 9.2.10), obtained by inverting `Φ(a) = a + PB(a)` (Lemma 9.2.11).  (p. 402) `dim T_mM` is
locally constant.  (p. 413) A point of `Mᵢ₀` in the interior of the `Σⱼ` it meets is "clearly"
good.

## What is formalized

* **Level-`1` calculus of an sc⁺-retraction** `r` (`ScRetraction.plusLift = 1₀¹ ∘ r`,
  `plusDeriv`): the lift is `C¹` on level `1` (`hasFDerivWithinAt_plusLift`,
  `continuousOn_plusDeriv`, `exists_strict_plusLift`), `ι ∘ plusDeriv = Dr`
  (`toBase_plusDeriv`), and the level-`0` estimates `exists_approx` (`DB(0) = 0`: chords of the
  retract are close to `T = range Dr(z)`) and `exists_strict_range`.
* **Lemma 9.2.9** (`ScRetraction.exists_cone`, via `nonneg_scDeriv`): `x₀ + s B̄_T(h₁, r) ⊆ C`.
* **Lemmas 9.2.10, 9.2.11** (`exists_graph_unif`, `exists_graph`, `exists_graph_ball`): the
  graph over a cone, and over a ball of `T` at interior points; the inversion is Mathlib's
  `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` on `T`.
* **Invariance of domain** (`ScRetraction.eq_of_range_eq`) and **local constancy of the rank**
  (`ScRetraction.eventually_finrank_eq`, via the idempotents `P_z = L_z ∘ ι` of `E₁` and
  `finrank_range_le_of_norm_sub_lt`).
* **In an M-polyfold**: the chart sc⁺-retraction `t` of a submanifold
  (`exists_plusRetraction`, `chartTangent_eq_range`, `levelLift_eq_plusLift`,
  `hasDimAt_finrank`), and
  - `isGraphChartAt_goodDirections`, `hasClassGraphChartAt`: the graph representation at every
    point, with the admissible cone `goodDirections φ x (T_xA)` of each tangent space (gap
    G.97); `isGraphBallAt_of_mem_interior`, `hasGraphBallAt_of_mem_interior`,
    `hasGraphChartAt_of_mem_interior` at interior points, with
    `exists_chart_mem_interior_of_degIndex_eq_zero` (`d_X(x) = 0`);
  - `hasLocallyConstantDimAt` (Remark 9.1.1, gap G.93): the hypothesis
    `HasLocallyConstantDimAt` is no longer needed;
  - `hasDomainInvarianceAt` (gap G.98): the hypothesis `HasDomainInvarianceAt` of
    `lemma_9_2_7_2` is no longer needed;
  - `hasContinuousLevelOneOn` (gap G.100): the hypothesis `HasContinuousLevelOneOn` of
    `lemma_9_3_4_of_hasGraphBallAt` is no longer needed.
  The Chapter 9 theorems that follow are in `GeneralCorollaries.lean`.

## What the text leaves implicit, and the choices made

* The text works at level `0` with "`B` is `C¹`"; the retraction is only sc-smooth, so all
  estimates are proved on level `1` for the lift `1₀¹ ∘ r` and brought down by `ι`; on `T` the
  two norms are equivalent since `T` is finite-dimensional (`lemma_4_1_7_ii`).
* The project's earlier hypothesis `HasGraphChartAt` of `AppendixSlices.lean` (one cone `K` for
  every submanifold through `x`) was stronger than the text needs: the slice arguments use the
  cone of one tangent space at a time, so here the cone is chosen per tangent space
  (`HasClassGraphChartAt`), and this form holds at every point.  `HasGraphChartAt` and
  `HasGraphBallAt` are proved at interior points.
* Definition 9.2.12 (`TMᵢ` smooth submanifolds of `TX`, gap G.99) needs the tangent map of an
  sc⁺-retraction on `TX`; it is treated in `TangentSubmanifoldSmooth.lean`, and Lemma 9.3.4 at
  boundary points in `GeneralBoundaryPoints.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module

noncomputable section

namespace Polyfold

/-! ### The level-`1` calculus of an sc⁺-retraction -/

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)

/-- The lift `1₀¹ ∘ r : U → E¹` of a retraction (sc-smooth into `E¹` when `r` is sc⁺). -/
def plusLift : E 0 → E 1 := E.liftOne ∘ R

/-- The derivative of the lift, `D(1₀¹ ∘ r)(z) : E₀ → E₁`. -/
def plusDeriv (z : E 1) : E 0 →L[ℝ] E 1 := scDeriv (F := E.shift) R.U R.plusLift z

variable {R}

theorem toBase_plusLift (hR : R.IsScPlus) {x : E 0} (hx : x ∈ R.U) :
    E.toBase 1 (R.plusLift x) = R x :=
  Polyfold.IsScPlus.toBase_lift hR hx

theorem plusLift_mem_lvlSet (hR : R.IsScPlus) {x : E 0} (hx : x ∈ R.U) :
    R.plusLift x ∈ E.lvlSet R.U 1 := by
  rw [ScBanach.mem_lvlSet, toBase_plusLift hR hx]; exact R.mapsTo hx

theorem plusLift_toBase_of_mem_retract {z : E 1} (hz : E.toBase 1 z ∈ R.retract) :
    R.plusLift (E.toBase 1 z) = z := by
  change E.liftOne (R (E.toBase 1 z)) = z
  rw [R.apply_eq_self_of_mem_retract hz, E.liftOne_toBase]

theorem toBase_plusLift_of_mem_retract (hR : R.IsScPlus) {a : E 0} (ha : a ∈ R.retract) :
    E.toBase 1 (R.plusLift a) = a := by
  rw [toBase_plusLift hR (R.retract_subset ha), R.apply_eq_self_of_mem_retract ha]

/-- `ι ∘ D(1₀¹ ∘ r)(z) = Dr(z)` (the chain rule for `r = ι ∘ (1₀¹ ∘ r)`). -/
theorem toBase_plusDeriv (hR : R.IsScPlus) {z : E 1} (hz : z ∈ E.lvlSet R.U 1) (v : E 0) :
    E.toBase 1 (R.plusDeriv z v) = scDeriv R.U R z v := by
  have hU := R.isScDomain
  have hgsc : IsScSmooth (E := E) (F := E.shift) R.U R.plusLift := hR.isScSmooth_lift
  have hfg : EqOn (E.shiftIncl 0 ∘ R.plusLift) R R.U := fun y hy => toBase_plusLift hR hy
  have h1 := scDeriv_comp_apply_of_isScDomain hU (isScDomain_univ _) hgsc.isSc1
    ((E.shiftIncl.isScSmooth (isScDomain_univ _)).isSc1) (mapsTo_univ _ _) hz v
  rw [ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _)] at h1
  have hsc : IsScSmooth R.U (E.shiftIncl 0 ∘ R.plusLift) := IsScSmooth.comp hU (isScDomain_univ _)
    (E.shiftIncl.isScSmooth (isScDomain_univ _)) hgsc (mapsTo_univ _ _)
  have hf1 : IsSc1With R.U R (scDeriv R.U (E.shiftIncl 0 ∘ R.plusLift)) :=
    hsc.isSc1.isSc1With_scDeriv.congr hfg
  have h2 := congrArg (fun L : E 0 →L[ℝ] E 0 => L v)
    (IsSc1.scDeriv_eqOn hf1 (hU.uniqueDiffWithinAt 1) hz).symm
  dsimp only at h2
  rw [← h2, ← h1]
  rfl

/-- `D(1₀¹ ∘ r)(z) ∘ Dr(z) = D(1₀¹ ∘ r)(z)` at a point of the retract (`Dr(z)` is a
projection). -/
theorem plusDeriv_scDeriv (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    (v : E 0) : R.plusDeriv z (scDeriv R.U R z v) = R.plusDeriv z v := by
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  apply E.toBase_injective 1
  rw [toBase_plusDeriv hR hzU, toBase_plusDeriv hR hzU]
  exact congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hz)

/-- On the tangent space `T = range Dr(z)`, `ι ∘ D(1₀¹ ∘ r)(z)` is the identity. -/
theorem toBase_plusDeriv_of_mem_range (hR : R.IsScPlus) {z : E 1}
    (hz : E.toBase 1 z ∈ R.retract) {v : E 0} (hv : v ∈ range (scDeriv R.U R z)) :
    E.toBase 1 (R.plusDeriv z v) = v := by
  obtain ⟨u, rfl⟩ := hv
  rw [toBase_plusDeriv hR (R.retract_subset hz)]
  exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hz)

/-- **The lift is differentiable on level `1`** (Proposition 1.16 for the sc¹ map
`1₀¹ ∘ r : U → E¹` on level `0` of `E¹`): `1₀¹ ∘ r ∘ ι : U₁ → E₁` has derivative
`D(1₀¹ ∘ r)(y) ∘ ι` within `U₁` at every `y ∈ U₁`. -/
theorem hasFDerivWithinAt_plusLift (hR : R.IsScPlus) {y : E 1} (hy : y ∈ E.lvlSet R.U 1) :
    HasFDerivWithinAt (R.plusLift ∘ E.toBase 1) ((R.plusDeriv y).comp (E.toBase 1))
      (E.lvlSet R.U 1) y := by
  have hD := (hR.isScSmooth_lift.isSc1 (E := E) (F := E.shift)).isSc1With_scDeriv
  have h := hD.hasFDerivWithinAt_level R.isScDomain (m := 0) hy
  refine (h.congr_fderiv ?_).congr' (fun w _ => ?_) hy
  · ext v
    rw [levelDeriv_zero]
    rfl
  · change R.plusLift (E.toBase 1 w) = levelMap (F := E.shift) R.plusLift 0 (E.incl 0 w)
    rw [levelMap_zero]
    rfl

/-- **The derivative of the lift is continuous on level `1` in the operator norm**
(Proposition 1.16 (1), the compact-open lemma). -/
theorem continuousOn_plusDeriv (hR : R.IsScPlus) :
    ContinuousOn (fun y => (R.plusDeriv y).comp (E.toBase 1)) (E.lvlSet R.U 1) := by
  have hD := (hR.isScSmooth_lift.isSc1 (E := E) (F := E.shift)).isSc1With_scDeriv
  refine (hD.continuousOn_levelDeriv_clm 0).congr fun y _ => ?_
  ext v
  change R.plusDeriv y (E.toBase 1 v) =
    levelDeriv (F := E.shift) (scDeriv (F := E.shift) R.U R.plusLift) 0 y (E.incl 0 v)
  rw [levelDeriv_zero]
  rfl

/-- The lift is continuous from level `0` to `E₁` (the sc⁰ property of `1₀¹ ∘ r`). -/
theorem continuousOn_plusLift (hR : R.IsScPlus) : ContinuousOn R.plusLift R.U :=
  (hR.isScSmooth_lift.isSc1 (E := E) (F := E.shift)).isSc0.continuousOn_base

/-- **Strict differentiability of the lift on level `1`** within `U₁` (mean value inequality on
the convex set `U₁ ∩ B(z, δ)`, `C¹` on level `1`). -/
theorem exists_strict_plusLift (hR : R.IsScPlus) {z : E 1} (hz : z ∈ E.lvlSet R.U 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ y ∈ E.lvlSet R.U 1, ∀ y' ∈ E.lvlSet R.U 1, ‖y - z‖ < δ →
      ‖y' - z‖ < δ → ‖R.plusLift (E.toBase 1 y) - R.plusLift (E.toBase 1 y') -
        R.plusDeriv z (E.toBase 1 (y - y'))‖ ≤ ε * ‖y - y'‖ := by
  obtain ⟨O, K, hO, hK, hUOK⟩ := R.isScDomain.relOpenConvex 1
  have hzO : z ∈ O := (hUOK ▸ hz).1
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO z hzO
  have hc := continuousOn_plusDeriv hR z hz
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := hc ε hε
  refine ⟨min ρ δ₁, lt_min hρ hδ₁, fun y hy y' hy' hyz hy'z => ?_⟩
  set s := Metric.ball z (min ρ δ₁) ∩ E.lvlSet R.U 1 with hsdef
  have hsK : s = Metric.ball z (min ρ δ₁) ∩ K := by
    rw [hsdef, hUOK]
    ext w
    constructor
    · rintro ⟨hw, -, hwK⟩; exact ⟨hw, hwK⟩
    · rintro ⟨hw, hwK⟩
      exact ⟨hw, hρO (Metric.ball_subset_ball (min_le_left _ _) hw), hwK⟩
  have hs : Convex ℝ s := by rw [hsK]; exact (convex_ball z _).inter hK
  have hmem : ∀ w ∈ E.lvlSet R.U 1, ‖w - z‖ < min ρ δ₁ → w ∈ s := fun w hw hwz =>
    ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hwz, hw⟩
  have hder : ∀ w ∈ s, HasFDerivWithinAt (R.plusLift ∘ E.toBase 1)
      ((R.plusDeriv w).comp (E.toBase 1)) s w := fun w hw =>
    (hasFDerivWithinAt_plusLift hR hw.2).mono inter_subset_right
  have hbound : ∀ w ∈ s, ‖(R.plusDeriv w).comp (E.toBase 1) - (R.plusDeriv z).comp (E.toBase 1)‖
      ≤ ε := fun w hw => by
    have := hδ₁c hw.2 (lt_of_lt_of_le (Metric.mem_ball.1 hw.1) (min_le_right _ _))
    rw [dist_eq_norm] at this
    exact this.le
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hder hbound (hmem y' hy' hy'z)
    (hmem y hy hyz)
  simpa using h

/-- **Chords of the retract are approximated by the tangent space** (level `0`): for `a`, `b` in
the retract near `x₀ = ι z`, `‖(a − b) − Dr(z)(a − b)‖₀ ≤ ε ‖a − b‖₀`.  On level `1` this is the
strict differentiability of the lift; the level-`1` norm of the chord is bounded by
`‖D(1₀¹ ∘ r)(z)‖ ‖a − b‖₀`, since the lifted chord is `D(1₀¹ ∘ r)(z)(a − b)` up to a small error. -/
theorem exists_approx (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ a ∈ R.retract, ∀ b ∈ R.retract, ‖a - E.toBase 1 z‖ < δ →
      ‖b - E.toBase 1 z‖ < δ → ‖(a - b) - scDeriv R.U R z (a - b)‖ ≤ ε * ‖a - b‖ := by
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  set L := R.plusDeriv z with hLdef
  set ι := E.toBase 1 with hιdef
  set η : ℝ := min (1 / 2) (ε / (2 * ‖ι‖ * ‖L‖ + 1)) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη2 : η ≤ 1 / 2 := min_le_left _ _
  have hηε : η * (2 * ‖ι‖ * ‖L‖) ≤ ε := by
    have h1 : η ≤ ε / (2 * ‖ι‖ * ‖L‖ + 1) := min_le_right _ _
    have h2 : ε / (2 * ‖ι‖ * ‖L‖ + 1) * (2 * ‖ι‖ * ‖L‖) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg ι, norm_nonneg L, mul_nonneg (norm_nonneg ι) (norm_nonneg L)]
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2
  obtain ⟨δS, hδS, hS⟩ := exists_strict_plusLift hR hzU hη
  have hc := continuousOn_plusLift hR _ (R.retract_subset hz)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδc⟩ := hc δS hδS
  rw [plusLift_toBase_of_mem_retract hz] at hδc
  refine ⟨δ, hδ, fun a ha b hb hax hbx => ?_⟩
  have haU := R.retract_subset ha
  have hbU := R.retract_subset hb
  set pa := R.plusLift a
  set pb := R.plusLift b
  have hιa : ι pa = a := toBase_plusLift_of_mem_retract hR ha
  have hιb : ι pb = b := toBase_plusLift_of_mem_retract hR hb
  have hpaU : pa ∈ E.lvlSet R.U 1 := plusLift_mem_lvlSet hR haU
  have hpbU : pb ∈ E.lvlSet R.U 1 := plusLift_mem_lvlSet hR hbU
  have hpaz : ‖pa - z‖ < δS := by
    have := hδc haU (by rw [dist_eq_norm]; exact hax); rwa [dist_eq_norm] at this
  have hpbz : ‖pb - z‖ < δS := by
    have := hδc hbU (by rw [dist_eq_norm]; exact hbx); rwa [dist_eq_norm] at this
  have h := hS pa hpaU pb hpbU hpaz hpbz
  have hιab : ι (pa - pb) = a - b := by rw [map_sub, hιa, hιb]
  rw [hιab] at h
  have hla : R.plusLift (ι pa) = pa := by rw [hιa]
  have hlb : R.plusLift (ι pb) = pb := by rw [hιb]
  rw [hla, hlb] at h
  -- the level-`1` norm of the chord
  have hnorm : ‖pa - pb‖ ≤ 2 * ‖L‖ * ‖a - b‖ := by
    have h1 : ‖pa - pb‖ ≤ ‖L (a - b)‖ + η * ‖pa - pb‖ := by
      calc ‖pa - pb‖ = ‖(pa - pb - L (a - b)) + L (a - b)‖ := by rw [sub_add_cancel]
        _ ≤ ‖pa - pb - L (a - b)‖ + ‖L (a - b)‖ := norm_add_le _ _
        _ ≤ η * ‖pa - pb‖ + ‖L (a - b)‖ := by gcongr
        _ = _ := by ring
    have h2 : ‖L (a - b)‖ ≤ ‖L‖ * ‖a - b‖ := L.le_opNorm _
    nlinarith [norm_nonneg (pa - pb)]
  have hD : scDeriv R.U R z (a - b) = ι (L (a - b)) := (toBase_plusDeriv hR hzU _).symm
  rw [hD]
  calc ‖(a - b) - ι (L (a - b))‖ = ‖ι (pa - pb - L (a - b))‖ := by
        rw [map_sub ι (pa - pb) (L (a - b)), hιab]
    _ ≤ ‖ι‖ * ‖pa - pb - L (a - b)‖ := ι.le_opNorm _
    _ ≤ ‖ι‖ * (η * ‖pa - pb‖) := by gcongr
    _ ≤ ‖ι‖ * (η * (2 * ‖L‖ * ‖a - b‖)) := by gcongr
    _ = η * (2 * ‖ι‖ * ‖L‖) * ‖a - b‖ := by ring
    _ ≤ ε * ‖a - b‖ := by gcongr

/-- **Strict differentiability along the tangent space** (level `0`): for `c`, `c'` in
`T = range Dr(z)` with `x₀ + c`, `x₀ + c' ∈ U` small,
`‖r(x₀ + c) − r(x₀ + c') − Dr(z)(c − c')‖₀ ≤ ε ‖c − c'‖₀`.  `T` lies in `E₁`
(`c = ι D(1₀¹ ∘ r)(z) c`), and the estimate is the level-`1` one, pushed down by `ι`. -/
theorem exists_strict_range (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ c ∈ range (scDeriv R.U R z), ∀ c' ∈ range (scDeriv R.U R z),
      E.toBase 1 z + c ∈ R.U → E.toBase 1 z + c' ∈ R.U → ‖c‖ < δ → ‖c'‖ < δ →
      ‖R (E.toBase 1 z + c) - R (E.toBase 1 z + c') - scDeriv R.U R z (c - c')‖ ≤
        ε * ‖c - c'‖ := by
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  set L := R.plusDeriv z with hLdef
  set ι := E.toBase 1 with hιdef
  set η : ℝ := ε / (‖ι‖ * ‖L‖ + 1) with hηdef
  have hη : 0 < η := by positivity
  have hηε : ‖ι‖ * (η * ‖L‖) ≤ ε := by
    rw [hηdef, show ‖ι‖ * (ε / (‖ι‖ * ‖L‖ + 1) * ‖L‖) = ε * (‖ι‖ * ‖L‖) / (‖ι‖ * ‖L‖ + 1) by
      ring, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg ι, norm_nonneg L, mul_nonneg (norm_nonneg ι) (norm_nonneg L)]
  obtain ⟨δS, hδS, hS⟩ := exists_strict_plusLift hR hzU hη
  refine ⟨δS / (‖L‖ + 1), by positivity, fun c hc c' hc' hcU hc'U hcδ hc'δ => ?_⟩
  have hιc : ι (L c) = c := toBase_plusDeriv_of_mem_range hR hz hc
  have hιc' : ι (L c') = c' := toBase_plusDeriv_of_mem_range hR hz hc'
  have hy : z + L c ∈ E.lvlSet R.U 1 := by
    rw [ScBanach.mem_lvlSet, map_add, hιc]; exact hcU
  have hy' : z + L c' ∈ E.lvlSet R.U 1 := by
    rw [ScBanach.mem_lvlSet, map_add, hιc']; exact hc'U
  have hLc : ∀ w, ‖w‖ < δS / (‖L‖ + 1) → ‖L w‖ < δS := fun w hw => by
    calc ‖L w‖ ≤ ‖L‖ * ‖w‖ := L.le_opNorm _
      _ ≤ (‖L‖ + 1) * ‖w‖ := by gcongr; linarith
      _ < (‖L‖ + 1) * (δS / (‖L‖ + 1)) := by gcongr
      _ = δS := by field_simp
  have h := hS (z + L c) hy (z + L c') hy' (by rw [add_sub_cancel_left]; exact hLc c hcδ)
    (by rw [add_sub_cancel_left]; exact hLc c' hc'δ)
  have e1 : ι (z + L c) = ι z + c := by rw [map_add, hιc]
  have e2 : ι (z + L c') = ι z + c' := by rw [map_add, hιc']
  have e3 : ι ((z + L c) - (z + L c')) = c - c' := by
    rw [add_sub_add_left_eq_sub, map_sub, hιc, hιc']
  rw [e1, e2, e3] at h
  have e4 : ι (R.plusLift (ι z + c) - R.plusLift (ι z + c') - L (c - c')) =
      R (ι z + c) - R (ι z + c') - scDeriv R.U R z (c - c') := by
    rw [map_sub, map_sub, toBase_plusLift hR hcU, toBase_plusLift hR hc'U,
      toBase_plusDeriv hR hzU]
  rw [← e4]
  have e5 : (z + L c) - (z + L c') = L (c - c') := by rw [add_sub_add_left_eq_sub, map_sub]
  rw [e5] at h
  calc ‖ι (R.plusLift (ι z + c) - R.plusLift (ι z + c') - L (c - c'))‖
      ≤ ‖ι‖ * ‖R.plusLift (ι z + c) - R.plusLift (ι z + c') - L (c - c')‖ := ι.le_opNorm _
    _ ≤ ‖ι‖ * (η * ‖L (c - c')‖) := by gcongr
    _ ≤ ‖ι‖ * (η * (‖L‖ * ‖c - c'‖)) := by gcongr; exact L.le_opNorm _
    _ = ‖ι‖ * (η * ‖L‖) * ‖c - c'‖ := by ring
    _ ≤ ε * ‖c - c'‖ := by gcongr

/-- **The graph representation over a cone in the tangent space** (the content of 2021 Lemmas
9.2.10 and 9.2.11, pp. 414–417, at a point `x₀ = ι z` of the image of an sc⁺-retraction): let
`T = range Dr(z)`, `Q` a continuous projection onto `T`, and `h₀ ∈ T` such that
`x₀ + s B̄_T(h₀, r) ⊆ C`.  Then for small `t > 0` some point `a` of the retract has
`Q(a − x₀) = t h₀` and `‖a − x₀ − t h₀‖₀ ≤ ε t`.  The point is `a = r(x₀ + c)` with `c ∈ T`
solving `Q(r(x₀ + c) − x₀) = t h₀` on the ball `B̄_T(t h₀, r t)`, which lies in `U`
(`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`, with the estimate
`exists_strict_range`).  The time `t₀` is uniform over the directions `h₀` with `‖h₀‖ ≤ 1` and
the given `r`, `s`. -/
theorem exists_graph_unif (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    (Q : E 0 →L[ℝ] E 0) (hQT : ∀ v, Q v ∈ range (scDeriv R.U R z))
    (hQid : ∀ v ∈ range (scDeriv R.U R z), Q v = v) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ > 0, ∀ h₀ ∈ range (scDeriv R.U R z), ‖h₀‖ ≤ 1 →
      (∀ h' ∈ range (scDeriv R.U R z), ‖h' - h₀‖ ≤ r → E.toBase 1 z + s • h' ∈ C) →
      ∀ t, 0 < t → t < t₀ → ∃ a ∈ R.retract,
        Q (a - E.toBase 1 z) = t • h₀ ∧ ‖(a - E.toBase 1 z) - t • h₀‖ ≤ ε * t := by
  classical
  set D := scDeriv R.U R z with hDdef
  set x₀ := E.toBase 1 z with hx₀def
  set N : Submodule ℝ (E 0) := LinearMap.range (D : E 0 →ₗ[ℝ] E 0) with hNdef
  have hmemN : ∀ v, v ∈ N ↔ v ∈ range D := fun v => by rw [hNdef, LinearMap.mem_range]; rfl
  have : FiniteDimensional ℝ N := lemma_4_1_7_ii hR hz
  have : CompleteSpace N := FiniteDimensional.complete ℝ N
  have hDfix : ∀ v ∈ range D, D v = v := by
    rintro _ ⟨u, rfl⟩
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hz)
  have hx₀U : x₀ ∈ R.U := R.retract_subset hz
  have hRx₀ : R x₀ = x₀ := R.apply_eq_self_of_mem_retract hz
  obtain ⟨O, hO, hUO⟩ := R.relOpen.relOpen
  have hCc : Convex ℝ C := R.relOpen.isPartialQuadrant.convex
  have hx₀C : x₀ ∈ C := (hUO ▸ hx₀U).2
  obtain ⟨ρO, hρO, hρOsub⟩ := Metric.isOpen_iff.1 hO x₀ (hUO ▸ hx₀U).1
  -- the constants
  set q : ℝ := ‖Q‖ + 1 with hqdef
  have hq : 0 < q := by positivity
  set M : ℝ := r + 2 with hMdef
  have hM : 0 < M := by positivity
  set η : ℝ := min (1 / (2 * q)) (min (r / (2 * q * M)) (ε / (q * M))) with hηdef
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη1 : q * η ≤ 1 / 2 := by
    have : η ≤ 1 / (2 * q) := min_le_left _ _
    calc q * η ≤ q * (1 / (2 * q)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hη2 : q * η * M ≤ r / 2 := by
    have : η ≤ r / (2 * q * M) := (min_le_right _ _).trans (min_le_left _ _)
    calc q * η * M ≤ q * (r / (2 * q * M)) * M := by gcongr
      _ = r / 2 := by field_simp
  have hη3 : q * η * M ≤ ε := by
    have : η ≤ ε / (q * M) := (min_le_right _ _).trans (min_le_right _ _)
    calc q * η * M ≤ q * (ε / (q * M)) * M := by gcongr
      _ = ε := by field_simp
  have hQq : ‖Q‖ ≤ q := by rw [hqdef]; linarith
  obtain ⟨δK, hδK, hK⟩ := exists_strict_range hR hz hη
  refine ⟨min s (min (δK / M) (ρO / M)), lt_min hs (lt_min (by positivity) (by positivity)),
    fun h₀ hh₀ hh₀1 hcone t ht htt => ?_⟩
  have hts : t < s := lt_of_lt_of_le htt (min_le_left _ _)
  have htδ : t * M < δK := by
    have : t < δK / M := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_left _ _))
    rwa [lt_div_iff₀ hM] at this
  have htρ : t * M < ρO := by
    have : t < ρO / M := lt_of_lt_of_le htt ((min_le_right _ _).trans (min_le_right _ _))
    rwa [lt_div_iff₀ hM] at this
  -- the ball `B̄_T(t h₀, r t)`
  have hh₀N : h₀ ∈ N := (hmemN h₀).2 hh₀
  set b : N := t • (⟨h₀, hh₀N⟩ : N) with hbdef
  have hbcoe : (b : E 0) = t • h₀ := rfl
  set B := Metric.closedBall b (r * t) with hBdef
  have hBnorm : ∀ c ∈ B, ‖(c : E 0)‖ < t * M := fun c hc => by
    have h1 : ‖(c : E 0) - t • h₀‖ ≤ r * t := by
      rw [← hbcoe, ← Submodule.coe_sub, ← Submodule.coe_norm, ← dist_eq_norm]; exact hc
    calc ‖(c : E 0)‖ = ‖((c : E 0) - t • h₀) + t • h₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖(c : E 0) - t • h₀‖ + ‖t • h₀‖ := norm_add_le _ _
      _ ≤ r * t + t * ‖h₀‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.le]; linarith
      _ < t * M := by rw [hMdef]; nlinarith [mul_le_mul_of_nonneg_left hh₀1 ht.le]
  have hBU : ∀ c ∈ B, x₀ + (c : E 0) ∈ R.U := fun c hc => by
    rw [hUO]
    refine ⟨hρOsub ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (hBnorm c hc).trans htρ
    · have hcN : (c : E 0) ∈ range D := (hmemN _).1 c.2
      have hh' : t⁻¹ • (c : E 0) ∈ range D := (hmemN _).1 (N.smul_mem _ c.2)
      have hdist : ‖t⁻¹ • (c : E 0) - h₀‖ ≤ r := by
        have h1 : ‖(c : E 0) - t • h₀‖ ≤ r * t := by
          rw [← hbcoe, ← Submodule.coe_sub, ← Submodule.coe_norm, ← dist_eq_norm]; exact hc
        have h2 : t⁻¹ • (c : E 0) - h₀ = t⁻¹ • ((c : E 0) - t • h₀) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
        rw [h2, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
        calc t⁻¹ * ‖(c : E 0) - t • h₀‖ ≤ t⁻¹ * (r * t) := by gcongr
          _ = r := by field_simp
      have hmem := hcone _ hh' hdist
      have hcomb := hCc.add_smul_sub_mem hx₀C hmem (t := t / s)
        ⟨by positivity, by rw [div_le_one hs]; exact hts.le⟩
      have e : x₀ + (t / s) • ((x₀ + s • t⁻¹ • (c : E 0)) - x₀) = x₀ + (c : E 0) := by
        rw [add_sub_cancel_left, smul_smul, smul_smul]
        congr 1
        rw [show t / s * s * t⁻¹ = 1 by field_simp, one_smul]
      rwa [e] at hcomb
  -- the map `f(c) = Q(r(x₀ + c) − x₀)` on `T`
  let f : N → N := fun c => ⟨Q (R (x₀ + c) - x₀), (hmemN _).2 (hQT _)⟩
  have hfcoe : ∀ c, (f c : E 0) = Q (R (x₀ + c) - x₀) := fun _ => rfl
  have hQD : ∀ c : N, Q (D c) = c := fun c => by
    rw [hDfix _ ((hmemN _).1 c.2), hQid _ ((hmemN _).1 c.2)]
  have happrox : ApproximatesLinearOn f (ContinuousLinearMap.id ℝ N) B
      ⟨‖Q‖ * η, by positivity⟩ := by
    intro c₁ hc₁ c₂ hc₂
    have hk := hK c₁ ((hmemN _).1 c₁.2) c₂ ((hmemN _).1 c₂.2) (hBU c₁ hc₁) (hBU c₂ hc₂)
      ((hBnorm c₁ hc₁).trans htδ) ((hBnorm c₂ hc₂).trans htδ)
    rw [Submodule.coe_norm, Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_sub,
      ContinuousLinearMap.id_apply, hfcoe, hfcoe, Submodule.coe_sub]
    have e : Q (R (x₀ + c₁) - x₀) - Q (R (x₀ + c₂) - x₀) - ((c₁ : E 0) - c₂) =
        Q (R (x₀ + c₁) - R (x₀ + c₂) - D ((c₁ : E 0) - c₂)) := by
      have := hQD (c₁ - c₂)
      rw [Submodule.coe_sub] at this
      rw [map_sub Q (R (x₀ + c₁) - R (x₀ + c₂)), this, map_sub, map_sub, map_sub]
      abel
    rw [e]
    change _ ≤ ‖Q‖ * η * _
    calc ‖Q (R (x₀ + c₁) - R (x₀ + c₂) - D ((c₁ : E 0) - c₂))‖
        ≤ ‖Q‖ * ‖R (x₀ + c₁) - R (x₀ + c₂) - D ((c₁ : E 0) - c₂)‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (η * ‖(c₁ : E 0) - c₂‖) := by gcongr
      _ = ‖Q‖ * η * ‖(c₁ : E 0) - c₂‖ := by ring
  let finv : (ContinuousLinearMap.id ℝ N).NonlinearRightInverse :=
    ⟨fun y => y, 1, fun y => by simp, fun y => rfl⟩
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse finv
    (by positivity : (0 : ℝ) ≤ r * t) subset_rfl
  have hfinv : ((finv.nnnorm : ℝ))⁻¹ = 1 := by simp [finv]
  rw [hfinv] at hsurj
  -- the base point is close to its image
  have hfb : dist b (f b) ≤ (1 - ‖Q‖ * η) * (r * t) := by
    have hk := hK (b : E 0) ((hmemN _).1 b.2) 0 ⟨0, map_zero D⟩ (hBU b (Metric.mem_closedBall_self
      (by positivity))) (by rw [add_zero]; exact hx₀U)
      ((hBnorm b (Metric.mem_closedBall_self (by positivity))).trans htδ)
      (by rw [norm_zero]; exact hδK)
    rw [add_zero, hRx₀, sub_zero] at hk
    rw [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub, hfcoe]
    have e : (b : E 0) - Q (R (x₀ + b) - x₀) = -Q (R (x₀ + b) - x₀ - D b) := by
      rw [map_sub Q (R (x₀ + b) - x₀), hQD b]; abel
    rw [e, norm_neg]
    calc ‖Q (R (x₀ + b) - x₀ - D b)‖ ≤ ‖Q‖ * ‖R (x₀ + b) - x₀ - D b‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * (η * ‖(b : E 0)‖) := by gcongr
      _ ≤ q * (η * (t * M)) := by
          gcongr
          rw [hbcoe, norm_smul, Real.norm_of_nonneg ht.le, hMdef]
          nlinarith [mul_le_mul_of_nonneg_left hh₀1 ht.le]
      _ = q * η * M * t := by ring
      _ ≤ r / 2 * t := by gcongr
      _ ≤ (1 - ‖Q‖ * η) * (r * t) := by
          have : ‖Q‖ * η ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hQq hη.le).trans hη1
          have h := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ 1 - ‖Q‖ * η by linarith)
            (by positivity : (0 : ℝ) ≤ r * t)
          linarith
  obtain ⟨c, hcB, hfc⟩ := hsurj (show b ∈ Metric.closedBall (f b) ((1 - ‖Q‖ * η) * (r * t)) by
    rw [Metric.mem_closedBall]; exact hfb)
  -- the point `a = r(x₀ + c)`
  have hcU := hBU c hcB
  have hQa : Q (R (x₀ + c) - x₀) = t • h₀ := by rw [← hfcoe, hfc]; exact hbcoe
  refine ⟨R (x₀ + c), R.apply_mem_retract hcU, hQa, ?_⟩
  have hk := hK (c : E 0) ((hmemN _).1 c.2) 0 ⟨0, map_zero D⟩ hcU (by rw [add_zero]; exact hx₀U)
    ((hBnorm c hcB).trans htδ) (by rw [norm_zero]; exact hδK)
  rw [add_zero, hRx₀, sub_zero, hDfix _ ((hmemN _).1 c.2)] at hk
  set e := R (x₀ + c) - x₀ - c with hedef
  have hQe : (c : E 0) + Q e = t • h₀ := by
    rw [← hQa, hedef, map_sub Q (R (x₀ + c) - x₀), hQid _ ((hmemN _).1 c.2)]; abel
  have e1 : R (x₀ + c) - x₀ - t • h₀ = e - Q e := by rw [← hQe, hedef]; abel
  rw [e1]
  calc ‖e - Q e‖ ≤ ‖e‖ + ‖Q e‖ := norm_sub_le _ _
    _ ≤ ‖e‖ + ‖Q‖ * ‖e‖ := by gcongr; exact Q.le_opNorm _
    _ ≤ q * ‖e‖ := by rw [hqdef]; nlinarith [norm_nonneg e]
    _ ≤ q * (η * ‖(c : E 0)‖) := by gcongr
    _ ≤ q * (η * (t * M)) := by gcongr; exact (hBnorm c hcB).le
    _ = q * η * M * t := by ring
    _ ≤ ε * t := by gcongr

/-- **The graph representation over a cone** (2021 Lemmas 9.2.10, 9.2.11, pp. 414–417), for one
direction `h₀ ∈ T` with `x₀ + s B̄_T(h₀, r) ⊆ C` (`exists_graph_unif` after rescaling `h₀`). -/
theorem exists_graph (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    (Q : E 0 →L[ℝ] E 0) (hQT : ∀ v, Q v ∈ range (scDeriv R.U R z))
    (hQid : ∀ v ∈ range (scDeriv R.U R z), Q v = v) {h₀ : E 0}
    (hh₀ : h₀ ∈ range (scDeriv R.U R z)) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hcone : ∀ h' ∈ range (scDeriv R.U R z), ‖h' - h₀‖ ≤ r → E.toBase 1 z + s • h' ∈ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → ∃ a ∈ R.retract,
      Q (a - E.toBase 1 z) = t • h₀ ∧ ‖(a - E.toBase 1 z) - t • h₀‖ ≤ ε * t := by
  set lam := ‖h₀‖ + 1 with hlamdef
  have hlam : 0 < lam := by positivity
  obtain ⟨t₀, ht₀, hgr⟩ := exists_graph_unif hR hz Q hQT hQid (r := r / lam) (s := s * lam)
    (by positivity) (by positivity) (ε := ε / lam) (by positivity)
  refine ⟨t₀ / lam, by positivity, fun t ht htt => ?_⟩
  have hh₀' : lam⁻¹ • h₀ ∈ range (scDeriv R.U R z) := by
    obtain ⟨u, hu⟩ := hh₀; exact ⟨lam⁻¹ • u, by rw [map_smul, hu]⟩
  have hnorm : ‖lam⁻¹ • h₀‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le), inv_mul_le_iff₀ hlam, hlamdef]
    linarith
  have hcone' : ∀ h' ∈ range (scDeriv R.U R z), ‖h' - lam⁻¹ • h₀‖ ≤ r / lam →
      E.toBase 1 z + (s * lam) • h' ∈ C := fun h' hh' hd => by
    have hmem : lam • h' ∈ range (scDeriv R.U R z) := by
      obtain ⟨u, hu⟩ := hh'; exact ⟨lam • u, by rw [map_smul, hu]⟩
    have := hcone _ hmem (by
      have e : lam • h' - h₀ = lam • (h' - lam⁻¹ • h₀) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
      rw [e, norm_smul, Real.norm_of_nonneg hlam.le]
      calc lam * ‖h' - lam⁻¹ • h₀‖ ≤ lam * (r / lam) := by gcongr
        _ = r := by field_simp)
    rwa [smul_smul] at this
  have htlam : 0 < lam * t := by positivity
  obtain ⟨a, ha, hQa, hest⟩ := hgr _ hh₀' hnorm hcone' (lam * t) htlam
    (by rwa [lt_div_iff₀ hlam, mul_comm] at htt)
  have e : (lam * t) • (lam⁻¹ • h₀) = t • h₀ := by
    rw [smul_smul, show lam * t * lam⁻¹ = t by field_simp]
  rw [e] at hQa hest
  refine ⟨a, ha, hQa, hest.trans (le_of_eq ?_)⟩
  field_simp

/-- **The graph representation over a full ball of `T`** (2021 Lemmas 9.2.10, 9.2.11 at a point
where every direction is admissible): if `B(x₀, ρ) ⊆ C`, every small `u ∈ T` is `Q(a − x₀)` for
a point `a` of the retract with `‖a − x₀ − u‖₀ ≤ ε ‖u‖` (`exists_graph_unif` with `h₀ = u/‖u‖`,
`r = 1`, `s = ρ/3`). -/
theorem exists_graph_ball (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    (Q : E 0 →L[ℝ] E 0) (hQT : ∀ v, Q v ∈ range (scDeriv R.U R z))
    (hQid : ∀ v ∈ range (scDeriv R.U R z), Q v = v) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (E.toBase 1 z) ρ ⊆ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ > 0, ∀ u ∈ range (scDeriv R.U R z), ‖u‖ < r₀ → ∃ a ∈ R.retract,
      Q (a - E.toBase 1 z) = u ∧ ‖(a - E.toBase 1 z) - u‖ ≤ ε * ‖u‖ := by
  obtain ⟨t₀, ht₀, hgr⟩ := exists_graph_unif hR hz Q hQT hQid one_pos
    (by positivity : (0 : ℝ) < ρ / 3) hε
  refine ⟨t₀, ht₀, fun u hu hut => ?_⟩
  by_cases hu0 : u = 0
  · refine ⟨E.toBase 1 z, hz, ?_, ?_⟩ <;> simp [hu0]
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hh₀ : ‖u‖⁻¹ • u ∈ range (scDeriv R.U R z) := by
    obtain ⟨v, hv⟩ := hu; exact ⟨‖u‖⁻¹ • v, by rw [map_smul, hv]⟩
  have hnorm : ‖‖u‖⁻¹ • u‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hun.ne']
  have hcone : ∀ h' ∈ range (scDeriv R.U R z), ‖h' - ‖u‖⁻¹ • u‖ ≤ 1 →
      E.toBase 1 z + (ρ / 3) • h' ∈ C := fun h' _ hd => hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    have : ‖h'‖ ≤ 2 := by
      calc ‖h'‖ = ‖(h' - ‖u‖⁻¹ • u) + ‖u‖⁻¹ • u‖ := by rw [sub_add_cancel]
        _ ≤ ‖h' - ‖u‖⁻¹ • u‖ + ‖‖u‖⁻¹ • u‖ := norm_add_le _ _
        _ ≤ 2 := by linarith
    nlinarith)
  obtain ⟨a, ha, hQa, hest⟩ := hgr _ hh₀ hnorm hcone ‖u‖ hun hut
  rw [smul_smul, mul_inv_cancel₀ hun.ne', one_smul] at hQa hest
  exact ⟨a, ha, hQa, hest⟩

/-- **The derivative points into `C` along level-`1` directions** (the step of 2021 Lemma 9.2.9,
p. 414, that `T_0M ∩ C` is large): if a continuous linear `ℓ` is `≥ 0` on `C` and vanishes at
`x₀ = ι z`, then `ℓ(Dr(z)(ι c)) ≥ 0` for every `c ∈ E₁` with `x₀ + ι c ∈ C`.  Indeed
`r(x₀ + τ ι c) ∈ C`, and `r(x₀ + τ ι c) = x₀ + τ Dr(z)(ι c) + o(τ)` by the level-`1`
differentiability of the lift (`exists_strict_plusLift`). -/
theorem nonneg_scDeriv (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    (ℓ : E 0 →L[ℝ] ℝ) (hℓ : ∀ e ∈ C, 0 ≤ ℓ e) (hℓ0 : ℓ (E.toBase 1 z) = 0) {c : E 1}
    (hc : E.toBase 1 z + E.toBase 1 c ∈ C) : 0 ≤ ℓ (scDeriv R.U R z (E.toBase 1 c)) := by
  by_contra hneg
  push Not at hneg
  set x₀ := E.toBase 1 z with hx₀def
  set κ := -ℓ (scDeriv R.U R z (E.toBase 1 c)) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  obtain ⟨O, hO, hUO⟩ := R.relOpen.relOpen
  have hx₀U : x₀ ∈ R.U := R.retract_subset hz
  have hx₀C : x₀ ∈ C := (hUO ▸ hx₀U).2
  obtain ⟨ρO, hρO, hρOsub⟩ := Metric.isOpen_iff.1 hO x₀ (hUO ▸ hx₀U).1
  set K := ‖ℓ‖ * ‖E.toBase 1‖ * ‖c‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  obtain ⟨δ, hδ, hstr⟩ := exists_strict_plusLift hR hzU (show 0 < κ / (2 * K) by positivity)
  obtain ⟨τ, ⟨h1, h2, h3⟩, hτ⟩ := (((eventually_mul_lt (C := ‖c‖) hδ).and
    ((eventually_mul_lt (C := ‖E.toBase 1 c‖) hρO).and
      (eventually_mul_lt (C := 1) one_pos))).and self_mem_nhdsWithin).exists
  have hτ0 : (0 : ℝ) < τ := hτ
  have hτ1 : τ ≤ 1 := by linarith
  have hyC : x₀ + τ • E.toBase 1 c ∈ C := by
    have := (R.relOpen.isPartialQuadrant.convex).add_smul_sub_mem hx₀C hc ⟨hτ0.le, hτ1⟩
    rwa [add_sub_cancel_left] at this
  have hyO : x₀ + τ • E.toBase 1 c ∈ O := hρOsub (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hτ0.le]; exact h2)
  have hyU : z + τ • c ∈ E.lvlSet R.U 1 := by
    rw [ScBanach.mem_lvlSet, map_add, map_smul, hUO]; exact ⟨hyO, hyC⟩
  have hst := hstr _ hyU _ hzU (by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]; exact h1)
    (by rw [sub_self, norm_zero]; exact hδ)
  rw [add_sub_cancel_left, plusLift_toBase_of_mem_retract hz, map_smul, map_smul] at hst
  -- apply `ι`
  have hι : ‖R (E.toBase 1 (z + τ • c)) - x₀ - τ • scDeriv R.U R z (E.toBase 1 c)‖ ≤
      ‖E.toBase 1‖ * (κ / (2 * K) * (τ * ‖c‖)) := by
    have e : R (E.toBase 1 (z + τ • c)) - x₀ - τ • scDeriv R.U R z (E.toBase 1 c) =
        E.toBase 1 (R.plusLift (E.toBase 1 (z + τ • c)) - z -
          τ • R.plusDeriv z (E.toBase 1 c)) := by
      rw [map_sub, map_sub, map_smul, toBase_plusLift hR hyU, toBase_plusDeriv hR hzU]
    rw [e]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    gcongr
    rw [norm_smul, Real.norm_of_nonneg hτ0.le] at hst
    exact hst
  have hmem : R (E.toBase 1 (z + τ • c)) ∈ C := by
    have := R.mapsTo hyU
    rw [hUO] at this; exact this.2
  have hpos := hℓ _ hmem
  have hsplit : ℓ (R (E.toBase 1 (z + τ • c))) = ℓ x₀ + τ * ℓ (scDeriv R.U R z (E.toBase 1 c)) +
      ℓ (R (E.toBase 1 (z + τ • c)) - x₀ - τ • scDeriv R.U R z (E.toBase 1 c)) := by
    rw [map_sub, map_sub, map_smul, smul_eq_mul]; ring
  have hbound : ℓ (R (E.toBase 1 (z + τ • c)) - x₀ - τ • scDeriv R.U R z (E.toBase 1 c)) ≤
      τ * (κ / 2) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖ℓ‖ * ‖R (E.toBase 1 (z + τ • c)) - x₀ - τ • scDeriv R.U R z (E.toBase 1 c)‖
        ≤ ‖ℓ‖ * (‖E.toBase 1‖ * (κ / (2 * K) * (τ * ‖c‖))) := by gcongr
      _ = τ * (κ / 2) * ((‖ℓ‖ * ‖E.toBase 1‖ * ‖c‖) / K) := by
          field_simp
      _ ≤ τ * (κ / 2) * 1 := by
          gcongr
          rw [div_le_one hK, hKdef]; linarith
      _ = τ * (κ / 2) := mul_one _
  rw [hsplit, hℓ0] at hpos
  have : τ * ℓ (scDeriv R.U R z (E.toBase 1 c)) = -(τ * κ) := by rw [hκdef]; ring
  rw [this] at hpos
  nlinarith

/-- **2021 Lemma 9.2.9** (p. 414; 2017: Lemma 9.6) for the image of an sc⁺-retraction, in the
form used by the graph representation: at `x₀ = ι z` of the retract, with `T = range Dr(z)`,
some `h₁ ∈ T` and `r, s > 0` have `x₀ + s B̄_T(h₁, r) ⊆ C`.  With `C = T₀⁻¹([0,∞)ⁿ ⊕ W)`, the
coordinates `ℓᵢ` and `c₁ ∈ E₁` with `ℓᵢ(ι c₁) = 1`, take `h₁ = Dr(z)(ι c₁)`: for
`h' = h₁ + v`, `v ∈ T` small, `h' = Dr(z)(ι (c₁ + L v))` (`L` the lift of `Dr(z)`), so
`ℓᵢ(h') ≥ 0` for the coordinates vanishing at `x₀` (`nonneg_scDeriv`); the others are positive
at `x₀`. -/
theorem exists_cone (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) :
    ∃ h₁ ∈ range (scDeriv R.U R z), ∃ r > (0 : ℝ), ∃ s > (0 : ℝ),
      ∀ h' ∈ range (scDeriv R.U R z), ‖h' - h₁‖ ≤ r → E.toBase 1 z + s • h' ∈ C := by
  classical
  obtain ⟨n, W, T, hC⟩ := R.relOpen.isPartialQuadrant
  set x₀ := E.toBase 1 z with hx₀def
  set D := scDeriv R.U R z with hDdef
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  have hDfix : ∀ v ∈ range D, D v = v := by
    rintro _ ⟨u, rfl⟩
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hz)
  -- the coordinates
  let ℓ : Fin n → E 0 →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T 0 : E 0 →L[ℝ] _))
  have hℓapp : ∀ i e, ℓ i e = (T 0 e).1 i := fun _ _ => rfl
  have hmemC : ∀ e, e ∈ C ↔ ∀ i, 0 ≤ ℓ i e := fun e => by rw [hC]; exact Iff.rfl
  set B := ‖(T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0)‖ with hBdef
  have hℓB : ∀ i e, |ℓ i e| ≤ B * ‖e‖ := fun i e => by
    rw [hℓapp]
    calc |(T 0 e).1 i| = ‖(T 0 e).1 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(T 0 e).1‖ := norm_le_pi_norm _ i
      _ ≤ ‖T 0 e‖ := norm_fst_le _
      _ ≤ B * ‖e‖ :=
        (T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0).le_opNorm e
  -- the vector `c₁`
  set c₁ : E 1 := (T 1).symm (((fun _ => 1 : Fin n → ℝ), 0) : (Fin n → ℝ) × W 1) with hc₁def
  have hℓc₁ : ∀ i, ℓ i (E.toBase 1 c₁) = 1 := fun i => by
    rw [hℓapp, hc₁def, ScIso.symm_toBase_comm, ContinuousLinearEquiv.apply_symm_apply,
      ScBanach.prod_toBase]
    change (ScBanach.const (Fin n → ℝ)).toBase 1 (fun _ => 1 : Fin n → ℝ) i = 1
    rw [ScBanach.const_toBase]
  have hx₀C : x₀ ∈ C := by
    obtain ⟨O, -, hUO⟩ := R.relOpen.relOpen
    exact (hUO ▸ R.retract_subset hz).2
  set h₁ := D (E.toBase 1 c₁) with hh₁def
  set r : ℝ := 1 / (2 * (B + 1)) with hrdef
  have hr : 0 < r := by positivity
  have hBr : B * r ≤ 1 / 2 := by
    rw [hrdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg (T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0)]
  -- the coordinates vanishing at `x₀` are `≥ 0` on the ball
  have hact : ∀ h' ∈ range D, ‖h' - h₁‖ ≤ r → ∀ i, ℓ i x₀ = 0 → 0 ≤ ℓ i h' := by
    intro h' hh' hdist i hi
    have hv : h' - h₁ ∈ range D := by
      obtain ⟨u, rfl⟩ := hh'
      exact ⟨u - E.toBase 1 c₁, by rw [map_sub]⟩
    set v := h' - h₁ with hvdef
    have hιL : E.toBase 1 (R.plusDeriv z v) = v := toBase_plusDeriv_of_mem_range hR hz hv
    have hc : x₀ + E.toBase 1 (c₁ + R.plusDeriv z v) ∈ C := by
      rw [hmemC]
      intro k
      rw [map_add, map_add, hιL, map_add, hℓc₁]
      have h1 : 0 ≤ ℓ k x₀ := (hmemC x₀).1 hx₀C k
      have h2 := hℓB k v
      have h3 : B * ‖v‖ ≤ B * r := by gcongr
      have h4 := neg_abs_le (ℓ k v)
      linarith
    have := nonneg_scDeriv hR hz (ℓ i) (fun e he => (hmemC e).1 he i) hi hc
    rwa [map_add, map_add, hιL, ← hDdef, hDfix v hv, ← hh₁def, add_sub_cancel] at this
  -- the scale `s`
  set M := ‖h₁‖ + r with hMdef
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i, ℓ i x₀ = 0 ∨ s * (B * M) < ℓ i x₀ := by
    rw [Filter.eventually_all]
    intro i
    rcases (le_iff_eq_or_lt.1 ((hmemC x₀).1 hx₀C i)) with h | h
    · exact Filter.Eventually.of_forall fun _ => Or.inl h.symm
    · exact (eventually_mul_lt h).mono fun _ hs => Or.inr hs
  obtain ⟨s, hs, hs0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hs0 : (0 : ℝ) < s := hs0
  refine ⟨h₁, ⟨E.toBase 1 c₁, rfl⟩, r, hr, s, hs0, fun h' hh' hdist => ?_⟩
  rw [hmemC]
  intro i
  rw [map_add, map_smul, smul_eq_mul]
  rcases hs i with h | h
  · rw [h, zero_add]; exact mul_nonneg hs0.le (hact h' hh' hdist i h)
  · have hnorm : ‖h'‖ ≤ M := by
      calc ‖h'‖ = ‖(h' - h₁) + h₁‖ := by rw [sub_add_cancel]
        _ ≤ ‖h' - h₁‖ + ‖h₁‖ := norm_add_le _ _
        _ ≤ M := by rw [hMdef]; linarith
    have h1 := neg_abs_le (ℓ i h')
    have h2 := hℓB i h'
    have h3 : B * ‖h'‖ ≤ B * M := by gcongr
    have h4 : s * (B * ‖h'‖) ≤ s * (B * M) := by gcongr
    nlinarith

/-- **Invariance of domain for two sc⁺-retracts with the same tangent space** (the content of
2021 Lemma 9.2.7(2), p. 412, read for two retracts through `x₀ = ι z`): if
`range Dr₁(z) = range Dr₂(z)`, then near `x₀` every `b` of the first retract with
`a = r₂(b)` in the first retract is fixed by `r₂`.  On level `1`, with `u = â − b̂` the
difference of the lifts, `w = L₁(a − b)` and `L₂(ι w) = w`: `‖u − w‖₁ ≤ η‖u‖₁` and
`‖L₂(ι u)‖₁ ≤ η‖u‖₁` (because `r₂(a) = r₂(b)`), so `‖u‖₁ ≤ η(2 + ‖L₂‖‖ι‖)‖u‖₁` and `u = 0`. -/
theorem eq_of_range_eq {R₁ R₂ : ScRetraction E C} (h₁ : R₁.IsScPlus) (h₂ : R₂.IsScPlus)
    {z : E 1} (hz₁ : E.toBase 1 z ∈ R₁.retract) (hz₂ : E.toBase 1 z ∈ R₂.retract)
    (hT : range (scDeriv R₁.U R₁ z) = range (scDeriv R₂.U R₂ z)) :
    ∃ δ > 0, ∀ b ∈ R₁.retract, b ∈ R₂.U → R₂ b ∈ R₁.retract →
      ‖b - E.toBase 1 z‖ < δ → ‖R₂ b - E.toBase 1 z‖ < δ → R₂ b = b := by
  set ι := E.toBase 1 with hιdef
  set x₀ := ι z with hx₀def
  set L₂ := R₂.plusDeriv z with hL₂def
  set c := ‖L₂‖ * ‖ι‖ with hcdef
  have hc : 0 ≤ c := by positivity
  set η : ℝ := 1 / (2 * (2 + c)) with hηdef
  have hη : 0 < η := by positivity
  have hηc : η * (2 + c) = 1 / 2 := by rw [hηdef]; field_simp
  have hz₁U : z ∈ E.lvlSet R₁.U 1 := R₁.retract_subset hz₁
  have hz₂U : z ∈ E.lvlSet R₂.U 1 := R₂.retract_subset hz₂
  obtain ⟨δ₁, hδ₁, hs₁⟩ := exists_strict_plusLift h₁ hz₁U hη
  obtain ⟨δ₂, hδ₂, hs₂⟩ := exists_strict_plusLift h₂ hz₂U hη
  have hcont := (continuousOn_plusLift h₁) x₀ (R₁.retract_subset hz₁)
  rw [ContinuousWithinAt, plusLift_toBase_of_mem_retract hz₁] at hcont
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1
    (hcont (Metric.ball_mem_nhds z (lt_min hδ₁ hδ₂)))
  refine ⟨δ, hδ, fun b hb hb₂ ha hbx hax => ?_⟩
  set a := R₂ b with hadef
  have haU : a ∈ R₁.U := R₁.retract_subset ha
  have hbU : b ∈ R₁.U := R₁.retract_subset hb
  set pa := R₁.plusLift a with hpadef
  set pb := R₁.plusLift b with hpbdef
  have hιpa : ι pa = a := toBase_plusLift_of_mem_retract h₁ ha
  have hιpb : ι pb = b := toBase_plusLift_of_mem_retract h₁ hb
  have hpa : pa ∈ Metric.ball z (min δ₁ δ₂) :=
    hball ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hax, haU⟩
  have hpb : pb ∈ Metric.ball z (min δ₁ δ₂) :=
    hball ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hbx, hbU⟩
  rw [Metric.mem_ball, dist_eq_norm] at hpa hpb
  have hpa1 : pa ∈ E.lvlSet R₁.U 1 := by rw [ScBanach.mem_lvlSet, hιpa]; exact haU
  have hpb1 : pb ∈ E.lvlSet R₁.U 1 := by rw [ScBanach.mem_lvlSet, hιpb]; exact hbU
  have hpa2 : pa ∈ E.lvlSet R₂.U 1 := by
    rw [ScBanach.mem_lvlSet, hιpa]; exact R₂.mapsTo hb₂
  have hpb2 : pb ∈ E.lvlSet R₂.U 1 := by rw [ScBanach.mem_lvlSet, hιpb]; exact hb₂
  set u := pa - pb with hudef
  have hιu : ι u = a - b := by rw [hudef, map_sub, hιpa, hιpb]
  -- the estimate for `r₁`
  have e1 := hs₁ pa hpa1 pb hpb1 (lt_of_lt_of_le hpa (min_le_left _ _))
    (lt_of_lt_of_le hpb (min_le_left _ _))
  have hpa_eq : R₁.plusLift (ι pa) = pa := by rw [hιpa]
  have hpb_eq : R₁.plusLift (ι pb) = pb := by rw [hιpb]
  rw [hpa_eq, hpb_eq, ← hudef, hιu] at e1
  set w := R₁.plusDeriv z (a - b) with hwdef
  -- the estimate for `r₂`
  have e2 := hs₂ pa hpa2 pb hpb2 (lt_of_lt_of_le hpa (min_le_right _ _))
    (lt_of_lt_of_le hpb (min_le_right _ _))
  have hr2 : R₂.plusLift (ι pa) = R₂.plusLift (ι pb) := by
    rw [hιpa, hιpb]
    change E.liftOne (R₂ (R₂ b)) = E.liftOne (R₂ b)
    rw [R₂.idem b hb₂]
  rw [hr2, sub_self, zero_sub, norm_neg, ← hudef, hιu] at e2
  -- `L₂(ι w) = w`
  have hιw : ι w = scDeriv R₁.U R₁ z (a - b) := toBase_plusDeriv h₁ hz₁U (a - b)
  have hιw2 : ι w ∈ range (scDeriv R₂.U R₂ z) := by rw [hιw, ← hT]; exact ⟨a - b, rfl⟩
  have hLw : L₂ (ι w) = w :=
    E.toBase_injective 1 (toBase_plusDeriv_of_mem_range h₂ hz₂ hιw2)
  have hw : ‖w‖ ≤ η * ‖u‖ + c * (η * ‖u‖) := by
    have : w = L₂ (a - b) + L₂ (ι (w - u)) := by
      rw [map_sub ι, hιu, map_sub L₂ (ι w), hLw]; abel
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add e2 ?_)
    calc ‖L₂ (ι (w - u))‖ ≤ ‖L₂‖ * ‖ι (w - u)‖ := L₂.le_opNorm _
      _ ≤ ‖L₂‖ * (‖ι‖ * ‖w - u‖) := by gcongr; exact ι.le_opNorm _
      _ = c * ‖u - w‖ := by rw [hcdef, norm_sub_rev]; ring
      _ ≤ c * (η * ‖u‖) := by gcongr
  have hu : ‖u‖ ≤ ‖u‖ / 2 := by
    calc ‖u‖ = ‖(u - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ η * ‖u‖ + (η * ‖u‖ + c * (η * ‖u‖)) := add_le_add e1 hw
      _ = η * (2 + c) * ‖u‖ := by ring
      _ = ‖u‖ / 2 := by rw [hηc]; ring
  have hu0 : u = 0 := norm_le_zero_iff.1 (by linarith [norm_nonneg u])
  have : a - b = 0 := by rw [← hιu, hu0, map_zero]
  exact sub_eq_zero.1 this

end ScRetraction

section Idempotents

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An idempotent `P` with `‖P − P'‖ < 1` has rank at most that of `P'` (`P'` is injective on
`range P`). -/
theorem finrank_range_le_of_norm_sub_lt {P P' : F →L[ℝ] F} (hP : ∀ v, P (P v) = P v)
    (h : ‖P - P'‖ < 1) [FiniteDimensional ℝ (LinearMap.range (P' : F →ₗ[ℝ] F))] :
    finrank ℝ (LinearMap.range (P : F →ₗ[ℝ] F)) ≤
      finrank ℝ (LinearMap.range (P' : F →ₗ[ℝ] F)) := by
  let f : LinearMap.range (P : F →ₗ[ℝ] F) →ₗ[ℝ] LinearMap.range (P' : F →ₗ[ℝ] F) :=
    LinearMap.codRestrict _ ((P' : F →ₗ[ℝ] F).comp (LinearMap.range (P : F →ₗ[ℝ] F)).subtype)
      fun v => LinearMap.mem_range_self _ _
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun v w hvw => ?_
  have hvw' : P' (v - w : F) = 0 := by
    have := congrArg Subtype.val hvw
    simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      ContinuousLinearMap.coe_coe] at this
    rw [map_sub, this, sub_self]
  have hfix : P (v - w : F) = (v - w : F) := by
    obtain ⟨v', hv'⟩ := v.2
    obtain ⟨w', hw'⟩ := w.2
    rw [← hv', ← hw']
    simp only [ContinuousLinearMap.coe_coe]
    rw [map_sub, hP, hP]
  have hle : ‖(v - w : F)‖ ≤ ‖P - P'‖ * ‖(v - w : F)‖ := by
    calc ‖(v - w : F)‖ = ‖(P - P') (v - w : F)‖ := by
          rw [sub_apply, hfix, hvw', sub_zero]
      _ ≤ ‖P - P'‖ * ‖(v - w : F)‖ := (P - P').le_opNorm _
  have h0 : ‖(v - w : F)‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖(v - w : F)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h0))

end Idempotents

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}

/-- The level-`1` idempotent `P_z = L_z ∘ ι : E₁ → E₁` attached to a point of the retract. -/
theorem plusDeriv_toBase_idem (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract)
    (v : E 1) : R.plusDeriv z (E.toBase 1 (R.plusDeriv z (E.toBase 1 v))) =
      R.plusDeriv z (E.toBase 1 v) := by
  rw [toBase_plusDeriv hR (R.retract_subset hz), plusDeriv_scDeriv hR hz]

/-- `range Dr(z)` is the image under `ι` of `range P_z`. -/
theorem range_scDeriv_eq_map (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) :
    LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0) =
      (LinearMap.range (((R.plusDeriv z).comp (E.toBase 1) : E 1 →L[ℝ] E 1) :
        E 1 →ₗ[ℝ] E 1)).map (E.toBase 1 : E 1 →ₗ[ℝ] E 0) := by
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  ext v
  simp only [LinearMap.mem_range, Submodule.mem_map, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨R.plusDeriv z u, ⟨R.plusDeriv z u, ?_⟩, toBase_plusDeriv hR hzU u⟩
    rw [toBase_plusDeriv hR hzU, plusDeriv_scDeriv hR hz]
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨E.toBase 1 e, (toBase_plusDeriv hR hzU _).symm⟩

/-- The rank of `Dr(z)` is the rank of `P_z`. -/
theorem finrank_range_scDeriv_eq (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) :
    finrank ℝ (LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0)) =
      finrank ℝ (LinearMap.range (((R.plusDeriv z).comp (E.toBase 1) : E 1 →L[ℝ] E 1) :
        E 1 →ₗ[ℝ] E 1)) := by
  rw [range_scDeriv_eq_map hR hz]
  exact (Submodule.equivMapOfInjective _ (E.toBase_injective 1) _).finrank_eq.symm

theorem finiteDimensional_range_P (hR : R.IsScPlus) {z : E 1}
    (hz : E.toBase 1 z ∈ R.retract) :
    FiniteDimensional ℝ (LinearMap.range (((R.plusDeriv z).comp (E.toBase 1) : E 1 →L[ℝ] E 1) :
        E 1 →ₗ[ℝ] E 1)) := by
  have := lemma_4_1_7_ii hR hz
  rw [range_scDeriv_eq_map hR hz] at this
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (E.toBase_injective 1) _).symm

/-- **Local constancy of the rank of `Dr` on an sc⁺-retract** (the content of 2021 Remark
9.1.1, p. 402, that `dim T_mM` is locally constant): near `x₀ = ι z`, every point `a` of the
retract has `rank Dr(â) = rank Dr(z)` (`â` the lift of `a`).  The idempotents `P_{â}` depend
continuously on `a` in the operator norm of `E₁` (`continuousOn_plusDeriv`), and idempotents at
distance `< 1` have equal finite ranks. -/
theorem eventually_finrank_eq (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) :
    ∃ δ > 0, ∀ a ∈ R.retract, ‖a - E.toBase 1 z‖ < δ →
      finrank ℝ (LinearMap.range (scDeriv R.U R (R.plusLift a) : E 0 →ₗ[ℝ] E 0)) =
        finrank ℝ (LinearMap.range (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0)) := by
  have hx₀U : E.toBase 1 z ∈ R.U := R.retract_subset hz
  have hc1 := (continuousOn_plusDeriv hR).comp (continuousOn_plusLift hR)
    (fun x hx => plusLift_mem_lvlSet hR hx)
  have hc := hc1 _ hx₀U
  rw [ContinuousWithinAt, Function.comp_apply, plusLift_toBase_of_mem_retract hz] at hc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hc (Metric.ball_mem_nhds _ one_pos))
  refine ⟨δ, hδ, fun a ha hax => ?_⟩
  have haU : a ∈ R.U := R.retract_subset ha
  have hpa : E.toBase 1 (R.plusLift a) ∈ R.retract := by
    rw [toBase_plusLift_of_mem_retract hR ha]; exact ha
  have hmem := hball ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hax, haU⟩
  rw [mem_preimage, Function.comp_apply, Metric.mem_ball, dist_eq_norm] at hmem
  rw [finrank_range_scDeriv_eq hR hpa, finrank_range_scDeriv_eq hR hz]
  have := finiteDimensional_range_P hR hpa
  have := finiteDimensional_range_P hR hz
  refine le_antisymm (finrank_range_le_of_norm_sub_lt (fun v => ?_) hmem)
    (finrank_range_le_of_norm_sub_lt (fun v => ?_) (by rwa [norm_sub_rev]))
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    exact plusDeriv_toBase_idem hR hpa v
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    exact plusDeriv_toBase_idem hR hz v

end ScRetraction

/-! ### Submanifolds of a general M-polyfold, in a chart -/

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

section Chart

variable {φ : MChart X} (hφ : P.IsChart φ)
include hφ

/-- The chart sc⁺-retraction `t` of the proof of Theorem 4.18 (`exists_chartRetraction`), with
`t(U) = φ(W ∩ A)`. -/
theorem exists_plusRetraction {A : Set X} (d : P.SubmanifoldData A) {x : X} (hxA : x ∈ A)
    (hxV : x ∈ d.V) :
    ∃ t : ScRetraction φ.model.E φ.model.C,
      t.retract = φ '' (d.toSubData.shrink φ ∩ A) ∧ t.IsScPlus := by
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hφ (P.levelMk 1 x (d.mem_levelSet_one hxA hxV)) R hR
  exact ⟨t, ht, htp⟩

/-- At a point `y ∈ W ∩ A`, `φ(y)` lies in the retract of `t`, the level-`1` lift of `φ(y)` is
`levelLift φ 1 y`, and `T_yA` is `range Dt(levelLift φ 1 y)` in the chart (Remark 4.14). -/
theorem chartTangent_eq_range {A : Set X} (d : P.SubmanifoldData A)
    {t : ScRetraction φ.model.E φ.model.C} (ht : t.retract = φ '' (d.toSubData.shrink φ ∩ A))
    {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V) (hyφ : y ∈ φ.source) :
    φ.model.E.toBase 1 (levelLift φ 1 y) = φ y ∧ φ y ∈ t.retract ∧
      P.chartTangent hφ A y = range (scDeriv t.U t (levelLift φ 1 y)) := by
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one hyA hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  have hyt : φ y ∈ t.retract := by
    rw [ht]; exact ⟨y, ⟨d.toSubData.mem_shrink φ hyA hyV hyφ, hyA⟩, rfl⟩
  refine ⟨hz, hyt, ?_⟩
  rw [chartTangent_eq hφ d hyA hyV hyφ, ← ht]
  exact tangentSpace_eq_range t (by rw [ScBanach.mem_lvlSet, hz]; exact hyt)

/-- On `W ∩ A` the level-`1` lift is the lift `1₀¹ ∘ t` of the chart retraction. -/
theorem levelLift_eq_plusLift {A : Set X} (d : P.SubmanifoldData A)
    {t : ScRetraction φ.model.E φ.model.C} (ht : t.retract = φ '' (d.toSubData.shrink φ ∩ A))
    {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V) (hyφ : y ∈ φ.source) :
    levelLift φ 1 y = t.plusLift (φ y) := by
  obtain ⟨hz, hyt, -⟩ := chartTangent_eq_range hφ d ht hyA hyV hyφ
  rw [← hz] at hyt ⊢
  exact (ScRetraction.plusLift_toBase_of_mem_retract hyt).symm

/-- The dimension of `A` at `y ∈ W ∩ A` is the rank of `Dt` at the lift of `φ(y)`. -/
theorem hasDimAt_finrank {A : Set X} (d : P.SubmanifoldData A)
    {t : ScRetraction φ.model.E φ.model.C} (ht : t.retract = φ '' (d.toSubData.shrink φ ∩ A))
    {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V) (hyφ : y ∈ φ.source) :
    P.HasDimAt A y (finrank ℝ (LinearMap.range
      (scDeriv t.U t (t.plusLift (φ y)) : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))) := by
  obtain ⟨hz, hyt, -⟩ := chartTangent_eq_range hφ d ht hyA hyV hyφ
  refine ⟨hyA, d, φ, levelLift φ 1 y, hyV, hφ, hyφ, hz, ?_⟩
  rw [← ht, tangentSpace_eq_range t (by rw [ScBanach.mem_lvlSet, hz]; exact hyt),
    levelLift_eq_plusLift hφ d ht hyA hyV hyφ]
  rw [show range ⇑(scDeriv t.U t (t.plusLift (φ y))) =
      ((LinearMap.range (scDeriv t.U t (t.plusLift (φ y)) :
        φ.model.E 0 →ₗ[ℝ] φ.model.E 0)) : Set (φ.model.E 0)) from
      (LinearMap.coe_range _).symm, Submodule.span_eq]

end Chart

variable (φ : MChart X) in
/-- **The admissible directions at `x` for a tangent space `T`** (the cone of 2021 Lemma 9.2.10,
p. 415): `h` such that `φ(x) + s h' ∈ C` for some `s > 0` and all `h' ∈ T` near `h`. -/
def goodDirections (x : X) (T : Set (φ.model.E 0)) : Set (φ.model.E 0) :=
  {h | ∃ r > (0 : ℝ), ∃ s > (0 : ℝ), ∀ h' ∈ T, ‖h' - h‖ ≤ r → φ x + s • h' ∈ φ.model.C}

/-- **2021 Lemmas 9.2.9–9.2.11 (pp. 414–417; 2017: Lemmas 9.6–9.8) for every smooth
finite-dimensional submanifold of a general M-polyfold**, in every chart `φ` at `x`: `A` has the
graph representation `IsGraphChartAt` with the admissible directions
`goodDirections φ x (T_xA)` of its own tangent space.  From the chart sc⁺-retraction `t`:
`exists_cone` (Lemma 9.2.9), `exists_approx` (`DB(0) = 0`), `exists_graph` (Lemmas 9.2.10,
9.2.11). -/
theorem isGraphChartAt_goodDirections {φ : MChart X} (hφ : P.IsChart φ) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {x : X} (hxA : x ∈ A) (hxφ : x ∈ φ.source) :
    P.IsGraphChartAt hφ (goodDirections φ x (P.chartTangent hφ A x)) A x := by
  set d := hA.data hxA
  have hxV : x ∈ d.V := hA.mem_data_V hxA
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hxA hxV
  obtain ⟨hz, hxt, hT⟩ := chartTangent_eq_range hφ d ht hxA hxV hxφ
  have hzt : φ.model.E.toBase 1 (levelLift φ 1 x) ∈ t.retract := by rw [hz]; exact hxt
  have hW : d.toSubData.shrink φ ∈ 𝓝 x :=
    (d.toSubData.isOpen_shrink φ).mem_nhds (d.toSubData.mem_shrink φ hxA hxV hxφ)
  obtain ⟨ρ, hρ, hρW⟩ := exists_pos_forall_mem_of_mem_nhds hxφ hW
  have himg : ∀ a ∈ A ∩ φ.source, ‖φ a - φ x‖ < ρ → φ a ∈ t.retract := fun a ha haρ => by
    rw [ht]; exact ⟨a, ⟨hρW a ha.2 haρ, ha.1⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h₁, hh₁, r, hr, s, hs, hcone⟩ := ScRetraction.exists_cone htp hzt
    refine ⟨h₁, hT ▸ hh₁, r / 2, by positivity, fun v _ hvr =>
      ⟨r / 2, by positivity, s, hs, fun h' hh' hd => ?_⟩⟩
    rw [← hz]
    refine hcone h' (by rw [← hT]; exact hh') ?_
    calc ‖h' - h₁‖ = ‖(h' - v) + (v - h₁)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖h' - v‖ + ‖v - h₁‖ := norm_add_le _ _
      _ ≤ r := by linarith
  · intro ε hε
    obtain ⟨δ, hδ, happ⟩ := ScRetraction.exists_approx htp hzt hε
    refine ⟨min δ ρ, lt_min hδ hρ, fun a ha b hb haδ hbδ =>
      ⟨_, by rw [hT]; exact ⟨φ a - φ b, rfl⟩, ?_⟩⟩
    exact happ (φ a) (himg a ha (lt_of_lt_of_le haδ (min_le_right _ _))) (φ b)
      (himg b hb (lt_of_lt_of_le hbδ (min_le_right _ _)))
      (by rw [hz]; exact lt_of_lt_of_le haδ (min_le_left _ _))
      (by rw [hz]; exact lt_of_lt_of_le hbδ (min_le_left _ _))
  · intro Q hQT hQid h hh hK ε hε
    obtain ⟨r, hr, s, hs, hcone⟩ := hK
    obtain ⟨t₀, ht₀, hgr⟩ := ScRetraction.exists_graph htp hzt Q
      (fun v => by rw [← hT]; exact hQT v) (fun v hv => hQid v (by rw [hT]; exact hv))
      (by rw [← hT]; exact hh) hr hs
      (fun h' hh' hd => by rw [hz]; exact hcone h' (by rw [hT]; exact hh') hd) hε
    refine ⟨t₀, ht₀, fun τ hτ hτt => ?_⟩
    obtain ⟨a', ha', hQa, hest⟩ := hgr τ hτ hτt
    rw [ht] at ha'
    obtain ⟨a, ⟨haW, haA⟩, rfl⟩ := ha'
    rw [hz] at hQa hest
    exact ⟨a, ⟨haA, d.toSubData.shrink_subset_source φ haW⟩, hQa, hest⟩

variable (P) in
/-- **The graph representation at `x`, one admissible cone per tangent space**: one chart `φ`
at `x` and a choice `K(T)` of admissible directions for each tangent space `T` in which every
smooth finite-dimensional submanifold through `x` has the graph representation
(`IsGraphChartAt` with `K(T_xA)`).  It holds at every point (`hasClassGraphChartAt`).  The
project's earlier hypothesis `HasGraphChartAt` (`AppendixSlices`), one `K` for all tangent
spaces, was stronger than the text needs: the slice arguments use one tangent space at a
time. -/
def HasClassGraphChartAt (x : X) : Prop :=
  ∃ (φ : MChart X) (hφ : P.IsChart φ), x ∈ φ.source ∧
    ∃ K : Set (φ.model.E 0) → Set (φ.model.E 0), ∀ A : Set X, P.IsSmoothSubmanifold A → x ∈ A →
      P.IsGraphChartAt hφ (K (P.chartTangent hφ A x)) A x

/-- **The graph representation holds at every point of every M-polyfold**
(`isGraphChartAt_goodDirections`). -/
theorem hasClassGraphChartAt (x : X) : P.HasClassGraphChartAt x := by
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  exact ⟨φ, hφ, hxφ, goodDirections φ x, fun A hA hxA =>
    isGraphChartAt_goodDirections hφ hA hxA hxφ⟩


/-- **The ball form of the graph representation at interior points** (2021 Lemmas 9.2.10,
9.2.11, pp. 414–417, where every direction is admissible): if `φ(x)` is an interior point of the
partial quadrant `C`, every smooth finite-dimensional submanifold through `x` has the graph
representation `IsGraphBallAt` in `φ` (`ScRetraction.exists_graph_ball`). -/
theorem isGraphBallAt_of_mem_interior {φ : MChart X} (hφ : P.IsChart φ) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {x : X} (hxA : x ∈ A) (hxφ : x ∈ φ.source)
    (hint : φ x ∈ interior φ.model.C) : P.IsGraphBallAt hφ A x := by
  set d := hA.data hxA
  have hxV : x ∈ d.V := hA.mem_data_V hxA
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hxA hxV
  obtain ⟨hz, hxt, hT⟩ := chartTangent_eq_range hφ d ht hxA hxV hxφ
  have hzt : φ.model.E.toBase 1 (levelLift φ 1 x) ∈ t.retract := by rw [hz]; exact hxt
  refine ⟨(isGraphChartAt_goodDirections hφ hA hxA hxφ).approx, fun Q hQT hQid ε hε => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 _root_.isOpen_interior _ hint
  obtain ⟨r₀, hr₀, hgr⟩ := ScRetraction.exists_graph_ball htp hzt Q
    (fun v => by rw [← hT]; exact hQT v) (fun v hv => hQid v (by rw [hT]; exact hv)) hρ
    (by rw [hz]; exact hball.trans interior_subset) hε
  refine ⟨r₀, hr₀, fun u hu hur => ?_⟩
  obtain ⟨a', ha', hQa, hest⟩ := hgr u (by rw [← hT]; exact hu) hur
  rw [ht] at ha'
  obtain ⟨a, ⟨haW, haA⟩, rfl⟩ := ha'
  rw [hz] at hQa hest
  exact ⟨a, ⟨haA, d.toSubData.shrink_subset_source φ haW⟩, hQa, hest⟩

/-- **`HasGraphBallAt` at interior points** (the hypothesis of `lemma_9_3_4_of_hasGraphBallAt`):
it holds at every `x` with `φ(x) ∈ int C` for some chart `φ` at `x`. -/
theorem hasGraphBallAt_of_mem_interior {φ : MChart X} (hφ : P.IsChart φ) {x : X}
    (hxφ : x ∈ φ.source) (hint : φ x ∈ interior φ.model.C) (n : ℕ) : P.HasGraphBallAt x n :=
  ⟨φ, hφ, hxφ, fun _ hA hxA => isGraphBallAt_of_mem_interior hφ hA.1 hxA hxφ hint⟩

/-- **`HasGraphChartAt` at interior points**, with every direction admissible (`K = E₀`).  At
general points `HasClassGraphChartAt` (one cone per tangent space) is used instead; it is all
the slice arguments need. -/
theorem hasGraphChartAt_of_mem_interior {φ : MChart X} (hφ : P.IsChart φ) {x : X}
    (hxφ : x ∈ φ.source) (hint : φ x ∈ interior φ.model.C) : P.HasGraphChartAt x :=
  ⟨φ, hφ, hxφ, univ, fun _ _ hA hxA =>
    (isGraphBallAt_of_mem_interior hφ hA.1 hxA hxφ hint).isGraphChartAt hA.1 hxA hxφ⟩

/-- **The interior-point condition can be met**: every point of `ℝᵐ` is interior in the chart
`rnChart m 0` (whose partial quadrant is `ℝᵐ`). -/
theorem exists_chart_mem_interior_rn {m : ℕ} (x : Fin m → ℝ) :
    ∃ φ : MChart (Fin m → ℝ), (rnPolyfold m).IsChart φ ∧ x ∈ φ.source ∧
      φ x ∈ interior φ.model.C :=
  ⟨rnChart m 0, isChart_rnChart 0, mem_univ x, by
    change _ ∈ interior (univ : Set (Fin m → ℝ)); rw [interior_univ]; exact mem_univ _⟩

/-- A point of a partial quadrant with degeneracy index `0` (Definition 1.23) is an interior
point. -/
theorem _root_.Polyfold.mem_interior_of_degIndex_eq_zero {E : ScBanach} {C : Set (E 0)}
    (hC : IsPartialQuadrant E C) {x : E 0} (hx : x ∈ C) (h0 : Polyfold.degIndex E C x = 0) :
    x ∈ interior C := by
  obtain ⟨n, W, T, hT⟩ := hC
  rw [Polyfold.degIndex_eq T hT hx, degIndexWith, quadrantDeg, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff] at h0
  have hxq : ∀ i, 0 ≤ (T 0 x).1 i := by rw [hT] at hx; exact hx
  rw [mem_interior]
  refine ⟨{y | ∀ i, 0 < (T 0 y).1 i}, fun y hy => ?_, ?_,
    fun i => lt_of_le_of_ne (hxq i) (Ne.symm (h0 (Finset.mem_univ i)))⟩
  · rw [hT]; exact fun i => (hy i).le
  · have : {y : E 0 | ∀ i, 0 < (T 0 y).1 i} = ⋂ i, {y | 0 < (T 0 y).1 i} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_fst.comp (T 0).continuous))

/-- **Points of the interior `X ∖ ∂X` are interior in a chart**: if `d_X(x) = 0`
(Definition 2.22), some chart `φ` at `x` has `φ(x) ∈ int C`. -/
theorem exists_chart_mem_interior_of_degIndex_eq_zero {x : X} (h : P.degIndex x = 0) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ φ x ∈ interior φ.model.C := by
  obtain ⟨φ, hφ, hxφ, hd⟩ := P.exists_isChart_degIndex_eq x
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hxO : φ x ∈ φ.model.O := φ.mapsTo_model x hxφ
  have hxC : φ x ∈ φ.model.C := by
    obtain ⟨O, -, hUO⟩ := R.relOpen.relOpen
    rw [← hR] at hxO
    exact (hUO ▸ R.retract_subset hxO).2
  refine ⟨φ, hφ, hxφ, Polyfold.mem_interior_of_degIndex_eq_zero
    R.relOpen.isPartialQuadrant hxC ?_⟩
  change chartDegIndex φ x = 0
  rw [← hd, h]

/-- The degeneracy index of every point of `E` in the partial quadrant `E` is `0`. -/
theorem _root_.Polyfold.degIndex_univ (E : ScBanach) (y : E 0) :
    Polyfold.degIndex E univ y = 0 := by
  let T : ScIso E ((ScBanach.const (Fin 0 → ℝ)).prod E) :=
    { lvl := fun m => (ContinuousLinearEquiv.uniqueProd ℝ (E m) (Fin 0 → ℝ)).symm
      incl_comm := fun m x => Prod.ext (funext fun i => i.elim0) rfl }
  have hT : (univ : Set (E 0)) = T 0 ⁻¹' quadrant 0 E 0 := by ext; simp [quadrant]
  rw [Polyfold.degIndex_eq T hT (mem_univ y), degIndexWith, quadrantDeg]
  simp

/-- **The condition `d_X = 0` can be met**: every point of `ℝᵐ` has degeneracy index `0`. -/
theorem degIndex_rn {m : ℕ} (x : Fin m → ℝ) : (rnPolyfold m).degIndex x = 0 :=
  Nat.le_zero.1 (((rnPolyfold m).degIndex_le (isChart_rnChart 0) (mem_univ x)).trans
    (le_of_eq (Polyfold.degIndex_univ _ _)))

/-- **2021 Remark 9.1.1 (p. 402) for a general M-polyfold: the dimension of a smooth
finite-dimensional submanifold is locally constant** (gap G.93).  In a chart, `dim_y A` is the
rank of `Dt` at the lift of `φ(y)` (`hasDimAt_finrank`), which is locally constant along the
retract (`ScRetraction.eventually_finrank_eq`).  This makes the hypothesis
`HasLocallyConstantDimAt` unnecessary. -/
theorem hasLocallyConstantDimAt (x : X) : P.HasLocallyConstantDimAt x := by
  intro A hA hxA
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  set d := hA.data hxA
  have hxV : x ∈ d.V := hA.mem_data_V hxA
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hxA hxV
  obtain ⟨hz, hxt, -⟩ := chartTangent_eq_range hφ d ht hxA hxV hxφ
  have hzt : φ.model.E.toBase 1 (levelLift φ 1 x) ∈ t.retract := by rw [hz]; exact hxt
  obtain ⟨δ, hδ, hrank⟩ := ScRetraction.eventually_finrank_eq htp hzt
  have hW : d.toSubData.shrink φ ∈ 𝓝 x :=
    (d.toSubData.isOpen_shrink φ).mem_nhds (d.toSubData.mem_shrink φ hxA hxV hxφ)
  obtain ⟨ρ, hρ, hρW⟩ := exists_pos_forall_mem_of_mem_nhds hxφ hW
  set V := (φ.source ∩ φ ⁻¹' Metric.ball (φ x) (min δ ρ)) ∩ d.V with hVdef
  have hV : IsOpen V := (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source
    Metric.isOpen_ball).inter d.isOpen
  have hxV' : x ∈ V := ⟨⟨hxφ, Metric.mem_ball_self (lt_min hδ hρ)⟩, hxV⟩
  refine ⟨V, hV, hxV', finrank ℝ (LinearMap.range (scDeriv t.U t (levelLift φ 1 x) :
    φ.model.E 0 →ₗ[ℝ] φ.model.E 0)), hA.inter_isOpen hV, fun y hy => ?_⟩
  obtain ⟨hyA, ⟨hyφ, hyball⟩, hyV⟩ := hy
  rw [mem_preimage, Metric.mem_ball, dist_eq_norm] at hyball
  refine (hasDimAt_inter_isOpen_iff hA hV ⟨⟨hyφ, ?_⟩, hyV⟩).2 ?_
  · rw [mem_preimage, Metric.mem_ball, dist_eq_norm]; exact hyball
  have hdim := hasDimAt_finrank hφ d ht hyA hyV hyφ
  have hyt : φ y ∈ t.retract := (chartTangent_eq_range hφ d ht hyA hyV hyφ).2.1
  rwa [hrank (φ y) hyt (by rw [hz]; exact lt_of_lt_of_le hyball (min_le_left _ _))] at hdim

/-- An sc⁺-retraction is continuous on its domain on level `0`. -/
theorem _root_.Polyfold.ScRetraction.continuousOn_of_isScPlus {E : ScBanach} {C : Set (E 0)}
    {R : ScRetraction E C} (hR : R.IsScPlus) : ContinuousOn R R.U :=
  ((E.toBase 1).continuous.comp_continuousOn (ScRetraction.continuousOn_plusLift hR)).congr
    fun _ hx => (ScRetraction.toBase_plusLift hR hx).symm

/-- **The invariance of domain used in 2021 Lemma 9.2.7(2) (p. 412) for a general M-polyfold**
(gap G.98): an `n`-dimensional submanifold contained near `y` in another `n`-dimensional one
agrees with it near `y`.  Both are retracts of chart sc⁺-retractions with the same tangent space
at `y` (equal dimensions), and `ScRetraction.eq_of_range_eq` applies.  This makes the
hypothesis `HasDomainInvarianceAt` unnecessary. -/
theorem hasDomainInvarianceAt (y : X) (n : ℕ) : P.HasDomainInvarianceAt y n := by
  intro A B hA hB hyA V hV hAB
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨V₀, hV₀V, hV₀, hyV₀⟩ := mem_nhds_iff.1 hV
  have hyB : y ∈ B := hAB ⟨hyA, mem_of_mem_nhds hV⟩
  set dA := hA.1.data hyA
  set dB := hB.1.data hyB
  have hyVA : y ∈ dA.V := hA.1.mem_data_V hyA
  have hyVB : y ∈ dB.V := hB.1.mem_data_V hyB
  obtain ⟨tA, htA, htAp⟩ := exists_plusRetraction hφ dA hyA hyVA
  obtain ⟨tB, htB, htBp⟩ := exists_plusRetraction hφ dB hyB hyVB
  obtain ⟨hz, hyA', hTA⟩ := chartTangent_eq_range hφ dA htA hyA hyVA hyφ
  obtain ⟨-, hyB', hTB⟩ := chartTangent_eq_range hφ dB htB hyB hyVB hyφ
  set z := levelLift φ 1 y
  set x₀ := φ y with hx₀def
  have hzA : φ.model.E.toBase 1 z ∈ tA.retract := by rw [hz]; exact hyA'
  have hzB : φ.model.E.toBase 1 z ∈ tB.retract := by rw [hz]; exact hyB'
  -- the tangent spaces agree
  have hsub : P.chartTangent hφ A y ⊆ P.chartTangent hφ B y :=
    (chartTangent_subset_iff hφ hyφ).2 (submanifoldTangent_subset_of_subset hB.1 hV₀ hyV₀
      fun q hq => hAB ⟨hq.1, hV₀V hq.2⟩)
  obtain ⟨NA, hNA, hfA⟩ := exists_submodule_chartTangent hφ hA.1 hyA hyφ
  obtain ⟨NB, hNB, hfB⟩ := exists_submodule_chartTangent hφ hB.1 hyB hyφ
  have hrA := finrank_chartTangent hφ (hA.2 y hyA) hA.1 hyφ hNA
  have hrB := finrank_chartTangent hφ (hB.2 y hyB) hB.1 hyφ hNB
  have hle : NA ≤ NB := by rw [← SetLike.coe_subset_coe, hNA, hNB]; exact hsub
  have hEq : NA = NB := Submodule.eq_of_le_of_finrank_eq hle (by rw [hrA, hrB])
  have hT : range (scDeriv tB.U tB z) = range (scDeriv tA.U tA z) := by
    rw [← hTA, ← hTB, ← hNA, ← hNB, hEq]
  obtain ⟨δ, hδ, hfix⟩ := ScRetraction.eq_of_range_eq htBp htAp hzB hzA hT
  rw [hz] at hfix
  -- the neighbourhoods
  have hWB : dB.toSubData.shrink φ ∈ 𝓝 y :=
    (dB.toSubData.isOpen_shrink φ).mem_nhds (dB.toSubData.mem_shrink φ hyB hyVB hyφ)
  obtain ⟨ρ', hρ', hρ'W⟩ := exists_pos_forall_mem_of_mem_nhds hyφ
    (Filter.inter_mem (hV₀.mem_nhds hyV₀) hWB)
  obtain ⟨OA, hOA, hUA⟩ := tA.relOpen.relOpen
  have hx₀UA : x₀ ∈ tA.U := tA.retract_subset hyA'
  obtain ⟨ρA, hρA, hρAsub⟩ := Metric.isOpen_iff.1 hOA x₀ (hUA ▸ hx₀UA).1
  have hcont := ScRetraction.continuousOn_of_isScPlus htAp x₀ hx₀UA
  rw [ContinuousWithinAt, tA.apply_eq_self_of_mem_retract hyA'] at hcont
  obtain ⟨δc, hδc, hballc⟩ := Metric.mem_nhdsWithin_iff.1
    (hcont (Metric.ball_mem_nhds x₀ (lt_min hδ hρ')))
  set δ' := min (min δ δc) ρA with hδ'def
  have hδ' : 0 < δ' := lt_min (lt_min hδ hδc) hρA
  have hWBo : IsOpen (dB.toSubData.shrink φ) := dB.toSubData.isOpen_shrink φ
  refine ⟨(φ.source ∩ φ ⁻¹' Metric.ball x₀ δ') ∩ dB.toSubData.shrink φ,
    ((φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball).inter
      hWBo).mem_nhds ⟨⟨hyφ, Metric.mem_ball_self hδ'⟩, dB.toSubData.mem_shrink φ hyB hyVB hyφ⟩,
    fun q hq => ?_⟩
  obtain ⟨hqB, ⟨hqφ, hqball⟩, hqW⟩ := hq
  rw [mem_preimage, Metric.mem_ball, dist_eq_norm] at hqball
  have hb : φ q ∈ tB.retract := by rw [htB]; exact ⟨q, ⟨hqW, hqB⟩, rfl⟩
  have hbC : φ q ∈ φ.model.C := by
    obtain ⟨OB, -, hUB⟩ := tB.relOpen.relOpen
    exact (hUB ▸ tB.retract_subset hb).2
  have hbUA : φ q ∈ tA.U := by
    rw [hUA]
    refine ⟨hρAsub ?_, hbC⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hqball (min_le_right _ _)
  have hab := hballc ⟨by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hqball ((min_le_left _ _).trans (min_le_right _ _)), hbUA⟩
  rw [mem_preimage, Metric.mem_ball, dist_eq_norm] at hab
  have haA : tA (φ q) ∈ tA.retract := tA.apply_mem_retract hbUA
  rw [htA] at haA
  obtain ⟨p, ⟨hpW, hpA⟩, hpq⟩ := haA
  have hpφ : p ∈ φ.source := dA.toSubData.shrink_subset_source φ hpW
  have hpVW := hρ'W p hpφ (by rw [hpq]; exact lt_of_lt_of_le hab (min_le_right _ _))
  have hpB : p ∈ B := hAB ⟨hpA, hV₀V hpVW.1⟩
  have hat : tA (φ q) ∈ tB.retract := by rw [← hpq, htB]; exact ⟨p, ⟨hpVW.2, hpB⟩, rfl⟩
  have heq := hfix (φ q) hb hbUA hat (lt_of_lt_of_le hqball
    ((min_le_left _ _).trans (min_le_left _ _)))
    (lt_of_lt_of_le hab (min_le_left _ _))
  rw [← hpq] at heq
  have : p = q := φ.toPartialEquiv.injOn hpφ hqφ heq
  rw [← this]; exact hpA

/-- **Level-`1` coordinates are continuous along every smooth finite-dimensional submanifold of
a general M-polyfold** (gap G.100): on `W ∩ A` the lift `levelLift φ 1` is `(1₀¹ ∘ t) ∘ φ`
(`levelLift_eq_plusLift`), continuous since `t` is sc⁺.  This makes the hypothesis
`HasContinuousLevelOneOn` unnecessary. -/
theorem hasContinuousLevelOneOn {A : Set X} (hA : P.IsSmoothSubmanifold A) :
    P.HasContinuousLevelOneOn A := by
  intro φ hφ y hy
  obtain ⟨hyA, hyφ⟩ := hy
  set d := hA.data hyA
  have hyV : y ∈ d.V := hA.mem_data_V hyA
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hyA hyV
  set W := d.toSubData.shrink φ
  have hW : W ∈ 𝓝 y :=
    (d.toSubData.isOpen_shrink φ).mem_nhds (d.toSubData.mem_shrink φ hyA hyV hyφ)
  have hWV : W ⊆ d.V := fun q hq => d.toSubData.shrink_subset_V φ (by exact hq)
  have hmaps : MapsTo φ (A ∩ φ.source ∩ W) t.U := fun q hq =>
    t.retract_subset (by rw [ht]; exact ⟨q, ⟨hq.2, hq.1.1⟩, rfl⟩)
  have hc : ContinuousWithinAt (t.plusLift ∘ φ) (A ∩ φ.source ∩ W) y := by
    refine (ScRetraction.continuousOn_plusLift htp (φ y) (hmaps ⟨⟨hyA, hyφ⟩,
      mem_of_mem_nhds hW⟩)).comp ?_ hmaps
    exact (φ.continuousOn_toFun y hyφ).mono fun q hq => hq.1.2
  have hc' : ContinuousWithinAt (levelLift φ 1) (A ∩ φ.source ∩ W) y :=
    hc.congr (fun q hq => levelLift_eq_plusLift hφ d ht hq.1.1 (hWV hq.2) hq.1.2)
      (levelLift_eq_plusLift hφ d ht hyA hyV hyφ)
  exact (continuousWithinAt_inter hW).1 hc'

end MPolyfold

end Polyfold
