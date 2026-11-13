import Polyfold.Chapter9.TameOpen
import Polyfold.Chapter9.OrientationRn
import Polyfold.Chapter7.PropertyFiveResearch

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, Definitions 9.1.2, 9.1.6, 9.3.3, 9.3.6 (pp. 412–426) and Theorem 9.5.4
(p. 438; 2017: Theorem 9.2).  Numbers and pages are the 2021 text's.

# A compact witness of dimension `1`: the unit circle in `ℝ²`

The hypotheses of `EpGroupoid.FormEval.theorem_9_5_4_tame` (the concrete branched integral of
sc-differential forms) are satisfiable jointly with compactness and nonempty support.

* The unit circle `S¹ = {r₀² + r₁² = 1}` is a closed `1`-dimensional submanifold of the
  M-polyfold `ℝ²` (`rnPolyfold_isSubmanifoldOfDim_unitCircle2`): it is the image of the radial
  retraction `r ↦ r / |r|` of the open set `ℝ² ∖ {0}` (an sc⁺-retraction there), whose derivative
  at `a ∈ S¹` is `h ↦ (a₀h₁ − a₁h₀)(−a₁, a₀)`; so `T_aS¹ = ℝ(−a₁, a₀)`.
* `circleOrientation`: the counter-clockwise orientation of `S¹`, positive frames the positive
  multiples of `(−a₁, a₀)` (Definition 9.3.3; continuous since the frame field is).
* `circle_witness`: for `Θ = 1_{S¹}` (as the sum `∑ σᵢ 1_{Mᵢ}` over one sheet with weight `1`) in
  the trivial ep-groupoid of `ℝ²`, and `T` its oriented tangent sum: `Θ` is a branched
  ep⁺-subgroupoid, compact, tame, `1`-dimensional, `T` is an orientation, `(1, 0) ∈ supp Θ`, every
  point of the support has an oriented tame structure describing `T`, and (`F.sheets` form) one
  whose sheets lie in the class of `epFormEval 1`.
* `circle_theorem_9_5_4`: Theorem 9.5.4 for the concrete integral applies to this `Θ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### The circle and the radial retraction -/

/-- The unit circle `S¹ = {r₀² + r₁² = 1}` in `ℝ²`. -/
def unitCircle2 : Set (Fin 2 → ℝ) := {r | r 0 ^ 2 + r 1 ^ 2 = 1}

/-- The punctured plane `ℝ² ∖ {0}`, as `{0 < r₀² + r₁²}`. -/
def punctured2 : Set (Fin 2 → ℝ) := {r | 0 < r 0 ^ 2 + r 1 ^ 2}

/-- The radial retraction `r ↦ r / |r|`. -/
def radialRetraction (r : Fin 2 → ℝ) : Fin 2 → ℝ := (√(r 0 ^ 2 + r 1 ^ 2))⁻¹ • r

/-- The counter-clockwise tangent direction `(−a₁, a₀)`. -/
def circleDir (a : Fin 2 → ℝ) : Fin 2 → ℝ := ![-a 1, a 0]

theorem continuous_normSq2 : Continuous fun r : Fin 2 → ℝ => r 0 ^ 2 + r 1 ^ 2 := by
  fun_prop

theorem isOpen_punctured2 : IsOpen punctured2 :=
  isOpen_lt continuous_const continuous_normSq2

theorem isClosed_unitCircle2 : IsClosed unitCircle2 :=
  isClosed_eq continuous_normSq2 continuous_const

theorem unitCircle2_subset_punctured2 : unitCircle2 ⊆ punctured2 := fun r hr => by
  change 0 < r 0 ^ 2 + r 1 ^ 2
  rw [show r 0 ^ 2 + r 1 ^ 2 = 1 from hr]; exact one_pos

theorem radialRetraction_mem (r : Fin 2 → ℝ) (hr : r ∈ punctured2) :
    radialRetraction r ∈ unitCircle2 := by
  have hq : 0 < r 0 ^ 2 + r 1 ^ 2 := hr
  change ((√(r 0 ^ 2 + r 1 ^ 2))⁻¹ * r 0) ^ 2 + ((√(r 0 ^ 2 + r 1 ^ 2))⁻¹ * r 1) ^ 2 = 1
  rw [mul_pow, mul_pow, ← mul_add, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']

theorem radialRetraction_eq_self {r : Fin 2 → ℝ} (hr : r ∈ unitCircle2) :
    radialRetraction r = r := by
  have hq : r 0 ^ 2 + r 1 ^ 2 = 1 := hr
  simp only [radialRetraction, hq, Real.sqrt_one, inv_one, one_smul]

theorem radialRetraction_idem (r : Fin 2 → ℝ) (hr : r ∈ punctured2) :
    radialRetraction (radialRetraction r) = radialRetraction r :=
  radialRetraction_eq_self (radialRetraction_mem r hr)

theorem radialRetraction_image : radialRetraction '' punctured2 = unitCircle2 := by
  refine Subset.antisymm ?_ fun r hr => ⟨r, unitCircle2_subset_punctured2 hr,
    radialRetraction_eq_self hr⟩
  rintro _ ⟨r, hr, rfl⟩
  exact radialRetraction_mem r hr

theorem contDiffOn_radialRetraction : ContDiffOn ℝ ∞ radialRetraction punctured2 := by
  intro r hr
  have hq : (r 0 ^ 2 + r 1 ^ 2) ≠ 0 := (show 0 < r 0 ^ 2 + r 1 ^ 2 from hr).ne'
  have h1 : ContDiffAt ℝ ∞ (fun r : Fin 2 → ℝ => r 0 ^ 2 + r 1 ^ 2) r := by
    fun_prop
  have h2 : ContDiffAt ℝ ∞ (fun r : Fin 2 → ℝ => √(r 0 ^ 2 + r 1 ^ 2)) r := h1.sqrt hq
  have h3 : ContDiffAt ℝ ∞ (fun r : Fin 2 → ℝ => (√(r 0 ^ 2 + r 1 ^ 2))⁻¹) r :=
    h2.inv (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (by positivity) hq.symm))
  exact (h3.smul contDiffAt_id).contDiffWithinAt

/-- The derivative of the radial retraction at `a ∈ S¹`: `h ↦ (a₀h₁ − a₁h₀)(−a₁, a₀)`. -/
def radialDeriv (a : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ :=
  (a 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 -
    a 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight (circleDir a)

theorem hasFDerivAt_radialRetraction {a : Fin 2 → ℝ} (ha : a ∈ unitCircle2) :
    HasFDerivAt radialRetraction (radialDeriv a) a := by
  have hq : a 0 ^ 2 + a 1 ^ 2 = 1 := ha
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (0 : Fin 2) a
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (1 : Fin 2) a
  have hQ := (h0.pow 2).add (h1.pow 2)
  have hS := hQ.sqrt (by simp [hq])
  have hI := (hasDerivAt_inv (by simp [hq])).comp_hasFDerivAt a hS
  have hR := hI.smul (hasFDerivAt_id a)
  refine hR.congr_fderiv ?_
  ext h i
  have hsq : √(a 0 ^ 2 + a 1 ^ 2) = 1 := by rw [hq, Real.sqrt_one]
  fin_cases i
  · simp [radialDeriv, circleDir, hsq]
    linear_combination (-(h 0)) * hq
  · simp [radialDeriv, circleDir, hsq]
    linear_combination (-(h 1)) * hq

theorem circleDir_ne_zero {a : Fin 2 → ℝ} (ha : a ∈ unitCircle2) : circleDir a ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [circleDir, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
    neg_eq_zero] at h0 h1
  have hq : a 0 ^ 2 + a 1 ^ 2 = 1 := ha
  rw [h0, h1] at hq
  norm_num at hq

/-- The range of the derivative at `a ∈ S¹` is the line `ℝ(−a₁, a₀)`. -/
theorem range_radialDeriv {a : Fin 2 → ℝ} (ha : a ∈ unitCircle2) :
    LinearMap.range ((radialDeriv a : (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) :
      (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) = span ℝ {circleDir a} := by
  have hq : a 0 ^ 2 + a 1 ^ 2 = 1 := ha
  ext v
  rw [LinearMap.mem_range, mem_span_singleton]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a 0 * h 1 - a 1 * h 0, by simp [radialDeriv]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • circleDir a, ?_⟩
    simp only [radialDeriv, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
      FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
      ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul, circleDir,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    linear_combination c * hq

/-! ### `S¹` is a closed `1`-dimensional submanifold of `ℝ²` -/

open MPolyfold

theorem relOpen_punctured2 : IsRelOpenInQuadrant (rnSc 2) univ punctured2 :=
  ⟨isPartialQuadrant_univ _, punctured2, isOpen_punctured2, (inter_univ _).symm⟩

/-- The radial retraction as an sc-retraction of `ℝ²` with domain `ℝ² ∖ {0}`. -/
def radialScRetraction : ScRetraction (rnSc 2) univ where
  U := punctured2
  toFun := radialRetraction
  relOpen := relOpen_punctured2
  mapsTo r hr := unitCircle2_subset_punctured2 (radialRetraction_mem r hr)
  isScSmooth := IsScSmooth.of_contDiffOn_finiteDimensional (V := Fin 2 → ℝ)
    relOpen_punctured2.isScDomain contDiffOn_radialRetraction
  idem := radialRetraction_idem

theorem radialScRetraction_retract : radialScRetraction.retract = unitCircle2 :=
  radialRetraction_image

/-- **The tangent space of `S¹`** at `a` in the chart `id` of `ℝ²` (Remark 4.14): the line
`ℝ(−a₁, a₀)`. -/
theorem tangentSpace_unitCircle2 {a : Fin 2 → ℝ} (ha : a ∈ unitCircle2) :
    tangentSpace (rnSc 2) univ unitCircle2 (a : (rnSc 2) 1) =
      (span ℝ {circleDir a} : Set (Fin 2 → ℝ)) := by
  set R := radialScRetraction
  have hz : (a : (rnSc 2) 1) ∈ (rnSc 2).lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase, radialScRetraction_retract]; exact ha
  have haU : a ∈ punctured2 := unitCircle2_subset_punctured2 ha
  have hd : HasFDerivWithinAt radialRetraction
      (scDeriv (E := rnSc 2) (F := rnSc 2) punctured2 radialRetraction a) punctured2 a :=
    hasFDerivWithinAt_scDeriv_const' (V := Fin 2 → ℝ) (F := rnSc 2) (U := punctured2)
      (f := radialRetraction) R.isSc1 haU
  have hfd : scDeriv (E := rnSc 2) (F := rnSc 2) punctured2 radialRetraction a =
      radialDeriv a :=
    (hd.hasFDerivAt (isOpen_punctured2.mem_nhds haU)).unique (hasFDerivAt_radialRetraction ha)
  rw [← radialScRetraction_retract, tangentSpace_eq_range R hz]
  change range (scDeriv (E := rnSc 2) (F := rnSc 2) punctured2 radialRetraction a) = _
  rw [hfd, ← range_radialDeriv ha, LinearMap.coe_range]
  rfl

/-- The radial retraction is an sc⁺-retraction of the M-polyfold `ℝ²` on `ℝ² ∖ {0}`
(Definition 4.1.4). -/
theorem radialRetraction_isScPlusRetractionOn :
    (rnPolyfold 2).IsScPlusRetractionOn radialRetraction punctured2 where
  isScSmoothOn := isScSmoothOn_rn_rn_of_contDiffOn isOpen_punctured2 contDiffOn_radialRetraction
  mapsTo r hr := unitCircle2_subset_punctured2 (radialRetraction_mem r hr)
  idem := radialRetraction_idem
  mem_levelSet r _ := by rw [rnPolyfold_levelSet]; exact mem_univ _
  isScSmoothOn_one x₀ := IsScSmoothOn.comp (rnPolyfold_isScSmoothMap_toLevelOne x₀)
    (isScSmoothOn_rn_rn_of_contDiffOn isOpen_punctured2 contDiffOn_radialRetraction)
    (mapsTo_univ _ _)

/-- The submanifold data `(ℝ² ∖ {0}, r ↦ r/|r|)` of `S¹` (Definition 4.2.1). -/
def unitCircle2Data : (rnPolyfold 2).SubmanifoldData unitCircle2 :=
  ⟨punctured2, radialRetraction, isOpen_punctured2, radialRetraction_isScPlusRetractionOn, by
    rw [radialRetraction_image, inter_eq_left.2 unitCircle2_subset_punctured2]⟩

/-- **`S¹` is a smooth finite-dimensional submanifold of `ℝ²`** (Definition 4.2.1). -/
theorem rnPolyfold_isSmoothSubmanifold_unitCircle2 :
    (rnPolyfold 2).IsSmoothSubmanifold unitCircle2 := fun _ ha =>
  ⟨punctured2, isOpen_punctured2, unitCircle2_subset_punctured2 ha, radialRetraction,
    radialRetraction_isScPlusRetractionOn, unitCircle2Data.image⟩

theorem rnChart2_image_unitCircle2 {G : Set (Fin 2 → ℝ)} (hG : unitCircle2 ⊆ G) :
    (rnChart 2 0) '' (G ∩ unitCircle2) = unitCircle2 := by
  have hid : ∀ r : Fin 2 → ℝ, (rnChart 2 0) r = r := fun r => by rw [rnChart_apply, sub_zero]
  rw [inter_eq_right.2 hG]
  exact (image_congr fun r _ => hid r).trans (image_id _)

/-- **`S¹` is a `1`-dimensional submanifold of `ℝ²`** (Remark 9.1.1). -/
theorem rnPolyfold_isSubmanifoldOfDim_unitCircle2 :
    (rnPolyfold 2).IsSubmanifoldOfDim unitCircle2 1 := by
  refine ⟨rnPolyfold_isSmoothSubmanifold_unitCircle2, fun a ha => ?_⟩
  have himg := rnChart2_image_unitCircle2 unitCircle2_subset_punctured2
  have hQ : IsScRetract (rnChart 2 0).model.E (rnChart 2 0).model.C
      ((rnChart 2 0) '' (punctured2 ∩ unitCircle2)) := by
    rw [himg, ← radialScRetraction_retract]; exact radialScRetraction.isScRetract
  refine hasDimAt_of_finrank rnPolyfold_isSmoothSubmanifold_unitCircle2 ha (isChart_rnChart 0)
    isOpen_punctured2 (subset_univ _) hQ (unitCircle2_subset_punctured2 ha)
    (z := (a : (rnSc 2) 1)) ?_ ?_
  · change (ScBanach.const (Fin 2 → ℝ)).toBase 1 a = a - 0
    rw [ScBanach.const_toBase, sub_zero]
  · erw [himg, tangentSpace_unitCircle2 ha, span_eq]
    exact finrank_span_singleton (circleDir_ne_zero ha)

theorem isCompact_unitCircle2 : IsCompact unitCircle2 := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitCircle2
    ((Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun r hr => ?_)
  have hq : r 0 ^ 2 + r 1 ^ 2 = 1 := hr
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one] <;>
    nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]

/-! ### The counter-clockwise orientation -/

/-- **The tangent line of `S¹`**: the chart vectors of `T_zS¹` (chart `id` of `ℝ²`) form the line
`ℝ(−z₁, z₀)`. -/
theorem chartVec_image_unitCircle2 {z : Fin 2 → ℝ} (hz : z ∈ unitCircle2) :
    chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent unitCircle2 z =
      (span ℝ {circleDir z} : Set (Fin 2 → ℝ)) := by
  set d := unitCircle2Data
  rw [chartVec_image_submanifoldTangent idChart2 d hz (unitCircle2_subset_punctured2 hz)
    (mem_univ z)]
  have hshrink : d.toSubData.shrink (rnChart 2 0) = punctured2 :=
    Subset.antisymm (fun r hr => hr.1.1) fun r hr =>
      ⟨⟨hr, mem_univ _⟩, unitCircle2_subset_punctured2 (radialRetraction_mem r hr), mem_univ _⟩
  have hset : (rnChart 2 0) '' (d.toSubData.shrink (rnChart 2 0) ∩ unitCircle2) =
      unitCircle2 := by
    rw [hshrink]; exact rnChart2_image_unitCircle2 unitCircle2_subset_punctured2
  have hz1 : z ∈ (rnPolyfold 2).levelSet 1 := by rw [rnPolyfold_levelSet]; exact mem_univ z
  have hl : (rnChart 2 0).model.E.toBase 1 (levelLift (rnChart 2 0) 1 z) = rnChart 2 0 z :=
    (rnPolyfold 2).toBase_levelLift idChart2 (mem_univ z) hz1
  have hl' : levelLift (rnChart 2 0) 1 z = (show (rnChart 2 0).model.E 1 from z) := by
    rw [rnChart_apply, sub_zero] at hl
    exact (ScBanach.const_toBase (Fin 2 → ℝ) 1 _).symm.trans hl
  rw [hl']
  erw [hset, tangentSpace_unitCircle2 hz]

/-- `(−z₁, z₀)` as a vector of the chart model `E₀ = ℝ²` of `rnChart 2 0`. -/
def circleDirM (z : Fin 2 → ℝ) : (rnChart 2 0).model.E 0 := circleDir z

theorem continuous_circleDirM : Continuous circleDirM := by
  have h : Continuous circleDir := by
    refine continuous_pi (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
      simp only [circleDir, Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop
  exact h

/-- The frames of `T_zS¹` positive for the counter-clockwise orientation: those whose chart vector
is `c(−z₁, z₀)`, `c > 0`. -/
def circleFrames (z : Fin 2 → ℝ) : Set (Fin 1 → (rnPolyfold 2).TangentSpace) :=
  lineFrames idChart2 ((rnPolyfold 2).submanifoldTangent unitCircle2 z) (circleDirM z) 1

/-- **The counter-clockwise orientation of `S¹`** (Definition 9.3.3): positive frames the positive
multiples of `(−z₁, z₀)`; continuous since `z ↦ (−z₁, z₀)` is. -/
def circleOrientation : (rnPolyfold 2).SubmanifoldOrientation unitCircle2 1 where
  frames := circleFrames
  isOrientedAt _ hz := ⟨fun _ hα => hα.1, rnChart 2 0, idChart2, mem_univ _,
    isChartOrientation_lineFrames idChart2 (circleDir_ne_zero hz) one_ne_zero
      (chartVec_image_unitCircle2 hz)⟩
  continuous _ z hz := by
    have hlift : ∀ z' ∈ unitCircle2, ∃ α ∈ (rnPolyfold 2).submanifoldTangent unitCircle2 z',
        chartVec idChart2 α = circleDirM z' := fun z' hz' => by
      have : circleDirM z' ∈ chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent
          unitCircle2 z' := by
        rw [chartVec_image_unitCircle2 hz']
        exact mem_span_singleton_self (R := ℝ) (circleDir z')
      exact this
    obtain ⟨α₀, -, -⟩ := hlift z hz
    have : Nonempty (rnPolyfold 2).TangentSpace := ⟨α₀⟩
    choose! e he1 he2 using hlift
    refine ⟨rnChart 2 0, idChart2, univ, isOpen_univ, mem_univ z, subset_univ _,
      fun z' _ => e z', fun z' hz' => ⟨he1 z' hz'.1, 1, one_pos, by
        rw [he2 z' hz'.1, one_mul, one_smul]⟩, ?_⟩
    have hc : Continuous fun z' : Fin 2 → ℝ => fun _ : Fin 1 => circleDirM z' :=
      continuous_pi fun _ => continuous_circleDirM
    exact hc.continuousOn.congr fun z' hz' => funext fun _ => he2 z' hz'.1

/-! ### The witness -/

namespace EpGroupoid

open scoped Classical
open MeasureTheory

/-- The one sheet `S¹`. -/
def circleSheet : Unit → Set (Fin 2 → ℝ) := fun _ => unitCircle2

/-- `Θ = 1_{S¹}`, written as the weighted sum `∑ σᵢ 1_{Mᵢ}` over the one sheet with `σ = 1`. -/
def circleTheta : (Fin 2 → ℝ) → ℚ := fun y => ∑ i with y ∈ circleSheet i, (1 : ℚ)

/-- `T̂(y) = T_y(S¹, counter-clockwise)` for `y ∈ S¹`, the oriented tangent sum. -/
def circleT : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ :=
  orientedSumRn circleSheet (fun _ => (1 : ℚ)) (fun _ => circleOrientation)

theorem circleTheta_apply (y : Fin 2 → ℝ) :
    circleTheta y = if y ∈ unitCircle2 then 1 else 0 := by
  by_cases hy : y ∈ unitCircle2 <;> simp [circleTheta, circleSheet, hy]

theorem supp_circleTheta : supp circleTheta = unitCircle2 := by
  ext y
  change 0 < circleTheta y ↔ _
  rw [circleTheta_apply]
  by_cases hy : y ∈ unitCircle2 <;> simp [hy]

theorem circleSheet_isSubmanifoldOfDim (i : Unit) :
    (rnPolyfold 2).IsSubmanifoldOfDim (circleSheet i) 1 :=
  rnPolyfold_isSubmanifoldOfDim_unitCircle2

theorem circleSheet_isClosed (i : Unit) : IsClosed (circleSheet i) := isClosed_unitCircle2

/-- **`Θ = 1_{S¹}` is compact** (Definition 9.1.6): `|supp Θ| = π(S¹)`. -/
theorem isCompactBranched_circleTheta :
    (trivial (rnPolyfold 2)).IsCompactBranched circleTheta := by
  unfold IsCompactBranched orbitSupp
  rw [supp_circleTheta]
  exact isCompact_unitCircle2.image (trivial (rnPolyfold 2)).continuous_π

/-- The local hypothesis of Theorem 9.5.4: near every point there is an oriented tame structure
of dimension `1` describing `T̂`. -/
theorem circle_hloc (x : Fin 2 → ℝ) :
    ∃ C : (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x, C.Represents circleT :=
  exists_orientedTameStructure_sum_rn circleSheet (fun _ => 1) (fun _ => one_pos)
    circleSheet_isSubmanifoldOfDim circleSheet_isClosed _ x

/-- **A compact witness of dimension `1` for Theorem 9.5.4** (2021 p. 438; Definitions 9.1.2,
9.1.6, 9.3.3 (orientation), 9.3.6 (tame)): for `Θ = 1_{S¹}` in the trivial ep-groupoid of `ℝ²`
and the counter-clockwise oriented tangent sum `T`, `Θ` is a compact, tame, `1`-dimensional
branched ep⁺-subgroupoid, `T` is an orientation of `Θ`, `(1, 0) ∈ supp Θ`, every point of the
support has an oriented tame structure describing `T`, and one whose sheets lie in the class
`sheets` of the sc-differential `1`-forms (`epFormEval 1`).  Jointly, all hypotheses of
`FormEval.theorem_9_5_4_tame` hold with nonempty support. -/
theorem circle_witness :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid circleTheta ∧
      (trivial (rnPolyfold 2)).IsCompactBranched circleTheta ∧
      (trivial (rnPolyfold 2)).IsTameBranched circleTheta ∧
      (trivial (rnPolyfold 2)).IsNDimensional circleTheta 1 ∧
      (trivial (rnPolyfold 2)).IsOrientation circleTheta circleT ∧
      (![1, 0] : Fin 2 → ℝ) ∈ supp circleTheta ∧
      (∀ x ∈ supp circleTheta, ∃ C : (trivial (rnPolyfold 2)).OrientedTameStructure 1
        circleTheta x, C.Represents circleT) ∧
      (∀ x ∈ supp circleTheta, ∃ C : (trivial (rnPolyfold 2)).OrientedTameStructure 1
        circleTheta x, (∀ i, C.M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).sheets) ∧
          C.Represents circleT) := by
  refine ⟨isBranchedEpSubgroupoid_sum_rn circleSheet (fun _ => 1) (fun _ => one_pos)
      (fun i => (circleSheet_isSubmanifoldOfDim i).1) circleSheet_isClosed,
    isCompactBranched_circleTheta, fun x _ => ?_,
    isNDimensional_sum_rn circleSheet (fun _ => 1) (fun _ => one_pos)
      circleSheet_isSubmanifoldOfDim circleSheet_isClosed,
    isOrientation_sum_trivial_rn circleSheet (fun _ => 1) (fun _ => one_pos)
      circleSheet_isSubmanifoldOfDim circleSheet_isClosed _, ?_,
    fun x _ => circle_hloc x, FormEval.hcov_of_loc fun x _ => circle_hloc x⟩
  · obtain ⟨C, -⟩ := circle_hloc x
    exact ⟨C.toTameBranchingStructure⟩
  · rw [supp_circleTheta]
    change (1 : ℝ) ^ 2 + 0 ^ 2 = 1
    norm_num

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2), applied to the circle**: for
`Θ = 1_{S¹}` with the counter-clockwise orientation and the sc-differential `1`-forms of the
trivial ep-groupoid of `ℝ²`, there is exactly one linear map `ω ↦ μ_ω` into the signed measures
on `(S, L(S))` given locally by the sheet integrals (the instance of
`FormEval.theorem_9_5_4_tame`; no integral is computed). -/
theorem circle_theorem_9_5_4 :
    ∃! Φ : (trivial (rnPolyfold 2)).epForms 1 →ₗ[ℝ]
        @SignedMeasure ((trivial (rnPolyfold 2)).orbitSupp circleTheta)
          ((trivial (rnPolyfold 2)).lebesgueSigma
            ((trivial (rnPolyfold 2)).epFormEval 1).sheetNull circleTheta),
      ∀ (w : (trivial (rnPolyfold 2)).epForms 1) (x : Fin 2 → ℝ)
        (C : (trivial (rnPolyfold 2)).OrientedTameStructure 1 circleTheta x),
        ((∀ i, C.M i ∈ ((trivial (rnPolyfold 2)).epFormEval 1).sheets) ∧
          C.Represents circleT) →
        ∀ K : Set ((trivial (rnPolyfold 2)).orbitSupp circleTheta),
          MeasurableSet[(trivial (rnPolyfold 2)).lebesgueSigma
            ((trivial (rnPolyfold 2)).epFormEval 1).sheetNull circleTheta] K →
          Subtype.val '' K ⊆ (trivial (rnPolyfold 2)).π '' C.U →
          Φ w K = C.localMeasure (((trivial (rnPolyfold 2)).epFormEval 1).sheetIntegration
            one_pos) w (Subtype.val '' K) := by
  obtain ⟨hΘ, hcpt, -, -, hT, -, hloc, -⟩ := circle_witness
  exact FormEval.theorem_9_5_4_tame _ one_pos hΘ hcpt hT hloc

end EpGroupoid

end Polyfold
