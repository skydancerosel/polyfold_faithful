import Polyfold.Chapter5.SobolevRemarkScStructures

/-!
# The sc-structure `W^{1+m,p}` on a cube, part 1: the Volterra operator on `Lᵖ(0,1)`

Hofer–Wysocki–Zehnder, 2021 §5.5, the remark after Theorem 5.5.5 (pp. 230–231; preprint
pp. 193–194) equips `W^{1,4}(Ω)`, `Ω` a bounded domain, with the sc-structure `E_m = W^{1+m,4}(Ω)`.
The files `SobolevCubeVolterra–5` construct this sc-structure for the open unit cube
`Ω = (0,1)¹ ⊆ ℝ¹` and every `p > 1`: compactness of the inclusions (Rellich) and density of `E_∞`.

This file is the one-dimensional analysis on `I = (0,1)`:

* `μI`, `L p`: Lebesgue measure on `I`, the space `Lᵖ(I)`;
* `Vf g x = ∫₀ˣ g` (the Volterra operator), with the Hölder estimate
  `|Vf g x − Vf g y| ≤ ‖g‖_{Lᵖ} |x − y|^{1 − 1/p}` (`abs_Vf_sub_le`), and `|Vf g x| ≤ ‖g‖`
  on `[0,1]`;
* `V : Lᵖ(I) →L Lᵖ(I)`, `‖V g‖ ≤ ‖g‖`;
* **`isCompactOperator_V`** (`p > 1`): `V` is compact, since the image of the unit ball is
  determined up to `ε` by finitely many point values (equicontinuity, as in Arzelà–Ascoli).
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevCube

/-! ### The interval and its `Lᵖ` space -/

/-- The unit interval `I = (0,1)`. -/
abbrev I : Set ℝ := Ioo 0 1

/-- Lebesgue measure on `I`. -/
abbrev μI : Measure ℝ := volume.restrict I

instance isFiniteMeasure_μI : IsFiniteMeasure μI :=
  isFiniteMeasure_restrict.2 (by simp)

lemma μI_univ : μI univ = 1 := by simp

lemma measureUnivNNReal_μI : measureUnivNNReal μI = 1 := by
  simp [measureUnivNNReal]

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- `Lᵖ(I)`. -/
abbrev L (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] : Type := Lp ℝ (ENNReal.ofReal p) μI

lemma one_le_p : 1 ≤ p := BonicFrampton.one_le_p (p := p)

lemma p_pos : 0 < p := BonicFrampton.p_pos (p := p)

/-- A function of `Lᵖ(I)` bounded by `C` almost everywhere has norm at most `C`. -/
lemma norm_le_of_ae_bound' {f : L p} {C : ℝ} (hC : 0 ≤ C) (h : ∀ᵐ x ∂μI, ‖f x‖ ≤ C) :
    ‖f‖ ≤ C := by
  have := Lp.norm_le_of_ae_bound hC h
  simpa [measureUnivNNReal_μI] using this

lemma integrable_L (g : L p) : Integrable g μI :=
  (Lp.memLp g).integrable hP.out

/-- The extension of `g ∈ Lᵖ(I)` by zero. -/
def ext0 (g : L p) : ℝ → ℝ := I.indicator g

lemma integrable_ext0 (g : L p) : Integrable (ext0 g) :=
  (integrable_indicator_iff measurableSet_Ioo).2 (integrable_L g)

/-- Functions equal `μI`-a.e. have `volume`-a.e. equal extensions by zero. -/
lemma indicator_ae_eq {f g : ℝ → ℝ} (h : f =ᵐ[μI] g) : I.indicator f =ᵐ[volume] I.indicator g := by
  have := (ae_restrict_iff' measurableSet_Ioo).1 h
  filter_upwards [this] with x hx
  by_cases hxI : x ∈ I
  · simp [indicator_of_mem hxI, hx hxI]
  · simp [indicator_of_notMem hxI]

/-! ### Hölder on subsets -/

/-- **Hölder**: `∫_s |g| ≤ ‖g‖_{Lᵖ} μ(s)^{1−1/p}`. -/
lemma integral_abs_le (g : L p) (s : Set ℝ) :
    ∫ t in s, |g t| ∂μI ≤ ‖g‖ * (μI s).toReal ^ (1 - 1 / p) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hP.out
  have hfin := measure_lt_top μI s
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μI.restrict s) hp1
    (Lp.aestronglyMeasurable g).restrict
  have h2 : eLpNorm g (ENNReal.ofReal p) (μI.restrict s) ≤ eLpNorm g (ENNReal.ofReal p) μI :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [Measure.restrict_apply_univ, ENNReal.toReal_one, ENNReal.toReal_ofReal p_pos.le] at h1
  have hlt := Lp.eLpNorm_lt_top g
  have h3 : eLpNorm g 1 (μI.restrict s) ≤
      eLpNorm g (ENNReal.ofReal p) μI * μI s ^ (1 / 1 - 1 / p) :=
    h1.trans (mul_le_mul_left h2 _)
  have hint : ∫ t in s, |g t| ∂μI = (eLpNorm g 1 (μI.restrict s)).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
      (Lp.aestronglyMeasurable g).restrict]
    rfl
  rw [hint, Lp.norm_def]
  have hexp : (0 : ℝ) ≤ 1 / 1 - 1 / p := by
    rw [div_one, sub_nonneg, div_le_one p_pos]; exact one_le_p
  calc (eLpNorm g 1 (μI.restrict s)).toReal
      ≤ (eLpNorm g (ENNReal.ofReal p) μI * μI s ^ (1 / 1 - 1 / p)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hlt.ne
          (ENNReal.rpow_ne_top_of_nonneg hexp hfin.ne)) h3
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, div_one]

/-! ### The Volterra operator -/

/-- `Vf g x = ∫₀ˣ g`. -/
def Vf (g : L p) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, ext0 g t

lemma Vf_zero (g : L p) : Vf g 0 = 0 := intervalIntegral.integral_same

lemma continuous_Vf (g : L p) : Continuous (Vf g) :=
  intervalIntegral.continuous_primitive (fun _ _ => (integrable_ext0 g).intervalIntegrable) 0

lemma Vf_sub (g : L p) {x y : ℝ} (h : y ≤ x) : Vf g x - Vf g y = ∫ t in Ioc y x, g t ∂μI := by
  rw [Vf, Vf, intervalIntegral.integral_interval_sub_left (integrable_ext0 g).intervalIntegrable
    (integrable_ext0 g).intervalIntegrable, intervalIntegral.integral_of_le h, ext0,
    setIntegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioc]

lemma Vf_eq (g : L p) {x : ℝ} (hx : 0 ≤ x) : Vf g x = ∫ t in Ioc 0 x, g t ∂μI := by
  rw [← Vf_sub g hx, Vf_zero, sub_zero]

lemma μI_Ioc_le {x y : ℝ} (h : y ≤ x) : (μI (Ioc y x)).toReal ≤ x - y := by
  have : μI (Ioc y x) ≤ ENNReal.ofReal (x - y) := by
    calc μI (Ioc y x) ≤ volume (Ioc y x) := Measure.restrict_apply_le _ _
      _ = ENNReal.ofReal (x - y) := Real.volume_Ioc
  calc (μI (Ioc y x)).toReal ≤ (ENNReal.ofReal (x - y)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = x - y := ENNReal.toReal_ofReal (sub_nonneg.2 h)

lemma exp_nonneg : (0 : ℝ) ≤ 1 - 1 / p := by
  rw [sub_nonneg, div_le_one p_pos]; exact one_le_p

/-- **The Hölder estimate**: `|∫_y^x g| ≤ ‖g‖_{Lᵖ} (x − y)^{1 − 1/p}`. -/
lemma abs_Vf_sub_le (g : L p) {x y : ℝ} (h : y ≤ x) :
    |Vf g x - Vf g y| ≤ ‖g‖ * (x - y) ^ (1 - 1 / p) := by
  rw [Vf_sub g h]
  calc |∫ t in Ioc y x, g t ∂μI| ≤ ∫ t in Ioc y x, |g t| ∂μI := abs_integral_le_integral_abs
    _ ≤ ‖g‖ * (μI (Ioc y x)).toReal ^ (1 - 1 / p) := integral_abs_le g _
    _ ≤ ‖g‖ * (x - y) ^ (1 - 1 / p) := by
        gcongr
        · exact exp_nonneg
        · exact μI_Ioc_le h

lemma abs_Vf_le (g : L p) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : |Vf g x| ≤ ‖g‖ := by
  have := abs_Vf_sub_le g h0
  rw [Vf_zero, sub_zero, sub_zero] at this
  refine this.trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
  exact Real.rpow_le_one h0 h1 exp_nonneg

lemma ext0_add (g h : L p) : ext0 (g + h) =ᵐ[volume] ext0 g + ext0 h := by
  have := indicator_ae_eq (Lp.coeFn_add g h)
  filter_upwards [this] with x hx
  rw [ext0, hx]
  by_cases hxI : x ∈ I
  · simp only [indicator_of_mem hxI, Pi.add_apply, ext0]
  · simp only [indicator_of_notMem hxI, Pi.add_apply, ext0, add_zero]

lemma ext0_smul (c : ℝ) (g : L p) : ext0 (c • g) =ᵐ[volume] c • ext0 g := by
  have := indicator_ae_eq (Lp.coeFn_smul c g)
  filter_upwards [this] with x hx
  rw [ext0, hx]
  by_cases hxI : x ∈ I
  · simp only [indicator_of_mem hxI, Pi.smul_apply, ext0]
  · simp only [indicator_of_notMem hxI, Pi.smul_apply, ext0, smul_zero]

lemma Vf_add (g h : L p) : Vf (g + h) = Vf g + Vf h := by
  funext x
  simp only [Vf, Pi.add_apply]
  rw [← intervalIntegral.integral_add (integrable_ext0 g).intervalIntegrable
    (integrable_ext0 h).intervalIntegrable]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ext0_add g h] with t ht _
  rw [ht]; rfl

lemma Vf_smul (c : ℝ) (g : L p) : Vf (c • g) = c • Vf g := by
  funext x
  simp only [Vf, Pi.smul_apply]
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ext0_smul c g] with t ht _
  rw [ht]; rfl

lemma ae_abs_Vf_le (g : L p) : ∀ᵐ x ∂μI, ‖Vf g x‖ ≤ ‖g‖ :=
  (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun _ hx =>
    abs_Vf_le g hx.1.le hx.2.le)

lemma memLp_Vf (g : L p) : MemLp (Vf g) (ENNReal.ofReal p) μI :=
  MemLp.of_bound (continuous_Vf g).aestronglyMeasurable ‖g‖ (ae_abs_Vf_le g)

/-- `V` as a linear map. -/
def Vlin : L p →ₗ[ℝ] L p where
  toFun g := (memLp_Vf g).toLp _
  map_add' g h := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff, Vf_add]
  map_smul' c g := by
    rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff, Vf_smul]; rfl

lemma norm_Vlin_le (g : L p) : ‖Vlin g‖ ≤ ‖g‖ := by
  refine norm_le_of_ae_bound' (norm_nonneg _) ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_Vf g), ae_abs_Vf_le g] with x hx h
  change ‖((memLp_Vf g).toLp _ : ℝ → ℝ) x‖ ≤ _
  rw [hx]; exact h

/-- **The Volterra operator** `V : Lᵖ(I) → Lᵖ(I)`, `(V g)(x) = ∫₀ˣ g`. -/
def V : L p →L[ℝ] L p :=
  Vlin.mkContinuous 1 fun g => by rw [one_mul]; exact norm_Vlin_le g

lemma coeFn_V (g : L p) : (V g : ℝ → ℝ) =ᵐ[μI] Vf g :=
  MemLp.coeFn_toLp (memLp_Vf g)

lemma norm_V_le (g : L p) : ‖V g‖ ≤ ‖g‖ := norm_Vlin_le g

/-! ### Compactness -/

lemma floor_bounds {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ I) :
    ⌊(N : ℝ) * x⌋₊ < N ∧ ((⌊(N : ℝ) * x⌋₊ : ℕ) : ℝ) / N ≤ x ∧
      x - ((⌊(N : ℝ) * x⌋₊ : ℕ) : ℝ) / N ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg hN'.le hx.1.le
  have h1 := Nat.floor_le hNx
  have h2 := Nat.lt_floor_add_one ((N : ℝ) * x)
  refine ⟨?_, ?_, ?_⟩
  · have : (N : ℝ) * x < N := by nlinarith [hx.2]
    exact_mod_cast (Nat.floor_lt hNx).2 this
  · rw [div_le_iff₀ hN']; linarith
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN']; linarith

/-- The point values `Vf g (i/N)` determine `V g` up to `2 (1/N)^{1−1/p}` on the unit ball. -/
lemma dist_V_le {N : ℕ} (hN : 0 < N) {g h : L p} (hg : ‖g‖ ≤ 1) (hh : ‖h‖ ≤ 1) :
    dist (V g) (V h) ≤ 2 * (1 / (N : ℝ)) ^ (1 - 1 / p) +
      dist (fun i : Fin (N + 1) => Vf g ((i : ℝ) / N))
        (fun i : Fin (N + 1) => Vf h ((i : ℝ) / N)) := by
  rw [dist_eq_norm]
  set δ : ℝ := (1 / (N : ℝ)) ^ (1 - 1 / p)
  set D := dist (fun i : Fin (N + 1) => Vf g ((i : ℝ) / N))
    (fun i : Fin (N + 1) => Vf h ((i : ℝ) / N))
  have hδ : 0 ≤ δ := Real.rpow_nonneg (by positivity) _
  refine norm_le_of_ae_bound' (by positivity) ?_
  filter_upwards [Lp.coeFn_sub (V g) (V h), coeFn_V g, coeFn_V h,
    ae_restrict_mem measurableSet_Ioo] with x e1 e2 e3 hx
  rw [e1, Pi.sub_apply, e2, e3]
  obtain ⟨hi, hle, hsub⟩ := floor_bounds hN hx
  set i := ⌊(N : ℝ) * x⌋₊
  have hpow : (x - (i : ℝ) / N) ^ (1 - 1 / p) ≤ δ :=
    Real.rpow_le_rpow (sub_nonneg.2 hle) hsub exp_nonneg
  have ha := abs_Vf_sub_le g hle
  have hb := abs_Vf_sub_le h hle
  have hc : |Vf g ((i : ℝ) / N) - Vf h ((i : ℝ) / N)| ≤ D := by
    have := dist_le_pi_dist (fun j : Fin (N + 1) => Vf g ((j : ℝ) / N))
      (fun j : Fin (N + 1) => Vf h ((j : ℝ) / N)) ⟨i, by omega⟩
    simpa [Real.dist_eq] using this
  have ha' : |Vf g x - Vf g ((i : ℝ) / N)| ≤ δ :=
    ha.trans ((mul_le_mul hg hpow (Real.rpow_nonneg (sub_nonneg.2 hle) _) zero_le_one).trans
      (by rw [one_mul]))
  have hb' : |Vf h x - Vf h ((i : ℝ) / N)| ≤ δ :=
    hb.trans ((mul_le_mul hh hpow (Real.rpow_nonneg (sub_nonneg.2 hle) _) zero_le_one).trans
      (by rw [one_mul]))
  rw [Real.norm_eq_abs]
  calc |Vf g x - Vf h x|
      = |(Vf g x - Vf g ((i : ℝ) / N)) + (Vf g ((i : ℝ) / N) - Vf h ((i : ℝ) / N)) -
          (Vf h x - Vf h ((i : ℝ) / N))| := by ring_nf
    _ ≤ |Vf g x - Vf g ((i : ℝ) / N)| + |Vf g ((i : ℝ) / N) - Vf h ((i : ℝ) / N)| +
          |Vf h x - Vf h ((i : ℝ) / N)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ δ + D + δ := by gcongr
    _ = 2 * δ + D := by ring

/-- **The Volterra operator is compact on `Lᵖ(0,1)`, `p > 1`.** -/
theorem isCompactOperator_V (hp : 1 < p) : IsCompactOperator (V (p := p)) := by
  have hθ : 0 < 1 - 1 / p := by
    rw [sub_pos, div_lt_one p_pos]; exact hp
  have htb : TotallyBounded (V '' Metric.ball (0 : L p) 1) := by
    refine GapP1Sobolev.totallyBounded_image_of_coords _ fun ε hε => ?_
    have hlim : Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-(1 - 1 / p))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hNε, hN⟩ :=
      ((hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).and
        (eventually_gt_atTop 0)).exists
    have hδ : (1 / (N : ℝ)) ^ (1 - 1 / p) < ε / 4 := by
      rwa [one_div, Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _)]
    refine ⟨Fin (N + 1) → ℝ, inferInstance, inferInstance,
      fun g => fun i : Fin (N + 1) => Vf g ((i : ℝ) / N), ε / 2, by positivity, ?_, ?_⟩
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hg
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      have hi : (i : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 i.2
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      refine (abs_Vf_le g (by positivity) ((div_le_one hN').2 hi)).trans hg.le
    · intro g hg h hh hd
      rw [Metric.mem_ball, dist_zero_right] at hg hh
      refine (dist_V_le hN hg.le hh.le).trans_lt ?_
      linarith
  refine (isCompactOperator_iff_image_ball_subset_compact (V : L p →L[ℝ] L p).toLinearMap
    one_pos).2 ⟨closure (V '' Metric.ball 0 1), ?_, subset_closure⟩
  exact isCompact_iff_totallyBounded_isComplete.2 ⟨htb.closure, isClosed_closure.isComplete⟩

end SobolevCube

end Polyfold
