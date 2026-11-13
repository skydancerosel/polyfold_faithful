import Polyfold.Chapter9.DimensionJumpRetract

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), gap G.110: the M-polyfold `X`.

# `X = {(−1,0)} ∪ ((−1,1) × B) ∪ {(1,0)} ⊆ ℝ × ℂ` as an M-polyfold

## The text, paraphrased
(p. 451) `B` is the open unit disk in `ℂ`, `X = {(−1,0)} ∪ ((−1,1) × B) ∪ {(1,0)} ⊆ ℝ × ℂ`, and "one
can equip `X` with an M-polyfold structure"; (p. 452) `∂X = {(−1,0), (1,0)}`.

## What is formalized
* `K3.Xs ⊆ ℝ × ℂ` and the space `K3.XR` (subspace topology).
* The fibres of the retract `O` of `DimensionJumpRetract.lean`: `β τ = Σ b_k(τ) e_{n_k}` spans the range
  of `fam τ` for `τ > 0` and `fam τ y = coef τ y • β τ` (`fam_eq_coef_smul`, every `τ`).
* **`K3.chart`**: the homeomorphism `X → O`,
  `(t, z) ↦ (2(cos θ, sin θ), Re w · β_τ, Im w · β_τ)`, `θ = π(1+t)/4`, `τ = 4 cos θ sin θ`,
  `w = z/√(1−|z|²)`; its inverse uses `arg` and `coef`.  **`K3.P : MPolyfold XR`**, the M-polyfold
  with this one chart.
* **`K3.degIndex_eq`**: `d_X(t,z) = 1` at `(±1,0)` and `0` elsewhere, i.e. `∂X = {(−1,0),(1,0)}`
  (`K3.boundary_eq`).  The upper bound is read in the chart; the lower bound is Theorem 2.4.12: at the
  end point the tangent space of `O` contains the inward normal of the face.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped ContDiff Real

noncomputable section

namespace Polyfold

namespace K3

open RemarkFourThree ScOneExample

/-! ### The fibres: `β τ` and the coefficient `coef τ` -/

/-- The unit vector `β_τ = Σ_k b_k(τ) e_{n_k}` spanning the range of `fam τ` (`0` for `τ ≤ 0`). -/
def β (τ : ℝ) : c0 := ∑ k ∈ supp τ, bb k τ • δv (nk k)

/-- The coefficient `y ↦ Σ_k b_k(τ) y_{n_k}`. -/
def coef (τ : ℝ) (y : c0) : ℝ := ∑ k ∈ supp τ, bb k τ * y (nk k)

lemma β_eq_sum {τ : ℝ} {s : Finset ℕ} (hs : supp τ ⊆ s) :
    β τ = ∑ k ∈ s, bb k τ • δv (nk k) :=
  Finset.sum_subset hs fun k _ hk => by rw [bb_eq_zero_of_not_mem hk, zero_smul]

lemma coef_eq_sum {τ : ℝ} {s : Finset ℕ} (hs : supp τ ⊆ s) (y : c0) :
    coef τ y = ∑ k ∈ s, bb k τ * y (nk k) :=
  Finset.sum_subset hs fun k _ hk => by rw [bb_eq_zero_of_not_mem hk, zero_mul]

lemma β_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) : β τ = 0 := by
  rw [β, supp, if_neg (not_lt.2 hτ), Finset.sum_empty]

lemma coef_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) (y : c0) : coef τ y = 0 := by
  rw [coef, supp, if_neg (not_lt.2 hτ), Finset.sum_empty]

lemma β_of_pos {τ : ℝ} (hτ : 0 < τ) :
    β τ = cc (kt τ) τ • δv (nk (kt τ)) + ss (kt τ) τ • δv (nk (kt τ + 1)) := by
  rw [β, supp, if_pos hτ, Finset.sum_pair (by omega), bb_kt hτ, bb_kt_succ hτ]

lemma coef_of_pos {τ : ℝ} (hτ : 0 < τ) (y : c0) :
    coef τ y = cc (kt τ) τ * y (nk (kt τ)) + ss (kt τ) τ * y (nk (kt τ + 1)) := by
  rw [coef, supp, if_pos hτ, Finset.sum_pair (by omega), bb_kt hτ, bb_kt_succ hτ]

lemma β_apply_of_pos {τ : ℝ} (hτ : 0 < τ) (i : ℕ) :
    β τ i = (if i = nk (kt τ) then cc (kt τ) τ else 0) +
      (if i = nk (kt τ + 1) then ss (kt τ) τ else 0) := by
  rw [β_of_pos hτ]
  simp only [ZeroAtInftyContinuousMap.coe_add, ZeroAtInftyContinuousMap.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, δv_apply]
  split_ifs <;> simp

lemma coef_add (τ : ℝ) (y y' : c0) : coef τ (y + y') = coef τ y + coef τ y' := by
  simp only [coef, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma coef_smul (τ c : ℝ) (y : c0) : coef τ (c • y) = c * coef τ y := by
  simp only [coef, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma coef_β {τ : ℝ} (hτ : 0 < τ) : coef τ (β τ) = 1 := by
  have hne := nk_ne (kt τ)
  rw [coef_of_pos hτ, β_apply_of_pos hτ, β_apply_of_pos hτ, if_pos rfl, if_neg hne,
    if_neg hne.symm, if_pos rfl]
  have := cc_sq_add_ss_sq (kt τ) τ
  linear_combination this

lemma coef_smul_β {τ : ℝ} (hτ : 0 < τ) (c : ℝ) : coef τ (c • β τ) = c := by
  rw [coef_smul, coef_β hτ, mul_one]

/-- **`fam τ y = coef τ y • β τ`** (every `τ`). -/
theorem fam_eq_coef_smul (τ : ℝ) (y : c0) : fam τ 0 y = coef τ y • β τ := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [fam_of_nonpos hτ, β_of_nonpos hτ, smul_zero]; rfl
  · ext i
    have hne := nk_ne (kt τ)
    rw [fam_zero_apply_of_pos hτ, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
      β_apply_of_pos hτ, coef_of_pos hτ, smul_eq_mul]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hne
    · ring
    · ring
    · ring

lemma fam_smul_β (τ c : ℝ) : fam τ 0 (c • β τ) = c • β τ := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [β_of_nonpos hτ, smul_zero, map_zero]
  · rw [fam_eq_coef_smul, coef_smul_β hτ]

lemma norm_β_le (τ : ℝ) : ‖β τ‖ ≤ 2 := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [β_of_nonpos hτ, norm_zero]; norm_num
  · rw [β_of_pos hτ]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖cc (kt τ) τ • δv (nk (kt τ))‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_one₀ (abs_cc_le _ _) (norm_nonneg _) (norm_δv_le _)
    have h2 : ‖ss (kt τ) τ • δv (nk (kt τ + 1))‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_one₀ (abs_ss_le _ _) (norm_nonneg _) (norm_δv_le _)
    linarith

lemma abs_coef_le (τ : ℝ) (y : c0) : |coef τ y| ≤ 2 * ‖y‖ := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [coef_of_nonpos hτ, abs_zero]; positivity
  · rw [coef_of_pos hτ]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul (abs_cc_le (kt τ) τ) (abs_apply_le_norm y (nk (kt τ))) (abs_nonneg _)
      zero_le_one
    have h2 := mul_le_mul (abs_ss_le (kt τ) τ) (abs_apply_le_norm y (nk (kt τ + 1)))
      (abs_nonneg _) zero_le_one
    linarith

/-- Near `t₀ > 0` the support of `k ↦ b_k(τ)` lies in a fixed finite set. -/
lemma supp_subset_range {t₀ τ : ℝ} (ht₀ : 0 < t₀) (hτ : t₀ / 2 < τ) :
    supp τ ⊆ Finset.range (⌈2 / t₀⌉₊ + 2) := by
  have hτ0 : 0 < τ := lt_trans (by positivity) hτ
  rw [supp, if_pos hτ0]
  have hinv : τ⁻¹ < 2 / t₀ := by
    rw [inv_lt_comm₀ hτ0 (by positivity)]
    rwa [inv_div]
  have hfl : ⌊τ⁻¹⌋₊ ≤ ⌈2 / t₀⌉₊ := by
    have h1 : (⌊τ⁻¹⌋₊ : ℝ) ≤ τ⁻¹ := Nat.floor_le (inv_nonneg.2 hτ0.le)
    have h2 : 2 / t₀ ≤ ⌈2 / t₀⌉₊ := Nat.le_ceil _
    exact_mod_cast (h1.trans (hinv.le.trans h2))
  intro k hk
  rw [Finset.mem_range]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  unfold kt at hk
  omega

lemma continuousOn_β : ContinuousOn β (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hev : ∀ᶠ τ in 𝓝 t₀, β τ = ∑ k ∈ Finset.range (⌈2 / t₀⌉₊ + 2), bb k τ • δv (nk k) := by
    filter_upwards [Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith)] with τ hτ
    exact β_eq_sum (supp_subset_range ht₀' hτ)
  refine (ContinuousAt.congr ?_ (hev.mono fun _ h => h.symm)).continuousWithinAt
  exact (continuous_finsetSum _ fun k _ =>
    ((contDiff_bb k).continuous.smul continuous_const)).continuousAt

lemma continuousOn_coef : ContinuousOn (fun q : ℝ × c0 => coef q.1 q.2) (Ioi 0 ×ˢ univ) := by
  rintro ⟨t₀, y₀⟩ ⟨ht₀, -⟩
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hev : ∀ᶠ q : ℝ × c0 in 𝓝 (t₀, y₀), coef q.1 q.2 =
      ∑ k ∈ Finset.range (⌈2 / t₀⌉₊ + 2), bb k q.1 * evalL (nk k) q.2 := by
    filter_upwards [(continuous_fst.tendsto (t₀, y₀)).eventually
      (Ioi_mem_nhds (show t₀ / 2 < t₀ by linarith))] with q hq
    exact coef_eq_sum (supp_subset_range ht₀' hq) q.2
  refine (ContinuousAt.congr ?_ (hev.mono fun _ h => h.symm)).continuousWithinAt
  exact (continuous_finsetSum _ fun k _ =>
    ((contDiff_bb k).continuous.comp continuous_fst).mul
      ((evalL (nk k)).continuous.comp continuous_snd)).continuousAt

/-! ### The set `X ⊆ ℝ × ℂ` -/

/-- **The set `X = {(−1,0)} ∪ ((−1,1) × B) ∪ {(1,0)} ⊆ ℝ × ℂ`** of Remark 9.5.20. -/
def Xs : Set (ℝ × ℂ) := {(-1, 0), (1, 0)} ∪ (Ioo (-1) 1 ×ˢ Metric.ball 0 1)

/-- `X` with the subspace topology of `ℝ × ℂ`. -/
abbrev XR : Type := Xs

example : T2Space XR := inferInstance
example : ParacompactSpace XR := inferInstance

lemma mem_Xs_iff {x : ℝ × ℂ} :
    x ∈ Xs ↔ x = (-1, 0) ∨ x = (1, 0) ∨ (x.1 ∈ Ioo (-1) 1 ∧ ‖x.2‖ < 1) := by
  simp only [Xs, mem_union, mem_insert_iff, mem_singleton_iff, mem_prod, Metric.mem_ball,
    dist_zero_right, or_assoc]

lemma norm_lt_one_of_mem {x : ℝ × ℂ} (hx : x ∈ Xs) : ‖x.2‖ < 1 := by
  rcases mem_Xs_iff.1 hx with rfl | rfl | h
  · simp
  · simp
  · exact h.2

lemma fst_mem_Icc_of_mem {x : ℝ × ℂ} (hx : x ∈ Xs) : x.1 ∈ Icc (-1) 1 := by
  rcases mem_Xs_iff.1 hx with rfl | rfl | h
  · simp
  · simp
  · exact Ioo_subset_Icc_self h.1

/-! ### The disk `B` and the plane -/

/-- `w(z) = z/√(1−|z|²)`, a homeomorphism of `B` onto `ℂ`. -/
def wdisk (z : ℂ) : ℂ := ((√(1 - ‖z‖ ^ 2))⁻¹ : ℝ) • z

/-- Its inverse `w ↦ w/√(1+|w|²)`. -/
def wback (w : ℂ) : ℂ := ((√(1 + ‖w‖ ^ 2))⁻¹ : ℝ) • w

lemma wback_wdisk {z : ℂ} (hz : ‖z‖ < 1) : wback (wdisk z) = z := by
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  set s := √(1 - ‖z‖ ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hss : s ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt hpos.le
  have hn : ‖wdisk z‖ = ‖z‖ / s := by
    rw [wdisk, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, inv_mul_eq_div]
  have h1 : 1 + ‖wdisk z‖ ^ 2 = (1 / s) ^ 2 := by
    rw [hn, div_pow, div_pow, one_pow, hss]
    field_simp
    ring
  rw [wback, h1, Real.sqrt_sq (by positivity), wdisk, smul_smul, ← hs, one_div, inv_inv,
    mul_inv_cancel₀ hs0.ne', one_smul]

lemma wdisk_wback (w : ℂ) : wdisk (wback w) = w := by
  set r := √(1 + ‖w‖ ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hrr : r ^ 2 = 1 + ‖w‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hn : ‖wback w‖ = ‖w‖ / r := by
    rw [wback, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, inv_mul_eq_div]
  have h1 : 1 - ‖wback w‖ ^ 2 = (1 / r) ^ 2 := by
    rw [hn, div_pow, div_pow, one_pow]
    field_simp
    linarith
  rw [wdisk, h1, Real.sqrt_sq (by positivity), wback, smul_smul, ← hr, one_div, inv_inv,
    mul_inv_cancel₀ hr0.ne', one_smul]

lemma norm_wback_lt (w : ℂ) : ‖wback w‖ < 1 := by
  have hr0 : 0 < √(1 + ‖w‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [wback, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, inv_mul_lt_iff₀ hr0, mul_one]
  calc ‖w‖ = √(‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
    _ < √(1 + ‖w‖ ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

lemma wback_zero : wback 0 = 0 := by rw [wback, smul_zero]

lemma wdisk_zero : wdisk 0 = 0 := by rw [wdisk, smul_zero]

lemma continuous_wback : Continuous wback := by
  have h : Continuous fun w : ℂ => (√(1 + ‖w‖ ^ 2))⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun w => (Real.sqrt_pos.2 (by positivity)).ne'
  exact h.smul continuous_id

lemma continuousOn_wdisk : ContinuousOn wdisk (Metric.ball 0 1) := by
  have h : ContinuousOn (fun z : ℂ => (√(1 - ‖z‖ ^ 2))⁻¹) (Metric.ball 0 1) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun z hz => (Real.sqrt_pos.2 ?_).ne'
    rw [Metric.mem_ball, dist_zero_right] at hz
    nlinarith [norm_nonneg z]
  exact h.smul continuousOn_id

/-! ### The quarter circle -/

/-- `θ(t) = π(1+t)/4`. -/
def θ (t : ℝ) : ℝ := π * (1 + t) / 4

/-- `t ↦ 2(cos θ, sin θ)`, the quarter circle from `(2,0)` (`t = −1`) to `(0,2)` (`t = 1`). -/
def arcPt (t : ℝ) : V2 := ![2 * Real.cos (θ t), 2 * Real.sin (θ t)]

/-- `τ(t) = G(arcPt t)`, the parameter of the projections over `arcPt t`. -/
def τ (t : ℝ) : ℝ := G (arcPt t)

lemma θ_mem {t : ℝ} (ht : t ∈ Icc (-1) 1) : θ t ∈ Icc 0 (π / 2) := by
  have := Real.pi_pos
  constructor <;> unfold θ <;> nlinarith [ht.1, ht.2]

lemma arcPt_mem_arc {t : ℝ} (ht : t ∈ Icc (-1) 1) : arcPt t ∈ arc := by
  have h := θ_mem ht
  have hc : 0 ≤ Real.cos (θ t) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, h.1], h.2⟩
  have hs : 0 ≤ Real.sin (θ t) := Real.sin_nonneg_of_nonneg_of_le_pi h.1 (by linarith [h.2, Real.pi_pos])
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [arcPt] <;> assumption
  · simp only [len, arcPt, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (2 * Real.cos (θ t)) ^ 2 + (2 * Real.sin (θ t)) ^ 2 = 2 ^ 2 by
      nlinarith [Real.cos_sq_add_sin_sq (θ t)]]
    exact Real.sqrt_sq zero_le_two

lemma τ_pos {t : ℝ} (ht : t ∈ Ioo (-1) 1) : 0 < τ t := by
  have := Real.pi_pos
  have h1 : 0 < θ t := by unfold θ; nlinarith [ht.1]
  have h2 : θ t < π / 2 := by unfold θ; nlinarith [ht.2]
  have hc : 0 < Real.cos (θ t) := Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have hs : 0 < Real.sin (θ t) := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  simp only [τ, G, arcPt, Matrix.cons_val_zero, Matrix.cons_val_one]
  positivity

lemma τ_neg_one : τ (-1) = 0 := by
  simp [τ, G, arcPt, θ]

lemma τ_one : τ 1 = 0 := by
  simp only [τ, G, arcPt, θ, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show π * (1 + 1) / 4 = π / 2 by ring, Real.cos_pi_div_two]
  ring

/-- The parameter of a point of the quarter circle: `t = 4 arg(p₀ + i p₁)/π − 1`. -/
def tOf (p : V2) : ℝ := 4 / π * Complex.arg ⟨p 0, p 1⟩ - 1

lemma tOf_arcPt {t : ℝ} (ht : t ∈ Icc (-1) 1) : tOf (arcPt t) = t := by
  have h := θ_mem ht
  have hpi := Real.pi_pos
  have e : (⟨arcPt t 0, arcPt t 1⟩ : ℂ) =
      ((2 : ℝ) : ℂ) * (Complex.cos (θ t) + Complex.sin (θ t) * Complex.I) := by
    apply Complex.ext <;> simp [arcPt, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [tOf, e, Complex.arg_real_mul _ two_pos,
    Complex.arg_cos_add_sin_mul_I ⟨by linarith [h.1], by linarith [h.2]⟩]
  unfold θ
  field_simp
  ring

lemma tOf_mem_Icc {p : V2} (hp : p ∈ arc) : tOf p ∈ Icc (-1) 1 := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ Complex.arg ⟨p 0, p 1⟩ := Complex.arg_nonneg_iff.2 (hp.1 1)
  have h1 : Complex.arg ⟨p 0, p 1⟩ ≤ π / 2 := Complex.arg_le_pi_div_two_iff.2 (Or.inl (hp.1 0))
  constructor
  · unfold tOf
    have : 0 ≤ 4 / π * Complex.arg ⟨p 0, p 1⟩ := by positivity
    linarith
  · unfold tOf
    have : 4 / π * Complex.arg ⟨p 0, p 1⟩ ≤ 4 / π * (π / 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [show 4 / π * (π / 2) = 2 by field_simp; ring] at this
    linarith

lemma norm_mk_of_mem_arc {p : V2} (hp : p ∈ arc) : ‖(⟨p 0, p 1⟩ : ℂ)‖ = 2 := by
  rw [Complex.norm_def, Complex.normSq_mk, ← hp.2, len]
  congr 1
  ring

lemma arcPt_tOf {p : V2} (hp : p ∈ arc) : arcPt (tOf p) = p := by
  have hpi := Real.pi_pos
  have hθ : θ (tOf p) = Complex.arg ⟨p 0, p 1⟩ := by
    unfold θ tOf
    field_simp
    ring
  have hn := norm_mk_of_mem_arc hp
  have hc := Complex.norm_mul_cos_arg (⟨p 0, p 1⟩ : ℂ)
  have hs := Complex.norm_mul_sin_arg (⟨p 0, p 1⟩ : ℂ)
  rw [hn] at hc hs
  funext i
  fin_cases i
  · simp only [arcPt, hθ]
    exact hc
  · simp only [arcPt, hθ]
    exact hs

lemma mem_slitPlane_of_mem_arc {p : V2} (hp : p ∈ arc) : (⟨p 0, p 1⟩ : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases h1 : p 1 = 0
  · left
    have hn := norm_mk_of_mem_arc hp
    rw [Complex.norm_def, Complex.normSq_mk, h1, mul_zero, add_zero] at hn
    have h0 := hp.1 0
    change 0 < p 0
    by_contra hle
    have : p 0 = 0 := le_antisymm (not_lt.1 hle) h0
    rw [this] at hn
    simp at hn
  · exact Or.inr h1

lemma continuous_mk2 : Continuous fun p : V2 => (⟨p 0, p 1⟩ : ℂ) := by
  have e : (fun p : V2 => (⟨p 0, p 1⟩ : ℂ)) =
      fun p => ((p 0 : ℝ) : ℂ) + ((p 1 : ℝ) : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp
  rw [e]
  fun_prop

lemma continuousOn_tOf : ContinuousOn tOf arc := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  unfold tOf
  refine ((continuousAt_const.mul ?_).sub continuousAt_const)
  exact (Complex.continuousAt_arg (mem_slitPlane_of_mem_arc hp)).comp
    (f := fun p : V2 => (⟨p 0, p 1⟩ : ℂ)) continuous_mk2.continuousAt

lemma continuous_arcPt : Continuous arcPt := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [arcPt, θ] <;> fun_prop

lemma continuous_τ : Continuous τ := by
  change Continuous fun t => arcPt t 0 * arcPt t 1
  exact ((continuous_apply 0).comp continuous_arcPt).mul ((continuous_apply 1).comp continuous_arcPt)

/-! ### The chart `X → O` -/

/-- The chart map `(t, z) ↦ (arcPt t, Re w(z) · β_{τ(t)}, Im w(z) · β_{τ(t)})`. -/
def ψfun (x : ℝ × ℂ) : E 0 :=
  (arcPt x.1, ((wdisk x.2).re • β (τ x.1), (wdisk x.2).im • β (τ x.1)))

/-- Its inverse `(p, a, b) ↦ (tOf p, w⁻¹(coef a + i coef b))`. -/
def ψinv (q : E 0) : ℝ × ℂ :=
  (tOf q.1, wback ⟨coef (G q.1) q.2.1, coef (G q.1) q.2.2⟩)

lemma ψfun_mem_O {x : ℝ × ℂ} (hx : x ∈ Xs) : ψfun x ∈ O :=
  (mem_O_iff _).2 ⟨arcPt_mem_arc (fst_mem_Icc_of_mem hx),
    Prod.ext (fam_smul_β _ _) (fam_smul_β _ _)⟩

lemma G_eq_τ_tOf {p : V2} (hp : p ∈ arc) : G p = τ (tOf p) := by
  rw [τ, arcPt_tOf hp]

lemma ψinv_mem {q : E 0} (hq : q ∈ O) : ψinv q ∈ Xs := by
  obtain ⟨harc, -⟩ := (mem_O_iff q).1 hq
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc (tOf_mem_Icc harc) with h | h | h
  · have hG : G q.1 = 0 := by rw [G_eq_τ_tOf harc, h, τ_neg_one]
    rw [mem_Xs_iff]
    left
    simp only [ψinv, hG, coef_of_nonpos le_rfl, h]
    rw [show (⟨0, 0⟩ : ℂ) = 0 from rfl, wback_zero]
  · have hG : G q.1 = 0 := by rw [G_eq_τ_tOf harc, h, τ_one]
    rw [mem_Xs_iff]
    right; left
    simp only [ψinv, hG, coef_of_nonpos le_rfl, h]
    rw [show (⟨0, 0⟩ : ℂ) = 0 from rfl, wback_zero]
  · exact mem_Xs_iff.2 (Or.inr (Or.inr ⟨h, norm_wback_lt _⟩))

lemma ψinv_ψfun {x : ℝ × ℂ} (hx : x ∈ Xs) : ψinv (ψfun x) = x := by
  have ht := fst_mem_Icc_of_mem hx
  have hc : ∀ c : ℝ, (c ≠ 0 → 0 < τ x.1) → coef (τ x.1) (c • β (τ x.1)) = c := by
    intro c hc
    by_cases h0 : c = 0
    · rw [h0, coef_smul, zero_mul]
    · exact coef_smul_β (hc h0) c
  have hpos : x.2 ≠ 0 → 0 < τ x.1 := by
    intro hz
    rcases mem_Xs_iff.1 hx with rfl | rfl | h
    · exact absurd rfl hz
    · exact absurd rfl hz
    · exact τ_pos h.1
  have hw : wdisk x.2 ≠ 0 → x.2 ≠ 0 := fun h h0 => h (by rw [h0, wdisk_zero])
  have e1 : coef (τ x.1) ((wdisk x.2).re • β (τ x.1)) = (wdisk x.2).re :=
    hc _ fun h => hpos (hw fun h' => h (by rw [h']; rfl))
  have e2 : coef (τ x.1) ((wdisk x.2).im • β (τ x.1)) = (wdisk x.2).im :=
    hc _ fun h => hpos (hw fun h' => h (by rw [h']; rfl))
  change (tOf (arcPt x.1), wback ⟨coef (τ x.1) ((wdisk x.2).re • β (τ x.1)),
    coef (τ x.1) ((wdisk x.2).im • β (τ x.1))⟩) = x
  rw [e1, e2, tOf_arcPt ht]
  refine Prod.ext rfl ?_
  change wback (wdisk x.2) = x.2
  exact wback_wdisk (norm_lt_one_of_mem hx)

lemma ψfun_ψinv {q : E 0} (hq : q ∈ O) : ψfun (ψinv q) = q := by
  obtain ⟨harc, hL⟩ := (mem_O_iff q).1 hq
  have h1 : fam (G q.1) 0 q.2.1 = q.2.1 := congrArg Prod.fst hL
  have h2 : fam (G q.1) 0 q.2.2 = q.2.2 := congrArg Prod.snd hL
  rw [fam_eq_coef_smul] at h1 h2
  change (arcPt (tOf q.1), ((wdisk (wback _)).re • β (τ (tOf q.1)),
    (wdisk (wback _)).im • β (τ (tOf q.1)))) = q
  rw [wdisk_wback, ← G_eq_τ_tOf harc, arcPt_tOf harc]
  exact Prod.ext rfl (Prod.ext h1 h2)

/-- The base point `(1, 0)` of `X` (the junk value of the inverse chart off `O`). -/
def x₀ : XR := ⟨(1, 0), mem_Xs_iff.2 (Or.inr (Or.inl rfl))⟩

open scoped Classical in
/-- The inverse chart `E₀ → X`. -/
def chartInv (q : E 0) : XR := if h : ψinv q ∈ Xs then ⟨ψinv q, h⟩ else x₀

lemma chartInv_of_mem {q : E 0} (hq : q ∈ O) : chartInv q = ⟨ψinv q, ψinv_mem hq⟩ := by
  rw [chartInv, dif_pos (ψinv_mem hq)]

/-- A product `c • b` with `c → 0` and `b` bounded tends to `0`. -/
lemma continuousAt_smul_of_bdd {α : Type*} [TopologicalSpace α] {c : α → ℝ} {b : α → c0}
    {x : α} (hc : ContinuousAt c x) (hcx : c x = 0) (hb : ∀ y, ‖b y‖ ≤ 2) :
    ContinuousAt (fun y => c y • b y) x := by
  rw [ContinuousAt, hcx, zero_smul]
  have hc' : Tendsto (fun y => |c y|) (𝓝 x) (𝓝 0) := by
    have h := (show Tendsto c (𝓝 x) (𝓝 0) from hcx ▸ hc).abs
    rwa [abs_zero] at h
  refine squeeze_zero_norm (fun y => ?_) (by simpa using hc'.const_mul 2)
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb y) (abs_nonneg _)

lemma continuousAt_fibre {c : XR → ℝ} (hc : Continuous c)
    (hc0 : ∀ x : XR, x.1.1 ∉ Ioo (-1) 1 → c x = 0) (x : XR) :
    ContinuousAt (fun y : XR => c y • β (τ y.1.1)) x := by
  by_cases hx : x.1.1 ∈ Ioo (-1) 1
  · refine hc.continuousAt.smul ?_
    have hβ : ContinuousAt β (τ x.1.1) :=
      continuousOn_β.continuousAt (Ioi_mem_nhds (τ_pos hx))
    exact ContinuousAt.comp (g := β) (f := fun y : XR => τ y.1.1) hβ
      ((continuous_τ.comp (continuous_fst.comp continuous_subtype_val)).continuousAt)
  · exact continuousAt_smul_of_bdd hc.continuousAt (hc0 x hx) fun y => norm_β_le _

lemma continuous_wdisk_snd : Continuous fun x : XR => wdisk x.1.2 := by
  refine continuousOn_wdisk.comp_continuous (continuous_snd.comp continuous_subtype_val) fun x => ?_
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_lt_one_of_mem x.2

lemma snd_eq_zero_of_not_mem {x : XR} (hx : x.1.1 ∉ Ioo (-1) 1) : x.1.2 = 0 := by
  rcases mem_Xs_iff.1 x.2 with h | h | h
  · rw [h]
  · rw [h]
  · exact absurd h.1 hx

lemma continuous_ψfun : Continuous fun x : XR => ψfun x.1 := by
  refine (continuous_arcPt.comp (continuous_fst.comp continuous_subtype_val)).prodMk ?_
  refine continuous_iff_continuousAt.2 fun x => ContinuousAt.prodMk ?_ ?_
  · refine continuousAt_fibre (Complex.continuous_re.comp continuous_wdisk_snd) (fun y hy => ?_) x
    change (wdisk y.1.2).re = 0
    rw [snd_eq_zero_of_not_mem hy, wdisk_zero, Complex.zero_re]
  · refine continuousAt_fibre (Complex.continuous_im.comp continuous_wdisk_snd) (fun y hy => ?_) x
    change (wdisk y.1.2).im = 0
    rw [snd_eq_zero_of_not_mem hy, wdisk_zero, Complex.zero_im]

lemma G_of_mem_O_nonpos {q : E 0} (hq : q ∈ O) (hG : G q.1 ≤ 0) : q.2 = 0 := by
  obtain ⟨-, hL⟩ := (mem_O_iff q).1 hq
  rw [← hL, L_apply, fam_of_nonpos hG]
  rfl

lemma continuousAt_coef_comp {q₀ : E 0} (hq₀ : q₀ ∈ O) (f : Z2 0 → c0) (hf : Continuous f)
    (hf0 : f 0 = 0) : ContinuousAt (fun q : E 0 => coef (G q.1) (f q.2)) q₀ := by
  by_cases hG : 0 < G q₀.1
  · have h := continuousOn_coef.continuousAt (x := (G q₀.1, f q₀.2))
      (prod_mem_nhds (Ioi_mem_nhds hG) univ_mem)
    exact ContinuousAt.comp (f := fun q : E 0 => (G q.1, f q.2)) h
      (((contDiff_G.continuous.comp continuous_fst).prodMk (hf.comp continuous_snd)).continuousAt)
  · have h2 := G_of_mem_O_nonpos hq₀ (not_lt.1 hG)
    rw [ContinuousAt, coef_of_nonpos (not_lt.1 hG)]
    have hft : Tendsto (fun q : E 0 => f q.2) (𝓝 q₀) (𝓝 0) := by
      have := (hf.comp continuous_snd).tendsto q₀
      rwa [Function.comp_apply, h2, hf0] at this
    refine squeeze_zero_norm (fun q => ?_) (by simpa using (hft.norm).const_mul 2)
    rw [Real.norm_eq_abs]
    exact abs_coef_le _ _

lemma continuousOn_ψinv : ContinuousOn ψinv O := by
  refine ContinuousOn.prodMk ?_ ?_
  · exact continuousOn_tOf.comp continuous_fst.continuousOn fun q hq => ((mem_O_iff q).1 hq).1
  · refine continuous_wback.comp_continuousOn ?_
    have hmk : Continuous fun ab : ℝ × ℝ => (⟨ab.1, ab.2⟩ : ℂ) := by
      have e : (fun ab : ℝ × ℝ => (⟨ab.1, ab.2⟩ : ℂ)) =
          fun ab => ((ab.1 : ℝ) : ℂ) + ((ab.2 : ℝ) : ℂ) * Complex.I := by
        funext ab
        apply Complex.ext <;> simp
      rw [e]
      fun_prop
    refine hmk.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · exact fun q hq => (continuousAt_coef_comp hq Prod.fst continuous_fst rfl).continuousWithinAt
    · exact fun q hq => (continuousAt_coef_comp hq Prod.snd continuous_snd rfl).continuousWithinAt

/-- **The chart of `X`**: the homeomorphism `X → O` onto the retract of `Rt`. -/
def chart : MChart XR where
  model := ⟨E, quadrant 2 Z2 0, O, Rt.isScRetract⟩
  toPartialEquiv :=
    { toFun := fun x => ψfun x.1
      invFun := chartInv
      source := univ
      target := O
      map_source' := fun x _ => ψfun_mem_O x.2
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun x _ => by
        rw [chartInv_of_mem (ψfun_mem_O x.2)]
        exact Subtype.ext (ψinv_ψfun x.2)
      right_inv' := fun q hq => by
        rw [chartInv_of_mem hq]
        exact ψfun_ψinv hq }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := continuous_ψfun.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (O.domRestrict chartInv)
    have e : O.domRestrict chartInv = fun q : O => (⟨ψinv q, ψinv_mem q.2⟩ : XR) := by
      funext q
      exact chartInv_of_mem q.2
    rw [e]
    exact (continuousOn_iff_continuous_domRestrict.1 continuousOn_ψinv).subtype_mk _

lemma chart_apply (x : XR) : chart x = ψfun x.1 := rfl

/-- **The M-polyfold `X` of Remark 9.5.20**, with the one chart `chart`. -/
def P : MPolyfold XR where
  atlas :=
    { charts := {chart}
      compatible := fun φ hφ ψ hψ => by
        rw [mem_singleton_iff.1 hφ, mem_singleton_iff.1 hψ]; exact MChart.compatible_self _
      cover := fun _ => ⟨chart, mem_singleton _, mem_univ _⟩ }

lemma isChart_chart : P.IsChart chart := P.isChart_of_mem (mem_singleton _)

/-! ### The degeneracy index: `∂X = {(−1,0), (1,0)}` -/

lemma chartDegIndex_eq (x : XR) :
    MPolyfold.chartDegIndex chart x = (Finset.univ.filter fun i => arcPt x.1.1 i = 0).card := by
  rw [MPolyfold.chartDegIndex, chart_apply]
  change degIndex E (quadrant 2 Z2 0) (ψfun x.1) = _
  rw [degIndex_quadrant (Rt.retract_subset (ψfun_mem_O x.2)).2]
  rfl

lemma arcPt_pos {t : ℝ} (ht : t ∈ Ioo (-1) 1) (i : Fin 2) : 0 < arcPt t i := by
  have := Real.pi_pos
  have h1 : 0 < θ t := by unfold θ; nlinarith [ht.1]
  have h2 : θ t < π / 2 := by unfold θ; nlinarith [ht.2]
  have hc : 0 < Real.cos (θ t) := Real.cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
  have hs : 0 < Real.sin (θ t) := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
  fin_cases i <;> simp [arcPt] <;> linarith

lemma arcPt_neg_one : arcPt (-1) = ![2, 0] := by
  funext i
  fin_cases i <;> simp [arcPt, θ]

lemma arcPt_one : arcPt 1 = ![0, 2] := by
  funext i
  fin_cases i
  · simp only [arcPt, θ]
    rw [show π * (1 + 1) / 4 = π / 2 by ring, Real.cos_pi_div_two]
    simp
  · simp only [arcPt, θ]
    rw [show π * (1 + 1) / 4 = π / 2 by ring, Real.sin_pi_div_two]
    simp

lemma chartDegIndex_of_mem_Ioo {x : XR} (hx : x.1.1 ∈ Ioo (-1) 1) :
    MPolyfold.chartDegIndex chart x = 0 := by
  rw [chartDegIndex_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ => (arcPt_pos hx i).ne'

lemma chartDegIndex_of_not_mem_Ioo {x : XR} (hx : x.1.1 ∉ Ioo (-1) 1) :
    MPolyfold.chartDegIndex chart x = 1 := by
  rw [chartDegIndex_eq]
  rcases mem_Xs_iff.1 x.2 with h | h | h
  · rw [h, arcPt_neg_one, Finset.card_eq_one]
    exact ⟨1, by ext i; fin_cases i <;> simp⟩
  · rw [h, arcPt_one, Finset.card_eq_one]
    exact ⟨0, by ext i; fin_cases i <;> simp⟩
  · exact absurd h.1 hx

/-- A tangent vector outside the minimal subspace gives `dim(T/T^R) ≥ 1`. -/
lemma one_le_quotDim {n : ℕ} {W F : ScBanach} (T : ScIso F ((ScBanach.const (Fin n → ℝ)).prod W))
    (A : Submodule ℝ (F 0)) (e : F 0) {v : F 0} (hv : v ∈ A)
    (hvn : v ∉ minimalSubspaceWith T e) : 1 ≤ quotDim A (A ⊓ minimalSubspaceWith T e) := by
  rw [quotDim, Nat.one_le_iff_ne_zero, Ne, Module.finrank_eq_zero_iff_of_free]
  intro h
  have := h.elim (Submodule.Quotient.mk ⟨v, hv⟩) 0
  rw [Submodule.Quotient.mk_eq_zero] at this
  exact hvn (Submodule.mem_comap.1 this).2

/-- The end points of the quarter circle: one coordinate `0`, the other `2`. -/
structure IsEnd (p : V2) (i₀ : Fin 2) : Prop where
  mem : p ∈ arc
  zero : p i₀ = 0

lemma IsEnd.sq_add {p : V2} {i₀ : Fin 2} (h : IsEnd p i₀) : p 0 ^ 2 + p 1 ^ 2 = 4 := by
  have h2 := h.mem.2
  rw [len] at h2
  have := Real.sq_sqrt (show 0 ≤ p 0 ^ 2 + p 1 ^ 2 by positivity)
  rw [h2] at this
  linarith

lemma len_add_single {p : V2} {i₀ : Fin 2} (h : IsEnd p i₀) (s : ℝ) :
    len (p + s • Pi.single i₀ 1) = √(4 + s ^ 2) := by
  rw [len]
  congr 1
  have hs := h.sq_add
  have hz := h.zero
  fin_cases i₀
  · simp only [Fin.zero_eta, Fin.isValue] at hz
    simp [hz] at hs ⊢
    linarith
  · simp only [Fin.mk_one, Fin.isValue] at hz
    simp [hz] at hs ⊢
    linarith

/-- Along the inward normal `e_{i₀}`, the `i₀`-th coordinate of `ρ` is `2s/√(4+s²)`. -/
lemma ρ_add_single {p : V2} {i₀ : Fin 2} (h : IsEnd p i₀) (s : ℝ) :
    ρ (p + s • Pi.single i₀ 1) i₀ = 2 / √(4 + s ^ 2) * s := by
  rw [ρ_apply, len_add_single h]
  simp [h.zero]

lemma hasDerivAt_end : HasDerivAt (fun s : ℝ => 2 / √(4 + s ^ 2) * s) 1 0 := by
  have hg : DifferentiableAt ℝ (fun s : ℝ => 2 / √(4 + s ^ 2)) 0 := by
    refine DifferentiableAt.div (differentiableAt_const _) ?_ (by positivity)
    exact (DifferentiableAt.sqrt (by fun_prop) (by positivity))
  have h := hg.hasDerivAt.mul (hasDerivAt_id (0 : ℝ))
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
  have e : deriv (fun s : ℝ => 2 / √(4 + s ^ 2)) 0 * id 0 + 2 / √(4 + 0 ^ 2) * 1 = 1 := by
    simp [h4]
  rw [e] at h
  exact h

/-- **The inward normal is tangent at an end**: for the level-`1` point `z = (p, 0)` over an end `p`
and `w = (e_{i₀}, 0)`, the `i₀`-th coordinate of `Dr(z) w` is `1`. -/
lemma scDeriv_end {p : V2} {i₀ : Fin 2} (h : IsEnd p i₀) :
    (scDeriv Rt.U Rt ((p, 0) : E 1) (E.toBase 1 ((Pi.single i₀ 1, 0) : E 1))).1 i₀ = 1 := by
  set z : E 1 := (p, 0)
  set w : E 1 := (Pi.single i₀ 1, 0)
  have hb : ∀ q : V2, E.toBase 1 ((q, 0) : E 1) = ((q, 0) : E 0) := fun q => by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase, map_zero]
  have hp0 : p ≠ 0 := ne_zero_of_mem_arc h.mem
  -- the curve `γ s = z + s w`
  set γ : ℝ → E 1 := fun s => z + s • w
  have hγ : ∀ s, γ s = ((p + s • Pi.single i₀ 1, 0) : E 1) := fun s => by
    simp only [γ, z, w, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
  have hγd : HasDerivWithinAt γ w (Ici 0) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z).hasDerivWithinAt (s := Ici 0)
    simpa [γ] using this
  have hmaps : MapsTo γ (Ici 0) (E.lvlSet Rt.U 1) := by
    intro s hs
    rw [ScBanach.mem_lvlSet, hγ, hb]
    refine ⟨fun h0 => ?_, fun i => ?_⟩
    · have hl := len_add_single h s
      change p + s • Pi.single i₀ 1 = 0 at h0
      have h00 : len (0 : V2) = 0 := by simp [len]
      rw [h0, h00] at hl
      have : (0 : ℝ) < √(4 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
      linarith
    · have hs' : (0 : ℝ) ≤ s := hs
      have : 0 ≤ s * (Pi.single i₀ (1 : ℝ) : V2) i := by
        rw [Pi.single_apply]; split_ifs <;> simp [hs']
      change 0 ≤ p i + s • (Pi.single i₀ (1 : ℝ) : V2) i
      rw [smul_eq_mul]; linarith [h.mem.1 i]
  have hz1 : z ∈ E.lvlSet Rt.U 1 := by
    have := hmaps (self_mem_Ici : (0 : ℝ) ∈ Ici 0)
    simpa [γ] using this
  have hD := Rt.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hz1
  have hcomp := hD.comp_hasDerivWithinAt_of_eq 0 hγd hmaps (by simp [γ])
  -- apply the coordinate functional `q ↦ q.1 i₀`
  set ℓ : E 0 →L[ℝ] ℝ := (ContinuousLinearMap.proj i₀).comp (ContinuousLinearMap.fst ℝ V2 (Z2 0))
  have hℓ := ℓ.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hcomp
  have hfun : (ℓ ∘ ((⇑Rt ∘ E.toBase 1) ∘ γ)) = fun s : ℝ => 2 / √(4 + s ^ 2) * s := by
    funext s
    simp only [Function.comp_apply, hγ, hb]
    rw [Rt_apply]
    exact ρ_add_single h s
  rw [hfun] at hℓ
  have huniq := (uniqueDiffOn_Ici (0 : ℝ) 0 self_mem_Ici).eq_deriv _ hℓ
    hasDerivAt_end.hasDerivWithinAt
  simpa [ℓ] using huniq

lemma isEnd_of_not_mem_Ioo {x : XR} (hx : x.1.1 ∉ Ioo (-1) 1) :
    ∃ i₀, IsEnd (arcPt x.1.1) i₀ := by
  rcases mem_Xs_iff.1 x.2 with h | h | h
  · refine ⟨1, arcPt_mem_arc (fst_mem_Icc_of_mem x.2), ?_⟩
    rw [h, arcPt_neg_one]; rfl
  · refine ⟨0, arcPt_mem_arc (fst_mem_Icc_of_mem x.2), ?_⟩
    rw [h, arcPt_one]; rfl
  · exact absurd h.1 hx

lemma ψfun_of_not_mem_Ioo {x : XR} (hx : x.1.1 ∉ Ioo (-1) 1) :
    ψfun x.1 = ((arcPt x.1.1, 0) : E 0) := by
  rw [ψfun, snd_eq_zero_of_not_mem hx, wdisk_zero, Complex.zero_re, Complex.zero_im, zero_smul]
  rfl

/-- **`d_X = 1` at `(±1, 0)`**: Theorem 2.4.12 with the inward normal in `T_xO`. -/
lemma one_le_degIndex {x : XR} (hx : x.1.1 ∉ Ioo (-1) 1) : 1 ≤ P.degIndex x := by
  obtain ⟨i₀, hend⟩ := isEnd_of_not_mem_Ioo hx
  set p := arcPt x.1.1
  have hz : E.toBase 1 ((p, 0) : E 1) = chart x := by
    rw [chart_apply, ψfun_of_not_mem_Ioo hx, ScBanach.prod_toBase, ScBanach.const_toBase,
      map_zero]
  have key : quotDim (LinearMap.range (scDeriv Rt.U Rt ((p, 0) : E 1) : E 0 →ₗ[ℝ] E 0))
      (reducedTangentSpaceWith Rt (ScIso.refl E) ((p, 0) : E 1)) ≤ P.degIndex x :=
    theorem_2_4_12 (P := P) isChart_chart Rt rfl (ScIso.refl E) (by ext; rfl) (mem_univ x) hz
  refine le_trans ?_ key
  refine one_le_quotDim (ScIso.refl E) _ _ (LinearMap.mem_range_self
    (scDeriv Rt.U Rt ((p, 0) : E 1) : E 0 →ₗ[ℝ] E 0) (E.toBase 1 ((Pi.single i₀ 1, 0) : E 1))) ?_
  rw [mem_minimalSubspaceWith]
  intro hmin
  have h1 := hmin i₀ (by
    change (E.toBase 1 ((p, 0) : E 1)).1 i₀ = 0
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
    exact hend.zero)
  have h2 := scDeriv_end hend
  change (scDeriv Rt.U Rt ((p, 0) : E 1) (E.toBase 1 ((Pi.single i₀ 1, 0) : E 1))).1 i₀ = 0 at h1
  rw [h1] at h2
  exact zero_ne_one h2

/-- **The degeneracy index of `X`**: `0` on `(−1,1) × B`, `1` at `(±1, 0)`. -/
theorem degIndex_eq (x : XR) : P.degIndex x = if x.1.1 ∈ Ioo (-1) 1 then 0 else 1 := by
  split_ifs with hx
  · exact Nat.le_zero.1 ((P.degIndex_le isChart_chart (mem_univ x)).trans
      (chartDegIndex_of_mem_Ioo hx).le)
  · exact le_antisymm ((P.degIndex_le isChart_chart (mem_univ x)).trans
      (chartDegIndex_of_not_mem_Ioo hx).le) (one_le_degIndex hx)

/-- **`∂X = {(−1, 0), (1, 0)}`** (Remark 9.5.20, p. 452). -/
theorem boundary_eq : P.boundary = {x | x.1 = (-1, 0) ∨ x.1 = (1, 0)} := by
  ext x
  change 1 ≤ P.degIndex x ↔ _
  rw [degIndex_eq]
  rcases mem_Xs_iff.1 x.2 with h | h | h
  · simp [h]
  · simp [h]
  · simp only [if_pos h.1]
    change 1 ≤ 0 ↔ x.1 = (-1, 0) ∨ x.1 = (1, 0)
    constructor
    · intro h'; omega
    · rintro (h' | h') <;> rw [h'] at h <;> simp at h

end K3

end Polyfold
