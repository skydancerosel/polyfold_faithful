import Polyfold.Chapter5.GapP1_LpWeightedProduct

/-!
# Bonic–Frampton: the differentiability of `‖·‖ᵖ` on `Lᵖ`

2021 Theorem 5.5.5, p. 230 (preprint Theorem 5.32), cited from Bonic–Frampton: on `Lᵖ`, `p ≥ 1`,
(1) `‖·‖ᵖ` is `C^∞` for `p` an even integer, (2) `C^{p-1}` for `p` an odd integer, (3) `C^{[p]}` for
`p` not an integer.

## The proof

Write `|t|ᵖ = u_p(t) + u_p(−t)`, `u_r(t) = (max t 0)^r`.  Its `j`-th derivative is
`gⱼ = aⱼ u_{p−j}(t) + bⱼ u_{p−j}(−t)` (`gK`), a kernel homogeneous of degree `r = p − j`.  For
`j < p` the form `Tⱼ(f)(h₁, …, hⱼ) = ∫ gⱼ(f) ∏ hᵢ` is continuous `j`-linear on `Lᵖ`, with
`gⱼ(f) ∈ L^{p/(p−j)}` (`wMul`, generalized Hölder).  Two one-variable estimates do the analysis:

* `|gⱼ(s + t) − gⱼ(s)| ≤ ε|s|^r + C_ε|t|^r` for `r > 0` (`kern_sub_le`, from the continuity of
  `z ↦ z^r` at `1` and homogeneity); in `L^{p/r}` it gives
  `‖gⱼ(f + h) − gⱼ(f)‖ ≤ ε‖f‖^r + C_ε‖h‖^r`,
  hence the continuity of `Tⱼ`;
* `|gⱼ(s + t) − gⱼ(s) − gⱼ₊₁(s)t| ≤ |t|(ε|s|^{r−1} + C_ε|t|^{r−1})` for `r > 1` (mean value
  theorem), which with Hölder gives `Tⱼ(f + h) − Tⱼ(f) − Tⱼ₊₁(f)(h, ·) = o(‖h‖)`.

So `(Tⱼ)_{j ≤ n}` is a Taylor series of `‖·‖ᵖ` up to every `n < p`
(`hasFTaylorSeriesUpTo_normRpow`),
and `‖·‖ᵖ` is `C^n` for every integer `n < p` (`contDiff_normRpow_of_lt`).  For `p` odd that is
`n = p − 1`, for `p` not an integer `n = [p]`.  The even case is `theorem_5_5_5_even`.
-/

open MeasureTheory Finset Function Filter Topology Asymptotics
open scoped ENNReal NNReal

noncomputable section

namespace Polyfold

namespace BonicFrampton

/-! ### One-variable kernels -/

/-- `u_r(t) = (max t 0)^r`. -/
def posPow (r t : ℝ) : ℝ := (max t 0) ^ r

lemma posPow_nonneg (r t : ℝ) : 0 ≤ posPow r t := Real.rpow_nonneg (le_max_right _ _) _

lemma max_zero_le_abs (t : ℝ) : max t 0 ≤ |t| := max_le (le_abs_self t) (abs_nonneg t)

lemma posPow_le {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : posPow r t ≤ |t| ^ r :=
  Real.rpow_le_rpow (le_max_right _ _) (max_zero_le_abs t) hr

lemma continuous_posPow {r : ℝ} (hr : 0 < r) : Continuous (posPow r) :=
  (continuous_id.max continuous_const).rpow_const fun _ => Or.inr hr.le

lemma posPow_add_posPow_neg {r : ℝ} (hr : 0 < r) (t : ℝ) :
    posPow r t + posPow r (-t) = |t| ^ r := by
  rcases le_total 0 t with ht | ht
  · simp [posPow, max_eq_left ht, max_eq_right (neg_nonpos.2 ht), abs_of_nonneg ht,
      Real.zero_rpow hr.ne']
  · simp [posPow, max_eq_right ht, max_eq_left (neg_nonneg.2 ht), abs_of_nonpos ht,
      Real.zero_rpow hr.ne']

lemma hasDerivAt_posPow {r : ℝ} (hr : 1 < r) (t : ℝ) :
    HasDerivAt (posPow r) (r * posPow (r - 1) t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h0 : posPow (r - 1) t = 0 := by
      simp [posPow, max_eq_right ht.le, Real.zero_rpow (by linarith : r - 1 ≠ 0)]
    rw [h0, mul_zero]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with y hy
    have hy' : y < 0 := hy
    simp [posPow, max_eq_right hy'.le, Real.zero_rpow (by linarith : r ≠ 0)]
  · have h0 : posPow (r - 1) 0 = 0 := by
      simp [posPow, Real.zero_rpow (by linarith : r - 1 ≠ 0)]
    have hpos0 : posPow r 0 = 0 := by simp [posPow, Real.zero_rpow (by linarith : r ≠ 0)]
    rw [h0, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, hpos0, sub_zero, smul_zero]
    have htend : Tendsto (fun h : ℝ => |h| ^ (r - 1)) (𝓝 0) (𝓝 0) := by
      have := (continuous_abs.rpow_const fun _ => Or.inr (by linarith : (0 : ℝ) ≤ r - 1)).tendsto 0
      simpa [Real.zero_rpow (by linarith : r - 1 ≠ 0)] using this
    have hO : (posPow r) =O[𝓝 0] fun h : ℝ => |h| ^ (r - 1) * h := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (posPow_nonneg r h), abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
      calc posPow r h ≤ |h| ^ r := posPow_le (by linarith) h
        _ = |h| ^ (r - 1) * |h| := by
          conv_lhs => rw [show r = (r - 1) + 1 by ring]
          rw [Real.rpow_add' (abs_nonneg h) (by linarith), Real.rpow_one]
    have hlo : (fun h : ℝ => |h| ^ (r - 1) * h) =o[𝓝 0] fun h => h := by
      simpa using ((isLittleO_one_iff ℝ).2 htend).mul_isBigO (isBigO_refl (fun h : ℝ => h) _)
    exact hO.trans_isLittleO hlo
  · have hd := Real.hasDerivAt_rpow_const (x := t) (p := r) (Or.inl ht.ne')
    have : posPow (r - 1) t = t ^ (r - 1) := by simp [posPow, max_eq_left ht.le]
    rw [this]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with y hy
    have hy' : 0 < y := hy
    simp [posPow, max_eq_left hy'.le]

/-- **The homogeneous continuity estimate**: for `r > 0` and `ε > 0` there is `C` with
`|x^r − y^r| ≤ ε y^r + C d^r` whenever `x, y ≥ 0`, `|x − y| ≤ d`. -/
lemma rpow_sub_rpow_le {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ x y d : ℝ, 0 ≤ x → 0 ≤ y → |x - y| ≤ d →
      |x ^ r - y ^ r| ≤ ε * y ^ r + C * d ^ r := by
  have hcont : ContinuousAt (fun z : ℝ => z ^ r) 1 :=
    Real.continuousAt_rpow_const 1 r (Or.inl one_ne_zero)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont ε hε
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  refine ⟨(1 / δ' + 1) ^ r, by positivity, fun x y d hx hy hxy => ?_⟩
  have hd : 0 ≤ d := (abs_nonneg _).trans hxy
  have hRHS : 0 ≤ ε * y ^ r + (1 / δ' + 1) ^ r * d ^ r := by positivity
  by_cases hcase : d ≤ δ' * y
  · rcases hy.eq_or_lt with hy0 | hy0
    · subst hy0
      have : x = 0 := by
        have : |x - 0| ≤ 0 := hxy.trans (by simpa using hcase)
        simpa using this
      subst this
      simpa using hRHS
    · have hz : dist (x / y) 1 < δ := by
        rw [Real.dist_eq, div_sub_one hy0.ne', abs_div, abs_of_pos hy0, div_lt_iff₀ hy0]
        calc |x - y| ≤ d := hxy
          _ ≤ δ' * y := hcase
          _ < δ * y := by rw [hδ']; nlinarith
      have h1 := hδε hz
      rw [Real.dist_eq, Real.one_rpow] at h1
      have hx' : x ^ r = (x / y) ^ r * y ^ r := by
        rw [← Real.mul_rpow (div_nonneg hx hy) hy, div_mul_cancel₀ x hy0.ne']
      have hyr : 0 < y ^ r := Real.rpow_pos_of_pos hy0 r
      calc |x ^ r - y ^ r| = |(x / y) ^ r - 1| * y ^ r := by
            rw [hx', ← sub_one_mul, abs_mul, abs_of_pos hyr]
        _ ≤ ε * y ^ r := by gcongr
        _ ≤ ε * y ^ r + (1 / δ' + 1) ^ r * d ^ r := by
            have : 0 ≤ (1 / δ' + 1) ^ r * d ^ r := by positivity
            linarith
  · rw [not_le] at hcase
    have hyM : y ≤ (1 / δ' + 1) * d := by
      have : y < d / δ' := by rw [lt_div_iff₀ hδ'0]; linarith
      rw [one_div, add_mul, inv_mul_eq_div, one_mul]
      linarith
    have hxM : x ≤ (1 / δ' + 1) * d := by
      have hxy' : x ≤ y + d := by linarith [le_abs_self (x - y)]
      have : y < d / δ' := by rw [lt_div_iff₀ hδ'0]; linarith
      rw [one_div, add_mul, inv_mul_eq_div, one_mul]
      linarith
    have hM : ((1 / δ' + 1) * d) ^ r = (1 / δ' + 1) ^ r * d ^ r :=
      Real.mul_rpow (by positivity) hd
    have hxr : x ^ r ≤ (1 / δ' + 1) ^ r * d ^ r := hM ▸ Real.rpow_le_rpow hx hxM hr.le
    have hyr : y ^ r ≤ (1 / δ' + 1) ^ r * d ^ r := hM ▸ Real.rpow_le_rpow hy hyM hr.le
    have hx0 : 0 ≤ x ^ r := Real.rpow_nonneg hx r
    have hy0 : 0 ≤ y ^ r := Real.rpow_nonneg hy r
    have hεy : 0 ≤ ε * y ^ r := by positivity
    rw [abs_le]
    constructor <;> linarith

lemma posPow_sub_le {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ s t : ℝ, |posPow r (s + t) - posPow r s| ≤ ε * |s| ^ r + C * |t| ^ r := by
  obtain ⟨C, hC, hCb⟩ := rpow_sub_rpow_le hr hε
  refine ⟨C, hC, fun s t => ?_⟩
  have h1 : |max (s + t) 0 - max s 0| ≤ |t| := by
    have := abs_max_sub_max_le_abs (s + t) s 0
    simpa using this
  refine (hCb _ _ _ (le_max_right _ _) (le_max_right _ _) h1).trans ?_
  have : (max s 0) ^ r ≤ |s| ^ r := Real.rpow_le_rpow (le_max_right _ _) (max_zero_le_abs s) hr.le
  have := mul_le_mul_of_nonneg_left this hε.le
  linarith

/-- The kernel `a u_r(t) + b u_r(−t)`. -/
def kern (a b r t : ℝ) : ℝ := a * posPow r t + b * posPow r (-t)

lemma abs_kern_le {a b r : ℝ} (hr : 0 ≤ r) (t : ℝ) : |kern a b r t| ≤ (|a| + |b|) * |t| ^ r := by
  have h1 := posPow_le hr t
  have h2 := posPow_le hr (-t)
  rw [abs_neg] at h2
  have h3 := posPow_nonneg r t
  have h4 := posPow_nonneg r (-t)
  calc |kern a b r t| ≤ |a * posPow r t| + |b * posPow r (-t)| := abs_add_le _ _
    _ = |a| * posPow r t + |b| * posPow r (-t) := by
        rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg h4]
    _ ≤ |a| * |t| ^ r + |b| * |t| ^ r := by gcongr
    _ = (|a| + |b|) * |t| ^ r := by ring

lemma continuous_kern {a b r : ℝ} (hr : 0 < r) : Continuous (kern a b r) :=
  (continuous_const.mul (continuous_posPow hr)).add
    (continuous_const.mul ((continuous_posPow hr).comp continuous_neg))

lemma hasDerivAt_kern {a b r : ℝ} (hr : 1 < r) (t : ℝ) :
    HasDerivAt (kern a b r) (kern (r * a) (-(r * b)) (r - 1) t) t := by
  have h1 := (hasDerivAt_posPow hr t).const_mul a
  have h2 := ((hasDerivAt_posPow hr (-t)).comp t (hasDerivAt_neg t)).const_mul b
  have := h1.add h2
  refine this.congr_deriv ?_
  simp only [kern]
  ring

lemma kern_sub_le {a b r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ s t : ℝ, |kern a b r (s + t) - kern a b r s| ≤ ε * |s| ^ r + C * |t| ^ r := by
  obtain ⟨C, hC, hCb⟩ := posPow_sub_le hr (ε := ε / (|a| + |b| + 1)) (by positivity)
  refine ⟨(|a| + |b|) * C, by positivity, fun s t => ?_⟩
  have h1 := hCb s t
  have h2 := hCb (-s) (-t)
  rw [abs_neg, abs_neg, show -s + -t = -(s + t) by ring] at h2
  have hab : (|a| + |b|) * (ε / (|a| + |b| + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hs : 0 ≤ |s| ^ r := by positivity
  calc |kern a b r (s + t) - kern a b r s|
      = |a * (posPow r (s + t) - posPow r s) + b * (posPow r (-(s + t)) - posPow r (-s))| := by
        simp only [kern]; ring_nf
    _ ≤ |a| * |posPow r (s + t) - posPow r s| + |b| * |posPow r (-(s + t)) - posPow r (-s)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ |a| * (ε / (|a| + |b| + 1) * |s| ^ r + C * |t| ^ r) +
          |b| * (ε / (|a| + |b| + 1) * |s| ^ r + C * |t| ^ r) := by gcongr
    _ = (|a| + |b|) * (ε / (|a| + |b| + 1)) * |s| ^ r + (|a| + |b|) * C * |t| ^ r := by ring
    _ ≤ ε * |s| ^ r + (|a| + |b|) * C * |t| ^ r := by gcongr

lemma abs_le_abs_of_mem_uIcc {τ t : ℝ} (h : τ ∈ Set.uIcc 0 t) : |τ| ≤ |t| := by
  rcases Set.mem_uIcc.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- **First-order Taylor estimate** from a homogeneous continuity estimate of the derivative. -/
lemma taylor1_le {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) {ρ ε C : ℝ} (hρ : 0 ≤ ρ)
    (hC : 0 ≤ C) (hg' : ∀ s t, |g' (s + t) - g' s| ≤ ε * |s| ^ ρ + C * |t| ^ ρ) (s t : ℝ) :
    |g (s + t) - g s - g' s * t| ≤ |t| * (ε * |s| ^ ρ + C * |t| ^ ρ) := by
  set φ : ℝ → ℝ := fun τ => g (s + τ) - g' s * τ
  have hφ : ∀ τ ∈ Set.uIcc 0 t, HasDerivWithinAt φ (g' (s + τ) - g' s) (Set.uIcc 0 t) τ := by
    intro τ _
    have h1 : HasDerivAt (fun x => g (s + x)) (g' (s + τ)) τ := by
      have := (hg (s + τ)).comp τ ((hasDerivAt_id τ).const_add s)
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun x => g' s * x) (g' s) τ := by
      simpa using (hasDerivAt_id τ).const_mul (g' s)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ τ ∈ Set.uIcc 0 t, ‖g' (s + τ) - g' s‖ ≤ ε * |s| ^ ρ + C * |t| ^ ρ := by
    intro τ hτ
    rw [Real.norm_eq_abs]
    refine (hg' s τ).trans ?_
    have := Real.rpow_le_rpow (abs_nonneg τ) (abs_le_abs_of_mem_uIcc hτ) hρ
    have := mul_le_mul_of_nonneg_left this hC
    linarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbound (convex_uIcc 0 t)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [φ, add_zero, mul_zero, sub_zero, Real.norm_eq_abs] at this
  calc |g (s + t) - g s - g' s * t| = |g (s + t) - g' s * t - g s| := by ring_nf
    _ ≤ _ := this
    _ = _ := mul_comm _ _

/-! ### The derivatives of `|t|ᵖ` -/

/-- The coefficients of `gⱼ`: `a₀ = b₀ = 1`, `aⱼ₊₁ = (p − j)aⱼ`, `bⱼ₊₁ = −(p − j)bⱼ`. -/
def coef (p : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | j + 1 => ((p - j) * (coef p j).1, -((p - j) * (coef p j).2))

/-- `gⱼ(t) = aⱼ u_{p−j}(t) + bⱼ u_{p−j}(−t)`, the `j`-th derivative of `|t|ᵖ`. -/
def gK (p : ℝ) (j : ℕ) : ℝ → ℝ := kern (coef p j).1 (coef p j).2 (p - j)

lemma gK_zero {p : ℝ} (hp : 0 < p) (t : ℝ) : gK p 0 t = |t| ^ p := by
  simp [gK, coef, kern, posPow_add_posPow_neg hp]

lemma hasDerivAt_gK {p : ℝ} {j : ℕ} (hj : (j : ℝ) + 1 < p) (t : ℝ) :
    HasDerivAt (gK p j) (gK p (j + 1) t) t := by
  have := hasDerivAt_kern (a := (coef p j).1) (b := (coef p j).2) (r := p - j) (by linarith) t
  have e : p - ((j + 1 : ℕ) : ℝ) = (p - j) - 1 := by push_cast; ring
  simp only [gK, coef, e]
  exact this

lemma continuous_gK {p : ℝ} {j : ℕ} (hj : (j : ℝ) < p) : Continuous (gK p j) :=
  continuous_kern (sub_pos.2 hj)

lemma gK_sub_le {p : ℝ} {j : ℕ} (hj : (j : ℝ) < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ s t : ℝ, |gK p j (s + t) - gK p j s| ≤ ε * |s| ^ (p - j) + C * |t| ^ (p - j) :=
  kern_sub_le (sub_pos.2 hj) hε

lemma gK_taylor_le {p : ℝ} {j : ℕ} (hj : (j : ℝ) + 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ s t : ℝ, |gK p j (s + t) - gK p j s - gK p (j + 1) s * t| ≤
      |t| * (ε * |s| ^ (p - ((j + 1 : ℕ) : ℝ)) + C * |t| ^ (p - ((j + 1 : ℕ) : ℝ))) := by
  have hj1 : ((j + 1 : ℕ) : ℝ) < p := by push_cast; linarith
  obtain ⟨C, hC, hCb⟩ := gK_sub_le hj1 hε
  exact ⟨C, hC, fun s t => taylor1_le (hasDerivAt_gK hj) (sub_pos.2 hj1).le hC hCb s t⟩

/-! ### The exponents -/

section Exponents

variable {p : ℝ}

/-- The exponent `p/(p − j)` of `gⱼ(f)`. -/
def qE (p : ℝ) (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (p / (p - j))

lemma qE_inv {j : ℕ} (hp : 0 < p) (hj : (j : ℝ) < p) :
    (qE p j)⁻¹ = ENNReal.ofReal ((p - j) / p) := by
  rw [qE, ← ENNReal.ofReal_inv_of_pos (div_pos hp (sub_pos.2 hj)), inv_div]

lemma ofReal_inv' (hp : 0 < p) : (ENNReal.ofReal p)⁻¹ = ENNReal.ofReal p⁻¹ :=
  (ENNReal.ofReal_inv_of_pos hp).symm

lemma qE_hq {j : ℕ} (hp : 0 < p) (hj : (j : ℝ) < p) :
    (qE p j)⁻¹ + (j : ℝ≥0∞) * (ENNReal.ofReal p)⁻¹ = 1 := by
  rw [qE_inv hp hj, ofReal_inv' hp, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg j),
    ← ENNReal.ofReal_add (div_nonneg (sub_pos.2 hj).le hp.le) (by positivity)]
  rw [show (p - j) / p + j * p⁻¹ = 1 by field_simp; ring, ENNReal.ofReal_one]

lemma holderTriple_qE {j : ℕ} (hp : 0 < p) (hj : (j : ℝ) + 1 < p) :
    ENNReal.HolderTriple (qE p (j + 1)) (ENNReal.ofReal p) (qE p j) := by
  have hj0 : (j : ℝ) < p := by linarith
  have hj1 : ((j + 1 : ℕ) : ℝ) < p := by push_cast; linarith
  refine ⟨?_⟩
  rw [qE_inv hp hj1, qE_inv hp hj0, ofReal_inv' hp,
    ← ENNReal.ofReal_add (div_nonneg (sub_pos.2 hj1).le hp.le) (by positivity)]
  congr 1
  push_cast
  field_simp
  ring

lemma one_le_qE {j : ℕ} (hj : (j : ℝ) < p) : 1 ≤ qE p j := by
  rw [qE, ENNReal.one_le_ofReal, le_div_iff₀ (sub_pos.2 hj)]
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

end Exponents

/-! ### `Lᵖ` estimates -/

section LpEstimates

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

lemma one_le_p : 1 ≤ p := ENNReal.one_le_ofReal.1 hP.out

lemma p_pos : 0 < p := zero_lt_one.trans_le one_le_p

omit hP in
lemma memLp_abs_rpow (f : Lp ℝ (ENNReal.ofReal p) μ) {r : ℝ} (hr : 0 < r) :
    MemLp (fun x => |(f : α → ℝ) x| ^ r) (ENNReal.ofReal (p / r)) μ := by
  have := (Lp.memLp f).norm_rpow_div (ENNReal.ofReal r)
  rw [ENNReal.toReal_ofReal hr.le, ← ENNReal.ofReal_div_of_pos hr] at this
  simpa [Real.norm_eq_abs] using this

lemma eLpNorm_abs_rpow (f : Lp ℝ (ENNReal.ofReal p) μ) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => |(f : α → ℝ) x| ^ r) (ENNReal.ofReal (p / r)) μ =
      ENNReal.ofReal (‖f‖ ^ r) := by
  have := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / r)) (f : α → ℝ) hr
  simp only [Real.norm_eq_abs] at this
  rw [this, ← ENNReal.ofReal_mul (div_nonneg p_pos.le hr.le), div_mul_cancel₀ p hr.ne',
    Lp.norm_def, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr.le,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

lemma eLpNorm_combo_le (f h : Lp ℝ (ENNReal.ofReal p) μ) {r : ℝ} (hr : 0 < r) (hrp : r ≤ p)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) :
    eLpNorm (fun x => ε * |(f : α → ℝ) x| ^ r + C * |(h : α → ℝ) x| ^ r)
        (ENNReal.ofReal (p / r)) μ ≤ ENNReal.ofReal (ε * ‖f‖ ^ r + C * ‖h‖ ^ r) := by
  have hq1 : 1 ≤ ENNReal.ofReal (p / r) := by
    rw [ENNReal.one_le_ofReal, le_div_iff₀ hr]; linarith
  have hf := memLp_abs_rpow f hr
  have hh := memLp_abs_rpow h hr
  calc eLpNorm (fun x => ε * |(f : α → ℝ) x| ^ r + C * |(h : α → ℝ) x| ^ r)
        (ENNReal.ofReal (p / r)) μ
      ≤ eLpNorm (ε • fun x => |(f : α → ℝ) x| ^ r) (ENNReal.ofReal (p / r)) μ +
          eLpNorm (C • fun x => |(h : α → ℝ) x| ^ r) (ENNReal.ofReal (p / r)) μ :=
        eLpNorm_add_le (hf.1.const_smul ε) (hh.1.const_smul C) hq1
    _ = ENNReal.ofReal ε * ENNReal.ofReal (‖f‖ ^ r) +
          ENNReal.ofReal C * ENNReal.ofReal (‖h‖ ^ r) := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_abs_rpow f hr, eLpNorm_abs_rpow h hr,
          Real.enorm_eq_ofReal hε, Real.enorm_eq_ofReal hC]
    _ = ENNReal.ofReal (ε * ‖f‖ ^ r + C * ‖h‖ ^ r) := by
        rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

lemma eLpNorm_le_of_ae_bound' {F : α → ℝ} (f h : Lp ℝ (ENNReal.ofReal p) μ) {r : ℝ} (hr : 0 < r)
    (hrp : r ≤ p) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hF : ∀ᵐ x ∂μ, |F x| ≤ ε * |(f : α → ℝ) x| ^ r + C * |(h : α → ℝ) x| ^ r) :
    (eLpNorm F (ENNReal.ofReal (p / r)) μ).toReal ≤ ε * ‖f‖ ^ r + C * ‖h‖ ^ r := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  exact (eLpNorm_mono_ae_real (by simpa [Real.norm_eq_abs] using hF)).trans
    (eLpNorm_combo_le f h hr hrp hε hC)

omit hP in
/-- `gⱼ(f) ∈ L^{p/(p−j)}`. -/
lemma memLp_gK (f : Lp ℝ (ENNReal.ofReal p) μ) {j : ℕ} (hj : (j : ℝ) < p) :
    MemLp (fun x => gK p j ((f : α → ℝ) x)) (qE p j) μ := by
  refine (memLp_abs_rpow f (sub_pos.2 hj)).of_le_mul (c := |(coef p j).1| + |(coef p j).2|)
    ((continuous_gK hj).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact abs_kern_le (sub_pos.2 hj).le _

/-- A uniform `ε`-estimate gives eventual smallness near `0`. -/
lemma eventually_lt_of_bound {E : Type*} [NormedAddCommGroup E] {A r : ℝ} (hr : 0 < r)
    (hA : 0 ≤ A) {B : E → ℝ} (hB : ∀ ε > 0, ∃ C, ∀ h, B h ≤ ε * A + C * ‖h‖ ^ r) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ h in 𝓝 (0 : E), B h < c := by
  obtain ⟨C, hC⟩ := hB (c / (2 * (A + 1))) (by positivity)
  have ht : Tendsto (fun h : E => C * ‖h‖ ^ r) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun h : E => C * ‖h‖ ^ r :=
      continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hr.le)
    have := hc.tendsto (0 : E)
    simpa [Real.zero_rpow hr.ne'] using this
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hc))] with h hh
  have h1 : c / (2 * (A + 1)) * A < c / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith [hC h]

end LpEstimates

/-! ### The Taylor series of `‖·‖ᵖ` -/

section Taylor

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- `Tⱼ(f) = (h₁, …, hⱼ) ↦ ∫ gⱼ(f) ∏ hᵢ`, for `j < p`. -/
def Tj (j : ℕ) (hj : (j : ℝ) < p) (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => Lp ℝ (ENNReal.ofReal p) μ) ℝ :=
  wMul j (qE_hq p_pos hj) (memLp_gK f hj)

/-- The Taylor series: `Tⱼ` for `j < p`, `0` beyond. -/
def taylorNormRpow (f : Lp ℝ (ENNReal.ofReal p) μ) :
    FormalMultilinearSeries ℝ (Lp ℝ (ENNReal.ofReal p) μ) ℝ := fun j =>
  if hj : (j : ℝ) < p then Tj μ j hj f else 0

variable {μ}

lemma taylorNormRpow_of_lt (f : Lp ℝ (ENNReal.ofReal p) μ) {j : ℕ} (hj : (j : ℝ) < p) :
    taylorNormRpow μ f j = Tj μ j hj f :=
  dif_pos hj

lemma continuous_Tj {j : ℕ} (hj : (j : ℝ) < p) : Continuous (Tj μ j hj) := by
  have hr : 0 < p - j := sub_pos.2 hj
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro c hc
  have key : ∀ᶠ h in 𝓝 (0 : Lp ℝ (ENNReal.ofReal p) μ), ‖Tj μ j hj (f + h) - Tj μ j hj f‖ < c := by
    refine eventually_lt_of_bound hr (by positivity : 0 ≤ ‖f‖ ^ (p - j)) (fun ε hε => ?_) hc
    obtain ⟨C, hC, hCb⟩ := gK_sub_le hj hε
    refine ⟨C, fun h => ?_⟩
    refine (norm_wMul_sub_le _ _ _).trans ?_
    refine eLpNorm_le_of_ae_bound' f h hr (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      hε.le hC ?_
    filter_upwards [Lp.coeFn_add f h] with x hx
    simp only [Pi.sub_apply, hx, Pi.add_apply]
    exact hCb _ _
  have ht : Tendsto (fun y => y - f) (𝓝 f) (𝓝 (0 : Lp ℝ (ENNReal.ofReal p) μ)) := by
    exact tendsto_sub_nhds_zero_iff.2 tendsto_id
  filter_upwards [ht.eventually key] with y hy
  rw [dist_eq_norm]
  simpa using hy

lemma hasFDerivAt_Tj {j : ℕ} (hj : (j : ℝ) + 1 < p) (f : Lp ℝ (ENNReal.ofReal p) μ) :
    HasFDerivAt (Tj μ j (by linarith))
      ((Tj μ (j + 1) (by push_cast; linarith) f).curryLeft) f := by
  have hj0 : (j : ℝ) < p := by linarith
  have hj1 : ((j + 1 : ℕ) : ℝ) < p := by push_cast; linarith
  have hr1 : 0 < p - ((j + 1 : ℕ) : ℝ) := sub_pos.2 hj1
  have := holderTriple_qE p_pos hj
  have hP1 : 1 ≤ ENNReal.ofReal p := hP.out
  -- the weight of `Tⱼ₊₁(f)(h, ·)`
  have hwv : ∀ h : Lp ℝ (ENNReal.ofReal p) μ,
      MemLp (fun x => gK p (j + 1) ((f : α → ℝ) x) * (h : α → ℝ) x) (qE p j) μ :=
    fun h => (Lp.memLp h).mul' (memLp_gK f hj1)
  have hcurry : ∀ h, (Tj μ (j + 1) hj1 f).curryLeft h = wMul j (qE_hq p_pos hj0) (hwv h) :=
    fun h => wMul_curryLeft (qE_hq p_pos hj0) (qE_hq p_pos hj1) (memLp_gK f hj1) h (hwv h)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  -- the remainder estimate
  have hrem : ∀ h : Lp ℝ (ENNReal.ofReal p) μ, ∀ ε > 0, ∀ C ≥ 0,
      (∀ s t : ℝ, |gK p j (s + t) - gK p j s - gK p (j + 1) s * t| ≤
        |t| * (ε * |s| ^ (p - ((j + 1 : ℕ) : ℝ)) + C * |t| ^ (p - ((j + 1 : ℕ) : ℝ)))) →
      ‖Tj μ j hj0 (f + h) - Tj μ j hj0 f - (Tj μ (j + 1) hj1 f).curryLeft h‖ ≤
        ‖h‖ * (ε * ‖f‖ ^ (p - ((j + 1 : ℕ) : ℝ)) + C * ‖h‖ ^ (p - ((j + 1 : ℕ) : ℝ))) := by
    intro h ε hε C hC hb
    rw [hcurry h]
    have hA := memLp_gK (f + h) hj0
    have hB := memLp_gK f hj0
    simp only [Tj]
    rw [← wMul_sub _ hA hB, ← wMul_sub _ (hA.sub hB) (hwv h)]
    refine (norm_wMul_le _ _).trans ?_
    set Φ : α → ℝ := fun x => ε * |(f : α → ℝ) x| ^ (p - ((j + 1 : ℕ) : ℝ)) +
      C * |(h : α → ℝ) x| ^ (p - ((j + 1 : ℕ) : ℝ))
    have hΦ : (eLpNorm Φ (qE p (j + 1)) μ).toReal ≤
        ε * ‖f‖ ^ (p - ((j + 1 : ℕ) : ℝ)) + C * ‖h‖ ^ (p - ((j + 1 : ℕ) : ℝ)) :=
      eLpNorm_le_of_ae_bound' f h hr1 (by linarith [(Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ _)])
        hε.le hC (ae_of_all _ fun x => by
          rw [abs_of_nonneg (by positivity)])
    have hΦm : MemLp Φ (qE p (j + 1)) μ :=
      ((memLp_abs_rpow f hr1).const_mul ε).add ((memLp_abs_rpow h hr1).const_mul C)
    have hpt : ∀ᵐ x ∂μ, ‖((fun x => gK p j (((f + h : Lp ℝ (ENNReal.ofReal p) μ) : α → ℝ) x)) -
        (fun x => gK p j ((f : α → ℝ) x)) -
        fun x => gK p (j + 1) ((f : α → ℝ) x) * (h : α → ℝ) x) x‖ ≤
          ‖(h : α → ℝ) x * Φ x‖ := by
      filter_upwards [Lp.coeFn_add f h] with x hx
      simp only [Pi.sub_apply, hx, Pi.add_apply, Real.norm_eq_abs, Φ]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε * |(f : α → ℝ) x| ^
        (p - ((j + 1 : ℕ) : ℝ)) + C * |(h : α → ℝ) x| ^ (p - ((j + 1 : ℕ) : ℝ)))]
      exact hb _ _
    have hH : eLpNorm (fun x => (h : α → ℝ) x * Φ x) (qE p j) μ ≤
        (1 : ℝ≥0) * eLpNorm (h : α → ℝ) (ENNReal.ofReal p) μ * eLpNorm Φ (qE p (j + 1)) μ := by
      have := (holderTriple_qE p_pos hj).symm
      exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.aestronglyMeasurable h) hΦm.1 (· * ·) 1
        (ae_of_all _ fun x => by simp [nnnorm_mul])
    have hfin : eLpNorm (h : α → ℝ) (ENNReal.ofReal p) μ * eLpNorm Φ (qE p (j + 1)) μ ≠ ⊤ :=
      ENNReal.mul_ne_top (Lp.eLpNorm_ne_top h) hΦm.eLpNorm_ne_top
    calc (eLpNorm (((fun x => gK p j (((f + h : Lp ℝ (ENNReal.ofReal p) μ) : α → ℝ) x)) -
          fun x => gK p j ((f : α → ℝ) x)) -
          fun x => gK p (j + 1) ((f : α → ℝ) x) * (h : α → ℝ) x) (qE p j) μ).toReal
        ≤ (eLpNorm (fun x => (h : α → ℝ) x * Φ x) (qE p j) μ).toReal := by
          refine ENNReal.toReal_mono ?_ (eLpNorm_mono_ae hpt)
          refine ne_top_of_le_ne_top ?_ hH
          rw [ENNReal.coe_one, one_mul]; exact hfin
      _ ≤ (eLpNorm (h : α → ℝ) (ENNReal.ofReal p) μ * eLpNorm Φ (qE p (j + 1)) μ).toReal := by
          rw [ENNReal.coe_one, one_mul] at hH
          exact ENNReal.toReal_mono hfin hH
      _ = ‖h‖ * (eLpNorm Φ (qE p (j + 1)) μ).toReal := by rw [ENNReal.toReal_mul, Lp.norm_def]
      _ ≤ ‖h‖ * (ε * ‖f‖ ^ (p - ((j + 1 : ℕ) : ℝ)) + C * ‖h‖ ^ (p - ((j + 1 : ℕ) : ℝ))) := by
          gcongr
  -- `‖R(h)‖ / ‖h‖` is eventually small
  have hev := eventually_lt_of_bound (E := Lp ℝ (ENNReal.ofReal p) μ) hr1
    (by positivity : 0 ≤ ‖f‖ ^ (p - ((j + 1 : ℕ) : ℝ)))
    (B := fun h => ‖Tj μ j hj0 (f + h) - Tj μ j hj0 f - (Tj μ (j + 1) hj1 f).curryLeft h‖ / ‖h‖)
    (fun ε hε => by
      obtain ⟨C, hC, hCb⟩ := gK_taylor_le hj hε
      refine ⟨C, fun h => ?_⟩
      rcases eq_or_ne h 0 with rfl | hh
      · simp only [norm_zero, div_zero]
        have : (0 : ℝ) ^ (p - ((j + 1 : ℕ) : ℝ)) = 0 := Real.zero_rpow hr1.ne'
        rw [this, mul_zero, add_zero]
        positivity
      · rw [div_le_iff₀ (norm_pos_iff.2 hh), mul_comm]
        exact hrem h ε hε C hC hCb) hc
  filter_upwards [hev] with h hh
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  · have := (div_lt_iff₀ (norm_pos_iff.2 hne)).1 hh
    exact this.le

/-- **The Taylor series of `‖·‖ᵖ` up to every integer `n < p`.** -/
theorem hasFTaylorSeriesUpTo_normRpow {n : ℕ} (hn : (n : ℝ) < p) :
    HasFTaylorSeriesUpTo (n : ℕ∞) (fun f : Lp ℝ (ENNReal.ofReal p) μ => ‖f‖ ^ p)
      (taylorNormRpow μ) := by
  have hp0 : (0 : ℝ) < p := p_pos
  refine ⟨fun f => ?_, fun m hm f => ?_, fun m hm => ?_⟩
  · rw [taylorNormRpow_of_lt f (by simpa using hp0)]
    simp only [Tj, ContinuousMultilinearMap.curry0_apply, wMul_apply, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one]
    rw [norm_rpow_eq_integral hp0 f]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact gK_zero hp0 _
  · have hm' : m < n := by exact_mod_cast hm
    have hmp : (m : ℝ) + 1 < p := by
      have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm'
      push_cast at this; linarith
    have e1 : (fun y => taylorNormRpow μ y m) = Tj μ m (by linarith) := by
      funext y; exact taylorNormRpow_of_lt y _
    rw [e1, taylorNormRpow_of_lt f (by push_cast; linarith)]
    exact hasFDerivAt_Tj hmp f
  · have hm' : m ≤ n := by exact_mod_cast hm
    have hmp : (m : ℝ) < p := lt_of_le_of_lt (by exact_mod_cast hm') hn
    have e1 : (fun y => taylorNormRpow μ y m) = Tj μ m hmp := by
      funext y; exact taylorNormRpow_of_lt y _
    rw [e1]
    exact continuous_Tj hmp

/-- **`‖·‖ᵖ` is `C^n` on `Lᵖ` for every integer `n < p`.** -/
theorem contDiff_normRpow_of_lt {n : ℕ} (hn : (n : ℝ) < p) :
    ContDiff ℝ (n : ℕ∞) (fun f : Lp ℝ (ENNReal.ofReal p) μ => ‖f‖ ^ p) :=
  (hasFTaylorSeriesUpTo_normRpow hn).contDiff

end Taylor

/-! ### Theorem 5.5.5 -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **2021 Theorem 5.5.5, p. 230 (preprint 5.32), Bonic–Frampton.**  Let `p ≥ 1` and `‖·‖` the
usual norm of `Lᵖ(μ)`.
(1) If `p` is an even integer, `‖·‖ᵖ` is of class `C^∞`.
(2) If `p` is an odd integer, `‖·‖ᵖ` is of class `C^{p−1}`.
(3) If `p ≥ 1` is not an integer, `‖·‖ᵖ` is of class `C^{[p]}`. -/
theorem theorem_5_5_5 (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ((∃ k : ℕ, p = 2 * k) →
        ContDiff ℝ (⊤ : ℕ∞) (fun f : Lp ℝ (ENNReal.ofReal p) μ => ‖f‖ ^ p)) ∧
      (∀ k : ℕ, p = 2 * k + 1 →
        ContDiff ℝ ((2 * k : ℕ) : ℕ∞) (fun f : Lp ℝ (ENNReal.ofReal p) μ => ‖f‖ ^ p)) ∧
      ((∀ k : ℕ, p ≠ k) →
        ContDiff ℝ (⌊p⌋₊ : ℕ∞) (fun f : Lp ℝ (ENNReal.ofReal p) μ => ‖f‖ ^ p)) := by
  have hp1 : 1 ≤ p := one_le_p
  refine ⟨fun ⟨k, hk⟩ => ?_, fun k hk => ?_, fun hk => ?_⟩
  · subst hk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; norm_num at hp1
      · exact h
    have := theorem_5_5_5_even (μ := μ) k hk0
    have e : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    rwa [e] at this
  · exact contDiff_normRpow_of_lt (by push_cast; linarith)
  · refine contDiff_normRpow_of_lt (lt_of_le_of_ne (Nat.floor_le (by linarith)) ?_)
    exact fun h => hk _ h.symm

end BonicFrampton

end Polyfold
