import Polyfold.Chapter4.RemarkFourThreeExample
import Polyfold.Chapter1.ScOneNotNormContinuous

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), §4.1, Remark 4.3, p. 148.

# Remark 4.3's example: an sc-retract `O = O_∞` that is not an sc⁺-retract

## The text, paraphrased

(Remark 4.3) "It is possible that `X¹ ≠ X` as M-polyfolds although the underlying sets agree":
an M-polyfold with `X₀ = X_∞` for which `1₀¹ : X → X¹` is not sc-smooth.  No example is given
(comparison item V4.6, gap G.31).

## What is formalized

* **The example** (`remark_4_3_example`): an M-polyfold `X` (`retractPolyfold`, a retract with
  one chart) with every point smooth and `1₀¹ : X → X¹` not sc-smooth, for every junk value.  At
  the level of retracts: `remark_4_3_retract_example`, an sc-retract `O = O_∞` that is not an
  sc⁺-retract.  Both come from `RemarkFourThree.remarkFourThreeData : RemarkFourThreeData ℝ X`
  through the reduction of `RemarkFourThreeExample.lean`.
* **The family.**  `X` is the weighted sequence space of `ScOneNotNormContinuous.lean`
  (`|x|_m = sup (i+1)^m |x_i|`, every level `c₀`).  With `n_k = 2^k` (`nk`), nodes `1/(k+1)`
  (`node`), and angles `θ_k(t) = π/2 σ((k+1)(k+2)(1/(k+1) − t))` (`σ` = Mathlib's
  `Real.smoothTransition`; `θ_k = 0` for `t ≥ 1/(k+1)`, `π/2` for `t ≤ 1/(k+2)`), the
  coefficients `b_k = sin θ_{k−1} cos θ_k` (`bb`) vanish except `b_k = cos θ_k` and
  `b_{k+1} = sin θ_k` for the active block `k = ⌊1/t⌋ − 1` (`bb_eq_zero_of_pos`, `bb_kt`,
  `bb_kt_succ`), and all vanish for `t ≤ 0`.  `RemarkFourThree.fam t m` is `Σ_k (block k)`
  (`blk`, a `tsum` with two nonzero terms): on level `0` the projection onto
  `β_t = b_k e_{n_k} + b_{k+1} e_{n_{k+1}}` (`fam_of_pos`); on level `m` the entries carry the
  weight ratios `((a+1)/(b+1))^m` (`elemL`), at most `2^m` since consecutive `n_k` have ratio
  `≤ 2`.
* **The estimates.**  `norm_fam_le`: `‖L(t)_m‖ ≤ 3 + 2^m`.  `contDiff_fam_comp`: `t ↦ L(t)_m ∘ ι`
  is `C^∞` into `L(X_{m+1}, X_m)` (`contDiff_tsum`): `j` derivatives of the `k`-th block cost
  `K4_j (k+3)^{2j}` (`DerivBound`, products by Leibniz, the transition's derivatives bounded by
  `exists_bound_iteratedFDeriv`), and one level gains `(2 + 2^m) 2^{−k}`.
  `continuous_apply_of_bound`: a uniform bound and norm continuity after the dense `ι` give
  strong continuity.  Hence `isLossFamily_fam`.  `fam_idem` (projections), `fam_mem_smooth`
  (finitely supported ranges), and `not_continuousOn_liftOne`: the points
  `o_k = (1/(k+1), (1/(k+1)) e_{n_k}) ∈ O` tend to `0` in `E₀` while their level-`1` coordinates
  have norm `≥ (2^k + 1)/(k + 1) ≥ 1`.

## What the text leaves implicit, and the choices made

* The text's "`X¹ ≠ X` as M-polyfolds" is read as "`1₀¹` is not sc-smooth" (with
  `remark_4_3_isScDiffeo`, the identity is then not an sc-diffeomorphism `X → X¹`).  The example
  even has different topologies: `X` and `X¹` have the same points but `o_k → 0` only in `X`.
* The sparse indices `2^k` make one level gain `2^{−k}`, which absorbs the polynomial cost
  `(k+3)^{2j}` of the transitions; consecutive indices would not (Findings, Chapter 4, item 142).
* The instances of `c₀ →L[ℝ] c₀` need `maxSynthPendingDepth 3` (as `Test.lean` does).
-/

open Set Filter Topology Function
open scoped ContDiff

-- the instances of `c₀ →L[ℝ] c₀` (`c₀ = C₀(ℕ, ℝ)`) need a deeper instance search
set_option maxSynthPendingDepth 3

noncomputable section

namespace Polyfold

namespace RemarkFourThree

/-! ### The flat transition and its derivative bounds -/

/-- `cos(π/2 σ(x))`, `σ` Mathlib's smooth transition (`0` for `x ≤ 0`, `1` for `x ≥ 1`). -/
def cf (x : ℝ) : ℝ := Real.cos (Real.pi / 2 * Real.smoothTransition x)

/-- `sin(π/2 σ(x))`. -/
def sf (x : ℝ) : ℝ := Real.sin (Real.pi / 2 * Real.smoothTransition x)

lemma contDiff_smoothTransition : ContDiff ℝ ∞ Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := ⊤)

lemma contDiff_cf : ContDiff ℝ ∞ cf :=
  Real.contDiff_cos.comp (contDiff_const.mul contDiff_smoothTransition)

lemma contDiff_sf : ContDiff ℝ ∞ sf :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_smoothTransition)

lemma cf_of_nonpos {x : ℝ} (hx : x ≤ 0) : cf x = 1 := by
  rw [cf, Real.smoothTransition.zero_of_nonpos hx, mul_zero, Real.cos_zero]

lemma sf_of_nonpos {x : ℝ} (hx : x ≤ 0) : sf x = 0 := by
  rw [sf, Real.smoothTransition.zero_of_nonpos hx, mul_zero, Real.sin_zero]

lemma cf_of_one_le {x : ℝ} (hx : 1 ≤ x) : cf x = 0 := by
  rw [cf, Real.smoothTransition.one_of_one_le hx, mul_one, Real.cos_pi_div_two]

lemma sf_of_one_le {x : ℝ} (hx : 1 ≤ x) : sf x = 1 := by
  rw [sf, Real.smoothTransition.one_of_one_le hx, mul_one, Real.sin_pi_div_two]

lemma cf_sq_add_sf_sq (x : ℝ) : cf x ^ 2 + sf x ^ 2 = 1 := Real.cos_sq_add_sin_sq _

/-- A smooth function, constant on `(-∞, 0]` and on `[1, ∞)`, has bounded derivatives. -/
lemma exists_bound_iteratedFDeriv {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (h0 : ∀ x ≤ 0, G x = G 0) (h1 : ∀ x, 1 ≤ x → G x = G 1) (j : ℕ) :
    ∃ M, ∀ x, ‖iteratedFDeriv ℝ j G x‖ ≤ M := by
  have hc : Continuous fun x => iteratedFDeriv ℝ j G x :=
    hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M₀ (max ‖G 0‖ ‖G 1‖), fun x => ?_⟩
  have hconst : ∀ (c : ℝ), G =ᶠ[𝓝 x] (fun _ => c) → ‖iteratedFDeriv ℝ j G x‖ ≤ ‖c‖ := by
    intro c hc'
    rw [(hc'.iteratedFDeriv ℝ j).eq_of_nhds]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne hj.ne']; simp
  rcases lt_or_ge x 0 with hx | hx
  · have := hconst (G 0) (by filter_upwards [Iio_mem_nhds hx] with y hy using h0 y hy.le)
    exact this.trans (le_max_of_le_right (le_max_left _ _))
  rcases le_or_gt x 1 with hx1 | hx1
  · exact (hM₀ x ⟨hx, hx1⟩).trans (le_max_left _ _)
  · have := hconst (G 1) (by filter_upwards [Ioi_mem_nhds hx1] with y hy using h1 y hy.le)
    exact this.trans (le_max_of_le_right (le_max_right _ _))

/-- The derivative bound of `cos(π/2 σ)`. -/
def Mc (j : ℕ) : ℝ :=
  (exists_bound_iteratedFDeriv contDiff_cf
    (fun x hx => by rw [cf_of_nonpos hx, cf_of_nonpos le_rfl])
    (fun x hx => by rw [cf_of_one_le hx, cf_of_one_le le_rfl]) j).choose

lemma norm_iteratedFDeriv_cf_le (j : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ j cf x‖ ≤ Mc j :=
  (exists_bound_iteratedFDeriv contDiff_cf
    (fun x hx => by rw [cf_of_nonpos hx, cf_of_nonpos le_rfl])
    (fun x hx => by rw [cf_of_one_le hx, cf_of_one_le le_rfl]) j).choose_spec x

/-- The derivative bound of `sin(π/2 σ)`. -/
def Ms (j : ℕ) : ℝ :=
  (exists_bound_iteratedFDeriv contDiff_sf
    (fun x hx => by rw [sf_of_nonpos hx, sf_of_nonpos le_rfl])
    (fun x hx => by rw [sf_of_one_le hx, sf_of_one_le le_rfl]) j).choose

lemma norm_iteratedFDeriv_sf_le (j : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ j sf x‖ ≤ Ms j :=
  (exists_bound_iteratedFDeriv contDiff_sf
    (fun x hx => by rw [sf_of_nonpos hx, sf_of_nonpos le_rfl])
    (fun x hx => by rw [sf_of_one_le hx, sf_of_one_le le_rfl]) j).choose_spec x

/-- Derivatives of `t ↦ G(α(a − t))`: `|α|^j` times those of `G`. -/
lemma norm_iteratedFDeriv_comp_affine {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (α a : ℝ) (j : ℕ)
    (t : ℝ) : ‖iteratedFDeriv ℝ j (fun t => G (α * (a - t))) t‖ =
      |α| ^ j * ‖iteratedFDeriv ℝ j G (α * (a - t))‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have e1 := congrFun (iteratedDeriv_comp_const_sub j (fun x => G (α * x)) a) t
  have e2 := congrFun
    (iteratedDeriv_comp_const_mul (n := j) (hG.of_le (by exact_mod_cast le_top)) α)
    (a - t)
  rw [e1, e2]
  simp [norm_mul, Real.norm_eq_abs]

/-! ### Bounds of the form `‖D^j f‖ ≤ C_j D^j` and products -/

/-- `‖D^j f(t)‖ ≤ C_j D^j` for all `j`, `t`. -/
def DerivBound (f : ℝ → ℝ) (D : ℝ) (C : ℕ → ℝ) : Prop :=
  ∀ j t, ‖iteratedFDeriv ℝ j f t‖ ≤ C j * D ^ j

/-- The constants of a product (Leibniz). -/
def mulBound (C C' : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C i * C' (j - i)

lemma DerivBound.mul {f g : ℝ → ℝ} {D : ℝ} {C C' : ℕ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (h1 : DerivBound f D C) (h2 : DerivBound g D C') :
    DerivBound (fun t => f t * g t) D (mulBound C C') := by
  intro j t
  refine (norm_iteratedFDeriv_mul_le hf hg t (by exact_mod_cast le_top)).trans ?_
  rw [mulBound, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : D ^ j = D ^ i * D ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hij]
  rw [e]
  have a1 := h1 i t
  have a2 := h2 (j - i) t
  have b1 : 0 ≤ C i * D ^ i := (norm_nonneg _).trans a1
  calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f t‖ * ‖iteratedFDeriv ℝ (j - i) g t‖
      ≤ (j.choose i : ℝ) * (C i * D ^ i) * (C' (j - i) * D ^ (j - i)) := by
        gcongr
    _ = (j.choose i : ℝ) * C i * C' (j - i) * (D ^ i * D ^ (j - i)) := by ring

/-! ### The angles and the coefficients `b_j` -/

/-- The slopes `(j+1)(j+2)`. -/
def slope (j : ℕ) : ℝ := ((j : ℝ) + 1) * ((j : ℝ) + 2)

/-- The nodes `1/(j+1)`. -/
def node (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma slope_nonneg (j : ℕ) : 0 ≤ slope j := by unfold slope; positivity

lemma node_pos (j : ℕ) : 0 < node j := by unfold node; positivity

lemma node_anti {i j : ℕ} (h : i ≤ j) : node j ≤ node i := by
  unfold node
  gcongr

lemma slope_mono {i j : ℕ} (h : i ≤ j) : slope i ≤ slope j := by
  unfold slope
  have : (i : ℝ) ≤ j := by exact_mod_cast h
  gcongr

lemma slope_mul_node_sub (j : ℕ) : slope j * (node j - node (j + 1)) = 1 := by
  unfold slope node; push_cast; field_simp; ring

/-- `c_j(t) = cos θ_j(t)`, `θ_j(t) = π/2 σ((j+1)(j+2)(1/(j+1) − t))`: `θ_j = 0` for
`t ≥ 1/(j+1)` and `θ_j = π/2` for `t ≤ 1/(j+2)`. -/
def cc (j : ℕ) (t : ℝ) : ℝ := cf (slope j * (node j - t))

/-- `s_j(t) = sin θ_j(t)`. -/
def ss (j : ℕ) (t : ℝ) : ℝ := sf (slope j * (node j - t))

lemma arg_nonpos {j : ℕ} {t : ℝ} (ht : node j ≤ t) : slope j * (node j - t) ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (slope_nonneg j) (by linarith)

lemma one_le_arg {j : ℕ} {t : ℝ} (ht : t ≤ node (j + 1)) : 1 ≤ slope j * (node j - t) := by
  rw [← slope_mul_node_sub j]
  exact mul_le_mul_of_nonneg_left (by linarith) (slope_nonneg j)

lemma cc_of_le {j : ℕ} {t : ℝ} (ht : node j ≤ t) : cc j t = 1 := cf_of_nonpos (arg_nonpos ht)
lemma ss_of_le {j : ℕ} {t : ℝ} (ht : node j ≤ t) : ss j t = 0 := sf_of_nonpos (arg_nonpos ht)
lemma cc_of_ge {j : ℕ} {t : ℝ} (ht : t ≤ node (j + 1)) : cc j t = 0 := cf_of_one_le (one_le_arg ht)
lemma ss_of_ge {j : ℕ} {t : ℝ} (ht : t ≤ node (j + 1)) : ss j t = 1 := sf_of_one_le (one_le_arg ht)

lemma contDiff_cc (j : ℕ) : ContDiff ℝ ∞ (cc j) :=
  contDiff_cf.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

lemma contDiff_ss (j : ℕ) : ContDiff ℝ ∞ (ss j) :=
  contDiff_sf.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

/-- The previous sine factor: `1` for `j = 0`, `s_{j−1}` otherwise. -/
def sp : ℕ → ℝ → ℝ
  | 0, _ => 1
  | j + 1, t => ss j t

/-- **The coefficients** `b_j = s_{j−1} c_j` (`b_0 = c_0`): on `[1/(k+2), 1/(k+1)]` only `b_k = c_k`
and `b_{k+1} = s_k` are nonzero. -/
def bb (j : ℕ) (t : ℝ) : ℝ := sp j t * cc j t

lemma contDiff_sp (j : ℕ) : ContDiff ℝ ∞ (sp j) := by
  cases j with
  | zero => exact contDiff_const
  | succ j => exact contDiff_ss j

lemma contDiff_bb (j : ℕ) : ContDiff ℝ ∞ (bb j) := (contDiff_sp j).mul (contDiff_cc j)

/-- The uniform constants `K_j ≥ 1` bounding the derivatives of `cos(π/2 σ)`, `sin(π/2 σ)`, `1`. -/
def K (j : ℕ) : ℝ := max (Mc j) (Ms j) + 1

lemma one_le_K (j : ℕ) : 1 ≤ K j := by
  have h0 : 0 ≤ Mc j := (norm_nonneg _).trans (norm_iteratedFDeriv_cf_le j 0)
  unfold K; linarith [le_max_left (Mc j) (Ms j)]

lemma derivBound_cc (j : ℕ) {D : ℝ} (hD : slope j ≤ D) : DerivBound (cc j) D K := by
  intro i t
  change ‖iteratedFDeriv ℝ i (fun t => cf (slope j * (node j - t))) t‖ ≤ _
  rw [norm_iteratedFDeriv_comp_affine contDiff_cf, abs_of_nonneg (slope_nonneg j)]
  rw [mul_comm]
  have hM : Mc i ≤ K i := by have := le_max_left (Mc i) (Ms i); unfold K; linarith
  exact mul_le_mul ((norm_iteratedFDeriv_cf_le i _).trans hM)
    (pow_le_pow_left₀ (slope_nonneg j) hD i)
    (pow_nonneg (slope_nonneg j) i) ((zero_le_one).trans (one_le_K i))

lemma derivBound_ss (j : ℕ) {D : ℝ} (hD : slope j ≤ D) : DerivBound (ss j) D K := by
  intro i t
  change ‖iteratedFDeriv ℝ i (fun t => sf (slope j * (node j - t))) t‖ ≤ _
  rw [norm_iteratedFDeriv_comp_affine contDiff_sf, abs_of_nonneg (slope_nonneg j)]
  rw [mul_comm]
  have hM : Ms i ≤ K i := by have := le_max_right (Mc i) (Ms i); unfold K; linarith
  exact mul_le_mul ((norm_iteratedFDeriv_sf_le i _).trans hM)
    (pow_le_pow_left₀ (slope_nonneg j) hD i)
    (pow_nonneg (slope_nonneg j) i) ((zero_le_one).trans (one_le_K i))

lemma derivBound_sp (j : ℕ) {D : ℝ} (hD : slope j ≤ D) (hD0 : 0 ≤ D) :
    DerivBound (sp j) D K := by
  cases j with
  | zero =>
    intro i t
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [sp, norm_iteratedFDeriv_zero, norm_one, pow_zero, mul_one]; exact one_le_K 0
    · rw [show sp 0 = fun _ => (1 : ℝ) from rfl, iteratedFDeriv_const_of_ne hi.ne']
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg ((zero_le_one).trans (one_le_K i)) (pow_nonneg hD0 i)
  | succ j => exact derivBound_ss j ((slope_mono (Nat.le_succ j)).trans hD)

/-- The constants for `b_j`. -/
def K2 : ℕ → ℝ := mulBound K K

lemma derivBound_bb (j : ℕ) {D : ℝ} (hD : slope j ≤ D) : DerivBound (bb j) D K2 :=
  DerivBound.mul (contDiff_sp j) (contDiff_cc j)
    (derivBound_sp j hD ((slope_nonneg j).trans hD)) (derivBound_cc j hD)

/-- The constants for `b_j b_l`. -/
def K4 : ℕ → ℝ := mulBound K2 K2

/-- The derivative scale of the `k`-th block, `(k+3)²`. -/
def Dk (k : ℕ) : ℝ := ((k : ℝ) + 3) ^ 2

lemma slope_le_Dk {k j : ℕ} (hj : j ≤ k + 1) : slope j ≤ Dk k := by
  unfold slope Dk
  have : (j : ℝ) ≤ k + 1 := by exact_mod_cast hj
  nlinarith

lemma derivBound_bb_sq (k : ℕ) : DerivBound (fun t => bb k t * bb k t) (Dk k) K4 :=
  DerivBound.mul (contDiff_bb k) (contDiff_bb k) (derivBound_bb k (slope_le_Dk (by omega)))
    (derivBound_bb k (slope_le_Dk (by omega)))

lemma derivBound_bb_mul (k : ℕ) : DerivBound (fun t => bb k t * bb (k + 1) t) (Dk k) K4 :=
  DerivBound.mul (contDiff_bb k) (contDiff_bb (k + 1)) (derivBound_bb k (slope_le_Dk (by omega)))
    (derivBound_bb (k + 1) (slope_le_Dk le_rfl))

/-! ### Which coefficients are nonzero -/

/-- The active block at `t > 0`: `k = ⌊1/t⌋ − 1` (`0` for `t > 1`). -/
def kt (t : ℝ) : ℕ := ⌊t⁻¹⌋₊ - 1

lemma node_succ_kt_lt {t : ℝ} (ht : 0 < t) : node (kt t + 1) < t := by
  have h1 : t⁻¹ < (⌊t⁻¹⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : (⌊t⁻¹⌋₊ : ℝ) ≤ (kt t : ℝ) + 1 := by unfold kt; exact_mod_cast (by omega)
  unfold node
  rw [div_lt_iff₀ (by positivity)]
  have := (inv_lt_iff_one_lt_mul₀ ht).1 (show t⁻¹ < (kt t + 1 : ℕ) + 1 by push_cast; linarith)
  push_cast at this ⊢; linarith

lemma le_node_kt {t : ℝ} (ht : 0 < t) (hk : 1 ≤ kt t) : t ≤ node (kt t) := by
  have h1 : ⌊t⁻¹⌋₊ = kt t + 1 := by unfold kt at hk ⊢; omega
  have h2 : ((kt t : ℝ) + 1) ≤ t⁻¹ := by
    have := Nat.floor_le (inv_nonneg.2 ht.le); rw [h1] at this; exact_mod_cast this
  unfold node
  rw [le_div_iff₀ (by positivity)]
  calc t * ((kt t : ℝ) + 1) ≤ t * t⁻¹ := mul_le_mul_of_nonneg_left h2 ht.le
    _ = 1 := mul_inv_cancel₀ ht.ne'

/-- **At `t > 0` only `b_k = c_k` and `b_{k+1} = s_k` (`k = kt t`) are nonzero.** -/
lemma bb_eq_zero_of_pos {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : j ≠ kt t) (hj' : j ≠ kt t + 1) :
    bb j t = 0 := by
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · -- `j < k`: `c_j = 0`
    have hk : 1 ≤ kt t := by omega
    have : t ≤ node (j + 1) := (le_node_kt ht hk).trans (node_anti (by omega))
    rw [bb, cc_of_ge this, mul_zero]
  · -- `j ≥ k + 2`: `s_{j−1} = 0`
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have : node i ≤ t := (node_anti (by omega)).trans (node_succ_kt_lt ht).le
    rw [bb, show sp (i + 1) t = ss i t from rfl, ss_of_le this, zero_mul]

lemma bb_kt {t : ℝ} (ht : 0 < t) : bb (kt t) t = cc (kt t) t := by
  rcases Nat.eq_zero_or_pos (kt t) with h | h
  · rw [bb, h]; simp [sp]
  · obtain ⟨i, hi⟩ : ∃ i, kt t = i + 1 := ⟨kt t - 1, by omega⟩
    have h1 : t ≤ node (i + 1) := hi ▸ le_node_kt ht (by omega)
    rw [bb, hi, show sp (i + 1) t = ss i t from rfl, ss_of_ge h1, one_mul]

lemma bb_kt_succ {t : ℝ} (ht : 0 < t) : bb (kt t + 1) t = ss (kt t) t := by
  rw [bb, show sp (kt t + 1) t = ss (kt t) t from rfl, cc_of_le (node_succ_kt_lt ht).le, mul_one]

/-- At `t ≤ 0` every `b_j` vanishes. -/
lemma bb_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) (j : ℕ) : bb j t = 0 := by
  rw [bb, cc_of_ge (ht.trans (node_pos _).le), mul_zero]

/-- The support of `j ↦ b_j(t)`. -/
def supp (t : ℝ) : Finset ℕ := if 0 < t then {kt t, kt t + 1} else ∅

lemma bb_eq_zero_of_not_mem {t : ℝ} {j : ℕ} (hj : j ∉ supp t) : bb j t = 0 := by
  unfold supp at hj
  split_ifs at hj with ht
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact bb_eq_zero_of_pos ht hj.1 hj.2
  · exact bb_eq_zero_of_nonpos (not_lt.1 ht) j

/-! ### Elementary operators on `c₀` -/

open ScOneExample

/-- The unit vector `e_a ∈ c₀`. -/
def δv (a : ℕ) : c0 :=
  mkC0 (fun i => if i = a then 1 else 0) (tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop a] with i hi
    rw [if_neg (by omega)]))

@[simp] lemma δv_apply (a i : ℕ) : δv a i = if i = a then 1 else 0 := rfl

lemma norm_δv_le (a : ℕ) : ‖δv a‖ ≤ 1 :=
  norm_le_of_forall zero_le_one fun i => by rw [δv_apply]; split_ifs <;> simp

/-- The coordinate `y ↦ y_b` as a continuous functional on `c₀`. -/
def evalL (b : ℕ) : c0 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun y : c0 => y b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun y => by
        rw [one_mul, Real.norm_eq_abs]; exact abs_apply_le_norm y b)

lemma norm_evalL_le (b : ℕ) : ‖evalL b‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The elementary operator `y ↦ y_b e_a` on `c₀`. -/
def elem (a b : ℕ) : c0 →L[ℝ] c0 := (evalL b).smulRight (δv a)

lemma elem_apply (a b : ℕ) (y : c0) (i : ℕ) : elem a b y i = if i = a then y b else 0 := by
  change y b * (if i = a then (1 : ℝ) else 0) = _
  split_ifs <;> simp

lemma norm_elem_le (a b : ℕ) : ‖elem a b‖ ≤ 1 := by
  rw [elem, ContinuousLinearMap.norm_smulRight_apply]
  calc ‖evalL b‖ * ‖δv a‖ ≤ 1 * 1 :=
        mul_le_mul (norm_evalL_le b) (norm_δv_le a) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The weight ratio `(a+1)/(b+1)` of the entry `(a, b)` on level `1`. -/
def ratio (a b : ℕ) : ℝ := ((a : ℝ) + 1) / ((b : ℝ) + 1)

lemma ratio_nonneg (a b : ℕ) : 0 ≤ ratio a b := by unfold ratio; positivity

/-- The entry `(a, b)` read on level `m` (coordinates `(i+1)^m x_i`): `((a+1)/(b+1))^m y_b e_a`. -/
def elemL (m a b : ℕ) : c0 →L[ℝ] c0 := (ratio a b ^ m) • elem a b

lemma elemL_apply (m a b : ℕ) (y : c0) (i : ℕ) :
    elemL m a b y i = if i = a then ratio a b ^ m * y b else 0 := by
  change ratio a b ^ m * elem a b y i = _
  rw [elem_apply]; split_ifs <;> simp

lemma elemL_zero (a b : ℕ) : elemL 0 a b = elem a b := by rw [elemL, pow_zero, one_smul ℝ]

lemma norm_elemL_le (m a b : ℕ) : ‖elemL m a b‖ ≤ ratio a b ^ m := by
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (ratio_nonneg a b) m)]
  calc ratio a b ^ m * ‖elem a b‖ ≤ ratio a b ^ m * 1 :=
        mul_le_mul_of_nonneg_left (norm_elem_le a b) (pow_nonneg (ratio_nonneg a b) m)
    _ = ratio a b ^ m := mul_one _

/-- The level-`m` entries are compatible with the inclusions `X_m → X₀`. -/
lemma toBase_elemL (m a b : ℕ) (y : X m) :
    X.toBase m (elemL m a b y) = elemL 0 a b (X.toBase m y) := by
  ext i
  rw [X_toBase_apply, elemL_apply, elemL_apply, X_toBase_apply]
  split_ifs with h
  · subst h
    rw [pow_zero, one_mul, ← mul_assoc, ← mul_pow]
    congr 2
    unfold w ratio; field_simp
  · simp

lemma toBase_elemL' (m a b : ℕ) (y : X m) :
    XScale.toBase m (elemL m a b y) = elemL 0 a b (XScale.toBase m y) := toBase_elemL m a b y

lemma norm_elemL_comp_inclOp_le (m a b : ℕ) :
    ‖(elemL m a b).comp inclOp‖ ≤ ratio a b ^ m * w b := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (pow_nonneg (ratio_nonneg a b) m) (w_pos b).le) fun y => ?_
  refine norm_le_of_forall (by have := w_pos b; have := ratio_nonneg a b; positivity) fun i => ?_
  rw [ContinuousLinearMap.comp_apply, elemL_apply]
  split_ifs
  · change |ratio a b ^ m * (w b * y b)| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (ratio_nonneg a b) m),
      abs_of_pos (w_pos b), ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_apply_le_norm y b)
      (mul_nonneg (pow_nonneg (ratio_nonneg a b) m) (w_pos b).le)
  · simp only [abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (ratio_nonneg a b) m) (w_pos b).le) (norm_nonneg _)

/-! ### The sparse indices `n_k = 2^k` -/

/-- The coordinates `n_k = 2^k` visited by the moving vector. -/
def nk (k : ℕ) : ℕ := 2 ^ k

lemma nk_lt (k : ℕ) : nk k < nk (k + 1) :=
  Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)

lemma nk_ne (k : ℕ) : nk k ≠ nk (k + 1) := (nk_lt k).ne

lemma ratio_up_le (k : ℕ) : ratio (nk k) (nk (k + 1)) ≤ 1 := by
  unfold ratio
  rw [div_le_one (by positivity)]
  have := nk_lt k
  have : (nk k : ℝ) ≤ nk (k + 1) := by exact_mod_cast this.le
  linarith

lemma ratio_down_le (k : ℕ) : ratio (nk (k + 1)) (nk k) ≤ 2 := by
  unfold ratio nk
  rw [div_le_iff₀ (by positivity)]
  push_cast; rw [pow_succ]; nlinarith [pow_pos (two_pos (α := ℝ)) k]

lemma ratio_self (a : ℕ) : ratio a a = 1 := by unfold ratio; field_simp

lemma w_nk_le (k : ℕ) : w (nk k) ≤ (1 / 2) ^ k := by
  unfold w nk
  rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
  push_cast; linarith

lemma w_nk_succ_le (k : ℕ) : w (nk (k + 1)) ≤ (1 / 2) ^ k :=
  (w_nk_le (k + 1)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k))

/-! ### The blocks and the family -/

/-- **The `k`-th block** on level `m`: `b_k² e_{n_k} ⊗ e_{n_k} + b_k b_{k+1}(e_{n_k} ⊗ e_{n_{k+1}} +
e_{n_{k+1}} ⊗ e_{n_k})`, read in level-`m` coordinates. -/
def blk (k : ℕ) (t : ℝ) (m : ℕ) : c0 →L[ℝ] c0 :=
  (bb k t * bb k t) • elemL m (nk k) (nk k) +
    (bb k t * bb (k + 1) t) • (elemL m (nk k) (nk (k + 1)) + elemL m (nk (k + 1)) (nk k))

/-- **The family** `L(t)_m = Σ_k (block k)`: on level `0` the projection onto
`β_t = Σ_j b_j(t) e_{n_j}` (two consecutive terms at a time); `L(t) = 0` for `t ≤ 0`. -/
def fam (t : ℝ) (m : ℕ) : c0 →L[ℝ] c0 := ∑' k, blk k t m

lemma blk_eq_zero {k : ℕ} {t : ℝ} (hk : k ∉ supp t) (m : ℕ) : blk k t m = 0 := by
  rw [blk, bb_eq_zero_of_not_mem hk]; simp

lemma fam_eq_sum (t : ℝ) (m : ℕ) : fam t m = ∑ k ∈ supp t, blk k t m :=
  tsum_eq_sum fun _ hk => blk_eq_zero hk m

lemma fam_comp_eq_tsum (t : ℝ) (m : ℕ) :
    (fam t m).comp inclOp = ∑' k, (blk k t m).comp inclOp := by
  rw [tsum_eq_sum (s := supp t) fun k hk => by rw [blk_eq_zero hk, ContinuousLinearMap.zero_comp],
    fam_eq_sum]
  ext y i
  simp

lemma fam_of_nonpos {t : ℝ} (ht : t ≤ 0) (m : ℕ) : fam t m = 0 := by
  rw [fam_eq_sum, supp, if_neg (not_lt.2 ht), Finset.sum_empty]

/-- **The family at `t > 0`**: with `k = kt t`, `c = c_k(t)`, `s = s_k(t)`, `a = n_k`,
`b = n_{k+1}`, `L(t)_m = c² e_a⊗e_a + cs(ρ^m e_a⊗e_b + ρ^{−m} e_b⊗e_a) + s² e_b⊗e_b`. -/
lemma fam_of_pos {t : ℝ} (ht : 0 < t) (m : ℕ) :
    fam t m = (cc (kt t) t * cc (kt t) t) • elemL m (nk (kt t)) (nk (kt t)) +
      (cc (kt t) t * ss (kt t) t) • (elemL m (nk (kt t)) (nk (kt t + 1)) +
        elemL m (nk (kt t + 1)) (nk (kt t))) +
      (ss (kt t) t * ss (kt t) t) • elemL m (nk (kt t + 1)) (nk (kt t + 1)) := by
  rw [fam_eq_sum, supp, if_pos ht, Finset.sum_pair (by omega), blk, blk, bb_kt ht, bb_kt_succ ht,
    bb_eq_zero_of_pos ht (j := kt t + 1 + 1) (by omega) (by omega)]
  simp only [mul_zero, zero_smul, add_zero]

/-- Level `0` coordinates at `t > 0`. -/
lemma fam_zero_apply_of_pos {t : ℝ} (ht : 0 < t) (y : c0) (i : ℕ) :
    fam t 0 y i =
      if i = nk (kt t) then cc (kt t) t * (cc (kt t) t * y (nk (kt t)) +
          ss (kt t) t * y (nk (kt t + 1)))
      else if i = nk (kt t + 1) then ss (kt t) t * (cc (kt t) t * y (nk (kt t)) +
          ss (kt t) t * y (nk (kt t + 1)))
      else 0 := by
  rw [fam_of_pos ht]
  simp only [elemL_zero, add_apply, FunLike.coe_smul,
    ZeroAtInftyContinuousMap.coe_add, ZeroAtInftyContinuousMap.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, elem_apply]
  have hne := nk_ne (kt t)
  split_ifs with h1 h2 <;> subst_vars <;> simp_all <;> ring

/-! ### The loss-family estimates -/

lemma toBase_blk (k : ℕ) (t : ℝ) (m : ℕ) (y : X m) :
    X.toBase m (blk k t m y) = blk k t 0 (X.toBase m y) := by
  simp only [blk, add_apply, FunLike.coe_smul, Pi.smul_apply,
    map_add, map_smul]
  erw [toBase_elemL', toBase_elemL', toBase_elemL']

/-- The family is compatible with the inclusions `X_m → X₀`. -/
lemma toBase_fam (t : ℝ) (m : ℕ) (y : X m) :
    X.toBase m (fam t m y) = fam t 0 (X.toBase m y) := by
  rw [fam_eq_sum, fam_eq_sum, sum_apply, sum_apply, map_sum]
  exact Finset.sum_congr rfl fun k _ => toBase_blk k t m y

lemma norm_smul_le_of_abs_le {r B : ℝ} {T : c0 →L[ℝ] c0} (hr : |r| ≤ 1) (hT : ‖T‖ ≤ B) :
    ‖r • T‖ ≤ B := by
  refine (norm_smul_le r T).trans ?_
  rw [Real.norm_eq_abs]
  calc |r| * ‖T‖ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    _ ≤ B := by rw [one_mul]; exact hT

lemma abs_cc_le (k : ℕ) (t : ℝ) : |cc k t| ≤ 1 := Real.abs_cos_le_one _
lemma abs_ss_le (k : ℕ) (t : ℝ) : |ss k t| ≤ 1 := Real.abs_sin_le_one _

lemma abs_mul_le_one' {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) hb

/-- **The level-`m` operators are uniformly bounded**: `‖L(t)_m‖ ≤ 3 + 2^m`. -/
lemma norm_fam_le (t : ℝ) (m : ℕ) : ‖fam t m‖ ≤ 3 + 2 ^ m := by
  rcases le_or_gt t 0 with ht | ht
  · rw [fam_of_nonpos ht, norm_zero]; positivity
  · rw [fam_of_pos ht m]
    set k := kt t
    have h1 : ‖elemL m (nk k) (nk k)‖ ≤ 1 :=
      (norm_elemL_le _ _ _).trans (by rw [ratio_self, one_pow])
    have h2 : ‖elemL m (nk k) (nk (k + 1))‖ ≤ 1 :=
      (norm_elemL_le _ _ _).trans (pow_le_one₀ (ratio_nonneg _ _) (ratio_up_le k))
    have h3 : ‖elemL m (nk (k + 1)) (nk k)‖ ≤ 2 ^ m :=
      (norm_elemL_le _ _ _).trans (pow_le_pow_left₀ (ratio_nonneg _ _) (ratio_down_le k) m)
    have h4 : ‖elemL m (nk (k + 1)) (nk (k + 1))‖ ≤ 1 :=
      (norm_elemL_le _ _ _).trans (by rw [ratio_self, one_pow])
    refine (norm_add₃_le).trans ?_
    have e1 := norm_smul_le_of_abs_le (abs_mul_le_one' (abs_cc_le k t) (abs_cc_le k t)) h1
    have e2 := norm_smul_le_of_abs_le (abs_mul_le_one' (abs_cc_le k t) (abs_ss_le k t))
      ((norm_add_le _ _).trans (add_le_add h2 h3))
    have e3 := norm_smul_le_of_abs_le (abs_mul_le_one' (abs_ss_le k t) (abs_ss_le k t)) h4
    linarith

/-- **Strong continuity from a uniform bound** and norm continuity after the dense inclusion
`ι : X₁ → X₀` (an `ε/3` argument). -/
lemma continuous_apply_of_bound (A : ℝ → c0 →L[ℝ] c0) (C : ℝ) (hb : ∀ t, ‖A t‖ ≤ C)
    (hc : Continuous fun t => (A t).comp inclOp) : Continuous fun q : ℝ × c0 => A q.1 q.2 := by
  rw [Metric.continuous_iff]
  rintro ⟨t₀, y₀⟩ ε hε
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  set η := ε / (4 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hd : DenseRange inclOp := X.denseRange_incl 0
  obtain ⟨z, hz⟩ : ∃ z, dist y₀ (inclOp z) < η := hd.exists_dist_lt y₀ hη0
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuous_iff.1 hc t₀ (ε / (4 * (‖z‖ + 1))) (by positivity)
  refine ⟨min δ₁ η, lt_min hδ₁ hη0, ?_⟩
  rintro ⟨t, y⟩ hq
  rw [Prod.dist_eq] at hq
  have ht : dist t t₀ < δ₁ := (le_max_left _ _).trans_lt (hq.trans_le (min_le_left _ _))
  have hy : dist y y₀ < η := (le_max_right _ _).trans_lt (hq.trans_le (min_le_right _ _))
  have h1 := hδ₁' t ht
  rw [dist_eq_norm] at h1 hy hz ⊢
  have e : A t y - A t₀ y₀ = A t (y - y₀) + A t (y₀ - inclOp z) +
      ((A t).comp inclOp - (A t₀).comp inclOp) z + A t₀ (inclOp z - y₀) := by
    simp only [map_sub, sub_apply, ContinuousLinearMap.comp_apply]; abel
  have b1 : ‖A t (y - y₀)‖ ≤ C * η :=
    ((A t).le_opNorm _).trans (mul_le_mul (hb t) hy.le (norm_nonneg _) hC)
  have b2 : ‖A t (y₀ - inclOp z)‖ ≤ C * η :=
    ((A t).le_opNorm _).trans (mul_le_mul (hb t) hz.le (norm_nonneg _) hC)
  have b3 : ‖((A t).comp inclOp - (A t₀).comp inclOp) z‖ ≤ ε / 4 := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖(A t).comp inclOp - (A t₀).comp inclOp‖ * ‖z‖ ≤ ε / (4 * (‖z‖ + 1)) * (‖z‖ + 1) :=
          mul_le_mul h1.le (by linarith) (norm_nonneg _) (by positivity)
      _ = ε / 4 := by field_simp
  have b4 : ‖A t₀ (inclOp z - y₀)‖ ≤ C * η := by
    refine ((A t₀).le_opNorm _).trans (mul_le_mul (hb t₀) ?_ (norm_nonneg _) hC)
    rw [norm_sub_rev]; exact hz.le
  have hCη : C * η < ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [e]
  calc ‖A t (y - y₀) + A t (y₀ - inclOp z) + ((A t).comp inclOp - (A t₀).comp inclOp) z +
        A t₀ (inclOp z - y₀)‖
      ≤ ‖A t (y - y₀)‖ + ‖A t (y₀ - inclOp z)‖ +
          ‖((A t).comp inclOp - (A t₀).comp inclOp) z‖ + ‖A t₀ (inclOp z - y₀)‖ :=
        norm_add₄_le
    _ < ε := by linarith

/-- `‖D^j(t ↦ φ(t) M)‖ ≤ ‖D^jφ‖ ‖M‖`. -/
lemma norm_iteratedFDeriv_smul_const_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (M : c0 →L[ℝ] c0)
    (j : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ j (fun t => φ t • M) t‖ ≤ ‖iteratedFDeriv ℝ j φ t‖ * ‖M‖ := by
  have e : (fun t => φ t • M) =
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) M) ∘ φ := by
    funext t; simp
  rw [e]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hφ.contDiffAt
    (by exact_mod_cast le_top)).trans ?_
  rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖ContinuousLinearMap.id ℝ ℝ‖ * ‖M‖ ≤ 1 * ‖M‖ :=
        mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ = ‖M‖ := one_mul _

lemma K4_nonneg (j : ℕ) : 0 ≤ K4 j := by
  have h := derivBound_bb_sq 0 j 0
  have h9 : (0 : ℝ) < Dk 0 ^ j := by unfold Dk; positivity
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) h9

lemma summable_poly_geom (p : ℕ) : Summable fun k : ℕ => ((k : ℝ) + 3) ^ p * (1 / 2) ^ k := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) p
    (r := 1 / 2) (by rw [Real.norm_eq_abs]; norm_num)
  have h3 := (summable_nat_add_iff 3).2 h
  refine (h3.mul_left 8).congr fun k => ?_
  push_cast
  rw [pow_add]; ring

lemma blk_comp_eq (k : ℕ) (t : ℝ) (m : ℕ) :
    (blk k t m).comp inclOp = (bb k t * bb k t) • (elemL m (nk k) (nk k)).comp inclOp +
      (bb k t * bb (k + 1) t) •
        (elemL m (nk k) (nk (k + 1)) + elemL m (nk (k + 1)) (nk k)).comp inclOp := by
  rw [blk, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.smul_comp]

/-- **One level of loss buys all derivatives**: `t ↦ L(t)_m ∘ ι ∈ L(X_{m+1}, X_m)` is `C^∞`: the
`k`-th block costs `K4_j (k+3)^{2j}` per `j` derivatives and gains `(2 + 2^m) 2^{-k}`. -/
lemma contDiff_fam_comp (m : ℕ) : ContDiff ℝ ∞ fun t => (fam t m).comp inclOp := by
  have e : (fun t => (fam t m).comp inclOp) = fun t => ∑' k, (blk k t m).comp inclOp :=
    funext fun t => fam_comp_eq_tsum t m
  rw [e]
  set M1 : ℕ → c0 →L[ℝ] c0 := fun k => (elemL m (nk k) (nk k)).comp inclOp
  set M2 : ℕ → c0 →L[ℝ] c0 := fun k =>
    (elemL m (nk k) (nk (k + 1)) + elemL m (nk (k + 1)) (nk k)).comp inclOp
  have hM1 : ∀ k, ‖M1 k‖ ≤ (1 / 2) ^ k := fun k =>
    (norm_elemL_comp_inclOp_le _ _ _).trans (by rw [ratio_self, one_pow, one_mul]; exact w_nk_le k)
  have hM2 : ∀ k, ‖M2 k‖ ≤ (1 + 2 ^ m) * (1 / 2) ^ k := fun k => by
    have e2 : M2 k = (elemL m (nk k) (nk (k + 1))).comp inclOp +
        (elemL m (nk (k + 1)) (nk k)).comp inclOp := ContinuousLinearMap.add_comp _ _ _
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    have a1 := (norm_elemL_comp_inclOp_le m (nk k) (nk (k + 1))).trans
      (mul_le_mul (pow_le_one₀ (ratio_nonneg _ _) (ratio_up_le k)) (w_nk_succ_le k)
        (w_pos _).le zero_le_one)
    have a2 := (norm_elemL_comp_inclOp_le m (nk (k + 1)) (nk k)).trans
      (mul_le_mul (pow_le_pow_left₀ (ratio_nonneg _ _) (ratio_down_le k) m) (w_nk_le k)
        (w_pos _).le (by positivity))
    linarith
  have hf : ∀ k, (fun t => (blk k t m).comp inclOp) =
      fun t => (fun t => bb k t * bb k t) t • M1 k + (fun t => bb k t * bb (k + 1) t) t • M2 k :=
    fun k => funext fun t => blk_comp_eq k t m
  have hsq : ∀ k, ContDiff ℝ ∞ fun t => bb k t * bb k t := fun k =>
    (contDiff_bb k).mul (contDiff_bb k)
  have hpr : ∀ k, ContDiff ℝ ∞ fun t => bb k t * bb (k + 1) t := fun k =>
    (contDiff_bb k).mul (contDiff_bb (k + 1))
  refine contDiff_tsum (N := ⊤) (v := fun j k => K4 j * (2 + 2 ^ m) * (Dk k ^ j * (1 / 2) ^ k))
    (fun k => ?_) (fun j _ => ?_) (fun j k t _ => ?_)
  · rw [hf k]; exact ((hsq k).smul contDiff_const).add ((hpr k).smul contDiff_const)
  · have : (fun k : ℕ => Dk k ^ j * (1 / 2 : ℝ) ^ k) =
        fun k : ℕ => ((k : ℝ) + 3) ^ (2 * j) * (1 / 2) ^ k := by
      funext k; unfold Dk; rw [← pow_mul]
    exact ((this ▸ summable_poly_geom (2 * j)).mul_left _)
  · have e3 : (fun t => (blk k t m).comp inclOp) =
        (fun t => (bb k t * bb k t) • M1 k) + (fun t => (bb k t * bb (k + 1) t) • M2 k) := hf k
    have d1 : ContDiff ℝ ∞ fun t => (bb k t * bb k t) • M1 k := (hsq k).smul contDiff_const
    have d2 : ContDiff ℝ ∞ fun t => (bb k t * bb (k + 1) t) • M2 k := (hpr k).smul contDiff_const
    rw [e3, iteratedFDeriv_add_apply (d1.contDiffAt.of_le (by exact_mod_cast le_top))
      (d2.contDiffAt.of_le (by exact_mod_cast le_top))]
    refine (norm_add_le _ _).trans ?_
    have c1 := (norm_iteratedFDeriv_smul_const_le (hsq k) (M1 k) j t).trans
      (mul_le_mul (derivBound_bb_sq k j t) (hM1 k) (norm_nonneg _)
        (mul_nonneg (K4_nonneg j) (by unfold Dk; positivity)))
    have c2 := (norm_iteratedFDeriv_smul_const_le (hpr k) (M2 k) j t).trans
      (mul_le_mul (derivBound_bb_mul k j t) (hM2 k) (norm_nonneg _)
        (mul_nonneg (K4_nonneg j) (by unfold Dk; positivity)))
    have : K4 j * Dk k ^ j * (1 / 2) ^ k + K4 j * Dk k ^ j * ((1 + 2 ^ m) * (1 / 2) ^ k) =
        K4 j * (2 + 2 ^ m) * (Dk k ^ j * (1 / 2) ^ k) := by ring
    linarith

/-- **The family is a loss family** (`IsLossFamily`) on `ℝ ⊕ X`. -/
theorem isLossFamily_fam : IsLossFamily (V := ℝ) (Z := X) (W := X) fam where
  toBase t m y := toBase_fam t m y
  continuous m := continuous_apply_of_bound (fun t => fam t m) (3 + 2 ^ m)
    (fun t => norm_fam_le t m) (contDiff_fam_comp m).continuous
  contDiff m := contDiff_fam_comp m

/-! ### Projections, smooth ranges, and the discontinuous lift -/

lemma cc_sq_add_ss_sq (k : ℕ) (t : ℝ) : cc k t ^ 2 + ss k t ^ 2 = 1 := cf_sq_add_sf_sq _

/-- **Every `L(t)₀` is a projection.** -/
theorem fam_idem (t : ℝ) (y : c0) : fam t 0 (fam t 0 y) = fam t 0 y := by
  rcases le_or_gt t 0 with ht | ht
  · rw [fam_of_nonpos ht]; rfl
  · ext i
    have hne := nk_ne (kt t)
    have h1 := cc_sq_add_ss_sq (kt t) t
    rw [fam_zero_apply_of_pos ht (fam t 0 y) i, fam_zero_apply_of_pos ht y (nk (kt t)),
      fam_zero_apply_of_pos ht y (nk (kt t + 1)), fam_zero_apply_of_pos ht y i]
    simp only [if_true, if_neg hne.symm]
    split_ifs
    · linear_combination (cc (kt t) t * (cc (kt t) t * y (nk (kt t)) +
        ss (kt t) t * y (nk (kt t + 1)))) * h1
    · linear_combination (ss (kt t) t * (cc (kt t) t * y (nk (kt t)) +
        ss (kt t) t * y (nk (kt t + 1)))) * h1
    · rfl

/-- **The ranges of the `L(t)₀` are smooth points** (finitely supported sequences). -/
theorem fam_mem_smooth (t : ℝ) (y : c0) : fam t 0 y ∈ X.smooth := by
  rcases le_or_gt t 0 with ht | ht
  · rw [fam_of_nonpos ht]; exact X.smooth.zero_mem
  · have := mem_smoothLvl_of_finSupp (m := 0) (fam t 0 y) (n := nk (kt t + 1) + 1) fun i hi => by
      have hlt := nk_lt (kt t)
      rw [fam_zero_apply_of_pos ht, if_neg (by omega), if_neg (by omega)]
    exact this

/-- The active block at the node `1/(k+1)` is `k`. -/
lemma kt_node (k : ℕ) : kt (node k) = k := by
  have : (node k)⁻¹ = ((k + 1 : ℕ) : ℝ) := by unfold node; push_cast; rw [one_div, inv_inv]
  rw [kt, this, Nat.floor_natCast]; rfl

/-- At the node `1/(k+1)` the projection is onto `e_{n_k}`. -/
lemma fam_node_smul_δv (k : ℕ) (r : ℝ) : fam (node k) 0 (r • δv (nk k)) = r • δv (nk k) := by
  ext i
  have hc : cc k (node k) = 1 := cc_of_le le_rfl
  have hs : ss k (node k) = 0 := ss_of_le le_rfl
  rw [fam_zero_apply_of_pos (node_pos k), kt_node, hc, hs]
  have hne := nk_ne k
  simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, δv_apply]
  split_ifs <;> simp_all

/-- The points `o_k = (1/(k+1), (1/(k+1)) e_{n_k})` of `ℝ ⊕ X` (level `0`). -/
def pt (k : ℕ) : ((ScBanach.const ℝ).prod X) 0 := (node k, node k • δv (nk k))

/-- Their level-`1` coordinates: `(1/(k+1), ((n_k + 1)/(k+1)) e_{n_k})`. -/
def ptOne (k : ℕ) : ((ScBanach.const ℝ).prod X) 1 :=
  (node k, (((nk k : ℝ) + 1) * node k) • δv (nk k))

lemma toBase_ptOne (k : ℕ) : ((ScBanach.const ℝ).prod X).toBase 1 (ptOne k) = pt k := by
  rw [toBase_constProd]
  refine Prod.ext rfl ?_
  ext i
  change X.toBase 1 ((((nk k : ℝ) + 1) * node k) • δv (nk k)) i = (node k • δv (nk k)) i
  rw [X_toBase_apply]
  simp only [pow_one, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, δv_apply]
  split_ifs with h
  · subst h; unfold w; field_simp
  · simp

/-- **The lift `O → E₁` is discontinuous at `0`**: `o_k → 0` in `E₀` but `|o_k|₁ ≥ 1`. -/
theorem not_continuousOn_liftOne :
    ¬ ContinuousOn ((ScBanach.const ℝ).prod X).liftOne
      (isLossFamily_fam.retraction fun t y => fam_idem t y).retract := by
  intro hcont
  set R := isLossFamily_fam.retraction fun t y => fam_idem t y
  have hmem : ∀ k, pt k ∈ R.retract := fun k =>
    ⟨pt k, mem_univ _, Prod.ext rfl (fam_node_smul_δv k (node k))⟩
  have h0 : (0 : ((ScBanach.const ℝ).prod X) 0) ∈ R.retract :=
    ⟨0, mem_univ _, Prod.ext rfl (map_zero (fam 0 0))⟩
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpt : Tendsto pt atTop (𝓝 0) := by
    refine (hnode.prodMk_nhds ?_)
    refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => ?_) hnode)
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (node_pos k)]
    exact mul_le_of_le_one_right (node_pos k).le (norm_δv_le _)
  have hlim := (hcont 0 h0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpt, Eventually.of_forall hmem⟩)
  have hl0 : ((ScBanach.const ℝ).prod X).liftOne 0 = 0 := by
    have := ((ScBanach.const ℝ).prod X).liftOne_toBase 0
    rwa [map_zero] at this
  rw [hl0] at hlim
  have hlk : ∀ k, ((ScBanach.const ℝ).prod X).liftOne (pt k) = ptOne k := fun k => by
    rw [← toBase_ptOne, ScBanach.liftOne_toBase]
  have h2 : Tendsto (fun k => (ptOne k).2) atTop (𝓝 0) := by
    have := (continuous_snd.tendsto _).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, hlk]
  have h3 := (tendsto_zero_iff_norm_tendsto_zero.1 h2).eventually (gt_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := h3.exists
  have hge : 1 ≤ ‖(ptOne k).2‖ := by
    refine le_trans ?_ (abs_apply_le_norm _ (nk k))
    change 1 ≤ |(((nk k : ℝ) + 1) * node k) * (if nk k = nk k then 1 else 0)|
    rw [if_pos rfl, mul_one, abs_of_pos (by have := node_pos k; positivity)]
    unfold node nk
    rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
    have : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
    push_cast; linarith
  exact absurd hk (not_lt.2 hge)

/-- **Remark 4.3's data, machine-checked**: the moving rank-one projections `L(t)` on the weighted
sequence space `X` of `ScOneNotNormContinuous.lean` form a loss family of projections with smooth
ranges whose retract has a discontinuous lift into level `1`. -/
theorem remarkFourThreeData : RemarkFourThreeData ℝ X :=
  ⟨fam, isLossFamily_fam, fun t y => fam_idem t y, fun t y => fam_mem_smooth t y,
    not_continuousOn_liftOne⟩

end RemarkFourThree

/-- **Remark 4.3: "`X¹ ≠ X` is possible"** (§4.1, p. 148; comparison item V4.6, gap G.31), at the
level of retracts: there is an sc-retract `O = r(ℝ ⊕ X)` (the moving rank-one projections of
`RemarkFourThree.fam` on the weighted sequence space `X`) all of whose points are smooth,
`O = O_∞`, which is not an sc⁺-retract, i.e. `1₀¹ : O → O¹` is not sc-smooth
(Proposition 4.8). -/
theorem remark_4_3_retract_example :
    ∃ (E : ScBanach) (O : Set (E 0)), IsScRetract E univ O ∧ O ⊆ E.smooth ∧
      ¬ IsScPlusRetract E univ O :=
  exists_retract_smooth_not_scPlus_of_data RemarkFourThree.remarkFourThreeData

/-! ### The M-polyfold of a retract, and Remark 4.3 for M-polyfolds -/

section RetractPolyfold

variable {E : ScBanach} {C O : Set (E 0)}

open scoped Classical in
/-- The single chart `O → O ⊆ E` of a retract `O` (with a junk value `o₀` off `O`). -/
def retractChart (hO : IsScRetract E C O) (o₀ : O) : MChart O where
  model := ⟨E, C, O, hO⟩
  toPartialEquiv :=
    { toFun := Subtype.val
      invFun := fun x => if h : x ∈ O then ⟨x, h⟩ else o₀
      source := univ
      target := O
      map_source' := fun x _ => x.2
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun x _ => by simp [x.2]
      right_inv' := fun x hx => by simp [hx] }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have e : O.domRestrict (fun x => if h : x ∈ O then (⟨x, h⟩ : O) else o₀) = fun x => x := by
      funext x; change (if h : (x : E 0) ∈ O then (⟨x, h⟩ : O) else o₀) = x; rw [dif_pos x.2]
    change Continuous (O.domRestrict (fun x => if h : x ∈ O then (⟨x, h⟩ : O) else o₀))
    rw [e]; exact continuous_id

/-- **The M-polyfold of a retract** `O` (Definition 2.13): `O` with the single chart `O → O`. -/
def retractPolyfold (hO : IsScRetract E C O) (o₀ : O) : MPolyfold O where
  atlas :=
    { charts := {retractChart hO o₀}
      compatible := fun φ hφ ψ hψ => by
        rw [mem_singleton_iff.1 hφ, mem_singleton_iff.1 hψ]; exact MChart.compatible_self _
      cover := fun _ => ⟨retractChart hO o₀, mem_singleton _, mem_univ _⟩ }

lemma isChart_retractChart (hO : IsScRetract E C O) (o₀ : O) :
    (retractPolyfold hO o₀).IsChart (retractChart hO o₀) :=
  (retractPolyfold hO o₀).isChart_of_mem (mem_singleton _)

/-- **Remark 4.3 for the M-polyfold of a retract**: if `O ⊆ E_∞` is not an sc⁺-retract, the
M-polyfold `X = O` has `X₀ = X_∞` but `1₀¹ : X → X¹` is not sc-smooth. -/
theorem retractPolyfold_smooth_not_toLevelOne (hO : IsScRetract E C O) (o₀ : O)
    (hsm : O ⊆ E.smooth) (hnot : ¬ IsScPlusRetract E C O) :
    (∀ x, x ∈ (retractPolyfold hO o₀).smoothSet) ∧
      ∀ x₀ : (retractPolyfold hO o₀).Level 1,
        ¬ (retractPolyfold hO o₀).IsScSmoothMap (retractPolyfold hO o₀).shift
          ((retractPolyfold hO o₀).toLevelOne x₀) := by
  have hall : ∀ x, x ∈ (retractPolyfold hO o₀).smoothSet := fun x =>
    (MPolyfold.mem_smoothSet_iff (isChart_retractChart hO o₀) (mem_univ x)).2 (hsm x.2)
  refine ⟨hall, fun x₀ hmap => hnot ?_⟩
  exact (MPolyfold.isScSmoothMap_toLevelOne_iff x₀).1 ⟨hall, hmap⟩ _ (isChart_retractChart hO o₀)

end RetractPolyfold

/-- **Remark 4.3: "`X¹ ≠ X` is possible although the underlying sets agree"** (§4.1, p. 148;
comparison item V4.6, gap G.31), machine-checked: there is an M-polyfold `X` (a retract
`O ⊆ ℝ ⊕ X` of the moving rank-one projections `RemarkFourThree.fam`, with one chart) with
`X₀ = X_∞` (every point smooth) for which `1₀¹ : X → X¹` is not sc-smooth; so `X¹ ≠ X` as
M-polyfolds (`remark_4_3_isScDiffeo`: `1₀¹` would otherwise be an sc-diffeomorphism). -/
theorem remark_4_3_example :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : ParacompactSpace Y)
      (P : MPolyfold Y), (∀ x, x ∈ P.smoothSet) ∧
        ∀ x₀ : P.Level 1, ¬ P.IsScSmoothMap P.shift (P.toLevelOne x₀) := by
  obtain ⟨L, h, hidem, hsm, hdisc⟩ := RemarkFourThree.remarkFourThreeData
  have h0 : (0 : ((ScBanach.const ℝ).prod ScOneExample.X) 0) ∈ (h.retraction hidem).retract :=
    ⟨0, mem_univ _, Prod.ext rfl (map_zero (L 0 0))⟩
  exact ⟨_, _, _, _, retractPolyfold (h.retraction hidem).isScRetract ⟨0, h0⟩,
    retractPolyfold_smooth_not_toLevelOne _ _ (h.retract_subset_smooth hidem hsm)
      (h.not_isScPlusRetract hidem hdisc)⟩

end Polyfold
