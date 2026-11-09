import Polyfold.Chapter1.ScSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1, the remark
after Definition 1.1.15 (preprint 1.14).

# An sc¹ map whose derivative is not continuous in the operator norm

## The text, paraphrased

After Definition 1.1.15 (preprint 1.14) (sc¹ maps): "In general `x ↦ Df(x)` is not continuous into `L(E₀, F₀)`
equipped with the operator norm, but it is continuous with the compact-open topology."  The text
gives no example.

## What is formalized

* `Polyfold.ScOneExample.c0 = C₀(ℕ, ℝ)` (real sequences tending to `0`, sup norm), the diagonal
  operators `diag c` for bounded multipliers `c : ℕ → ℝ`, and the **weighted sequence sc-Banach
  space** `Polyfold.ScOneExample.X`: every level is `c₀`, read as the coordinates
  `y_k = (k+1)^m x_k` of a sequence `x` with `|x|_m = sup_k (k+1)^m |x_k|`, so that the inclusion
  `X_{m+1} → X_m` is the diagonal operator `y ↦ (y_k / (k+1))_k`; it is compact (a norm limit of
  finite-rank truncations) and injective, and the finitely supported sequences are smooth points
  dense in every level.  The project had no infinite-dimensional sc-Banach space before.
* The map `f : ℝ ⊕ X → X`, `f(t, x)_k = cos(k t) x_k` (`ScOneExample.f`), on `E = ℝ ⊕ X`
  (`ScBanach.const ℝ` times `X`, `U = C = E₀`), with derivative
  `Df(t, x)(τ, ξ)_k = −k sin(k t) x_k τ + cos(k t) ξ_k` at `(t, x) ∈ E₁` (`ScOneExample.D`).
  `ScOneExample.isSc1With`: `f` is sc¹ with this derivative (Definition 1.1.15 (preprint 1.14): sc⁰, the
  differentiability of `f : E₁ → F₀`, and `Tf` sc⁰).  Every level map is "the same formula",
  because diagonal operators commute with the weights.
* `ScOneExample.not_continuousAt_deriv`: `x ↦ Df(x) ∈ L(E₀, F₀)` is not continuous at `0 ∈ E₁`
  for the operator norm: `‖Df(π/(n+1), 0) − Df(0, 0)‖ ≥ 2` (test with the unit vector
  `e_{n+1}`).  `ScOneExample.not_continuousOn_of_isSc1With`: the same for **every** derivative
  family of `f` (the derivative is unique on `E₁`).
* `exists_isSc1_not_continuousOn_deriv` (**the remark after Definition 1.1.15 (preprint 1.14)**): there are
  sc-Banach spaces `E, F`, a relatively open `U` in a partial quadrant `C ⊆ E` and an sc¹ map
  `f : U → F` such that for every derivative family `D` of `f`, `x ↦ D x` is not continuous on
  `U₁` into `L(E₀, F₀)` with the operator norm (round-trip items V1.13, V1.34).

## What the text leaves implicit / choices

* The levels are `c₀` with weights `(k+1)^m` rather than the text's typical weighted `L²`/Sobolev
  spaces: the sup norm makes the estimates pointwise, and the inclusion `c₀ → c₀` by
  `diag(1/(k+1))` is compact.  `ℓ²` with the same weights would work the same way.
* The mechanism is the one behind Remark 1.1.16, in miniature: the
  `t`-derivative of `cos(k t) x_k` costs a factor `k`, absorbed by one level (`x ∈ E₁`), while
  `Df(t, 0) = diag(cos(k t))` on level `0` moves by `sup_k |cos(k t) − cos(k s)| ≥ 1` for
  `t ≠ s` arbitrarily close.  The continuity in the compact-open topology is the project's
  general `IsSc1With.continuousOn_deriv` / `IsSc1With.deriv_uniformOnCompact`.
* Only sc¹ is proved; `f` is in fact sc-smooth (all derivatives are diagonal operators of the
  same kind), which is not formalized here.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

namespace ScOneExample

/-! ### The sequence space `c₀` and diagonal operators -/

/-- `c₀ = C₀(ℕ, ℝ)`: real sequences tending to `0`, with the sup norm. -/
abbrev c0 : Type := ZeroAtInftyContinuousMap ℕ ℝ

/-- A sequence tending to `0` as an element of `c₀`. -/
def mkC0 (g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0)) : c0 :=
  ⟨⟨g, continuous_of_discreteTopology⟩, cocompact_eq_atTop (α := ℕ) ▸ hg⟩

@[simp] lemma mkC0_apply (g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0)) (k : ℕ) : mkC0 g hg k = g k :=
  rfl

/-- An element of `c₀` tends to `0`. -/
lemma tendsto_c0 (y : c0) : Tendsto (fun k => y k) atTop (𝓝 0) := by
  have := y.zero_at_infty'
  rwa [cocompact_eq_atTop] at this

/-- `|y_k| ≤ ‖y‖` in `c₀`. -/
lemma abs_apply_le_norm (y : c0) (k : ℕ) : |y k| ≤ ‖y‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact y.toBCF.norm_coe_le_norm k

/-- The sup norm of `c₀` is bounded by a pointwise bound. -/
lemma norm_le_of_forall {y : c0} {C : ℝ} (hC : 0 ≤ C) (h : ∀ k, |y k| ≤ C) : ‖y‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 fun k => by rw [Real.norm_eq_abs]; exact h k

/-- The tail of an element of `c₀` is small. -/
lemma eventually_abs_lt (y : c0) {ε : ℝ} (hε : 0 < ε) : ∃ K, ∀ k, K ≤ k → |y k| < ε := by
  have := (tendsto_c0 y).eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 this
  exact ⟨K, fun k hk => by simpa [Real.dist_eq] using hK k hk⟩

/-- **Uniform smallness of bounded multipliers tending to `0` pointwise**: if `|c s k| ≤ B` and
`c s k → 0` along `l` for every `k`, then `sup_k |c s k · y k| → 0` along `l` for `y ∈ c₀`. -/
lemma eventually_forall_abs_mul_le {ι : Type*} {l : Filter ι} {c : ι → ℕ → ℝ} {B : ℝ}
    (hB : ∀ s k, |c s k| ≤ B) (hc : ∀ k, Tendsto (fun s => c s k) l (𝓝 0)) (y : c0) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ s in l, ∀ k, |c s k * y k| ≤ ε := by
  set B' := |B| + 1 with hB'
  have hB'0 : 0 < B' := by positivity
  obtain ⟨K, hK⟩ := eventually_abs_lt y (div_pos hε hB'0)
  have hfin : ∀ᶠ s in l, ∀ k ∈ Finset.range K, |c s k| ≤ ε / (‖y‖ + 1) := by
    refine (Filter.eventually_all_finset _).2 fun k _ => ?_
    have := (hc k).eventually (Metric.closedBall_mem_nhds 0 (by positivity : 0 < ε / (‖y‖ + 1)))
    exact this.mono fun s hs => by simpa [Real.dist_eq] using hs
  refine hfin.mono fun s hs k => ?_
  rw [abs_mul]
  rcases lt_or_ge k K with hk | hk
  · have h1 := hs k (Finset.mem_range.2 hk)
    calc |c s k| * |y k| ≤ ε / (‖y‖ + 1) * ‖y‖ :=
          mul_le_mul h1 (abs_apply_le_norm y k) (abs_nonneg _) (by positivity)
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg y]
  · have h1 : |c s k| ≤ B' := (hB s k).trans (by rw [hB']; linarith [le_abs_self B])
    calc |c s k| * |y k| ≤ B' * (ε / B') :=
          mul_le_mul h1 (hK k hk).le (abs_nonneg _) hB'0.le
      _ = ε := by field_simp

/-- The diagonal operator `y ↦ (c_k y_k)_k` on `c₀` for a bounded multiplier `|c_k| ≤ B`. -/
def diag (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) : c0 →L[ℝ] c0 :=
  LinearMap.mkContinuous
    { toFun := fun y => mkC0 (fun k => c k * y k) (by
        refine squeeze_zero_norm (a := fun k => |B| * |y k|) (fun k => ?_) ?_
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right ((hc k).trans (le_abs_self B)) (abs_nonneg _)
        · simpa using ((tendsto_c0 y).abs.const_mul |B|))
      map_add' := fun y z => by ext k; simp [mul_add]
      map_smul' := fun r y => by ext k; simp; ring }
    |B| (fun y => by
      refine norm_le_of_forall (by positivity) fun k => ?_
      change |c k * y k| ≤ |B| * ‖y‖
      rw [abs_mul]
      exact mul_le_mul ((hc k).trans (le_abs_self B)) (abs_apply_le_norm y k) (abs_nonneg _)
        (abs_nonneg _))

@[simp] lemma diag_apply (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) (y : c0) (k : ℕ) :
    diag c hc y k = c k * y k := rfl

/-- `‖diag c‖ ≤ |B|` for `|c_k| ≤ B`. -/
lemma norm_diag_le (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) : ‖diag c hc‖ ≤ |B| :=
  LinearMap.mkContinuous_norm_le _ (abs_nonneg B) _

/-- **Continuity of a continuous family of diagonal operators**: if `|c s k| ≤ B` and every
`s ↦ c s k` is continuous, then `(s, y) ↦ diag (c s) y` is continuous on `ℝ × c₀` (strong
continuity, from `eventually_forall_abs_mul_le`). -/
lemma continuous_diag_family (c : ℝ → ℕ → ℝ) {B : ℝ} (hc : ∀ s k, |c s k| ≤ B)
    (hcont : ∀ k, Continuous fun s => c s k) :
    Continuous fun p : ℝ × c0 => diag (c p.1) (hc p.1) p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, y⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ s in 𝓝 t, ∀ k, |(c s k - c t k) * y k| ≤ ε / 4 := by
    refine eventually_forall_abs_mul_le (B := 2 * |B|) (fun s k => ?_) (fun k => ?_) y
      (by positivity)
    · calc |c s k - c t k| ≤ |c s k| + |c t k| := abs_sub _ _
        _ ≤ 2 * |B| := by linarith [(hc s k).trans (le_abs_self B), (hc t k).trans (le_abs_self B)]
    · have := ((hcont k).tendsto t).sub_const (c t k)
      simpa using this
  have h2 : ∀ᶠ p in 𝓝 ((t, y) : ℝ × c0), ‖p.2 - y‖ < ε / (2 * (|B| + 1)) := by
    have hc : Continuous fun p : ℝ × c0 => ‖p.2 - y‖ :=
      (continuous_snd.sub (continuous_const (y := y))).norm
    have : Tendsto (fun p : ℝ × c0 => ‖p.2 - y‖) (𝓝 (t, y)) (𝓝 0) := by
      simpa using hc.tendsto ((t, y) : ℝ × c0)
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [(continuous_fst.tendsto ((t, y) : ℝ × c0)).eventually h1, h2] with p hp1 hp2
  rw [dist_eq_norm]
  have e : diag (c p.1) (hc p.1) p.2 - diag (c t) (hc t) y =
      diag (c p.1) (hc p.1) (p.2 - y) + mkC0 (fun k => (c p.1 k - c t k) * y k) (by
        refine squeeze_zero_norm (a := fun k => 2 * |B| * |y k|) (fun k => ?_) ?_
        · rw [Real.norm_eq_abs, abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          calc |c p.1 k - c t k| ≤ |c p.1 k| + |c t k| := abs_sub _ _
            _ ≤ 2 * |B| := by
              linarith [(hc p.1 k).trans (le_abs_self B), (hc t k).trans (le_abs_self B)]
        · simpa using ((tendsto_c0 y).abs.const_mul (2 * |B|))) := by
    ext k; simp; ring
  rw [e]
  calc ‖diag (c p.1) (hc p.1) (p.2 - y) + mkC0 _ _‖
      ≤ ‖diag (c p.1) (hc p.1) (p.2 - y)‖ + ‖mkC0 (fun k => (c p.1 k - c t k) * y k) _‖ :=
        norm_add_le _ _
    _ ≤ |B| * ‖p.2 - y‖ + ε / 4 := by
        gcongr
        · exact ((diag (c p.1) (hc p.1)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (norm_diag_le _ _) (norm_nonneg _))
        · exact norm_le_of_forall (by positivity) hp1
    _ ≤ (|B| + 1) * (ε / (2 * (|B| + 1))) + ε / 4 := by
        gcongr
        linarith
    _ < ε := by
        have : (|B| + 1) * (ε / (2 * (|B| + 1))) = ε / 2 := by field_simp
        rw [this]; linarith

/-! ### The weighted sequence sc-Banach space `X` -/

/-- The weights `w_k = 1/(k+1)`. -/
def w (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- The weights are positive. -/
lemma w_pos (k : ℕ) : 0 < w k := by unfold w; positivity

/-- The weights are at most `1`. -/
lemma abs_w_le (k : ℕ) : |w k| ≤ 1 := by
  rw [abs_of_pos (w_pos k)]
  unfold w
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- `k w_k ≤ 1`: one level absorbs one factor `k`. -/
lemma natCast_mul_w_le (k : ℕ) : (k : ℝ) * w k ≤ 1 := by
  unfold w
  rw [mul_one_div, div_le_one (by positivity)]
  linarith

/-- The inclusion `X_{m+1} → X_m`: `y ↦ (y_k / (k+1))_k`. -/
def inclOp : c0 →L[ℝ] c0 := diag w abs_w_le

/-- The inclusion `X_{m+1} → X_m` is injective. -/
lemma inclOp_injective : Function.Injective inclOp := by
  intro y z h
  ext k
  have := congrArg (fun u : c0 => u k) h
  simp only [inclOp, diag_apply] at this
  exact mul_left_cancel₀ (w_pos k).ne' this

/-- The truncated weights `w_k 1_{k < n}`. -/
def wTrunc (n k : ℕ) : ℝ := if k < n then w k else 0

/-- The truncated weights are at most `1`. -/
lemma abs_wTrunc_le (n k : ℕ) : |wTrunc n k| ≤ 1 := by
  unfold wTrunc; split_ifs
  · exact abs_w_le k
  · simp

/-- The truncation `diag (w 1_{<n})` has finite rank: it factors through `Fin n → ℝ`. -/
lemma isCompactOperator_diag_wTrunc (n : ℕ) :
    IsCompactOperator (diag (wTrunc n) (abs_wTrunc_le n)) := by
  let P : c0 →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi fun i =>
    LinearMap.mkContinuous
      { toFun := fun y : c0 => y i
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } 1 (fun y => by
          rw [one_mul, Real.norm_eq_abs]; exact abs_apply_le_norm y i)
  let J₀ : (Fin n → ℝ) →ₗ[ℝ] c0 :=
    { toFun := fun v => mkC0 (fun k => if h : k < n then w k * v ⟨k, h⟩ else 0) (by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with k hk
        rw [dif_neg (by omega)])
      map_add' := fun v v' => by
        ext k; simp only [mkC0_apply, ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
        split_ifs <;> simp [mul_add]
      map_smul' := fun r v => by
        ext k; simp only [mkC0_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp [mul_left_comm] }
  let J : (Fin n → ℝ) →L[ℝ] c0 := LinearMap.toContinuousLinearMap J₀
  have hP : IsCompactOperator P := isCompactOperator_of_locallyCompactSpace_dom P
  have hJP : diag (wTrunc n) (abs_wTrunc_le n) = J.comp P := by
    ext y k
    change wTrunc n k * y k = if h : k < n then w k * y k else 0
    unfold wTrunc
    split_ifs <;> simp
  rw [hJP]
  exact hP.clm_comp J

/-- The truncations converge to the inclusion in operator norm:
`‖diag(w 1_{<n}) − diag w‖ ≤ 1/(n+1)`. -/
lemma tendsto_diag_wTrunc :
    Tendsto (fun n => diag (wTrunc n) (abs_wTrunc_le n)) atTop (𝓝 inclOp) := by
  refine (tendsto_iff_norm_sub_tendsto_zero (f := fun n => diag (wTrunc n) (abs_wTrunc_le n))
    (b := inclOp)).2 ?_
  refine squeeze_zero (fun n => norm_nonneg (diag (wTrunc n) (abs_wTrunc_le n) - inclOp))
    (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  refine norm_le_of_forall (by positivity) fun k => ?_
  change |wTrunc n k * y k - w k * y k| ≤ 1 / ((n : ℝ) + 1) * ‖y‖
  unfold wTrunc
  split_ifs with hk
  · rw [sub_self, abs_zero]; positivity
  · rw [zero_mul, zero_sub, abs_neg, abs_mul, abs_of_pos (w_pos k)]
    refine mul_le_mul ?_ (abs_apply_le_norm y k) (abs_nonneg _) (by positivity)
    unfold w
    gcongr
    exact_mod_cast not_lt.1 hk

/-- The inclusion `X_{m+1} → X_m` is compact (a norm limit of finite-rank operators). -/
lemma inclOp_isCompactOperator : IsCompactOperator inclOp :=
  isCompactOperator_of_tendsto tendsto_diag_wTrunc
    (Eventually.of_forall isCompactOperator_diag_wTrunc)

/-- The scale `X_m = c₀` (coordinates `y_k = (k+1)^m x_k`) with inclusions `inclOp`. -/
abbrev XScale : ScScale where
  lvl _ := c0
  incl _ := inclOp
  incl_injective _ := inclOp_injective
  incl_isCompactOperator _ := inclOp_isCompactOperator

/-- The inclusion `X_m → X₀` is `y ↦ (w_k^m y_k)_k`. -/
lemma XScale_toBase_apply : ∀ (m : ℕ) (y : XScale m) (k : ℕ),
    XScale.toBase m y k = w k ^ m * (y : c0) k
  | 0, y, k => by rw [pow_zero, one_mul]; rfl
  | m + 1, y, k => by
    rw [ScScale.toBase_succ, XScale_toBase_apply m]
    change w k ^ m * (w k * (y : c0) k) = _
    ring

/-- Finitely supported sequences are smooth points of every level. -/
lemma mem_smoothLvl_of_finSupp {m : ℕ} (y : XScale m) {n : ℕ} (hy : ∀ k, n ≤ k → (y : c0) k = 0) :
    y ∈ XScale.smoothLvl m := by
  refine (XScale.mem_smoothLvl_iff).2 fun j => ?_
  refine ⟨mkC0 (fun k => if k < n then ((k : ℝ) + 1) ^ j * (w k ^ m * (y : c0) k) else 0) (by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [if_neg (by omega)]), ?_⟩
  ext k
  rw [XScale_toBase_apply, XScale_toBase_apply]
  change w k ^ j * (if k < n then ((k : ℝ) + 1) ^ j * (w k ^ m * (y : c0) k) else 0) = _
  split_ifs with hk
  · rw [← mul_assoc, ← mul_pow]
    have : w k * ((k : ℝ) + 1) = 1 := by unfold w; field_simp
    rw [this, one_pow, one_mul]
  · rw [hy k (not_lt.1 hk)]; simp

/-- **The weighted sequence sc-Banach space** `X`: `|x|_m = sup_k (k+1)^m |x_k|`, `x_k → 0`
weighted, represented on every level by the coordinates `(k+1)^m x_k ∈ c₀`. -/
abbrev X : ScBanach where
  toScScale := XScale
  dense_smooth m := by
    rw [Metric.dense_iff]
    intro y r hr
    obtain ⟨K, hK⟩ := eventually_abs_lt (y : c0) (half_pos hr)
    let z : c0 := mkC0 (fun k => if k < K then (y : c0) k else 0) (by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      rw [if_neg (by omega)])
    refine ⟨z, ?_, mem_smoothLvl_of_finSupp (m := m) z (n := K) fun k hk => ?_⟩
    · rw [Metric.mem_ball, dist_comm, dist_eq_norm]
      refine (norm_le_of_forall (half_pos hr).le fun k => ?_).trans_lt (half_lt_self hr)
      change |(y : c0) k - (if k < K then (y : c0) k else 0)| ≤ r / 2
      split_ifs with hk
      · rw [sub_self, abs_zero]; positivity
      · rw [sub_zero]; exact (hK k (not_lt.1 hk)).le
    · change (if k < K then (y : c0) k else 0) = 0
      rw [if_neg (by omega)]

/-- The inclusion `X_m → X₀` is `y ↦ (w_k^m y_k)_k`. -/
lemma X_toBase_apply (m : ℕ) (y : X m) (k : ℕ) : X.toBase m y k = w k ^ m * (y : c0) k :=
  XScale_toBase_apply m y k

/-- The inclusion `(X¹)_m = X_{m+1} → X₁` is `y ↦ (w_k^m y_k)_k`. -/
lemma X_shift_toBase_apply : ∀ (m : ℕ) (y : X.shift m) (k : ℕ),
    X.shift.toBase m y k = w k ^ m * (y : c0) k
  | 0, y, k => by rw [pow_zero, one_mul]; rfl
  | m + 1, y, k => by
    rw [ScScale.toBase_succ, X_shift_toBase_apply m]
    change w k ^ m * (w k * (y : c0) k) = _
    ring

/-- `X_shift_toBase_apply`, stated for the underlying scale (as it appears after unfolding). -/
lemma shiftScale_XScale_toBase_apply (m : ℕ) (y : X.shift m) (k : ℕ) :
    (ScBanach.shiftScale XScale).toBase m y k = w k ^ m * (y : c0) k :=
  X_shift_toBase_apply m y k

/-- Diagonal operators commute with the inclusions `X_m → X₀`. -/
lemma X_toBase_diag (m : ℕ) (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) (y : X m) :
    X.toBase m (diag c hc y) = diag c hc (X.toBase m y) := by
  ext k
  rw [X_toBase_apply, diag_apply, diag_apply, X_toBase_apply]
  ring

/-- Diagonal operators commute with the inclusions `(X¹)_m → X₁`. -/
lemma X_shift_toBase_diag (m : ℕ) (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) (y : X.shift m) :
    X.shift.toBase m (diag c hc y) = diag c hc (X.shift.toBase m y) := by
  ext k
  rw [X_shift_toBase_apply, diag_apply, diag_apply, X_shift_toBase_apply]
  ring

/-! ### The map `f(t, x)_k = cos(k t) x_k` on `ℝ ⊕ X` -/

/-- The multiplier `cos(k t)`. -/
def cosMul (t : ℝ) (k : ℕ) : ℝ := Real.cos ((k : ℝ) * t)

/-- `|cos(k t)| ≤ 1`. -/
lemma abs_cosMul_le (t : ℝ) (k : ℕ) : |cosMul t k| ≤ 1 := Real.abs_cos_le_one _

/-- The multiplier `−k w_k sin(k t)`: the `t`-derivative of `cos(k t)`, in level-`1` coordinates. -/
def sinMul (t : ℝ) (k : ℕ) : ℝ := -((k : ℝ) * w k) * Real.sin ((k : ℝ) * t)

/-- `|k w_k sin(k t)| ≤ 1`. -/
lemma abs_sinMul_le (t : ℝ) (k : ℕ) : |sinMul t k| ≤ 1 := by
  unfold sinMul
  rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (w_pos k).le)]
  calc (k : ℝ) * w k * |Real.sin ((k : ℝ) * t)| ≤ 1 * 1 :=
        mul_le_mul (natCast_mul_w_le k) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- `x ↦ (cos(k t) x_k)_k`. -/
def cosOp (t : ℝ) : c0 →L[ℝ] c0 := diag (cosMul t) (abs_cosMul_le t)

/-- `y ↦ (−k w_k sin(k t) y_k)_k`. -/
def sinOp (t : ℝ) : c0 →L[ℝ] c0 := diag (sinMul t) (abs_sinMul_le t)

/-- `(t, y) ↦ (cos(k t) y_k)_k` is continuous on `ℝ × c₀`. -/
lemma continuous_cosOp : Continuous fun p : ℝ × c0 => cosOp p.1 p.2 :=
  continuous_diag_family cosMul abs_cosMul_le fun k => by
    unfold cosMul; fun_prop

/-- `(t, y) ↦ (−k w_k sin(k t) y_k)_k` is continuous on `ℝ × c₀`. -/
lemma continuous_sinOp : Continuous fun p : ℝ × c0 => sinOp p.1 p.2 :=
  continuous_diag_family sinMul abs_sinMul_le fun k => by
    unfold sinMul; fun_prop

/-- The domain `E = ℝ ⊕ X`. -/
abbrev E : ScBanach := (ScBanach.const ℝ).prod X

/-- **The example**: `f(t, x)_k = cos(k t) x_k`, `f : ℝ ⊕ X → X`. -/
def f : E 0 → X 0 := fun p => cosOp p.1 p.2

/-- The derivative `Df(t, x)(τ, ξ) = τ (−k sin(k t) x_k)_k + (cos(k t) ξ_k)_k` at `(t, x) ∈ E₁`
(`x` given by its level-`1` coordinates `y_k = (k+1) x_k`, so
`−k sin(k t) x_k = sinMul t k · y_k`). -/
def D : E 1 → E 0 →L[ℝ] X 0 := fun p =>
  (ContinuousLinearMap.fst ℝ ℝ c0).smulRight (sinOp p.1 p.2) +
    (cosOp p.1).comp (ContinuousLinearMap.snd ℝ ℝ c0)

/-- `Df(t, y)(τ, ξ) = τ (sinMul t k y_k)_k + (cos(k t) ξ_k)_k`. -/
lemma D_apply (p : E 1) (q : E 0) : D p q = q.1 • sinOp p.1 p.2 + cosOp p.1 q.2 := rfl

/-- The inclusion `E_m → E₀` of `E = ℝ ⊕ X`. -/
lemma E_toBase (m : ℕ) (p : E m) : E.toBase m p = ((p.1, X.toBase m p.2) : E 0) := by
  rw [ScBanach.prod_toBase, ScBanach.const_toBase]

/-- The inclusion `(E¹)_m → E₁` of `E = ℝ ⊕ X`. -/
lemma E_shift_toBase : ∀ (m : ℕ) (p : E.shift m),
    E.shift.toBase m p = ((p.1, X.shift.toBase m p.2) : E.shift 0)
  | 0, _ => rfl
  | m + 1, p => by
    rw [ScScale.toBase_succ, E_shift_toBase m, ScScale.toBase_succ]
    rfl

/-- On every level, `f` is given by the same formula. -/
lemma levelMap_f (m : ℕ) (p : E m) : levelMap f m p = cosOp p.1 p.2 := by
  apply levelMap_eq_of_toBase_eq
  rw [E_toBase]
  exact X_toBase_diag m _ _ p.2

/-- `f` is sc⁰ (Definition 1.1.13 (preprint 1.12)): on level `m` it is `(t, y) ↦ (cos(k t) y_k)_k`. -/
lemma isSc0_f : IsSc0 E X univ f where
  mem_range m p _ := ⟨cosOp p.1 p.2, by rw [E_toBase]; exact X_toBase_diag m _ _ p.2⟩
  continuousOn m := continuous_cosOp.continuousOn.congr fun p _ => levelMap_f m p

/-- **The derivative** of `(t, y) ↦ f(t, ι y)` on `E₁ = ℝ × X₁` (`ι = inclOp : X₁ → X₀`).  The
`t`-derivative of `cos(k t) x_k` is `−k sin(k t) x_k`; the factor `k` is absorbed by the weight of
`X₁`.  Remainder estimate: `|(cos(k(t+τ)) − cos(kt) + τk sin(kt)) x_k| = |τ| |ρ_k(τ) y_k|` with
multipliers `ρ_k(τ) → 0`, `|ρ_k| ≤ 2` (uniformly small on `y ∈ c₀`, `eventually_forall_abs_mul_le`),
and `|(cos(k(t+τ)) − cos(kt)) w_k ζ_k| ≤ |τ| |ζ|`. -/
theorem hasFDerivAt_f (t : ℝ) (y : c0) :
    HasFDerivAt (fun q : ℝ × c0 => cosOp q.1 (inclOp q.2))
      ((ContinuousLinearMap.fst ℝ ℝ c0).smulRight (sinOp t y) +
        (cosOp t).comp (inclOp.comp (ContinuousLinearMap.snd ℝ ℝ c0))) (t, y) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  set ρ : ℝ → ℕ → ℝ := fun τ k =>
    w k * (τ⁻¹ * (Real.cos ((k : ℝ) * (t + τ)) - Real.cos ((k : ℝ) * t)) +
      (k : ℝ) * Real.sin ((k : ℝ) * t)) with hρdef
  have hA : ∀ τ (k : ℕ),
      |Real.cos ((k : ℝ) * (t + τ)) - Real.cos ((k : ℝ) * t)| ≤ (k : ℝ) * |τ| := by
    intro τ k
    refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
    rw [show (k : ℝ) * (t + τ) - (k : ℝ) * t = (k : ℝ) * τ by ring, abs_mul, Nat.abs_cast]
  have hρB : ∀ τ k, |ρ τ k| ≤ 2 := by
    intro τ k
    have h1 : |τ⁻¹ * (Real.cos ((k : ℝ) * (t + τ)) - Real.cos ((k : ℝ) * t))| ≤ (k : ℝ) := by
      rcases eq_or_ne τ 0 with rfl | hτ
      · simp
      · rw [abs_mul, abs_inv]
        calc |τ|⁻¹ * |Real.cos ((k : ℝ) * (t + τ)) - Real.cos ((k : ℝ) * t)|
            ≤ |τ|⁻¹ * ((k : ℝ) * |τ|) := by gcongr; exact hA τ k
          _ = k := by field_simp
    have h2 : |(k : ℝ) * Real.sin ((k : ℝ) * t)| ≤ (k : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg k) (Real.abs_sin_le_one _)
    simp only [hρdef]
    rw [abs_mul, abs_of_pos (w_pos k)]
    calc w k * |τ⁻¹ * (Real.cos ((k : ℝ) * (t + τ)) - Real.cos ((k : ℝ) * t)) +
          (k : ℝ) * Real.sin ((k : ℝ) * t)| ≤ w k * ((k : ℝ) + k) := by
          gcongr
          · exact (w_pos k).le
          · exact (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = 2 * ((k : ℝ) * w k) := by ring
      _ ≤ 2 * 1 := by gcongr; exact natCast_mul_w_le k
      _ = 2 := mul_one 2
  have hρ : ∀ k, Tendsto (fun τ => ρ τ k) (𝓝[≠] 0) (𝓝 0) := by
    intro k
    have hd : HasDerivAt (fun s => Real.cos ((k : ℝ) * s))
        (-Real.sin ((k : ℝ) * t) * ((k : ℝ) * 1)) t :=
      ((hasDerivAt_id' t).const_mul (k : ℝ)).cos
    have := hasDerivAt_iff_tendsto_slope_zero.1 hd
    have h2 := (this.add_const ((k : ℝ) * Real.sin ((k : ℝ) * t))).const_mul (w k)
    simp only [smul_eq_mul] at h2
    convert h2 using 2
    ring
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ∀ k, |ρ τ k * y k| ≤ ε / 2 :=
    eventually_forall_abs_mul_le hρB hρ y (half_pos hε)
  have h1' : ∀ᶠ q in 𝓝 (0 : ℝ × c0), q.1 ≠ 0 → ∀ k, |ρ q.1 k * y k| ≤ ε / 2 := by
    have := eventually_nhdsWithin_iff.1 h1
    exact (continuous_fst.tendsto (0 : ℝ × c0)).eventually this
  have h2 : ∀ᶠ q in 𝓝 (0 : ℝ × c0), ‖q‖ ≤ ε / 2 := by
    have := Metric.closedBall_mem_nhds (0 : ℝ × c0) (half_pos hε)
    filter_upwards [this] with q hq
    simpa using hq
  filter_upwards [h1', h2] with q hq1 hq2
  obtain ⟨τ, ζ⟩ := q
  have hτ : |τ| ≤ ‖((τ, ζ) : ℝ × c0)‖ := by
    have := norm_fst_le ((τ, ζ) : ℝ × c0); rwa [Real.norm_eq_abs] at this
  have hζ : ‖ζ‖ ≤ ‖((τ, ζ) : ℝ × c0)‖ := norm_snd_le ((τ, ζ) : ℝ × c0)
  refine norm_le_of_forall (by positivity) fun k => ?_
  change |Real.cos ((k : ℝ) * (t + τ)) * (w k * ((y : c0) k + ζ k)) -
      Real.cos ((k : ℝ) * t) * (w k * y k) -
      (τ * (sinMul t k * y k) + Real.cos ((k : ℝ) * t) * (w k * ζ k))| ≤ ε * ‖((τ, ζ) : ℝ × c0)‖
  set A := Real.cos ((k : ℝ) * (t + τ)) - Real.cos ((k : ℝ) * t) with hAdef
  have e : Real.cos ((k : ℝ) * (t + τ)) * (w k * ((y : c0) k + ζ k)) -
      Real.cos ((k : ℝ) * t) * (w k * y k) -
      (τ * (sinMul t k * y k) + Real.cos ((k : ℝ) * t) * (w k * ζ k)) =
      (A + τ * ((k : ℝ) * Real.sin ((k : ℝ) * t))) * w k * y k + A * w k * ζ k := by
    rw [hAdef]; unfold sinMul; ring
  rw [e]
  have hfirst : |(A + τ * ((k : ℝ) * Real.sin ((k : ℝ) * t))) * w k * y k| ≤ |τ| * (ε / 2) := by
    rcases eq_or_ne τ 0 with rfl | hτ0
    · simp [hAdef]
    · have : (A + τ * ((k : ℝ) * Real.sin ((k : ℝ) * t))) * w k * y k = τ * (ρ τ k * y k) := by
        simp only [hρdef, hAdef]; field_simp
      rw [this, abs_mul]
      exact mul_le_mul_of_nonneg_left (hq1 hτ0 k) (abs_nonneg τ)
  have hsecond : |A * w k * ζ k| ≤ |τ| * ‖ζ‖ := by
    rw [abs_mul, abs_mul, abs_of_pos (w_pos k)]
    calc |A| * w k * |ζ k| ≤ ((k : ℝ) * |τ|) * w k * ‖ζ‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hA τ k) (w_pos k).le) (abs_apply_le_norm ζ k)
            (abs_nonneg _) (by have := w_pos k; positivity)
      _ = |τ| * ((k : ℝ) * w k) * ‖ζ‖ := by ring
      _ ≤ |τ| * 1 * ‖ζ‖ := by gcongr; exact natCast_mul_w_le k
      _ = |τ| * ‖ζ‖ := by ring
  calc |(A + τ * ((k : ℝ) * Real.sin ((k : ℝ) * t))) * w k * y k + A * w k * ζ k|
      ≤ |τ| * (ε / 2) + |τ| * ‖ζ‖ := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
    _ ≤ ‖((τ, ζ) : ℝ × c0)‖ * (ε / 2) + ‖((τ, ζ) : ℝ × c0)‖ * ‖((τ, ζ) : ℝ × c0)‖ := by
        gcongr
    _ ≤ ‖((τ, ζ) : ℝ × c0)‖ * (ε / 2) + ‖((τ, ζ) : ℝ × c0)‖ * (ε / 2) := by
        gcongr
    _ = ε * ‖((τ, ζ) : ℝ × c0)‖ := by ring

/-- The inclusion `X₁ → X₀` is `inclOp`. -/
lemma X_toBase_one (y : X 1) : X.toBase 1 y = inclOp y := rfl

/-- The tangent map on level `m`, again the same formula on every level:
`((t, y), (τ, ξ)) ↦ (cos(kt) y_k, τ sinMul_k(t) y_k + cos(kt) ξ_k)`. -/
def tangentLevel (p : (ℝ × c0) × (ℝ × c0)) : c0 × c0 :=
  (cosOp p.1.1 p.1.2, p.2.1 • sinOp p.1.1 p.1.2 + cosOp p.1.1 p.2.2)

/-- The level maps of `Tf` are continuous. -/
lemma continuous_tangentLevel : Continuous tangentLevel := by
  unfold tangentLevel
  refine (continuous_cosOp.comp continuous_fst).prodMk
    ((continuous_snd.fst.smul (continuous_sinOp.comp continuous_fst)).add
      (continuous_cosOp.comp (continuous_fst.fst.prodMk continuous_snd.snd)))

/-- `tangentLevel` is the level-`m` map of `Tf`. -/
lemma toBase_tangentLevel (m : ℕ) (p : E.tangent m) :
    X.tangent.toBase m (tangentLevel p) = tangentMapWith f D (E.tangent.toBase m p) := by
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
  change (_, _) = (levelMap f 1 (E.shift.toBase m p.1), D (E.shift.toBase m p.1) (E.toBase m p.2))
  rw [levelMap_f, D_apply, E_shift_toBase, E_toBase]
  refine Prod.ext ?_ ?_
  · exact X_shift_toBase_diag m _ _ _
  · ext k
    change X.toBase m (p.2.1 • sinOp p.1.1 p.1.2 + cosOp p.1.1 p.2.2) k = _
    rw [X_toBase_apply]
    have h1 : ((ScBanach.shiftScale XScale).toBase m) p.1.2 k = w k ^ m * (p.1.2 : c0) k :=
      X_shift_toBase_apply m p.1.2 k
    have h2 : (XScale.toBase m) p.2.2 k = w k ^ m * (p.2.2 : c0) k := XScale_toBase_apply m p.2.2 k
    simp only [ZeroAtInftyContinuousMap.coe_add, ZeroAtInftyContinuousMap.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, sinOp, cosOp, diag_apply]
    rw [h1, h2]
    ring

/-- **`f` is sc¹** (Definition 1.1.15 (preprint 1.14)) on `U = E₀`, with the derivative family `D`. -/
theorem isSc1With : IsSc1With univ f D where
  isSc0 := isSc0_f
  hasFDerivWithinAt p _ := by
    rw [ScBanach.lvlSet_univ]
    have hfun : f ∘ E.toBase 1 = fun q : ℝ × c0 => cosOp q.1 (inclOp q.2) := by
      funext q
      simp only [Function.comp, f]
      rw [E_toBase]
      rfl
    rw [hfun]
    refine ((hasFDerivAt_f p.1 p.2).congr_fderiv ?_).hasFDerivWithinAt
    refine ContinuousLinearMap.ext fun q => ?_
    rw [ContinuousLinearMap.comp_apply, D_apply, E_toBase]
    rfl
  tangent_isSc0 :=
    { mem_range := fun m p _ => ⟨tangentLevel p, toBase_tangentLevel m p⟩
      continuousOn := fun m => continuous_tangentLevel.continuousOn.congr fun p _ =>
        levelMap_eq_of_toBase_eq (toBase_tangentLevel m p) }

/-- `f` is sc¹ (Definition 1.1.15 (preprint 1.14)). -/
theorem isSc1 : IsSc1 univ f := ⟨D, isSc1With⟩

/-! ### The derivative is not continuous in the operator norm -/

/-- The unit vector `e_j ∈ c₀`. -/
def unitVec (j : ℕ) : c0 := mkC0 (fun k => if k = j then 1 else 0) (by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop j] with k hk
  rw [if_neg (by omega)])

/-- `‖e_j‖ ≤ 1`. -/
lemma norm_unitVec_le (j : ℕ) : ‖unitVec j‖ ≤ 1 :=
  norm_le_of_forall zero_le_one fun k => by
    change |(if k = j then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> simp

/-- `‖Df(π/(n+1), 0) − Df(0, 0)‖ ≥ 2`: on the unit vector `e_{n+1}` the difference is
`cos(π) − cos(0) = −2`. -/
lemma two_le_norm_D_sub (n : ℕ) :
    2 ≤ ‖D ((Real.pi / ((n : ℝ) + 1), 0) : E 1) - D ((0, 0) : E 1)‖ := by
  set L := D ((Real.pi / ((n : ℝ) + 1), 0) : E 1) - D ((0, 0) : E 1) with hL
  have hv : ‖(((0 : ℝ), unitVec (n + 1)) : E 0)‖ ≤ 1 := by
    rw [Prod.norm_def]
    exact max_le (by simp) (norm_unitVec_le _)
  have hval : |L ((0, unitVec (n + 1)) : E 0) (n + 1)| = 2 := by
    rw [hL, FunLike.coe_sub, Pi.sub_apply, D_apply, D_apply]
    simp only [zero_smul, zero_add, ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, cosOp,
      diag_apply, unitVec, mkC0_apply, if_pos, mul_one]
    unfold cosMul
    have : ((n + 1 : ℕ) : ℝ) * (Real.pi / ((n : ℝ) + 1)) = Real.pi := by
      push_cast; field_simp
    rw [this, Real.cos_pi, mul_zero, Real.cos_zero]
    norm_num
  calc (2 : ℝ) = |L ((0, unitVec (n + 1)) : E 0) (n + 1)| := hval.symm
    _ ≤ ‖L ((0, unitVec (n + 1)) : E 0)‖ := abs_apply_le_norm _ _
    _ ≤ ‖L‖ * ‖(((0 : ℝ), unitVec (n + 1)) : E 0)‖ := L.le_opNorm _
    _ ≤ ‖L‖ * 1 := by gcongr
    _ = ‖L‖ := mul_one _

/-- **`x ↦ Df(x)` is not continuous into `L(E₀, F₀)` with the operator norm** at `0 ∈ E₁`:
`(π/(n+1), 0) → (0, 0)` in `E₁` while `‖Df(π/(n+1), 0) − Df(0, 0)‖ ≥ 2`. -/
theorem not_continuousAt_D : ¬ ContinuousAt D ((0, 0) : E 1) := by
  intro h
  obtain ⟨δ, hδ, hδ'⟩ :=
    (Metric.continuousAt_iff (α := E 1) (β := E 0 →L[ℝ] X 0) (f := D) (a := (0, 0))).1 h 2 two_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.pi / δ)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsmall : Real.pi / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [Real.pi_pos]
  have hd : dist ((Real.pi / ((n : ℝ) + 1), 0) : E 1) ((0, 0) : E 1) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
      abs_of_pos (div_pos Real.pi_pos hpos)]
    exact max_lt hsmall hδ
  have h1 := hδ' hd
  have h2 : dist (D ((Real.pi / ((n : ℝ) + 1), 0) : E 1)) (D ((0, 0) : E 1)) =
      ‖D ((Real.pi / ((n : ℝ) + 1), 0) : E 1) - D ((0, 0) : E 1)‖ :=
    dist_eq_norm (E := E 0 →L[ℝ] X 0) _ _
  have h3 := two_le_norm_D_sub n
  linarith

/-- The same for **every** derivative family of `f`: the derivative is unique on `E₁` (the
project's `IsSc1With.eq_of_uniqueDiffWithinAt`), so `x ↦ D' x` is not continuous on `U₁ = E₁`
for the operator norm. -/
theorem not_continuousOn_of_isSc1With {D' : E 1 → E 0 →L[ℝ] X 0} (h : IsSc1With univ f D') :
    ¬ ContinuousOn D' (E.lvlSet univ 1) := by
  intro hc
  have hDD : D' = D := funext fun x =>
    (isSc1With.eq_of_uniqueDiffWithinAt h (mem_univ x) (by
      rw [ScBanach.lvlSet_univ]; exact uniqueDiffWithinAt_univ)).symm
  rw [ScBanach.lvlSet_univ, continuousOn_univ, hDD] at hc
  exact not_continuousAt_D hc.continuousAt

end ScOneExample

/-- **The remark after Definition 1.1.15 (preprint 1.14)** ("in general `x ↦ Df(x)` is not continuous into
`L(E₀, F₀)` with the operator norm"; round-trip items V1.13, V1.34): there are sc-Banach spaces
`E, F`, a relatively open subset `U` of a partial quadrant `C ⊆ E` and an sc¹ map `f : U → F` such
that for every derivative family `D` of `f`, `x ↦ D x` is not continuous on `U₁` (with the
`E₁`-topology) into `L(E₀, F₀)` with the operator norm.  The example: `E = ℝ ⊕ X`, `F = X`
(`X` the weighted sequence sc-Banach space `ScOneExample.X`), `U = C = E₀`,
`f(t, x)_k = cos(k t) x_k`. -/
theorem exists_isSc1_not_continuousOn_deriv :
    ∃ (E F : ScBanach) (C U : Set (E 0)) (f : E 0 → F 0),
      IsRelOpenInQuadrant E C U ∧ IsSc1 U f ∧
        ∀ D : E 1 → E 0 →L[ℝ] F 0, IsSc1With U f D → ¬ ContinuousOn D (E.lvlSet U 1) :=
  ⟨ScOneExample.E, ScOneExample.X, univ, univ, ScOneExample.f,
    ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩, ScOneExample.isSc1,
    fun _ h => ScOneExample.not_continuousOn_of_isSc1With h⟩

end Polyfold
