import Polyfold.Chapter7.LineSobolevScale

/-!
# Subsection 1.4.4 (2021, p. 18): translates of a test function in `H^{m,δ}(ℝ)`

For the moving projections `π_t(f) = ⟨f, β(· + e^{1/t})⟩ β(· + e^{1/t})` we need, for a smooth
compactly supported `χ` (`IsTest1`) and its translates `χ_c = χ(· + c)`:

* `norm_toH1_le`: `‖g‖_{H^{m,δ}} ≤ #idx · K · √(b − a)` if the derivatives of `g` up to order `m`
  vanish off `[a, b]` and `e^{δ|s|} |g^{(i)}(s)| ≤ K` on `[a, b]`;
* `norm_trH_le`: `‖χ_c‖_{H^{m,δ}} ≤ #idx · e^{δ(|c| + R)} M √(2R)`;
* `norm_ell_le`: the pairing `f ↦ ⟨χ_c, f⟩` on `H^{m,δ}(ℝ)` has norm `≤ e^{-δ(c - R)} M √(2R)`
  for `c ≥ R` (the weight `e^{δ|s|}` of `f` is large on the support of `χ_c`);
* `hasDerivAt_trH`: `c ↦ χ_c ∈ H^{m,δ}(ℝ)` is differentiable with derivative `(χ')_c`, hence
  `C^∞` (`contDiff_trH`, `iteratedDeriv_trH`), and the same for the pairings (`contDiff_ellT`,
  `iteratedDeriv_ellT`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal InnerProductSpace

noncomputable section

namespace Polyfold.ZhouLine

open Polyfold.GapP1Sobolev

/-! ### Test functions of the line -/

/-- Smooth functions of `s` vanishing for `|s| ≥ R`. -/
structure IsTest1 (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ g
  bdd : ∃ R, 0 ≤ R ∧ ∀ s, R ≤ |s| → g s = 0

lemma IsTest1.isTest {g : ℝ → ℝ} (h : IsTest1 g) : IsTest (liftFun g) := by
  obtain ⟨R, -, hR⟩ := h.bdd
  exact isTest_liftFun h.smooth fun s hs => hR s hs.le

lemma IsTest1.memLp {g : ℝ → ℝ} (h : IsTest1 g) : MemLp g 2 volume := by
  obtain ⟨R, -, hR⟩ := h.bdd
  exact h.smooth.continuous.memLp_of_hasCompactSupport (win_hasCompactSupport hR)

lemma IsTest1.deriv {g : ℝ → ℝ} (h : IsTest1 g) : IsTest1 (deriv g) := by
  obtain ⟨R, hR0, hR⟩ := h.bdd
  refine ⟨h.smooth.iterate_deriv 1, R + 1, by linarith, fun s hs => ?_⟩
  have := win_deriv_zero hR 1 (show R < |s| by linarith)
  simpa using this

lemma IsTest1.iteratedDeriv {g : ℝ → ℝ} (h : IsTest1 g) (k : ℕ) : IsTest1 (iteratedDeriv k g) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma IsTest1.shift {g : ℝ → ℝ} (h : IsTest1 g) (c : ℝ) : IsTest1 fun s => g (s + c) := by
  obtain ⟨R, hR0, hR⟩ := h.bdd
  refine ⟨h.smooth.comp (contDiff_id.add contDiff_const), R + |c|, by positivity, fun s hs => ?_⟩
  refine hR _ ?_
  have := abs_add_le (s + c) (-c)
  rw [add_neg_cancel_right, abs_neg] at this
  linarith

lemma IsTest1.sub {g g' : ℝ → ℝ} (h : IsTest1 g) (h' : IsTest1 g') : IsTest1 fun s => g s - g' s := by
  obtain ⟨R, hR0, hR⟩ := h.bdd
  obtain ⟨R', hR0', hR'⟩ := h'.bdd
  refine ⟨h.smooth.sub h'.smooth, max R R', le_max_of_le_left hR0, fun s hs => ?_⟩
  rw [hR s ((le_max_left _ _).trans hs), hR' s ((le_max_right _ _).trans hs), sub_zero]

lemma IsTest1.const_mul {g : ℝ → ℝ} (h : IsTest1 g) (a : ℝ) : IsTest1 fun s => a * g s := by
  obtain ⟨R, hR0, hR⟩ := h.bdd
  exact ⟨contDiff_const.mul h.smooth, R, hR0, fun s hs => by rw [hR s hs, mul_zero]⟩

/-- A test function of the line as an element of `H^{m,δ}(ℝ)`. -/
def toH1 (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {g : ℝ → ℝ} (h : IsTest1 g) : H1 m hδ :=
  ofTest1 m hδ h.isTest h.memLp

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma val_toH1 {g : ℝ → ℝ} (h : IsTest1 g) : H1.val (toH1 m hδ h) = h.memLp.toLp g := rfl

lemma toH1_congr {g g' : ℝ → ℝ} (h : IsTest1 g) (h' : IsTest1 g') (e : g = g') :
    toH1 m hδ h = toH1 m hδ h' := by subst e; rfl

lemma toH1_sub {g g' : ℝ → ℝ} (h : IsTest1 g) (h' : IsTest1 g') :
    toH1 m hδ (h.sub h') = toH1 m hδ h - toH1 m hδ h' := by
  refine H1.val_injective ?_
  change (h.sub h').memLp.toLp _ = h.memLp.toLp g - h'.memLp.toLp g'
  rw [← MemLp.toLp_sub]; rfl

lemma toH1_const_mul {g : ℝ → ℝ} (h : IsTest1 g) (a : ℝ) :
    toH1 m hδ (h.const_mul a) = a • toH1 m hδ h := by
  refine H1.val_injective ?_
  change (h.const_mul a).memLp.toLp _ = a • h.memLp.toLp g
  rw [← MemLp.toLp_const_smul]; rfl

lemma liftH_toH1 {g : ℝ → ℝ} (h : IsTest1 g) : liftH m hδ (toH1 m hδ h) = toH m hδ h.isTest :=
  liftH_ofTest1 _ _

/-! ### Norm bounds -/

lemma Dt_zero : Dt (0 : ℝ × ℝ → ℝ) = 0 := by funext x; simp [Dt]

lemma Ds_zero : Ds (0 : ℝ × ℝ → ℝ) = 0 := by funext x; simp [Ds]

lemma iterate_Ds_liftFun {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ a : ℕ, Ds^[a] (liftFun g) = liftFun (iteratedDeriv a g)
  | 0 => by simp
  | a + 1 => by
    rw [Function.iterate_succ_apply', iterate_Ds_liftFun hg a,
      Ds_liftFun (hg.differentiable_iteratedDeriv a (by exact_mod_cast WithTop.coe_lt_top _)),
      iteratedDeriv_succ]

lemma pD_liftFun {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (a b : ℕ) :
    pD a b (liftFun g) = if b = 0 then liftFun (iteratedDeriv a g) else 0 := by
  rcases b with _ | b
  · simp [pD, iterate_Ds_liftFun hg]
  · have h0 : Dt^[b + 1] (liftFun g) = 0 := by
      rw [Function.iterate_succ_apply]
      rw [Dt_liftFun (hg.differentiable (by simp))]
      induction b with
      | zero => rfl
      | succ b ih => rw [Function.iterate_succ_apply', ih, Dt_zero]
    have h1 : ∀ a : ℕ, Ds^[a] (0 : ℝ × ℝ → ℝ) = 0 := fun a => by
      induction a with
      | zero => rfl
      | succ a ih => rw [Function.iterate_succ_apply', ih, Ds_zero]
    simp [pD, h0, h1]

/-- An element of `L²(ℝ × S¹)` bounded by `K` on the strip `[a, b] × S¹` and `0` off it has norm
`≤ K √(b − a)`. -/
lemma norm_le_of_strip {F : Lp ℝ 2 cyl} {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hF : ∀ᵐ x ∂cyl, |F x| ≤ (Icc a b ×ˢ (univ : Set ℝ)).indicator (fun _ => K) x) :
    ‖F‖ ≤ K * Real.sqrt (b - a) := by
  have hS : MeasurableSet (Icc a b ×ˢ (univ : Set ℝ)) := measurableSet_Icc.prod MeasurableSet.univ
  have hμ : cyl (Icc a b ×ˢ (univ : Set ℝ)) ≠ ⊤ := by rw [cyl_slab]; exact ENNReal.ofReal_ne_top
  have hn := norm_indicatorConstLp (p := 2) (by norm_num) (by norm_num) (hs := hS) (hμs := hμ)
    (c := K)
  rw [measureReal_def, cyl_slab, ENNReal.toReal_ofReal (by linarith), Real.norm_eq_abs,
    abs_of_nonneg hK] at hn
  calc ‖F‖ ≤ ‖indicatorConstLp 2 hS hμ K‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [hF, indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hμ) (c := K)]
          with x h1 h2
        rw [Real.norm_eq_abs, Real.norm_eq_abs, h2]
        refine h1.trans (le_abs_self _)
    _ = K * Real.sqrt (b - a) := by
        rw [hn, Real.sqrt_eq_rpow]; norm_num

lemma norm_le_card_mul {u : H m hδ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ p : idx m, ‖wdv (H.toSub u) p‖ ≤ B) :
    ‖u‖ ≤ (idx m).card * B := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_sq_H]
  calc ∑ p : idx m, ‖wdv (H.toSub u) p‖ ^ 2 ≤ ∑ _p : idx m, B ^ 2 :=
        Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (h p) 2
    _ = (idx m).card * B ^ 2 := by simp
    _ ≤ ((idx m).card * B) ^ 2 := by
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : ((idx m).card : ℝ) ≤ ((idx m).card : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos (idx m).card with h0 | h0
          · simp [h0]
          · exact le_self_pow₀ (by exact_mod_cast h0) two_ne_zero
        exact this

/-- **Sup bound for the `H^{m,δ}(ℝ)`-norm of a test function**. -/
theorem norm_toH1_le {g : ℝ → ℝ} (h : IsTest1 g) {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hvan : ∀ i ≤ m, ∀ s, s ∉ Icc a b → iteratedDeriv i g s = 0)
    (hbd : ∀ i ≤ m, ∀ s ∈ Icc a b, wt1 δ s * |iteratedDeriv i g s| ≤ K) :
    ‖toH1 m hδ h‖ ≤ (idx m).card * (K * Real.sqrt (b - a)) := by
  rw [← norm_liftH, liftH_toH1]
  refine norm_le_card_mul (by positivity) fun p => ?_
  have hd : dv (H.toSub (toH m hδ h.isTest)) p =ᵐ[cyl] pD p.1.1 p.1.2 (liftFun g) :=
    dv_unique _ p ((h.isTest.smPer.hasWeakDeriv p.1.1 p.1.2).congr_ae
      (h.isTest.memLp 2).coeFn_toLp.symm (ae_eq_refl _)) ((h.isTest.pD _ _).memLp 2)
  refine norm_le_of_strip hab hK ?_
  filter_upwards [coeFn_wdv (H.toSub (toH m hδ h.isTest)) p, hd] with x e1 e2
  rw [e1, e2, pD_liftFun h.smooth]
  have hp := mem_idx.1 p.2
  split_ifs with hb
  · by_cases hx : x ∈ Icc a b ×ˢ (univ : Set ℝ)
    · rw [indicator_of_mem hx, abs_mul, abs_of_pos (wt_pos _ _)]
      exact hbd p.1.1 (by omega) x.1 hx.1
    · rw [indicator_of_notMem hx]
      have hx1 : x.1 ∉ Icc a b := fun h' => hx ⟨h', mem_univ _⟩
      simp [liftFun, hvan p.1.1 (by omega) x.1 hx1]
  · simp only [Pi.zero_apply, mul_zero, abs_zero]
    exact indicator_nonneg (fun _ _ => hK) _

/-! ### Translates -/

/-- The translate `χ(· + c)` in `H^{m,δ}(ℝ)` (junk `0` if `χ` is not a test function). -/
def trH (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (χ : ℝ → ℝ) (c : ℝ) : H1 m hδ := by
  classical
  exact if h : IsTest1 χ then toH1 m hδ (h.shift c) else 0

lemma trH_eq {χ : ℝ → ℝ} (h : IsTest1 χ) (c : ℝ) : trH m hδ χ c = toH1 m hδ (h.shift c) := by
  simp [trH, h]

/-- `|s| ≥ c − R` on the support of `χ(· + c)`. -/
lemma abs_ge_of_mem {R c s : ℝ} (hs : s ∈ Icc (-c - R) (-c + R)) : c - R ≤ |s| := by
  rw [abs_eq_max_neg]; exact le_max_of_le_right (by linarith [hs.2])

lemma abs_le_of_mem {R c s : ℝ} (hs : s ∈ Icc (-c - R) (-c + R)) : |s| ≤ |c| + R := by
  have h1 := le_abs_self c
  have h2 := neg_le_abs c
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

lemma not_mem_Icc_shift {R c s : ℝ} (hs : s ∉ Icc (-c - R) (-c + R)) : R < |s + c| := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hs
  rw [lt_abs]
  rcases hs with hs | hs
  · right; linarith
  · left; linarith

/-- **`‖χ(· + c)‖_{H^{m,δ}} ≤ #idx · e^{δ(|c|+R)} M √(2R)`.** -/
theorem norm_trH_le {χ : ℝ → ℝ} (h : IsTest1 χ) {R M : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ s, R ≤ |s| → χ s = 0) (hM0 : 0 ≤ M) (hM : ∀ i ≤ m, ∀ s, |iteratedDeriv i χ s| ≤ M)
    (c : ℝ) :
    ‖trH m hδ χ c‖ ≤ (idx m).card * ((Real.exp (δ * (|c| + R)) * M) * Real.sqrt (2 * R)) := by
  rw [trH_eq h]
  have e2 : 2 * R = (-c + R) - (-c - R) := by ring
  rw [e2]
  refine norm_toH1_le (h.shift c) (by linarith) (by positivity) (fun i _ s hs => ?_)
    (fun i hi s hs => ?_)
  · rw [iteratedDeriv_comp_add_const]; exact win_deriv_zero hR i (not_mem_Icc_shift hs)
  · rw [iteratedDeriv_comp_add_const]
    refine mul_le_mul ?_ (hM i hi _) (abs_nonneg _) (Real.exp_pos _).le
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le_of_mem hs) hδ)

/-! ### Pairings -/

/-- `f ↦ f ∈ L²(ℝ)` on `H^{m,δ}(ℝ)`, of norm `≤ 1`. -/
def val1CLM (m : ℕ) (hδ : 0 ≤ δ) : H1 m hδ →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := H1.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1 fun f => by
    rw [one_mul]
    change ‖H1.val f‖ ≤ ‖f‖
    rw [← norm_liftC, ← valCLM_liftH, ← norm_liftH]
    exact ((valCLM m hδ).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (LinearMap.mkContinuous_norm_le _ zero_le_one _))

lemma val1CLM_apply (f : H1 m hδ) : val1CLM m hδ f = H1.val f := rfl

/-- The pairing `g ↦ (f ↦ ⟨g, f⟩_{L²(ℝ)})`, from `L²(ℝ)` to the dual of `H^{m,δ}(ℝ)`. -/
def ellL (m : ℕ) (hδ : 0 ≤ δ) : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] (H1 m hδ →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (H1 m hδ) (Lp ℝ 2 (volume : Measure ℝ)) ℝ).flip
    (val1CLM m hδ)).comp (innerSL ℝ)

lemma ellL_apply (g : Lp ℝ 2 (volume : Measure ℝ)) (f : H1 m hδ) :
    ellL m hδ g f = ⟪g, H1.val f⟫_ℝ := rfl

lemma Minv_eq_Mc : Minv hδ = Mc hδ := by
  ext1 v
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp _ (continuous_wt (-δ)).aestronglyMeasurable 1 (abs_wt_neg_le hδ) v,
    coeFn_mulG (μ := cyl) _ (continuous_wt (-δ)).aestronglyMeasurable 1 (abs_wt_neg_le hδ) v]
    with x h1 h2
  rw [h1, h2]

lemma abs_ellL_le (g : Lp ℝ 2 (volume : Measure ℝ)) (f : H1 m hδ) :
    |ellL m hδ g f| ≤ ‖Mc hδ (liftC g)‖ * ‖f‖ := by
  rw [ellL_apply, ← inner_liftC, ← valCLM_liftH, valCLM_apply, val_eq_Minv, Minv_eq_Mc,
    ← inner_mulG]
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [← norm_liftH]; exact norm_wdv_le _ _

lemma norm_ellL_le (g : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖ellL m hδ g‖ ≤ ‖Mc hδ (liftC g)‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => by
    rw [Real.norm_eq_abs]; exact abs_ellL_le g f

/-- The translate `χ(· + c)` in `L²(ℝ)`. -/
def tr0 (χ : ℝ → ℝ) (c : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  val1CLM 0 (le_refl (0 : ℝ)) (trH 0 (le_refl (0 : ℝ)) χ c)

lemma tr0_eq {χ : ℝ → ℝ} (h : IsTest1 χ) (c : ℝ) : tr0 χ c = (h.shift c).memLp.toLp _ := by
  rw [tr0, trH_eq h]; rfl

lemma val_trH {χ : ℝ → ℝ} (c : ℝ) : H1.val (trH m hδ χ c) = tr0 χ c := by
  by_cases h : IsTest1 χ
  · rw [tr0_eq h, trH_eq h]; rfl
  · simp only [tr0, trH, h, dif_neg, not_false_eq_true]; rfl

/-- **The pairing with a far translate is small**: `‖⟨χ(· + c), ·⟩‖_{H^{m,δ}(ℝ)'} ≤
e^{-δ(c - R)} M √(2R)`, since `e^{-δ|s|} ≤ e^{-δ(c-R)}` on the support of `χ(· + c)`. -/
theorem norm_ellL_tr0_le {χ : ℝ → ℝ} (h : IsTest1 χ) {R M : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ s, R ≤ |s| → χ s = 0) (hM0 : 0 ≤ M) (hM : ∀ s, |χ s| ≤ M) (c : ℝ) :
    ‖ellL m hδ (tr0 χ c)‖ ≤ (Real.exp (-(δ * (c - R))) * M) * Real.sqrt (2 * R) := by
  refine (norm_ellL_le _).trans ?_
  have e2 : 2 * R = (-c + R) - (-c - R) := by ring
  rw [e2]
  refine norm_le_of_strip (by linarith) (by positivity) ?_
  rw [tr0_eq h]
  have h3 : (fun x : ℝ × ℝ => ((h.shift c).memLp.toLp _ : Lp ℝ 2 (volume : Measure ℝ)) x.1)
      =ᵐ[cyl] fun x => χ (x.1 + c) :=
    measurePreserving_fst_cyl.quasiMeasurePreserving.ae_eq_comp (h.shift c).memLp.coeFn_toLp
  filter_upwards [coeFn_mulG (μ := cyl) _ (continuous_wt (-δ)).aestronglyMeasurable 1
    (abs_wt_neg_le hδ) (liftC ((h.shift c).memLp.toLp _)), coeFn_liftC ((h.shift c).memLp.toLp _),
    h3] with x e1 e2 e3
  rw [e1, e2, e3]
  by_cases hx : x ∈ Icc (-c - R) (-c + R) ×ˢ (univ : Set ℝ)
  · rw [indicator_of_mem hx, abs_mul, abs_of_pos (wt_pos _ _)]
    refine mul_le_mul ?_ (hM _) (abs_nonneg _) (Real.exp_pos _).le
    rw [wt, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left (abs_ge_of_mem hx.1) hδ
    linarith
  · rw [indicator_of_notMem hx]
    have hx1 : x.1 ∉ Icc (-c - R) (-c + R) := fun h' => hx ⟨h', mem_univ _⟩
    rw [hR _ (not_mem_Icc_shift hx1).le, mul_zero, abs_zero]

/-! ### Derivative of the translates -/

lemma IsTest1.contDiffAt {g : ℝ → ℝ} (h : IsTest1 g) (n : ℕ) (s : ℝ) : ContDiffAt ℝ n g s :=
  (h.smooth.of_le (by exact_mod_cast le_top)).contDiffAt

/-- Second-order Taylor bound: `|F(x+h) - F(x) - h F'(x)| ≤ M h²` if `|F''| ≤ M`. -/
lemma taylor2 {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {M : ℝ}
    (hM : ∀ x, |deriv (deriv F) x| ≤ M) (x h : ℝ) :
    |F (x + h) - F x - h * deriv F x| ≤ M * h ^ 2 := by
  have hd1 : Differentiable ℝ F := hF.differentiable (by simp)
  have hd2 : Differentiable ℝ (deriv F) := (hF.iterate_deriv 1).differentiable (by simp)
  have hlip : ∀ t, |deriv F (x + t) - deriv F x| ≤ M * |t| := fun t => by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv F) (s := univ) (x := x)
      (y := x + t) (fun y _ => hd2 y) (fun y _ => by rw [Real.norm_eq_abs]; exact hM y)
      convex_univ (mem_univ _) (mem_univ _)
    simpa [Real.norm_eq_abs] using this
  set G : ℝ → ℝ := fun t => F (x + t) - t * deriv F x
  have hG : ∀ t ∈ uIcc 0 h, HasDerivWithinAt G (deriv F (x + t) - deriv F x) (uIcc 0 h) t :=
    fun t _ => by
      have h1 : HasDerivAt (fun t => F (x + t)) (deriv F (x + t)) t :=
        (hd1 (x + t)).hasDerivAt.comp_const_add x t
      have h2 := h1.fun_sub ((hasDerivAt_id t).mul_const (deriv F x))
      simp only [id, one_mul] at h2
      exact h2.hasDerivWithinAt
  have hb : ∀ t ∈ uIcc 0 h, ‖deriv F (x + t) - deriv F x‖ ≤ M * |h| := fun t ht => by
    rw [Real.norm_eq_abs]
    refine (hlip t).trans (mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hM x)))
    rcases le_total 0 h with h0 | h0
    · rw [uIcc_of_le h0] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
    · rw [uIcc_of_ge h0] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h0]; linarith [ht.1]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hG hb (convex_uIcc 0 h) left_mem_uIcc
    right_mem_uIcc
  simp only [G, Real.norm_eq_abs, add_zero, zero_mul, sub_zero] at this
  calc |F (x + h) - F x - h * deriv F x| = |F (x + h) - h * deriv F x - F x| := by ring_nf
    _ ≤ M * |h| * |h| := this
    _ = M * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **`c ↦ χ(· + c) ∈ H^{m,δ}(ℝ)` is differentiable, with derivative `χ'(· + c)`.** -/
theorem hasDerivAt_trH {χ : ℝ → ℝ} (h : IsTest1 χ) (c : ℝ) :
    HasDerivAt (trH m hδ χ) (trH m hδ (deriv χ) c) c := by
  obtain ⟨R, hR0, hR⟩ := h.bdd
  obtain ⟨M2, hM2⟩ := bdd_iteratedDeriv h.smooth (win_hasCompactSupport hR) (m + 2)
  have hM20 : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0 (Nat.zero_le _) 0)
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  set C : ℝ := (idx m).card * ((Real.exp (δ * (|c| + (R + 1))) * M2) * Real.sqrt (2 * (R + 1)))
  have hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖trH m hδ χ (c + t) - trH m hδ χ c - t • trH m hδ (deriv χ) c‖ ≤ C * t ^ 2 := by
    intro t ht
    rw [trH_eq h, trH_eq h, trH_eq h.deriv, ← toH1_const_mul, ← toH1_sub, ← toH1_sub]
    have e2 : 2 * (R + 1) = (-c + (R + 1)) - (-c - (R + 1)) := by ring
    have hit : ∀ i s, iteratedDeriv i (fun s => χ (s + (c + t)) - χ (s + c) -
        t * deriv χ (s + c)) s = iteratedDeriv i χ (s + (c + t)) - iteratedDeriv i χ (s + c) -
        t * iteratedDeriv (i + 1) χ (s + c) := fun i s => by
      rw [iteratedDeriv_fun_sub (((h.shift _).sub (h.shift c)).contDiffAt i s)
          ((h.deriv.shift c).const_mul t |>.contDiffAt i s),
        iteratedDeriv_fun_sub ((h.shift _).contDiffAt i s) ((h.shift c).contDiffAt i s),
        iteratedDeriv_const_mul _ ((h.deriv.shift c).contDiffAt i s),
        iteratedDeriv_comp_add_const, iteratedDeriv_comp_add_const, iteratedDeriv_comp_add_const,
        iteratedDeriv_succ']
    calc _ ≤ (idx m).card * ((Real.exp (δ * (|c| + (R + 1))) * (M2 * t ^ 2)) *
          Real.sqrt (2 * (R + 1))) := by
          rw [e2]
          refine norm_toH1_le _ (by linarith) (by positivity) (fun i _ s hs => ?_)
            (fun i hi s hs => ?_)
          · rw [hit]
            rw [mem_Icc, not_and_or, not_le, not_le] at hs
            rw [abs_le] at ht
            have k1 : R < |s + (c + t)| := by
              rw [lt_abs]
              rcases hs with hs | hs
              · right; linarith
              · left; linarith
            have k2 : R < |s + c| := by
              rw [lt_abs]
              rcases hs with hs | hs
              · right; linarith
              · left; linarith
            rw [win_deriv_zero hR i k1, win_deriv_zero hR i k2, win_deriv_zero hR (i + 1) k2]
            ring
          · rw [hit]
            refine mul_le_mul ?_ ?_ (abs_nonneg _) (Real.exp_pos _).le
            · exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_le_of_mem hs) hδ)
            · have hF := h.iteratedDeriv i
              have hT := taylor2 hF.smooth (M := M2) (fun x => by
                rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
                exact hM2 (i + 2) (by omega) x) (s + c) t
              rw [← iteratedDeriv_succ] at hT
              rw [show s + (c + t) = s + c + t by ring]
              exact hT
      _ = C * t ^ 2 := by simp only [C]; ring
  refine (Asymptotics.IsBigO.of_bound C ?_).trans_isLittleO (Asymptotics.isLittleO_pow_id
    one_lt_two)
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  exact hbound t ht

/-- A family `F χ c` with `∂_c F χ = F χ'` for test functions is smooth in `c`, with
`∂_c^k F χ = F χ^{(k)}`. -/
lemma iteratedDeriv_of_hasDerivAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : (ℝ → ℝ) → ℝ → X} (hF : ∀ χ, IsTest1 χ → ∀ c, HasDerivAt (F χ) (F (deriv χ) c) c) :
    ∀ (k : ℕ) {χ : ℝ → ℝ}, IsTest1 χ → iteratedDeriv k (F χ) = F (iteratedDeriv k χ)
  | 0, _, _ => by simp
  | k + 1, χ, h => by
    have hd : deriv (F χ) = F (deriv χ) := funext fun c => (hF χ h c).deriv
    rw [iteratedDeriv_succ', hd, iteratedDeriv_of_hasDerivAt hF k h.deriv, iteratedDeriv_succ']

lemma contDiff_of_hasDerivAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : (ℝ → ℝ) → ℝ → X} (hF : ∀ χ, IsTest1 χ → ∀ c, HasDerivAt (F χ) (F (deriv χ) c) c)
    {χ : ℝ → ℝ} (h : IsTest1 χ) : ContDiff ℝ ∞ (F χ) :=
  contDiff_of_differentiable_iteratedDeriv fun k _ => by
    rw [iteratedDeriv_of_hasDerivAt hF k h]
    exact fun c => (hF _ (h.iteratedDeriv k) c).differentiableAt

lemma contDiff_trH {χ : ℝ → ℝ} (h : IsTest1 χ) : ContDiff ℝ ∞ (trH m hδ χ) :=
  contDiff_of_hasDerivAt (fun _ h' c => hasDerivAt_trH h' c) h

lemma iteratedDeriv_trH {χ : ℝ → ℝ} (h : IsTest1 χ) (k : ℕ) :
    iteratedDeriv k (trH m hδ χ) = trH m hδ (iteratedDeriv k χ) :=
  iteratedDeriv_of_hasDerivAt (fun _ h' c => hasDerivAt_trH h' c) k h

/-- The pairing with the translate, `c ↦ ⟨χ(· + c), ·⟩ ∈ H^{m,δ}(ℝ)'`. -/
def ellT (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (χ : ℝ → ℝ) (c : ℝ) : H1 m hδ →L[ℝ] ℝ :=
  ellL m hδ (tr0 χ c)

lemma hasDerivAt_tr0 {χ : ℝ → ℝ} (h : IsTest1 χ) (c : ℝ) :
    HasDerivAt (tr0 χ) (tr0 (deriv χ) c) c :=
  (val1CLM 0 (le_refl (0 : ℝ))).hasFDerivAt.comp_hasDerivAt c (hasDerivAt_trH h c)

lemma hasDerivAt_ellT {χ : ℝ → ℝ} (h : IsTest1 χ) (c : ℝ) :
    HasDerivAt (ellT m hδ χ) (ellT m hδ (deriv χ) c) c :=
  (ellL m hδ).hasFDerivAt.comp_hasDerivAt c (hasDerivAt_tr0 h c)

lemma contDiff_ellT {χ : ℝ → ℝ} (h : IsTest1 χ) : ContDiff ℝ ∞ (ellT m hδ χ) :=
  contDiff_of_hasDerivAt (fun _ h' c => hasDerivAt_ellT h' c) h

lemma iteratedDeriv_ellT {χ : ℝ → ℝ} (h : IsTest1 χ) (k : ℕ) :
    iteratedDeriv k (ellT m hδ χ) = ellT m hδ (iteratedDeriv k χ) :=
  iteratedDeriv_of_hasDerivAt (fun _ h' c => hasDerivAt_ellT h' c) k h

end Polyfold.ZhouLine
