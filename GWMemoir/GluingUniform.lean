import GWMemoir.GluingIso
import GWMemoir.Scales

/-!
# Memoir §4.3: the centred norms (4.7), (4.8) and the weighted estimates behind Props 4.13, 4.14

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.3, pp. 107–108.

For `u ∈ H^{k,δ}(ℝ × S¹)` and a weight `ω(s)` we write `guDv ω u p = ‖ω(s) ∂^p u‖_{L²}` (in
`[0, ∞]`), `guSum ω u = ∑_p guDv ω u p` and `guSq ω u = ∑_p (guDv ω u p)²`.  The squared norms
(4.7), (4.8) of the memoir are `guSq` for the weight `e^{γ|s - R/2|}`:
`∑_{|α| ≤ k} ∫ |D^α q|² e^{2γ|s - R/2|} ds dt`.  The gluing estimates use three weights, for
`d = δ_m ≥ 0`:

* `guE d s = e^{d|s|}`, the weight of `H^{k,d}(ℝ × S¹)` (`guDv_guE`);
* `guZ d R s = e^{d min(|s|, |s - R|)}`; on `[0, R]` it is `e^{dR/2} e^{-d|s - R/2|}`
  (`guZ_eq_of_mem`), so that `guSq (guZ d R)` restricted to `Z_a` is `e^{dR} ‖·‖²_{k,-d}` of (4.7);
* `guC d R s = e^{d max(s, R - s)} = e^{dR/2} e^{d|s - R/2|}` (`guC_eq`), so that
  `guSq (guC d R) = e^{dR} ‖·‖²_{k,d}` of (4.8) on `C_a = ℝ × S¹` (`guSq_guC`).

The two estimates every bound is built from, with constants depending on `k` and on the bounds of
the multiplier only:

* `guSum_mulHL`: `‖χ u‖_{ω'} ≤ K ‖u‖_ω` when `ω' |χ^{(i)}| ≤ M ω` for `i ≤ k` (Leibniz rule);
* `guDv_shH`: `‖u(· - c)‖_{ω'} ≤ ‖u‖_ω` when `ω'(s) ≤ ω(s - c)` (translation).

The multipliers `F(β_a(s)) = F(β(s - R/2))` are translates of one function, so their derivative
bounds do not depend on `R` (`bound_Fβa`).
-/

open Set Filter Topology MeasureTheory Finset
open scoped ENNReal NNReal
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

/-! ## 1. Weighted derivative norms -/

section Weighted

variable {k : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- `‖ω(s) ∂^p u‖_{L²(ℝ × S¹)}`, in `[0, ∞]`. -/
def guDv (ω : ℝ → ℝ) (u : H k hδ) (p : idx k) : ℝ≥0∞ :=
  eLpNorm (fun x : ℝ × ℝ => ω x.1 * dv (H.toSub u) p x) 2 cyl

/-- `∑_p ‖ω ∂^p u‖`. -/
def guSum (ω : ℝ → ℝ) (u : H k hδ) : ℝ≥0∞ := ∑ p : idx k, guDv ω u p

/-- `∑_p ‖ω ∂^p u‖² = ∑_{|α| ≤ k} ∫ |D^α u|² ω² ds dt`: for `ω = e^{γ|s - R/2|}` the squared
norm of (4.7), (4.8) (Memoir p. 107). -/
def guSq (ω : ℝ → ℝ) (u : H k hδ) : ℝ≥0∞ := ∑ p : idx k, guDv ω u p ^ 2

lemma aesm_guDv {ω : ℝ → ℝ} (hω : Measurable ω) (u : H k hδ) (p : idx k) :
    AEStronglyMeasurable (fun x : ℝ × ℝ => ω x.1 * dv (H.toSub u) p x) cyl :=
  (hω.comp measurable_fst).aestronglyMeasurable.mul (dv_memLp _ p).1

lemma dv_lin (a b : ℝ) (u v : H k hδ) (p : idx k) :
    dv (H.toSub (a • u + b • v)) p =ᵐ[cyl]
      fun x => a * dv (H.toSub u) p x + b * dv (H.toSub v) p x := by
  filter_upwards [dv_add (a • H.toSub u) (b • H.toSub v) p, dv_smul a (H.toSub u) p,
    dv_smul b (H.toSub v) p] with x h1 h2 h3
  rw [show H.toSub (a • u + b • v) = a • H.toSub u + b • H.toSub v from rfl, h1, Pi.add_apply,
    h2, h3]

lemma guDv_lin {ω : ℝ → ℝ} (hω : Measurable ω) (a b : ℝ) (u v : H k hδ) (p : idx k) :
    guDv ω (a • u + b • v) p ≤ ‖a‖ₑ * guDv ω u p + ‖b‖ₑ * guDv ω v p := by
  unfold guDv
  rw [eLpNorm_congr_ae (g := a • (fun x : ℝ × ℝ => ω x.1 * dv (H.toSub u) p x) +
      b • (fun x : ℝ × ℝ => ω x.1 * dv (H.toSub v) p x)) ?_]
  · refine (eLpNorm_add_le ((aesm_guDv hω u p).const_smul a) ((aesm_guDv hω v p).const_smul b)
      (by norm_num)).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul]
  · filter_upwards [dv_lin a b u v p] with x hx
    simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma guSum_add {ω : ℝ → ℝ} (hω : Measurable ω) (u v : H k hδ) :
    guSum ω (u + v) ≤ guSum ω u + guSum ω v := by
  rw [guSum, guSum, guSum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have := guDv_lin hω 1 1 u v p
  rwa [one_smul, one_smul, enorm_one, one_mul, one_mul] at this

lemma guSum_sub {ω : ℝ → ℝ} (hω : Measurable ω) (u v : H k hδ) :
    guSum ω (u - v) ≤ guSum ω u + guSum ω v := by
  rw [guSum, guSum, guSum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have := guDv_lin hω 1 (-1) u v p
  rwa [one_smul, neg_one_smul, ← sub_eq_add_neg, enorm_one, enorm_neg, enorm_one, one_mul,
    one_mul] at this

lemma guDv_zero {ω : ℝ → ℝ} (hω : Measurable ω) (p : idx k) : guDv ω (0 : H k hδ) p = 0 := by
  refine le_antisymm ?_ bot_le
  have := guDv_lin hω 0 0 (0 : H k hδ) 0 p
  rwa [zero_smul, add_zero, enorm_zero, zero_mul, add_zero] at this

lemma guSum_zero {ω : ℝ → ℝ} (hω : Measurable ω) : guSum ω (0 : H k hδ) = 0 := by
  simp [guSum, guDv_zero hω]

lemma guSq_zero {ω : ℝ → ℝ} (hω : Measurable ω) : guSq ω (0 : H k hδ) = 0 := by
  simp [guSq, guDv_zero hω]

/-- A pointwise bound between weights. -/
lemma guDv_le_mul {ω ω' : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ s, |ω' s| ≤ B * |ω s|)
    (u : H k hδ) (p : idx k) : guDv ω' u p ≤ ENNReal.ofReal B * guDv ω u p := by
  unfold guDv
  rw [← Real.enorm_eq_ofReal hB, ← eLpNorm_const_smul]
  refine eLpNorm_mono fun x => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h x.1) (abs_nonneg _)

lemma guSum_le_mul {ω ω' : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ s, |ω' s| ≤ B * |ω s|)
    (u : H k hδ) : guSum ω' u ≤ ENNReal.ofReal B * guSum ω u := by
  rw [guSum, guSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => guDv_le_mul hB h u p

/-! ### Squares and sums -/

lemma guSq_le_guSum_sq (ω : ℝ → ℝ) (u : H k hδ) : guSq ω u ≤ guSum ω u ^ 2 := by
  rw [guSq, guSum, sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [sq]
  exact mul_le_mul_right (Finset.single_le_sum (f := fun p => guDv ω u p)
    (fun _ _ => bot_le) (Finset.mem_univ p)) _

lemma guSum_sq_le (ω : ℝ → ℝ) (u : H k hδ) :
    guSum ω u ^ 2 ≤ (Fintype.card (idx k) : ℝ≥0∞) * guSq ω u := by
  have := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset (idx k))
    (fun p => guDv ω u p) (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at this
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, Finset.card_univ] at this
  exact this

lemma ennreal_add_sq_le (A B : ℝ≥0∞) : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
  rcases eq_or_ne A ⊤ with rfl | hA
  · simp
  rcases eq_or_ne B ⊤ with rfl | hB
  · simp
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((A : ℝ) - B)]

/-! ### Translation -/

lemma dv_shH (c θ : ℝ) (u : H k hδ) (p : idx k) :
    dv (H.toSub (shH c θ u)) p =ᵐ[cyl] fun x => dv (H.toSub u) p (shT c θ x) :=
  dv_unique _ p (((dv_spec (H.toSub u) p).1.comp_shT (Lp.aestronglyMeasurable _)
      (dv_memLp _ p).1 c θ).congr_ae (val_shH c θ u).symm (ae_eq_refl _))
    ((dv_memLp _ p).comp_measurePreserving (measurePreserving_shT c θ))

/-- **Translation**: `‖u(s - c, t - θ)‖_{ω'} ≤ ‖u‖_ω` when `|ω'(s)| ≤ |ω(s - c)|`. -/
lemma guDv_shH {ω ω' : ℝ → ℝ} (hω : Measurable ω) {c : ℝ} (h : ∀ s, |ω' s| ≤ |ω (s - c)|)
    (θ : ℝ) (u : H k hδ) (p : idx k) : guDv ω' (shH c θ u) p ≤ guDv ω u p := by
  unfold guDv
  rw [eLpNorm_congr_ae (g := fun x => ω' x.1 * dv (H.toSub u) p (shT c θ x))
    (by filter_upwards [dv_shH c θ u p] with x hx; rw [hx])]
  calc _ ≤ eLpNorm ((fun x : ℝ × ℝ => ω x.1 * dv (H.toSub u) p x) ∘ shT c θ) 2 cyl :=
        eLpNorm_mono fun x => by
          simp only [Function.comp, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (h x.1) (abs_nonneg _)
    _ = _ := eLpNorm_comp_measurePreserving (aesm_guDv hω u p) (measurePreserving_shT c θ)

lemma guSum_shH {ω ω' : ℝ → ℝ} (hω : Measurable ω) {c : ℝ} (h : ∀ s, |ω' s| ≤ |ω (s - c)|)
    (θ : ℝ) (u : H k hδ) : guSum ω' (shH c θ u) ≤ guSum ω u :=
  Finset.sum_le_sum fun p _ => guDv_shH hω h θ u p

/-! ### Multipliers -/

/-- The constant of the multiplier estimate. -/
def multK (k : ℕ) (M : ℝ) : ℝ := Fintype.card (idx k) * (2 ^ k * M)

lemma multK_nonneg (k : ℕ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ multK k M := by
  unfold multK; positivity

lemma guDv_mulHL {ω ω' : ℝ → ℝ} (hω : Measurable ω) {χ : ℝ → ℝ} (hχ : Mult k χ) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ≤ k, ∀ s, |ω' s * iteratedDeriv i χ s| ≤ M * |ω s|)
    (u : H k hδ) (p : idx k) :
    guDv ω' (mulHL χ hχ u) p ≤ ENNReal.ofReal (2 ^ k * M) * guSum ω u := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  have hab : a + b ≤ k := mem_idx.1 hp
  set G := Gu (H.toSub u)
  have hd : dv (H.toSub (mulHL χ hχ u)) ⟨(a, b), hp⟩ =ᵐ[cyl] leib χ G a b :=
    dv_mulH hχ u ⟨(a, b), hp⟩
  have hGi : ∀ i ∈ Finset.range (a + 1), eLpNorm (fun x : ℝ × ℝ => ω x.1 * G (a - i) b x) 2 cyl ≤
      guSum ω u := fun i hi => by
    have hi' : a - i + b ≤ k := by omega
    have e : (fun x : ℝ × ℝ => ω x.1 * G (a - i) b x) =
        fun x : ℝ × ℝ => ω x.1 * dv (H.toSub u) ⟨(a - i, b), mem_idx.2 hi'⟩ x := by
      funext x; simp only [G, Gu_of _ hi']
    rw [e]
    exact Finset.single_le_sum (f := fun p => guDv ω u p) (fun _ _ => bot_le)
      (Finset.mem_univ _)
  set F : ℕ → ℝ × ℝ → ℝ := fun i x => ((a.choose i : ℝ) * M) * |ω x.1 * G (a - i) b x|
  have hF : ∀ i, AEStronglyMeasurable (F i) cyl := fun i => by
    by_cases hi : a - i + b ≤ k
    · have e : (fun x : ℝ × ℝ => ω x.1 * G (a - i) b x) =
          fun x : ℝ × ℝ => ω x.1 * dv (H.toSub u) ⟨(a - i, b), mem_idx.2 hi⟩ x := by
        funext x; simp only [G, Gu_of _ hi]
      have := (aesm_guDv hω u ⟨(a - i, b), mem_idx.2 hi⟩).norm.const_mul ((a.choose i : ℝ) * M)
      simp only [Real.norm_eq_abs] at this
      have e' : F i = fun x : ℝ × ℝ => ((a.choose i : ℝ) * M) *
          |ω x.1 * dv (H.toSub u) ⟨(a - i, b), mem_idx.2 hi⟩ x| := by
        funext x; simp only [F, G, Gu_of _ hi]
      rw [e']; exact this
    · have e : F i = fun _ => 0 := by
        funext x; simp [F, G, Gu, hi]
      rw [e]; exact aestronglyMeasurable_const
  unfold guDv
  rw [eLpNorm_congr_ae (g := fun x => ω' x.1 * leib χ G a b x)
    (by filter_upwards [hd] with x hx; rw [hx])]
  calc eLpNorm (fun x => ω' x.1 * leib χ G a b x) 2 cyl
      ≤ eLpNorm (∑ i ∈ Finset.range (a + 1), F i) 2 cyl := by
        refine eLpNorm_mono fun x => ?_
        rw [Finset.sum_apply, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (a := ∑ i ∈ Finset.range (a + 1), F i x)
            (Finset.sum_nonneg fun i _ => by positivity), leib, Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        have hik : i ≤ k := by have := Finset.mem_range.1 hi; omega
        have h1 := h i hik x.1
        have : ω' x.1 * ((a.choose i : ℝ) * (iteratedDeriv i χ x.1 * G (a - i) b x)) =
            (a.choose i : ℝ) * ((ω' x.1 * iteratedDeriv i χ x.1) * G (a - i) b x) := by ring
        have hc : (0 : ℝ) ≤ a.choose i := Nat.cast_nonneg _
        rw [this]
        calc |(a.choose i : ℝ) * ((ω' x.1 * iteratedDeriv i χ x.1) * G (a - i) b x)|
            = (a.choose i : ℝ) * (|ω' x.1 * iteratedDeriv i χ x.1| * |G (a - i) b x|) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hc]
          _ ≤ (a.choose i : ℝ) * ((M * |ω x.1|) * |G (a - i) b x|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) hc
          _ = F i x := by simp only [F]; rw [abs_mul]; ring
    _ ≤ ∑ i ∈ Finset.range (a + 1), eLpNorm (F i) 2 cyl :=
        eLpNorm_sum_le (fun i _ => hF i) (by norm_num)
    _ ≤ ∑ i ∈ Finset.range (a + 1), ENNReal.ofReal ((a.choose i : ℝ) * M) * guSum ω u := by
        refine Finset.sum_le_sum fun i hi => ?_
        have e : F i = ((a.choose i : ℝ) * M) • fun x : ℝ × ℝ => |ω x.1 * G (a - i) b x| := by
          funext x; simp [F]
        rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
        refine mul_le_mul_right ?_ _
        have : eLpNorm (fun x : ℝ × ℝ => |ω x.1 * G (a - i) b x|) 2 cyl =
            eLpNorm (fun x : ℝ × ℝ => ω x.1 * G (a - i) b x) 2 cyl := by
          simpa only [Real.norm_eq_abs] using
            eLpNorm_norm (f := fun x : ℝ × ℝ => ω x.1 * G (a - i) b x) (p := 2) (μ := cyl)
        rw [this]; exact hGi i hi
    _ = ENNReal.ofReal (2 ^ a * M) * guSum ω u := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
          ← Finset.sum_mul]
        congr 2
        rw [show (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ)) = 2 ^ a by
          exact_mod_cast Nat.sum_range_choose a]
    _ ≤ ENNReal.ofReal (2 ^ k * M) * guSum ω u := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hM

/-- **Multiplier estimate**: `‖χ u‖_{ω'} ≤ K_k(M) ‖u‖_ω` when `|ω' χ^{(i)}| ≤ M |ω|`, `i ≤ k`. -/
lemma guSum_mulHL {ω ω' : ℝ → ℝ} (hω : Measurable ω) {χ : ℝ → ℝ} (hχ : Mult k χ) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ≤ k, ∀ s, |ω' s * iteratedDeriv i χ s| ≤ M * |ω s|) (u : H k hδ) :
    guSum ω' (mulHL χ hχ u) ≤ ENNReal.ofReal (multK k M) * guSum ω u := by
  calc guSum ω' (mulHL χ hχ u) ≤ ∑ _p : idx k, ENNReal.ofReal (2 ^ k * M) * guSum ω u :=
        Finset.sum_le_sum fun p _ => guDv_mulHL hω hχ hM h u p
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, multK, ENNReal.ofReal_mul
          (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

end Weighted

/-! ## 2. The weights; the norms (4.7), (4.8) -/

section Weights

/-- `e^{d|s|}`, the weight of `H^{k,d}(ℝ × S¹)`. -/
def guE (d s : ℝ) : ℝ := Real.exp (d * |s|)

/-- `e^{d min(|s|, |s - R|)}`: on `[0, R]` the weight `e^{dR/2} e^{-d|s - R/2|}` of (4.7); off
`[0, R]` it grows as `e^{d|s|}` and `e^{d|s - R|}`. -/
def guZ (d R s : ℝ) : ℝ := Real.exp (d * min |s| |s - R|)

/-- `e^{d max(s, R - s)} = e^{dR/2} e^{d|s - R/2|}`, the weight of (4.8) times `e^{dR/2}`. -/
def guC (d R s : ℝ) : ℝ := Real.exp (d * max s (R - s))

lemma continuous_guE (d : ℝ) : Continuous (guE d) := by unfold guE; fun_prop
lemma continuous_guZ (d R : ℝ) : Continuous (guZ d R) := by
  unfold guZ; exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_abs.min (continuous_abs.comp (continuous_id.sub continuous_const))))
lemma continuous_guC (d R : ℝ) : Continuous (guC d R) := by
  unfold guC; exact Real.continuous_exp.comp (continuous_const.mul
    (continuous_id.max (continuous_const.sub continuous_id)))

lemma measurable_guE (d : ℝ) : Measurable (guE d) := (continuous_guE d).measurable
lemma measurable_guZ (d R : ℝ) : Measurable (guZ d R) := (continuous_guZ d R).measurable
lemma measurable_guC (d R : ℝ) : Measurable (guC d R) := (continuous_guC d R).measurable

lemma guE_pos (d s : ℝ) : 0 < guE d s := Real.exp_pos _
lemma guZ_pos (d R s : ℝ) : 0 < guZ d R s := Real.exp_pos _
lemma guC_pos (d R s : ℝ) : 0 < guC d R s := Real.exp_pos _

/-- On `Z_a = [0, R] × S¹`, `guZ d R = e^{dR/2} e^{-d|s - R/2|}`. -/
lemma guZ_eq_of_mem {d R s : ℝ} (hs : s ∈ Icc 0 R) :
    guZ d R s = Real.exp (d * R / 2) * Real.exp (-d * |s - R / 2|) := by
  rw [guZ, ← Real.exp_add]
  congr 1
  obtain ⟨h0, h1⟩ := hs
  rw [abs_of_nonneg h0, abs_of_nonpos (by linarith : s - R ≤ 0)]
  rcases le_total s (R / 2) with h | h
  · rw [min_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring

/-- `guC d R = e^{dR/2} e^{d|s - R/2|}`. -/
lemma guC_eq (d R s : ℝ) : guC d R s = Real.exp (d * R / 2) * Real.exp (d * |s - R / 2|) := by
  rw [guC, ← Real.exp_add]
  congr 1
  rcases le_total s (R / 2) with h | h
  · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]; ring

lemma exp_mul_le {d A B c : ℝ} (hd : 0 ≤ d) (h : A ≤ c + B) :
    Real.exp (d * A) ≤ Real.exp (d * c) * Real.exp (d * B) := by
  rw [← Real.exp_add, ← mul_add]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hd)

variable {d R s : ℝ} (hd : 0 ≤ d) (hR : 2 ≤ R)
include hd

lemma w1 : guZ d R s ≤ Real.exp (d * 0) * guE d s :=
  exp_mul_le hd (by rw [zero_add]; exact min_le_left _ _)
lemma w2 : guZ d R s ≤ Real.exp (d * 0) * guE d (s - R) :=
  exp_mul_le hd (by rw [zero_add]; exact min_le_right _ _)

include hR

lemma w3 (hs : R / 2 - 1 ≤ s) : guC d R s ≤ Real.exp (d * 2) * guE d s :=
  exp_mul_le hd (max_le (by linarith [le_abs_self s]) (by linarith [le_abs_self s]))
lemma w4 (hs : s ≤ R / 2 + 1) : guC d R s ≤ Real.exp (d * 2) * guE d (s - R) :=
  exp_mul_le hd (max_le (by linarith [neg_abs_le (s - R)]) (by linarith [neg_abs_le (s - R)]))
lemma w5 (hs : s ≤ R / 2 + 1) : guE d s ≤ Real.exp (d * 2) * guZ d R s := by
  refine exp_mul_le hd ?_
  rcases min_cases |s| |s - R| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · linarith
  · rcases le_total 0 s with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonpos (by linarith : s - R ≤ 0)]; linarith
    · rw [abs_of_nonpos h0, abs_of_nonpos (by linarith : s - R ≤ 0)]; linarith
lemma w6 (hs : R / 2 - 1 ≤ s) : guE d s ≤ Real.exp (d * 0) * guC d R s :=
  exp_mul_le hd (by rw [zero_add, abs_of_nonneg (by linarith)]; exact le_max_left _ _)
lemma w7 (hs : R / 2 - 1 ≤ s) : guE d (s - R) ≤ Real.exp (d * 2) * guZ d R s := by
  refine exp_mul_le hd ?_
  rcases min_cases |s| |s - R| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s)]
    rcases le_total 0 (s - R) with h0 | h0
    · rw [abs_of_nonneg h0]; linarith
    · rw [abs_of_nonpos h0]; linarith
  · linarith
lemma w8 (hs : s ≤ R / 2 + 1) : guE d (s - R) ≤ Real.exp (d * 0) * guC d R s :=
  exp_mul_le hd (by rw [zero_add, abs_of_nonpos (by linarith)]; linarith [le_max_right s (R - s)])

end Weights

section Norms

variable {k : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- The squared norm (4.8) on `C_a = ℝ × S¹` (Memoir p. 107), with weight `γ` and centre `R/2`:
`∑_{|α| ≤ k} ∫_{ℝ × S¹} |D^α p|² e^{2γ|s - R/2|} ds dt`. -/
def memoirNormSq48 (R γ : ℝ) (u : H k hδ) : ℝ≥0∞ := guSq (fun s => Real.exp (γ * |s - R / 2|)) u

/-- The squared norm (4.7) on `Z_a = [0, R] × S¹` (Memoir p. 107), evaluated on a representative
`u` on `ℝ × S¹`: `∑_{|α| ≤ k} ∫_{[0,R] × S¹} |D^α u|² e^{2γ|s - R/2|} ds dt`. -/
def memoirNormSq47 (R γ : ℝ) (u : H k hδ) : ℝ≥0∞ :=
  ∑ p : idx k, eLpNorm (fun x : ℝ × ℝ =>
    (Icc 0 R).indicator (fun s => Real.exp (γ * |s - R / 2|)) x.1 * dv (H.toSub u) p x) 2 cyl ^ 2

lemma guDv_const_mul {ω : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (u : H k hδ) (p : idx k) :
    guDv (fun s => c * ω s) u p = ENNReal.ofReal c * guDv ω u p := by
  unfold guDv
  rw [← Real.enorm_eq_ofReal hc, ← eLpNorm_const_smul]
  congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- `guSq (guC d R) = e^{dR} ‖·‖²_{k,d}` of (4.8). -/
lemma guSq_guC (d R : ℝ) (u : H k hδ) :
    guSq (guC d R) u = ENNReal.ofReal (Real.exp (d * R)) * memoirNormSq48 R d u := by
  have e : guC d R = fun s => Real.exp (d * R / 2) * Real.exp (d * |s - R / 2|) :=
    funext (guC_eq d R)
  rw [e, guSq, memoirNormSq48, guSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [guDv_const_mul (Real.exp_pos _).le, mul_pow, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  congr 3; push_cast; ring

/-- On a representative, `e^{dR} ‖·‖²_{k,-d}` of (4.7) is at most `guSq (guZ d R)`. -/
lemma memoirNormSq47_le (d R : ℝ) (u : H k hδ) :
    ENNReal.ofReal (Real.exp (d * R)) * memoirNormSq47 R (-d) u ≤ guSq (guZ d R) u := by
  rw [memoirNormSq47, guSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have h2 : ENNReal.ofReal (Real.exp (d * R)) = ENNReal.ofReal (Real.exp (d * R / 2)) ^ 2 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [h2, ← mul_pow, ← Real.enorm_eq_ofReal (Real.exp_pos _).le, ← eLpNorm_const_smul]
  refine ENNReal.pow_le_pow_left (eLpNorm_mono fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (dv (H.toSub u) p x))
  by_cases hx : x.1 ∈ Icc 0 R
  · rw [indicator_of_mem hx, guZ_eq_of_mem hx, abs_mul]
  · rw [indicator_of_notMem hx, abs_zero, mul_zero]; exact abs_nonneg _

lemma guDv_guE (u : H k hδ) (p : idx k) :
    guDv (guE δ) u p = ENNReal.ofReal ‖wdv (H.toSub u) p‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), guDv]
  exact eLpNorm_congr_ae (coeFn_wdv (H.toSub u) p).symm

lemma ofReal_norm_le_guSum (u : H k hδ) : ENNReal.ofReal ‖u‖ ≤ guSum (guE δ) u := by
  refine (ENNReal.ofReal_le_ofReal (norm_H_le_sum u)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _), guSum]
  exact (Finset.sum_congr rfl fun p _ => (guDv_guE u p).symm).le

lemma guSum_guE_le (u : H k hδ) :
    guSum (guE δ) u ≤ (Fintype.card (idx k) : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  calc guSum (guE δ) u ≤ ∑ _p : idx k, ENNReal.ofReal ‖u‖ :=
        Finset.sum_le_sum fun p _ => by rw [guDv_guE]; exact ENNReal.ofReal_le_ofReal (norm_wdv_le u p)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The weights `guZ`, `guC` are bounded by a multiple of `e^{δ|s|}`, so the norms are finite. -/
lemma guSq_lt_top {ω : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ s, |ω s| ≤ B * |guE δ s|)
    (u : H k hδ) : guSq ω u < ⊤ := by
  refine ENNReal.sum_lt_top.2 fun p _ => ENNReal.pow_lt_top ?_
  refine (guDv_le_mul hB h u p).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  rw [guDv_guE]; exact ENNReal.ofReal_lt_top

end Norms

/-! ## 3. Uniform bounds on the multipliers `F(β_a)` -/

section Bounds

variable {β : ℝ → ℝ} (hβ : IsCutoff β)
include hβ

/-- The derivatives of `F(β_a(s)) = F(β(s - R/2))` are bounded independently of `R`. -/
lemma bound_Fβa {F : ℝ → ℝ} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ R, ∀ i ≤ k, ∀ s, |iteratedDeriv i (fun s => F (βa β R s)) s| ≤ C := by
  obtain ⟨C, hC⟩ := (multβ hβ 0 hF k).bdd
  refine ⟨max C 0, le_max_right _ _, fun R i hi s => ?_⟩
  have e : (fun s => F (βa β R s)) = fun s => (fun s => F (βa β 0 s)) (s - R / 2) := by
    funext s; simp [βa]
  rw [e, iteratedDeriv_comp_sub_const i (fun s => F (βa β 0 s)) (R / 2)]
  exact (hC i hi _).trans (le_max_left _ _)

lemma iteratedDeriv_Fβa_hi {F : ℝ → ℝ} (hF0 : F 0 = 0) {R s : ℝ} (hs : R / 2 + 1 < s) (i : ℕ) :
    iteratedDeriv i (fun s => F (βa β R s)) s = 0 := by
  have h : (fun s => F (βa β R s)) =ᶠ[𝓝 s] 0 := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    rw [Pi.zero_apply, βa_zero hβ (le_of_lt hy), hF0]
  rw [h.iteratedDeriv_eq i]; simp

lemma iteratedDeriv_Fβa_lo {F : ℝ → ℝ} (hF1 : F 1 = 0) {R s : ℝ} (hs : s < R / 2 - 1) (i : ℕ) :
    iteratedDeriv i (fun s => F (βa β R s)) s = 0 := by
  have h : (fun s => F (βa β R s)) =ᶠ[𝓝 s] 0 := by
    filter_upwards [Iio_mem_nhds hs] with y hy
    rw [Pi.zero_apply, βa_one hβ (le_of_lt hy), hF1]
  rw [h.iteratedDeriv_eq i]; simp

end Bounds

/-- The hypothesis of `guSum_mulHL`, from a bound `C` on the derivatives and a weight comparison
`ω' ≤ B ω` where the derivatives do not vanish. -/
lemma multHyp {ω ω' χ : ℝ → ℝ} {k : ℕ} {C B : ℝ} (hC0 : 0 ≤ C) (hB : 0 ≤ B)
    (hC : ∀ i ≤ k, ∀ s, |iteratedDeriv i χ s| ≤ C) (hω : ∀ s, 0 ≤ ω' s)
    (h : ∀ i ≤ k, ∀ s, iteratedDeriv i χ s = 0 ∨ ω' s ≤ B * ω s) :
    ∀ i ≤ k, ∀ s, |ω' s * iteratedDeriv i χ s| ≤ (C * B) * |ω s| := by
  intro i hi s
  rcases h i hi s with h0 | h1
  · rw [h0, mul_zero, abs_zero]; positivity
  · rw [abs_mul, abs_of_nonneg (hω s)]
    have hBω : 0 ≤ B * ω s := (hω s).trans h1
    calc ω' s * |iteratedDeriv i χ s| ≤ (B * ω s) * C :=
          mul_le_mul h1 (hC i hi s) (abs_nonneg _) hBω
      _ = C * (B * ω s) := by ring
      _ ≤ C * (B * |ω s|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hB) hC0
      _ = (C * B) * |ω s| := by ring

/-! ## 4. Representatives and quotient norms -/

/-- A bound valid on every representative passes to the quotient norm. -/
lemma le_ofReal_of_reps {M : Type*} [SeminormedAddCommGroup M] [Module ℝ M] {S : Submodule ℝ M}
    (ξ : M ⧸ S) {X : ℝ≥0∞} {f : ℝ → ℝ} (hf : Continuous f) (hmono : MonotoneOn f (Ici 0))
    (h : ∀ a : M, Submodule.Quotient.mk a = ξ → X ≤ ENNReal.ofReal (f ‖a‖)) :
    X ≤ ENNReal.ofReal (f ‖ξ‖) := by
  have hc : Continuous fun ε : ℝ => ENNReal.ofReal (f (‖ξ‖ + ε)) :=
    ENNReal.continuous_ofReal.comp (hf.comp (continuous_const.add continuous_id))
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (f (‖ξ‖ + ε))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (f ‖ξ‖))) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  obtain ⟨a, ha, hlt⟩ := Submodule.Quotient.norm_mk_lt ξ hε
  exact (h a ha).trans (ENNReal.ofReal_le_ofReal
    (hmono (mem_Ici.2 (norm_nonneg a)) (mem_Ici.2 (by positivity)) hlt.le))

end GWMemoir.Neck
