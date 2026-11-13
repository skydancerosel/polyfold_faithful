import Mathlib

/-!
# Weighted product integrals on `Lᵖ`, and Bonic–Frampton for even `p`

2021 Theorem 5.5.5 (1), p. 230 (preprint Theorem 5.32 (1)), cited from Bonic–Frampton: on `Lᵖ`
with `p` an even integer, `‖·‖ᵖ` is of class `C^∞`.

For an exponent `P` and a weight `w ∈ L^q` with `q⁻¹ + m P⁻¹ = 1`, the map
`(h₁, …, hₘ) ↦ ∫ w ∏ hᵢ` is a continuous `m`-linear form on `L^P` of norm at most `‖w‖_q`
(`wMul`, generalized Hölder).  For `p = 2k` and `w = 1`, `q = ∞`, its value on the diagonal is
`∫ f^{2k} = ‖f‖^{2k}`, so `‖·‖^{2k}` is a continuous homogeneous polynomial and `C^∞`
(`theorem_5_5_5_even`).  The general case of Theorem 5.5.5 uses the same forms with weights
`gⱼ(f)` (`GapP1_BonicFrampton.lean`).
-/

open MeasureTheory Finset Function
open scoped ENNReal NNReal

noncomputable section

namespace Polyfold

namespace BonicFrampton

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Hölder's inequality for finite products**: `‖∏ fᵢ‖_r ≤ ∏ ‖fᵢ‖_{pᵢ}` with
`r⁻¹ = Σ pᵢ⁻¹`. -/
lemma eLpNorm_prod_le {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) (p : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => ∏ i ∈ s, f i x) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simp only [prod_empty, sum_empty, ENNReal.inv_zero]
    refine (eLpNorm_le_of_ae_bound (C := 1) (ae_of_all _ fun x => by simp)).trans ?_
    simp
  | cons i s hi ih =>
    simp only [prod_cons, sum_cons]
    have hs : AEStronglyMeasurable (fun x => ∏ j ∈ s, f j x) μ :=
      Finset.aestronglyMeasurable_fun_prod s fun j hj => hf j (mem_cons_of_mem hj)
    have : ENNReal.HolderTriple (p i) (∑ j ∈ s, (p j)⁻¹)⁻¹ ((p i)⁻¹ + ∑ j ∈ s, (p j)⁻¹)⁻¹ :=
      ⟨by simp⟩
    calc eLpNorm (fun x => f i x * ∏ j ∈ s, f j x) ((p i)⁻¹ + ∑ j ∈ s, (p j)⁻¹)⁻¹ μ
        ≤ (1 : ℝ≥0) * eLpNorm (f i) (p i) μ * eLpNorm (fun x => ∏ j ∈ s, f j x)
            (∑ j ∈ s, (p j)⁻¹)⁻¹ μ :=
          eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (hf i (mem_cons_self i s)) hs (· * ·) 1
            (ae_of_all _ fun x => by simp [nnnorm_mul])
      _ ≤ eLpNorm (f i) (p i) μ * ∏ j ∈ s, eLpNorm (f j) (p j) μ := by
          rw [ENNReal.coe_one, one_mul]
          gcongr
          exact ih fun j hj => hf j (mem_cons_of_mem hj)

variable {P : ℝ≥0∞} [Fact (1 ≤ P)]

omit [Fact (1 ≤ P)] in
lemma inv_prod_exponent (m : ℕ) : (∑ _i : Fin m, P⁻¹)⁻¹ = ((m : ℝ≥0∞) * P⁻¹)⁻¹ := by
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Fact (1 ≤ P)] in
/-- The product of `m` functions of `L^P` lies in `L^{P/m}`. -/
lemma memLp_prod {m : ℕ} (h : Fin m → Lp ℝ P μ) :
    MemLp (fun x => ∏ i, (h i : α → ℝ) x) ((m : ℝ≥0∞) * P⁻¹)⁻¹ μ := by
  have := MemLp.prod' (s := Finset.univ) (f := fun i => (h i : α → ℝ)) (p := fun _ => P) (μ := μ)
    fun i _ => Lp.memLp (h i)
  rwa [inv_prod_exponent] at this

lemma eLpNorm_prod_le_prod_norm {m : ℕ} (h : Fin m → Lp ℝ P μ) :
    eLpNorm (fun x => ∏ i, (h i : α → ℝ) x) ((m : ℝ≥0∞) * P⁻¹)⁻¹ μ ≤
      ENNReal.ofReal (∏ i, ‖h i‖) := by
  have := eLpNorm_prod_le (μ := μ) Finset.univ (fun i => (h i : α → ℝ)) (fun _ => P)
    fun i _ => (Lp.memLp (h i)).1
  rw [inv_prod_exponent] at this
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => norm_nonneg _]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

variable (μ P) in
/-- The weighted product integral `∫ w ∏ hᵢ`. -/
def wMulFun (m : ℕ) (w : α → ℝ) (h : Fin m → Lp ℝ P μ) : ℝ :=
  ∫ x, w x * ∏ i, (h i : α → ℝ) x ∂μ

omit [Fact (1 ≤ P)] in
lemma holderTriple_of {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) :
    ENNReal.HolderTriple q ((m : ℝ≥0∞) * P⁻¹)⁻¹ 1 :=
  ⟨by rw [inv_inv, hq, inv_one]⟩

omit [Fact (1 ≤ P)] in
lemma integrable_wMul {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w : α → ℝ}
    (hw : MemLp w q μ) (h : Fin m → Lp ℝ P μ) :
    Integrable (fun x => w x * ∏ i, (h i : α → ℝ) x) μ := by
  have := holderTriple_of hq
  exact memLp_one_iff_integrable.1 ((memLp_prod h).mul' hw)

lemma eLpNorm_wMul_le {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w : α → ℝ}
    (hw : MemLp w q μ) (h : Fin m → Lp ℝ P μ) :
    eLpNorm (fun x => w x * ∏ i, (h i : α → ℝ) x) 1 μ ≤
      eLpNorm w q μ * ENNReal.ofReal (∏ i, ‖h i‖) := by
  have := holderTriple_of hq
  calc eLpNorm (fun x => w x * ∏ i, (h i : α → ℝ) x) 1 μ
      ≤ (1 : ℝ≥0) * eLpNorm w q μ * eLpNorm (fun x => ∏ i, (h i : α → ℝ) x)
          ((m : ℝ≥0∞) * P⁻¹)⁻¹ μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hw.1 (memLp_prod h).1 (· * ·) 1
          (ae_of_all _ fun x => by simp [nnnorm_mul])
    _ ≤ eLpNorm w q μ * ENNReal.ofReal (∏ i, ‖h i‖) := by
        rw [ENNReal.coe_one, one_mul]
        gcongr
        exact eLpNorm_prod_le_prod_norm h

/-- `|∫ F| ≤ ‖F‖₁`. -/
lemma norm_integral_le_eLpNorm_one {F : α → ℝ} (hF : Integrable F μ) :
    ‖∫ x, F x ∂μ‖ ≤ (eLpNorm F 1 μ).toReal := by
  refine (norm_integral_le_integral_norm F).trans (le_of_eq ?_)
  rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hF.1]

lemma norm_wMulFun_le {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w : α → ℝ}
    (hw : MemLp w q μ) (h : Fin m → Lp ℝ P μ) :
    ‖wMulFun μ P m w h‖ ≤ (eLpNorm w q μ).toReal * ∏ i, ‖h i‖ := by
  refine (norm_integral_le_eLpNorm_one (integrable_wMul hq hw h)).trans ?_
  have h1 := eLpNorm_wMul_le hq hw h
  have h2 : eLpNorm w q μ * ENNReal.ofReal (∏ i, ‖h i‖) ≠ ⊤ :=
    ENNReal.mul_ne_top hw.eLpNorm_ne_top ENNReal.ofReal_ne_top
  calc (eLpNorm (fun x => w x * ∏ i, (h i : α → ℝ) x) 1 μ).toReal
      ≤ (eLpNorm w q μ * ENNReal.ofReal (∏ i, ‖h i‖)).toReal := ENNReal.toReal_mono h2 h1
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (prod_nonneg fun i _ => norm_nonneg _)]

omit [Fact (1 ≤ P)] in
lemma prod_update_apply {m : ℕ} [DecidableEq (Fin m)] (h : Fin m → Lp ℝ P μ) (i : Fin m)
    (v : Lp ℝ P μ) (x : α) :
    ∏ j, (update h i v j : α → ℝ) x = (v : α → ℝ) x * ∏ j ∈ univ.erase i, (h j : α → ℝ) x := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
  congr 1
  · simp
  · refine prod_congr rfl fun j hj => ?_
    rw [update_of_ne (ne_of_mem_erase hj)]

/-- **The weighted product form** `(h₁, …, hₘ) ↦ ∫ w ∏ hᵢ`, a continuous `m`-linear form on
`L^P` of norm at most `‖w‖_q`, for `w ∈ L^q` with `q⁻¹ + m P⁻¹ = 1` (generalized Hölder). -/
def wMul (m : ℕ) {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w : α → ℝ} (hw : MemLp w q μ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => Lp ℝ P μ) ℝ :=
  MultilinearMap.mkContinuous
    { toFun := wMulFun μ P m w
      map_update_add' := fun h i a b => by
        simp only [wMulFun]
        rw [← integral_add (integrable_wMul hq hw _) (integrable_wMul hq hw _)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add a b] with x hx
        simp only [prod_update_apply, hx, Pi.add_apply]
        ring
      map_update_smul' := fun h i c a => by
        simp only [wMulFun, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c a] with x hx
        simp only [prod_update_apply, hx, Pi.smul_apply, smul_eq_mul]
        ring }
    (eLpNorm w q μ).toReal fun h => norm_wMulFun_le hq hw h

lemma wMul_apply {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w : α → ℝ} (hw : MemLp w q μ)
    (h : Fin m → Lp ℝ P μ) : wMul m hq hw h = ∫ x, w x * ∏ i, (h i : α → ℝ) x ∂μ :=
  rfl

lemma norm_wMul_le {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w : α → ℝ} (hw : MemLp w q μ) :
    ‖wMul m hq hw‖ ≤ (eLpNorm w q μ).toReal :=
  MultilinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

lemma wMul_sub {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w w' : α → ℝ} (hw : MemLp w q μ)
    (hw' : MemLp w' q μ) : wMul m hq (hw.sub hw') = wMul m hq hw - wMul m hq hw' := by
  ext h
  simp only [sub_apply, wMul_apply]
  rw [← integral_sub (integrable_wMul hq hw h) (integrable_wMul hq hw' h)]
  congr 1
  funext x
  simp only [Pi.sub_apply]
  ring

lemma norm_wMul_sub_le {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w w' : α → ℝ}
    (hw : MemLp w q μ) (hw' : MemLp w' q μ) :
    ‖wMul m hq hw - wMul m hq hw'‖ ≤ (eLpNorm (w - w') q μ).toReal := by
  rw [← wMul_sub hq hw hw']
  exact norm_wMul_le hq _

lemma wMul_congr {m : ℕ} {q : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1) {w w' : α → ℝ} (hw : MemLp w q μ)
    (hw' : MemLp w' q μ) (hww' : w =ᵐ[μ] w') : wMul m hq hw = wMul m hq hw' := by
  ext h
  simp only [wMul_apply]
  refine integral_congr_ae ?_
  filter_upwards [hww'] with x hx
  rw [hx]

/-- **Currying the first variable**: `(∫ w h ∏ kᵢ)` is the `m`-linear form of the weight `w h`. -/
lemma wMul_curryLeft {m : ℕ} {q q' : ℝ≥0∞} (hq : q⁻¹ + m * P⁻¹ = 1)
    (hq' : q'⁻¹ + (m + 1 : ℕ) * P⁻¹ = 1) {w : α → ℝ} (hw : MemLp w q' μ) (v : Lp ℝ P μ)
    (hwv : MemLp (fun x => w x * (v : α → ℝ) x) q μ) :
    (wMul (m + 1) hq' hw).curryLeft v = wMul m hq hwv := by
  ext k
  simp only [ContinuousMultilinearMap.curryLeft_apply, wMul_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  congr 1
  funext x
  ring

/-! ### Bonic–Frampton for even `p` -/

/-- `‖f‖ᵖ = ∫ |f|ᵖ` on `Lᵖ`, `0 < p < ∞`. -/
lemma norm_rpow_eq_integral {p : ℝ} (hp : 0 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖ ^ p = ∫ x, |(f : α → ℝ) x| ^ p ∂μ := by
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (by positivity)]
  simp only [Real.norm_eq_abs]
  exact Real.rpow_inv_rpow (integral_nonneg fun x => by positivity) hp.ne'

/-- **2021 Theorem 5.5.5 (1), p. 230 (preprint 5.32 (1)), Bonic–Frampton for even `p`**: on
`Lᵖ(μ)` with `p = 2k` an even integer, `f ↦ ‖f‖ᵖ` is `C^∞`.  It is the diagonal of the continuous
`2k`-linear form `(h₁, …, h_{2k}) ↦ ∫ ∏ hᵢ`. -/
theorem theorem_5_5_5_even (k : ℕ) (hk : 0 < k) [Fact (1 ≤ ENNReal.ofReal (2 * k))] :
    ContDiff ℝ (⊤ : ℕ∞) (fun f : Lp ℝ (ENNReal.ofReal (2 * k)) μ => ‖f‖ ^ ((2 * k : ℕ) : ℝ)) := by
  set P := ENNReal.ofReal (2 * k) with hPdef
  have hP : P = ((2 * k : ℕ) : ℝ≥0∞) := by
    rw [hPdef]; exact_mod_cast ENNReal.ofReal_natCast (2 * k)
  have hq : (⊤ : ℝ≥0∞)⁻¹ + ((2 * k : ℕ) : ℝ≥0∞) * P⁻¹ = 1 := by
    rw [ENNReal.inv_top, zero_add, hP]
    exact ENNReal.mul_inv_cancel (by simp; omega) (ENNReal.natCast_ne_top _)
  have hw : MemLp (fun _ : α => (1 : ℝ)) ⊤ μ := memLp_top_const 1
  set Φ := wMul (μ := μ) (P := P) (2 * k) hq hw
  set D : Lp ℝ P μ →L[ℝ] (Fin (2 * k) → Lp ℝ P μ) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ (Lp ℝ P μ)
  have heq : (fun f : Lp ℝ P μ => ‖f‖ ^ ((2 * k : ℕ) : ℝ)) = fun f => Φ (D f) := by
    funext f
    have h2k : (0 : ℝ) < 2 * (k : ℝ) := by positivity
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
    have habs : ∀ a : ℝ, |a| ^ (2 * (k : ℝ)) = a ^ (2 * k) := fun a => by
      rw [← hcast, Real.rpow_natCast, (even_two_mul k).pow_abs]
    rw [hcast, norm_rpow_eq_integral h2k f, wMul_apply]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [D, ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply, prod_const,
      card_univ, Fintype.card_fin, one_mul]
    exact habs _
  rw [heq]
  exact Φ.contDiff.comp D.contDiff

end BonicFrampton

end Polyfold
