import GWMemoir.NeckModelsSolve

/-!
# Memoir Proposition 4.15: `∂_s + J ∂_t` with antipodal asymptotic constants

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Proposition 4.15 (p. 109),
in the form without the gluing parameter: after the translation `s ↦ s + R/2` of p. 170 the
cylinder `C_a` with the centred norm (4.8) and the cut-off `β_a(s) = β(s - R/2)` becomes
`ℝ × S¹` with the norm of `H^{m,δ}` (weight `e^{δ|s|}`) and the cut-off `β`.

* `HcSp m hδ n = ℝⁿ × (H^{m,δ})ⁿ`: the pairs `(c, r)`, representing
  `p = (1 - 2β(s)) c + r`, with the antipodal constants `p(+∞) = c = -p(-∞)` (the memoir's
  `p∞`; `r = p - (1 - 2β) p∞` is its `p̂`).
* `dbarCL`: `∂_s + J ∂_t : (c, r) ↦ (∂_s + J ∂_t) r - 2β'(s) c`, from `H_c^{m+1,δ}` to
  `(H^{m,δ})ⁿ`.
* `intL`: `u ↦ ∫ u` on `H^{m,δ}`, `δ > 0`; it vanishes on `∂_s`, `∂_t` (`intL_dsH`,
  `intL_dtH`) and `∫ β' = -1`.  Hence **`const_eq_intL`**: `2 c_k = ∫ (∂̄(c, r))_k` (mode `0`),
  and `|c| ≤ C ‖∂̄(c, r)‖`.
* **`cyl_dbar_estimate_C`**: `‖(c, r)‖ ≤ C ‖∂̄(c, r)‖` (`neck_estimate` and the bound on `c`).
* **`cyl_dbar_iso_C`**: for `0 < δ < 2π` and `J² = -1`, `∂̄ : H_c^{m+1,δ} → (H^{m,δ})ⁿ` is an
  isomorphism of Banach spaces (`cylDbarEquiv`).  Ontoness: the range is closed by the estimate
  and contains the test tuples (`exists_smooth_solution`, the Cauchy transform), which are dense.
* **`memoir_proposition_4_15`**: on the levels `H_c^{3+m,δ_m} → H^{2+m,δ_m}`, `0 < δ_m < 2π`:
  bijective, with `C_m⁻¹ ‖ξ‖ ≤ ‖∂̄ξ‖ ≤ C_m ‖ξ‖`, and the level operators are restrictions of
  each other (`dbarCL_incl`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Real NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev GWMemoir.Neck

noncomputable section

namespace GWMemoir

/-! ## 1. The derivative of the cut-off -/

section Cut

variable {β : ℝ → ℝ}

lemma deriv_cut_eq_zero (hβ : IsCutoff β) {s : ℝ} (hs : 2 ≤ |s|) : deriv β s = 0 := by
  rcases le_abs'.1 hs with h | h
  · have : β =ᶠ[𝓝 s] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds (show s < -1 by linarith)] with x hx
      exact hβ.one_of_le x (le_of_lt hx)
    rw [this.deriv_eq, deriv_const]
  · have : β =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (show 1 < s by linarith)] with x hx
      exact hβ.zero_of_ge (le_of_lt hx)
    rw [this.deriv_eq, deriv_const]

/-- `β'(s)`, a test function on the cylinder. -/
lemma isTest_dcut (hβ : IsCutoff β) : IsTest (fun x : ℝ × ℝ => deriv β x.1) :=
  isTest_of_s (contDiff_infty_iff_deriv.1 hβ.smooth).2 (fun _ hs => deriv_cut_eq_zero hβ hs)

/-- `∫_ℝ β' = -1`. -/
lemma integral_deriv_cut (hβ : IsCutoff β) : ∫ s, deriv β s = -1 := by
  have hd : Differentiable ℝ β := hβ.smooth.differentiable (by simp)
  have hc : Continuous (deriv β) := (contDiff_infty_iff_deriv.1 hβ.smooth).2.continuous
  have hsupp : ∀ s ∉ Icc (-2 : ℝ) 2, deriv β s = 0 := fun s hs => by
    refine deriv_cut_eq_zero hβ ?_
    simp only [mem_Icc, not_and_or, not_le] at hs
    rcases hs with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) (hc.intervalIntegrable _ _),
    hβ.zero_of_ge (by norm_num), hβ.one_of_le _ (by norm_num)]
  norm_num

/-- `∫_{ℝ × S¹} β'(s) = -1`. -/
lemma integral_dcut_cyl (hβ : IsCutoff β) : ∫ x, deriv β x.1 ∂cyl = -1 := by
  rw [cyl, integral_fun_fst, integral_deriv_cut hβ]
  simp [Measure.real]

end Cut

/-! ## 2. The integral over the cylinder -/

section Int

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma integrable_exp_abs {a : ℝ} (ha : 0 < a) : Integrable (fun s : ℝ => Real.exp (-a * |s|)) := by
  have hg : Integrable ((Ici (0 : ℝ)).indicator fun s => Real.exp (-a * s)) :=
    (integrable_indicator_iff measurableSet_Ici).2
      ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 (exp_neg_integrableOn_Ioi 0 ha))
  refine (hg.add hg.comp_neg).mono' (by fun_prop) (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := Set.indicator_nonneg (s := Ici (0 : ℝ)) (f := fun s => Real.exp (-a * s))
    (fun _ _ => (Real.exp_pos _).le) s
  have h2 := Set.indicator_nonneg (s := Ici (0 : ℝ)) (f := fun s => Real.exp (-a * s))
    (fun _ _ => (Real.exp_pos _).le) (-s)
  simp only [Pi.add_apply]
  rcases le_total 0 s with h | h
  · rw [Set.indicator_of_mem (show s ∈ Ici (0 : ℝ) from h), abs_of_nonneg h]; linarith
  · rw [Set.indicator_of_mem (show -s ∈ Ici (0 : ℝ) by simp; linarith), abs_of_nonpos h]
    simp only [mul_neg] at *; linarith

lemma memLp_wt_neg {δ : ℝ} (h0 : 0 < δ) : MemLp (wt (-δ)) 2 cyl := by
  have h1 : MemLp (fun s : ℝ => Real.exp (-δ * |s|)) 2 volume := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    have : (fun s : ℝ => Real.exp (-δ * |s|) ^ 2) = fun s => Real.exp (-(2 * δ) * |s|) := by
      funext s; rw [← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact integrable_exp_abs (by linarith)
  exact h1.comp_fst _

variable (m hδ) in
/-- `u ↦ ∫_{ℝ × S¹} u`, a continuous functional on `H^{m,δ}` for `δ > 0`. -/
def intL (h0 : 0 < δ) : H m hδ →L[ℝ] ℝ :=
  (pairing (wt (-δ)) (memLp_wt_neg h0)).comp (wdvCLM m hδ (CylinderSobolev.idx0 m))

lemma intL_toH (h0 : 0 < δ) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    intL m hδ h0 (toH m hδ hφ) = ∫ x, φ x ∂cyl := by
  simp only [intL, ContinuousLinearMap.comp_apply, pairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_wdv (H.toSub (toH m hδ hφ)) (CylinderSobolev.idx0 m),
    dv_idx0 (H.toSub (toH m hδ hφ)), val_toH (m := m) (hδ := hδ) hφ] with x h1 h2 h3
  change wdvCLM m hδ (CylinderSobolev.idx0 m) (toH m hδ hφ) x * wt (-δ) x = φ x
  change wdv (H.toSub (toH m hδ hφ)) (CylinderSobolev.idx0 m) x * wt (-δ) x = φ x
  rw [h1, h2]
  change wt δ x * (H.val (toH m hδ hφ) : ℝ × ℝ → ℝ) x * wt (-δ) x = φ x
  rw [h3, mul_comm (wt δ x), mul_assoc, mul_comm (wt δ x), wt_neg_mul, mul_one]

lemma intL_dsH (h0 : 0 < δ) (u : H (m + 1) hδ) : intL m hδ h0 (dsH m hδ u) = 0 := by
  have h := Continuous.ext_on (dense_test (m + 1) hδ)
    ((intL m hδ h0).comp (dsH m hδ)).continuous continuous_const
    (f := fun u => intL m hδ h0 (dsH m hδ u)) (g := fun _ => 0) (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [dsH_toH, intL_toH, hφ.integral_ds])
  exact congrFun h u

lemma intL_dtH (h0 : 0 < δ) (u : H (m + 1) hδ) : intL m hδ h0 (dtH m hδ u) = 0 := by
  have h := Continuous.ext_on (dense_test (m + 1) hδ)
    ((intL m hδ h0).comp (dtH m hδ)).continuous continuous_const
    (f := fun u => intL m hδ h0 (dtH m hδ u)) (g := fun _ => 0) (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [dtH_toH, intL_toH, hφ.integral_dt])
  exact congrFun h u

end Int

/-! ## 3. The operator on `H_c^{m+1,δ}` -/

section Op

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- `H_c^{m,δ}(ℝ × S¹, ℝⁿ)`: pairs `(c, r)`, `c ∈ ℝⁿ` the asymptotic constant at `+∞` and
`r = p - (1 - 2β(s)) c ∈ (H^{m,δ})ⁿ`; the map is `p = (1 - 2β(s)) c + r`. -/
abbrev HcSp (m : ℕ) (hδ : 0 ≤ δ) (n : ℕ) := (Fin n → ℝ) × (Fin n → H m hδ)

/-- `∂_s + J ∂_t` on tuples, as a bounded operator. -/
def crOpWL (m : ℕ) (hδ : 0 ≤ δ) (J : Fin n → Fin n → ℝ) :
    (Fin n → H (m + 1) hδ) →L[ℝ] (Fin n → H m hδ) :=
  ContinuousLinearMap.pi fun k => (dsH m hδ).comp (ContinuousLinearMap.proj k) +
    ∑ l, J k l • (dtH m hδ).comp (ContinuousLinearMap.proj l)

lemma crOpWL_apply (m : ℕ) (g : Fin n → H (m + 1) hδ) (k : Fin n) :
    crOpWL m hδ J g k = crOpW m hδ J g k := by
  simp [crOpWL, crOpW]

/-- `c ↦ -2 β'(s) c`. -/
def cstLNeck (m : ℕ) (hδ : 0 ≤ δ) (n : ℕ) (hβ : IsCutoff β) : (Fin n → ℝ) →L[ℝ] (Fin n → H m hδ) :=
  ContinuousLinearMap.pi fun k => (-2 : ℝ) • (ContinuousLinearMap.proj k).smulRight
    (toH m hδ (isTest_dcut hβ))

lemma cstL_apply (m : ℕ) (hβ : IsCutoff β) (c : Fin n → ℝ) (k : Fin n) :
    cstLNeck m hδ n hβ c k = (-2 * c k) • toH m hδ (isTest_dcut hβ) := by
  simp [cstLNeck, mul_smul]

/-- **`∂_s + J ∂_t : H_c^{m+1,δ} → (H^{m,δ})ⁿ`**, `(c, r) ↦ (∂_s + J ∂_t) r - 2 β'(s) c`: the
operator on `p = (1 - 2β(s)) c + r`. -/
def dbarCL (m : ℕ) (hδ : 0 ≤ δ) (J : Fin n → Fin n → ℝ) (hβ : IsCutoff β) :
    HcSp (m + 1) hδ n →L[ℝ] (Fin n → H m hδ) :=
  ContinuousLinearMap.coprod (cstLNeck m hδ n hβ) (crOpWL m hδ J)

lemma dbarCL_apply (m : ℕ) (hβ : IsCutoff β) (x : HcSp (m + 1) hδ n) (k : Fin n) :
    dbarCL m hδ J hβ x k = crOpW m hδ J x.2 k - (2 * x.1 k) • toH m hδ (isTest_dcut hβ) := by
  simp only [dbarCL, ContinuousLinearMap.coprod_apply, Pi.add_apply, cstL_apply, crOpWL_apply]
  rw [neg_mul, neg_smul, add_comm, sub_eq_add_neg]

/-- **The constant through mode `0`**: `∫ (∂̄(c, r))_k = 2 c_k`. -/
theorem const_eq_intL (hβ : IsCutoff β) (h0 : 0 < δ) (m : ℕ) (x : HcSp (m + 1) hδ n)
    (k : Fin n) : intL m hδ h0 (dbarCL m hδ J hβ x k) = 2 * x.1 k := by
  rw [dbarCL_apply, map_sub, map_smul, intL_toH, integral_dcut_cyl hβ, crOpW, map_add, map_sum,
    intL_dsH]
  simp [intL_dtH]

/-- **`|c| ≤ C ‖∂̄(c, r)‖`**. -/
theorem norm_const_le (hβ : IsCutoff β) (h0 : 0 < δ) (m : ℕ) (x : HcSp (m + 1) hδ n) :
    ‖x.1‖ ≤ ‖intL m hδ h0‖ * ‖dbarCL m hδ J hβ x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have h := const_eq_intL (J := J) hβ h0 m x k
  have hb := (intL m hδ h0).le_opNorm (dbarCL m hδ J hβ x k)
  have hk := norm_le_pi_norm (dbarCL m hδ J hβ x) k
  rw [h, Real.norm_eq_abs, abs_mul, abs_two] at hb
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (x.1 k), norm_nonneg (intL m hδ h0), norm_nonneg (dbarCL m hδ J hβ x),
    mul_le_mul_of_nonneg_left hk (norm_nonneg (intL m hδ h0))]

/-- **The estimate on `H_c^{m+1,δ}`**: for `0 < δ < 2π` and `J² = -1` there is `C` with
`‖(c, r)‖ ≤ C ‖(∂_s + J ∂_t)((1 - 2β) c + r)‖_{H^{m,δ}}`. -/
theorem cyl_dbar_estimate_C (hJ : IsCxMat J) (hβ : IsCutoff β) (h0 : 0 < δ) (h1 : δ < 2 * π)
    (m : ℕ) : ∃ C : ℝ≥0, ∀ x : HcSp (m + 1) hδ n, ‖x‖ ≤ C * ‖dbarCL m hδ J hβ x‖ := by
  obtain ⟨C₀, hC₀⟩ := neck_estimate (n := n) (hδ := hδ) hJ h0 h1 m
  set A := ‖intL m hδ h0‖
  set B := ‖toH m hδ (isTest_dcut hβ)‖
  set K := A + |C₀| * (n * (1 + 2 * A * B))
  refine ⟨⟨K, by positivity⟩, fun x => ?_⟩
  change ‖x‖ ≤ K * _
  set g := dbarCL m hδ J hβ x
  have hc := norm_const_le (J := J) hβ h0 m x
  have hg : 0 ≤ ‖g‖ := norm_nonneg _
  have hl : ∀ l, ‖crOpW m hδ J x.2 l‖ ≤ (1 + 2 * A * B) * ‖g‖ := by
    intro l
    have e : crOpW m hδ J x.2 l = g l + (2 * x.1 l) • toH m hδ (isTest_dcut hβ) := by
      simp only [g, dbarCL_apply]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    have h1 := norm_le_pi_norm g l
    have h2 : |x.1 l| ≤ A * ‖g‖ := (Real.norm_eq_abs _ ▸ norm_le_pi_norm x.1 l).trans hc
    nlinarith [norm_nonneg (toH m hδ (isTest_dcut hβ)), abs_nonneg (x.1 l)]
  have hr : ‖x.2‖ ≤ |C₀| * (n * (1 + 2 * A * B)) * ‖g‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
    refine (hC₀ x.2 k).trans ?_
    have hs : ∑ l, ‖crOpW m hδ J x.2 l‖ ≤ n * ((1 + 2 * A * B) * ‖g‖) := by
      have := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hl l
      simpa using this
    have hs0 : 0 ≤ ∑ l, ‖crOpW m hδ J x.2 l‖ := by positivity
    calc C₀ * ∑ l, ‖crOpW m hδ J x.2 l‖ ≤ |C₀| * ∑ l, ‖crOpW m hδ J x.2 l‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hs0
      _ ≤ |C₀| * (n * ((1 + 2 * A * B) * ‖g‖)) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring
  rw [Prod.norm_def, max_le_iff]
  constructor
  · nlinarith [abs_nonneg C₀, mul_nonneg (abs_nonneg C₀)
      (mul_nonneg (Nat.cast_nonneg n) (by positivity : (0 : ℝ) ≤ 1 + 2 * A * B))]
  · nlinarith [norm_nonneg (intL m hδ h0)]

end Op

/-! ## 4. Ontoness -/

section Onto

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma crOpW_mkH {m : ℕ} {r : Fin n → ℝ × ℝ → ℝ} (hr : ∀ l, SmoothW δ (r l)) {ψ : ℝ × ℝ → ℝ}
    (hψ : IsTest ψ) (k : Fin n) (h : ∀ x, Ds (r k) x + ∑ l, J k l * Dt (r l) x = ψ x) :
    crOpW m hδ J (fun l => mkH (m + 1) hδ (hr l)) k = toH m hδ hψ := by
  apply valCLM_injective (m := m) (hδ := hδ)
  simp only [crOpW, map_add, map_sum, map_smul, dsH_mkH, dtH_mkH]
  refine Lp.ext ?_
  have hs : ∀ l, (valCLM m hδ (mkH m hδ (hr l).dt) : ℝ × ℝ → ℝ) =ᵐ[cyl] Dt (r l) := fun l =>
    val_mkH (k := m) (hδ := hδ) (hr l).dt
  filter_upwards [Lp.coeFn_add (valCLM m hδ (mkH m hδ (hr k).ds))
      (∑ l, J k l • valCLM m hδ (mkH m hδ (hr l).dt)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun l => J k l • valCLM m hδ (mkH m hδ (hr l).dt)),
    ae_all_iff.2 fun l => Lp.coeFn_smul (J k l) (valCLM m hδ (mkH m hδ (hr l).dt)),
    ae_all_iff.2 hs, val_mkH (k := m) (hδ := hδ) (hr k).ds,
    val_toH (m := m) (hδ := hδ) hψ] with x h1 h2 h3 h4 h5 h6
  change _ = (H.val (toH m hδ hψ) : ℝ × ℝ → ℝ) x
  rw [h1, Pi.add_apply, h2, h6, ← h x]
  rw [show (valCLM m hδ (mkH m hδ (hr k).ds) : ℝ × ℝ → ℝ) x = Ds (r k) x from h5]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h3 l, Pi.smul_apply, smul_eq_mul, h4 l]

lemma toH_add_mul {m : ℕ} {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) (a : ℝ) :
    toH m hδ (hφ.add (hψ.const_mul a)) = toH m hδ hφ + a • toH m hδ hψ := by
  apply valCLM_injective (m := m) (hδ := hδ)
  rw [map_add, map_smul]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (valCLM m hδ (toH m hδ hφ)) (a • valCLM m hδ (toH m hδ hψ)),
    Lp.coeFn_smul a (valCLM m hδ (toH m hδ hψ)), val_toH (m := m) (hδ := hδ) hφ,
    val_toH (m := m) (hδ := hδ) hψ, val_toH (m := m) (hδ := hδ) (hφ.add (hψ.const_mul a))]
    with x h1 h2 h3 h4 h5
  change (H.val _ : ℝ × ℝ → ℝ) x = _
  rw [h5, h1]
  simp only [Pi.add_apply]
  rw [h2, Pi.smul_apply, smul_eq_mul]
  change _ = (H.val (toH m hδ hφ) : ℝ × ℝ → ℝ) x + a * (H.val (toH m hδ hψ) : ℝ × ℝ → ℝ) x
  rw [h3, h4]

/-- **The test tuples are in the range**: `∂̄(c, r) = φ` with `r` the smooth solution of
`exists_smooth_solution`. -/
theorem test_mem_range (hJ : IsCxMat J) (hβ : IsCutoff β) (h1 : δ < 2 * π) (m : ℕ)
    {φ : Fin n → ℝ × ℝ → ℝ} (hφ : ∀ k, IsTest (φ k)) :
    (fun k => toH m hδ (hφ k)) ∈ range (dbarCL m hδ J hβ) := by
  obtain ⟨c, r, hr, hdr⟩ := exists_smooth_solution hJ hβ hφ
  have hr' : ∀ l, SmoothW δ (r l) := fun l => hr l δ h1
  refine ⟨(c, fun l => mkH (m + 1) hδ (hr' l)), funext fun k => ?_⟩
  rw [dbarCL_apply]
  have hψ := (hφ k).add ((isTest_dcut hβ).const_mul (2 * c k))
  rw [crOpW_mkH hr' hψ k (fun x => hdr k x), toH_add_mul (hφ k) (isTest_dcut hβ)]
  simp

/-- **`∂̄ : H_c^{m+1,δ} → (H^{m,δ})ⁿ` is onto**, for `0 ≤ δ < 2π`, `δ > 0`. -/
theorem dbarCL_surjective (hJ : IsCxMat J) (hβ : IsCutoff β) (h0 : 0 < δ) (h1 : δ < 2 * π)
    (m : ℕ) : Surjective (dbarCL m hδ J hβ) := by
  obtain ⟨C, hC⟩ := cyl_dbar_estimate_C (n := n) (hδ := hδ) hJ hβ h0 h1 m
  have hcl : IsClosed (range (dbarCL m hδ J hβ)) :=
    ((dbarCL m hδ J hβ).antilipschitz_of_bound hC).isClosed_range
      (dbarCL m hδ J hβ).uniformContinuous
  set T : Set (H m hδ) := {u | ∃ φ, ∃ hφ : IsTest φ, u = toH m hδ hφ}
  have hD : Dense (Set.pi Set.univ fun _ : Fin n => T) :=
    dense_pi Set.univ fun k _ => dense_test m hδ
  have hsub : Set.pi Set.univ (fun _ : Fin n => T) ⊆ range (dbarCL m hδ J hβ) := by
    intro g hg
    simp only [Set.mem_pi, Set.mem_univ, true_implies, T, Set.mem_ofPred_eq] at hg
    choose φ hφ hgφ using hg
    have : g = fun k => toH m hδ (hφ k) := funext hgφ
    rw [this]
    exact test_mem_range hJ hβ h1 m hφ
  have := hD.closure_eq ▸ closure_minimal hsub hcl
  exact fun y => this (mem_univ y)

/-- **`∂_s + J ∂_t : H_c^{m+1,δ} → (H^{m,δ})ⁿ` is an isomorphism** for `0 < δ < 2π` and
`J² = -1` (the a-free form of Memoir Proposition 4.15, p. 109, after the translation of p. 170):
bijective, with `‖(c, r)‖ ≤ C ‖∂̄(c, r)‖` and `‖∂̄(c, r)‖ ≤ ‖∂̄‖ ‖(c, r)‖`. -/
theorem cyl_dbar_iso_C (hJ : IsCxMat J) (hβ : IsCutoff β) (h0 : 0 < δ) (h1 : δ < 2 * π)
    (m : ℕ) : Bijective (dbarCL m hδ J hβ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : HcSp (m + 1) hδ n,
      ‖x‖ ≤ C * ‖dbarCL m hδ J hβ x‖ ∧ ‖dbarCL m hδ J hβ x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC⟩ := cyl_dbar_estimate_C (n := n) (hδ := hδ) hJ hβ h0 h1 m
  refine ⟨⟨fun x y hxy => ?_, dbarCL_surjective hJ hβ h0 h1 m⟩,
    ⟨C + ‖dbarCL m hδ J hβ‖ + 1, by positivity, fun x => ⟨?_, ?_⟩⟩⟩
  · have h := hC (x - y)
    rw [map_sub, hxy, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
  · refine (hC x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have := norm_nonneg (dbarCL m hδ J hβ); linarith
  · refine ((dbarCL m hδ J hβ).le_opNorm x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have := C.2; linarith

/-- The isomorphism `H_c^{m+1,δ} ≃ (H^{m,δ})ⁿ` given by `∂_s + J ∂_t`. -/
def cylDbarEquiv (hJ : IsCxMat J) (hβ : IsCutoff β) (h0 : 0 < δ) (h1 : δ < 2 * π) (m : ℕ) :
    HcSp (m + 1) hδ n ≃L[ℝ] (Fin n → H m hδ) :=
  ContinuousLinearEquiv.ofBijective (dbarCL m hδ J hβ)
    (LinearMap.ker_eq_bot.2 (cyl_dbar_iso_C hJ hβ h0 h1 m).1.1)
    (LinearMap.range_eq_top.2 (cyl_dbar_iso_C hJ hβ h0 h1 m).1.2)

end Onto

/-! ## 5. The levels, and Memoir Proposition 4.15 -/

section Levels

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ}

lemma val_dsH_inclH' {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m + 1 ≤ m' + 1)
    (hδδ : δ ≤ δ') (u : H (m' + 1) hδ') :
    H.val (dsH m hδ (inclH hδ hδ' hm hδδ u)) = H.val (dsH m' hδ' u) :=
  Lp.ext ((coeFn_dsH _).trans ((dv_unique (H.toSub (inclH hδ hδ' hm hδδ u)) (idxS m)
    (dv_spec (H.toSub u) (idxS m')).1 (dv_memLp _ _)).trans (coeFn_dsH u).symm))

lemma val_dtH_inclH' {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m + 1 ≤ m' + 1)
    (hδδ : δ ≤ δ') (u : H (m' + 1) hδ') :
    H.val (dtH m hδ (inclH hδ hδ' hm hδδ u)) = H.val (dtH m' hδ' u) :=
  Lp.ext ((coeFn_dtH _).trans ((dv_unique (H.toSub (inclH hδ hδ' hm hδδ u)) (idxT m)
    (dv_spec (H.toSub u) (idxT m')).1 (dv_memLp _ _)).trans (coeFn_dtH u).symm))

/-- The inclusion `H_c^{m'+1,δ'} → H_c^{m+1,δ}`, `(c, r) ↦ (c, r)`. -/
def inclC {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hm : m + 1 ≤ m' + 1)
    (hδδ : δ ≤ δ') (x : HcSp (m' + 1) hδ' n) : HcSp (m + 1) hδ n :=
  (x.1, fun k => inclH hδ hδ' hm hδδ (x.2 k))

/-- **The level operators are restrictions of each other**: `∂̄` commutes with the inclusions
`H_c^{m'+1,δ'} → H_c^{m+1,δ}` and `H^{m',δ'} → H^{m,δ}`. -/
theorem dbarCL_incl (hβ : IsCutoff β) {m m' : ℕ} {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hm : m ≤ m') (hδδ : δ ≤ δ') (x : HcSp (m' + 1) hδ' n) (k : Fin n) :
    inclH hδ hδ' hm hδδ (dbarCL m' hδ' J hβ x k) =
      dbarCL m hδ J hβ (inclC hδ hδ' (by omega) hδδ x) k := by
  apply valCLM_injective (m := m) (hδ := hδ)
  rw [valCLM_inclH, dbarCL_apply, dbarCL_apply]
  simp only [crOpW, map_sub, map_add, map_sum, map_smul, inclC]
  congr 1
  · congr 1
    · exact (val_dsH_inclH' hδ hδ' (by omega) hδδ (x.2 k)).symm
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [show valCLM m hδ (dtH m hδ (inclH hδ hδ' _ hδδ (x.2 l))) =
        valCLM m' hδ' (dtH m' hδ' (x.2 l)) from val_dtH_inclH' hδ hδ' (by omega) hδδ (x.2 l)]

lemma weight_nonneg {δ : ℕ → ℝ} (h0 : 0 < δ 0) (hmono : StrictMono δ) (m : ℕ) : 0 ≤ δ m :=
  h0.le.trans (hmono.monotone (Nat.zero_le m))

/-- **Memoir Proposition 4.15** (p. 109), without the gluing parameter.  For a constant `J(0)`
with `J(0)² = -1` (`IsCxMat J`) and weights `0 < δ₀ < δ₁ < ⋯ < 2π`, the operator
`∂̄₀ = ∂_s + J(0) ∂_t : H_c^{3+m,δ_m}(ℝ × S¹, ℝⁿ) → H^{2+m,δ_m}(ℝ × S¹, ℝⁿ)` is bijective on
every level, with `C_m⁻¹ |ξ| ≤ |∂̄₀ ξ| ≤ C_m |ξ|`; the level operators are restrictions of each
other (`dbarCL_incl`), so `∂̄₀` is an sc-isomorphism.

On `C_a` the memoir uses the centred norms (4.8), weight `e^{δ|s - R/2|}`, and the cut-off
`β_a(s) = β(s - R/2)` in `p̂ = p - (1 - 2β_a) p∞`.  The translation `s ↦ s + R/2` of p. 170
carries these isometrically onto the norm of `H^{m,δ}` on `ℝ × S¹` and the cut-off `β`, and
commutes with `∂_s + J(0) ∂_t`; so the statement below is the proposition, with `C_m`
independent of `a`. -/
theorem memoir_proposition_4_15 (hJ : IsCxMat J) (hβ : IsCutoff β) {δ : ℕ → ℝ} (h0 : 0 < δ 0)
    (hmono : StrictMono δ) (h2π : ∀ m, δ m < 2 * π) (m : ℕ) :
    Bijective (dbarCL (2 + m) (weight_nonneg h0 hmono m) J hβ) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ξ : HcSp (2 + m + 1) (weight_nonneg h0 hmono m) n,
        C⁻¹ * ‖ξ‖ ≤ ‖dbarCL (2 + m) (weight_nonneg h0 hmono m) J hβ ξ‖ ∧
        ‖dbarCL (2 + m) (weight_nonneg h0 hmono m) J hβ ξ‖ ≤ C * ‖ξ‖ := by
  have hm : 0 < δ m := h0.trans_le (hmono.monotone (Nat.zero_le m))
  obtain ⟨hb, C, hC, hCx⟩ := cyl_dbar_iso_C (n := n) (hδ := weight_nonneg h0 hmono m) hJ hβ hm
    (h2π m) (2 + m)
  refine ⟨hb, C, hC, fun ξ => ⟨?_, (hCx ξ).2⟩⟩
  rw [inv_mul_le_iff₀ hC]
  exact (hCx ξ).1

end Levels

end GWMemoir
