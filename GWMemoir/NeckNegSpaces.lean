import GWMemoir.NeckNegWeight

/-!
# The model with growth on `ℝ × S¹`: the operator on `H^m` and its estimate

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Proposition 4.16 (p. 110),
after the translation by `R/2` of p. 170.

With `h(s) = ∫₀^s (1 - 2β)` and `a = δ (1 - 2β)` (`negH`, `negA`), the substitution
`u = e^{δ h} v` turns `∂̄ = ∂_s + J ∂_t` on `H^{m,-δ}(ℝ × S¹)` into
`L v = ∂_s v + J ∂_t v + a(s) v` on the unweighted spaces `H^m = H^{m,0}` (`dbar_transport`):
`∂̄(e^{δh} v) = e^{δh} L v`, and `[u]_0 = [v]_0` since `h(0) = 0`.

* `Lop m : (H^{m+1})ⁿ → (H^m)ⁿ` is `L`; `Lop_toH` computes it on test functions.
* `Lop_lowH`, `Lop_dtH`, `Lop_dsH`, `trH_dsH_Lop`: how `L` meets the inclusion `H^{m+1} ⊂ H^m`,
  `∂_t`, `∂_s` and the circle average `[·]_0`.
* `low_estimate_neg`: the estimate of `exists_test_estimate_neg` on `(H^{m+1})ⁿ`, by density.
* `neg_estimate_sq`: for every `m`,
  `∑_k ‖v_k‖²_{m+1} ≤ C (∑_k ‖(L v)_k‖²_m + ∑_k [v_k]_0²)`, for `0 < δ < π`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped ContDiff Topology Real
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev GWMemoir.Neck

noncomputable section

namespace GWMemoir.NeckNeg

/-! ## 1. Inclusions, multipliers and the circle average -/

section General

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ} {χ : ℝ → ℝ}

lemma toH_add' {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) :
    toH m hδ (hφ.add hψ) = toH m hδ hφ + toH m hδ hψ := by
  apply valCLM_injective (m := m) (hδ := hδ)
  rw [map_add]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (valCLM m hδ (toH m hδ hφ)) (valCLM m hδ (toH m hδ hψ)),
    Neck.val_toH (m := m) (hδ := hδ) hφ, Neck.val_toH (m := m) (hδ := hδ) hψ,
    Neck.val_toH (m := m) (hδ := hδ) (hφ.add hψ)] with x h1 h2 h3 h4
  rw [h4, h1, Pi.add_apply, Pi.add_apply, h2, h3]

variable (m hδ) in
/-- The inclusion `H^{m+1,δ} ⊂ H^{m,δ}`. -/
def lowH : H (m + 1) hδ →L[ℝ] H m hδ := inclH hδ hδ (Nat.le_succ m) le_rfl

lemma val_lowH (u : H (m + 1) hδ) : valCLM m hδ (lowH m hδ u) = valCLM (m + 1) hδ u := rfl

lemma norm_lowH_le (u : H (m + 1) hδ) : ‖lowH m hδ u‖ ≤ ‖u‖ :=
  norm_inclL_le hδ hδ (Nat.le_succ m) le_rfl u

lemma lowH_toH {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) : lowH m hδ (toH (m + 1) hδ hφ) = toH m hδ hφ :=
  inclH_toH _ hφ

lemma lowH_dsH (u : H (m + 1 + 1) hδ) :
    lowH m hδ (dsH (m + 1) hδ u) = dsH m hδ (lowH (m + 1) hδ u) := by
  have h := Continuous.ext_on (dense_test (m + 1 + 1) hδ)
    ((lowH m hδ).comp (dsH (m + 1) hδ)).continuous ((dsH m hδ).comp (lowH (m + 1) hδ)).continuous
    (f := fun u => lowH m hδ (dsH (m + 1) hδ u)) (g := fun u => dsH m hδ (lowH (m + 1) hδ u))
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [dsH_toH, lowH_toH])
  exact congrFun h u

lemma lowH_dtH (u : H (m + 1 + 1) hδ) :
    lowH m hδ (dtH (m + 1) hδ u) = dtH m hδ (lowH (m + 1) hδ u) := by
  have h := Continuous.ext_on (dense_test (m + 1 + 1) hδ)
    ((lowH m hδ).comp (dtH (m + 1) hδ)).continuous ((dtH m hδ).comp (lowH (m + 1) hδ)).continuous
    (f := fun u => lowH m hδ (dtH (m + 1) hδ u)) (g := fun u => dtH m hδ (lowH (m + 1) hδ u))
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [dtH_toH, lowH_toH])
  exact congrFun h u

lemma lowH_mulHL (h : Mult (m + 1) χ) (h' : Mult m χ) (u : H (m + 1) hδ) :
    lowH m hδ (mulHL χ h u) = mulHL χ h' (lowH m hδ u) := by
  apply valCLM_injective
  refine Lp.ext ?_
  rw [val_lowH]
  filter_upwards [val_mulHL (hδ := hδ) χ h u, val_mulHL (hδ := hδ) χ h' (lowH m hδ u)]
    with x h1 h2
  rw [h1, h2, val_lowH]

/-- `∂_s (χ u) = χ' u + χ ∂_s u`. -/
lemma dsH_mulHL (h1 : Mult (m + 1) χ) (h0 : Mult m χ) (h' : Mult m (deriv χ))
    (u : H (m + 1) hδ) :
    dsH m hδ (mulHL χ h1 u) = mulHL (deriv χ) h' (lowH m hδ u) + mulHL χ h0 (dsH m hδ u) := by
  have h := Continuous.ext_on (dense_test (m + 1) hδ)
    (f := fun u => dsH m hδ (mulHL χ h1 u))
    (g := fun u => mulHL (deriv χ) h' (lowH m hδ u) + mulHL χ h0 (dsH m hδ u))
    (by fun_prop) (by fun_prop)
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [mulHL_toH, dsH_toH, lowH_toH]
      rw [← toH_add']
      exact toH_congr (Ds_mul_s (hφ.smooth.differentiable (by simp))
        (h1.smooth.differentiable (by simp))) _ _)
  exact congrFun h u

/-- `∂_t (χ u) = χ ∂_t u`. -/
lemma dtH_mulHL (h1 : Mult (m + 1) χ) (h0 : Mult m χ) (u : H (m + 1) hδ) :
    dtH m hδ (mulHL χ h1 u) = mulHL χ h0 (dtH m hδ u) := by
  have h := Continuous.ext_on (dense_test (m + 1) hδ)
    (f := fun u => dtH m hδ (mulHL χ h1 u)) (g := fun u => mulHL χ h0 (dtH m hδ u))
    (by fun_prop) (by fun_prop)
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [mulHL_toH, dtH_toH]
      exact toH_congr (Dt_mul_s (hφ.smooth.differentiable (by simp))
        (h1.smooth.differentiable (by simp))) _ _)
  exact congrFun h u

lemma mulHL_comm {χ' : ℝ → ℝ} (h : Mult m χ) (h' : Mult m χ') (u : H m hδ) :
    mulHL χ h (mulHL χ' h' u) = mulHL χ' h' (mulHL χ h u) := by
  apply valCLM_injective
  refine Lp.ext ?_
  filter_upwards [val_mulHL (hδ := hδ) χ h (mulHL χ' h' u), val_mulHL (hδ := hδ) χ' h' u,
    val_mulHL (hδ := hδ) χ' h' (mulHL χ h u), val_mulHL (hδ := hδ) χ h u] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]; ring

/-- `χ₁ (χ₂ u) + χ₃ u = 0` when `χ₁ χ₂ + χ₃ = 0`. -/
lemma mulHL_mulHL_add {χ₁ χ₂ χ₃ : ℝ → ℝ} (h₁ : Mult m χ₁) (h₂ : Mult m χ₂) (h₃ : Mult m χ₃)
    (he : ∀ s, χ₁ s * χ₂ s + χ₃ s = 0) (u : H m hδ) :
    mulHL χ₁ h₁ (mulHL χ₂ h₂ u) + mulHL χ₃ h₃ u = 0 := by
  apply valCLM_injective
  rw [map_add, map_zero]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (valCLM m hδ (mulHL χ₁ h₁ (mulHL χ₂ h₂ u)))
      (valCLM m hδ (mulHL χ₃ h₃ u)), Lp.coeFn_zero ℝ 2 cyl,
    val_mulHL (hδ := hδ) χ₁ h₁ (mulHL χ₂ h₂ u), val_mulHL (hδ := hδ) χ₂ h₂ u,
    val_mulHL (hδ := hδ) χ₃ h₃ u] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.zero_apply, ← mul_assoc, ← add_mul, he, zero_mul]

lemma trH_lowH (hm : 1 ≤ m) (σ : ℝ) (u : H (m + 1) hδ) :
    trH hm σ (lowH m hδ u) = trH (hm.trans (Nat.le_succ m)) σ u := by
  have h := Continuous.ext_on (dense_test (m + 1) hδ)
    ((trH hm σ).comp (lowH m hδ)).continuous (trH (hδ := hδ) (hm.trans (Nat.le_succ m)) σ).continuous
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [ContinuousLinearMap.comp_apply, lowH_toH, trH_toH])
  exact congrFun h u

/-- `[∂_t u]_σ = 0`. -/
lemma trH_dtH (hm : 1 ≤ m) (σ : ℝ) (u : H (m + 1) hδ) : trH hm σ (dtH m hδ u) = 0 := by
  have h := Continuous.ext_on (dense_test (m + 1) hδ)
    ((trH hm σ).comp (dtH m hδ)).continuous (continuous_const (y := (0 : ℝ)))
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      simp only [ContinuousLinearMap.comp_apply, dtH_toH, trH_toH]
      have := cmean_Dt hφ σ
      rwa [cmean, intervalIntegral.integral_of_le zero_le_one] at this)
  exact congrFun h u

end General

/-! ## 2. The operator `L = ∂_s + J ∂_t + a(s)` -/

section Op

variable {m n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ}

/-- `0 ≤ 0`: the unweighted spaces `H^m = H^{m,0}`. -/
lemma zle : (0 : ℝ) ≤ 0 := le_rfl

lemma mult_deriv_negA (hβ : IsCutoff β) (m : ℕ) : Mult m (deriv (negA δ β)) := by
  rw [deriv_negA hβ]
  exact mult_of_vanish (contDiff_const.mul (contDiff_deriv_cut hβ)) (R := 2)
    (fun s hs => by rw [deriv_cut_eq_zero hβ hs.le, mul_zero]) m

variable (m J) in
/-- **`L = ∂_s + J ∂_t + a(s) : (H^{m+1})ⁿ → (H^m)ⁿ`**, `a = δ (1 - 2β)`. -/
def Lop (hβ : IsCutoff β) (hδ : 0 ≤ δ) : (Fin n → H (m + 1) zle) →L[ℝ] (Fin n → H m zle) :=
  crOpWL m zle J + ContinuousLinearMap.pi fun k =>
    (mulHL (negA δ β) (mult_negA hβ hδ m)).comp ((lowH m zle).comp (ContinuousLinearMap.proj k))

variable {hβ : IsCutoff β} {hδ : 0 ≤ δ}

lemma Lop_apply (v : Fin n → H (m + 1) zle) (k : Fin n) :
    Lop m J hβ hδ v k = crOpW m zle J v k + mulHL (negA δ β) (mult_negA hβ hδ m) (lowH m zle (v k)) := by
  simp [Lop, crOpWL_apply]

lemma Lop_toH {r : Fin n → ℝ × ℝ → ℝ} (hr : ∀ k, IsTest (r k)) (k : Fin n) :
    Lop m J hβ hδ (fun l => toH (m + 1) zle (hr l)) k =
      toH m zle (isTest_negL (J := J) (contDiff_negA (δ := δ) hβ) hr k) := by
  rw [Lop_apply, crOpW_toH hr, lowH_toH, mulHL_toH, ← toH_add']
  exact toH_congr rfl _ _

/-- `L` commutes with `H^{m+2} ⊂ H^{m+1}`. -/
lemma Lop_lowH (v : Fin n → H (m + 1 + 1) zle) (k : Fin n) :
    Lop m J hβ hδ (fun l => lowH (m + 1) zle (v l)) k = lowH m zle (Lop (m + 1) J hβ hδ v k) := by
  rw [Lop_apply, Lop_apply, map_add,
    lowH_mulHL (mult_negA hβ hδ (m + 1)) (mult_negA hβ hδ m)]
  simp only [crOpW, map_add, map_sum, map_smul, lowH_dsH, lowH_dtH]

/-- `L ∂_t = ∂_t L`. -/
lemma Lop_dtH (v : Fin n → H (m + 1 + 1) zle) (k : Fin n) :
    Lop m J hβ hδ (fun l => dtH (m + 1) zle (v l)) k = dtH m zle (Lop (m + 1) J hβ hδ v k) := by
  rw [Lop_apply, Lop_apply, crOpW_dtH, map_add, lowH_dtH,
    dtH_mulHL (mult_negA hβ hδ (m + 1)) (mult_negA hβ hδ m)]

/-- `L ∂_s = ∂_s L - a'`. -/
lemma Lop_dsH (v : Fin n → H (m + 1 + 1) zle) (k : Fin n) :
    Lop m J hβ hδ (fun l => dsH (m + 1) zle (v l)) k = dsH m zle (Lop (m + 1) J hβ hδ v k) -
      mulHL (deriv (negA δ β)) (mult_deriv_negA hβ m) (lowH m zle (lowH (m + 1) zle (v k))) := by
  rw [Lop_apply, Lop_apply, crOpW_dsH, map_add, lowH_dsH,
    dsH_mulHL (mult_negA hβ hδ (m + 1)) (mult_negA hβ hδ m) (mult_deriv_negA hβ m)]
  abel

/-- `[∂_s v]_0 = [L v]_0`, since `[∂_t v]_0 = 0` and `a(0) = 0`. -/
lemma trH_dsH_Lop (v : Fin n → H (m + 1 + 1) zle) (k : Fin n) :
    trH (Nat.le_add_left 1 m) 0 (dsH (m + 1) zle (v k)) =
      trH (Nat.le_add_left 1 m) 0 (Lop (m + 1) J hβ hδ v k) := by
  rw [Lop_apply, crOpW]
  simp only [map_add, map_sum, map_smul, trH_dtH, trH_mulHL, negA_zero hβ, smul_zero,
    Finset.sum_const_zero, zero_mul, add_zero]

/-- **Leibniz**: `L (χ u) = χ L u + χ' u`. -/
lemma Lop_mulHL {χ : ℝ → ℝ} (h1 : Mult (m + 1) χ) (h0 : Mult m χ) (h' : Mult m (deriv χ))
    (u : Fin n → H (m + 1) zle) (k : Fin n) :
    Lop m J hβ hδ (fun l => mulHL χ h1 (u l)) k =
      mulHL χ h0 (Lop m J hβ hδ u k) + mulHL (deriv χ) h' (lowH m zle (u k)) := by
  rw [Lop_apply, Lop_apply, lowH_mulHL h1 h0, mulHL_comm (mult_negA hβ hδ m) h0]
  simp only [crOpW, map_add, map_sum, map_smul, dsH_mulHL h1 h0 h', dtH_mulHL h1 h0]
  abel

end Op

/-! ## 3. The estimate on `H^{m+1}` -/

section Estimate

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ}

/-- **The estimate at level `0`** on `(H^{m+1})ⁿ`, for `0 < δ < π`, with one constant for all
`m`: `∑_k ‖v_k‖²_{L²} + ‖∂_s v_k‖²_{L²} + ‖∂_t v_k‖²_{L²} ≤
C (∑_k ‖(L v)_k‖²_{L²} + ∑_k [v_k]_0²)`. -/
theorem low_estimate_neg (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π) :
    ∃ C, 0 ≤ C ∧ ∀ (m : ℕ) (v : Fin n → H (m + 1) zle),
      ∑ k, (‖wdv (H.toSub (v k)) (CylinderSobolev.idx0 (m + 1))‖ ^ 2 +
        ‖wdv (H.toSub (dsH m zle (v k))) (CylinderSobolev.idx0 m)‖ ^ 2 +
        ‖wdv (H.toSub (dtH m zle (v k))) (CylinderSobolev.idx0 m)‖ ^ 2) ≤
      C * (∑ k, ‖wdv (H.toSub (Lop m J hβ hδ.le v k)) (CylinderSobolev.idx0 m)‖ ^ 2 +
        ∑ k, trH (Nat.le_add_left 1 m) 0 (v k) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_test_estimate_neg hJ (contDiff_negA (δ := δ) hβ) hδ hπ
    (fun s hs => negA_nonneg hβ hδ.le hs) (fun s hs => negA_nonpos hβ hδ.le hs)
    (abs_negA_le hβ hδ.le) (fun s hs => le_abs_negA hβ hδ.le hs)
  refine ⟨C, hC0, fun m v => ?_⟩
  set T : Set (H (m + 1) zle) := {u | ∃ φ, ∃ hφ : IsTest φ, u = toH (m + 1) zle hφ}
  have hD : Dense (Set.pi Set.univ fun _ : Fin n => T) :=
    dense_pi Set.univ fun k _ => dense_test (m + 1) zle
  have hCl : IsClosed {g : Fin n → H (m + 1) zle |
      ∑ k, (‖wdvCLM (m + 1) zle (CylinderSobolev.idx0 (m + 1)) (g k)‖ ^ 2 +
        ‖wdvCLM m zle (CylinderSobolev.idx0 m) (dsH m zle (g k))‖ ^ 2 +
        ‖wdvCLM m zle (CylinderSobolev.idx0 m) (dtH m zle (g k))‖ ^ 2) ≤
      C * (∑ k, ‖wdvCLM m zle (CylinderSobolev.idx0 m) (Lop m J hβ hδ.le g k)‖ ^ 2 +
        ∑ k, trH (Nat.le_add_left 1 m) 0 (g k) ^ 2)} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub := closure_minimal (s := Set.pi Set.univ fun _ : Fin n => T) ?_ hCl
  · rw [hD.closure_eq] at hsub
    exact hsub (Set.mem_univ v)
  intro g hg
  simp only [Set.mem_pi, Set.mem_univ, true_implies, T, Set.mem_ofPred_eq] at hg
  choose r hr hgr using hg
  have hg' : g = fun l => toH (m + 1) zle (hr l) := funext hgr
  subst hg'
  change ∑ k, (‖wdv (H.toSub (toH (m + 1) zle (hr k))) (CylinderSobolev.idx0 (m + 1))‖ ^ 2 +
        ‖wdv (H.toSub (dsH m zle (toH (m + 1) zle (hr k)))) (CylinderSobolev.idx0 m)‖ ^ 2 +
        ‖wdv (H.toSub (dtH m zle (toH (m + 1) zle (hr k)))) (CylinderSobolev.idx0 m)‖ ^ 2) ≤
      C * (∑ k, ‖wdv (H.toSub (Lop m J hβ hδ.le (fun l => toH (m + 1) zle (hr l)) k))
        (CylinderSobolev.idx0 m)‖ ^ 2 + ∑ k, trH (Nat.le_add_left 1 m) 0 (toH (m + 1) zle (hr k)) ^ 2)
  simp only [dsH_toH, dtH_toH, Lop_toH hr, nsq_toH, trH_toH]
  have h := hC r hr
  simp only [cmean, intervalIntegral.integral_of_le zero_le_one] at h
  simp only [wt, zero_mul, Real.exp_zero, one_mul]
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_add, integral_add]
  · exact tInt_sq (hr k)
  · exact tInt_sq (hr k).ds
  · exact (tInt_sq (hr k)).add (tInt_sq (hr k).ds)
  · exact tInt_sq (hr k).dt

lemma sum_sq_wdv_le' {m : ℕ} (g : Fin n → H m zle) :
    ∑ k, ‖wdv (H.toSub (g k)) (CylinderSobolev.idx0 m)‖ ^ 2 ≤ ∑ k, ‖g k‖ ^ 2 :=
  Finset.sum_le_sum fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_wdv_le (g k) (CylinderSobolev.idx0 m)) 2

/-- **The estimate modulo the average, at every level**: for `0 < δ < π` and `J² = -1`, every
`m` has `C` with `∑_k ‖v_k‖²_{H^{m+1}} ≤ C (∑_k ‖(L v)_k‖²_{H^m} + ∑_k [v_k]_0²)`. -/
theorem neg_estimate_sq (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π) :
    ∀ m : ℕ, ∃ C, 0 ≤ C ∧ ∀ v : Fin n → H (m + 1) zle,
      ∑ k, ‖v k‖ ^ 2 ≤ C * (∑ k, ‖Lop m J hβ hδ.le v k‖ ^ 2 +
        ∑ k, trH (Nat.le_add_left 1 m) 0 (v k) ^ 2) := by
  obtain ⟨C0, hC0, hL⟩ := low_estimate_neg (n := n) hJ hβ hδ hπ
  intro m
  induction m with
  | zero =>
    refine ⟨C0, hC0, fun v => ?_⟩
    have h := hL 0 v
    simp only [← norm_sq_H0] at h
    calc ∑ k, ‖v k‖ ^ 2 ≤ ∑ k, (‖wdv (H.toSub (v k)) (CylinderSobolev.idx0 (0 + 1))‖ ^ 2 +
          ‖dsH 0 zle (v k)‖ ^ 2 + ‖dtH 0 zle (v k)‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => norm_sq_le_split (v k)
      _ ≤ _ := h
  | succ m ih =>
    obtain ⟨C, hC, hCv⟩ := ih
    set T1 := trH (hδ := zle) (Nat.le_add_left 1 m) 0
    set M := ‖mulHL (hδ := zle) (deriv (negA δ β)) (mult_deriv_negA hβ m)‖
    refine ⟨C0 + C * (3 + ‖T1‖ ^ 2) + 2 * C * M ^ 2 * C, by positivity, fun v => ?_⟩
    set P := ∑ k, ‖Lop (m + 1) J hβ hδ.le v k‖ ^ 2
    set Q := ∑ k, trH (Nat.le_add_left 1 (m + 1)) 0 (v k) ^ 2
    have hP : 0 ≤ P := by positivity
    have hQ : 0 ≤ Q := by positivity
    -- the `L²` part
    have hA : ∑ k, ‖wdv (H.toSub (v k)) (CylinderSobolev.idx0 (m + 1 + 1))‖ ^ 2 ≤ C0 * (P + Q) := by
      have h := hL (m + 1) v
      refine le_trans ?_ (h.trans (mul_le_mul_of_nonneg_left
        (add_le_add (sum_sq_wdv_le' _) le_rfl) hC0))
      refine Finset.sum_le_sum fun k _ => ?_
      have := sq_nonneg ‖wdv (H.toSub (dsH (m + 1) zle (v k))) (CylinderSobolev.idx0 (m + 1))‖
      have := sq_nonneg ‖wdv (H.toSub (dtH (m + 1) zle (v k))) (CylinderSobolev.idx0 (m + 1))‖
      linarith
    -- the inclusion `H^{m+2} ⊂ H^{m+1}`
    have hU : ∑ k, ‖lowH (m + 1) zle (v k)‖ ^ 2 ≤ C * (P + Q) := by
      refine (hCv fun l => lowH (m + 1) zle (v l)).trans (mul_le_mul_of_nonneg_left
        (add_le_add (Finset.sum_le_sum fun k _ => ?_) (le_of_eq (Finset.sum_congr rfl
          fun k _ => ?_))) hC)
      · rw [Lop_lowH]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_lowH_le _) 2
      · rw [trH_lowH]
    -- `∂_t`
    have hT : ∑ k, ‖dtH (m + 1) zle (v k)‖ ^ 2 ≤ C * P := by
      refine (hCv fun l => dtH (m + 1) zle (v l)).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have h0 : ∀ k, T1 (dtH (m + 1) zle (v k)) = 0 := fun k => trH_dtH _ _ _
      simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, add_zero]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Lop_dtH]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_dtH_le _) 2
    -- `∂_s`
    have hS : ∑ k, ‖dsH (m + 1) zle (v k)‖ ^ 2 ≤
        C * ((2 + ‖T1‖ ^ 2) * P + 2 * M ^ 2 * ∑ k, ‖lowH (m + 1) zle (v k)‖ ^ 2) := by
      refine (hCv fun l => dsH (m + 1) zle (v l)).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have e1 : ∀ k, ‖Lop m J hβ hδ.le (fun l => dsH (m + 1) zle (v l)) k‖ ^ 2 ≤
          2 * ‖Lop (m + 1) J hβ hδ.le v k‖ ^ 2 + 2 * M ^ 2 * ‖lowH (m + 1) zle (v k)‖ ^ 2 := by
        intro k
        rw [Lop_dsH]
        have h1 := norm_sub_le (dsH m zle (Lop (m + 1) J hβ hδ.le v k))
          (mulHL (deriv (negA δ β)) (mult_deriv_negA hβ m)
            (lowH m zle (lowH (m + 1) zle (v k))))
        have h2 := norm_dsH_le (Lop (m + 1) J hβ hδ.le v k)
        have h3 : ‖mulHL (deriv (negA δ β)) (mult_deriv_negA hβ m)
            (lowH m zle (lowH (m + 1) zle (v k)))‖ ≤ M * ‖lowH (m + 1) zle (v k)‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (norm_lowH_le _) (norm_nonneg _))
        have hle := h1.trans (add_le_add h2 h3)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
        nlinarith [sq_nonneg (‖Lop (m + 1) J hβ hδ.le v k‖ - M * ‖lowH (m + 1) zle (v k)‖)]
      have e2 : ∀ k, trH (Nat.le_add_left 1 m) 0 (dsH (m + 1) zle (v k)) ^ 2 ≤
          ‖T1‖ ^ 2 * ‖Lop (m + 1) J hβ hδ.le v k‖ ^ 2 := by
        intro k
        rw [trH_dsH_Lop (hβ := hβ) (hδ := hδ.le) (J := J), ← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          rw [← Real.norm_eq_abs]; exact T1.le_opNorm _) 2
      calc ∑ k, ‖Lop m J hβ hδ.le (fun l => dsH (m + 1) zle (v l)) k‖ ^ 2 +
            ∑ k, trH (Nat.le_add_left 1 m) 0 (dsH (m + 1) zle (v k)) ^ 2
          ≤ ∑ k, (2 * ‖Lop (m + 1) J hβ hδ.le v k‖ ^ 2 +
              2 * M ^ 2 * ‖lowH (m + 1) zle (v k)‖ ^ 2) +
            ∑ k, ‖T1‖ ^ 2 * ‖Lop (m + 1) J hβ hδ.le v k‖ ^ 2 :=
            add_le_add (Finset.sum_le_sum fun k _ => e1 k) (Finset.sum_le_sum fun k _ => e2 k)
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    have hS' : C * (2 * M ^ 2 * ∑ k, ‖lowH (m + 1) zle (v k)‖ ^ 2) ≤
        C * (2 * M ^ 2 * (C * (P + Q))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU (by positivity)) hC
    have hT1 : 0 ≤ ‖T1‖ ^ 2 := by positivity
    calc ∑ k, ‖v k‖ ^ 2 ≤ ∑ k, (‖wdv (H.toSub (v k)) (CylinderSobolev.idx0 (m + 1 + 1))‖ ^ 2 +
          ‖dsH (m + 1) zle (v k)‖ ^ 2 + ‖dtH (m + 1) zle (v k)‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => norm_sq_le_split (v k)
      _ = ∑ k, ‖wdv (H.toSub (v k)) (CylinderSobolev.idx0 (m + 1 + 1))‖ ^ 2 +
          ∑ k, ‖dsH (m + 1) zle (v k)‖ ^ 2 + ∑ k, ‖dtH (m + 1) zle (v k)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ C0 * (P + Q) + C * ((2 + ‖T1‖ ^ 2) * P + 2 * M ^ 2 * (C * (P + Q))) + C * P := by
          nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg hC hQ, mul_nonneg hC hP, mul_nonneg hT1 hP,
          mul_nonneg (mul_nonneg hC hT1) hQ]

end Estimate

end GWMemoir.NeckNeg
