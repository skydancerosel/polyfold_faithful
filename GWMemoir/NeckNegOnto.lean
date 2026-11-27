import GWMemoir.NeckNegSpaces

/-!
# The model with growth on `ℝ × S¹`: kernel, ontoness and Memoir Proposition 4.16

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Proposition 4.16 (p. 110)
and §5.8 (p. 170).

In the picture `u = e^{δ h} v` of `GWMemoir.NeckNegSpaces`, with `ψ = e^{-δ h}` (`negPsi`):

* `Lop_negPsiH`: `L (c ψ) = 0`, and `[ψ]_0 = 1` (`trH_negPsiH`); `c ψ` is the constant `u = c`.
* `Lop_eq_zero_iff`: the kernel of `L` on `(H^{m+1})ⁿ` is `{c ψ}`.
* `Lop_surjective`: `L : (H^{m+1})ⁿ → (H^m)ⁿ` is onto: the range is closed by the estimate on
  `{[v]_0 = 0}`, and a test tuple `g` is `L (ψ r - 2 c β ψ)` for the solution `(c, r)` of
  `∂̄ r = e^{δh} g + 2 β' c` of `exists_smooth_solution`.
* `cyl_dbar_neg`, `memoir_proposition_4_16`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped ContDiff Topology Real
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev GWMemoir.Neck

noncomputable section

namespace GWMemoir.NeckNeg

/-! ## 1. The kernel element `ψ` -/

section Kernel

variable {m n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ}

lemma valCLM_mkH {f : ℝ × ℝ → ℝ} (hf : SmoothW 0 f) :
    (valCLM m zle (mkH m zle hf) : ℝ × ℝ → ℝ) =ᵐ[cyl] f :=
  val_mkH (k := m) (hδ := zle) hf

variable (m) in
/-- `ψ(s) = e^{-δ h(s)}` in `H^m(ℝ × S¹)`. -/
def negPsiH (hβ : IsCutoff β) (hδ : 0 < δ) : H m zle := mkH m zle (smoothW_negPsi hβ hδ)

variable {hβ : IsCutoff β} {hδ : 0 < δ}

lemma val_negPsiH :
    (valCLM m zle (negPsiH m hβ hδ) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => negPsi δ β x.1 :=
  valCLM_mkH (smoothW_negPsi hβ hδ)

lemma lowH_negPsiH : lowH m zle (negPsiH (m + 1) hβ hδ) = negPsiH m hβ hδ :=
  valCLM_injective (by rw [val_lowH]; rfl)

lemma dtH_negPsiH : dtH m zle (negPsiH (m + 1) hβ hδ) = 0 := by
  have e : dtH m zle (negPsiH (m + 1) hβ hδ) = mkH m zle (smoothW_negPsi hβ hδ).dt := dtH_mkH _
  rw [e]
  apply valCLM_injective
  rw [map_zero]
  refine Lp.ext ?_
  filter_upwards [valCLM_mkH (m := m) (smoothW_negPsi hβ hδ).dt,
    Lp.coeFn_zero ℝ 2 cyl] with x h1 h2
  rw [h1, h2, Dt_fun_s ((contDiff_negPsi hβ).differentiable (by simp))]
  rfl

/-- `ψ' = -a ψ`. -/
lemma dsH_negPsiH :
    dsH m zle (negPsiH (m + 1) hβ hδ) = -mulHL (negA δ β) (mult_negA hβ hδ.le m) (negPsiH m hβ hδ) := by
  have e : dsH m zle (negPsiH (m + 1) hβ hδ) = mkH m zle (smoothW_negPsi hβ hδ).ds := dsH_mkH _
  rw [e]
  apply valCLM_injective
  rw [map_neg]
  refine Lp.ext ?_
  filter_upwards [valCLM_mkH (m := m) (smoothW_negPsi hβ hδ).ds,
    Lp.coeFn_neg (valCLM m zle (mulHL (negA δ β) (mult_negA hβ hδ.le m) (negPsiH m hβ hδ))),
    val_mulHL (hδ := zle) (negA δ β) (mult_negA hβ hδ.le m) (negPsiH m hβ hδ),
    val_negPsiH (m := m) (hβ := hβ) (hδ := hδ)] with x h1 h2 h3 h4
  rw [h1, h2, Pi.neg_apply, h3, h4, Ds_fun_s ((contDiff_negPsi hβ).differentiable (by simp)),
    deriv_negPsi hβ]
  ring

/-- **`L (c ψ) = 0`**. -/
lemma Lop_negPsiH (c : Fin n → ℝ) :
    Lop m J hβ hδ.le (fun l => c l • negPsiH (m + 1) hβ hδ) = 0 := by
  funext k
  rw [Lop_apply, Pi.zero_apply, crOpW]
  simp only [map_smul, dsH_negPsiH, dtH_negPsiH, lowH_negPsiH, smul_zero, Finset.sum_const_zero,
    add_zero, smul_neg, neg_add_cancel]

/-- A bump: `β(s - 2) β(-s - 2)`, `= 1` at `0`, `= 0` for `|s| ≥ 3`. -/
def bumpN (β : ℝ → ℝ) (s : ℝ) : ℝ := β (s - 2) * β (-s - 2)

lemma contDiff_bumpN (hβ : IsCutoff β) : ContDiff ℝ ∞ (bumpN β) := by
  unfold bumpN
  have := hβ.smooth
  fun_prop

lemma bumpN_zero (hβ : IsCutoff β) : bumpN β 0 = 1 := by
  unfold bumpN
  rw [show (0 : ℝ) - 2 = -2 by norm_num, show -(0 : ℝ) - 2 = -2 by norm_num,
    hβ.one_of_le (-2) (by norm_num)]
  ring

lemma bumpN_vanish (hβ : IsCutoff β) {s : ℝ} (hs : 3 ≤ |s|) : bumpN β s = 0 := by
  unfold bumpN
  rcases le_abs'.1 hs with h | h
  · rw [hβ.zero_of_ge (s := -s - 2) (by linarith), mul_zero]
  · rw [hβ.zero_of_ge (s := s - 2) (by linarith), zero_mul]

lemma mult_bumpN (hβ : IsCutoff β) (m : ℕ) : Mult m (bumpN β) :=
  mult_of_vanish (contDiff_bumpN hβ) (R := 3) (fun _ hs => bumpN_vanish hβ hs.le) m

lemma mulHL_mkH_toH {χ : ℝ → ℝ} (h : Mult m χ) {f : ℝ × ℝ → ℝ} (hf : SmoothW 0 f)
    {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (he : ∀ x, χ x.1 * f x = φ x) :
    mulHL χ h (mkH m zle hf) = toH m zle hφ := by
  apply valCLM_injective
  refine Lp.ext ?_
  filter_upwards [val_mulHL (hδ := zle) χ h (mkH m zle hf),
    valCLM_mkH (m := m) hf,
    Neck.val_toH (m := m) (hδ := zle) hφ] with x h1 h2 h3
  rw [h1, h2, h3, he]

/-- **`[ψ]_0 = 1`**. -/
lemma trH_negPsiH (hm : 1 ≤ m) : trH hm 0 (negPsiH m hβ hδ) = 1 := by
  have hT : IsTest (fun x : ℝ × ℝ => bumpN β x.1 * negPsi δ β x.1) :=
    isTest_of_s ((contDiff_bumpN hβ).mul (contDiff_negPsi hβ)) (R := 3)
      (fun s hs => by rw [bumpN_vanish hβ hs, zero_mul])
  have e := trH_mulHL hm 0 (mult_bumpN hβ m) (negPsiH m hβ hδ)
  rw [bumpN_zero hβ, one_mul] at e
  rw [← e, negPsiH, mulHL_mkH_toH (mult_bumpN hβ m) _ hT (fun x => rfl), trH_toH]
  simp [bumpN_zero hβ, negPsi_zero]

variable (m) in
/-- `v ↦ ([v_k]_0)_k`. -/
def trT : (Fin n → H (m + 1) zle) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => (trH (Nat.le_add_left 1 m) 0).comp (ContinuousLinearMap.proj k)

lemma trT_apply (v : Fin n → H (m + 1) zle) (k : Fin n) :
    trT m v k = trH (Nat.le_add_left 1 m) 0 (v k) := rfl

variable (m) in
/-- `c ↦ c ψ`: the kernel. -/
def psiL (hβ : IsCutoff β) (hδ : 0 < δ) : (Fin n → ℝ) →L[ℝ] (Fin n → H (m + 1) zle) :=
  ContinuousLinearMap.pi fun k => (ContinuousLinearMap.proj k).smulRight (negPsiH (m + 1) hβ hδ)

lemma psiL_apply (c : Fin n → ℝ) (k : Fin n) : psiL m hβ hδ c k = c k • negPsiH (m + 1) hβ hδ :=
  rfl

lemma Lop_psiL (c : Fin n → ℝ) : Lop m J hβ hδ.le (psiL m hβ hδ c) = 0 := Lop_negPsiH c

lemma trT_psiL (c : Fin n → ℝ) : trT m (psiL m hβ hδ c) = c := by
  funext k
  rw [trT_apply, psiL_apply, map_smul, trH_negPsiH, smul_eq_mul, mul_one]

lemma psiL_injective : Injective (psiL (n := n) m hβ hδ) := fun c c' h => by
  have := congrArg (trT m) h
  rwa [trT_psiL, trT_psiL] at this

end Kernel

/-! ## 2. Kernel, closed range, ontoness -/

section Onto

variable {m n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ}

/-- **`‖v‖ ≤ K (‖L v‖ + |[v]_0|)`** on `(H^{m+1})ⁿ`. -/
theorem norm_le_Lop_trT (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π) (m : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ v : Fin n → H (m + 1) zle,
      ‖v‖ ≤ K * (‖Lop m J hβ hδ.le v‖ + ‖trT m v‖) := by
  obtain ⟨C, hC, hCv⟩ := neg_estimate_sq hJ hβ hδ hπ m
  refine ⟨1 + C * n, by positivity, fun v => ?_⟩
  set S := ‖Lop m J hβ hδ.le v‖ + ‖trT m v‖
  have hS : 0 ≤ S := by positivity
  have h1 : ∑ k, ‖Lop m J hβ hδ.le v k‖ ^ 2 ≤ n * ‖Lop m J hβ hδ.le v‖ ^ 2 := by
    refine (Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
      (norm_le_pi_norm (Lop m J hβ hδ.le v) k) 2).trans (le_of_eq ?_)
    simp
  have h2 : ∑ k, trH (Nat.le_add_left 1 m) 0 (v k) ^ 2 ≤ n * ‖trT m v‖ ^ 2 := by
    refine (Finset.sum_le_sum fun k _ => ?_).trans (le_of_eq (by simp : ∑ _k : Fin n,
      ‖trT m v‖ ^ 2 = n * ‖trT m v‖ ^ 2))
    rw [← trT_apply, ← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (trT m v) k) 2
  have h3 : ‖Lop m J hβ hδ.le v‖ ^ 2 + ‖trT m v‖ ^ 2 ≤ S ^ 2 := by
    nlinarith [norm_nonneg (Lop m J hβ hδ.le v), norm_nonneg (trT m v)]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have hk : ‖v k‖ ^ 2 ≤ ∑ l, ‖v l‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖v l‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : ‖v k‖ ^ 2 ≤ ((1 + C * n) * S) ^ 2 := by
    have := hCv v
    have h5 : C * (∑ k, ‖Lop m J hβ hδ.le v k‖ ^ 2 + ∑ k, trH (Nat.le_add_left 1 m) 0 (v k) ^ 2)
        ≤ C * n * S ^ 2 := by
      calc _ ≤ C * (n * ‖Lop m J hβ hδ.le v‖ ^ 2 + n * ‖trT m v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
        _ = C * n * (‖Lop m J hβ hδ.le v‖ ^ 2 + ‖trT m v‖ ^ 2) := by ring
        _ ≤ C * n * S ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hC hn) (sq_nonneg S), sq_nonneg S,
      mul_nonneg (mul_nonneg (mul_nonneg hC hn) (mul_nonneg hC hn)) (sq_nonneg S)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-- **The kernel of `L` is `{c ψ}`**: `L v = 0 ↔ v = [v]_0 ψ`. -/
theorem Lop_eq_zero_iff (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π) (m : ℕ)
    (v : Fin n → H (m + 1) zle) :
    Lop m J hβ hδ.le v = 0 ↔ v = psiL m hβ hδ (trT m v) := by
  constructor
  · intro hv
    obtain ⟨K, hK, hKv⟩ := norm_le_Lop_trT hJ hβ hδ hπ m
    have h := hKv (v - psiL m hβ hδ (trT m v))
    simp only [map_sub, hv, Lop_psiL, trT_psiL, sub_self, norm_zero, add_zero,
      mul_zero] at h
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 h))
  · intro h
    rw [h]
    exact Lop_psiL _

/-- **The range of `L` is closed.** -/
theorem isClosed_range_Lop (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π)
    (m : ℕ) : IsClosed (range (Lop (n := n) m J hβ hδ.le)) := by
  obtain ⟨K, hK0, hK⟩ := norm_le_Lop_trT (n := n) hJ hβ hδ hπ m
  set N := LinearMap.ker (trT (n := n) m : (Fin n → H (m + 1) zle) →ₗ[ℝ] (Fin n → ℝ))
  have : CompleteSpace N := (ContinuousLinearMap.isClosed_ker (trT (n := n) m)).completeSpace_coe
  set L' := (Lop (n := n) m J hβ hδ.le).comp N.subtypeL
  have hb : ∀ x : N, ‖x‖ ≤ (Real.toNNReal K : ℝ) * ‖L' x‖ := by
    intro x
    have hx : trT m (x : Fin n → H (m + 1) zle) = 0 := x.2
    have := hK x
    rw [hx, norm_zero, add_zero] at this
    rw [Real.coe_toNNReal _ hK0]
    exact this
  have hcl := (L'.antilipschitz_of_bound hb).isClosed_range L'.uniformContinuous
  have heq : range (Lop (n := n) m J hβ hδ.le) = range L' := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨v - psiL m hβ hδ (trT m v), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, trT_psiL, sub_self]
      · simp [L', map_sub, Lop_psiL]
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  rw [heq]
  exact hcl

/-- **Conjugation by `ψ`**: `L (ψ u) = ψ (∂_s + J ∂_t) u`, since `ψ' = -a ψ`. -/
lemma Lop_conj (hβ : IsCutoff β) (hδ : 0 < δ) (u : Fin n → H (m + 1) zle) (k : Fin n) :
    Lop m J hβ hδ.le (fun l => mulHL (negPsi δ β) (mult_negPsi hβ hδ.le (m + 1)) (u l)) k =
      mulHL (negPsi δ β) (mult_negPsi hβ hδ.le m) (crOpW m zle J u k) := by
  rw [Lop_mulHL (mult_negPsi hβ hδ.le (m + 1)) (mult_negPsi hβ hδ.le m)
    (mult_deriv_negPsi hβ hδ.le m), Lop_apply, map_add, add_assoc,
    mulHL_mulHL_add (mult_negPsi hβ hδ.le m) (mult_negA hβ hδ.le m)
      (mult_deriv_negPsi hβ hδ.le m) (fun s => by rw [deriv_negPsi hβ]; ring), add_zero]

/-- **The test tuples are in the range of `L`.** -/
theorem test_mem_range_neg (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (m : ℕ)
    {g : Fin n → ℝ × ℝ → ℝ} (hg : ∀ k, IsTest (g k)) :
    (fun k => toH m zle (hg k)) ∈ range (Lop m J hβ hδ.le) := by
  have hE : ContDiff ℝ ∞ (fun s => Real.exp (δ * negH β s)) :=
    Real.contDiff_exp.comp (contDiff_const.mul (contDiff_negH hβ))
  have hφ : ∀ k, IsTest (fun x : ℝ × ℝ => Real.exp (δ * negH β x.1) * g k x) :=
    fun k => (hg k).mul_s hE
  obtain ⟨c, r, hr, hdr⟩ := exists_smooth_solution hJ hβ hφ
  have hr0 : ∀ l, SmoothW 0 (r l) := fun l => hr l 0 Real.two_pi_pos
  set A : Fin n → H (m + 1) zle :=
    fun l => mulHL (negPsi δ β) (mult_negPsi hβ hδ.le (m + 1)) (mkH (m + 1) zle (hr0 l))
  set B : Fin n → H (m + 1) zle :=
    fun l => mulHL β (mult_cut hβ (m + 1)) ((2 * c l) • negPsiH (m + 1) hβ hδ)
  have hβψ : IsTest (fun x : ℝ × ℝ => negPsi δ β x.1 * deriv β x.1) :=
    (isTest_dcut hβ).mul_s (contDiff_negPsi hβ)
  refine ⟨A - B, funext fun k => ?_⟩
  rw [map_sub, Pi.sub_apply]
  have hψk := (hφ k).add ((isTest_dcut hβ).const_mul (2 * c k))
  have eA : Lop m J hβ hδ.le A k = toH m zle (hψk.mul_s (contDiff_negPsi (δ := δ) hβ)) := by
    rw [Lop_conj hβ hδ, crOpW_mkH hr0 hψk k (fun x => hdr k x), mulHL_toH]
  have eB : Lop m J hβ hδ.le B k = (2 * c k) • toH m zle hβψ := by
    rw [Lop_mulHL (mult_cut hβ (m + 1)) (mult_cut hβ m) (mult_deriv_cut hβ m)]
    have h0 : Lop m J hβ hδ.le (fun l => (2 * c l) • negPsiH (m + 1) hβ hδ) k = 0 :=
      congrFun (Lop_negPsiH (fun l => 2 * c l)) k
    rw [h0, map_zero, zero_add, map_smul, map_smul, lowH_negPsiH, negPsiH,
      mulHL_mkH_toH (mult_deriv_cut hβ m) _ hβψ (fun x => mul_comm _ _)]
  rw [eA, eB]
  have hP : ∀ s, negPsi δ β s * Real.exp (δ * negH β s) = 1 := fun s => by
    rw [negPsi, ← Real.exp_add]; simp
  have e : toH m zle (hψk.mul_s (contDiff_negPsi (δ := δ) hβ)) =
      toH m zle ((hg k).add (hβψ.const_mul (2 * c k))) :=
    toH_congr (funext fun x => by
      simp only [Pi.add_apply]
      linear_combination g k x * hP x.1) _ _
  rw [e, toH_add_mul (hg k) hβψ, add_sub_cancel_right]

/-- **`L : (H^{m+1})ⁿ → (H^m)ⁿ` is onto**, for `0 < δ < π`. -/
theorem Lop_surjective (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π) (m : ℕ) :
    Surjective (Lop (n := n) m J hβ hδ.le) := by
  have hcl := isClosed_range_Lop (n := n) hJ hβ hδ hπ m
  set T : Set (H m zle) := {u | ∃ φ, ∃ hφ : IsTest φ, u = toH m zle hφ}
  have hD : Dense (Set.pi Set.univ fun _ : Fin n => T) :=
    dense_pi Set.univ fun k _ => dense_test m zle
  have hsub : Set.pi Set.univ (fun _ : Fin n => T) ⊆ range (Lop (n := n) m J hβ hδ.le) := by
    intro g hg
    simp only [Set.mem_pi, Set.mem_univ, true_implies, T, Set.mem_ofPred_eq] at hg
    choose φ hφ hgφ using hg
    have : g = fun k => toH m zle (hφ k) := funext hgφ
    rw [this]
    exact test_mem_range_neg hJ hβ hδ m hφ
  have := hD.closure_eq ▸ closure_minimal hsub hcl
  exact fun y => this (mem_univ y)

end Onto

/-! ## 3. The statements -/

section Statements

variable {n : ℕ} {J : Fin n → Fin n → ℝ} {β : ℝ → ℝ} {δ : ℝ}

/-- **`∂̄` on the spaces with growth `e^{δ|s|}`**, in the picture `u = e^{δ h} v`
(`h(s) = ∫₀^s (1 - 2β)`, so `h(s) = |s| + O(1)`, `h(0) = 0`; see `dbar_transport`): for
`J² = -1`, `0 < δ < π` and every `m`, `L = ∂_s + J ∂_t + δ (1 - 2β(s)) : (H^{m+1})ⁿ → (H^m)ⁿ`

* is onto;
* has kernel `{c ψ : c ∈ ℝⁿ}`, `ψ = e^{-δ h}`, which is `u = c`: the constants;
* satisfies `∑_k ‖v_k‖²_{m+1} ≤ C (∑_k ‖(L v)_k‖²_m + ∑_k [v_k]_0²)`, the estimate modulo the
  average `[u]_0 = [v]_0`.

Memoir Proposition 4.16, p. 110, takes `0 < δ < 2π`. The proof here treats the circle modes
`≠ 0` of `v - [v]` together, by one gap inequality and the bound `|a| ≤ δ`, and this needs
`δ < π`. The range `π ≤ δ < 2π` needs the estimate mode by mode in `t` (the mode `k ≠ 0` has
the gap `2π|k| - δ > 0`); the weights `nodeWeights` (`δ_m = π - 1/(m+2)`) lie below `π`. -/
theorem cyl_dbar_neg (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π) (m : ℕ) :
    Surjective (Lop (n := n) m J hβ hδ.le) ∧
    (∀ v : Fin n → H (m + 1) zle,
      Lop m J hβ hδ.le v = 0 ↔ ∃ c : Fin n → ℝ, v = fun k => c k • negPsiH (m + 1) hβ hδ) ∧
    ∃ C, 0 ≤ C ∧ ∀ v : Fin n → H (m + 1) zle,
      ∑ k, ‖v k‖ ^ 2 ≤ C * (∑ k, ‖Lop m J hβ hδ.le v k‖ ^ 2 +
        ∑ k, trH (Nat.le_add_left 1 m) 0 (v k) ^ 2) := by
  refine ⟨Lop_surjective hJ hβ hδ hπ m, fun v => ?_, neg_estimate_sq hJ hβ hδ hπ m⟩
  constructor
  · intro h
    exact ⟨trT m v, (Lop_eq_zero_iff hJ hβ hδ hπ m v).1 h⟩
  · rintro ⟨c, rfl⟩
    exact Lop_negPsiH c

/-- **Memoir Proposition 4.16, p. 110**, the `a`-free core. After the translation by `R/2`
(Memoir §5.8, p. 170) the operator is `∂̄₀` on `H^{3+m,-δ_m}(ℝ × S¹)`; in the picture
`u = e^{δ h} v` of `cyl_dbar_neg`, with `ℝⁿ` in place of `ℂⁿ` (`J² = -1`, so `n` is the real
dimension, `2n` in the Memoir's count) and `0 < δ < π`, for every `m`:

* `L : (H^{m+1})ⁿ → (H^m)ⁿ` is onto;
* its kernel is `{c ψ}`, of dimension `n`: the constants `u = c`. So `L` is Fredholm of index
  `n`. The sentence of p. 170, that this operator is a surjective Fredholm operator whose
  kernel consists of the constants, is proved here;
* (4.9) in the centred form: with `w = v - [v]_0 ψ` (so `[w]_0 = 0`; this is `u - [u]_0`),
  `(1/C) ‖w‖ ≤ ‖L w‖ ≤ C ‖w‖`.

The Memoir states (4.9) on the finite cylinders `Z_a^*` with the norms (4.7)/(4.8) and `C_m`
independent of `a`; that form needs the `a`-dependent gluing and is not stated here. The
spaces are the `v`-spaces `H^m`; the identification with `H^{m,-δ}` through `e^{δh}` is the
pointwise identity `dbar_transport` and is not formalized as an isomorphism of normed spaces. -/
theorem memoir_proposition_4_16 (hJ : IsCxMat J) (hβ : IsCutoff β) (hδ : 0 < δ) (hπ : δ < π)
    (m : ℕ) :
    Surjective (Lop (n := n) m J hβ hδ.le) ∧
    Module.finrank ℝ (LinearMap.ker
      (Lop (n := n) m J hβ hδ.le : (Fin n → H (m + 1) zle) →ₗ[ℝ] (Fin n → H m zle))) = n ∧
    ∃ C, 0 < C ∧ ∀ v : Fin n → H (m + 1) zle,
      trT m (v - psiL m hβ hδ (trT m v)) = 0 ∧
      1 / C * ‖v - psiL m hβ hδ (trT m v)‖ ≤ ‖Lop m J hβ hδ.le (v - psiL m hβ hδ (trT m v))‖ ∧
      ‖Lop m J hβ hδ.le (v - psiL m hβ hδ (trT m v))‖ ≤ C * ‖v - psiL m hβ hδ (trT m v)‖ := by
  refine ⟨Lop_surjective hJ hβ hδ hπ m, ?_, ?_⟩
  · have hker : LinearMap.ker
        (Lop (n := n) m J hβ hδ.le : (Fin n → H (m + 1) zle) →ₗ[ℝ] (Fin n → H m zle)) =
        LinearMap.range (psiL (n := n) m hβ hδ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → H (m + 1) zle)) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
      constructor
      · intro h
        exact ⟨trT m v, ((Lop_eq_zero_iff hJ hβ hδ hπ m v).1 h).symm⟩
      · rintro ⟨c, rfl⟩
        exact Lop_psiL c
    rw [hker, LinearMap.finrank_range_of_inj (by exact psiL_injective), Module.finrank_fin_fun]
  · obtain ⟨K, hK0, hK⟩ := norm_le_Lop_trT (n := n) hJ hβ hδ hπ m
    set Lm := Lop (n := n) m J hβ hδ.le
    refine ⟨K + ‖Lm‖ + 1, by positivity, fun v => ?_⟩
    have ht : trT m (v - psiL m hβ hδ (trT m v)) = 0 := by rw [map_sub, trT_psiL, sub_self]
    refine ⟨ht, ?_, ?_⟩
    · have h := hK (v - psiL m hβ hδ (trT m v))
      rw [ht, norm_zero, add_zero] at h
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (Lm (v - psiL m hβ hδ (trT m v))), norm_nonneg Lm]
    · refine (Lm.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by linarith)
        (norm_nonneg _))

/-- The hypotheses are satisfiable: `J = Jstd`, `β = stdCutoff`, `δ = 1`. -/
theorem memoir_proposition_4_16_hyps : IsCxMat Jstd ∧ IsCutoff stdCutoff ∧ (0 : ℝ) < 1 ∧
    (1 : ℝ) < π :=
  ⟨isCxMat_Jstd, isCutoff_stdCutoff, one_pos, by linarith [Real.pi_gt_three]⟩

/-- **The transport `u = e^{δ h} v`**: `∂̄ (e^{δh} v) = e^{δh} L v` for differentiable `v`. -/
theorem dbar_transport (hβ : IsCutoff β) {r : Fin n → ℝ × ℝ → ℝ}
    (hr : ∀ k, Differentiable ℝ (r k)) (k : Fin n) (x : ℝ × ℝ) :
    dbarCyl J (fun l y => Real.exp (δ * negH β y.1) * r l y) k x =
      Real.exp (δ * negH β x.1) * negL J (negA δ β) r k x := by
  have hE : Differentiable ℝ (fun s => Real.exp (δ * negH β s)) :=
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_negH hβ))).differentiable (by simp)
  have hdE : deriv (fun s => Real.exp (δ * negH β s)) x.1 =
      negA δ β x.1 * Real.exp (δ * negH β x.1) := by
    have := (((hasDerivAt_negH hβ x.1).const_mul δ).exp)
    rw [this.deriv, negA]; ring
  simp only [dbarCyl, negL]
  rw [Ds_mul_s (hr k) hE]
  have hD : ∀ l, Dt (fun y => Real.exp (δ * negH β y.1) * r l y) =
      fun y => Real.exp (δ * negH β y.1) * Dt (r l) y := fun l => Dt_mul_s (hr l) hE
  simp only [hD, hdE]
  rw [mul_add, mul_add, Finset.mul_sum]
  simp only [mul_left_comm (Real.exp _)]
  ring

end Statements

end GWMemoir.NeckNeg
