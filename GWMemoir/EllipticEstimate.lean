import GWMemoir.LinearCRKernel

/-!
# The elliptic estimate for `∂_s + J ∂_t` on the cylinder

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4: the elliptic estimate
behind the Fredholm property of the linearized Cauchy–Riemann operator, in its constant-coefficient
form on `ℝ × S¹` without weights.

* `cross_sq_le`: in a real inner product space, if `⟪A_k, B_l⟫ = ⟪A_l, B_k⟫` and `J² = -1`, then
  `∑ ‖A_k‖² + ‖B_k‖² ≤ (1 + ∑ J_{kl}²) ∑ ‖A_k + ∑_l J_{kl} B_l‖²`.  With `X = A + J B` one has
  `J X = J A - B`, and the cross terms of `‖X‖² + ‖J X‖²` cancel.
* `ibp_cross`: `∫ ∂_s φ ∂_t ψ = ∫ ∂_t φ ∂_s ψ` for test functions (integration by parts twice),
  and `cross_sym`: the same for the weak derivatives `∂_s ∂^p u`, `∂_t ∂^p v` of `u, v ∈ H^{m+1,0}`
  (density of the test functions).
* `norm_sq_le_shift`: `‖u‖²_{m+1} ≤ ‖u‖²_{L²} + ‖∂_s u‖²_m + ‖∂_t u‖²_m`.
* **`cyl_estimate_sq`**, **`cyl_estimate`**: for a tuple `g ∈ (H^{m+1,0})ⁿ` and a matrix `J` with
  `J² = -1`, `‖g‖_{H^{m+1}} ≤ C (‖g‖_{L²} + ‖∂_s g + J ∂_t g‖_{H^m})`.
* The disc charts of `S²` (stereographic) are conformal (`chartInv_conformal`), so `j` read in
  a chart is a rotation by a right angle (`jMat_skew`, `jMat_sq`), and **`jMat_disc_const`**:
  in each disc chart `j ∂_s = b ∂_t` with a constant `b = ±1`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology InnerProductSpace
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The algebra -/

section Algebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- A matrix with `J² = -1`. -/
def IsCxMat (J : Fin n → Fin n → ℝ) : Prop :=
  ∀ k l, ∑ j, J k j * J j l = if k = l then -1 else 0

lemma sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  rw [sq (∑ i ∈ s, f i), Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hf hi) (hf i hi)

lemma sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) : ∑ a ∈ s ∪ t, f a ≤ ∑ a ∈ s, f a + ∑ a ∈ t, f a := by
  rw [← Finset.sum_union_inter]
  linarith [Finset.sum_nonneg fun a (_ : a ∈ s ∩ t) => hf a]

/-- **The algebraic core of the estimate**: with `X = A + J B`, `J X = J A - B`, and the cross
terms of `‖X‖² + ‖J X‖²` cancel when `⟪A_k, B_l⟫` is symmetric. -/
theorem cross_sq_le (J : Fin n → Fin n → ℝ) (hJ : IsCxMat J) (A B : Fin n → V)
    (hAB : ∀ k l, ⟪A k, B l⟫_ℝ = ⟪A l, B k⟫_ℝ) :
    ∑ k, (‖A k‖ ^ 2 + ‖B k‖ ^ 2) ≤
      (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ‖A k + ∑ l, J k l • B l‖ ^ 2 := by
  set X : Fin n → V := fun k => A k + ∑ l, J k l • B l with hX
  set S : Fin n → V := fun k => ∑ l, J k l • B l with hS
  set T : Fin n → V := fun k => ∑ l, J k l • A l with hT
  have hY : ∀ k, ∑ l, J k l • X l = T k - B k := by
    intro k
    simp only [hX, hT, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun l j => (J k l * J l j) • B j), sub_eq_add_neg]
    congr 1
    simp_rw [← Finset.sum_smul, hJ k, ite_smul, zero_smul, neg_one_smul]
    simp
  have hcross : ∑ k, ⟪A k, S k⟫_ℝ = ∑ k, ⟪T k, B k⟫_ℝ := by
    simp only [hS, hT, inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hAB]
  have hXn : ∀ k, ‖X k‖ ^ 2 = ‖A k‖ ^ 2 + 2 * ⟪A k, S k⟫_ℝ + ‖S k‖ ^ 2 := fun k =>
    norm_add_sq_real _ _
  have hYn : ∀ k, ‖T k - B k‖ ^ 2 = ‖T k‖ ^ 2 - 2 * ⟪T k, B k⟫_ℝ + ‖B k‖ ^ 2 := fun k =>
    norm_sub_sq_real _ _
  have hid : ∑ k, ‖X k‖ ^ 2 + ∑ k, ‖T k - B k‖ ^ 2 =
      ∑ k, (‖A k‖ ^ 2 + ‖B k‖ ^ 2) + ∑ k, ‖S k‖ ^ 2 + ∑ k, ‖T k‖ ^ 2 := by
    simp only [hXn, hYn, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hcross]
    ring
  have hYb : ∀ k, ‖T k - B k‖ ^ 2 ≤ (∑ l, J k l ^ 2) * ∑ l, ‖X l‖ ^ 2 := by
    intro k
    rw [← hY k]
    have h1 : ‖∑ l, J k l • X l‖ ≤ ∑ l, |J k l| * ‖X l‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => by
        rw [norm_smul, Real.norm_eq_abs]))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => |J k l|) (fun l => ‖X l‖)
    simp only [sq_abs] at h2
    calc ‖∑ l, J k l • X l‖ ^ 2 ≤ (∑ l, |J k l| * ‖X l‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hYs : ∑ k, ‖T k - B k‖ ^ 2 ≤ (∑ k, ∑ l, J k l ^ 2) * ∑ l, ‖X l‖ ^ 2 := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun k _ => hYb k
  have h0 : 0 ≤ ∑ k, ‖S k‖ ^ 2 + ∑ k, ‖T k‖ ^ 2 := by positivity
  change _ ≤ (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ‖X k‖ ^ 2
  nlinarith

end Algebra

/-! ## 2. Integration by parts and the cross symmetry -/

section Cross

lemma wt_zero (x : ℝ × ℝ) : wt 0 x = 1 := by simp [wt]

lemma inner_L2_eq (f g : Lp ℝ 2 cyl) : ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂cyl := by
  rw [L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [mul_comm]

/-- `∫ ∂_s φ ∂_t ψ = ∫ ∂_t φ ∂_s ψ` for test functions. -/
lemma ibp_cross {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) :
    ∫ x, Ds φ x * Dt ψ x ∂cyl = ∫ x, Dt φ x * Ds ψ x ∂cyl := by
  have h1 := hψ.dt.smPer.integral_mul_ds hφ
  have h2 := hψ.ds.smPer.integral_mul_dt hφ
  rw [Ds_Dt hψ.smooth] at h1
  have e1 : ∫ x, Ds φ x * Dt ψ x ∂cyl = ∫ x, Dt ψ x * Ds φ x ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  have e2 : ∫ x, Dt φ x * Ds ψ x ∂cyl = ∫ x, Ds ψ x * Dt φ x ∂cyl :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [e1, e2, h1, h2]

variable {m : ℕ}

lemma shS_mem (p : CylinderSobolev.idx m) : shS p.1 ∈ CylinderSobolev.idx (m + 1) :=
  mem_idx.2 (by have := mem_idx.1 p.2; change p.1.1 + 1 + p.1.2 ≤ m + 1; omega)

lemma shT_mem (p : CylinderSobolev.idx m) : shT p.1 ∈ CylinderSobolev.idx (m + 1) :=
  mem_idx.2 (by have := mem_idx.1 p.2; change p.1.1 + (p.1.2 + 1) ≤ m + 1; omega)

lemma wdv_ae_dv0 (u : H m (le_refl (0 : ℝ))) (p : CylinderSobolev.idx m) :
    (wdv (H.toSub u) p : ℝ × ℝ → ℝ) =ᵐ[cyl] dv (H.toSub u) p := by
  filter_upwards [coeFn_wdv (H.toSub u) p] with x hx
  rw [hx, wt_zero, one_mul]

lemma wdv_toH_ae {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (p : CylinderSobolev.idx m) :
    (wdv (H.toSub (toH m (le_refl (0 : ℝ)) hφ)) p : ℝ × ℝ → ℝ) =ᵐ[cyl] pD p.1.1 p.1.2 φ :=
  (wdv_ae_dv0 _ p).trans (dv_unique _ p ((hφ.smPer.hasWeakDeriv _ _).congr_ae
    (hφ.memLp 2).coeFn_toLp.symm (ae_eq_refl _)) ((hφ.pD _ _).memLp 2))

/-- **The cross symmetry** `⟪∂_s ∂^p u, ∂_t ∂^p v⟫ = ⟪∂_t ∂^p u, ∂_s ∂^p v⟫` on `H^{m+1,0}`. -/
theorem cross_sym (u v : H (m + 1) (le_refl (0 : ℝ))) (p : CylinderSobolev.idx m) :
    ⟪wdv (H.toSub u) ⟨shS p.1, shS_mem p⟩, wdv (H.toSub v) ⟨shT p.1, shT_mem p⟩⟫_ℝ =
      ⟪wdv (H.toSub u) ⟨shT p.1, shT_mem p⟩, wdv (H.toSub v) ⟨shS p.1, shS_mem p⟩⟫_ℝ := by
  set qS : CylinderSobolev.idx (m + 1) := ⟨shS p.1, shS_mem p⟩
  set qT : CylinderSobolev.idx (m + 1) := ⟨shT p.1, shT_mem p⟩
  set W := wdvCLM (m + 1) (le_refl (0 : ℝ))
  change ⟪W qS u, W qT v⟫_ℝ = ⟪W qT u, W qS v⟫_ℝ
  have htest : ∀ {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ),
      ⟪W qS (toH (m + 1) _ hφ), W qT (toH (m + 1) _ hψ)⟫_ℝ =
        ⟪W qT (toH (m + 1) _ hφ), W qS (toH (m + 1) _ hψ)⟫_ℝ := by
    intro φ ψ hφ hψ
    change ⟪wdv _ qS, wdv _ qT⟫_ℝ = ⟪wdv _ qT, wdv _ qS⟫_ℝ
    rw [inner_L2_eq, inner_L2_eq]
    have eS : ∀ {χ : ℝ × ℝ → ℝ} (hχ : IsTest χ),
        (wdv (H.toSub (toH (m + 1) (le_refl (0 : ℝ)) hχ)) qS : ℝ × ℝ → ℝ) =ᵐ[cyl]
          Ds (pD p.1.1 p.1.2 χ) := fun hχ => by
      refine (wdv_toH_ae hχ qS).trans (ae_of_all _ fun x => ?_)
      change pD (p.1.1 + 1) p.1.2 _ x = _
      rw [← ChartChange.Ds_pD]
    have eT : ∀ {χ : ℝ × ℝ → ℝ} (hχ : IsTest χ),
        (wdv (H.toSub (toH (m + 1) (le_refl (0 : ℝ)) hχ)) qT : ℝ × ℝ → ℝ) =ᵐ[cyl]
          Dt (pD p.1.1 p.1.2 χ) := fun hχ => by
      refine (wdv_toH_ae hχ qT).trans (ae_of_all _ fun x => ?_)
      change pD p.1.1 (p.1.2 + 1) _ x = _
      rw [← ChartChange.Dt_pD hχ.smooth]
    have i1 : (fun x => (wdv (H.toSub (toH (m + 1) (le_refl (0 : ℝ)) hφ)) qS : ℝ × ℝ → ℝ) x *
        (wdv (H.toSub (toH (m + 1) (le_refl (0 : ℝ)) hψ)) qT : ℝ × ℝ → ℝ) x) =ᵐ[cyl]
        fun x => Ds (pD p.1.1 p.1.2 φ) x * Dt (pD p.1.1 p.1.2 ψ) x := by
      filter_upwards [eS hφ, eT hψ] with x h1 h2; rw [h1, h2]
    have i2 : (fun x => (wdv (H.toSub (toH (m + 1) (le_refl (0 : ℝ)) hφ)) qT : ℝ × ℝ → ℝ) x *
        (wdv (H.toSub (toH (m + 1) (le_refl (0 : ℝ)) hψ)) qS : ℝ × ℝ → ℝ) x) =ᵐ[cyl]
        fun x => Dt (pD p.1.1 p.1.2 φ) x * Ds (pD p.1.1 p.1.2 ψ) x := by
      filter_upwards [eT hφ, eS hψ] with x h1 h2; rw [h1, h2]
    rw [integral_congr_ae i1, integral_congr_ae i2]
    exact ibp_cross (hφ.pD _ _) (hψ.pD _ _)
  have hD := dense_test (m + 1) (le_refl (0 : ℝ))
  have step1 : ∀ {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (v : H (m + 1) (le_refl (0 : ℝ))),
      ⟪W qS (toH (m + 1) _ hφ), W qT v⟫_ℝ = ⟪W qT (toH (m + 1) _ hφ), W qS v⟫_ℝ := by
    intro φ hφ v
    have hc : IsClosed {v : H (m + 1) (le_refl (0 : ℝ)) |
        ⟪W qS (toH (m + 1) _ hφ), W qT v⟫_ℝ = ⟪W qT (toH (m + 1) _ hφ), W qS v⟫_ℝ} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub := closure_minimal (s := {u : H (m + 1) (le_refl (0 : ℝ)) |
      ∃ ψ, ∃ hψ : IsTest ψ, u = toH (m + 1) _ hψ}) (by
        rintro _ ⟨ψ, hψ, rfl⟩; exact htest hφ hψ) hc
    rw [hD.closure_eq] at hsub
    exact hsub (mem_univ v)
  have hc : IsClosed {u : H (m + 1) (le_refl (0 : ℝ)) |
      ⟪W qS u, W qT v⟫_ℝ = ⟪W qT u, W qS v⟫_ℝ} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub := closure_minimal (s := {u : H (m + 1) (le_refl (0 : ℝ)) |
    ∃ φ, ∃ hφ : IsTest φ, u = toH (m + 1) _ hφ}) (by
      rintro _ ⟨φ, hφ, rfl⟩; exact step1 hφ v) hc
  rw [hD.closure_eq] at hsub
  exact hsub (mem_univ u)

end Cross

/-! ## 3. The estimate -/

section Estimate

variable {m n : ℕ}

lemma norm_wdv_idx0 (u : H m (le_refl (0 : ℝ))) :
    ‖wdv (H.toSub u) (CylinderSobolev.idx0 m)‖ = ‖H.val u‖ := by
  congr 1
  exact Lp.ext ((wdv_ae_dv0 u _).trans (dv_idx0 _))

lemma norm_H00 (u : H 0 (le_refl (0 : ℝ))) : ‖u‖ = ‖H.val u‖ := by
  have h := norm_sq_H u
  rw [Fintype.sum_eq_single (CylinderSobolev.idx0 0) fun p hp => absurd (Subtype.ext (by
    have := mem_idx.1 p.2
    exact Prod.ext (by change p.1.1 = 0; omega) (by change p.1.2 = 0; omega))) hp,
    norm_wdv_idx0] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `‖u‖²_{m+1} ≤ ‖u‖²_{(0,0)} + ∑_{p ∈ idx m} (‖∂_s ∂^p u‖² + ‖∂_t ∂^p u‖²)`. -/
lemma norm_sq_le_shift {δ : ℝ} {hδ : 0 ≤ δ} (u : H (m + 1) hδ) :
    ‖u‖ ^ 2 ≤ ‖wdv (H.toSub u) (CylinderSobolev.idx0 (m + 1))‖ ^ 2 + ∑ p : CylinderSobolev.idx m,
      (‖wdv (H.toSub u) ⟨shS p.1, shS_mem p⟩‖ ^ 2 +
        ‖wdv (H.toSub u) ⟨shT p.1, shT_mem p⟩‖ ^ 2) := by
  classical
  set F : ℕ × ℕ → ℝ := fun q => if hq : q ∈ CylinderSobolev.idx (m + 1) then
    ‖wdv (H.toSub u) ⟨q, hq⟩‖ ^ 2 else 0 with hF
  have hF0 : ∀ q, 0 ≤ F q := fun q => by simp only [hF]; split_ifs <;> positivity
  have hFp : ∀ p : CylinderSobolev.idx (m + 1), F p.1 = ‖wdv (H.toSub u) p‖ ^ 2 := fun p => by
    simp only [hF, dif_pos p.2]
  have hsub : CylinderSobolev.idx (m + 1) ⊆
      {(0, 0)} ∪ ((CylinderSobolev.idx m).map shS ∪ (CylinderSobolev.idx m).map shT) := by
    intro q hq
    have hq' := mem_idx.1 hq
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_map]
    by_cases h1 : q.1 = 0
    · by_cases h2 : q.2 = 0
      · left; exact Prod.ext h1 h2
      · right; right
        refine ⟨(q.1, q.2 - 1), mem_idx.2 (by simp only; omega), ?_⟩
        change (q.1, q.2 - 1 + 1) = q
        exact Prod.ext rfl (by simp only; omega)
    · right; left
      refine ⟨(q.1 - 1, q.2), mem_idx.2 (by simp only; omega), ?_⟩
      change (q.1 - 1 + 1, q.2) = q
      exact Prod.ext (by simp only; omega) rfl
  rw [norm_sq_H]
  calc ∑ p : CylinderSobolev.idx (m + 1), ‖wdv (H.toSub u) p‖ ^ 2 =
        ∑ q ∈ CylinderSobolev.idx (m + 1), F q := by
        rw [← Finset.sum_coe_sort (CylinderSobolev.idx (m + 1)) F]
        exact Finset.sum_congr rfl fun p _ => (hFp p).symm
    _ ≤ ∑ q ∈ {(0, 0)} ∪ ((CylinderSobolev.idx m).map shS ∪ (CylinderSobolev.idx m).map shT), F q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hF0 q
    _ ≤ F (0, 0) + (∑ q ∈ (CylinderSobolev.idx m).map shS, F q +
        ∑ q ∈ (CylinderSobolev.idx m).map shT, F q) := by
        refine (sum_union_le _ _ hF0).trans ?_
        rw [Finset.sum_singleton]
        exact add_le_add le_rfl (sum_union_le _ _ hF0)
    _ = _ := by
        rw [Finset.sum_map, Finset.sum_map, ← Finset.sum_coe_sort (CylinderSobolev.idx m),
          ← Finset.sum_coe_sort (CylinderSobolev.idx m), ← Finset.sum_add_distrib]
        congr 1
        · exact hFp (CylinderSobolev.idx0 (m + 1))
        · refine Finset.sum_congr rfl fun p _ => ?_
          rw [hFp ⟨shS p.1, shS_mem p⟩, hFp ⟨shT p.1, shT_mem p⟩]

lemma wdv_dsH {δ : ℝ} {hδ : 0 ≤ δ} (u : H (m + 1) hδ) (p : CylinderSobolev.idx m) :
    wdvCLM m hδ p (dsH m hδ u) = wdv (H.toSub u) ⟨shS p.1, shS_mem p⟩ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_wdv (H.toSub (dsH m hδ u)) p,
    coeFn_wdv (H.toSub u) ⟨shS p.1, shS_mem p⟩, dv_dsL u p] with x h1 h2 h3
  change wdv (H.toSub (dsH m hδ u)) p x = _
  rw [h1, h2]
  exact congrArg (wt δ x * ·) h3

lemma wdv_dtH {δ : ℝ} {hδ : 0 ≤ δ} (u : H (m + 1) hδ) (p : CylinderSobolev.idx m) :
    wdvCLM m hδ p (dtH m hδ u) = wdv (H.toSub u) ⟨shT p.1, shT_mem p⟩ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_wdv (H.toSub (dtH m hδ u)) p,
    coeFn_wdv (H.toSub u) ⟨shT p.1, shT_mem p⟩, dv_dtL u p] with x h1 h2 h3
  change wdv (H.toSub (dtH m hδ u)) p x = _
  rw [h1, h2]
  exact congrArg (wt δ x * ·) h3

variable (J : Fin n → Fin n → ℝ)

variable (m) in
/-- **`∂_s + J ∂_t`** on tuples: `(g_k) ↦ ∂_s g_k + ∑_l J_{kl} ∂_t g_l`. -/
def crOp (g : Fin n → H (m + 1) (le_refl (0 : ℝ))) (k : Fin n) : H m (le_refl (0 : ℝ)) :=
  dsH m (le_refl (0 : ℝ)) (g k) + ∑ l, J k l • dtH m (le_refl (0 : ℝ)) (g l)

lemma wdv_crOp (g : Fin n → H (m + 1) (le_refl (0 : ℝ))) (k : Fin n) (p : CylinderSobolev.idx m) :
    wdv (H.toSub (crOp m J g k)) p = wdv (H.toSub (g k)) ⟨shS p.1, shS_mem p⟩ +
      ∑ l, J k l • wdv (H.toSub (g l)) ⟨shT p.1, shT_mem p⟩ := by
  change wdvCLM m _ p (crOp m J g k) = _
  simp only [crOp, map_add, map_sum, map_smul, wdv_dsH, wdv_dtH]

/-- **The estimate for `∂_s + J ∂_t` on `ℝ × S¹`**, squared form. -/
theorem cyl_estimate_sq (hJ : IsCxMat J) (g : Fin n → H (m + 1) (le_refl (0 : ℝ))) :
    ∑ k, ‖g k‖ ^ 2 ≤ ∑ k, ‖H.val (g k)‖ ^ 2 +
      (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ‖crOp m J g k‖ ^ 2 := by
  let A : CylinderSobolev.idx m → Fin n → Lp ℝ 2 cyl := fun p k =>
    wdv (H.toSub (g k)) ⟨shS p.1, shS_mem p⟩
  let B : CylinderSobolev.idx m → Fin n → Lp ℝ 2 cyl := fun p k =>
    wdv (H.toSub (g k)) ⟨shT p.1, shT_mem p⟩
  have hp : ∀ p, ∑ k, (‖A p k‖ ^ 2 + ‖B p k‖ ^ 2) ≤
      (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ‖wdv (H.toSub (crOp m J g k)) p‖ ^ 2 := by
    intro p
    simp only [wdv_crOp]
    exact cross_sq_le J hJ (A p) (B p) fun k l =>
      (cross_sym (g k) (g l) p).trans (real_inner_comm _ _)
  calc ∑ k, ‖g k‖ ^ 2 ≤
      ∑ k, (‖H.val (g k)‖ ^ 2 + ∑ p : CylinderSobolev.idx m, (‖A p k‖ ^ 2 + ‖B p k‖ ^ 2)) :=
        Finset.sum_le_sum fun k _ => by
          have := norm_sq_le_shift (g k)
          rwa [norm_wdv_idx0] at this
    _ = ∑ k, ‖H.val (g k)‖ ^ 2 + ∑ p : CylinderSobolev.idx m, ∑ k, (‖A p k‖ ^ 2 + ‖B p k‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ k, ‖H.val (g k)‖ ^ 2 + ∑ p : CylinderSobolev.idx m,
          (1 + ∑ k, ∑ l, J k l ^ 2) * ∑ k, ‖wdv (H.toSub (crOp m J g k)) p‖ ^ 2 :=
        add_le_add le_rfl (Finset.sum_le_sum fun p _ => hp p)
    _ = _ := by
        congr 1
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (norm_sq_H _).symm

/-- **The estimate for `∂_s + J ∂_t` on `ℝ × S¹`**: `‖g_k‖_{H^{m+1,0}} ≤ C (∑ ‖g_l‖_{L²} +
∑ ‖(∂_s + J ∂_t) g‖_{H^{m,0}})`. -/
theorem cyl_estimate (hJ : IsCxMat J) (m : ℕ) : ∃ C, ∀ (g : Fin n → H (m + 1) (le_refl (0 : ℝ)))
    (k : Fin n), ‖g k‖ ≤ C * (∑ l, ‖H.val (g l)‖ + ∑ l, ‖crOp m J g l‖) := by
  set C0 := 1 + ∑ k, ∑ l, J k l ^ 2
  have hC0 : 1 ≤ C0 := le_add_of_nonneg_right (by positivity)
  refine ⟨1 + C0, fun g k => ?_⟩
  set S := ∑ l, ‖H.val (g l)‖ + ∑ l, ‖crOp m J g l‖
  have ha : ∑ l, ‖H.val (g l)‖ ^ 2 ≤ S ^ 2 :=
    (sum_sq_le_sq_sum _ fun _ _ => norm_nonneg _).trans
      (pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_right (by positivity)) 2)
  have hb : ∑ l, ‖crOp m J g l‖ ^ 2 ≤ S ^ 2 :=
    (sum_sq_le_sq_sum _ fun _ _ => norm_nonneg _).trans
      (pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_left (by positivity)) 2)
  have hk : ‖g k‖ ^ 2 ≤ ∑ l, ‖g l‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖g l‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
  have hsq := cyl_estimate_sq J hJ g
  have hS : 0 ≤ S := by positivity
  have h2 : ‖g k‖ ^ 2 ≤ ((1 + C0) * S) ^ 2 := by
    have : C0 * ∑ l, ‖crOp m J g l‖ ^ 2 ≤ C0 * S ^ 2 := mul_le_mul_of_nonneg_left hb (by linarith)
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end Estimate

/-! ## 4. The complex structure of `S²` in the disc charts -/

section Stereo
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]


lemma fderiv_stereoAux_apply (v x h : F) : fderiv ℝ (stereoInvFunAux v) x h =
    (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • h + (2 * ⟪x, h⟫_ℝ) • v) +
      (-((‖x‖ ^ 2 + 4) ^ 2)⁻¹ * (2 * ⟪x, h⟫_ℝ)) • ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • v) := by
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hN : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have h1 := (hasFDerivAt_inv hN).comp x (hn.add_const 4)
  have h2 := ((hasFDerivAt_id x).const_smul (4 : ℝ)).add ((hn.sub_const 4).smul_const v)
  have h3 := h1.smul h2
  have h4 : HasFDerivAt (stereoInvFunAux v) _ x :=
    h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [stereoInvFunAux])
  rw [h4.fderiv]
  simp
  module

lemma stereoAux_conformal (v x h k : F) (hv : ‖v‖ = 1) (hx : ⟪x, v⟫_ℝ = 0) (hh : ⟪h, v⟫_ℝ = 0)
    (hk : ⟪k, v⟫_ℝ = 0) :
    ⟪fderiv ℝ (stereoInvFunAux v) x h, fderiv ℝ (stereoInvFunAux v) x k⟫_ℝ =
      16 / (‖x‖ ^ 2 + 4) ^ 2 * ⟪h, k⟫_ℝ := by
  have hN : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hv' : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hxx : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  rw [fderiv_stereoAux_apply, fderiv_stereoAux_apply]
  have hx' : ⟪v, x⟫_ℝ = 0 := by rw [real_inner_comm]; exact hx
  have hh' : ⟪v, h⟫_ℝ = 0 := by rw [real_inner_comm]; exact hh
  have hk' : ⟪v, k⟫_ℝ = 0 := by rw [real_inner_comm]; exact hk
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hx, hh,
    hv', hxx, hx', hk']
  rw [real_inner_comm h x, real_inner_comm k x]
  field_simp
  ring

end Stereo

/-- The inverse of the chart of `S²` at `z`, read in `ℝ³`. -/
def chartInv (z : S2) (w : E2) : E3 := ((extChartAt 𝓘(ℝ, E2) z).symm w : E3)

/-- The isometry of the chart at `z`. -/
def chartU (z : S2) : (ℝ ∙ ((-z : S2) : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere (-z))).repr

/-- The inclusion `E2 → E3` of the tangent plane at `-z`, through `chartU`. -/
def chartV (z : S2) : E2 →L[ℝ] E3 :=
  (Submodule.subtypeL _).comp (chartU z).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma chartInv_eq (z : S2) (w : E2) :
    chartInv z w = stereoInvFunAux ((-z : S2) : E3) (chartV z w) := by
  have h := stereographic'_symm_apply (n := 2) (-z) w
  simp only [chartInv, extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply,
    id_eq]
  change ((stereographic' 2 (-z)).symm w : E3) = _
  rw [h, stereoInvFunAux_apply, smul_add]
  rfl

lemma inner_chartV (z : S2) (a b : E2) : ⟪chartV z a, chartV z b⟫_ℝ = ⟪a, b⟫_ℝ := by
  change ⟪(((chartU z).symm a : (ℝ ∙ ((-z : S2) : E3))ᗮ) : E3), ((chartU z).symm b : E3)⟫_ℝ = _
  rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]

lemma chartV_perp (z : S2) (a : E2) : ⟪chartV z a, ((-z : S2) : E3)⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left.1 ((chartU z).symm a).2

/-- **The chart of `S²` is conformal**: `⟪D(ι ∘ φ⁻¹) a, D(ι ∘ φ⁻¹) b⟫ = c ⟪a, b⟫`, `c > 0`. -/
lemma chartInv_conformal (z : S2) (w : E2) : ∃ c > 0, ∀ a b : E2,
    ⟪fderiv ℝ (chartInv z) w a, fderiv ℝ (chartInv z) w b⟫_ℝ = c * ⟪a, b⟫_ℝ := by
  have e : chartInv z = stereoInvFunAux ((-z : S2) : E3) ∘ chartV z := funext (chartInv_eq z)
  have hd : fderiv ℝ (chartInv z) w =
      (fderiv ℝ (stereoInvFunAux ((-z : S2) : E3)) (chartV z w)).comp (chartV z) := by
    rw [e, fderiv_comp _ ((contDiff_stereoInvFunAux (m := 1)).differentiable one_ne_zero _)
      (chartV z).differentiableAt, (chartV z).fderiv]
  refine ⟨16 / (‖chartV z w‖ ^ 2 + 4) ^ 2, by positivity, fun a b => ?_⟩
  rw [hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    stereoAux_conformal _ _ _ _ (norm_eq_of_mem_sphere _) (chartV_perp z w) (chartV_perp z a)
      (chartV_perp z b), inner_chartV]

lemma incD_tcc (z : sphere3.S) (w : E2) (a : E2) :
    incD ((extChartAt 𝓘(ℝ, E2) z).symm w) (tangentCoordChange 𝓘(ℝ, E2) z
      ((extChartAt 𝓘(ℝ, E2) z).symm w) ((extChartAt 𝓘(ℝ, E2) z).symm w) a) =
        fderiv ℝ (chartInv z) w a := by
  have hT : ChartsOnto sphere3 := sphere3_chartsOnto
  have hsymm : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm w :=
    ((contMDiff_extChartAt_symm (X := sphere3) hT z) w).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) (Subtype.val : S2 → E3)
      ((extChartAt 𝓘(ℝ, E2) z).symm w) :=
    (contMDiff_coe_sphere (m := ∞) (n := 2) _).mdifferentiableAt (by simp)
  have h := mfderiv_comp w hval hsymm
  have h3 : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm w =
      tangentCoordChange 𝓘(ℝ, E2) z ((extChartAt 𝓘(ℝ, E2) z).symm w)
        ((extChartAt 𝓘(ℝ, E2) z).symm w) := mfderiv_extChartAt_symm_eq (X := sphere3) hT z w
  have h2 : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (Subtype.val ∘ (extChartAt 𝓘(ℝ, E2) z).symm) w =
      fderiv ℝ (chartInv z) w := mfderiv_eq_fderiv
  rw [← h2, h]
  exact (congrArg (incD _) (congrArg (fun L => L a) h3)).symm

lemma crossL_skew (y a b : E3) : ⟪crossL y a, b⟫_ℝ = -⟪a, crossL y b⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    crossL_apply, crossL_apply]
  simp only [star_trivial]
  rw [dotProduct_comm (crossProduct (WithLp.ofLp y) (WithLp.ofLp b)), triple_product_permutation,
    triple_product_permutation (WithLp.ofLp a), ← cross_anticomm (WithLp.ofLp a), dotProduct_neg,
    neg_neg]

/-- **`j` read in a chart of `S²` is skew**: the charts are conformal. -/
lemma jMat_skew (z : sphere3.S) (w : E2) (a b : E2) :
    ⟪jMat (X := sphere3) z ((extChartAt 𝓘(ℝ, E2) z).symm w) a, b⟫_ℝ =
      -⟪a, jMat (X := sphere3) z ((extChartAt 𝓘(ℝ, E2) z).symm w) b⟫_ℝ := by
  set y : sphere3.S := (extChartAt 𝓘(ℝ, E2) z).symm w
  have hy : y ∈ (extChartAt 𝓘(ℝ, E2) z).source :=
    (extChartAt 𝓘(ℝ, E2) z).map_target (mem_target (X := sphere3) sphere3_chartsOnto z w)
  have key : ∀ a, fderiv ℝ (chartInv z) w (jMat (X := sphere3) z y a) =
      crossL (Subtype.val (y : S2)) (fderiv ℝ (chartInv z) w a) := by
    intro a
    rw [← incD_tcc, ← incD_tcc, tcc_jMat hy a]
    change incD y (jStdMap y _) = _
    simp only [jStdMap, ContinuousLinearMap.comp_apply]
    exact incD_retrD_of_perp y (inner_crossL_self _ _)
  obtain ⟨c, hc, hconf⟩ := chartInv_conformal z w
  have h1 := hconf (jMat (X := sphere3) z y a) b
  have h2 := hconf a (jMat (X := sphere3) z y b)
  rw [key] at h1
  rw [key] at h2
  have cs := crossL_skew (Subtype.val (y : S2)) (fderiv ℝ (chartInv z) w a)
    (fderiv ℝ (chartInv z) w b)
  have : c * ⟪jMat (X := sphere3) z y a, b⟫_ℝ = c * -⟪a, jMat (X := sphere3) z y b⟫_ℝ := by
    rw [mul_neg]; linarith
  exact mul_left_cancel₀ hc.ne' this

lemma jMat_sq {z y : sphere3.S} (hy : y ∈ (extChartAt 𝓘(ℝ, E2) z).source) (a : E2) :
    jMat (X := sphere3) z y (jMat (X := sphere3) z y a) = -a := by
  have hinv : ∀ u, tangentCoordChange 𝓘(ℝ, E2) y z y (tangentCoordChange 𝓘(ℝ, E2) z y y u) = u :=
    fun u => by
      rw [tangentCoordChange_comp ⟨⟨hy, mem_extChartAt_source _⟩, hy⟩, tangentCoordChange_self hy]
  have h1 : tangentCoordChange 𝓘(ℝ, E2) z y y (jMat (X := sphere3) z y (jMat (X := sphere3) z y a))
      = tangentCoordChange 𝓘(ℝ, E2) z y y (-a) := by
    rw [tcc_jMat hy, tcc_jMat hy, map_neg]
    have := congrArg (fun L => L (tangentCoordChange 𝓘(ℝ, E2) z y y a)) (sphere3.j.sq y)
    simpa using this
  rw [← hinv (jMat (X := sphere3) z y _), h1, hinv]

lemma jMat_e0 (z : sphere3.S) (w : E2) : ∃ b : ℝ, b ^ 2 = 1 ∧
    jMat (X := sphere3) z ((extChartAt 𝓘(ℝ, E2) z).symm w) (EuclideanSpace.single 0 1) =
      b • EuclideanSpace.single 1 1 := by
  set M := jMat (X := sphere3) z ((extChartAt 𝓘(ℝ, E2) z).symm w)
  have hy : (extChartAt 𝓘(ℝ, E2) z).symm w ∈ (extChartAt 𝓘(ℝ, E2) z).source :=
    (extChartAt 𝓘(ℝ, E2) z).map_target (mem_target (X := sphere3) sphere3_chartsOnto z w)
  have crd : ∀ (i : Fin 2) (u : E2), u i = ⟪EuclideanSpace.single i 1, u⟫_ℝ := fun i u => by
    rw [EuclideanSpace.inner_single_left]; simp
  have h00 : M (EuclideanSpace.single 0 1) 0 = 0 := by
    have := jMat_skew z w (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
    rw [real_inner_comm] at this
    rw [crd]; linarith
  set b := M (EuclideanSpace.single 0 1) 1
  have hMe0 : M (EuclideanSpace.single 0 1) = b • EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp [b, h00]
  have h10 : M (EuclideanSpace.single 1 1) 0 = -b := by
    have := jMat_skew z w (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1)
    rw [real_inner_comm, ← crd, ← crd] at this
    rw [this]
  have hsq := jMat_sq hy (EuclideanSpace.single 0 1)
  rw [hMe0, map_smul] at hsq
  have := congrArg (fun u : E2 => u 0) hsq
  change b * (M (EuclideanSpace.single 1 1)) 0 = -(EuclideanSpace.single 0 1 : E2) 0 at this
  rw [h10] at this
  refine ⟨b, ?_, hMe0⟩
  simp at this
  nlinarith

/-- **In each disc chart of `S²`, `j ∂_s = b ∂_t`, `b = ±1` constant.** -/
theorem jMat_disc_const (z : sphere3.S) (ε : ℝ) : ∃ b : ℝ, b ^ 2 = 1 ∧ ∀ p : ℝ × ℝ,
    jMat (X := sphere3) z (sphere3.discPt z ε p) (EuclideanSpace.single 0 1) =
      b • EuclideanSpace.single 1 1 := by
  set f : ℝ × ℝ → ℝ := fun p =>
    jMat (X := sphere3) z (sphere3.discPt z ε p) (EuclideanSpace.single 0 1) 1
  have hf : Continuous f :=
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).continuous.comp
      (((contDiff_jMat (X := sphere3) sphere3_chartsOnto z ε).continuous).clm_apply
        continuous_const)
  have hpt : ∀ p, jMat (X := sphere3) z (sphere3.discPt z ε p) (EuclideanSpace.single 0 1) =
      f p • EuclideanSpace.single 1 1 ∧ f p ^ 2 = 1 := by
    intro p
    obtain ⟨b, hb, he⟩ := jMat_e0 z (sphere3.place z ε p)
    have e : sphere3.discPt z ε p = (extChartAt 𝓘(ℝ, E2) z).symm (sphere3.place z ε p) := rfl
    have hfp : f p = b := by simp only [f, e, he]; simp
    rw [e, he, hfp]; exact ⟨rfl, hb⟩
  rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hf.continuousOn
    (fun p _ => by simpa using (hpt p).2) with h | h
  · exact ⟨1, one_pow 2, fun p => by rw [(hpt p).1, h (mem_univ p)]; rfl⟩
  · exact ⟨-1, by norm_num, fun p => by rw [(hpt p).1, h (mem_univ p)]; rfl⟩

end GWMemoir
