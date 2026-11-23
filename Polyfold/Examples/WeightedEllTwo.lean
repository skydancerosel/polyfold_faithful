import Polyfold.Chapter1.ScOneNotNormContinuous
import Polyfold.Chapter1.FredholmPerturbation
import Polyfold.Chapter6.DetNonOrientableTransport
import Polyfold.Chapter5.PartitionsOfUnity

/-!
# A weighted `ℓ²` sc-Hilbert space with strictly nested levels

An sc-Hilbert space for the worked example of Hofer–Wysocki–Zehnder, *Polyfold and Fredholm
Theory* (Springer 2021), Definition 1.1.1, p. 4.

## What is formalized (namespace `Polyfold.Examples.WeightedEllTwo`)

* `incl`: the diagonal operator `x ↦ (x_k / (k+1))_k` of `ℓ² = ℓ²(ℕ, ℝ)`; `incl_injective`,
  `isCompactOperator_incl` (a norm limit of finite-rank operators), `not_surjective_incl`.
* `scale`, **`H`**: the sc-Banach space with levels
  `H_m = {x | ∑ (k+1)^{2m} x_k² < ∞}`, each represented by the coordinates
  `y_k = (k+1)^m x_k ∈ ℓ²`, so that every level is the Hilbert space `ℓ²` and the inclusion
  `H_{m+1} → H_m` is `incl`.  `toBase_apply`: `H_m → H_0` is `y ↦ (y_k / (k+1)^m)_k`.
* `not_surjective_inclLevel`: the levels are strictly nested; `harmH_not_mem_smooth`: the point
  `(1/(k+1))_k` of `H_0` is not smooth.
* `mem_smoothLvl_of_finSupp`: finitely supported sequences are smooth points.
* `hasContDiffBump_level_zero`, `secondCountableTopology_level_zero`: `H_0 = ℓ²` has a
  `C^∞` bump function and is second countable.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped ENNReal

noncomputable section

namespace Polyfold.Examples.WeightedEllTwo

open ScOneExample

/-- `ℓ² = ℓ²(ℕ, ℝ)`. -/
abbrev L2 : Type := LTwo ℕ

/-- The diagonal operator with weights `c`, `|c| ≤ 1`. -/
def dg (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) : L2 →L[ℝ] L2 := wcomp injective_id hc

theorem dg_apply (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) (x : L2) (k : ℕ) :
    dg c hc x k = c k * x k := rfl

theorem norm_dg_le (c : ℕ → ℝ) (hc : ∀ k, |c k| ≤ 1) : ‖dg c hc‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one (norm_wcompₗ_le injective_id hc)

/-- **The inclusion `H_{m+1} → H_m`**: `y ↦ (y_k / (k+1))_k`. -/
def incl : L2 →L[ℝ] L2 := dg w abs_w_le

theorem incl_apply (x : L2) (k : ℕ) : incl x k = w k * x k := rfl

theorem incl_injective : Injective incl := by
  intro y z h
  refine lp.ext (funext fun k => ?_)
  have := congrArg (fun u : L2 => u k) h
  simp only [incl_apply] at this
  exact mul_left_cancel₀ (w_pos k).ne' this

/-- The sequences vanishing from `n` on. -/
def finSub (n : ℕ) : Submodule ℝ L2 where
  carrier := {y | ∀ k, n ≤ k → y k = 0}
  add_mem' := fun {a b} ha hb k hk => by
    rw [lp.coeFn_add, Pi.add_apply, ha k hk, hb k hk, add_zero]
  zero_mem' := fun k _ => rfl
  smul_mem' := fun c a ha k hk => by
    rw [lp.coeFn_smul, Pi.smul_apply, ha k hk, smul_zero]

instance finiteDimensional_finSub (n : ℕ) : FiniteDimensional ℝ (finSub n) := by
  let T : finSub n →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun y i => (y : L2) i
      map_add' := fun a b => funext fun i => by
        change ((a : L2) + (b : L2)) i = _
        rw [lp.coeFn_add]; rfl
      map_smul' := fun c a => funext fun i => by
        change (c • (a : L2)) i = _
        rw [lp.coeFn_smul]; rfl }
  refine FiniteDimensional.of_injective T fun a b h => ?_
  refine Subtype.ext (lp.ext (funext fun k => ?_))
  by_cases hk : k < n
  · exact congrFun h ⟨k, hk⟩
  · rw [a.2 k (not_lt.1 hk), b.2 k (not_lt.1 hk)]

/-- The truncated inclusion has finite rank. -/
theorem isCompactOperator_dg_wTrunc (n : ℕ) :
    IsCompactOperator (dg (wTrunc n) (abs_wTrunc_le n)) := by
  have hle : LinearMap.range (dg (wTrunc n) (abs_wTrunc_le n) : L2 →ₗ[ℝ] L2) ≤ finSub n := by
    rintro _ ⟨x, rfl⟩ k hk
    change wTrunc n k * x k = 0
    unfold wTrunc
    rw [if_neg (by omega), zero_mul]
  have : FiniteDimensional ℝ (LinearMap.range (dg (wTrunc n) (abs_wTrunc_le n) : L2 →ₗ[ℝ] L2)) :=
    Submodule.finiteDimensional_of_le hle
  exact isCompactOperator_of_finiteDimensional_range _

/-- The rescaled tail weights `(n+1)(w_k 1_{k<n} − w_k)`. -/
def tail (n k : ℕ) : ℝ := ((n : ℝ) + 1) * (wTrunc n k - w k)

theorem abs_tail_le (n k : ℕ) : |tail n k| ≤ 1 := by
  unfold tail wTrunc
  split_ifs with hk
  · rw [sub_self, mul_zero, abs_zero]; exact zero_le_one
  · rw [zero_sub, abs_mul, abs_neg, abs_of_pos (w_pos k), abs_of_pos (by positivity)]
    unfold w
    rw [mul_one_div, div_le_one (by positivity)]
    have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.1 hk
    linarith

theorem tendsto_dg_wTrunc :
    Tendsto (fun n => dg (wTrunc n) (abs_wTrunc_le n)) atTop (𝓝 incl) := by
  refine (tendsto_iff_norm_sub_tendsto_zero (f := fun n => dg (wTrunc n) (abs_wTrunc_le n))
    (b := incl)).2 ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have e : dg (wTrunc n) (abs_wTrunc_le n) - incl =
      (1 / ((n : ℝ) + 1)) • dg (tail n) (abs_tail_le n) := by
    ext x : 1
    refine lp.ext (funext fun k => ?_)
    change wTrunc n k * x k - w k * x k = (1 / ((n : ℝ) + 1)) * (tail n k * x k)
    unfold tail
    field_simp
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (norm_dg_le _ _)

/-- **The inclusion `H_{m+1} → H_m` is compact.** -/
theorem isCompactOperator_incl : IsCompactOperator incl :=
  isCompactOperator_of_tendsto tendsto_dg_wTrunc
    (Eventually.of_forall isCompactOperator_dg_wTrunc)

/-- The scale `H_m = ℓ²` (coordinates `y_k = (k+1)^m x_k`) with the inclusions `incl`. -/
abbrev scale : ScScale where
  lvl _ := L2
  incl _ := incl
  incl_injective _ := incl_injective
  incl_isCompactOperator _ := isCompactOperator_incl

theorem toBase_apply : ∀ (m : ℕ) (y : scale m) (k : ℕ),
    scale.toBase m y k = w k ^ m * (y : L2) k
  | 0, y, k => by rw [pow_zero, one_mul]; rfl
  | m + 1, y, k => by
    rw [ScScale.toBase_succ, toBase_apply m]
    change w k ^ m * (w k * (y : L2) k) = _
    ring

/-- A finitely supported sequence of `ℓ²`. -/
def finSeq (n : ℕ) (a : ℕ → ℝ) : L2 :=
  ∑ k ∈ Finset.range n, lp.single 2 k (a k)

theorem finSeq_apply (n : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    finSeq n a k = if k < n then a k else 0 := by
  unfold finSeq
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  split_ifs with hk
  · rw [Finset.sum_eq_single k]
    · exact Pi.single_eq_same _ _
    · intro b _ hb
      exact Pi.single_eq_of_ne (Ne.symm hb) _
    · intro h
      exact absurd (Finset.mem_range.2 hk) h
  · refine Finset.sum_eq_zero fun b hb => ?_
    refine Pi.single_eq_of_ne ?_ _
    have := Finset.mem_range.1 hb
    omega

/-- Finitely supported sequences are smooth points of every level. -/
theorem mem_smoothLvl_of_finSupp {m : ℕ} (y : scale m) {n : ℕ}
    (hy : ∀ k, n ≤ k → (y : L2) k = 0) : y ∈ scale.smoothLvl m := by
  refine (scale.mem_smoothLvl_iff).2 fun j => ?_
  refine ⟨finSeq n fun k => ((k : ℝ) + 1) ^ j * (w k ^ m * (y : L2) k), ?_⟩
  refine lp.ext (funext fun k => ?_)
  rw [toBase_apply, toBase_apply, finSeq_apply]
  split_ifs with hk
  · rw [← mul_assoc, ← mul_pow]
    have : w k * ((k : ℝ) + 1) = 1 := by unfold w; field_simp
    rw [this, one_pow, one_mul]
  · rw [hy k (not_lt.1 hk)]; simp

/-- **The weighted `ℓ²` sc-Hilbert space `H`**: `|x|_m² = ∑ (k+1)^{2m} x_k²`. -/
def H : ScBanach where
  toScScale := scale
  dense_smooth m := by
    intro y
    have hs : HasSum (fun k => lp.single 2 k ((y : L2) k)) (y : L2) :=
      lp.hasSum_single (by norm_num) y
    refine mem_closure_of_tendsto hs.tendsto_sum_nat (Eventually.of_forall fun n => ?_)
    refine mem_smoothLvl_of_finSupp (m := m) _ (n := n) fun k hk => ?_
    have h := finSeq_apply n (fun k => (y : L2) k) k
    rw [if_neg (by omega)] at h
    exact h

theorem H_lvl (m : ℕ) : H m = L2 := rfl

/-- The sequence `(1/(k+1))_k` of `ℓ²`. -/
def harm : L2 :=
  ⟨fun k => w k, memℓp_gen (by
    have h := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (one_lt_two))
    refine h.congr fun k => ?_
    rw [Real.norm_eq_abs, abs_of_pos (w_pos k)]
    unfold w
    have e : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [e, Real.rpow_two, div_pow, one_pow]
    push_cast
    rfl)⟩

/-- `(1/(k+1))_k` is not in the image of the inclusion. -/
theorem incl_ne_harm (x : L2) : incl x ≠ harm := by
  intro hx
  have h1 : ∀ k, (x : L2) k = 1 := fun k => by
    have := congrArg (fun u : L2 => u k) hx
    change w k * x k = w k at this
    exact mul_left_cancel₀ (w_pos k).ne' (this.trans (mul_one _).symm)
  have hsum := (lp.memℓp x).summable ellTwo_toReal_pos
  have h0 := hsum.tendsto_atTop_zero
  have h2 : (fun k => ‖(x : L2) k‖ ^ (2 : ℝ≥0∞).toReal) = fun _ => (1 : ℝ) := by
    funext k
    rw [h1 k, norm_one, Real.one_rpow]
  rw [h2] at h0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)

/-- **The levels are strictly nested**: the inclusion is not onto. -/
theorem not_surjective_incl : ¬ Surjective incl := fun h =>
  let ⟨x, hx⟩ := h harm
  incl_ne_harm x hx

/-- **`H_{m+1} → H_m` is not onto.** -/
theorem not_surjective_inclLevel (m : ℕ) : ¬ Surjective (H.incl m) := not_surjective_incl

/-- `H_0 = ℓ²` has a `C^∞` bump function (Proposition 5.5.8). -/
theorem hasContDiffBump_level_zero : HasContDiffBump (H 0) ⊤ :=
  hasContDiffBump_of_hilbert (V := L2) (innerSL ℝ) fun v => (real_inner_self_eq_norm_sq v).symm

/-- `ℓ²` is separable: the finitely supported sequences with one non-zero entry span a dense
subspace. -/
instance separableSpace_L2 : TopologicalSpace.SeparableSpace L2 := by
  have hc : (range fun p : ℕ × ℚ => (lp.single 2 p.1 ((p.2 : ℝ)) : L2)).Countable :=
    countable_range _
  have hsep : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℝ (range fun p : ℕ × ℚ => (lp.single 2 p.1 ((p.2 : ℝ)) : L2)) :
        Set L2)) := (hc.isSeparable.span (R := ℝ)).closure
  have huniv : closure (Submodule.span ℝ
      (range fun p : ℕ × ℚ => (lp.single 2 p.1 ((p.2 : ℝ)) : L2)) : Set L2) = univ := by
    refine eq_univ_of_forall fun y => ?_
    have hs : HasSum (fun k => lp.single 2 k ((y : L2) k)) (y : L2) :=
      lp.hasSum_single (by norm_num) y
    refine mem_closure_of_tendsto hs.tendsto_sum_nat (Eventually.of_forall fun n => ?_)
    refine Submodule.sum_mem _ fun k _ => ?_
    have e : (lp.single 2 k ((y : L2) k) : L2) = ((y : L2) k) • lp.single 2 k ((1 : ℚ) : ℝ) := by
      rw [← lp.single_smul]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, 1), rfl⟩)
  rw [huniv] at hsep
  exact TopologicalSpace.isSeparable_univ_iff.1 hsep

instance secondCountableTopology_L2 : SecondCountableTopology L2 :=
  UniformSpace.secondCountable_of_separable L2

theorem secondCountableTopology_level_zero : SecondCountableTopology (H 0) :=
  secondCountableTopology_L2

/-- The point `(1/(k+1))_k` of `H_0`. -/
def harmH : H 0 := harm

/-- **`(1/(k+1))_k ∈ H_0` is not in `H_1`**, hence not a smooth point. -/
theorem harmH_not_mem_smooth : harmH ∉ H.smooth := fun h =>
  let ⟨y, hy⟩ := H.mem_smooth_iff.1 h 1
  incl_ne_harm y hy

end Polyfold.Examples.WeightedEllTwo
