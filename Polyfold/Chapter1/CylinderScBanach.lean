import Polyfold.Chapter1.CylinderTestDensity
import Polyfold.Chapter1.ScBanach

/-!
# Example 1.1.3 (2021, p. 6; preprint Example 1.2): the sc-Banach space `L²(ℝ × S¹)`

For a strictly increasing sequence `δ₀ = 0 < δ₁ < ⋯`, the spaces
`E_m = H^{m,δ_m}(ℝ × S¹)` form an sc-structure on `E = L²(ℝ × S¹)` (`example_1_1_3`):
each level is a Banach space (`completeSpace_H`), the inclusions `E_{m+1} → E_m` are compact
(`isCompactOperator_inclH`, from Rellich on bounded cylinders and the decay of the weights),
and `E_∞` is dense in every level, since it contains the test functions (`IsTest.mem_Hsub`),
which are dense (`dense_test`). Level `0` is `L²(ℝ × S¹)` itself (`level0_isometry`,
`level0_surjective`).

Modelling: `S¹ = ℝ/ℤ` is realised by functions on `ℝ × (0,1]`, with test functions
`1`-periodic in `t`; weak derivatives are taken against these test functions.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold.GapP1Sobolev

lemma nonneg_of_strictMono {δ : ℕ → ℝ} (h0 : δ 0 = 0) (hmono : StrictMono δ) (m : ℕ) :
    0 ≤ δ m := h0 ▸ hmono.monotone (Nat.zero_le m)

/-- The sc-scale `E_m = H^{m,δ_m}(ℝ × S¹)`. -/
def scaleH (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) : ScScale where
  lvl m := H m (nonneg_of_strictMono h0 hmono m)
  incl m := inclH (nonneg_of_strictMono h0 hmono m) (nonneg_of_strictMono h0 hmono (m + 1))
    (Nat.le_succ m) (hmono (Nat.lt_succ_self m)).le
  incl_injective _ := inclH_injective _ _ _ _
  incl_isCompactOperator m := isCompactOperator_inclH _ _ (hmono (Nat.lt_succ_self m))

lemma toBase_toH (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) {φ : ℝ × ℝ → ℝ}
    (hφ : IsTest φ) : ∀ m, (scaleH δ h0 hmono).toBase m
      (toH m (nonneg_of_strictMono h0 hmono m) hφ) = toH 0 (nonneg_of_strictMono h0 hmono 0) hφ
  | 0 => rfl
  | m + 1 => by
    change (scaleH δ h0 hmono).toBase m ((scaleH δ h0 hmono).incl m _) = _
    have : (scaleH δ h0 hmono).incl m (toH (m + 1) (nonneg_of_strictMono h0 hmono (m + 1)) hφ) =
        toH m (nonneg_of_strictMono h0 hmono m) hφ := valCLM_injective rfl
    rw [this, toBase_toH δ h0 hmono hφ m]

/-- **Example 1.1.3** (2021, p. 6; preprint Example 1.2): for `δ₀ = 0 < δ₁ < δ₂ < ⋯`, the
filtration `E_m = H^{m,δ_m}(ℝ × S¹)` is an sc-structure on `L²(ℝ × S¹)`. -/
def example_1_1_3 (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) : ScBanach where
  toScScale := scaleH δ h0 hmono
  dense_smooth m := by
    refine (dense_test m (nonneg_of_strictMono h0 hmono m)).mono ?_
    rintro _ ⟨φ, hφ, rfl⟩
    refine (scaleH δ h0 hmono).mem_smoothLvl_iff.2 fun j =>
      ⟨toH j (nonneg_of_strictMono h0 hmono j) hφ, ?_⟩
    rw [toBase_toH, toBase_toH]

lemma example_1_1_3_lvl (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) (m : ℕ) :
    (example_1_1_3 δ h0 hmono).lvl m = H m (nonneg_of_strictMono h0 hmono m) := rfl

/-! ### Level `0` is `L²(ℝ × S¹)` -/

/-- For `δ = 0`, the norm of `H^{0,0}` is the `L²` norm. -/
theorem level0_isometry {δ : ℝ} (hδ : 0 ≤ δ) (h : δ = 0) : Isometry (valCLM 0 hδ) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun u => ?_
  have hw : wdv (H.toSub u) (idx0 0) = (H.toSub u : Lp ℝ 2 cyl) := by
    refine Lp.ext ?_
    filter_upwards [coeFn_wdv (H.toSub u) (idx0 0), dv_idx0 (H.toSub u)] with x e1 e2
    rw [e1, e2]; simp [wt, h]
  have hsq : ‖u‖ ^ 2 = ‖valCLM 0 hδ u‖ ^ 2 := by
    rw [norm_sq_H]
    have huniv : (Finset.univ : Finset (idx 0)) = {idx0 0} := by
      ext p
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      obtain ⟨⟨a, b⟩, hp⟩ := p
      have := mem_idx.1 hp
      exact Subtype.ext (Prod.ext (by simp [idx0]; omega) (by simp [idx0]; omega))
    rw [huniv, Finset.sum_singleton, hw, valCLM_apply]
  exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq).symm

/-- Every `f ∈ L²(ℝ × S¹)` lies in `H^{0,δ}` when `δ = 0`. -/
theorem level0_surjective {δ : ℝ} (hδ : 0 ≤ δ) (h : δ = 0) :
    Function.Surjective (valCLM 0 hδ) := fun f =>
  ⟨(⟨f, fun a b hab => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      exact ⟨f, hasWeakDeriv_zero _, by simpa [wt, h] using Lp.memLp f⟩⟩ : Hsub 0 hδ), rfl⟩

end Polyfold.GapP1Sobolev
