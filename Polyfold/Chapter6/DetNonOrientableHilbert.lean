import Polyfold.Chapter6.DetNonOrientable
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), the end of §6.5 (p. 262;
preprint p. 219): the remark that **the line bundle `DET(E, F)` is non-orientable**.  Gap G.60,
the instance `E = F = ℓ² × ℓ²`.

# `DET(ℓ² × ℓ², ℓ² × ℓ²)` is not orientable

## What is formalized

* `ellTwoShift`: the left shift `(x₀, x₁, …) ↦ (x₁, x₂, …)` of `ℓ² = ℓ²(ℕ, ℝ)`, a bounded
  operator; `ellTwoShift_surjective`; `kerEllTwoShiftEquiv`: its kernel is the line `ℝ e₀`.
* `isEmpty_lineOrientation_det_ellTwo`: `DET(ℓ² × ℓ², ℓ² × ℓ²)` has no orientation
  (`isEmpty_lineOrientation_det_prod` for the shift).  `ℓ² × ℓ²` is a separable
  infinite-dimensional Hilbert space up to isomorphism; the loop is the conjugation of
  `shift × 1` by the rotations of `ℓ² × ℓ²`.
-/

open Module Bundle Topology Set
open scoped ENNReal

noncomputable section

namespace Polyfold

/-- `ℓ² = ℓ²(ℕ, ℝ)`. -/
abbrev EllTwo : Type := lp (fun _ : ℕ => ℝ) 2

theorem ellTwo_toReal_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

/-- The shifted sequence `(x₁, x₂, …)` is in `ℓ²`. -/
theorem memℓp_shift (x : EllTwo) : Memℓp (fun n : ℕ => (x (n + 1) : ℝ)) 2 :=
  memℓp_gen ((summable_nat_add_iff 1).2 ((lp.memℓp x).summable ellTwo_toReal_pos))

/-- The sequence `(0, y₀, y₁, …)` is in `ℓ²`. -/
theorem memℓp_unshift (y : EllTwo) :
    Memℓp (fun n : ℕ => (Nat.casesOn n 0 (fun m => y m) : ℝ)) 2 :=
  memℓp_gen ((summable_nat_add_iff 1).1 ((lp.memℓp y).summable ellTwo_toReal_pos))

/-- The left shift of `ℓ²` as a linear map. -/
def ellTwoShiftₗ : EllTwo →ₗ[ℝ] EllTwo where
  toFun x := ⟨fun n => x (n + 1), memℓp_shift x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ellTwoShiftₗ_apply (x : EllTwo) (n : ℕ) : ellTwoShiftₗ x n = x (n + 1) := rfl

/-- The left shift does not increase the norm. -/
theorem norm_ellTwoShiftₗ_le (x : EllTwo) : ‖ellTwoShiftₗ x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  refine lp.norm_le_of_forall_sum_le ellTwo_toReal_pos (norm_nonneg x) fun s => ?_
  have h := lp.sum_rpow_le_norm_rpow ellTwo_toReal_pos x
    (s.map ⟨fun n => n + 1, add_left_injective 1⟩)
  rw [Finset.sum_map] at h
  exact h

/-- **The left shift** `(x₀, x₁, …) ↦ (x₁, x₂, …)` of `ℓ²`. -/
def ellTwoShift : EllTwo →L[ℝ] EllTwo := ellTwoShiftₗ.mkContinuous 1 norm_ellTwoShiftₗ_le

theorem ellTwoShift_apply (x : EllTwo) (n : ℕ) : ellTwoShift x n = x (n + 1) := rfl

/-- The left shift is onto: `(0, y₀, y₁, …) ↦ y`. -/
theorem ellTwoShift_surjective : Function.Surjective ellTwoShift := fun y =>
  ⟨⟨_, memℓp_unshift y⟩, lp.ext (funext fun _ => rfl)⟩

/-- **The kernel of the left shift is the line `ℝ e₀`.** -/
def kerEllTwoShiftEquiv : LinearMap.ker (ellTwoShift : EllTwo →ₗ[ℝ] EllTwo) ≃ₗ[ℝ] ℝ where
  toFun x := (x : EllTwo) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun t := ⟨lp.single 2 0 t, lp.ext (funext fun n => by
    change (lp.single 2 0 t : EllTwo) (n + 1) = 0
    exact lp.single_apply_ne 2 0 t (Nat.succ_ne_zero n))⟩
  left_inv x := Subtype.ext (lp.ext (funext fun n => by
    cases n with
    | zero => exact lp.single_apply_self 2 0 _
    | succ m =>
      have hx : ellTwoShift (x : EllTwo) = 0 := x.2
      have hm : (x : EllTwo) (m + 1) = 0 := by
        have := congrArg (fun z : EllTwo => z m) hx
        exact this
      change (lp.single 2 0 ((x : EllTwo) 0) : EllTwo) (m + 1) = (x : EllTwo) (m + 1)
      rw [hm]
      exact lp.single_apply_ne 2 0 _ (Nat.succ_ne_zero m)))
  right_inv t := by
    change (lp.single 2 0 t : EllTwo) 0 = t
    exact lp.single_apply_self (E := fun _ : ℕ => ℝ) 2 0 t

/-- **(2021, p. 262) `DET(ℓ² × ℓ², ℓ² × ℓ²)` is not orientable.** -/
theorem isEmpty_lineOrientation_det_ellTwo :
    IsEmpty (LineOrientation (DetFiber (E := EllTwo × EllTwo) (F := EllTwo × EllTwo))) := by
  have : FiniteDimensional ℝ (LinearMap.ker (ellTwoShift : EllTwo →ₗ[ℝ] EllTwo)) :=
    kerEllTwoShiftEquiv.symm.finiteDimensional
  refine isEmpty_lineOrientation_det_prod ellTwoShift_surjective ?_
  rw [kerEllTwoShiftEquiv.finrank_eq, Module.finrank_self]
  exact odd_one

end Polyfold
