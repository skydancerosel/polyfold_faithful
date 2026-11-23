import Polyfold.Chapter3.NonVacuity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.ZMod.Basic

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the algebra

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739.  This file has the finite-dimensional algebra.

`ℂ` is read as `Fin 2 → ℝ` through `cE`; `ζ = exp(2πi/5)`; `χ : ℤ/5 → ℂ`, `χ(g) = ζ^g`;
`rot c` is the multiplication by `c`; `sq` is `z ↦ z²`.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `χ_mul`, `χ_eq_one_iff`, `χ_sq_eq_one_iff`, `norm_χ`.
* `sq_rot`: `(c z)² = c² z²`; `sq_eq_zero_iff`; `contDiff_sq`, `fderiv_sq`.
* **`eq_zero_of_rot_sq_fixed`**: a vector fixed by the multiplication by `ζ²` is zero (weight `2`
  has no invariant vector).
* **`linear_eq_zero_of_equivariant`**: a real-linear `L : ℂ → ℂ` with `L(ζ z) = ζ² L(z)` is zero
  (`L(z) = a z + b z̄` forces `a = b = 0`, since `2 ≢ ±1` mod `5`).
-/

open Complex Function

open scoped ContDiff Real

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

/-- `ℝ² ≅ ℂ`, `(a, b) ↦ a + b i`. -/
def cE : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm

/-- `ζ = exp(2πi/5)`. -/
def ζ : ℂ := Complex.exp (2 * π * I / (5 : ℕ))

theorem isPrimitiveRoot_ζ : IsPrimitiveRoot ζ 5 := Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem ζ_pow_five : ζ ^ 5 = 1 := isPrimitiveRoot_ζ.pow_eq_one

theorem ζ_ne_zero : ζ ≠ 0 := Complex.exp_ne_zero _

theorem ζ_pow_eq_one_iff (k : ℕ) : ζ ^ k = 1 ↔ 5 ∣ k := isPrimitiveRoot_ζ.pow_eq_one_iff_dvd k

theorem norm_ζ : ‖ζ‖ = 1 := isPrimitiveRoot_ζ.norm'_eq_one (by norm_num)

/-- The character `χ(g) = ζ^g` of `ℤ/5`. -/
def χ (g : Multiplicative (ZMod 5)) : ℂ := ζ ^ (Multiplicative.toAdd g).val

theorem χ_one : χ 1 = 1 := by
  change ζ ^ (0 : ZMod 5).val = 1
  rw [ZMod.val_zero, pow_zero]

theorem χ_mul (g h : Multiplicative (ZMod 5)) : χ (g * h) = χ g * χ h := by
  change ζ ^ (Multiplicative.toAdd g + Multiplicative.toAdd h).val = _
  rw [χ, χ, ← pow_add, ZMod.val_add]
  exact (pow_eq_pow_mod _ ζ_pow_five).symm

theorem χ_ne_zero (g : Multiplicative (ZMod 5)) : χ g ≠ 0 := pow_ne_zero _ ζ_ne_zero

theorem norm_χ (g : Multiplicative (ZMod 5)) : ‖χ g‖ = 1 := by
  rw [χ, norm_pow, norm_ζ, one_pow]

theorem χ_ofAdd_one : χ (Multiplicative.ofAdd 1) = ζ := by
  change ζ ^ (1 : ZMod 5).val = ζ
  rw [show (1 : ZMod 5).val = 1 from rfl, pow_one]

theorem χ_pow_five (g : Multiplicative (ZMod 5)) : χ g ^ 5 = 1 := by
  rw [χ, ← pow_mul, mul_comm, pow_mul, ζ_pow_five, one_pow]

theorem χ_eq_one_iff (g : Multiplicative (ZMod 5)) : χ g = 1 ↔ g = 1 := by
  rw [χ, ζ_pow_eq_one_iff]
  constructor
  · intro h
    have h5 : (Multiplicative.toAdd g).val < 5 := ZMod.val_lt _
    have h0 : (Multiplicative.toAdd g).val = 0 := Nat.eq_zero_of_dvd_of_lt h h5
    exact (ZMod.val_eq_zero _).1 h0
  · rintro rfl
    change 5 ∣ (0 : ZMod 5).val
    rw [ZMod.val_zero]
    exact dvd_zero 5

theorem χ_sq_eq_one_iff (g : Multiplicative (ZMod 5)) : χ g ^ 2 = 1 ↔ g = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, χ_one, one_pow]⟩
  have h5 : χ g ^ 5 = 1 := χ_pow_five g
  have h4 : χ g ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
  have h1 : χ g = 1 := by
    rw [pow_succ, h4, one_mul] at h5
    exact h5
  exact (χ_eq_one_iff g).1 h1

/-- The multiplication by `c ∈ ℂ` on `ℝ²`. -/
def rot (c : ℂ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (cE.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp ((ContinuousLinearMap.mul ℝ ℂ c).comp
    (cE : (Fin 2 → ℝ) →L[ℝ] ℂ))

theorem rot_apply (c : ℂ) (x : Fin 2 → ℝ) : rot c x = cE.symm (c * cE x) := rfl

theorem cE_rot (c : ℂ) (x : Fin 2 → ℝ) : cE (rot c x) = c * cE x := by
  rw [rot_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem rot_one (x : Fin 2 → ℝ) : rot 1 x = x := by
  rw [rot_apply, one_mul, ContinuousLinearEquiv.symm_apply_apply]

theorem rot_mul (a b : ℂ) (x : Fin 2 → ℝ) : rot (a * b) x = rot a (rot b x) := by
  rw [rot_apply, rot_apply, cE_rot, mul_assoc]

theorem rot_eq_self_iff {c : ℂ} (hc : c ≠ 1) (x : Fin 2 → ℝ) : rot c x = x ↔ x = 0 := by
  constructor
  · intro h
    have h1 : c * cE x = cE x := by rw [← cE_rot, h]
    have h2 : (c - 1) * cE x = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    have h3 : cE x = 0 := (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc)
    exact cE.map_eq_zero_iff.1 h3
  · rintro rfl
    exact map_zero _

/-- `z ↦ z²` on `ℝ² = ℂ`. -/
def sq (x : Fin 2 → ℝ) : Fin 2 → ℝ := cE.symm (cE x ^ 2)

theorem cE_sq (x : Fin 2 → ℝ) : cE (sq x) = cE x ^ 2 := by
  rw [sq, ContinuousLinearEquiv.apply_symm_apply]

theorem contDiff_sq : ContDiff ℝ ∞ sq :=
  cE.symm.contDiff.comp (cE.contDiff.pow 2)

/-- `(c z)² = c² z²`. -/
theorem sq_rot (c : ℂ) (x : Fin 2 → ℝ) : sq (rot c x) = rot (c ^ 2) (sq x) := by
  rw [sq, cE_rot, rot_apply, cE_sq, mul_pow]

theorem sq_eq_zero_iff (x : Fin 2 → ℝ) : sq x = 0 ↔ x = 0 := by
  rw [sq, cE.symm.map_eq_zero_iff, pow_eq_zero_iff (by norm_num), cE.map_eq_zero_iff]

/-- The derivative of `z ↦ z²` at `x` is `v ↦ 2 x v`. -/
theorem hasFDerivAt_sq (x : Fin 2 → ℝ) : HasFDerivAt sq (rot (2 * cE x)) x := by
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ => cE y) (cE : (Fin 2 → ℝ) →L[ℝ] ℂ) x :=
    cE.hasFDerivAt
  have h2 := h1.pow 2
  have h3 := (cE.symm.hasFDerivAt (x := cE x ^ 2)).comp x h2
  refine h3.congr_fderiv ?_
  ext v : 1
  change cE.symm (((2 : ℕ) • cE x ^ (2 - 1)) • cE v) = cE.symm (2 * cE x * cE v)
  congr 1
  simp [smul_eq_mul]

theorem fderiv_sq (x : Fin 2 → ℝ) : fderiv ℝ sq x = rot (2 * cE x) := (hasFDerivAt_sq x).fderiv

theorem surjective_rot {c : ℂ} (hc : c ≠ 0) : Surjective (rot c) := fun w =>
  ⟨rot c⁻¹ w, by rw [← rot_mul, mul_inv_cancel₀ hc, rot_one]⟩

/-! ### Multisections are needed: the algebra -/

/-- **Weight `2` has no invariant vector**: a vector fixed by `ζ²` is zero. -/
theorem eq_zero_of_rot_sq_fixed {w : Fin 2 → ℝ} (h : rot (ζ ^ 2) w = w) : w = 0 :=
  (rot_eq_self_iff (fun h1 => by
    have := (ζ_pow_eq_one_iff 2).1 h1
    omega) w).1 h

/-- **An equivariant real-linear map of weight `1 → 2` is zero**: if `L(ζ z) = ζ² L(z)` for all
`z`, then `L = 0`. -/
theorem linear_eq_zero_of_equivariant (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (h : ∀ x, L (rot ζ x) = rot (ζ ^ 2) (L x)) : L = 0 := by
  -- transport to `ℂ`
  let M : ℂ →ₗ[ℝ] ℂ :=
    (cE.toLinearEquiv.toLinearMap.comp L).comp cE.symm.toLinearEquiv.toLinearMap
  have hM : ∀ z : ℂ, M (ζ * z) = ζ ^ 2 * M z := by
    intro z
    change cE (L (cE.symm (ζ * z))) = ζ ^ 2 * cE (L (cE.symm z))
    have := h (cE.symm z)
    rw [rot_apply, ContinuousLinearEquiv.apply_symm_apply] at this
    rw [this, cE_rot]
  have hz : ∀ z : ℂ, z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • I := by
    intro z
    apply Complex.ext <;> simp
  set u := M 1 with hu
  set v := M I with hv
  have hMz : ∀ z : ℂ, M z = z.re * u + z.im * v := by
    intro z
    conv_lhs => rw [hz z]
    rw [map_add, map_smul, map_smul, real_smul, real_smul]
  have e1 := hM 1
  have e2 := hM I
  rw [mul_one, hMz ζ] at e1
  rw [hMz (ζ * I)] at e2
  have hre : (ζ * I).re = -ζ.im := by simp
  have him : (ζ * I).im = ζ.re := by simp
  rw [hre, him] at e2
  have hζ : (ζ.re : ℂ) + ζ.im * I = ζ := Complex.re_add_im ζ
  -- `(u - i v)` and `(u + i v)`
  have k1 : ζ * (u - I * v) = ζ ^ 2 * (u - I * v) := by
    have : ζ * (u - I * v) = (ζ.re * u + ζ.im * v) - I * ((-ζ.im : ℝ) * u + ζ.re * v) := by
      conv_lhs => rw [← hζ]
      push_cast
      linear_combination (-(ζ.im : ℂ) * v) * Complex.I_sq
    rw [this, e1, e2]
    ring
  have k2 : (ζ.re - ζ.im * I) * (u + I * v) = ζ ^ 2 * (u + I * v) := by
    have : (ζ.re - ζ.im * I) * (u + I * v) =
        (ζ.re * u + ζ.im * v) + I * ((-ζ.im : ℝ) * u + ζ.re * v) := by
      push_cast
      linear_combination (-(ζ.im : ℂ) * v) * Complex.I_sq
    rw [this, e1, e2]
    ring
  have hconj : (ζ.re - ζ.im * I : ℂ) = ζ ^ 4 := by
    have h1 : (ζ.re - ζ.im * I : ℂ) * ζ = 1 := by
      have hn : (ζ.re : ℂ) ^ 2 + (ζ.im : ℂ) ^ 2 = 1 := by
        have h' : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
          rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, norm_ζ, one_pow]
        have h'' : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by rw [pow_two, pow_two]; exact h'
        exact_mod_cast h''
      have h0 : (ζ.re - ζ.im * I : ℂ) * ζ = (ζ.re - ζ.im * I) * (ζ.re + ζ.im * I) := by rw [hζ]
      rw [h0]
      linear_combination hn - (ζ.im : ℂ) ^ 2 * Complex.I_sq
    have h2 : ζ ^ 4 * ζ = 1 := by rw [← pow_succ]; exact ζ_pow_five
    exact mul_right_cancel₀ ζ_ne_zero (h1.trans h2.symm)
  rw [hconj] at k2
  have n1 : ζ ^ 2 ≠ ζ := fun h1 => by
    have h2 : ζ ^ 1 = 1 := by
      have : ζ * ζ = ζ * 1 := by rw [mul_one, ← pow_two]; exact h1
      rw [pow_one]; exact mul_left_cancel₀ ζ_ne_zero this
    have := (ζ_pow_eq_one_iff 1).1 h2
    omega
  have n2 : ζ ^ 2 ≠ ζ ^ 4 := fun h1 => by
    have h2 : ζ ^ 2 = 1 := by
      have : ζ ^ 2 * 1 = ζ ^ 2 * ζ ^ 2 := by rw [mul_one, ← pow_add]; exact h1
      exact (mul_left_cancel₀ (pow_ne_zero 2 ζ_ne_zero) this).symm
    have := (ζ_pow_eq_one_iff 2).1 h2
    omega
  have a1 : u - I * v = 0 := by
    have : (ζ ^ 2 - ζ) * (u - I * v) = 0 := by rw [sub_mul, ← k1, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 n1)
  have a2 : u + I * v = 0 := by
    have : (ζ ^ 2 - ζ ^ 4) * (u + I * v) = 0 := by rw [sub_mul, ← k2, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 n2)
  have u0 : u = 0 := by linear_combination (1 / 2 : ℂ) * a1 + (1 / 2 : ℂ) * a2
  have v0 : v = 0 := by
    have : I * v = 0 := by linear_combination (1 / 2 : ℂ) * a2 - (1 / 2 : ℂ) * a1
    exact (mul_eq_zero.1 this).resolve_left Complex.I_ne_zero
  refine LinearMap.ext fun x => ?_
  have : M (cE x) = 0 := by rw [hMz, u0, v0, mul_zero, mul_zero, add_zero]
  have h' : cE (L (cE.symm (cE x))) = 0 := this
  rw [ContinuousLinearEquiv.symm_apply_apply] at h'
  exact cE.map_eq_zero_iff.1 h'

end Polyfold.Examples.OrbifoldSquare
