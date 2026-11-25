import Polyfold.Chapter1.ExpositionLemmas
import Polyfold.Chapter1.ScOneNotNormContinuous

/-!
# Sc¹ maps and the tangent map: examples (row V1.13)

* `isSc1_const_iff`: on `ℝ` with the constant sc-structure, sc¹ is `C¹`.
* `scDeriv_const_eq_fderiv`, `tangentMap_const`: there the chosen derivative family is the usual
  derivative, and `Tf(x, h) = (f(x), f'(x) h)`.
* `tangentMap_sq`: for `f(x) = x²`, `Tf(x, h) = (x², 2 x h)`.
* `not_isSc1_abs`: `x ↦ |x|` is sc⁰ but not sc¹.

The infinite-dimensional example `f(t, x)_k = cos(k t) x_k` on `ℝ ⊕ X`, `X` the weighted `c₀`
scale, is `Polyfold.ScOneExample.isSc1With`; that its derivative is not norm continuous is
`Polyfold.ScOneExample.not_continuousOn_of_isSc1With`.
-/

open Set Function

noncomputable section

namespace Polyfold.Examples.Path

/-- `ℝ` with the constant sc-structure. -/
abbrev Rc : ScBanach := ScBanach.const ℝ

theorem relOpen_univ_Rc : IsRelOpenInQuadrant Rc univ univ :=
  ⟨isPartialQuadrant_univ Rc, univ, isOpen_univ, (univ_inter _).symm⟩

/-- Row V1.13, Definition 1.1.15 (p. 10): on `ℝ` with the constant sc-structure a map is sc¹ iff
it is `C¹`. -/
theorem isSc1_const_iff (f : ℝ → ℝ) : IsSc1 (E := Rc) (F := Rc) univ f ↔ ContDiff ℝ 1 f := by
  rw [isSc1_iff_contDiffOn_const relOpen_univ_Rc.isScDomain f, contDiffOn_univ]

/-- Row V1.13, Definition 1.1.15 (p. 10): for a `C¹` map of `ℝ` with the constant sc-structure,
the chosen derivative family `Df` is the derivative. -/
theorem scDeriv_const_eq_fderiv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ) :
    scDeriv (E := Rc) (F := Rc) univ f x = fderiv ℝ f x := by
  have h : IsSc1 (E := Rc) (F := Rc) univ f := (isSc1_const_iff f).2 hf
  have hD := (h.isSc1With_scDeriv.hasFDerivWithinAt x (by simp [ScBanach.lvlSet_const]))
  rw [ScBanach.lvlSet_const] at hD
  have hcomp : (f ∘ Rc.toBase 1) = f := funext fun y => congrArg f (ScBanach.const_toBase ℝ 1 y)
  have hL : ((scDeriv (E := Rc) (F := Rc) univ f x).comp (Rc.toBase 1)) =
      scDeriv (E := Rc) (F := Rc) univ f x :=
    ContinuousLinearMap.ext fun y => congrArg _ (ScBanach.const_toBase ℝ 1 y)
  rw [hcomp, hL, hasFDerivWithinAt_univ] at hD
  exact (hD.fderiv).symm

/-- Row V1.13, Definition 1.1.15 (p. 10): for a `C¹` map of `ℝ` with the constant sc-structure,
the tangent map is `Tf(x, h) = (f(x), f'(x) h)`. -/
theorem tangentMap_const {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (x h : ℝ) :
    tangentMap (E := Rc) (F := Rc) univ f (x, h) = (f x, deriv f x * h) := by
  change (levelMap (E := Rc) (F := Rc) f 1 (show Rc 1 from x),
    scDeriv (E := Rc) (F := Rc) univ f x h) = _
  have hl : levelMap (E := Rc) (F := Rc) f 1 (show Rc 1 from x) = f x :=
    levelMap_eq_of_toBase_eq (by rw [ScBanach.const_toBase, ScBanach.const_toBase])
  rw [hl, scDeriv_const_eq_fderiv hf, ← fderiv_apply_one_eq_deriv, mul_comm]
  simp

/-- Row V1.13: for `f(x) = x²` on `ℝ` with the constant sc-structure,
`Tf(x, h) = (x², 2 x h)`. -/
theorem tangentMap_sq (x h : ℝ) :
    tangentMap (E := Rc) (F := Rc) univ (fun y : ℝ => y ^ 2) (x, h) = (x ^ 2, 2 * x * h) := by
  rw [tangentMap_const (f := fun y : ℝ => y ^ 2) (contDiff_id.pow 2)]
  simp

/-- Row V1.13, a non-example: `x ↦ |x|` on `ℝ` with the constant sc-structure is sc⁰ (it is
continuous) but not sc¹. -/
theorem not_isSc1_abs :
    IsSc0 Rc Rc univ (fun x : ℝ => |x|) ∧ ¬ IsSc1 (E := Rc) (F := Rc) univ (fun x : ℝ => |x|) := by
  refine ⟨?_, fun h => ?_⟩
  · have hl : ∀ m (x : Rc m), levelMap (E := Rc) (F := Rc) (fun x : ℝ => |x|) m x =
        (show Rc m from |(show ℝ from x)|) := fun m x =>
      levelMap_eq_of_toBase_eq (by rw [ScBanach.const_toBase, ScBanach.const_toBase])
    refine ⟨fun m x _ => ⟨show Rc m from |(show ℝ from Rc.toBase m x)|, ?_⟩, fun m => ?_⟩
    · rw [ScBanach.const_toBase]
    · rw [show levelMap (E := Rc) (F := Rc) (fun x : ℝ => |x|) m = fun x => |(show ℝ from x)| from
        funext (hl m)]
      exact continuous_abs.continuousOn
  · rw [isSc1_const_iff] at h
    exact not_differentiableAt_abs_zero (h.differentiable one_ne_zero 0)

end Polyfold.Examples.Path
