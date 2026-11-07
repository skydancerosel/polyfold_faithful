import Polyfold.Chapter6.ExactSequence
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.LinearAlgebra.Ray

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.3, p. 207:
**Definition 6.7** (the determinant `det(T)` of a Fredholm operator) and **Definition 6.8** (an
orientation of `T`) *(book 2017: Definitions 6.4 and 6.5; see `BookConcordance.md`)*.

# The determinant line of a Fredholm operator

## The text, paraphrased

(Definition 6.7) The determinant of a bounded linear Fredholm operator `T : E → F` between real
Banach spaces is the line `det(T) = λ(ker T) ⊗ λ*(coker T)`.  (Definition 6.8) An orientation of
`T` is an orientation of the line `det(T)`.

## What is formalized

* `Polyfold.linDet T = λ(ker T) ⊗ λ*(F / im T)` for a linear map `T`, and
  `Polyfold.fredholmDet T`, the same for a bounded operator (**Definition 6.7**);
  `Polyfold.finrank_fredholmDet`: for `T` Fredholm it is a line.
* `Polyfold.linDetEquivOfEq`: the identification `det(T) ≅ det(T')` for `T = T'` (the types
  `ker T` and `ker T'` are different), computed on wedges by `linDetEquivOfEq_tmul`; it is the
  identity for `T = T` (`linDetEquivOfEq_self`) and the identifications compose
  (`linDetEquivOfEq_trans`).
* `Polyfold.FredholmOrientation T`: the rays of `det(T)` (**Definition 6.8**);
  `nonempty_fredholmOrientation`, `exists_two_fredholmOrientation`: for `T` Fredholm there are
  exactly two.

## Reading

An orientation of a line `L` is a ray of `L` (`Module.Ray ℝ L`: a nonzero vector up to positive
multiples), Mathlib's notion; for a line it is the same as a component of `L ∖ {0}`.  The
definitions make sense for every bounded operator; for `T` Fredholm the two spaces are
finite-dimensional, which is what makes `det(T)` a line.
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

section Linear

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **`det(T) = λ(ker T) ⊗ λ*(coker T)`** for a linear map `T` (Definition 6.7). -/
abbrev linDet (T : E →ₗ[ℝ] F) : Type _ :=
  maxPow (LinearMap.ker T) ⊗[ℝ] maxPowDual (F ⧸ LinearMap.range T)

/-- `det(T)` is a line when `ker T` and `coker T` are finite-dimensional. -/
theorem finrank_linDet (T : E →ₗ[ℝ] F) [FiniteDimensional ℝ (LinearMap.ker T)]
    [FiniteDimensional ℝ (F ⧸ LinearMap.range T)] : finrank ℝ (linDet T) = 1 := by
  rw [Module.finrank_tensorProduct, finrank_maxPow, finrank_maxPowDual]

/-- The identification `det(T) ≅ det(T')` for `T = T'`: `λ` of `ker T = ker T'` tensored with
`λ*` of `F / im T' ≅ F / im T`. -/
def linDetEquivOfEq {T T' : E →ₗ[ℝ] F} (h : T = T') : linDet T ≃ₗ[ℝ] linDet T' :=
  TensorProduct.congr (maxPowEquiv (LinearEquiv.ofEq _ _ (by rw [h])))
    (maxPowDualEquiv (Submodule.quotEquivOfEq _ _ (by rw [h])))

/-- `linDetEquivOfEq` on wedges: the same vectors, read in `ker T'` and `F / im T'`. -/
theorem linDetEquivOfEq_tmul {T T' : E →ₗ[ℝ] F} (h : T = T')
    [FiniteDimensional ℝ (F ⧸ LinearMap.range T')] {k l : ℕ} (a : Fin k → LinearMap.ker T)
    (hk : k = finrank ℝ (LinearMap.ker T)) (d : Fin l → F ⧸ LinearMap.range T)
    (hd : LinearIndependent ℝ d) (hl : l = finrank ℝ (F ⧸ LinearMap.range T)) :
    linDetEquivOfEq h (wedge a hk ⊗ₜ dualVec (wedge d hl)) =
      wedge (LinearEquiv.ofEq (LinearMap.ker T) (LinearMap.ker T') (by rw [h]) ∘ a)
          (hk.trans
            (LinearEquiv.ofEq (LinearMap.ker T) (LinearMap.ker T') (by rw [h])).finrank_eq) ⊗ₜ
        dualVec (wedge
          (Submodule.quotEquivOfEq (LinearMap.range T) (LinearMap.range T') (by rw [h]) ∘ d)
          (hl.trans (Submodule.quotEquivOfEq (LinearMap.range T) (LinearMap.range T')
            (by rw [h])).finrank_eq)) := by
  rw [linDetEquivOfEq, TensorProduct.congr_tmul, maxPowEquiv_wedge]
  congr 1
  set Φ := Submodule.quotEquivOfEq (LinearMap.range T') (LinearMap.range T) (by rw [h])
  set v := Submodule.quotEquivOfEq (LinearMap.range T) (LinearMap.range T') (by rw [h]) ∘ d
    with hv_def
  have hv : LinearIndependent ℝ v := hd.map' _ (LinearEquiv.ker _)
  have hΦv : ⇑Φ ∘ v = d := by
    funext i
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (d i)
    simp [Φ, hv_def, ← hx]
  rw [← maxPowDualEquiv_dualVec Φ hv, hΦv]

omit [Module ℝ F] [AddCommGroup F] in
/-- `λ(id) = id`. -/
theorem maxPowEquiv_refl : maxPowEquiv (LinearEquiv.refl ℝ E) = LinearEquiv.refl ℝ (maxPow E) := by
  apply LinearEquiv.toLinearMap_injective
  rw [coe_maxPowEquiv, LinearEquiv.refl_toLinearMap]
  exact maxPowMap_eq_id LinearEquiv.refl_toLinearMap _

omit [Module ℝ F] [AddCommGroup F] in
/-- `λ*(id) = id`. -/
theorem maxPowDualEquiv_refl :
    maxPowDualEquiv (LinearEquiv.refl ℝ E) = LinearEquiv.refl ℝ (maxPowDual E) := by
  rw [maxPowDualEquiv, maxPowEquiv_refl, LinearEquiv.dualMap_refl]

omit [Module ℝ E] [AddCommGroup E] in
/-- `F / p ≅ F / p` (for `p = p`) is the identity. -/
theorem quotEquivOfEq_self (p : Submodule ℝ F) (h : p = p) :
    Submodule.quotEquivOfEq p p h = LinearEquiv.refl ℝ (F ⧸ p) := by
  ext x
  induction x using Submodule.Quotient.induction_on
  rfl

/-- `linDetEquivOfEq` of `T = T` is the identity. -/
theorem linDetEquivOfEq_self (T : E →ₗ[ℝ] F) (h : T = T) :
    linDetEquivOfEq h = LinearEquiv.refl ℝ (linDet T) := by
  rw [linDetEquivOfEq, LinearEquiv.ofEq_rfl, maxPowEquiv_refl, quotEquivOfEq_self,
    maxPowDualEquiv_refl, TensorProduct.congr_refl_refl]

/-- The identifications `linDetEquivOfEq` compose: `det(T) ≅ det(T') ≅ det(T'')` is
`det(T) ≅ det(T'')`. -/
theorem linDetEquivOfEq_trans {T T' T'' : E →ₗ[ℝ] F} (h : T = T') (h' : T' = T'')
    (x : linDet T) :
    linDetEquivOfEq h' (linDetEquivOfEq h x) = linDetEquivOfEq (h.trans h') x := by
  subst h h'
  rw [linDetEquivOfEq_self, LinearEquiv.refl_apply]

end Linear

section Banach

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Definition 6.7**: the determinant `det(T) = λ(ker T) ⊗ λ*(coker T)` of a bounded operator
`T : E → F`. -/
abbrev fredholmDet (T : E →L[ℝ] F) : Type _ := linDet (T : E →ₗ[ℝ] F)

/-- For `T` Fredholm, `det(T)` is a line. -/
theorem finrank_fredholmDet {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    finrank ℝ (fredholmDet T) = 1 := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  exact finrank_linDet _

/-- **Definition 6.8**: an orientation of `T` is an orientation of the line `det(T)`, that is, a
ray of `det(T)`. -/
abbrev FredholmOrientation (T : E →L[ℝ] F) : Type _ := Module.Ray ℝ (fredholmDet T)

/-- A Fredholm operator has an orientation. -/
theorem nonempty_fredholmOrientation {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    Nonempty (FredholmOrientation T) := by
  obtain ⟨v, hv, -⟩ := finrank_eq_one_iff'.1 (finrank_fredholmDet hT)
  exact ⟨rayOfNeZero ℝ v hv⟩

/-- **A Fredholm operator has exactly two orientations**: there are two different ones, and
every orientation is one of them. -/
theorem exists_two_fredholmOrientation {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    ∃ o₁ o₂ : FredholmOrientation T, o₁ ≠ o₂ ∧ ∀ o : FredholmOrientation T, o = o₁ ∨ o = o₂ := by
  have h1 := finrank_fredholmDet hT
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 h1
  have hv' : ((-1 : ℝ) • v) ≠ 0 := smul_ne_zero (by norm_num) hv
  refine ⟨rayOfNeZero ℝ v hv, rayOfNeZero ℝ ((-1 : ℝ) • v) hv', ?_, ?_⟩
  · rw [Ne, ray_eq_iff]
    rintro (h | h | ⟨r₁, r₂, h₁, h₂, h⟩)
    · exact hv h
    · exact hv' h
    · have := congrArg (dualVec v) h
      simp only [map_smul, dualVec_self h1 hv, smul_eq_mul] at this
      linarith
  · intro o
    induction o using Module.Ray.ind with
    | h w hw =>
      obtain ⟨c, rfl⟩ := hall w
      rcases lt_or_gt_of_ne (left_ne_zero_of_smul hw) with hc | hc
      · right
        rw [ray_eq_iff]
        have : c • v = (-c) • ((-1 : ℝ) • v) := by rw [smul_smul]; norm_num
        rw [this]
        exact SameRay.sameRay_pos_smul_left _ (neg_pos.2 hc)
      · left
        rw [ray_eq_iff]
        exact SameRay.sameRay_pos_smul_left _ hc

end Banach

end Polyfold
