import Polyfold.Chapter1.FredholmIndex
import Polyfold.Chapter1.FredholmPerturbation
import Polyfold.Chapter6.DetNonOrientableTransport
import Polyfold.Examples.WeightedEllTwo

/-!
# The Fredholm index: examples (row V1.28)

Examples for the index `ind u = dim ker u − dim (F / range u)` (`Polyfold.linIndex`,
`Polyfold.fredholmIndex`) and its invariance under compact perturbations.

* `linIndex_eq_finrank_sub`: between finite-dimensional spaces the index is `dim E − dim F`.
* `linIndex_fst`, `linIndex_inl`, `linIndex_fst_comp_inl`: the projection `ℝ² → ℝ` has index
  `1`, the inclusion `ℝ → ℝ²` index `−1`, and their composite, the identity, `0 = −1 + 1`.
* `not_hasFiniteIndex_zero`: the zero map of the infinite-dimensional `ℕ →₀ ℝ` has no finite
  index.
* `linIndex_shift_ltwo`: a shift of `ℓ²(ℕ)` has index `1`.
* `fredholmIndex_one_add_incl`: on `ℓ²(ℕ)`, `1 + K` with `K x = (x_k/(k+1))_k` compact has
  index `0`.
-/

open Module ContinuousLinearMap

noncomputable section

namespace Polyfold.Examples.Path

/-- Row V1.28, the index of a linear map: between finite-dimensional spaces it is
`dim E − dim F`, whatever the map. -/
theorem linIndex_eq_finrank_sub {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (u : E →ₗ[ℝ] F) : linIndex u = (finrank ℝ E : ℤ) - finrank ℝ F := by
  have h1 := LinearMap.finrank_range_add_finrank_ker u
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range u)
  unfold linIndex
  omega

/-- Row V1.28: a linear map between finite-dimensional spaces has finite index. -/
theorem hasFiniteIndex_of_finiteDimensional {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (u : E →ₗ[ℝ] F) : HasFiniteIndex u :=
  ⟨inferInstance, inferInstance⟩

/-- Row V1.28: the projection `ℝ² → ℝ`, `(x, y) ↦ x`, has index `1`. -/
theorem linIndex_fst : linIndex (LinearMap.fst ℝ ℝ ℝ) = 1 := by
  rw [linIndex_eq_finrank_sub, Module.finrank_prod, Module.finrank_self]
  norm_num

/-- Row V1.28: the inclusion `ℝ → ℝ²`, `x ↦ (x, 0)`, has index `−1`. -/
theorem linIndex_inl : linIndex (LinearMap.inl ℝ ℝ ℝ) = -1 := by
  rw [linIndex_eq_finrank_sub, Module.finrank_prod, Module.finrank_self]
  norm_num

/-- Row V1.28, additivity under composition: the identity `ℝ → ℝ² → ℝ` has index
`0 = ind(inl) + ind(fst) = −1 + 1`. -/
theorem linIndex_fst_comp_inl :
    linIndex (LinearMap.fst ℝ ℝ ℝ ∘ₗ LinearMap.inl ℝ ℝ ℝ) =
      linIndex (LinearMap.inl ℝ ℝ ℝ) + linIndex (LinearMap.fst ℝ ℝ ℝ) ∧
    linIndex (LinearMap.fst ℝ ℝ ℝ ∘ₗ LinearMap.inl ℝ ℝ ℝ) = 0 := by
  refine ⟨linIndex_comp (hasFiniteIndex_of_finiteDimensional _)
    (hasFiniteIndex_of_finiteDimensional _), ?_⟩
  rw [linIndex_eq_finrank_sub]
  simp

/-- Row V1.28, a non-example: the zero map of the infinite-dimensional space `ℕ →₀ ℝ` has an
infinite-dimensional kernel, so it has no finite index. -/
theorem not_hasFiniteIndex_zero : ¬ HasFiniteIndex (0 : (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ)) := by
  rintro ⟨hk, -⟩
  have hfin : FiniteDimensional ℝ (ℕ →₀ ℝ) := by
    rw [LinearMap.ker_zero] at hk
    exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl)
  have h := Module.rank_lt_aleph0 ℝ (ℕ →₀ ℝ)
  rw [rank_finsupp_self', Cardinal.mk_nat] at h
  exact lt_irrefl _ h

/-- Row V1.28, an example in infinite dimensions: a shift of `ℓ²(ℕ)`, onto with a
one-dimensional kernel, has index `1`. -/
theorem linIndex_shift_ltwo :
    ∃ T : LTwo ℕ →L[ℝ] LTwo ℕ, fredholmIndex T = 1 := by
  obtain ⟨T, hs, ⟨φ⟩⟩ := exists_shift_ltwo (ι := ℕ)
  refine ⟨T, ?_⟩
  have hr : LinearMap.range (T : LTwo ℕ →ₗ[ℝ] LTwo ℕ) = ⊤ := LinearMap.range_eq_top.2 hs
  have hk : finrank ℝ (LinearMap.ker (T : LTwo ℕ →ₗ[ℝ] LTwo ℕ)) = 1 := by
    rw [φ.finrank_eq, Module.finrank_self]
  have hq : finrank ℝ (LTwo ℕ ⧸ LinearMap.range (T : LTwo ℕ →ₗ[ℝ] LTwo ℕ)) = 0 := by
    rw [hr]
    exact Module.finrank_zero_of_subsingleton
  unfold fredholmIndex linIndex
  rw [hk, hq]
  norm_num

/-- Row V1.28: the identity of a Banach space has index `0`. -/
theorem fredholmIndex_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : fredholmIndex (1 : E →L[ℝ] E) = 0 :=
  linIndex_equiv (LinearEquiv.refl ℝ E)

open Polyfold.Examples.WeightedEllTwo in
/-- Row V1.28, invariance under compact perturbations: on `ℓ²(ℕ)`, `1 + K` with the compact
diagonal operator `K x = (x_k/(k+1))_k` is Fredholm of index `0`. -/
theorem fredholmIndex_one_add_incl :
    IsFredholm (1 + incl : L2 →L[ℝ] L2) ∧ fredholmIndex (1 + incl : L2 →L[ℝ] L2) = 0 := by
  have h1 : IsFredholm (1 : L2 →L[ℝ] L2) := by
    simpa using isFredholm_one_add (E := L2) (c := 0) isCompactOperator_zero
  exact ⟨isFredholm_one_add isCompactOperator_incl,
    (fredholmIndex_add_isCompactOperator h1 isCompactOperator_incl).trans fredholmIndex_one⟩

end Polyfold.Examples.Path
