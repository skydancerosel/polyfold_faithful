import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_8

/-! Round trip for V6_8 (Definition 6.7: the determinant `det(T)`).

The listed declarations are the definitions `Polyfold.linDet`, `Polyfold.fredholmDet`,
`Polyfold.linDetEquivOfEq` and the theorem `Polyfold.finrank_fredholmDet`, so `A` is
`finrank_fredholmDet` (universes at `0`): for a Fredholm operator in Mathlib's sense
(`ContinuousLinearMap.IsFredholm`: strict, closed range, finite-dimensional kernel, finite
codimension, complemented kernel) between real *normed* spaces, `det(T)` is a line.  B, for Banach
spaces and the textbook notion `IsFredholmB` (finite-dimensional kernel, closed range,
finite-dimensional cokernel): (1) `fredholmDet T = λ(ker T) ⊗ λ*(coker T)` (a type equality),
(2) `finrank (fredholmDet T) = 1`, (3) `1 ⊗ ι : λ(ker T) ⊗ λ(coker(T)*) → λ(ker T) ⊗ λ*(coker T)`
is bijective.

* `A ⇒ B`: (1) is `rfl` (`fredholmDet`, `linDet` are abbreviations of exactly this type); (2) is A,
  since between Banach spaces `IsFredholmB` gives Mathlib's `IsFredholm` (the project's
  `isFredholm_of_banach`: open mapping theorem for the strictness, Hahn–Banach for the complement
  of the kernel); (3), independent of A: `ι` is a nonzero map of lines (`iotaDual_ne_zero`), hence
  bijective, and so is `1 ⊗ ι`.
* `B ⇒ A`: A covers normed spaces that need not be complete, B only Banach spaces.  Since `det(T)`
  depends, up to isomorphism, only on `dim ker T` and `dim coker T`, A is reduced to B for the zero
  operator `T' = 0 : ℝⁿ → ℝᵏ`, `n = dim ker T`, `k = dim coker T` (Banach, textbook-Fredholm):
  `det(T) ≅ det(T')` by `λ(ker T ≅ ker T') ⊗ λ*(coker T' ≅ coker T)`, and B gives
  `finrank det(T') = 1`.
-/

namespace RoundTrip.V6_8
open Polyfold Module
open scoped TensorProduct

/-- The project's statement (`det(T)` is a line for Fredholm `T`), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.finrank_fredholmDet.{0, 0}

theorem A_holds : A := @Polyfold.finrank_fredholmDet.{0, 0}

/-- `1 ⊗ ι` is bijective. -/
theorem bijective_one_tensor_iotaDual {K Q : Type} [AddCommGroup K] [Module ℝ K]
    [AddCommGroup Q] [Module ℝ Q] [FiniteDimensional ℝ Q] :
    Function.Bijective (TensorProduct.map (LinearMap.id : maxPow K →ₗ[ℝ] maxPow K)
      (iotaDual Q)) := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 (iotaDual_ne_zero (E := Q))
  rw [LinearMap.zero_apply] at hv
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hι : Function.Bijective (iotaDual Q) :=
    bijective_of_finrank_eq_one (L := maxPow (Module.Dual ℝ Q)) (M := maxPowDual Q)
      finrank_maxPow finrank_maxPowDual (iotaDual Q) hv0 hv
  exact (TensorProduct.congr (LinearEquiv.refl ℝ (maxPow K)) (LinearEquiv.ofBijective _ hι)).bijective

/-- `A ⇒ B`. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T hT
  obtain ⟨hker, hcl, hcoker⟩ := hT
  refine ⟨rfl, ?_, ?_⟩
  · refine hA (isFredholm_of_banach T hker ?_ hcoker)
    rw [LinearMap.coe_range]
    exact hcl
  · exact bijective_one_tensor_iotaDual

/-- `B ⇒ A`, through the zero operator `ℝⁿ → ℝᵏ` with `n = dim ker T`, `k = dim coker T`. -/
theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ T hT
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  set n := finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))
  set k := finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))
  let T' : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) := 0
  have hker' : LinearMap.ker (T' : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) = ⊤ := by
    simp [T']
  have hrange' : LinearMap.range (T' : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) = ⊥ := by
    simp [T']
  have hT' : IsFredholmB T' := by
    refine ⟨inferInstance, ?_, inferInstance⟩
    have := (LinearMap.range (T' : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))).closed_of_finiteDimensional
    rwa [LinearMap.coe_range, ContinuousLinearMap.coe_coe] at this
  have h1 := (hB _ _ T' hT').2.1
  have eK : LinearMap.ker (T : E →ₗ[ℝ] F) ≃ₗ[ℝ]
      LinearMap.ker (T' : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ)) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hker', finrank_top, Module.finrank_fin_fun])
  have eQ : ((Fin k → ℝ) ⧸ LinearMap.range (T' : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))) ≃ₗ[ℝ]
      (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [(Submodule.quotEquivOfEqBot _ hrange').finrank_eq, Module.finrank_fin_fun])
  have e : fredholmDet T ≃ₗ[ℝ] fredholmDet T' :=
    TensorProduct.congr (maxPowEquiv eK) (maxPowDualEquiv eQ)
  rw [e.finrank_eq]
  exact h1

#rt_check RoundTrip.V6_8.A_to_B [Polyfold.finrank_fredholmDet]
#rt_check RoundTrip.V6_8.B_to_A [Polyfold.finrank_fredholmDet]
#rt_overlap RoundTrip.V6_8.B_to_A [Polyfold.finrank_fredholmDet]

end RoundTrip.V6_8
