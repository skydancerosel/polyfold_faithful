import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_17

namespace RoundTrip.V6_17
open Polyfold Module

/-- The project's statement (formula (94)), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.stabPsi_dualVec.{0, 0}

theorem A_holds : A := @Polyfold.stabPsi_dualVec.{0, 0}

/-- `det_{std}(c)` is the determinant of the matrix with columns `c_j`. -/
theorem basisFun_det_eq {n : ℕ} (c : Fin n → Fin n → ℝ) :
    (Pi.basisFun ℝ (Fin n)).det c = Matrix.det (Matrix.of fun i j => c j i) := by
  rw [Basis.det_apply]
  congr 1

section Psi
variable {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℝ Z] [Subsingleton Z]

theorem h0Z : 0 = finrank ℝ Z := (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Z)).symm

/-- `(e₁ ∧ … ∧ eₙ)* ≠ 0`. -/
theorem dualStd_ne_zero : dualVec (stdW n) ≠ 0 :=
  dualVec_ne_zero finrank_maxPow (stdWedge_ne_zero n)

/-- `1* ≠ 0` in `λ*({0})`. -/
theorem oneStar_ne_zero (h0 : 0 = finrank ℝ Z) : oneStar Z h0 ≠ 0 :=
  dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff _).2 linearIndependent_empty_type)

/-- The map `x ↦ (e₁ ∧ … ∧ eₙ)**(x) · 1*`. -/
noncomputable def psi0 (n : ℕ) (Z : Type) [AddCommGroup Z] [Module ℝ Z] (h0 : 0 = finrank ℝ Z) :
    maxPowDual (Fin n → ℝ) →ₗ[ℝ] maxPowDual Z :=
  LinearMap.smulRight (dualVec (dualVec (stdW n))) (oneStar Z h0)

omit [Subsingleton Z] in
/-- `psi0((e₁ ∧ … ∧ eₙ)*) = 1*`. -/
theorem psi0_isPsi (h0 : 0 = finrank ℝ Z) : IsPsi h0 (psi0 n Z h0) := by
  rw [IsPsi, psi0, LinearMap.smulRight_apply, dualVec_self finrank_maxPowDual dualStd_ne_zero,
    one_smul]

theorem psi0_bijective (h0 : 0 = finrank ℝ Z) : Function.Bijective (psi0 n Z h0) := by
  have hinj : Function.Injective (psi0 n Z h0) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨t, rfl⟩ := Polyfold.exists_smul_eq_of_finrank_eq_one finrank_maxPowDual
      (dualStd_ne_zero (n := n)) x
    rw [map_smul, psi0_isPsi h0, smul_eq_zero] at hx
    rcases hx with rfl | h
    · exact zero_smul _ _
    · exact absurd h (oneStar_ne_zero h0)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_maxPowDual, finrank_maxPowDual])).1 hinj⟩

omit [Subsingleton Z] in
/-- Every `ψ` with `ψ((e₁ ∧ … ∧ eₙ)*) = 1*` is `psi0`. -/
theorem eq_psi0 (h0 : 0 = finrank ℝ Z) {ψ : maxPowDual (Fin n → ℝ) →ₗ[ℝ] maxPowDual Z}
    (hψ : IsPsi h0 ψ) : ψ = psi0 n Z h0 :=
  linearMap_ext_of_ne_zero finrank_maxPowDual dualStd_ne_zero (hψ.trans (psi0_isPsi h0).symm)

end Psi

/-- `ℝ → ℝ`, the identity, stabilized by `0 : ℝⁿ → ℝ`, is onto. -/
theorem surj_id_coprod_zero (n : ℕ) :
    Function.Surjective ((ContinuousLinearMap.id ℝ ℝ).coprod (0 : (Fin n → ℝ) →L[ℝ] ℝ)) :=
  fun y => ⟨(y, 0), by simp⟩

/-- `A ⇒ B`.  The existence of the isomorphism `ψ` (B's first conjunct, not part of A) is the
elementary `psi0`; the scalar `(e₁ ∧ … ∧ eₙ)**((c₁ ∧ … ∧ cₙ)*) = det[c]⁻¹` is read off A applied to
`T = id_ℝ`, `φ = 0` (where the project's `stabPsi` is `psi0` with `1* ≠ 0`). -/
theorem A_to_B : A → B := by
  intro hA n Z _ _ _
  set h0 := (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Z)).symm
  refine ⟨⟨LinearEquiv.ofBijective _ (psi0_bijective (n := n) h0), psi0_isPsi h0⟩, ?_⟩
  intro ψ hψ c hc
  rw [eq_psi0 h0 hψ, psi0, LinearMap.smulRight_apply, ← basisFun_det_eq]
  congr 1
  -- the scalar, from A
  have hφ := surj_id_coprod_zero n
  have key := hA (T := ContinuousLinearMap.id ℝ ℝ) (φ := 0) hφ hc
  rw [stabPsi, LinearMap.smulRight_apply] at key
  exact smul_left_injective ℝ (stabOne_ne_zero hφ) key

/-- `B ⇒ A`: B for `Z = F / R(T_φ)` (a subsingleton) and `ψ = stabPsi`, which satisfies
`ψ((e₁ ∧ … ∧ eₙ)*) = 1*`. -/
theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ T n φ hφ c hc
  have := subsingleton_coker_coprod hφ
  have := (hB n (F ⧸ LinearMap.range ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
    E × (Fin n → ℝ) →ₗ[ℝ] F))).2 (stabPsi hφ) (stabPsi_dualVec_stdWedge hφ) c hc
  rw [basisFun_det_eq]
  exact this

#rt_check RoundTrip.V6_17.A_to_B [Polyfold.stabPsi_dualVec]
#rt_check RoundTrip.V6_17.B_to_A [Polyfold.stabPsi_dualVec]
#rt_overlap RoundTrip.V6_17.B_to_A [Polyfold.stabPsi_dualVec]

end RoundTrip.V6_17
