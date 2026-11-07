import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_3

/-! Round trip for V6_3 (Definition 6.3, `ι : λ(E*) → λ*(E)`).  A is the conjunction of
`iotaDual_wedge_wedge`, `iotaDual_wedge_dualBasis` and `iotaDual_ne_zero`, universes at `0`. -/

namespace RoundTrip.V6_3
open Polyfold Module

/-- The project's statement (Definition 6.3 and its two facts), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.iotaDual_wedge_wedge.{0} ∧ type_of% @Polyfold.iotaDual_wedge_dualBasis.{0} ∧
    type_of% @Polyfold.iotaDual_ne_zero.{0}

theorem A_holds : A :=
  ⟨@Polyfold.iotaDual_wedge_wedge.{0}, @Polyfold.iotaDual_wedge_dualBasis.{0},
    @Polyfold.iotaDual_ne_zero.{0}⟩

/-- A nonzero linear map between lines is bijective. -/
theorem bijective_of_ne_zero {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (hM : finrank ℝ M = 1) (hN : finrank ℝ N = 1) {L : M →ₗ[ℝ] N} (hL : L ≠ 0) :
    Function.Bijective L := by
  obtain ⟨x, hx⟩ : ∃ x, L x ≠ 0 := by
    by_contra h
    exact hL (LinearMap.ext fun y => not_not.1 fun hy => h ⟨y, hy⟩)
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨c, rfl⟩ := _root_.exists_smul_eq_of_finrank_eq_one hM hx0 y
    rw [map_smul] at hy
    rw [(smul_eq_zero.1 hy).resolve_right hx, zero_smul]
  · intro w
    obtain ⟨c, rfl⟩ := _root_.exists_smul_eq_of_finrank_eq_one hN hx w
    exact ⟨c • x, map_smul L c x⟩

/-- A linear map out of a line which is injective is not zero. -/
theorem ne_zero_of_injective {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (hM : finrank ℝ M = 1) {L : M →ₗ[ℝ] N} (hL : Function.Injective L) : L ≠ 0 := by
  have := Module.finite_of_finrank_eq_succ hM
  obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := M)).1 (by omega)
  intro h
  apply hw
  apply hL
  rw [h, LinearMap.zero_apply, map_zero]

theorem A_to_B : A → B := by
  intro hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the defining formula: `iotaDual_wedge_wedge` at `k = dim E`
    intro E _ _ _ e a
    exact hA.1 e Subspace.dual_finrank_eq.symm a rfl
  · -- (2) `λ({0}*) = ℝ`: `⋀⁰ = 1 = range (algebraMap)` (not in A; proved outright)
    intro E _ _ _ h0
    have h : finrank ℝ (Module.Dual ℝ E) = 0 := by rw [Subspace.dual_finrank_eq, h0]
    change ((⋀[ℝ]^(finrank ℝ (Module.Dual ℝ E)) (Module.Dual ℝ E) :
      Submodule ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ E))) :
        Set (ExteriorAlgebra ℝ (Module.Dual ℝ E))) = _
    rw [h, ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_range, LinearMap.coe_range]
    rfl
  · -- (3) `ι` is bijective: a nonzero map of lines (`iotaDual_ne_zero`)
    intro E _ _ _
    exact bijective_of_ne_zero finrank_maxPow finrank_maxPowDual (hA.2.2 (E := E))
  · -- (4) `iotaDual_wedge_dualBasis` at `k = dim E`
    intro E _ _ _ e
    exact hA.2.1 e rfl

/-- The defining formula for an arbitrary (possibly infinite-dimensional) `E`, outright; used in
`B_to_A` only when `E` is not finite-dimensional, where B says nothing. -/
theorem iotaDual_wedge_wedge' {E : Type} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (e : Fin k → Module.Dual ℝ E) (he : k = finrank ℝ (Module.Dual ℝ E)) (a : Fin k → E)
    (ha : k = finrank ℝ E) :
    iotaDual E (wedge e he) (wedge a ha) = (Matrix.of fun i j => e i (a j)).det := by
  subst ha
  have : LinearEquiv.ofEq _ _ (by simp only [maxPow, Subspace.dual_finrank_eq]) (wedge e he) =
      exteriorPower.ιMulti ℝ (finrank ℝ E) e := Subtype.ext rfl
  rw [iotaDual, LinearMap.comp_apply, LinearEquiv.coe_coe, this, wedge_eq_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  rfl

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro E _ _ k e he a ha
    by_cases hE : FiniteDimensional ℝ E
    · subst ha
      exact hB.1 E e a
    · exact iotaDual_wedge_wedge' e he a ha
  · intro E _ _ _ k b hk
    subst hk
    exact hB.2.2.2 E b
  · intro E _ _ _
    exact ne_zero_of_injective finrank_maxPow (hB.2.2.1 E).1

#rt_check RoundTrip.V6_3.A_to_B [Polyfold.iotaDual_wedge_wedge, Polyfold.iotaDual_wedge_dualBasis,
  Polyfold.iotaDual_ne_zero]
#rt_check RoundTrip.V6_3.B_to_A [Polyfold.iotaDual_wedge_wedge, Polyfold.iotaDual_wedge_dualBasis,
  Polyfold.iotaDual_ne_zero]
#rt_overlap RoundTrip.V6_3.B_to_A [Polyfold.iotaDual_wedge_wedge, Polyfold.iotaDual_wedge_dualBasis,
  Polyfold.iotaDual_ne_zero]

end RoundTrip.V6_3
