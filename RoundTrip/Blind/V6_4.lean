import Polyfold
/-! Blind formalization of V6_4 (the text's §6.2, Proposition 6.4, p. 205: naturality of `ι`).
Choices:
- Setting: finite-dimensional real vector spaces `E F : Type` (universe 0) and a linear
  isomorphism `Φ : E ≃ F` (the text's "isomorphism `Φ : E → F`").
- `Φ* : F* → E*` is the transpose `φ ↦ φ ∘ Φ` (Mathlib's `LinearMap.dualMap`).
- `λ(Φ*) : λ(F*) → λ(E*)` is the project's `maxPowMap` of `Φ*` (dimension proof from
  `Subspace.dual_finrank_eq` and `dim E = dim F`); `λ*(Φ) : λ*(F) → λ*(E)` is the project's
  `maxPowDualMap Φ` (the dual of `λ(Φ)`); `ι` is the project's `iotaDual` (Definition 6.3).
  These are characterized in my V6_2 and V6_3.
- The commutativity of the square is the equality of linear maps
  `λ*(Φ) ∘ ι_F = ι_E ∘ λ(Φ*) : λ(F*) → λ*(E)`.
- Nothing here looks false to me.
-/
namespace RoundTrip.V6_4
open Polyfold

/-- Proposition 6.4: for an isomorphism `Φ : E → F`, `λ*(Φ) ∘ ι = ι ∘ λ(Φ*)`. -/
def B : Prop :=
  ∀ (E F : Type) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (Φ : E ≃ₗ[ℝ] F),
    (maxPowDualMap (Φ : E →ₗ[ℝ] F) Φ.finrank_eq) ∘ₗ iotaDual F =
      iotaDual E ∘ₗ
        maxPowMap (Φ : E →ₗ[ℝ] F).dualMap
          (Subspace.dual_finrank_eq.trans (Φ.finrank_eq.symm.trans Subspace.dual_finrank_eq.symm))

end RoundTrip.V6_4
