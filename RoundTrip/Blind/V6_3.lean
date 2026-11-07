import Polyfold
/-! Blind formalization of V6_3 (the text's §6.2, Definition 6.3, p. 204: the isomorphism
`ι : λ(E*) → λ*(E)`).  Choices:
- Setting: a finite-dimensional real vector space `E : Type` (universe 0), `n = dim E`,
  `E* = Module.Dual ℝ E` (so `dim E* = n`, `Subspace.dual_finrank_eq`).  `λ`, `λ*`, the wedge
  `e₁* ∧ … ∧ eₙ*` and the dual vector `v*` are the project's `maxPow`, `maxPowDual`, `wedge`,
  `dualVec` (characterized in my V6_2); `ι` is the project's `iotaDual E`.
- `B` is the conjunction of
  (1) the defining formula `ι(e₁* ∧ … ∧ eₙ*)(a₁ ∧ … ∧ aₙ) = det(eᵢ*(aⱼ))` for all families
      `e* : Fin n → E*`, `a : Fin n → E` (Mathlib's `Matrix.det` of the `n × n` matrix
      `(i, j) ↦ eᵢ*(aⱼ)`; for `n = 0` it reads `ι(1)(1) = det() = 1`);
  (2) the convention `λ({0}*) = ℝ` for `n = 0`: then `λ(E*)` is the line of scalars
      `ℝ · 1 ⊆ Λ E*` (the range of `algebraMap`);
  (3) `ι` is an isomorphism (the md's title calls it "the isomorphism `ι`"): bijective;
  (4) for a basis `e` of `E` with dual basis `e*` (Mathlib's `Basis.dualBasis`,
      `eᵢ*(eⱼ) = δᵢⱼ`), `ι(e₁* ∧ … ∧ eₙ*) = (e₁ ∧ … ∧ eₙ)*`.
- Nothing here looks false to me.
-/
namespace RoundTrip.V6_3
open Polyfold

/-- Definition 6.3: `ι(e₁* ∧ … ∧ eₙ*)(a₁ ∧ … ∧ aₙ) = det(eᵢ*(aⱼ))`, `λ({0}*) = ℝ`, `ι` is an
isomorphism, and `ι(e₁* ∧ … ∧ eₙ*) = (e₁ ∧ … ∧ eₙ)*` for a basis and its dual basis. -/
def B : Prop :=
  -- (1) the defining formula
  (∀ (E : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (e : Fin (Module.finrank ℝ E) → Module.Dual ℝ E) (a : Fin (Module.finrank ℝ E) → E),
      iotaDual E (wedge e Subspace.dual_finrank_eq.symm) (wedge a rfl) =
        Matrix.det (Matrix.of fun i j => e i (a j))) ∧
  -- (2) `λ({0}*) = ℝ` for `n = 0`
  (∀ (E : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E],
    Module.finrank ℝ E = 0 →
      (maxPow (Module.Dual ℝ E) : Set (ExteriorAlgebra ℝ (Module.Dual ℝ E))) =
        Set.range (algebraMap ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ E)))) ∧
  -- (3) `ι` is an isomorphism
  (∀ (E : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E],
    Function.Bijective (iotaDual E)) ∧
  -- (4) `ι(e₁* ∧ … ∧ eₙ*) = (e₁ ∧ … ∧ eₙ)*` for a basis and its dual basis
  (∀ (E : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (e : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E),
      iotaDual E (wedge (⇑e.dualBasis) Subspace.dual_finrank_eq.symm) = dualVec (wedge (⇑e) rfl))

end RoundTrip.V6_3
