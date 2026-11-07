import Polyfold
/-! Blind formalization of V6_2 (the text's §6.2, pp. 203–204: the determinant lines `λ(E)`,
`λ*(E)`, the maps `λ(Φ)`, `λ*(Φ)`, and the dual vector `v*` of a vector of a line).  Choices:
- This item is a block of definitions with three small claims.  `B` is the conjunction of
  (1) `λ(E) = Λ^max E`: the project's `maxPow E` is Mathlib's top exterior power
      `⋀[ℝ]^(dim E) E` (as a submodule of the exterior algebra), and it is a line (`finrank = 1`;
      the md's title calls `λ(E)` a "determinant line"), for finite-dimensional `E`;
  (2) `λ*(E) = (λ(E))*`: the project's `maxPowDual E` is the type `Module.Dual ℝ (maxPow E)`
      (a type equality, the definitional reading);
  (3) the defining formula `λ(Φ)(a₁ ∧ … ∧ aₙ) = Φ(a₁) ∧ … ∧ Φ(aₙ)` for the project's `maxPowMap`
      (for every family `a`, not only bases; `a₁ ∧ … ∧ aₙ` is the project's `wedge`, the product
      `ι(a₁) ⋯ ι(aₙ)` in the exterior algebra — I accept it, its docstring is the text's wedge);
  (4) "nontrivial iff `Φ` is an isomorphism": `λ(Φ) ≠ 0 ↔ Φ` bijective;
  (5) `λ(Ψ ∘ Φ) = λ(Ψ) ∘ λ(Φ)`;
  (6) `λ*(Φ)` is the dual (transpose) of `λ(Φ)`: `λ*(Φ)(φ)(w) = φ(λ(Φ) w)`;
  (7) the dual vector: for a line `L` and `v ≠ 0`, the project's `dualVec v` satisfies
      `v*(v) = 1` (this fixes `v*`, since `L` is a line).
- Setting: real vector spaces `E F G : Type` (universe 0), finite-dimensional, with
  `dim E = dim F = dim G` where maps `λ(Φ)` are formed (the text's "spaces of the same
  dimension"); the dimension equalities enter as the proof arguments of `maxPowMap`.
- Nothing here looks false to me.
-/
namespace RoundTrip.V6_2
open Polyfold

/-- `λ(E) = Λ^max E` and `λ*(E) = (λ(E))*`; `λ(Φ)` on decomposable vectors, nontrivial iff `Φ`
is an isomorphism, functorial; `λ*(Φ)` the dual of `λ(Φ)`; `v*(v) = 1`. -/
def B : Prop :=
  -- (1) `λ(E) = Λ^max E`, a line
  (∀ (E : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E],
    maxPow E = ⋀[ℝ]^(Module.finrank ℝ E) E ∧ Module.finrank ℝ (maxPow E) = 1) ∧
  -- (2) `λ*(E) = (λ(E))*`
  (∀ (E : Type) [AddCommGroup E] [Module ℝ E], maxPowDual E = Module.Dual ℝ (maxPow E)) ∧
  -- (3) `λ(Φ)(a₁ ∧ … ∧ aₙ) = Φ(a₁) ∧ … ∧ Φ(aₙ)`
  (∀ (E F : Type) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (Φ : E →ₗ[ℝ] F) (h : Module.finrank ℝ E = Module.finrank ℝ F)
    (a : Fin (Module.finrank ℝ E) → E),
      maxPowMap Φ h (wedge a rfl) = wedge (Φ ∘ a) h) ∧
  -- (4) `λ(Φ)` is nontrivial iff `Φ` is an isomorphism
  (∀ (E F : Type) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (Φ : E →ₗ[ℝ] F) (h : Module.finrank ℝ E = Module.finrank ℝ F),
      maxPowMap Φ h ≠ 0 ↔ Function.Bijective Φ) ∧
  -- (5) `λ(Ψ ∘ Φ) = λ(Ψ) ∘ λ(Φ)`
  (∀ (E F G : Type) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    (Φ : E →ₗ[ℝ] F) (Ψ : F →ₗ[ℝ] G)
    (h₁ : Module.finrank ℝ E = Module.finrank ℝ F) (h₂ : Module.finrank ℝ F = Module.finrank ℝ G),
      maxPowMap (Ψ ∘ₗ Φ) (h₁.trans h₂) = maxPowMap Ψ h₂ ∘ₗ maxPowMap Φ h₁) ∧
  -- (6) `λ*(Φ)` is the dual of `λ(Φ)`
  (∀ (E F : Type) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (Φ : E →ₗ[ℝ] F) (h : Module.finrank ℝ E = Module.finrank ℝ F)
    (φ : maxPowDual F) (w : maxPow E),
      maxPowDualMap Φ h φ w = φ (maxPowMap Φ h w)) ∧
  -- (7) the dual vector `v*` of `v ≠ 0` in a line: `v*(v) = 1`
  (∀ (L : Type) [AddCommGroup L] [Module ℝ L], Module.finrank ℝ L = 1 →
    ∀ v : L, v ≠ 0 → dualVec v v = 1)

end RoundTrip.V6_2
