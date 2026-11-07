import Polyfold
/-! Blind formalization of V6_8 (the text's §6.3, Definition 6.7, p. 208: the determinant
`det(T)` of a Fredholm operator).  Choices:
- Setting: real Banach spaces `E F : Type` (universe 0; `NormedAddCommGroup`, `NormedSpace ℝ`,
  `CompleteSpace`) and a bounded operator `T : E →L[ℝ] F`.  "Fredholm" is my `IsFredholmB`, the
  textbook definition: `ker T` finite-dimensional, range closed, `coker T = F / R(T)`
  finite-dimensional (I did not use Mathlib's `ContinuousLinearMap.IsFredholm`, whose extra
  clauses — strict map, complemented kernel — are automatic for Banach spaces).
- `ker T`, `R(T)` are the kernel and range of the underlying linear map; `coker T` is the
  algebraic quotient `F ⧸ R(T)`.  `λ`, `λ*` are the project's `maxPow`, `maxPowDual`
  (characterized in my V6_2); `detB T = λ(ker T) ⊗ λ*(coker T)` is my abbreviation.
- `B` is the conjunction, for every Fredholm `T`, of
  (1) the definition: the project's `fredholmDet T` is the type `λ(ker T) ⊗ λ*(coker T)` (a type
      equality, the definitional reading);
  (2) "a line": `finrank ℝ (det T) = 1`;
  (3) the remark on the other convention `λ(ker T) ⊗ λ(coker(T)*)`: with the text's convention
      `ι : λ(A*) → λ*(A)` of Definition 6.3 (the project's `iotaDual`, `A = coker T`), the map
      `1 ⊗ ι : λ(ker T) ⊗ λ(coker(T)*) → λ(ker T) ⊗ λ*(coker T)` is an isomorphism.  "Naturally"
      is not formalized beyond this: the naturality of `ι` itself is Proposition 6.4 (my V6_4).
      Reading of "given a convention identifying `λ*(A)` and `λ(A*)`": the convention is `ι`.
- Nothing here looks false to me.
-/
namespace RoundTrip.V6_8
open Polyfold
open scoped TensorProduct

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `T` is a Fredholm operator: finite-dimensional kernel, closed range, finite-dimensional
cokernel `F / R(T)`. -/
def IsFredholmB (T : E →L[ℝ] F) : Prop :=
  FiniteDimensional ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) ∧ IsClosed (Set.range T) ∧
    FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))

/-- `det(T) = λ(ker T) ⊗ λ*(coker T)`. -/
abbrev detB (T : E →L[ℝ] F) : Type :=
  maxPow (LinearMap.ker (T : E →ₗ[ℝ] F)) ⊗[ℝ] maxPowDual (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))

end

/-- Definition 6.7: `det(T) = λ(ker T) ⊗ λ*(coker T)`, a line; `1 ⊗ ι` identifies it with
`λ(ker T) ⊗ λ(coker(T)*)`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmB T →
      fredholmDet T = detB T ∧
      Module.finrank ℝ (fredholmDet T) = 1 ∧
      Function.Bijective
        (TensorProduct.map (LinearMap.id : maxPow (LinearMap.ker (T : E →ₗ[ℝ] F)) →ₗ[ℝ] _)
          (iotaDual (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))))

end RoundTrip.V6_8
