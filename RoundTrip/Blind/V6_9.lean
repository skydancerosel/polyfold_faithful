import Polyfold
/-! Blind formalization of V6_9 (the text's §6.3, Definition 6.8, p. 208: orientations of a
Fredholm operator).  Choices:
- Setting as in my V6_8: real Banach spaces `E F : Type` (universe 0), `T : E →L[ℝ] F` Fredholm
  in the textbook sense (`IsFredholmB`: finite-dimensional kernel, closed range,
  finite-dimensional cokernel), and `det(T) = λ(ker T) ⊗ λ*(coker T)` written out from the
  project's `maxPow`, `maxPowDual` (`detB`, as in V6_8; I did not use `fredholmDet` here).
- "An orientation of the line `L`": a ray of `L`, i.e. a class of nonzero vectors modulo positive
  scalars (Mathlib's `Module.Ray ℝ L`; for a line these are the two components of `L \ {0}`).
- `B` (the definitional reading): for Fredholm `T`, the project's type `FredholmOrientation T` of
  orientations of `T` is the type of rays of `det(T)` (a type equality).
- Nothing here looks false to me.
-/
namespace RoundTrip.V6_9
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

/-- Definition 6.8: an orientation of the Fredholm operator `T` is an orientation (a ray) of the
line `det(T)`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmB T → FredholmOrientation T = Module.Ray ℝ (detB T)

end RoundTrip.V6_9
