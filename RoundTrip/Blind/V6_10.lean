import Polyfold
/-! Blind formalization of V6_10 (the text's §6.3, Definition 6.9 and the paragraphs after it,
p. 208).

Text: a good left-projection for a Fredholm `T : E → F` is a bounded projection `P : F → F` with
(1) `dim F/R(P) < ∞` and (2) `R(P ∘ T) = R(P)`; `Π_T` is their set.  Then `P` is Fredholm of
index `0`, `PT` is Fredholm with `ind(PT) = ind(T)`, `P ≤ Q` iff `P = PQ = QP` is a partial order
on `Π_T`, and `R(P) ∩ R(P')` has finite codimension.

Choices:
- Setting: real Banach spaces `E F : Type` (`NormedAddCommGroup`, `NormedSpace ℝ`,
  `CompleteSpace`); spaces are put in `Type` as asked (the claim does not involve universes).
  Operators are `E →L[ℝ] F` (bounded linear maps).
- "Fredholm" is the classical notion, written out here (`IsFredholmOp`, the prelude of the blind
  V3_36): finite-dimensional kernel, closed range, finite-dimensional cokernel `F ⧸ R(T)`.
  The index is `dim ker − dim coker` as an integer (`fredIdx`).  I did not use Mathlib's
  `ContinuousLinearMap.IsFredholm` nor the project's `fredholmIndex` (they are equivalent on
  Banach spaces / literally the same formula, but the text's notion is the classical one).
- "bounded projection": `P : F →L[ℝ] F` with `P ∘L P = P`.  Good left-projections (`IsGLP`),
  `Π_T` (`PiT`) and the order (`PLe P Q := P = P ∘L Q ∧ P = Q ∘L P`) are written out here (the
  project's `IsGoodLeftProj`/`goodLeftProjs`/`ProjLE` have, by `#print`, the same fields; they are
  not used).
- "a partial order on `Π_T`": reflexive, antisymmetric and transitive for elements of `Π_T`.
- "`R(P) ∩ R(P')` has finite codimension": for `P, P' ∈ Π_T`, `F ⧸ (R(P) ⊓ R(P'))` is
  finite-dimensional.
- The claims about `P` and `PT` are made for every `P ∈ Π_T` of a Fredholm `T`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_10
open Polyfold

section Fredholm
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- A bounded operator is Fredholm: finite-dimensional kernel, closed range, finite-dimensional
cokernel. -/
def IsFredholmOp (L : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ (LinearMap.ker (L : X →ₗ[ℝ] Y)) ∧
    IsClosed (LinearMap.range (L : X →ₗ[ℝ] Y) : Set Y) ∧
    FiniteDimensional ℝ (Y ⧸ LinearMap.range (L : X →ₗ[ℝ] Y))

/-- The Fredholm index `dim ker L − dim (Y / range L)`. -/
noncomputable def fredIdx (L : X →L[ℝ] Y) : ℤ :=
  (Module.finrank ℝ (LinearMap.ker (L : X →ₗ[ℝ] Y)) : ℤ) -
    (Module.finrank ℝ (Y ⧸ LinearMap.range (L : X →ₗ[ℝ] Y)) : ℤ)

end Fredholm

section Proj
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Definition 6.9: `P` is a good left-projection for `T`: a bounded projection of `F` with
(1) `dim F/R(P) < ∞` and (2) `R(P ∘ T) = R(P)`. -/
def IsGLP (T : E →L[ℝ] F) (P : F →L[ℝ] F) : Prop :=
  P ∘L P = P ∧ FiniteDimensional ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) ∧
    LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) = LinearMap.range (P : F →ₗ[ℝ] F)

/-- `Π_T`, the set of good left-projections for `T`. -/
def PiT (T : E →L[ℝ] F) : Set (F →L[ℝ] F) := {P | IsGLP T P}

/-- The order `P ≤ Q` iff `P = PQ = QP`. -/
def PLe (P Q : F →L[ℝ] F) : Prop := P = P ∘L Q ∧ P = Q ∘L P

end Proj

/-- After Definition 6.9: for a Fredholm `T` and `P ∈ Π_T`, `P` is Fredholm of index `0` and `PT`
is Fredholm of index `ind(T)`; `≤` is a partial order on `Π_T`; and `R(P) ∩ R(P')` has finite
codimension for `P, P' ∈ Π_T`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T →
      (∀ P ∈ PiT T, IsFredholmOp P ∧ fredIdx P = 0 ∧
        IsFredholmOp (P ∘L T) ∧ fredIdx (P ∘L T) = fredIdx T) ∧
      (∀ P ∈ PiT T, PLe P P) ∧
      (∀ P ∈ PiT T, ∀ Q ∈ PiT T, PLe P Q → PLe Q P → P = Q) ∧
      (∀ P ∈ PiT T, ∀ Q ∈ PiT T, ∀ R ∈ PiT T, PLe P Q → PLe Q R → PLe P R) ∧
      (∀ P ∈ PiT T, ∀ P' ∈ PiT T,
        FiniteDimensional ℝ
          (F ⧸ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F))))

end RoundTrip.V6_10
