import Polyfold
/-! Blind formalization of V6_11 (the text's §6.3, Lemma 6.10, p. 208; proof pp. 208–209).

Text: for `P, P' ∈ Π_T` there is `P'' ∈ Π_T` with `P'' ≤ P` and `P'' ≤ P'`.  The proof takes
topological complements `X`, `X'` of `R(P) ∩ R(P')` in `R(P)`, `R(P')`, a topological complement
`Z` of `X ⊕ X' ⊕ (R(P) ∩ R(P'))` in `F`, and `P''` the projection onto `R(P) ∩ R(P')` along
`Z ⊕ X ⊕ X'`.

Choices:
- Setting and prelude as in the blind V6_10: real Banach spaces `E F : Type`, `T : E →L[ℝ] F`
  Fredholm in the classical sense (`IsFredholmOp`), good left-projections `IsGLP`/`PiT` and the
  order `PLe P Q := P = P ∘L Q ∧ P = Q ∘L P` written out (project's `IsGoodLeftProj`/`ProjLE`
  not used).
- `B` is Lemma 6.10 itself (the existence of a common lower bound).  The sentence on the proof
  describes how the proof works, not the claim; I formalize it separately and literally as
  `B_proof` (for all choices of the complements, the projection `P''` described is a common lower
  bound in `Π_T`).  "Topological complement" of a closed subspace in a Banach space: a closed
  subspace that is an algebraic complement (the projections are then bounded by the closed graph
  theorem); `R(P) ∩ R(P')` is closed.  "The projection onto `I` along `Z ⊕ X ⊕ X'`": any bounded
  `P''` with `P''² = P''`, range `I` and kernel `Z ⊔ X ⊔ X'` (it exists and is unique).  The
  directness of the sum `X ⊕ X' ⊕ I` (true) is not asserted.
- I believe `B_proof` is FALSE as we read it: `P'' ≤ P` needs `P'' P = P''`, i.e.
  `ker P ⊆ ker P'' = Z ⊕ X ⊕ X'`, which the choices do not give.  Example: `E = F = ℝ²`,
  `T = id`, `P` the projection onto `ℝe₁` along `ℝe₂`, `P'` the projection onto `ℝe₁` along
  `ℝ(e₁ + e₂)` (both in `Π_T`).  Then `I = ℝe₁`, `X = X' = 0`, and for every complement `Z` of
  `ℝe₁` the `P''` above has range `ℝe₁`; `P'' ≤ P` forces `Z = ℝe₂` and `P'' ≤ P'` forces
  `Z = ℝ(e₁ + e₂)`.  (Here `P'' = 0` is a common lower bound, so `B` itself holds.)
-/
namespace RoundTrip.V6_11
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

/-- Lemma 6.10: any two good left-projections of a Fredholm `T` have a common lower bound in
`Π_T`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T →
      ∀ P ∈ PiT T, ∀ P' ∈ PiT T, ∃ P'' ∈ PiT T, PLe P'' P ∧ PLe P'' P'

/-- The proof's construction, literally (believed false, see the header): for complements `X`,
`X'` of `I = R(P) ∩ R(P')` in `R(P)`, `R(P')` and `Z` of `X ⊕ X' ⊕ I` in `F`, the projection onto
`I` along `Z ⊕ X ⊕ X'` lies in `Π_T` and is below `P` and `P'`. -/
def B_proof : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T →
      ∀ P ∈ PiT T, ∀ P' ∈ PiT T, ∀ X X' Z : Submodule ℝ F,
        -- `X` a topological complement of `I` in `R(P)`
        IsClosed (X : Set F) →
        X ⊓ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F)) = ⊥ →
        X ⊔ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F)) =
          LinearMap.range (P : F →ₗ[ℝ] F) →
        -- `X'` a topological complement of `I` in `R(P')`
        IsClosed (X' : Set F) →
        X' ⊓ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F)) = ⊥ →
        X' ⊔ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F)) =
          LinearMap.range (P' : F →ₗ[ℝ] F) →
        -- `Z` a topological complement of `X ⊕ X' ⊕ I` in `F`
        IsClosed (Z : Set F) →
        IsCompl Z
          (X ⊔ X' ⊔ (LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F))) →
        -- `P''` the projection onto `I` along `Z ⊕ X ⊕ X'`
        ∀ P'' : F →L[ℝ] F, P'' ∘L P'' = P'' →
          LinearMap.range (P'' : F →ₗ[ℝ] F) =
            LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F) →
          LinearMap.ker (P'' : F →ₗ[ℝ] F) = Z ⊔ X ⊔ X' →
          P'' ∈ PiT T ∧ PLe P'' P ∧ PLe P'' P'

end RoundTrip.V6_11
