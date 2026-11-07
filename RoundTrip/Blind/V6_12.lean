import Polyfold
/-! Blind formalization of V6_12 (the text's §6.3, Lemma 6.11, p. 209).

Text: for `P ∈ Π_T` the sequence `0 → ker T → ker(PT) → F/R(P) → coker T → 0`, with the inclusion
`j^P_T`, `Φ^P_T(x) = Tx + R(P)` and `π^P_T(f + R(P)) = (I − P)f + R(T)`, is exact.

Choices:
- Setting and prelude as in the blind V6_10: real Banach spaces `E F : Type`, `T : E →L[ℝ] F`
  Fredholm in the classical sense (`IsFredholmOp`; Definition 6.9 is made for Fredholm `T`, so
  the hypothesis is kept although exactness does not use it), `IsGLP` written out.
- `coker T = F ⧸ R(T)`; kernels and ranges are those of the underlying linear maps.
- The maps are written out here: `jMap` (the inclusion `ker T ⊆ ker(PT)`), `PhiMap`
  (`x ↦ Tx + R(P)`), `piMap` (`f + R(P) ↦ (I − P)f + R(T)`, defined by `Submodule.liftQ`; it is
  well defined because `P` is a projection, which is the only property of `P` it uses).  The
  project's `projSeqJ`/`projSeqPhi`/`projSeqPi`/`projSeq` are not used.
- "Exact" for `0 → A →α B →β C →γ D → 0`: `α` injective, `range α = ker β`, `range β = ker γ`,
  `γ` surjective.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_12
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

/-- `j^P_T : ker T → ker(PT)`, the inclusion. -/
def jMap (T : E →L[ℝ] F) (P : F →L[ℝ] F) :
    LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ] LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
  Submodule.inclusion (fun x hx => by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    simp [hx])

/-- `Φ^P_T : ker(PT) → F/R(P)`, `x ↦ Tx + R(P)`. -/
def PhiMap (T : E →L[ℝ] F) (P : F →L[ℝ] F) :
    LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) →ₗ[ℝ]
      F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) :=
  (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ ∘ₗ (T : E →ₗ[ℝ] F) ∘ₗ
    (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype

/-- `π^P_T : F/R(P) → coker T`, `f + R(P) ↦ (I − P)f + R(T)` (well defined for a projection). -/
def piMap (T : E →L[ℝ] F) (P : F →L[ℝ] F) (hP : P ∘L P = P) :
    F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) →ₗ[ℝ] F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) :=
  (LinearMap.range (P : F →ₗ[ℝ] F)).liftQ
    ((LinearMap.range (T : E →ₗ[ℝ] F)).mkQ ∘ₗ (LinearMap.id - (P : F →ₗ[ℝ] F))) (by
      rintro _ ⟨y, rfl⟩
      have h : P (P y) = P y := by
        simpa using congrArg (fun Q : F →L[ℝ] F => Q y) hP
      simp [LinearMap.mem_ker, h])

end Proj

/-- Lemma 6.11: for a Fredholm `T` and `P ∈ Π_T`, the sequence
`0 → ker T →j ker(PT) →Φ F/R(P) →π coker T → 0` is exact. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T → ∀ (P : F →L[ℝ] F) (hP : IsGLP T P),
      Function.Injective (jMap T P) ∧
      LinearMap.range (jMap T P) = LinearMap.ker (PhiMap T P) ∧
      LinearMap.range (PhiMap T P) = LinearMap.ker (piMap T P hP.1) ∧
      Function.Surjective (piMap T P hP.1)

end RoundTrip.V6_12
