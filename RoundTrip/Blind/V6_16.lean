import Polyfold
/-! Blind formalization of V6_16 (the text's §6.3, pp. 211–212, Lemma 6.14, p. 212).

Text: for `T` Fredholm and a linear `φ : ℝⁿ → F` with `T_φ(e, r) = Te + φ(r)` onto, the sequence
`0 → ker T → ker T_φ → ℝⁿ → F/R(T) → 0` with `j(e) = (e, 0)`, `π(e, r) = r` and
`[φ](r) = φ(r) + R(T)` is exact.

Choices:
- Setting: real Banach spaces `E F : Type` (spaces in `Type`, as asked), `T : E →L[ℝ] F`
  Fredholm in the classical sense (`IsFredholmOp`, the prelude of the blind V6_10).
  `ℝⁿ = Fin n → ℝ`, `E ⊕ ℝⁿ = E × (Fin n → ℝ)` (product norm).
- "a linear `φ : ℝⁿ → F`": `φ : (Fin n → ℝ) →L[ℝ] F` (every linear map on `ℝⁿ` is continuous,
  so this is no restriction); `T_φ = T.coprod φ`, `(e, r) ↦ Te + φ(r)`, assumed onto.
- The maps are written out here: `jS` (`e ↦ (e, 0)`, into `ker T_φ`), `piS` (`(e, r) ↦ r` on
  `ker T_φ`), `clsPhi` (`r ↦ φ(r) + R(T)`).  The project's `stabJ`/`stabPi`/`stabClass`/`stabSeq`
  are not used.
- "Exact" for `0 → A →α B →β C →γ D → 0`: `α` injective, `range α = ker β`, `range β = ker γ`,
  `γ` surjective.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_16
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

section Stab
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ}

/-- The stabilization `T_φ : E ⊕ ℝⁿ → F`, `(e, r) ↦ Te + φ(r)`. -/
def Tphi (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →L[ℝ] F :=
  T.coprod φ

/-- `j : ker T → ker T_φ`, `e ↦ (e, 0)`. -/
def jS (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ]
      LinearMap.ker ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F) :=
  LinearMap.codRestrict _
    ((LinearMap.inl ℝ E (Fin n → ℝ)) ∘ₗ (LinearMap.ker (T : E →ₗ[ℝ] F)).subtype)
    (fun x => by simp [Tphi])

/-- `π : ker T_φ → ℝⁿ`, `(e, r) ↦ r`. -/
def piS (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    LinearMap.ker ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F) →ₗ[ℝ]
      (Fin n → ℝ) :=
  (LinearMap.snd ℝ E (Fin n → ℝ)) ∘ₗ (LinearMap.ker _).subtype

/-- `[φ] : ℝⁿ → F/R(T)`, `r ↦ φ(r) + R(T)`. -/
def clsPhi (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    (Fin n → ℝ) →ₗ[ℝ] F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) :=
  (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ ∘ₗ (φ : (Fin n → ℝ) →ₗ[ℝ] F)

end Stab

/-- Lemma 6.14: for a Fredholm `T` and `φ : ℝⁿ → F` with `T_φ` onto, the sequence
`0 → ker T →j ker T_φ →π ℝⁿ →[φ] F/R(T) → 0` is exact. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (n : ℕ) (T : E →L[ℝ] F)
    (φ : (Fin n → ℝ) →L[ℝ] F),
    IsFredholmOp T → Function.Surjective (Tphi T φ) →
      Function.Injective (jS T φ) ∧
      LinearMap.range (jS T φ) = LinearMap.ker (piS T φ) ∧
      LinearMap.range (piS T φ) = LinearMap.ker (clsPhi T φ) ∧
      Function.Surjective (clsPhi T φ)

end RoundTrip.V6_16
