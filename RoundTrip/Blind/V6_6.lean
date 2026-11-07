import Polyfold
/-! Blind formalization of V6_6 (the text's §6.2, Lemma 6.5, p. 206; proof §6.7.1, pp. 234–235:
`Φ_E` does not depend on the choices).  Choices:
- Setting and the choices of (91) exactly as in my V6_5 (prelude copied): finite-dimensional
  `A B C D : Type`, the project's `FourTermExact` (fields read with `#print`), my structure
  `Choice91` (bases `a`, `d`, complement `Z` with basis `b'`, complement `V`, lifts `c ∈ V` of
  `d`; the dimension fields `dimB`, `dimC` only make the wedges typecheck), and `Sat91 Φ χ`:
  `Φ(w_A ⊗ φ_D) = w_B ⊗ φ_C` whenever `φ_D(w_D) = 1`, `φ_C(w_C) = 1` (formula (91)).
- "With the two ordering conventions": `α(a)` before `b'` in `λ(B)`, `c` before `c' = β(b')` in
  `λ(C)` (`Fin.append`), as in (91).
- "Does not depend on the choices", in two readings, `B` is their conjunction:
  (1) the intrinsic reading: a linear map satisfying (91) for one choice satisfies it for every
      other choice (since the source vector of a choice spans the line `λ(A) ⊗ λ*(D)`, this says
      the maps defined by (91) from any two choices coincide);
  (2) the reading for the project's `Φ_E` (`FourTermExact.phi`, made with one choice): it
      satisfies (91) for every choice.
- Nothing here looks false to me (I checked the invariance under each change of choice: the
  determinant factors cancel, and changes of `Z`, `V` do not change the wedges).
-/
namespace RoundTrip.V6_6
open Polyfold
open scoped TensorProduct

noncomputable section
variable {A B C D : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]

/-- The choices of (91) for the exact sequence `S : 0 → A → B → C → D → 0`. -/
structure Choice91 (S : FourTermExact A B C D) where
  /-- a basis `a₁, …, aₙ` of `A` -/
  a : Module.Basis (Fin (Module.finrank ℝ A)) ℝ A
  /-- a basis `d₁, …, d_l` of `D` -/
  d : Module.Basis (Fin (Module.finrank ℝ D)) ℝ D
  /-- `j = m − n` -/
  j : ℕ
  /-- the complement `Z` of `α(A)` in `B` -/
  Z : Submodule ℝ B
  isCompl_Z : IsCompl (LinearMap.range S.α) Z
  /-- a basis `b'₁, …, b'_{m−n}` of `Z` -/
  b' : Module.Basis (Fin j) ℝ Z
  /-- the complement `V` of `β(B)` in `C` -/
  V : Submodule ℝ C
  isCompl_V : IsCompl (LinearMap.range S.β) V
  /-- `c₁, …, c_l ∈ V` with `γ(cᵢ) = dᵢ` -/
  c : Fin (Module.finrank ℝ D) → C
  c_mem : ∀ i, c i ∈ V
  γ_c : ∀ i, S.γ (c i) = d i
  dimB : Module.finrank ℝ A + j = Module.finrank ℝ B
  dimC : Module.finrank ℝ D + j = Module.finrank ℝ C

variable {S : FourTermExact A B C D}

/-- `a₁ ∧ … ∧ aₙ ∈ λ(A)`. -/
def Choice91.wA (χ : Choice91 S) : maxPow A := wedge (⇑χ.a) rfl
/-- `d₁ ∧ … ∧ d_l ∈ λ(D)`. -/
def Choice91.wD (χ : Choice91 S) : maxPow D := wedge (⇑χ.d) rfl
/-- `α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n} ∈ λ(B)`. -/
def Choice91.wB (χ : Choice91 S) : maxPow B :=
  wedge (Fin.append (S.α ∘ ⇑χ.a) (fun i => (χ.b' i : B))) χ.dimB
/-- `c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_{m−n} ∈ λ(C)`, `c'ᵢ = β(b'ᵢ)`. -/
def Choice91.wC (χ : Choice91 S) : maxPow C :=
  wedge (Fin.append χ.c (fun i => S.β (χ.b' i : B))) χ.dimC

/-- `Φ` satisfies (91) for the choice `χ`:
`Φ((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) = (α(a₁) ∧ … ∧ b'_{m−n}) ⊗ (c₁ ∧ … ∧ c'_{m−n})*`. -/
def Sat91 (Φ : (maxPow A ⊗[ℝ] maxPowDual D) →ₗ[ℝ] (maxPow B ⊗[ℝ] maxPowDual C))
    (χ : Choice91 S) : Prop :=
  ∀ (φD : maxPowDual D) (φC : maxPowDual C), φD χ.wD = 1 → φC χ.wC = 1 →
    Φ (χ.wA ⊗ₜ[ℝ] φD) = χ.wB ⊗ₜ[ℝ] φC

end

/-- Lemma 6.5: a map defined by (91) for one choice satisfies (91) for every choice; in particular
the project's `Φ_E` satisfies (91) for every choice. -/
def B : Prop :=
  ∀ (A B C D : Type) [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
    [FiniteDimensional ℝ D] (S : FourTermExact A B C D),
    (∀ (χ₁ χ₂ : Choice91 S)
      (Φ : (maxPow A ⊗[ℝ] maxPowDual D) →ₗ[ℝ] (maxPow B ⊗[ℝ] maxPowDual C)),
      Sat91 Φ χ₁ → Sat91 Φ χ₂) ∧
    (∀ χ : Choice91 S, Sat91 S.phi χ)

end RoundTrip.V6_6
