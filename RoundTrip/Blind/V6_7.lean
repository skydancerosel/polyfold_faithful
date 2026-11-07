import Polyfold
/-! Blind formalization of V6_7 (the text's §6.2, (92) and Proposition 6.6, p. 207: the
isomorphism `Ψ_E : λ(C) ⊗ λ(A) ⊗ λ*(D) → λ(B)`).  Choices:
- Setting and the choices of (91) as in my V6_5 (prelude copied): finite-dimensional
  `A B C D : Type`, the project's `FourTermExact`, my `Choice91` with the wedges
  `w_A = a₁ ∧ … ∧ aₙ`, `w_D = d₁ ∧ … ∧ d_l`, `w_B = α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}`,
  `w_C = c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_{m−n}` (`c'ᵢ = β(b'ᵢ)`).  `λ(C) ⊗ λ(A) ⊗ λ*(D)` is bracketed
  `λ(C) ⊗ (λ(A) ⊗ λ*(D))`.  `Φ_E` is the project's `FourTermExact.phi`, `Ψ_E` its
  `FourTermExact.psi`, `ῑ` its `contractDual`.
- `B` is the conjunction of
  (1) `ῑ(v ⊗ b ⊗ v*) = b` for every `v ≠ 0` of `λ(C)`, every `b ∈ λ(B)` and the dual vector `v*`
      (any `φ` with `φ(v) = 1`; unique on the line `λ(C)`);
  (2) (92): `Ψ_E(c ⊗ h) = ῑ(c ⊗ Φ_E(h))` for all `c ∈ λ(C)`, `h ∈ λ(A) ⊗ λ*(D)`;
  (3) `Ψ_E` is an isomorphism (the md's title, Proposition 6.6): bijective;
  (4) the formula `Ψ_E(c ⊗ a ⊗ d*) = b₁ ∧ … ∧ bₙ ∧ b'₁ ∧ … ∧ b'_{m−n}` for every choice of (91),
      `a = w_A`, `d* = w_D*`, `bᵢ = α(aᵢ)` (the md: "with the bases of (91)"; (91) has no other
      `bᵢ`).
- MISPRINT (as I read it): the md writes `c = c'₁ ∧ ⋯ ∧ c'_l ∧ c₁ ∧ ⋯ ∧ c_{m−n}`.  With the
  names of (91) (`c₁, …, c_l` the lifts of `d`, `c'₁, …, c'_{m−n}` = `β(b')`) this is ill-formed
  (`c'ᵢ` exists only for `i ≤ m − n`, `cᵢ` for `i ≤ l`).  I read the index ranges as right and
  the primes as swapped: the first block is the `l` lifts of `d`, the second the `m − n` vectors
  `β(b')`, i.e. `c = w_C`, the `C`-side wedge of (91); then (4) is exactly what (91) and (92)
  give.  The other reading (`β(b')` first, then the lifts) would change the right side by the
  sign `(−1)^{l(m−n)}`, so it would be false in general.
- Nothing else looks false to me.
-/
namespace RoundTrip.V6_7
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

/-- (92) and Proposition 6.6: `ῑ(v ⊗ b ⊗ v*) = b`; `Ψ_E(c ⊗ h) = ῑ(c ⊗ Φ_E(h))` is an
isomorphism, and `Ψ_E(c ⊗ a ⊗ d*) = α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}` for the bases of
(91). -/
def B : Prop :=
  -- (1) `ῑ(v ⊗ b ⊗ v*) = b`
  (∀ (B C : Type) [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ C] (v : maxPow C), v ≠ 0 →
      ∀ (b : maxPow B) (φ : maxPowDual C), φ v = 1 →
        contractDual B C (v ⊗ₜ[ℝ] (b ⊗ₜ[ℝ] φ)) = b) ∧
  (∀ (A B C D : Type) [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
    [FiniteDimensional ℝ D] (S : FourTermExact A B C D),
    -- (2) (92)
    (∀ (c : maxPow C) (h : maxPow A ⊗[ℝ] maxPowDual D),
      S.psi (c ⊗ₜ[ℝ] h) = contractDual B C (c ⊗ₜ[ℝ] S.phi h)) ∧
    -- (3) `Ψ_E` is an isomorphism
    Function.Bijective S.psi ∧
    -- (4) the value on the bases of (91)
    (∀ (χ : Choice91 S) (φD : maxPowDual D), φD χ.wD = 1 →
      S.psi (χ.wC ⊗ₜ[ℝ] (χ.wA ⊗ₜ[ℝ] φD)) = χ.wB))

end RoundTrip.V6_7
