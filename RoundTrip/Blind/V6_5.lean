import Polyfold
/-! Blind formalization of V6_5 (the text's §6.2, p. 206, formula (91): the isomorphism
`Φ_E : λ(A) ⊗ λ*(D) → λ(B) ⊗ λ*(C)` of a four-term exact sequence `E`).  Choices:
- Setting: finite-dimensional real vector spaces `A B C D : Type` (universe 0) and the project's
  `FourTermExact A B C D` (fields read with `#print`: linear maps `α β γ`, `α` injective,
  `range α = ker β`, `range β = ker γ`, `γ` surjective — the text's exact sequence
  `0 → A → B → C → D → 0`).  `λ`, `λ*`, wedges are the project's `maxPow`, `maxPowDual`, `wedge`
  (characterized in my V6_2).
- The choices of (91) are my structure `Choice91` (I did not use the project's
  `FourTermExact.Choice`): a basis `a` of `A` (indexed by `Fin n`, `n = dim A`), a basis `d` of
  `D` (`Fin l`, `l = dim D`), a complement `Z` of `α(A)` in `B` with a basis `b'` (`Fin j`), a
  complement `V` of `β(B)` in `C`, vectors `cᵢ ∈ V` with `γ(cᵢ) = dᵢ`; `c'ᵢ = β(b'ᵢ)`.  The
  fields `dimB : n + j = dim B`, `dimC : l + j = dim C` (so `j = m − n`) are consequences of the
  other data and exactness; they are recorded as fields only so that the wedges of (91) typecheck
  (`wedge` wants a family of exactly `dim` vectors), and exclude no genuine choice.
- "The two conventions on the order": on the `B` side `α(a₁), …, α(aₙ)` come first, then
  `b'₁, …, b'_{m−n}` (`Fin.append`); on the `C` side `c₁, …, c_l` first, then `c'₁, …, c'_{m−n}`.
- The dual vectors `(d₁ ∧ … ∧ d_l)*`, `(c₁ ∧ … ∧ c'_{m−n})*` are not taken from the project's
  `dualVec`: `Sat91 Φ χ` says `Φ(w_A ⊗ φ_D) = w_B ⊗ φ_C` for all `φ_D`, `φ_C` with
  `φ_D(w_D) = 1`, `φ_C(w_C) = 1` (the text's "`v*` fixed by `v*(v) = 1`"; on a line these are
  unique).
- `B` is the conjunction, for every such sequence, of
  (1) (91) defines an isomorphism of lines for every choice: the wedges `w_A`, `w_D`, `w_B`, `w_C`
      are all nonzero (so the source `w_A ⊗ w_D*` and the value `w_B ⊗ w_C*` are nonzero vectors of
      the lines `λ(A) ⊗ λ*(D)` and `λ(B) ⊗ λ*(C)`, and (91) determines a linear isomorphism);
  (2) the project's `Φ_E` (`FourTermExact.phi`) is the map of (91) for some choice
      (∃ χ, `Sat91 S.phi χ`) — a definition made with choices; that it satisfies (91) for EVERY
      choice is Lemma 6.5 (my V6_6);
  (3) `Φ_E` is an isomorphism (bijective), as the md's title says.
- Nothing here looks false to me.
-/
namespace RoundTrip.V6_5
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

/-- (91): for every choice the wedges are nonzero (so (91) defines an isomorphism of lines); the
project's `Φ_E` is the map of (91) for a choice, and is an isomorphism. -/
def B : Prop :=
  ∀ (A B C D : Type) [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
    [FiniteDimensional ℝ D] (S : FourTermExact A B C D),
    (∀ χ : Choice91 S, χ.wA ≠ 0 ∧ χ.wD ≠ 0 ∧ χ.wB ≠ 0 ∧ χ.wC ≠ 0) ∧
    (∃ χ : Choice91 S, Sat91 S.phi χ) ∧
    Function.Bijective S.phi

end RoundTrip.V6_5
