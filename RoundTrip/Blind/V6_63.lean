import Polyfold
/-! Blind formalization of V6_63 (the text's §6.7.1, the proof of Lemma 6.5, pp. 234–235).

Text: with complements `(V, W)`, a change of the basis of `V` by `σ` multiplies both wedges of (91)
by `det(σ)`, so has no influence.  A change of the bases of `A` and `D` multiplies `a ⊗ d*` by
`det(τ)/det(ε)`, and the vector is said to be independent of the bases iff `det(τ) = det(ε)`.
For two choices of complements, the new basis vectors differ from the old by `qᵢ ∈ α(A)` and
`pᵢ ∈ β(C)`, which leaves the wedges unchanged.

Choices:
- Setting: finite-dimensional real vector spaces `A B C D : Type` (universe 0) and an exact
  sequence `0 → A →α B →β C →γ D → 0`, written with plain linear maps and exactness hypotheses
  (`α` injective, `R(α) = ker β`, `R(β) = ker γ`, `γ` onto); I did not use the project's
  `FourTermExact` / `FourTermExact.Choice` (the computations are about explicit vectors).
- The data of (91) (item V6_5): a complement `Z` of `α(A)` in `B`, a complement `V` of `β(B)` in
  `C`, a basis `a` of `A` (`n = dim A`), a basis `d` of `D` (`l = dim D`), a basis `b'` of `Z`
  (`j` vectors, `n + j = dim B`), vectors `cᵢ ∈ V` with `γ(cᵢ) = dᵢ`, `c'ᵢ = β(b'ᵢ)`
  (`l + j = dim C`).  The two wedges of (91), with the text's order conventions:
  `wB = α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_j ∈ λ(B)` and `wC = c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_j ∈ λ(C)`
  (the project's `wedge` of a family of `dim` vectors, `Fin.append` for the concatenation); the
  vector of (91) is `wB ⊗ wC*` (`dualVec`: `v*(v) = 1`), the source vector `a ⊗ d*`.
- "With complements `(V, W)`, a change of the basis of `V` by `σ`": the complement whose basis
  enters BOTH wedges is the complement `Z` of `α(A)` in `B` (its basis `b'` gives `c' = β(b')`), so
  `V` there is my `Z`.  A change by a `j × j` matrix `σ`: `b''ᵢ = Σₖ σᵢₖ b'ₖ`.  Claim: both wedges
  are multiplied by `det σ` (any `σ`), and for invertible `σ` the vector `wB ⊗ wC*` is unchanged.
- "A change of the bases of `A` and `D`" by invertible `τ`, `ε`: `a'ᵢ = Σ τᵢₖ aₖ`,
  `d'ᵢ = Σ εᵢₖ dₖ`, with new vectors `c̃ᵢ ∈ V`, `γ(c̃ᵢ) = d'ᵢ`.  Claim: `a' ⊗ d'*` is
  `(det τ / det ε) · a ⊗ d*`, and so is the vector of (91) (that both sides change by the same
  factor is what makes `Φ_E` well defined; I include it as the evident content of the step);
  "independent of the bases iff `det τ = det ε`": for both vectors, equal to the old one iff
  `det τ = det ε`.
- "For two choices of complements": new complements `Z₂` of `α(A)` and `V₂` of `β(B)`.  Claims:
  (i) there is a basis `b₂` of `Z₂` with `b₂ᵢ − b'ᵢ ∈ α(A)`; (ii) every `c₂ᵢ ∈ V₂` with
  `γ(c₂ᵢ) = dᵢ` has `c₂ᵢ − cᵢ ∈ β(B)`; (iii) vectors differing from the old ones by such
  `qᵢ ∈ α(A)`, `pᵢ ∈ β(B)` give the same two wedges.
- MISPRINT: "`pᵢ ∈ β(C)`" is ill-typed (`β : B → C`); formalized as `β(B)` (`= ker γ`, the
  set in which two lifts of `dᵢ` differ).
- The dimension equalities `n + j = dim B`, `l + j = dim C` are hypotheses (they follow from the
  choices); the wedges need them.
-/
namespace RoundTrip.V6_63
open Polyfold

/-- The proof of Lemma 6.5: the three computations of §6.7.1. -/
def B : Prop :=
  ∀ {A B C D : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
    [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
    [FiniteDimensional ℝ D]
    (α : A →ₗ[ℝ] B) (β : B →ₗ[ℝ] C) (γ : C →ₗ[ℝ] D),
    Function.Injective α → LinearMap.range α = LinearMap.ker β →
    LinearMap.range β = LinearMap.ker γ → Function.Surjective γ →
    ∀ (Z : Submodule ℝ B) (V : Submodule ℝ C),
    IsCompl (LinearMap.range α) Z → IsCompl (LinearMap.range β) V →
    ∀ {n l j : ℕ} (a : Fin n → A) (d : Fin l → D) (b' : Fin j → B) (c : Fin l → C),
    LinearIndependent ℝ a → ∀ hn : n = Module.finrank ℝ A,
    LinearIndependent ℝ d → ∀ hl : l = Module.finrank ℝ D,
    (∀ i, b' i ∈ Z) → LinearIndependent ℝ b' → Submodule.span ℝ (Set.range b') = Z →
    (∀ i, c i ∈ V) → (∀ i, γ (c i) = d i) →
    ∀ (hB : n + j = Module.finrank ℝ B) (hC : l + j = Module.finrank ℝ C),
    -- (1) a change of the basis of the complement `Z` by `σ`
    (∀ σ : Matrix (Fin j) (Fin j) ℝ,
      let b'' : Fin j → B := fun i => ∑ k, σ i k • b' k
      wedge (Fin.append (α ∘ a) b'') hB = σ.det • wedge (Fin.append (α ∘ a) b') hB ∧
      wedge (Fin.append c (β ∘ b'')) hC = σ.det • wedge (Fin.append c (β ∘ b')) hC ∧
      (σ.det ≠ 0 →
        wedge (Fin.append (α ∘ a) b'') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c (β ∘ b'')) hC) =
          wedge (Fin.append (α ∘ a) b') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c (β ∘ b')) hC))) ∧
    -- (2) a change of the bases of `A` and `D` by `τ` and `ε`
    (∀ (τ : Matrix (Fin n) (Fin n) ℝ) (ε : Matrix (Fin l) (Fin l) ℝ), τ.det ≠ 0 → ε.det ≠ 0 →
      ∀ c' : Fin l → C, (∀ i, c' i ∈ V) → (∀ i, γ (c' i) = ∑ k, ε i k • d k) →
      let a' : Fin n → A := fun i => ∑ k, τ i k • a k
      let d' : Fin l → D := fun i => ∑ k, ε i k • d k
      (wedge a' hn ⊗ₜ[ℝ] dualVec (wedge d' hl) =
          (τ.det / ε.det) • (wedge a hn ⊗ₜ[ℝ] dualVec (wedge d hl))) ∧
      (wedge (Fin.append (α ∘ a') b') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c' (β ∘ b')) hC) =
          (τ.det / ε.det) •
            (wedge (Fin.append (α ∘ a) b') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c (β ∘ b')) hC))) ∧
      ((wedge a' hn ⊗ₜ[ℝ] dualVec (wedge d' hl) = wedge a hn ⊗ₜ[ℝ] dualVec (wedge d hl)) ↔
          τ.det = ε.det) ∧
      ((wedge (Fin.append (α ∘ a') b') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c' (β ∘ b')) hC) =
          wedge (Fin.append (α ∘ a) b') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c (β ∘ b')) hC)) ↔
          τ.det = ε.det)) ∧
    -- (3) two choices of complements
    (∀ (Z₂ : Submodule ℝ B) (V₂ : Submodule ℝ C),
      IsCompl (LinearMap.range α) Z₂ → IsCompl (LinearMap.range β) V₂ →
      (∃ b₂ : Fin j → B, (∀ i, b₂ i ∈ Z₂) ∧ (∀ i, b₂ i - b' i ∈ LinearMap.range α) ∧
        LinearIndependent ℝ b₂ ∧ Submodule.span ℝ (Set.range b₂) = Z₂) ∧
      (∀ c₂ : Fin l → C, (∀ i, c₂ i ∈ V₂) → (∀ i, γ (c₂ i) = d i) →
        ∀ i, c₂ i - c i ∈ LinearMap.range β) ∧
      (∀ (b₂ : Fin j → B) (c₂ : Fin l → C), (∀ i, b₂ i - b' i ∈ LinearMap.range α) →
        (∀ i, c₂ i - c i ∈ LinearMap.range β) →
        wedge (Fin.append (α ∘ a) b₂) hB = wedge (Fin.append (α ∘ a) b') hB ∧
        wedge (Fin.append c₂ (β ∘ b₂)) hC = wedge (Fin.append c (β ∘ b')) hC))

end RoundTrip.V6_63
