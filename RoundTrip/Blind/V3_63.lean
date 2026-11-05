import Polyfold
/-! Blind formalization of V3_63 (the text's §3.8.5, Theorem 3.78, p. 141). Choices:
- Setting: finite dimensions only, plain Mathlib.  `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (Mathlib's
  sup norms; the claim is insensitive to the choice of norms, the constants `ε, σ` being
  existential), and `C = [0, ∞)ᵏ ⊕ ℝⁿ⁻ᵏ` is `{x | x i ≥ 0 for the first k coordinates i < k}`
  with `k ≤ n` (presupposed by `ℝ^{n−k}`).  To avoid a clash I call the kernel elements `v`
  (the text's `k ∈ K`).  No universe choices arise.
- `U` a relatively open neighbourhood of `0` in `C`: `U = O ∩ C` with `O` open, `0 ∈ U`.
- "`f : U → ℝᴺ` of class `C^j`": `ContDiffOn ℝ j f U`.  `j ≥ 1` is added: it is presupposed by
  "`Df(0)` onto" (the text's `C^j`, `j ≥ 1`).  `f(0) = 0`.
- "`Df(0)` onto, `K = ker Df(0)`": for *any* `L` with `HasFDerivWithinAt f L U 0` (unique, as `U`
  is a neighbourhood of `0` in the convex set `C` with nonempty interior), `L` is surjective and
  `K = ker L`.
- "`K` in good position with good complement `Y`" (Definition 3.21, finite-dimensional case):
  `K ∩ C` has nonempty interior in `K`; `Y` is a complement of `K` (`IsCompl K Y`; in finite
  dimensions every complement is an sc-complement) with `ε₀ > 0` such that `v ∈ C ⟺ v + y ∈ C`
  whenever `v ∈ K`, `y ∈ Y`, `|y| ≤ ε₀|v|` (`IsGoodComplementFD`, defined here).  `Y` is given.
- Conclusion: `V ⊆ K` relatively open in `K ∩ C` ("open in `K ∩ C`") containing `0`, and
  `τ : K → ℝⁿ` with `τ(V) ⊆ Y`, `C^j` on `V`; `ε, σ > 0` with
  (1) `τ(0) = 0`, `Dτ(0) = 0` (derivative within `V`), `v + τ(v) ∈ U` for `v ∈ V`;
  (2) `|τ(v)| ≤ σ` for `v ∈ V` with `|v| ≤ ε`;
  (3) for `v ∈ V`, `y ∈ Y` with `|v| ≤ ε`, `|y| ≤ σ`, `v + y ∈ U` and `f(v + y) = 0`: `y = τ(v)`.
  In (2), (3) the text's `k` ranges over the domain `V` of `τ` (for `y = τ(k)` to make sense), and
  `y` over `Y`; `v + y ∈ U` is presupposed by `f(v + y)`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_63

/-- The partial quadrant `C = [0, ∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊆ ℝⁿ`. -/
def quadC (n k : ℕ) : Set (Fin n → ℝ) := {x | ∀ i : Fin n, (i : ℕ) < k → 0 ≤ x i}

/-- Definition 3.21 in finite dimensions: `Y` is a good complement of `K` with respect to `C`. -/
def IsGoodComplementFD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (C : Set V)
    (K Y : Submodule ℝ V) : Prop :=
  IsCompl K Y ∧ ∃ ε₀ > 0, ∀ v ∈ K, ∀ y ∈ Y, ‖y‖ ≤ ε₀ * ‖v‖ → (v ∈ C ↔ v + y ∈ C)

/-- The kernel of a continuous linear map, as a subspace. -/
def kerCLM {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] (L : V →L[ℝ] V') : Submodule ℝ V :=
  LinearMap.ker (L : V →ₗ[ℝ] V')

/-- Theorem 3.78 (implicit function theorem in partial quadrants): the solutions of `f = 0` near
`0` are the graph of a `C^j` map `τ : V → Y` over a relatively open `V ⊆ K ∩ C`, with
`τ(0) = 0`, `Dτ(0) = 0`, and uniqueness in `{|v| ≤ ε, |y| ≤ σ}`. -/
def B : Prop :=
  ∀ (n k N j : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)),
    k ≤ n → 1 ≤ j →
    (∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n k) → 0 ∈ U →
    ContDiffOn ℝ j f U → f 0 = 0 →
    HasFDerivWithinAt f L U 0 → Function.Surjective L →
    (interior (Subtype.val ⁻¹' quadC n k : Set (kerCLM L))).Nonempty →
    IsGoodComplementFD (quadC n k) (kerCLM L) Y →
    ∃ (V : Set (kerCLM L))
      (τ : kerCLM L → (Fin n → ℝ)) (ε σ : ℝ),
      (∃ O : Set (kerCLM L),
          IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' quadC n k)) ∧ 0 ∈ V ∧
      (∀ v ∈ V, τ v ∈ Y) ∧ ContDiffOn ℝ j τ V ∧ 0 < ε ∧ 0 < σ ∧
      -- (1)
      (τ 0 = 0 ∧ HasFDerivWithinAt τ (0 : kerCLM L →L[ℝ] (Fin n → ℝ)) V 0 ∧
        ∀ v ∈ V, (v : Fin n → ℝ) + τ v ∈ U) ∧
      -- (2)
      (∀ v ∈ V, ‖v‖ ≤ ε → ‖τ v‖ ≤ σ) ∧
      -- (3)
      (∀ v ∈ V, ∀ y ∈ Y, ‖v‖ ≤ ε → ‖y‖ ≤ σ → (v : Fin n → ℝ) + y ∈ U →
        f ((v : Fin n → ℝ) + y) = 0 → y = τ v)

end RoundTrip.V3_63
