import Polyfold
/-! Blind formalization of V4_58 (the text's §3.8, Theorem 3.78, p. 141, in the `C^∞` form used in
§4.3).

Text: Theorem 3.78 (implicit function theorem in partial quadrants) "for `f` of class `C^j`, with a
`C^j` solution"; the item is the `C^∞` form of it.

Choices:
- B is Theorem 3.78 exactly as in the earlier blind file V3_63 (prelude and conclusions copied
  verbatim), except that the smoothness class `j` now ranges over `ℕ∞ = ℕ ∪ {∞}` (`j ≥ 1`) instead
  of `ℕ`: "`f` of class `C^j`" is `ContDiffOn ℝ j f U` and "a `C^j` solution" is
  `ContDiffOn ℝ j τ V`, with `j : ℕ∞` coerced to Mathlib's smoothness exponent
  `WithTop ℕ∞` (so `j = ⊤` is `C^∞`, not analyticity).  The `C^∞` form is the case `j = ∞`; B
  states the theorem for every `j ∈ ℕ ∪ {∞}`, `j ≥ 1` (the text's "of class `C^j`" with the `C^∞`
  case included).  This is the text's generality as I read the item; it contains the case `j = ∞`
  which §4.3 uses.
- Setting (from V3_63): finite dimensions, plain Mathlib.  `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ`
  (Mathlib's sup norms; the claim does not depend on the norms, the constants `ε, σ` being
  existential); `C = [0, ∞)ᵏ ⊕ ℝⁿ⁻ᵏ` is `{x | x i ≥ 0 for i < k}` with `k ≤ n`.  Kernel elements
  are called `v` (the text's `k`).  `U = O ∩ C` with `O` open, `0 ∈ U`; `f(0) = 0`.
- "`Df(0)` onto, `K = ker Df(0)`": for any `L` with `HasFDerivWithinAt f L U 0`, `L` is onto and
  `K = ker L`.
- "`K` in good position with good complement `Y`" (Definition 3.21 in finite dimensions): `K ∩ C`
  has nonempty interior in `K`; `Y` is a complement of `K` with `ε₀ > 0` such that
  `v ∈ C ⟺ v + y ∈ C` for `v ∈ K`, `y ∈ Y`, `|y| ≤ ε₀|v|` (`IsGoodComplementFD`).
- Conclusion (as in V3_63): `V ⊆ K` relatively open in `K ∩ C` with `0 ∈ V`, `τ : K → ℝⁿ` with
  `τ(V) ⊆ Y` and `τ` of class `C^j` on `V`, `ε, σ > 0` with (1) `τ(0) = 0`, `Dτ(0) = 0`,
  `v + τ(v) ∈ U` on `V`; (2) `|τ(v)| ≤ σ` for `v ∈ V`, `|v| ≤ ε`; (3) uniqueness: for `v ∈ V`,
  `y ∈ Y`, `|v| ≤ ε`, `|y| ≤ σ`, `v + y ∈ U`, `f(v + y) = 0` imply `y = τ(v)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_58

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

/-- Theorem 3.78 for every smoothness class `C^j`, `1 ≤ j ≤ ∞`: the solutions of `f = 0` near `0`
are the graph of a `C^j` map `τ : V → Y` over a relatively open `V ⊆ K ∩ C`, with `τ(0) = 0`,
`Dτ(0) = 0`, and uniqueness in `{|v| ≤ ε, |y| ≤ σ}`; in particular the `C^∞` form. -/
def B : Prop :=
  ∀ (n k N : ℕ) (j : ℕ∞) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)),
    k ≤ n → 1 ≤ j →
    (∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n k) → 0 ∈ U →
    ContDiffOn ℝ (j : WithTop ℕ∞) f U → f 0 = 0 →
    HasFDerivWithinAt f L U 0 → Function.Surjective L →
    (interior (Subtype.val ⁻¹' quadC n k : Set (kerCLM L))).Nonempty →
    IsGoodComplementFD (quadC n k) (kerCLM L) Y →
    ∃ (V : Set (kerCLM L))
      (τ : kerCLM L → (Fin n → ℝ)) (ε σ : ℝ),
      (∃ O : Set (kerCLM L),
          IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' quadC n k)) ∧ 0 ∈ V ∧
      (∀ v ∈ V, τ v ∈ Y) ∧ ContDiffOn ℝ (j : WithTop ℕ∞) τ V ∧ 0 < ε ∧ 0 < σ ∧
      -- (1)
      (τ 0 = 0 ∧ HasFDerivWithinAt τ (0 : kerCLM L →L[ℝ] (Fin n → ℝ)) V 0 ∧
        ∀ v ∈ V, (v : Fin n → ℝ) + τ v ∈ U) ∧
      -- (2)
      (∀ v ∈ V, ‖v‖ ≤ ε → ‖τ v‖ ≤ σ) ∧
      -- (3)
      (∀ v ∈ V, ∀ y ∈ Y, ‖v‖ ≤ ε → ‖y‖ ≤ σ → (v : Fin n → ℝ) + y ∈ U →
        f ((v : Fin n → ℝ) + y) = 0 → y = τ v)

end RoundTrip.V4_58
