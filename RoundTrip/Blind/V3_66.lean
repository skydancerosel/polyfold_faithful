import Polyfold
/-! Blind formalization of V3_66 (the text's §3.8.5, Lemma 3.81, p. 144). Choices:
- Setting: the standing assumptions of §3.8.5 (Theorem 3.78), exactly as in my blind file V3_65
  (Lemma 3.80), plain Mathlib, no universe choices: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (sup norms),
  `C = [0, ∞)^q ⊕ ℝ^{n−q}` (`quadC n q`, `q ≤ n`), `U` a relatively open neighbourhood of `0` in
  `C`, `f : U → ℝᴺ` of class `C¹` (implied by the text's `C^j`, `j ≥ 1`), `f(0) = 0`, `Df(0) = L`
  onto, `K = ker L` in good position with good complement `Y` (`K ∩ C` with nonempty interior in
  `K`, `ℝⁿ = K ⊕ Y`, and the good-position constant `ε > 0`: `k ∈ C ⟺ k + y ∈ C` for
  `|y| ≤ ε|k|`); `B` is stated for every such `ε`.
- `B(k, y) = y − (D₂f(0))⁻¹ f(k + y)` (`Bmap`, as in V3_65; `D₂f(0) = L|_Y`).
- "`τ : B_K(a) ∩ C → B_Y(b)`" is the map of Lemma 3.80: `τ(k)` is the unique fixed point of
  `B(k, ·)` in `X_k = B̄_Y(ε|k|)`.  I characterize `τ : K → Y` on `D_a = B_K(a) ∩ C` by: `k + X_k ⊆ U`,
  `τ(k) ∈ X_k`, `B(k, τ(k)) = τ(k)`, and every fixed point of `B(k, ·)` in `X_k` equals `τ(k)`.
  Values of `τ` off `D_a` are irrelevant.
- `a, b` are the constants of Lemmas 3.79/3.80 ("replacing `a` by a smaller number"): for all
  `a₀, b₀ > 0` there are `0 < a ≤ a₀`, `0 < b ≤ b₀` with `(B_K(a) ⊕ B_Y(b)) ∩ C ⊆ U` (the region of
  Lemma 3.79, recorded so that `B_Y(b)` has its meaning; the contraction property of Lemma 3.79 is
  that lemma's claim and is not repeated) and `τ(D_a) ⊆ B_Y(b)`.
- Claims: `τ` continuous on `D_a` (`ContinuousOn`), `|τ(k)| ≤ ε|k|/2`, and
  `|τ(k) − τ(k₀)| ≤ ε|k − k₀|` for `k, k₀ ∈ D_a`.
- Nothing in the statement looks false to me (for `a` small, `|τ(k)| ≤ c(a)|k|` with `c(a) → 0`).
-/
namespace RoundTrip.V3_66
open Polyfold

/-- The partial quadrant `C = [0, ∞)^q ⊕ ℝ^{n−q} ⊆ ℝⁿ`. -/
def quadC (n q : ℕ) : Set (Fin n → ℝ) := {x | ∀ i : Fin n, (i : ℕ) < q → 0 ≤ x i}

/-- The kernel of a continuous linear map, as a subspace. -/
def kerCLM {n N : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ))

/-- `(L|_Y)⁻¹ z`: the element of `Y` mapped to `z` by `L` (junk `0` if there is none). -/
noncomputable def invY {n N : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ))
    (Y : Submodule ℝ (Fin n → ℝ)) (z : Fin N → ℝ) : Y := by
  classical
  exact if h : ∃ y : Y, L y = z then h.choose else 0

/-- The map `B(k, y) = y − (D₂f(0))⁻¹ f(k + y)`, `K × Y → Y`, with `D₂f(0) = L|_Y`. -/
noncomputable def Bmap {n N : ℕ} (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ))
    (p : kerCLM L × Y) : Y :=
  p.2 - invY L Y (f ((p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ)))

/-- Lemma 3.81: the fixed-point map `τ : B_K(a) ∩ C → B_Y(b)` of Lemma 3.80 is continuous, with
`|τ(k)| ≤ ε|k|/2` and `|τ(k) − τ(k₀)| ≤ ε|k − k₀|`. -/
def B : Prop :=
  ∀ (n q N : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (ε : ℝ),
    q ≤ n →
    (∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n q) → 0 ∈ U →
    ContDiffOn ℝ 1 f U → f 0 = 0 →
    HasFDerivWithinAt f L U 0 → Function.Surjective L →
    (interior (Subtype.val ⁻¹' quadC n q : Set (kerCLM L))).Nonempty →
    IsCompl (kerCLM L) Y → 0 < ε →
    (∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖v‖ → (v ∈ quadC n q ↔ v + y ∈ quadC n q)) →
    ∀ a₀ b₀ : ℝ, 0 < a₀ → 0 < b₀ →
    ∃ a b : ℝ, 0 < a ∧ a ≤ a₀ ∧ 0 < b ∧ b ≤ b₀ ∧
    ∃ τ : kerCLM L → Y,
      -- the region `(B_K(a) ⊕ B_Y(b)) ∩ C ⊆ U` of Lemma 3.79
      (∀ k : kerCLM L, (k : Fin n → ℝ) ∈ quadC n q → ‖k‖ < a →
        ∀ y : Y, ‖y‖ < b → (k : Fin n → ℝ) + (y : Fin n → ℝ) ∈ quadC n q →
          (k : Fin n → ℝ) + (y : Fin n → ℝ) ∈ U) ∧
      -- `τ(k)` is the unique fixed point of `B(k, ·)` in `X_k`, and `τ(k) ∈ B_Y(b)`
      (∀ k : kerCLM L, (k : Fin n → ℝ) ∈ quadC n q → ‖k‖ < a →
        (∀ y : Y, ‖y‖ ≤ ε * ‖k‖ → (k : Fin n → ℝ) + (y : Fin n → ℝ) ∈ U) ∧
        ‖τ k‖ ≤ ε * ‖k‖ ∧ Bmap f L Y (k, τ k) = τ k ∧
        (∀ y : Y, ‖y‖ ≤ ε * ‖k‖ → Bmap f L Y (k, y) = y → y = τ k) ∧
        ‖τ k‖ < b) ∧
      -- Lemma 3.81
      ContinuousOn τ {k : kerCLM L | (k : Fin n → ℝ) ∈ quadC n q ∧ ‖k‖ < a} ∧
      (∀ k : kerCLM L, (k : Fin n → ℝ) ∈ quadC n q → ‖k‖ < a → ‖τ k‖ ≤ ε * ‖k‖ / 2) ∧
      (∀ k k₀ : kerCLM L, (k : Fin n → ℝ) ∈ quadC n q → ‖k‖ < a →
        (k₀ : Fin n → ℝ) ∈ quadC n q → ‖k₀‖ < a → ‖τ k - τ k₀‖ ≤ ε * ‖k - k₀‖)

end RoundTrip.V3_66
