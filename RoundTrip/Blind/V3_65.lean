import Polyfold
/-! Blind formalization of V3_65 (the text's §3.8.5, Lemma 3.80, p. 143). Choices:
- Setting: the standing assumptions of §3.8.5 (Theorem 3.78, as in the earlier blind file V3_63),
  plain Mathlib, no universe choices.  `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (Mathlib's sup norms; the
  text's norms are not specified and the claims do not depend on them up to the constants);
  `C = [0, ∞)^q ⊕ ℝ^{n−q}` (`quadC n q`, `q ≤ n`; I write `q` since the text's `k` denotes kernel
  elements here); `U` a relatively open neighbourhood of `0` in `C`; `f : U → ℝᴺ` with `f(0) = 0`.
  Only `C¹` is assumed (Lemma 3.82 is the place where "`C^j`" enters; Theorem 3.78 assumes `C^j`,
  `j ≥ 1`, which implies `C¹`, so this is the same hypothesis for this lemma).  `Df(0) = L`
  (derivative within `U`, unique there) is onto, `K = ker L`.
- "`K` in good position with good complement `Y`" (Definition 3.21 in finite dimensions): `K ∩ C`
  has nonempty interior in `K`, `ℝⁿ = K ⊕ Y` (`IsCompl`), and `ε > 0` with
  `k ∈ C ⟺ k + y ∈ C` for `k ∈ K`, `y ∈ Y`, `|y| ≤ ε|k|`.  The text's `ε` in `X_k = B̄_Y(ε|k|)` is
  read as this good-position constant (that is what makes `k + X_k ⊆ C` for `k ∈ K ∩ C`); `B` is
  stated for *every* such `ε`.
- The map `B` of the proof (defined in the text before Lemma 3.79, not quoted): I use the standard
  `B(k, y) = y − (D₂f(0))⁻¹ f(k + y)`, `D₂f(0) = L|_Y : Y → ℝᴺ` (an isomorphism), so that
  `f(k + y) = 0 ⟺ B(k, y) = y` (`Bmap`; `(L|_Y)⁻¹` is `invY`, defined by choice with junk `0`,
  which is never used under the hypotheses).  `B` is a map `K × Y → Y` (product norm = max).
- "`DB`": the derivative of `B` as a map of `(k, y)`, within its domain `{(k, y) | k + y ∈ U}`
  (`fderivWithin`).  "`max_{B((1+ε)a)} |DB|`": the supremum of the operator norms `‖DB(p)‖` over the
  points `p` of the domain with `‖p‖ < (1 + ε)a` (`cConst`; `sSup` is a junk `0` if unbounded, which
  cannot happen for small `a`).
- "Replacing `a` by a smaller number": for every `a₀ > 0` (the `a` of Lemma 3.79) there is
  `0 < a ≤ a₀` such that, for every `k ∈ K ∩ C` with `|k| < a`: every `y ∈ Y` with `|y| ≤ ε|k|`
  has `k + y ∈ U` (so `B(k, y)` is defined), `|B(k, y)| ≤ c(a)|k|` and `|B(k, y)| ≤ ε|k|`
  (so `B(k, ·)` maps `X_k = B̄_Y(ε|k|)` into itself), and `B(k, ·)` has a unique fixed point in
  `X_k` (the text's `τ(k)`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_65
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

/-- The domain `{(k, y) ∈ K × Y | k + y ∈ U}` of `B`. -/
def domB {n N : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ))
    (U : Set (Fin n → ℝ)) : Set (kerCLM L × Y) :=
  {p | (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ U}

/-- `c(a) = (1 + ε) max_{B((1+ε)a)} |DB|`: `(1 + ε)` times the supremum of `‖DB(p)‖` over the
points `p` of the domain of `B` with `‖p‖ < (1 + ε)a`. -/
noncomputable def cConst {n N : ℕ} (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (ε a : ℝ) : ℝ :=
  (1 + ε) * sSup ((fun p => ‖fderivWithin ℝ (Bmap f L Y) (domB L Y U) p‖) ''
    {p | p ∈ domB L Y U ∧ ‖p‖ < (1 + ε) * a})

/-- Lemma 3.80: after shrinking `a`, for `k ∈ B_K(a) ∩ C` and `|y| ≤ ε|k|`: `k + y ∈ U`,
`|B(k, y)| ≤ c(a)|k|` and `|B(k, y)| ≤ ε|k|`, so `B(k, ·)` maps `X_k = B̄_Y(ε|k|)` into itself; and
it has a unique fixed point `τ(k)` in `X_k`. -/
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
    ∀ a₀ : ℝ, 0 < a₀ →
    ∃ a : ℝ, 0 < a ∧ a ≤ a₀ ∧
      ∀ k : kerCLM L, (k : Fin n → ℝ) ∈ quadC n q → ‖k‖ < a →
        (∀ y : Y, ‖y‖ ≤ ε * ‖k‖ →
          (k : Fin n → ℝ) + (y : Fin n → ℝ) ∈ U ∧
          ‖Bmap f L Y (k, y)‖ ≤ cConst f L Y U ε a * ‖k‖ ∧
          ‖Bmap f L Y (k, y)‖ ≤ ε * ‖k‖) ∧
        ∃! t : Y, ‖t‖ ≤ ε * ‖k‖ ∧ Bmap f L Y (k, t) = t

end RoundTrip.V3_65
