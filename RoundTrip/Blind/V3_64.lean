import Polyfold
/-! Blind formalization of V3_64 (the text's §3.8.5, Lemma 3.79, p. 142). `B` is the conjunction of
the claims.  Choices:
- Setting: the proof of Theorem 3.78, with the hypotheses of Theorem 3.78 taken over unchanged
  from the earlier blind file V3_63 (prelude reused): `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (Mathlib's
  sup norms; the claim holds for any norms, `a, b` being existential), `C = [0, ∞)ᵏ ⊕ ℝⁿ⁻ᵏ`
  (`quadC n k`, `k ≤ n`), `U = O ∩ C` a relatively open neighbourhood of `0` in `C`, `f : U → ℝᴺ`
  of class `C^j` (`j ≥ 1`), `f(0) = 0`, `L = Df(0)` (derivative within `U`) onto, `K = ker L` with
  `K ∩ C` of nonempty interior in `K` and `Y` a good complement of `K` (`IsGoodComplementFD`:
  `ℝⁿ = K ⊕ Y` and `v ∈ C ⟺ v + y ∈ C` for `|y| ≤ ε₀|v|`).  No universe choices arise.  As in
  V3_63, kernel elements are called `v` (the text's `k`), to avoid a clash with `k` in `quadC n k`.
- The map `B` is not defined in the quote; I take the text's `B(k, y) = y − [Df(0)|_Y]⁻¹ f(k + y)`
  (the map whose fixed points in `y` are the zeros of `f(k, ·) = f(k + ·)`; the text writes
  `f(k, y)` for `f(k + y)` via `ℝⁿ = K ⊕ Y`).  `[Df(0)|_Y]⁻¹ : ℝᴺ → Y ⊆ ℝⁿ` is given as any
  continuous linear `Linv` with values in `Y` and `L ∘ Linv = 1` (it is unique, since
  `L|_Y : Y → ℝᴺ` is bijective).  The consequence "`f(k, y) = f(k, y')` forces `y = y'`" does not
  depend on this reading of `B`.
- "`(B_K(a) ⊕ B_Y(b)) ∩ C ⊆ U`": every `k + y` with `k ∈ K`, `|k| < a`, `y ∈ Y`, `|y| < b` and
  `k + y ∈ C` lies in `U` (open balls).
- "`B(k, ·)` is a `½`-contraction on `(B_K(a) ⊕ B_Y(b)) ∩ C`": for `k ∈ K`, `|k| < a`, and
  `y, y' ∈ Y` with `|y|, |y'| < b` and `k + y, k + y' ∈ C`: `|B(k, y) − B(k, y')| ≤ ½|y − y'|`
  (a Lipschitz bound; that `B(k, ·)` maps the ball into itself is not claimed).  For the same
  points, `f(k + y) = f(k + y')` implies `y = y'`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_64

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

/-- Lemma 3.79: in the setting of Theorem 3.78 there are `a, b > 0` with
`(B_K(a) ⊕ B_Y(b)) ∩ C ⊆ U` such that `B(k, ·) = · − [Df(0)|_Y]⁻¹ f(k + ·)` is a `½`-contraction
there; hence `f(k + y) = f(k + y')` forces `y = y'`. -/
def B : Prop :=
  ∀ (n k N j : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)),
    k ≤ n → 1 ≤ j →
    (∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n k) → 0 ∈ U →
    ContDiffOn ℝ j f U → f 0 = 0 →
    HasFDerivWithinAt f L U 0 → Function.Surjective L →
    (interior (Subtype.val ⁻¹' quadC n k : Set (kerCLM L))).Nonempty →
    IsGoodComplementFD (quadC n k) (kerCLM L) Y →
    ∀ Linv : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ), (∀ z, Linv z ∈ Y) → (∀ z, L (Linv z) = z) →
      ∃ a > (0 : ℝ), ∃ b > (0 : ℝ),
        (∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖v‖ < a → ‖y‖ < b → v + y ∈ quadC n k → v + y ∈ U) ∧
        ∀ v ∈ kerCLM L, ‖v‖ < a → ∀ y ∈ Y, ∀ y' ∈ Y, ‖y‖ < b → ‖y'‖ < b →
          v + y ∈ quadC n k → v + y' ∈ quadC n k →
            ‖(y - Linv (f (v + y))) - (y' - Linv (f (v + y')))‖ ≤ 1 / 2 * ‖y - y'‖ ∧
            (f (v + y) = f (v + y') → y = y')

end RoundTrip.V3_64
