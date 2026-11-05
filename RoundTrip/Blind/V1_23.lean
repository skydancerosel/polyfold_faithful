import Polyfold
/-! Blind formalization of V1_23 (the text's §1.3, Theorem 1.25, boundary recognition, p. 14).

Text: given tuples `(U, C, E)` and `(U', C', E')` and a germ `f : (U, x) → (U', x')` of a local
sc-diffeomorphism with `x' = f(x)`, then `d_C(x) = d_{C'}(f(x))`.  (The text cites [20] for the
proof; that remark is not part of the claim.)

Choices:
- Setting: `E E' : ScBanach` (levels in `Type`, forced by `ScBanach`).  A tuple `(U, C, E)` is a
  relatively open subset `U` of a partial quadrant `C ⊆ E` (`IsRelOpenInQuadrant`, checked with
  `#print`).  `x ∈ U`.
- "Germ `f : (U, x) → (U', x')` of a local sc-diffeomorphism": there are open neighbourhoods
  `V = O ∩ U` of `x` in `U` and `V' = O' ∩ U'` in `U'` (`O`, `O'` open), and maps `f : E₀ → E'₀`,
  `g : E'₀ → E₀` with `f(V) ⊆ V'`, `g(V') ⊆ V`, `g ∘ f = id` on `V`, `f ∘ g = id` on `V'`, and `f`,
  `g` sc-smooth on `V`, `V'` (the project's `IsScSmooth`, i.e. `sc^k` for all `k`, checked with
  `#print`).  `x' = f(x)` is then automatically in `V'`.  `V`, `V'` are again relatively open
  subsets of the partial quadrants, so sc-smoothness on them is the text's notion.
- `d_C(x)` (Definition 1.23) is computed with an arbitrary presentation `T : E ≅ ℝⁿ ⊕ W` with
  `T(C) = [0,∞)ⁿ ⊕ W` (`degIndexWith T x`, checked: the number of vanishing `ℝⁿ`-coordinates of
  `T(x)`).  Since the text's `d_C` is presentation-independent (its Lemma 1.24), B states the
  equality for ALL presentations `T` of `C` and `T'` of `C'`; I did not use the project's
  choice-based `degIndex`.
-/
namespace RoundTrip.V1_23
open Polyfold

/-- Local sc-diffeomorphisms between relatively open subsets of partial quadrants preserve the
degeneracy index. -/
def B : Prop :=
  ∀ (E E' : ScBanach) (C U : Set (E.lvl 0)) (C' U' : Set (E'.lvl 0)),
    IsRelOpenInQuadrant E C U → IsRelOpenInQuadrant E' C' U' →
    ∀ (x : E.lvl 0) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0)
      (O : Set (E.lvl 0)) (O' : Set (E'.lvl 0)),
      IsOpen O → IsOpen O' → x ∈ O ∩ U →
      Set.MapsTo f (O ∩ U) (O' ∩ U') → Set.MapsTo g (O' ∩ U') (O ∩ U) →
      Set.LeftInvOn g f (O ∩ U) → Set.RightInvOn g f (O' ∩ U') →
      IsScSmooth (O ∩ U) f → IsScSmooth (O' ∩ U') g →
      ∀ (n n' : ℕ) (W W' : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
        (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')),
        C = T.lvl 0 ⁻¹' quadrant n W 0 → C' = T'.lvl 0 ⁻¹' quadrant n' W' 0 →
          degIndexWith T x = degIndexWith T' (f x)

end RoundTrip.V1_23
