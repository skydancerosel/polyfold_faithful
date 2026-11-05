import Polyfold
/-! Blind formalization of V1_22 (the text's §1.3, Lemma 1.24, p. 14).

Text: "The map `d_C` does not depend on the choice of the linear sc-isomorphism `T`."  Here (the
text's Definition 1.23) `C ⊆ E` is a partial quadrant, i.e. `T(C) = [0,∞)ⁿ ⊕ W` for a linear
sc-isomorphism `T : E → ℝⁿ ⊕ W`, and `d_C(x)` for `x ∈ C` is the number of vanishing coordinates
among the first `n` coordinates of `T(x)`.

Choices:
- Setting: `E W W' : ScBanach` (levels in `Type`, forced by `ScBanach`), `n n' : ℕ`, and two
  presentations `T : E ≅ ℝⁿ ⊕ W`, `T' : E ≅ ℝ^{n'} ⊕ W'` (`ScIso`, with `ℝⁿ` the constant
  sc-structure `ScBanach.const (Fin n → ℝ)`) of the same `C ⊆ E₀`.  The two presentations may
  have different `n` and different `W` — the text puts no restriction on them.
- `T(C) = [0,∞)ⁿ ⊕ W` is written `C = T₀⁻¹([0,∞)ⁿ ⊕ W₀)` (`quadrant n W 0`, checked with
  `#print`: the points whose `ℝⁿ`-coordinates are `≥ 0`); equivalent since `T₀` is bijective.
- `d_C(x)` computed with `T` is the project's `degIndexWith T x` (checked with `#print`: the
  cardinality of `{i | (T₀ x)_i = 0}`).
- "does not depend on `T`": for every `x ∈ C` the two counts agree.  (Outside `C` the text does
  not define `d_C`, so B only quantifies over `x ∈ C`.)
-/
namespace RoundTrip.V1_22
open Polyfold

/-- The degeneracy index of a point of a partial quadrant does not depend on the presentation. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (n n' : ℕ) (W W' : ScBanach)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W')),
    C = T.lvl 0 ⁻¹' quadrant n W 0 → C = T'.lvl 0 ⁻¹' quadrant n' W' 0 →
      ∀ x ∈ C, degIndexWith T x = degIndexWith T' x

end RoundTrip.V1_22
