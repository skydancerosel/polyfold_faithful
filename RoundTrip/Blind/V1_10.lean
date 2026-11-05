import Polyfold
/-! Blind formalization of V1_10 (the text's §1.1, Definition 1.11, p. 10). Choices:
- This item is a definition.  Setting: an sc-Banach space `E : ScBanach` (levels in `Type`);
  subsets of `E` are subsets of `E₀ = E.lvl 0`.
- The text's notions, defined here:
  * `IsPartialQuadrantText E C`: `C ⊆ E₀` is closed and convex, and there are `n : ℕ`, an
    sc-Banach space `W` and an sc-isomorphism `T : E → ℝⁿ ⊕ W` with `T(C) = [0,∞)ⁿ ⊕ W`.  Here
    `ℝⁿ` is `Fin n → ℝ` with its (unique, item V1_1) constant sc-structure `ScBanach.const`,
    `ℝⁿ ⊕ W` is the direct sum `ScBanach.prod` (levels `ℝⁿ × W_m`), "sc-isomorphism" is the
    project's `ScIso` (level-wise continuous linear equivalences compatible with the inclusions;
    item V1_2 states it is the text's notion), `T(C)` is the image under the level-0 map, and
    `[0,∞)ⁿ ⊕ W = {(a, w) | ∀ i, 0 ≤ a i}`.  The text's "closed convex" is kept although it
    follows from the rest.
  * the tuple `(U, C, E)`: `C` a partial quadrant and `U ⊆ C` open in the subspace topology of
    `C ⊆ E₀` (`IsRelOpenText`).
- B states the definition as a characterization of the project's `IsPartialQuadrant` and
  `IsRelOpenInQuadrant` (vocabulary: "the tuple `(U, C, E)` of the text").  The definition asserts
  no further property.
-/
namespace RoundTrip.V1_10
open Polyfold

/-- **Definition 1.11**: `C` is a partial quadrant in `E`. -/
def IsPartialQuadrantText (E : ScBanach) (C : Set (E.lvl 0)) : Prop :=
  IsClosed C ∧ Convex ℝ C ∧
    ∃ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      (T.lvl 0) '' C = {p | ∀ i, 0 ≤ p.1 i}

/-- The tuple `(U, C, E)`: `U` is a relatively open subset of the partial quadrant `C` in `E`. -/
def IsRelOpenText (E : ScBanach) (C U : Set (E.lvl 0)) : Prop :=
  IsPartialQuadrantText E C ∧ U ⊆ C ∧ IsOpen (Subtype.val ⁻¹' U : Set C)

/-- Definition 1.11: the project's partial quadrants and tuples `(U, C, E)` are the text's. -/
def B : Prop :=
  (∀ (E : ScBanach) (C : Set (E.lvl 0)), IsPartialQuadrant E C ↔ IsPartialQuadrantText E C) ∧
  (∀ (E : ScBanach) (C U : Set (E.lvl 0)), IsRelOpenInQuadrant E C U ↔ IsRelOpenText E C U)

end RoundTrip.V1_10
