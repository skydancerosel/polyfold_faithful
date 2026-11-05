import Polyfold
/-! Blind formalization of V4_10 (the text's §4.1, Lemma 4.5, p. 148).

Text: if `t : U → U` is an sc⁺-retraction onto `O`, every sc-smooth retraction `s : V → V` of a
relatively open `V ⊆ C` with `s(V) = O` is an sc⁺-retraction.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`.  `t` and `s` are
  sc-smooth retractions `ScRetraction E C` (Definition 2.1, audited in V2_1: domain relatively
  open in the partial quadrant `C`, sc-smooth, maps the domain into itself, idempotent there), on
  the same partial quadrant `C` of the same `E` (the text's `V ⊆ C`).
- "onto `O`": `t(U) = O`, the project's `ScRetraction.retract` (checked: `toFun '' U`);
  "`s(V) = O`": `s.retract = t.retract`.
- "sc⁺-retraction" (Definition 4.4): the project's `ScRetraction.IsScPlus` (checked with `#print`:
  `r(U) ⊆ E₁` and the lift `U → E¹` is sc-smooth; its agreement with the text's definition is
  item V4_9).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_10
open Polyfold

/-- Lemma 4.5: being an sc⁺-retraction depends only on the retract: if `t` is an sc⁺-retraction
onto `O`, so is every sc-smooth retraction `s` with `s(V) = O`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (t s : ScRetraction E C),
    t.IsScPlus → s.retract = t.retract → s.IsScPlus

end RoundTrip.V4_10
