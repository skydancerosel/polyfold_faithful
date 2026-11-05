import Polyfold
/-! Blind formalization of V2_2 (the text's §2.1, Definition 2.3, p. 18).

Text: a tuple `(O, C, E)` is an *sc-smooth retract* if `O = r(U)` for an sc-smooth retraction
`r : U → U` on a relatively open subset `U` of the partial quadrant `C`.

Choices:
- This item is a definition; it asserts no further property.  Setting: `E : ScBanach` (levels in
  `Type`, forced by `ScBanach`), `C O ⊆ E₀`.
- Prelude: `IsScRetractionB` is Definition 2.1 as in my `RoundTrip/Blind/V2_1.lean`
  (`IsRelOpenInQuadrant E C U` (checked with `#print`: `C` a partial quadrant, `U = W ∩ C`, `W`
  open), `r(U) ⊆ U`, `IsScSmooth U r`, `r ∘ r = r` on `U`; `r : E₀ → E₀` total, only its values on
  `U` matter).  `IsScRetractB E C O`: there are such `U`, `r` with `O = r(U)`.
- B characterizes the project's predicate `IsScRetract E C O` by my definition, and asserts that
  every project `LocalModel` (a structure with fields `E`, `C`, `O` and a proof of
  `IsScRetract E C O`, checked with `#print`; its docstring calls it the tuple `(O, C, E)`) is an
  sc-smooth retract in my sense.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_2
open Polyfold

/-- **Definition 2.1**: `r : U → U` is an sc-smooth retraction on the relatively open subset `U`
of the partial quadrant `C ⊆ E`. -/
def IsScRetractionB (E : ScBanach) (C U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0) : Prop :=
  IsRelOpenInQuadrant E C U ∧ Set.MapsTo r U U ∧ IsScSmooth U r ∧ ∀ x ∈ U, r (r x) = r x

/-- **Definition 2.3**: `(O, C, E)` is an sc-smooth retract: `O = r(U)` for an sc-smooth
retraction `r : U → U` on a relatively open subset `U` of `C`. -/
def IsScRetractB (E : ScBanach) (C O : Set (E.lvl 0)) : Prop :=
  ∃ (U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0), IsScRetractionB E C U r ∧ O = r '' U

/-- Definition 2.3: the project's sc-smooth retracts (and local models) are the text's. -/
def B : Prop :=
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O ↔ IsScRetractB E C O) ∧
  (∀ M : LocalModel, IsScRetractB M.E M.C M.O)

end RoundTrip.V2_2
