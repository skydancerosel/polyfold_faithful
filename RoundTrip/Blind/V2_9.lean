import Polyfold
/-! Blind formalization of V2_9 (the text's §2.2, Proposition 2.10, p. 23).

Text: (1) an open subset `O'` of a retract `O` is a retract.  (2) If `V ⊆ O` is open and
`s : V → V` is sc-smooth with `s ∘ s = s`, then `s(V)` is a retract.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C O ⊆ E₀` with `(O, C, E)` an
  sc-smooth retract: the project's `IsScRetract E C O` (Definition 2.3; checked with `#print`:
  `O = R.retract = R.toFun '' R.U` for some `R : ScRetraction E C`, and `ScRetraction` is
  Definition 2.1 — see my `RoundTrip/Blind/V2_1.lean`, `RoundTrip/Blind/V2_2.lean`).
- "Open subset of `O`": open in the subspace topology of `O ⊆ E₀`, i.e. `O ∩ W` with `W` open in
  `E₀`.  The conclusions are about the same partial quadrant `C` and space `E`: `(O', C, E)` and
  `(s(V), C, E)` are sc-smooth retracts (the text's retracts are tuples, and no other `C` is
  available).
- (2): `V` is a retract by (1), and "`s : V → V` is sc-smooth" is Definition 2.7 for the retracts
  `(V, C, E) → (V, C, E)`, read existentially (`IsScSmoothRetractMapB`: `s(V) ⊆ V` and `s ∘ ρ`
  sc-smooth for SOME retraction `ρ` onto `V`; the text proves this does not depend on `ρ`).  The
  weakest reading of the hypothesis gives the strongest claim.  `s ∘ s = s` is asserted on `V`; `s`
  is a total map `E₀ → E₀`, only its values on `V` matter.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_9
open Polyfold

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

/-- Proposition 2.10: open subsets of retracts, and images of sc-smooth idempotents on them, are
retracts. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
    -- (1)
    (∀ O' : Set (E.lvl 0), (∃ W : Set (E.lvl 0), IsOpen W ∧ O' = O ∩ W) →
      IsScRetract E C O') ∧
    -- (2)
    (∀ V : Set (E.lvl 0), (∃ W : Set (E.lvl 0), IsOpen W ∧ V = O ∩ W) →
      ∀ s : E.lvl 0 → E.lvl 0, IsScSmoothRetractMapB E C V E V s →
        (∀ x ∈ V, s (s x) = s x) → IsScRetract E C (s '' V))

end RoundTrip.V2_9
