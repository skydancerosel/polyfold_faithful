import Polyfold
/-! Blind formalization of V2_7 (the text's §2.1, Theorem 2.8, the chain rule for retracts,
p. 21).

Text: if `f : O → O'` and `g : O' → O''` are sc-smooth maps between sc-smooth retracts
`(O, C, E)`, `(O', C', E')`, `(O'', C'', E'')`, then `g ∘ f` is sc-smooth and
`T(g ∘ f) = Tg ∘ Tf`.

Choices:
- Setting: `E E' E'' : ScBanach` (levels in `Type`, forced by `ScBanach`).
- Misprint: the text writes `(O'', C', E'')` for the third retract; read literally this is
  ill-typed (`C' ⊆ E'`, not `E''`), so I use `(O'', C'', E'')`.
- sc-smooth retraction / retract (Definitions 2.1, 2.3): the project's `ScRetraction E C`
  (checked with `#print`: `U` relatively open in the partial quadrant `C`, `r : U → U`
  sc-smooth with `r ∘ r = r` on `U`) and `IsScRetract E C O` (`O = r(U)` for some such `r`).
- sc-smooth map between retracts (Definition 2.7): `f(O) ⊆ O'` and `f ∘ r : U → E'` is sc-smooth
  (`IsScSmooth`) for an sc-smooth retraction `r : U → U` onto `O`.  The text's notion does not
  depend on `r`; to avoid assuming more than the text, the HYPOTHESES on `f`, `g` only ask this
  for SOME retraction (`IsScSmoothB`), while the CONCLUSION on `g ∘ f` asserts it for EVERY
  retraction onto `O` (plus `(g ∘ f)(O) ⊆ O''`).  I did not use the project's
  `IsScSmoothRetractMap` (which asks it for every retraction).
- Tangent maps (Definitions 2.5, 2.7): `TO = Tr(TU)` (the project's `ScRetraction.tangent`,
  checked: the image of `TU` under `tangentMap U r`), and `Tf = T(f ∘ r)` restricted to `TO`,
  with `T(·)` the project's `tangentMap` of Definition 1.14 (chosen derivative family; canonical on
  `TU`, see `RoundTrip/Blind/V1_20.lean`).  Since the text's `Tf` does not depend on `r`,
  `T(g ∘ f) = Tg ∘ Tf` is asserted on `TO` for EVERY retraction `r` onto `O` (used for `Tf` and
  `T(g ∘ f)`) and EVERY retraction `r'` onto `O'` (used for `Tg`).
-/
namespace RoundTrip.V2_7
open Polyfold

/-- `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and `(O', C', E')`: `f(O) ⊆ O'`
and `f ∘ r` is sc-smooth for some sc-smooth retraction `r : U → U` onto `O`. -/
def IsScSmoothB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach) (O' : Set (E'.lvl 0))
    (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

/-- The chain rule for sc-smooth maps between sc-smooth retracts. -/
def B : Prop :=
  ∀ (E E' E'' : ScBanach) (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0))
    (C'' O'' : Set (E''.lvl 0)) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E''.lvl 0),
    IsScRetract E C O → IsScRetract E' C' O' → IsScRetract E'' C'' O'' →
    IsScSmoothB E C O E' O' f → IsScSmoothB E' C' O' E'' O'' g →
      -- `g ∘ f` is sc-smooth
      (Set.MapsTo (g ∘ f) O O'' ∧
        ∀ R : ScRetraction E C, R.retract = O → IsScSmooth R.U ((g ∘ f) ∘ R.toFun)) ∧
      -- `T(g ∘ f) = Tg ∘ Tf` on `TO`
      (∀ R : ScRetraction E C, R.retract = O → ∀ R' : ScRetraction E' C', R'.retract = O' →
        ∀ p ∈ R.tangent,
          tangentMap R.U ((g ∘ f) ∘ R.toFun) p =
            tangentMap R'.U (g ∘ R'.toFun) (tangentMap R.U (f ∘ R.toFun) p))

end RoundTrip.V2_7
