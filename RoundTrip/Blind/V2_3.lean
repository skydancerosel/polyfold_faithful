import Polyfold
/-! Blind formalization of V2_3 (the text's §2.1, Proposition 2.4, p. 19).

Text: if `r : U → U` and `r' : U' → U'` are sc-smooth retractions on relatively open subsets of
`C` with `r(U) = r'(U') = O`, then `Tr(TU) = Tr'(TU')`.

Choices:
- Setting: an sc-Banach space `E : ScBanach` (levels in `Type`, forced by `ScBanach`) and a
  subset `C ⊆ E₀`.
- "sc-smooth retraction on a relatively open subset of `C`" (Definition 2.1): the project's
  `ScRetraction E C` (checked with `#print`: `U` with `IsRelOpenInQuadrant E C U`, i.e. `C` is a
  partial quadrant and `U = O ∩ C` for an open `O ⊆ E₀`; `r : E₀ → E₀` maps `U` into `U`, is
  sc-smooth on `U` (`IsScSmooth`), and `r ∘ r = r` on `U`).  The map is total; only its values on
  `U` matter.  `r(U)` is `R.retract` (checked: `R.toFun '' R.U`).
- `TU = U¹ ⊕ E` is `E.tangentSet U` (checked: the pairs `(x, h) ∈ E₁ × E₀` with `x ∈ U`), and the
  tangent map `Tr(x, h) = (r(x), Dr(x)h)` is the project's `Polyfold.tangentMap U r` (Definition
  1.14, checked: `(levelMap r 1 x, scDeriv U r x h)`, with the derivative family chosen from the
  definition of sc¹; it is unique at the points of `U₁`, `U₁` being relatively open in the partial
  quadrant `C ∩ E₁` of `E₁`).  `Tr(TU)` is the image of `TU` under it (this is literally the
  project's `ScRetraction.tangent`, which I wrote out).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_3
open Polyfold

/-- Proposition 2.4: two sc-smooth retractions with the same image have the same tangent image. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (r r' : ScRetraction E C),
    r.retract = r'.retract →
      Polyfold.tangentMap r.U r.toFun '' E.tangentSet r.U =
        Polyfold.tangentMap r'.U r'.toFun '' E.tangentSet r'.U

end RoundTrip.V2_3
