import Polyfold
/-! Blind formalization of V2_38 (the text's §2.3, Corollary 2.32, p. 37).

Text: for a partial quadrant `C`, viewed as the M-polyfold `X_C`, `d_C = d_{X_C}`.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀` a partial quadrant
  (`IsPartialQuadrant`, Definition 1.11, checked with `#print`: `C = T⁻¹([0,∞)ⁿ ⊕ W)` for an
  sc-isomorphism `T`).
- `X_C`: `C` (the subtype `↥C` with the subspace topology) as an M-polyfold with the single chart
  `id : C → C` and model `(C, C, E)` (`C` is relatively open in itself, `r = id`).  This is the
  project's `IsRelOpenInQuadrant.toMPolyfold` for `U = C` (checked with `#print`:
  `(LocalModel.ofRelOpen hC).toMPolyfold`, the M-polyfold on `↥C` whose atlas is the single
  identity chart with model `(C, C, E)`), whose docstring calls it "the text's `X_C`".  It needs
  a proof `hC` that `C` is relatively open in the partial quadrant `C` (checked:
  `IsPartialQuadrant E C ∧ ∃ open V, C = V ∩ C`) and of nonemptiness.  So that B is not vacuous,
  B asserts that such an `hC` EXISTS for every partial quadrant (true: `V = E₀`), and then the
  equality for every nonemptiness proof (`0 ∈ C`).
- `d_{X_C}` is the project's `MPolyfold.degIndex` (Definition 2.22, checked: `sInf` of
  `d_{C'}(φ(x))` over all charts `φ` compatible with the atlas, around `x`), and `d_C` the
  project's `degIndex E C` (Definition 1.23, checked: number of vanishing half-line coordinates
  for a chosen presentation).  The equality is asserted at every `x ∈ C`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_38
open Polyfold

/-- Corollary 2.32: the degeneracy index of the M-polyfold `X_C` is `d_C`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)), IsPartialQuadrant E C →
    ∃ hC : IsRelOpenInQuadrant E C C,
      ∀ (hne : C.Nonempty) (x : ↥C), (hC.toMPolyfold hne).degIndex x = degIndex E C x

end RoundTrip.V2_38
