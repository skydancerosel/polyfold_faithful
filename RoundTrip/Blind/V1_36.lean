import Polyfold
/-! Blind formalization of V1_36 (the text's §1.1, Definitions 1.11 and 1.13, p. 10).

Text: "`T(U, C, E)` is a tuple consisting again of a relatively open subset `TU` in the partial
quadrant `TC` in the sc-Banach space `TE`"; tacitly, `C¹ = C ∩ E₁` is a partial quadrant in `E¹`
and `U¹` is relatively open in it.

Choices:
- Setting: a tuple `(U, C, E)` of Definition 1.11: `E : ScBanach` (the project's, levels in
  `Type`), `C ⊆ E₀` a partial quadrant and `U ⊆ C` relatively open: the project's
  `IsRelOpenInQuadrant E C U`, checked with `#print`: `IsPartialQuadrant E C`
  (`C = (T₀)⁻¹([0,∞)ⁿ ⊕ W)` for an sc-isomorphism `T : E → ℝⁿ ⊕ W`, `ℝⁿ` with its constant
  structure — Definition 1.11's `T(C) = [0,∞)ⁿ ⊕ W`, closedness and convexity being automatic)
  and `U = O ∩ C` with `O` open in `E₀`.
- Definition 1.13's objects, project definitions checked with `#print`:
  `TE = E¹ ⊕ E` is `E.tangent = E.shift.prod E` (levels `E_{m+1} × E_m`);
  `TC = C¹ ⊕ E` and `TU = U¹ ⊕ E` are `E.tangentSet C`, `E.tangentSet U`
  (`{(x, h) ∈ E₁ × E₀ | x ∈ C}` resp. `x ∈ U`); `E¹` is `E.shift` (levels `E_{m+1}`) and
  `C¹ = C ∩ E₁`, `U¹ = U ∩ E₁` are `E.lvlSet C 1`, `E.lvlSet U 1` (preimages in `E₁`).
- B is the conjunction of the quoted claim — `(TU, TC, TE)` is again a tuple: `TC` is a partial
  quadrant in `TE` and `TU` is relatively open in it — and the tacit one — `(U¹, C¹, E¹)` is a
  tuple.  Nothing looks false.
-/
namespace RoundTrip.V1_36
open Polyfold

/-- The tangent `(TU, TC, TE)` and the level shift `(U¹, C¹, E¹)` of a tuple `(U, C, E)` are
tuples. -/
def B : Prop :=
  ∀ (E : ScBanach) (C U : Set (E.lvl 0)), IsRelOpenInQuadrant E C U →
    IsRelOpenInQuadrant E.tangent (E.tangentSet C) (E.tangentSet U) ∧
    IsRelOpenInQuadrant E.shift (E.lvlSet C 1) (E.lvlSet U 1)

end RoundTrip.V1_36
