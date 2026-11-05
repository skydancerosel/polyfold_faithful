import Polyfold
/-! Blind formalization of V1_12 (the text's §1.1, Definition 1.13, p. 10).

Text: the tangent of a tuple `(U, C, E)` is `T(U, C, E) = (TU, TC, TE)` with `TU = U¹ ⊕ E`,
`TC = C¹ ⊕ E`, `TE = E¹ ⊕ E`.  "It is again a tuple: `TU` is relatively open in the partial
quadrant `TC` of the sc-Banach space `TE`."

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by the project's `ScBanach`; the text's spaces
  are real Banach spaces, so nothing is lost).  A tuple `(U, C, E)` is `U, C ⊆ E₀` with
  `IsRelOpenInQuadrant E C U` (checked with `#print`: `C = T₀⁻¹([0,∞)ⁿ ⊕ W₀)` for an
  sc-isomorphism `T : E ≅ ℝⁿ ⊕ W` (`IsPartialQuadrant`), and `U = O ∩ C` with `O ⊆ E₀` open).
- The definition is written out as Lean definitions: `tanSpace E = E¹ ⊕ E` (the project's
  `ScBanach.shift` and `ScBanach.prod`, checked with `#print`: levels `E_{m+1} × E_m`; this is
  literally the project's `E.tangent`), and for `A ⊆ E₀` the set
  `tanSet E A = A¹ ⊕ E = {(x, h) ∈ E₁ × E₀ | x ∈ A}` (`A¹ = A ∩ E₁` with the shifted levels), used
  for `A = U` (`TU`) and `A = C` (`TC`).  `tanSet` is the same set as the project's
  `ScBanach.tangentSet`, but I wrote it out.
- The asserted property ("it is again a tuple") is B: whenever `(U, C, E)` is a tuple, so is
  `(TU, TC, TE)`, i.e. `TC` is a partial quadrant of `TE` and `TU` is relatively open in it (both
  are the fields of `IsRelOpenInQuadrant`).
- Nothing looks false to me.
-/
namespace RoundTrip.V1_12
open Polyfold

/-- The tangent space `TE = E¹ ⊕ E`, with levels `(TE)_m = E_{m+1} × E_m`. -/
noncomputable abbrev tanSpace (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TA = A¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀` for `A ⊆ E₀`: the pairs `(x, h)` with `x ∈ A ∩ E₁`. -/
def tanSet (E : ScBanach) (A : Set (E.lvl 0)) : Set ((tanSpace E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ A}

/-- The tangent `(TU, TC, TE)` of a tuple `(U, C, E)` is again a tuple. -/
def B : Prop :=
  ∀ (E : ScBanach) (C U : Set (E.lvl 0)), IsRelOpenInQuadrant E C U →
    IsRelOpenInQuadrant (tanSpace E) (tanSet E C) (tanSet E U)

end RoundTrip.V1_12
