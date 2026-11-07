import Polyfold
/-! Blind formalization of V6_35 (the text's §6.5, pp. 222–223, and the bundles `L̃`,
pp. 224–227).

Text: `L = ⋃_{t ∈ [0,1]} {t} × L_t` and `λ(L) = ⋃_t {t} × λ(L_t)` over `[0, 1]`; an orientation of
one line `λ(L_t)` determines, by continuation, those of all the others, in particular one of
`λ(L_0)` determines one of `λ(L_1)`.  The bundles `L̃` over `[0, 1]²` are used in the same way.

Choices:
- Setting: the claim is about a continuous family of finite-dimensional subspaces `L_q` of a
  fixed real normed space `W` (in the text `L_t ⊆ T_{φ(t)}X × ℝᵏ`, read in a chart as subspaces of
  `E₀ × ℝᵏ`; the continuation argument only uses the family), over the base `Q = [0, 1]`
  (`unitInterval`) and over `Q = [0, 1]²` (`unitInterval × unitInterval`, for the `L̃`).
  `W : Type` (universe 0).  No completeness of `W` is needed for the claim, so none is assumed.
- "continuous family of subspaces" / "`L` a vector bundle over `[0, 1]`": the project's
  `SubspaceFamily Q W` (checked with `#print`: subspaces `L q` of constant finite dimension `n`,
  near every point spanned by a continuous linearly independent frame).  The text's `L` is even
  smooth (Lemma 6.30); continuity is all that the continuation uses, and a smooth family is a
  `SubspaceFamily`, so B (quantifying over all continuous families) covers the text's case.
- `λ(L)`: the line bundle `q ↦ λ(L_q) = Λ.det q` (top exterior power, `maxPow`) with the topology
  of the project's frame trivializations (`SubspaceFamily.prebundle`, the instance found by
  `#synth`).  "An orientation of `λ(L)`": the project's `LineOrientation Λ.det` (checked with
  `#print`: a ray `o q` of every fibre, locally the ray of a continuous nowhere vanishing section).
  "An orientation of one line `λ(L_{q₀})`": a ray `r : Module.Ray ℝ (Λ.det q₀)`.
- "determines, by continuation, those of all the others": for every `q₀` and ray `r` at `q₀` there
  is exactly one orientation `o` of `λ(L)` with `o(q₀) = r` (`∃!`).  The "in particular" (an
  orientation of `λ(L_0)` gives one of `λ(L_1)`) is the case `Q = [0, 1]`, `q₀ = 0`, read off at
  `1`; it is a consequence and not stated separately.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_35
open Polyfold

/-- Continuation over the base `Q`: every orientation of one line `λ(L_{q₀})` of a continuous
family of subspaces extends uniquely to an orientation of the line bundle `λ(L)`. -/
def ContinuationOver (Q : Type) [TopologicalSpace Q] : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (Λ : SubspaceFamily Q W) (q₀ : Q)
    (r : Module.Ray ℝ (Λ.det q₀)), ∃! o : LineOrientation Λ.det, o.1 q₀ = r

/-- An orientation of one line of `λ(L)` determines by continuation a unique orientation of
`λ(L)`, over `[0, 1]` and over `[0, 1]²`. -/
def B : Prop :=
  ContinuationOver unitInterval ∧ ContinuationOver (unitInterval × unitInterval)

end RoundTrip.V6_35
