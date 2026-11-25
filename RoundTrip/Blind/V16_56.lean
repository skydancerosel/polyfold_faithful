import Polyfold
/-! Blind formalization of V16_56 (the text's Part II, §16.3, Proposition 16.3.16 (2), p. 728 of
the Springer 2021 book; 2017: Proposition 16.5 (2)).

Text: if `y_k` is mixed convergent to `y`, then `n(y) ≤ liminf n(y_k)`.

Choices:
- Setting: `Y Z : Type` (universe `0`), a strong polyfold bundle `c : StrongPolyfoldBundle p`.
- The quoted item does not repeat the standing hypotheses of Proposition 16.3.16.  I take the
  ones that mixed convergence and the inequality presuppose: `(p, c̄)` has reflexive `1`-fibres
  (`HasReflexiveFibers`, Definition 16.3.12; mixed convergence, Definition 16.3.14, is only
  defined then) and `n` is a reflexive auxiliary norm (`IsReflexiveAuxNorm`, Definition 16.3.13;
  for a mere auxiliary norm the lower semicontinuity is not expected).  If the text's `n` is any
  auxiliary norm, my B is weaker than the text.
- "`y_k` mixed convergent to `y`": the project's `StrongPolyfoldBundle.MixedTendsto` (Definition
  16.3.14; `#print`ed: in some structure of `c̄` with reflexive `1`-fibres and a reflexive
  auxiliary norm the representatives are mixed convergent).  The text takes `y_k, y ∈ Y_{0,1}`;
  I add `y_k ∈ Y_{0,1}`, `y ∈ Y_{0,1}` explicitly (possibly redundant).
- `liminf` is taken in `EReal` (`Filter.liminf … atTop`), so it is meaningful also for unbounded
  sequences (in `ℝ` the `liminf` of an unbounded sequence is a junk value).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_56
open Polyfold Filter

/-- Proposition 16.3.16 (2): a reflexive auxiliary norm is lower semicontinuous along mixed
convergent sequences. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p), c.HasReflexiveFibers →
    ∀ n : Y → ℝ, c.IsReflexiveAuxNorm n →
    ∀ (y : ℕ → Y) (y₀ : Y), (∀ k, y k ∈ c.Y01) → y₀ ∈ c.Y01 → c.MixedTendsto y y₀ →
      ((n y₀ : ℝ) : EReal) ≤ liminf (fun k => ((n (y k) : ℝ) : EReal)) atTop

end RoundTrip.V16_56
