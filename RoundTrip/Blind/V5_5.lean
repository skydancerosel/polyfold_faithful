import Polyfold
/-! Blind formalization of V5_5 (the text's §5.1, Proposition 5.3, p. 171, existence part).

Text: every strong bundle has an auxiliary norm ("a partition of unity argument using the
paracompactness of `X`, pulling back by strong bundle maps the standard norm `|·|₁`").

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X` (`X` paracompact Hausdorff, as
  for every M-polyfold), `P : Y → X` with the fibrewise linear structure as instances on the
  fibres, `Bd : StrongBundle PX P` (Definition 2.51), as in `RoundTrip/Blind/V5_10.lean`.  "Every
  strong bundle": no further hypothesis (no tameness).
- "auxiliary norm": the project's `Bd.IsAuxNorm N`, `N : Y_{0,1} → ℝ` (`Bd.One`) (Definition 5.1,
  checked with `#print`: continuous, a complete norm on every fibre `(Y_{0,1})_x`, and
  `P(w_k) → x`, `N(w_k) → 0` imply `w_k → 0_x` in `Y_{0,1}`); compared with the text in
  `RoundTrip/Blind/V5_3.lean`.
- The parenthetical describes the proof; it is not part of the claim.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_5
open Polyfold

/-- Proposition 5.3 (existence): every strong bundle admits an auxiliary norm. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P),
    ∃ N : Bd.One → ℝ, Bd.IsAuxNorm N

end RoundTrip.V5_5
