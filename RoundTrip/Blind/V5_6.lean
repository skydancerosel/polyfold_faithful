import Polyfold
/-! Blind formalization of V5_6 (the text's §5.1, Proposition 5.3, p. 171, comparison part).

Text: for auxiliary norms `N₀`, `N₁` there is a continuous `f : X → (0, ∞)` with
`f(x)N₀(h) ≤ N₁(h) ≤ f(x)⁻¹N₀(h)` on `P⁻¹(x) ⊆ Y_{0,1}`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P` (Definition
  2.51), as in `RoundTrip/Blind/V5_10.lean`.  No further hypothesis.
- "auxiliary norm": the project's `Bd.IsAuxNorm`, on `Y_{0,1}` = `Bd.One` (Definition 5.1, checked
  with `#print`; compared with the text in `RoundTrip/Blind/V5_3.lean`).
- "continuous `f : X → (0, ∞)`": `f : X → ℝ` continuous (topology of `X = X₀`) with `f(x) > 0`
  for all `x`.
- "on `P⁻¹(x) ⊆ Y_{0,1}`": for every `x` and every `h ∈ Y_{0,1}` with `P(h) = x`, i.e. for every
  `h : Bd.One`, with `x = P(h)`.  `f(x)⁻¹N₀(h)` is `(f x)⁻¹ * N₀ h`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_6
open Polyfold

/-- Proposition 5.3 (comparison): any two auxiliary norms are equivalent on each fibre with a
constant depending continuously on the base point. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N₀ N₁ : Bd.One → ℝ),
    Bd.IsAuxNorm N₀ → Bd.IsAuxNorm N₁ →
      ∃ f : X → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧
        ∀ h : Bd.One,
          f (P (Bd.oneVal h)) * N₀ h ≤ N₁ h ∧ N₁ h ≤ (f (P (Bd.oneVal h)))⁻¹ * N₀ h

end RoundTrip.V5_6
