import Polyfold
/-! Blind formalization of V16_57 (the text's Part II, §16.3, Theorem 16.3.17 (1), p. 728 of the
Springer 2021 book; 2017: Theorem 16.4 (1)).

Text: over a tame polyfold, an auxiliary norm `n` of `Y_{0,1}|∂Z` extends to an auxiliary norm
of `p`.

Choices:
- Setting: `Y Z : Type` (universe `0`), a strong polyfold bundle `c : StrongPolyfoldBundle p`.
- "over a tame polyfold": the polyfold `(Z, c)` of the bundle is tame, `c.polyfold.IsTame`
  (Definition 16.1.20; equivalently `c.IsTame`, Definition 16.3.5 (1)).  No other hypothesis
  (no partitions of unity, no reflexivity).
- "auxiliary norm of `Y_{0,1}|∂Z`": the project's `StrongPolyfoldBundle.IsAuxNormBoundary`
  (`#print`ed: in every structure `((P, μ), Γ, γ)` of `c̄`, `e ↦ n(Γ(|e|))` is an auxiliary norm
  over `∂X`, `IsAuxNormOn`, the form of Theorem 12.2.7); `n` is a function `Y → ℝ` whose values
  off `p⁻¹(∂Z) ∩ Y_{0,1}` are irrelevant.  `∂Z = c.polyfold.boundary` (Definition 16.1.17).
- "auxiliary norm of `p`": `StrongPolyfoldBundle.IsAuxNorm` (Definition 16.3.9).
- "extends": `n' y = n y` for every `y ∈ Y_{0,1}` with `p y ∈ ∂Z`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_57
open Polyfold

/-- Theorem 16.3.17 (1): over a tame polyfold an auxiliary norm of `Y_{0,1}|∂Z` extends to an
auxiliary norm of `p`. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p), c.polyfold.IsTame →
    ∀ n : Y → ℝ, c.IsAuxNormBoundary n →
      ∃ n' : Y → ℝ, c.IsAuxNorm n' ∧
        ∀ y ∈ c.Y01, p y ∈ c.polyfold.boundary → n' y = n y

end RoundTrip.V16_57
