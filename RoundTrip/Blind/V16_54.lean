import Polyfold
/-! Blind formalization of V16_54 (the text's Part II, §16.3, Theorem 16.3.15, p. 727 of the
Springer 2021 book; 2017: Theorem 16.3).

Text: with reflexive `1`-fibres: (1) a reflexive auxiliary norm exists; (2) every auxiliary norm
`n` has reflexive auxiliary norms `n₁ ≤ n ≤ n₂`.

Choices:
- Setting: `Y Z : Type` (universe `0`, as in the other Chapter 16 items), a strong polyfold
  bundle `c : StrongPolyfoldBundle p` for `p : Y → Z` (Definition 16.3.4).
- "reflexive `1`-fibres": the project's `StrongPolyfoldBundle.HasReflexiveFibers` (Definition
  16.3.12; `#print`ed: some structure of `c̄` has reflexive `1`-fibres).  The only hypothesis.
- "auxiliary norm": `StrongPolyfoldBundle.IsAuxNorm` (Definition 16.3.9; `#print`ed: in every
  structure of `c̄`, `e ↦ n(Γ(|e|))` is an auxiliary norm); "reflexive auxiliary norm":
  `StrongPolyfoldBundle.IsReflexiveAuxNorm` (Definition 16.3.13; `#print`ed: an auxiliary norm
  represented in some structure by a reflexive auxiliary norm, Definition 12.2.10).
- Auxiliary norms are functions `Y → ℝ` of which only the values on `Y_{0,1}` matter (Definition
  16.3.9).  So `n₁ ≤ n ≤ n₂` is read pointwise on `Y_{0,1}` (`StrongPolyfoldBundle.Y01`); the
  values off `Y_{0,1}` are junk and are not compared.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_54
open Polyfold

/-- Theorem 16.3.15: with reflexive `1`-fibres, reflexive auxiliary norms exist, and every
auxiliary norm is squeezed between two reflexive ones on `Y_{0,1}`. -/
def B : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p), c.HasReflexiveFibers →
      (∃ n : Y → ℝ, c.IsReflexiveAuxNorm n) ∧
      (∀ n : Y → ℝ, c.IsAuxNorm n →
        ∃ n₁ n₂ : Y → ℝ, c.IsReflexiveAuxNorm n₁ ∧ c.IsReflexiveAuxNorm n₂ ∧
          ∀ y ∈ c.Y01, n₁ y ≤ n y ∧ n y ≤ n₂ y)

end RoundTrip.V16_54
