import Polyfold
/-! Blind formalization of V1_35 (the text's §1.1, after Definition 1.14, p. 11).

Text: the sc¹-maps between finite-dimensional Banach spaces are the familiar `C¹`-maps.

Choices:
- Setting: the setting of Definition 1.14 with finite-dimensional spaces: `E F : ScBanach` (the
  project's sc-Banach spaces, levels in `Type`) with `E₀`, `F₀` finite-dimensional — by the remark
  after Definition 1.1 (item V1_31) such spaces carry only the constant sc-structure, so this is
  the text's "finite-dimensional Banach spaces" in full generality (it covers
  `ScBanach.const V`).  The domain is as in Definition 1.14: `U` relatively open in a partial
  quadrant `C ⊆ E` (the project's `IsRelOpenInQuadrant E C U`, checked with `#print`: `C` the
  preimage of `[0,∞)ⁿ ⊕ W` under an sc-isomorphism `E → ℝⁿ ⊕ W`, and `U = O ∩ C`, `O` open).
  So boundary points of the quadrant are included (the item's title says "also at the
  boundary").  `f : U → F` is a map `E₀ → F₀` (values off `U` irrelevant on both sides).
- sc¹ is the project's `IsSc1 U f` (`∃ D, IsSc1With U f D`), checked with `#print` against
  Definition 1.14: sc⁰; for `x ∈ U₁`, derivative `Df(x) ∈ L(E₀, F₀)` within `U₁` in the
  `E₁`-topology; tangent map `Tf(x, h) = (f(x), Df(x)h)` sc⁰ on `TU`.
- "the familiar `C¹`-maps" on the relatively open subset `U` of a (finite-dimensional) quadrant:
  Mathlib's `ContDiffOn ℝ 1 f U` (continuously differentiable within `U`, one-sided at boundary
  points; on such `U` it is equivalent to the existence of a continuous `f' : U → L(E₀, F₀)` with
  `f'(x)` the derivative of `f` within `U` at every `x ∈ U`).
- B: for all such `E, F, C, U, f`: `f` is sc¹ iff `f` is `C¹` on `U`.  Nothing looks false.
-/
namespace RoundTrip.V1_35
open Polyfold

/-- Between finite-dimensional spaces, on a relatively open subset of a partial quadrant,
sc¹ is the same as `C¹`. -/
def B : Prop :=
  ∀ (E F : ScBanach), FiniteDimensional ℝ (E.lvl 0) → FiniteDimensional ℝ (F.lvl 0) →
    ∀ (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0), IsRelOpenInQuadrant E C U →
      (IsSc1 U f ↔ ContDiffOn ℝ 1 f U)

end RoundTrip.V1_35
