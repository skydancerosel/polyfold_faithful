import Polyfold
/-! Blind formalization of V2_26 (the text's §2.3, Definition 2.22, p. 31).

Text: for a chart `φ` around `x`, `d(x, φ) = d_C(φ(x))`; `d_X(x)` is the minimum of `d(x, φ)` over
all smooth charts around `x`.

Choices:
- This item is a definition.  Setting: `X : Type` (spaces put in `Type`; the project's
  `MPolyfold` is universe-polymorphic, this is the instance `u = 0`), Hausdorff, paracompact, with
  an M-polyfold structure `P : MPolyfold X` (Definition 2.13, `RoundTrip/Blind/V2_12.lean`).
- A chart `φ` (Definition 2.11) is a project `MChart X` (model `(O, C, E)`, a homeomorphism
  `dom φ → O`; characterized in `RoundTrip/Blind/V2_10.lean`); "around `x`": `x ∈ dom φ`.
  "Smooth charts" = the charts of the M-polyfold structure, i.e. of the maximal atlas of the class:
  the project's `P.IsChart φ` (compatible with every chart of the atlas; see
  `RoundTrip/Blind/V2_12.lean` (c)).
- `d_C` is the degeneracy index of the partial quadrant `C` of the chart's model (Definition 1.23):
  the project's `degIndex E C` (checked with `#print`: the number of vanishing `[0,∞)`-coordinates
  of `T x` for a chosen presentation `T : E ≅ ℝⁿ ⊕ W` of `C`, independent of `T` by Lemma 1.24).
- B: (a) the project's `chartDegIndex φ x` is `d_C(φ(x))`; (b) the project's `P.degIndex x` is the
  minimum (`IsLeast`, which also asserts that the minimum is attained, i.e. that some chart lies
  around `x`, presupposed by "the minimum") of `d_C(φ(x))` over the charts of the structure
  around `x`.
-/
namespace RoundTrip.V2_26
open Polyfold

/-- The text's set `{d(x, φ) | φ a smooth chart around x}`. -/
def chartIndicesB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (x : X) : Set ℕ :=
  {d | ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
    degIndex φ.model.E φ.model.C (φ.toPartialEquiv x) = d}

/-- Definition 2.22: `d(x, φ) = d_C(φ(x))` and `d_X(x) = min_φ d(x, φ)`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X) (x : X),
    (∀ φ : MChart X, x ∈ φ.source →
      MPolyfold.chartDegIndex φ x = degIndex φ.model.E φ.model.C (φ.toPartialEquiv x)) ∧
    IsLeast (chartIndicesB P x) (P.degIndex x)

end RoundTrip.V2_26
