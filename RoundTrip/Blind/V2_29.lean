import Polyfold
/-! Blind formalization of V2_29 (the text's §2.3, Definition 2.25, p. 31).

Text: `∂X = {x : d_X(x) ≥ 1}` is the boundary (of the M-polyfold `X`); `X` is without boundary if
`d_X ≡ 0`.

Choices:
- This item is a definition; it asserts no further property.  Setting: `X : Type` (spaces put in
  `Type`, universe instance `u = 0`), Hausdorff, paracompact, `P : MPolyfold X`.
- `d_X` is the project's `P.degIndex` (Definition 2.22, checked with `#print`; characterized in
  `RoundTrip/Blind/V2_26.lean`).
- B characterizes the project's `P.boundary` and `P.IsWithoutBoundary` as the text's notions.
-/
namespace RoundTrip.V2_29
open Polyfold

/-- Definition 2.25: the project's boundary and "without boundary" are the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.boundary = {x | 1 ≤ P.degIndex x} ∧
    (P.IsWithoutBoundary ↔ ∀ x : X, P.degIndex x = 0)

end RoundTrip.V2_29
