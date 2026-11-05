import Polyfold
/-! Blind formalization of V2_27 (the text's §2.3, Lemma 2.23, p. 31).

Text: (for an M-polyfold `X`) every `x ∈ X` has an open neighbourhood `U(x)` with
`d_X(y) ≤ d_X(x)` for `y ∈ U(x)`.

Choices:
- Setting: `X : Type` (spaces put in `Type`, universe instance `u = 0`), Hausdorff, paracompact,
  `P : MPolyfold X` (Definition 2.13).
- `d_X` is the project's `P.degIndex` (Definition 2.22; checked with `#print`: `sInf` of
  `d_C(φ(x))` over the charts `φ` of the structure (`P.IsChart`) around `x`; characterized as the
  text's minimum in `RoundTrip/Blind/V2_26.lean`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_27
open Polyfold

/-- Lemma 2.23: `d_X` is upper semicontinuous: `d_X ≤ d_X(x)` near `x`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X) (x : X),
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, P.degIndex y ≤ P.degIndex x

end RoundTrip.V2_27
