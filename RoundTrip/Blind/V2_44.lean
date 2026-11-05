import Polyfold
/-! Blind formalization of V2_44 (the text's §2.4, Definition 2.39, p. 43).

Text: a face of a tame M-polyfold is the closure of a connected component of `{d_X = 1}`; `X` is
face-structured if every `x` lies in exactly `d_X(x)` faces.

Choices:
- This item is a definition (no further property asserted), so B says the project's notions
  `MPolyfold.IsFace` and `MPolyfold.IsFaceStructured` agree, on tame M-polyfolds (the text
  defines them only there), with my renderings `IsFaceB`, `IsFaceStructuredB`.
- Setting: `X : Type` (spaces in `Type`; the project's `MPolyfold` is universe-polymorphic, this
  is `u = 0`) with `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]`, `P : MPolyfold X`
  tame: the project's `MPolyfold.IsTame` (Definition 2.37, checked with `#print`; my
  `RoundTrip/Blind/V2_43.lean` states it is the text's notion), used as a hypothesis.
- `d_X` is the project's `MPolyfold.degIndex` (Definition 2.22, checked with `#print`: `sInf` of
  `d_C(φ(x))` over the charts `φ` of the structure around `x`).
- Face: `F = closure c` (closure in `X`) for a connected component `c` of the subspace
  `S = {x | d_X(x) = 1}`: `c` is the image in `X` of `connectedComponent s` in the subtype `↥S`
  for some `s ∈ S` (components of the empty set: none).
- Face-structured: for every `x ∈ X`, the set of faces containing `x` has exactly `d_X(x)`
  elements, counted with `Set.encard` (so infinitely many faces are not counted as `0`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_44
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- A face: the closure of a connected component of `{x | d_X(x) = 1}`. -/
def IsFaceB (P : MPolyfold X) (F : Set X) : Prop :=
  ∃ s : {y : X // P.degIndex y = 1},
    F = closure (Subtype.val '' connectedComponent s)

/-- Face-structured: every `x` lies in exactly `d_X(x)` faces. -/
def IsFaceStructuredB (P : MPolyfold X) : Prop :=
  ∀ x : X, {F : Set X | IsFaceB P F ∧ x ∈ F}.encard = (P.degIndex x : ℕ∞)

end

/-- Definition 2.39: on tame M-polyfolds, the project's faces and face-structured M-polyfolds are
the text's. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame →
      (∀ F : Set X, P.IsFace F ↔ IsFaceB P F) ∧
      (P.IsFaceStructured ↔ IsFaceStructuredB P)

end RoundTrip.V2_44
