import Polyfold
/-! Blind formalization of V11_7 (the text's Part II, §11.1, Remark 11.1.7, p. 525 of the
Springer 2021 book; 2017: Remark 11.2, p. 379).

Text: if `f : X → Y` is a generalized isomorphism, `X` is tame face structured if and only if
`Y` is.

Choices:
- Setting: `X`, `Y` objects of the project's bundled `EP.{0}` (all spaces in `Type`), `f` a
  morphism of the project's `EP(E⁻¹)`; "generalized isomorphism": Mathlib's `IsIso`
  (Definition 10.3.9: inverse on both sides).
- "tame face structured": Definition 11.1.3 as rendered in my `RoundTrip/Blind/V11_3.lean`
  (copied): `FaceStructuredB X` = the object M-polyfold is tame (the project's
  `MPolyfold.IsTame`) and every `z ∈ |X|` lies in exactly `d_{|X|}(z)` faces of `|X|`.  Since face
  structured includes tame, "tame face structured" is `FaceStructuredB`.
- Literal reading: one equivalence of "tame and face structured".  The invariance of tameness
  alone (suggested by the item's title) is not asserted separately.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_7
open Polyfold CategoryTheory
open Polyfold.EPLocalization

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `d_{|X|}(z) = d_X(x)` for a representative `x` of `z`. -/
noncomputable def degOrbB (X : EpGroupoid Obj Mor) (z : X.OrbitSpace) : ℕ :=
  X.PObj.degIndex z.out

/-- A face of `|X|`: the closure of a connected component of `{z | d_{|X|}(z) = 1}`. -/
def IsOrbitFaceB (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) : Prop :=
  ∃ s : {z : X.OrbitSpace // degOrbB X z = 1},
    θ = closure (Subtype.val '' connectedComponent s)

/-- `X` is face structured: tame, and every `z ∈ |X|` lies in exactly `d_{|X|}(z)` faces. -/
def FaceStructuredB (X : EpGroupoid Obj Mor) : Prop :=
  X.PObj.IsTame ∧
    ∀ z : X.OrbitSpace, {θ | IsOrbitFaceB X θ ∧ z ∈ θ}.encard = (degOrbB X z : ℕ∞)

end

/-- Remark 11.1.7: being tame face structured is invariant under generalized isomorphisms. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), IsIso f →
    (FaceStructuredB X.X ↔ FaceStructuredB Y.X)

end RoundTrip.V11_7
