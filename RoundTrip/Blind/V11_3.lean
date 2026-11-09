import Polyfold
/-! Blind formalization of V11_3 (the text's Part II, §11.1, Definition 11.1.3, p. 523 of the
Springer 2021 book; 2017: Definition 11.1, p. 377).

Text: a face of `|X|` is the closure of a connected component of `{d_{|X|} = 1}`; a face of `X`
is the full subcategory `X_θ` over a face `θ`; `X` is face structured if it is tame and every `z`
lies in exactly `d_{|X|}(z)` faces of `|X|`, weakly face structured if the object M-polyfold is
face structured.

Choices:
- This item is a definition.  B says the project's `IsOrbitFace`, `faceObj`/`faceMor`,
  `IsEpFace`, `IsEpFaceStructured`, `IsWeaklyFaceStructured` are my renderings below.
- Setting: `X : EpGroupoid Obj Mor`, `Obj Mor : Type` (universe 0), Hausdorff and paracompact
  (the project's Definition 7.3, `RoundTrip/Blind/V7_3.lean`).
- `|X|`: the project's `X.OrbitSpace` (`#print`ed: the quotient of the objects by "there is a
  morphism `x → y`"), with Mathlib's quotient topology (`#synth`: `instTopologicalSpaceQuotient`).
- `d_{|X|}` (`degOrbB`): `d_{|X|}(z) = d_X(x)` for a representative `x` of `z` (`Quotient.out`),
  `d_X` the degeneracy index of the object M-polyfold (the project's `MPolyfold.degIndex`).  The
  text's `d_{|X|}` is well defined by the invariance of `d_X` along morphisms; the choice of
  representative is mine.  The project's `degIndexOrbit` is not used.
- Face of `|X|`: `θ = closure c` (closure in `|X|`) for a connected component `c` of the subspace
  `{z | d_{|X|}(z) = 1}`, i.e. the image of `connectedComponent s` of the subtype, `s` in it.
- Face of `X`: the full subcategory `X_θ`, objects `{x | |x| ∈ θ}`, morphisms all morphisms between
  such objects; the project records a face of `X` by its object set (`IsEpFace`), so B compares
  object sets for `IsEpFace` and both sets for `faceObj`, `faceMor`.
- Face structured (`FaceStructuredB`): the object M-polyfold is tame (the project's
  `MPolyfold.IsTame`, Part I Definition 2.37; "tame ep-groupoid" is "tame object M-polyfold",
  Definition 7.6) and for every `z ∈ |X|` the set of faces of `|X|` containing `z` has exactly
  `d_{|X|}(z)` elements (`Set.encard`, so infinitely many are not counted as `0`).
- Weakly face structured (`WeaklyFSB`): the object M-polyfold is face structured in Part I's
  sense (Definition 2.5.10 [preprint 2.39], copied from `RoundTrip/Blind/V2_44.lean`: faces the
  closures of components of `{d_X = 1}`, every `x` in exactly `d_X(x)` of them).  Part I defines
  face structured only for tame M-polyfolds, so I include tameness (the text presupposes it).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_3
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `|x| ∈ |X|`, the orbit of `x`. -/
abbrev piB (X : EpGroupoid Obj Mor) (x : Obj) : X.OrbitSpace := Quotient.mk _ x

/-- `d_{|X|}(z) = d_X(x)` for a representative `x` of `z`. -/
noncomputable def degOrbB (X : EpGroupoid Obj Mor) (z : X.OrbitSpace) : ℕ :=
  X.PObj.degIndex z.out

/-- A face of `|X|`: the closure of a connected component of `{z | d_{|X|}(z) = 1}`. -/
def IsOrbitFaceB (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) : Prop :=
  ∃ s : {z : X.OrbitSpace // degOrbB X z = 1},
    θ = closure (Subtype.val '' connectedComponent s)

/-- The objects of the full subcategory `X_θ`: `{x | |x| ∈ θ}`. -/
def faceObjB (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) : Set Obj :=
  {x | piB X x ∈ θ}

/-- The morphisms of the full subcategory `X_θ`: those between objects of `X_θ`. -/
def faceMorB (X : EpGroupoid Obj Mor) (θ : Set X.OrbitSpace) : Set Mor :=
  {φ | piB X (X.src φ) ∈ θ ∧ piB X (X.tgt φ) ∈ θ}

/-- A face of `X` (by its object set): `X_θ` for a face `θ` of `|X|`. -/
def IsEpFaceB (X : EpGroupoid Obj Mor) (A : Set Obj) : Prop :=
  ∃ θ, IsOrbitFaceB X θ ∧ A = faceObjB X θ

/-- `X` is face structured: tame, and every `z ∈ |X|` lies in exactly `d_{|X|}(z)` faces. -/
def FaceStructuredB (X : EpGroupoid Obj Mor) : Prop :=
  X.PObj.IsTame ∧
    ∀ z : X.OrbitSpace, {θ | IsOrbitFaceB X θ ∧ z ∈ θ}.encard = (degOrbB X z : ℕ∞)

/-- A face of an M-polyfold: the closure of a connected component of `{x | d(x) = 1}`. -/
def IsFaceMB (P : MPolyfold Obj) (F : Set Obj) : Prop :=
  ∃ s : {y : Obj // P.degIndex y = 1}, F = closure (Subtype.val '' connectedComponent s)

/-- A face-structured M-polyfold: every `x` lies in exactly `d(x)` faces. -/
def IsFaceStructuredMB (P : MPolyfold Obj) : Prop :=
  ∀ x : Obj, {F : Set Obj | IsFaceMB P F ∧ x ∈ F}.encard = (P.degIndex x : ℕ∞)

/-- `X` is weakly face structured: the (tame) object M-polyfold is face structured. -/
def WeaklyFSB (X : EpGroupoid Obj Mor) : Prop :=
  X.PObj.IsTame ∧ IsFaceStructuredMB X.PObj

end

/-- Definition 11.1.3: the project's faces of `|X|` and of `X`, face structured and weakly face
structured ep-groupoids are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ θ : Set X.OrbitSpace, X.IsOrbitFace θ ↔ IsOrbitFaceB X θ) ∧
    (∀ θ : Set X.OrbitSpace, X.faceObj θ = faceObjB X θ ∧ X.faceMor θ = faceMorB X θ) ∧
    (∀ A : Set Obj, X.IsEpFace A ↔ IsEpFaceB X A) ∧
    (X.IsEpFaceStructured ↔ FaceStructuredB X) ∧
    (X.IsWeaklyFaceStructured ↔ WeaklyFSB X)

end RoundTrip.V11_3
