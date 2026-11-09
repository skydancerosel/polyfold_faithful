import Polyfold
/-! Blind formalization of V11_6 (the text's Part II, §11.1, Proposition 11.1.6, the part on
`[d]_*`, pp. 524–525 of the Springer 2021 book; 2017: Proposition 11.2, p. 378).

Text: for tame face structured `X`, `Y` and a generalized isomorphism `[d]`: faces are tame face
structured ep-groupoids, two faces meet in a face of each, `[d]` induces a bijection `[d]_*` of
faces and generalized isomorphisms `[d]_F : F → [d]_*F`.

Choices:
- Scope: the item's title restricts it to "the part on `[d]_*`", so B is the claim that `[d]`
  induces a bijection `[d]_*` between the faces of `X` and those of `Y`.  The other claims (faces
  as tame face structured ep-groupoids, intersections of faces, the generalized isomorphisms
  `[d]_F`) are not formalized; they need the faces as ep-groupoids in their own right.
- Setting: `X`, `Y` objects of the project's bundled `EP.{0}` (all spaces in `Type`), `[d]` a
  morphism of the project's `EP(E⁻¹)`; "generalized isomorphism": Mathlib's `IsIso`
  (Definition 10.3.9).
- "tame face structured", faces of `X`: Definition 11.1.3 as rendered in my
  `RoundTrip/Blind/V11_3.lean` (copied: `FaceStructuredB` includes tameness; a face of `X` is
  recorded by its object set `X_θ = {x | |x| ∈ θ}`, `θ` a face of `|X|`).
- `[d]_*`: as in Remark 11.1.5 (my `RoundTrip/Blind/V11_5.lean`), `[d]_* = Ψ_* ∘ Φ^*` for a
  representative `d = X ←Φ A →Ψ Y` (the project's `Diagram`, `d.F = Φ`, `d.Φ = Ψ`), with
  `Φ^*(B) = Φ⁻¹(B)` and `Ψ_*(B) = saturation(Ψ(B))` (`dPushB`).
- B: for every representative, `[d]_*` maps the faces of `X` bijectively onto the faces of `Y`
  (`Set.BijOn`), and on faces it does not depend on the representative ("`[d]` induces").
- Nothing looks false to me.
-/
namespace RoundTrip.V11_6
open Polyfold CategoryTheory
open Polyfold.EPLocalization

universe u v

section
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

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

/-- A face of `X` (by its object set): `X_θ` for a face `θ` of `|X|`. -/
def IsEpFaceB (X : EpGroupoid Obj Mor) (A : Set Obj) : Prop :=
  ∃ θ, IsOrbitFaceB X θ ∧ A = faceObjB X θ

/-- `X` is face structured: tame, and every `z ∈ |X|` lies in exactly `d_{|X|}(z)` faces. -/
def FaceStructuredB (X : EpGroupoid Obj Mor) : Prop :=
  X.PObj.IsTame ∧
    ∀ z : X.OrbitSpace, {θ | IsOrbitFaceB X θ ∧ z ∈ θ}.encard = (degOrbB X z : ℕ∞)

/-- `saturation(Φ(A))`: the objects isomorphic to some `Φ(a)`, `a ∈ A`. -/
def pushObjB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (Φ : EpFunctor X Y)
    (A : Set Obj) : Set Obj' :=
  {y | ∃ a ∈ A, ∃ ψ : Mor', Y.src ψ = Φ.obj a ∧ Y.tgt ψ = y}

end

/-- `[d]_* = Ψ_* ∘ Φ^*` for `d = X ←Φ A →Ψ Y`. -/
def dPushB {X Y : EP.{0}} (d : Diagram X Y) (A : Set X.Obj) : Set Y.Obj :=
  pushObjB d.Φ (d.F.obj ⁻¹' A)

/-- Proposition 11.1.6, the part on `[d]_*`: a generalized isomorphism between tame face
structured ep-groupoids induces a bijection between their faces. -/
def B : Prop :=
  ∀ (X Y : EP.{0}), FaceStructuredB X.X → FaceStructuredB Y.X →
    ∀ f : EPLoc.of X ⟶ EPLoc.of Y, IsIso f →
      (∀ d : Diagram X Y, EPLoc.homMk d = f →
        Set.BijOn (dPushB d) {A | IsEpFaceB X.X A} {A' | IsEpFaceB Y.X A'}) ∧
      (∀ d d' : Diagram X Y, EPLoc.homMk d = f → EPLoc.homMk d' = f →
        ∀ A, IsEpFaceB X.X A → dPushB d A = dPushB d' A)

end RoundTrip.V11_6
