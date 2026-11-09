import Polyfold
/-! Blind formalization of V11_8 (the text's Part II, §11.1, Proposition 11.1.8, p. 526 of the
Springer 2021 book; 2017: Proposition 11.3, p. 380).

Text: if `f, g : X → Y` are generalized isomorphisms of tame face structured ep-groupoids with
`|f| = |g|`, then `f_* = g_*` and the induced maps `|F| → |f_*F|` agree.

Choices:
- Setting: `X`, `Y` objects of the project's bundled `EP.{0}` (all spaces in `Type`); `f`, `g`
  morphisms of the project's `EP(E⁻¹)`; "generalized isomorphism": Mathlib's `IsIso`.
- `|f|`: the project's `EPLoc.orbitMap f` (`#print`ed: `|Ψ| ∘ |Φ|⁻¹` on a representative,
  Definition 10.3.7); `|f| = |g|` is equality of functions `|X| → |Y|`.
- "tame face structured", faces: Definition 11.1.3 as rendered in my
  `RoundTrip/Blind/V11_3.lean` (copied; a face `F = X_θ` of `X` is recorded by its object set).
- `f_*` on faces of `X`: `[d]_* = Ψ_* ∘ Φ^*` for a representative `d = X ←Φ A →Ψ Y` (Remark
  11.1.5, my `RoundTrip/Blind/V11_5.lean`, `dPushB`); "`f_* = g_*`": for all representatives `d`
  of `f` and `e` of `g`, `[d]_*` and `[e]_*` agree on every face of `X`.
- "the induced maps `|F| → |f_*F|`": faces are not available as ep-groupoids, so I read `|F|` for
  `F = X_θ` as `θ ⊆ |X|` (the orbit space of the full saturated subcategory `X_θ`), `|f_*F|` as
  `|f|(θ)`, and the map induced by `f` (the orbit map of the text's `f_F`) as the restriction of
  `|f|` to `θ`.  B states that `|f|`, `|g|` map `θ` into `|f|(θ)`, `|g|(θ)` and agree on `θ`.
  Under this reading the second claim is immediate from `|f| = |g|`; the text's `f_F`, `g_F`
  (generalized isomorphisms of faces, Proposition 11.1.6) are not formalized.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_8
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

/-- Proposition 11.1.8: generalized isomorphisms with the same orbit map induce the same map of
faces and the same maps of the faces' orbit spaces. -/
def B : Prop :=
  ∀ (X Y : EP.{0}), FaceStructuredB X.X → FaceStructuredB Y.X →
    ∀ f g : EPLoc.of X ⟶ EPLoc.of Y, IsIso f → IsIso g →
      EPLoc.orbitMap f = EPLoc.orbitMap g →
      (∀ d e : Diagram X Y, EPLoc.homMk d = f → EPLoc.homMk e = g →
        ∀ A, IsEpFaceB X.X A → dPushB d A = dPushB e A) ∧
      (∀ θ, IsOrbitFaceB X.X θ →
        Set.MapsTo (EPLoc.orbitMap f) θ (EPLoc.orbitMap f '' θ) ∧
        Set.MapsTo (EPLoc.orbitMap g) θ (EPLoc.orbitMap g '' θ) ∧
        ∀ z ∈ θ, EPLoc.orbitMap f z = EPLoc.orbitMap g z)

end RoundTrip.V11_8
