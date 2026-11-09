import Polyfold
/-! Blind formalization of V11_5 (the text's Part II, §11.1, Remark 11.1.5, p. 524 of the
Springer 2021 book; 2017: Remark 11.1, p. 378).

Text: an equivalence `Φ` induces a bijection `θ ↦ |Φ|(θ)` between faces, with
`Φ_*(X_θ) = saturation(Φ(X_θ))` and `Φ^*(Y_θ') = Φ⁻¹(Y_θ')`; for a generalized isomorphism
`[d]_* = Ψ_* ∘ Φ^*`, `[d]^* = Φ_* ∘ Ψ^*`.  The text quotes [56, Proposition 3.15].

Choices:
- Setting: `X`, `Y` objects of the project's bundled `EP.{0}` (all spaces in `Type`).  No
  tameness is assumed (the quoted statement has none; the claims need none).
- "equivalence": the project's `EpFunctor.IsEquivalence` (Definition 10.1.1,
  `RoundTrip/Blind/V10_1.lean`).  `|Φ|`: the induced map of orbit spaces
  `Φ.toGroupoidFunctor.orbitMap` (`#print`ed: `Quotient.map Φ.obj`).
- Faces of `|X|`, `X_θ`: Definition 11.1.3 as rendered in my `RoundTrip/Blind/V11_3.lean`
  (copied: `IsOrbitFaceB`, `faceObjB`; faces of `X` recorded by their object sets).
- `saturation(Φ(A))` (`pushObjB`): the objects of `Y` isomorphic to some `Φ(a)`, `a ∈ A`.
- (a) for an equivalence `Φ`: `θ ↦ |Φ|(θ)` is a bijection from the faces of `|X|` onto those of
  `|Y|` (`Set.BijOn`); `Φ_*(X_θ) = saturation(Φ(X_θ))` is `Y_{|Φ|(θ)}`; `Φ^*(Y_θ') = Φ⁻¹(Y_θ')`
  is `X_{|Φ|⁻¹(θ')}`.  I read the remark as asserting that these are the faces corresponding to
  `θ`, `θ'` under the bijection (so `Φ_*`, `Φ^*` are mutually inverse bijections of faces).
- (b) for a generalized isomorphism `f` (Mathlib's `IsIso` in the project's `EP(E⁻¹)`), with
  `|f|` the project's `EPLoc.orbitMap` (`#print`ed: `|Ψ| ∘ |Φ|⁻¹` on a representative,
  Definition 10.3.7): `θ ↦ |f|(θ)` is a bijection of faces, and for every representative
  `d = X ←Φ A →Ψ Y` of `f` (the project's `Diagram`, `d.F = Φ`, `d.Φ = Ψ`),
  `[d]_*(X_θ) = Ψ_*(Φ^*(X_θ)) = Y_{|f|(θ)}` and `[d]^*(Y_θ') = Φ_*(Ψ^*(Y_θ')) = X_{|f|⁻¹(θ')}`
  (so `[d]_*`, `[d]^*` do not depend on the representative and are inverse bijections of faces).
- The citation of [56] is not formalized.
- Nothing looks false to me.
-/
namespace RoundTrip.V11_5
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

/-- The induced map `|Φ| : |X| → |Y|`. -/
def orbB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (Φ : EpFunctor X Y) :
    X.OrbitSpace → Y.OrbitSpace :=
  Φ.toGroupoidFunctor.orbitMap

/-- `saturation(Φ(A))`: the objects isomorphic to some `Φ(a)`, `a ∈ A`. -/
def pushObjB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (Φ : EpFunctor X Y)
    (A : Set Obj) : Set Obj' :=
  {y | ∃ a ∈ A, ∃ ψ : Mor', Y.src ψ = Φ.obj a ∧ Y.tgt ψ = y}

end

/-- Remark 11.1.5: faces correspond under equivalences (`Φ_*`, `Φ^*`) and under generalized
isomorphisms (`[d]_* = Ψ_* ∘ Φ^*`, `[d]^* = Φ_* ∘ Ψ^*`). -/
def B : Prop :=
  -- (a) an equivalence `Φ : X → Y`
  (∀ (X Y : EP.{0}) (Φ : EpFunctor X.X Y.X), Φ.IsEquivalence →
    Set.BijOn (fun θ => orbB Φ '' θ) {θ | IsOrbitFaceB X.X θ} {θ' | IsOrbitFaceB Y.X θ'} ∧
    (∀ θ, IsOrbitFaceB X.X θ → pushObjB Φ (faceObjB X.X θ) = faceObjB Y.X (orbB Φ '' θ)) ∧
    (∀ θ', IsOrbitFaceB Y.X θ' → Φ.obj ⁻¹' faceObjB Y.X θ' = faceObjB X.X (orbB Φ ⁻¹' θ'))) ∧
  -- (b) a generalized isomorphism `f = [X ←Φ A →Ψ Y]`
  (∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), IsIso f →
    Set.BijOn (fun θ => EPLoc.orbitMap f '' θ) {θ | IsOrbitFaceB X.X θ}
      {θ' | IsOrbitFaceB Y.X θ'} ∧
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ θ, IsOrbitFaceB X.X θ →
        pushObjB d.Φ (d.F.obj ⁻¹' faceObjB X.X θ) = faceObjB Y.X (EPLoc.orbitMap f '' θ)) ∧
      (∀ θ', IsOrbitFaceB Y.X θ' →
        pushObjB d.F (d.Φ.obj ⁻¹' faceObjB Y.X θ') = faceObjB X.X (EPLoc.orbitMap f ⁻¹' θ')))

end RoundTrip.V11_5
