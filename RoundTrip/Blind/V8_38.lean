import Polyfold
/-! Blind formalization of V8_38 (the 2017 book, arXiv 1707.08941, Part II, §8.5.1, p. 286, before
Lemma 8.9; 2021: §8.6.1, p. 397).

Text: for a proper covering functor `F : Y → X` and `x ∈ X`, `X(x)` is the full subcategory on `x`
(morphisms `G_x`) and `Y(x)` the full subcategory on the finite set `F⁻¹(x)` (morphisms
`mor(F⁻¹(x))`).  By Definition 8.5.1 (3), `mor(F⁻¹(x)) → G_x × F⁻¹(x)`, `φ ↦ (F(φ), s(φ))`, is a
bijection, so `#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)`.  `F⁻¹(x) = Θ₁ ∪ ⋯ ∪ Θ_q` is the decomposition into
isomorphism classes, and for `y, y' ∈ Θ_j` the isotropy groups `G_y`, `G_{y'}` are isomorphic.

Choices:
- Setting: object/morphism spaces in `Type` (universe 0, as in the Chapter 7 blind files),
  Hausdorff paracompact; `X`, `Y` the project's `EpGroupoid`, `F` an `EpFunctor`; "proper covering
  functor" the project's `EpFunctor.IsProperCovering` (fields read with `#print`; they are the
  text's Definition 8.5.1, see `RoundTrip/Blind/V8_29.lean`).
- `mor(F⁻¹(x))` (the morphisms of `Y(x)`): the morphisms `φ` with `s φ, t φ ∈ F⁻¹(x)` (my
  `morOnB`).  `G_x` as a set: `isoSetB X x = {g | s g = x ∧ t g = x}`.  The full subcategories
  themselves are definitions and are not formalized beyond these sets.
- `#` is `Set.ncard`; since `ncard` of an infinite set is `0`, I also assert that `mor(F⁻¹(x))` is
  finite (presupposed by `#`).
- "The decomposition into isomorphism classes" (my `IsIsoClassDecompB S Θ`): `Θ : Fin q → Set`,
  every `Θ_j` nonempty and contained in `S = F⁻¹(x)`, pairwise disjoint, covering `S`, and each
  `Θ_j` a full isomorphism class within `S` (`y ∈ Θ_j`, `y' ∈ S` ⇒ (`y' ∈ Θ_j` ↔ `y ≅ y'`)); B
  asserts that such a decomposition exists.  "Isomorphic" objects (`IsoB`): joined by a morphism.
- "`G_y`, `G_{y'}` isomorphic": isomorphic as groups, for the project's group `Y.Isotropy y`
  (product `(g * h).val = g ∘ h`, checked by `rfl`), for any decomposition and any `y, y'` in one
  `Θ_j`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_38
open Polyfold

/-- `G_x` as a set of morphisms. -/
def isoSetB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) : Set Mor :=
  {g | G.src g = x ∧ G.tgt g = x}

/-- The morphisms between points of `S`. -/
def morOnB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) : Set Mor :=
  {φ | G.src φ ∈ S ∧ G.tgt φ ∈ S}

/-- `y ≅ y'`: there is a morphism `y → y'`. -/
def IsoB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Prop :=
  ∃ φ : Mor, G.src φ = y ∧ G.tgt φ = y'

/-- `S = Θ₁ ⊔ ⋯ ⊔ Θ_q` is the decomposition of `S` into isomorphism classes. -/
def IsIsoClassDecompB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) {q : ℕ}
    (Θ : Fin q → Set Obj) : Prop :=
  (∀ j, (Θ j).Nonempty) ∧ (∀ j, Θ j ⊆ S) ∧ (⋃ j, Θ j) = S ∧
  Pairwise (fun i j => Disjoint (Θ i) (Θ j)) ∧
  ∀ j, ∀ y ∈ Θ j, ∀ y' ∈ S, (y' ∈ Θ j ↔ IsoB G y y')

/-- §8.6.1: `φ ↦ (F(φ), s(φ))` is a bijection `mor(F⁻¹(x)) → G_x × F⁻¹(x)`, so
`#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)`; `F⁻¹(x)` decomposes into isomorphism classes, and objects in one
class have isomorphic isotropy groups. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x : ObjX,
      -- the bijection `mor(F⁻¹(x)) → G_x × F⁻¹(x)`
      Set.BijOn (fun φ : MorY => (F.mor φ, Y.src φ)) (morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}))
        (isoSetB X.toGroupoidStr x ×ˢ (F.obj ⁻¹' {x})) ∧
      -- `#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)`
      (morOnB Y.toGroupoidStr (F.obj ⁻¹' {x})).Finite ∧
      (morOnB Y.toGroupoidStr (F.obj ⁻¹' {x})).ncard =
        (isoSetB X.toGroupoidStr x).ncard * (F.obj ⁻¹' {x}).ncard ∧
      -- the decomposition into isomorphism classes exists
      (∃ (q : ℕ) (Θ : Fin q → Set ObjY), IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) Θ) ∧
      -- objects in one class have isomorphic isotropy groups
      (∀ (q : ℕ) (Θ : Fin q → Set ObjY), IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) Θ →
        ∀ j, ∀ y ∈ Θ j, ∀ y' ∈ Θ j, Nonempty (Y.Isotropy y ≃* Y.Isotropy y'))

end RoundTrip.V8_38
