import Polyfold
/-! Blind formalization of V8_40 (the 2017 book, arXiv 1707.08941, Part II, §8.5.1, Lemma 8.10 and
the paragraph before it, p. 287; 2021: Lemma 8.6.2).

Text: given a proper covering functor `F : Y → X` and isomorphic `x`, `x'`, there is a one-to-one
correspondence between the isomorphism classes of `F⁻¹(x)` and of `F⁻¹(x')`: if
`F⁻¹(x) = ⨆_{j=1}^q Θ_j` is the decomposition into isomorphism classes, there is a decomposition
`F⁻¹(x') = ⨆_{j=1}^q Θ'_j` such that, if `y ∈ F⁻¹(x)` and `y' ∈ F⁻¹(x')` are connected by an
isomorphism, there is a uniquely determined `j` with `y ∈ Θ_j` and `y' ∈ Θ'_j`.  Before the lemma:
the objects of `F⁻¹(x')` reachable by a morphism from `y ∈ F⁻¹(x)` are mutually isomorphic, and so
are those reachable from the class of `y`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_38.lean`: spaces in `Type`, Hausdorff paracompact, the
  project's `EpGroupoid`, `EpFunctor`, `EpFunctor.IsProperCovering` (= Definition 8.5.1, checked
  with `#print`).  "Isomorphic"/"connected by an isomorphism" (`IsoB`): joined by a morphism (all
  morphisms of a groupoid are isomorphisms).
- "The decomposition into isomorphism classes" (`IsIsoClassDecompB`, as in V8_38): nonempty,
  pairwise disjoint classes `Θ : Fin q → Set`, covering the fibre, each a full isomorphism class
  within the fibre.  The decomposition of `F⁻¹(x)` is universally quantified (any enumeration of
  its classes); the `Θ'_j` are asserted to be the isomorphism classes of `F⁻¹(x')` (the "one-to-one
  correspondence between the isomorphism classes"), indexed by the same `j ∈ Fin q`.
- "Uniquely determined `j`": `∃!`.
- The paragraph before the lemma: (i) any two `y₁, y₂ ∈ F⁻¹(x')` reachable by morphisms from `y`
  are isomorphic; (ii) the same for `y₁, y₂` reachable from points of the class of `y`.  (i) is the
  special case of (ii) with the points equal to `y`; B states (ii) only.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_40
open Polyfold

/-- `y ≅ y'`: there is a morphism `y → y'`. -/
def IsoB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Prop :=
  ∃ φ : Mor, G.src φ = y ∧ G.tgt φ = y'

/-- `S = Θ₁ ⊔ ⋯ ⊔ Θ_q` is the decomposition of `S` into isomorphism classes. -/
def IsIsoClassDecompB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) {q : ℕ}
    (Θ : Fin q → Set Obj) : Prop :=
  (∀ j, (Θ j).Nonempty) ∧ (∀ j, Θ j ⊆ S) ∧ (⋃ j, Θ j) = S ∧
  Pairwise (fun i j => Disjoint (Θ i) (Θ j)) ∧
  ∀ j, ∀ y ∈ Θ j, ∀ y' ∈ S, (y' ∈ Θ j ↔ IsoB G y y')

/-- Lemma 8.6.2: for isomorphic `x`, `x'`, the isomorphism classes `Θ_j` of `F⁻¹(x)` correspond to
isomorphism classes `Θ'_j` of `F⁻¹(x')` such that isomorphic `y ∈ F⁻¹(x)`, `y' ∈ F⁻¹(x')` lie in
`Θ_j`, `Θ'_j` for a unique `j`; the objects of `F⁻¹(x')` reachable from the class of `y` are
mutually isomorphic. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x x' : ObjX, IsoB X.toGroupoidStr x x' →
      -- before the lemma
      (∀ y ∈ F.obj ⁻¹' {x}, ∀ y₁ ∈ F.obj ⁻¹' {x'}, ∀ y₂ ∈ F.obj ⁻¹' {x'},
        (∃ z₁ ∈ F.obj ⁻¹' {x}, IsoB Y.toGroupoidStr y z₁ ∧ IsoB Y.toGroupoidStr z₁ y₁) →
        (∃ z₂ ∈ F.obj ⁻¹' {x}, IsoB Y.toGroupoidStr y z₂ ∧ IsoB Y.toGroupoidStr z₂ y₂) →
        IsoB Y.toGroupoidStr y₁ y₂) ∧
      -- the lemma
      (∀ (q : ℕ) (Θ : Fin q → Set ObjY), IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) Θ →
        ∃ Θ' : Fin q → Set ObjY, IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x'}) Θ' ∧
          ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x'}, IsoB Y.toGroupoidStr y y' →
            ∃! j : Fin q, y ∈ Θ j ∧ y' ∈ Θ' j)

end RoundTrip.V8_40
