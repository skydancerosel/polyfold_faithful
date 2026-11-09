import Polyfold
/-! Blind formalization of V10_44 (the Springer 2021 book, Part II, §10.3, Definition 10.3.12,
p. 490; 2017: Definition 10.9, p. 354): the category `EP(E⁻¹)`.

Text: `EP(E⁻¹)` has the ep-groupoids as objects and the generalized maps as morphisms.

Choices:
- This item is a definition.  B says that the project's category `EPLoc` (Mathlib
  `CategoryTheory.Category` instance) is this category: (1) its objects are the ep-groupoids
  (`EPLoc.toEP : EPLoc → EP` is a bijection); (2) its morphisms `EPLoc.of X ⟶ EPLoc.of Y` are
  the generalized maps, the classes `[d] = EPLoc.homMk d` of diagrams (every morphism is one,
  and `[d] = [d']` iff `d`, `d'` have a common refinement: my `EquivB`, copied from
  `RoundTrip/Blind/V10_37.lean`).
- The composition and the units of `EP(E⁻¹)` are not spelled out in this sentence; the text
  presupposes those of Theorem 10.3.8, which I add: (3) `[d] ≫ [e]` (Mathlib order: first `[d]`,
  i.e. the text's `[e] ∘ [d]`) is the class of the composite diagram `X ← A ×_Y B → Z`, the
  project's `Diagram.comp d e` (see `RoundTrip/Blind/V10_40.lean`); (4) the identity of `X` is
  `[1_X]`, `1_X = X ←1 X →1 X` the project's `Diagram.id X`.
- Setting: `EP.{u}`, any universe `u`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_44
open Polyfold Polyfold.EPLocalization CategoryTheory

universe u

/-- `d'` is a refinement of `d`: an equivalence `H : A' → A` with natural transformations
`F ∘ H ⇒ F'` and `Φ ∘ H ⇒ Φ'`. -/
def IsRefinementB {X Y : EP.{u}} (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- `d` and `d'` have a common refinement (`[d] = [d']`). -/
def EquivB {X Y : EP.{u}} (d d' : Diagram X Y) : Prop :=
  ∃ d'' : Diagram X Y, IsRefinementB d'' d ∧ IsRefinementB d'' d'

/-- `EPLoc` is the category with the ep-groupoids as objects, the generalized maps as morphisms,
the composition of Theorem 10.3.8 and the units `[1_X]`. -/
def B : Prop :=
  Function.Bijective EPLoc.toEP.{u} ∧
  (∀ (X Y : EP.{u}) (f : EPLoc.of X ⟶ EPLoc.of Y), ∃ d : Diagram X Y, EPLoc.homMk d = f) ∧
  (∀ (X Y : EP.{u}) (d d' : Diagram X Y), EPLoc.homMk d = EPLoc.homMk d' ↔ EquivB d d') ∧
  (∀ (X Y Z : EP.{u}) (d : Diagram X Y) (e : Diagram Y Z),
      EPLoc.homMk d ≫ EPLoc.homMk e = EPLoc.homMk (d.comp e)) ∧
  (∀ X : EP.{u}, 𝟙 (EPLoc.of X) = EPLoc.homMk (Diagram.id X))

end RoundTrip.V10_44
