import Polyfold
/-! Blind formalization of V10_37 (the Springer 2021 book, Part II, §10.3, Definition 10.3.5,
p. 486; 2017: Definition 10.6, p. 350): equivalence of diagrams.

Text: two diagrams are equivalent if they have a common refinement; `[d]` is the class.

Choices:
- This item is a definition.  B says that the project's `Diagram.Equiv d d'` is my `EquivB d d'`
  ("`d`, `d'` have a common refinement"), and that the project's classes (the quotient by
  `Diagram.setoid X Y`, the setoid whose quotient is the morphism type of `EPLoc`) are the
  classes for this relation: `⟦d⟧ = ⟦d'⟧ ↔ EquivB d d'`.  The second conjunct also encodes the
  text's presupposition (behind "the class `[d]`") that having a common refinement is an
  equivalence relation.
- Setting: the project's bundled ep-groupoids `EP.{u}` (any universe `u`; the middle ep-groupoid
  `A` of a diagram lives in the same universe, as in the project's `Diagram`).  A diagram
  `d : X ←F A →Φ Y` is the project's `EPLocalization.Diagram X Y` (`#print`ed: fields `A`, `F`,
  a proof that `F` is an equivalence, `Φ`), matching 2021 p. 483.
- Refinement (2021 Definition 10.3.1, as I read it): `d' : X ←F' A' →Φ' Y` refines
  `d : X ←F A →Φ Y` if there is an equivalence `H : A' → A` (the project's
  `EpFunctor.IsEquivalence`, Definition 10.1.1: full, faithful, `|H|` a homeomorphism, local
  sc-diffeomorphism on objects) with `F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`, `≃` meaning an (sc-smooth)
  natural transformation, the project's `EpNatTrans` (Definition 8.1); its direction does not
  matter (natural transformations between functors into a groupoid are invertible).  I define
  this myself (`IsRefinementB`) instead of using the project's `Diagram.IsRefinement`.
- Common refinement (2021 Definition 10.3.3): a diagram refining both.
- Nothing in the definition looks false to me.
-/
namespace RoundTrip.V10_37
open Polyfold Polyfold.EPLocalization

universe u

/-- `d'` is a refinement of `d`: an equivalence `H : A' → A` with natural transformations
`F ∘ H ⇒ F'` and `Φ ∘ H ⇒ Φ'`. -/
def IsRefinementB {X Y : EP.{u}} (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- `d` and `d'` have a common refinement. -/
def EquivB {X Y : EP.{u}} (d d' : Diagram X Y) : Prop :=
  ∃ d'' : Diagram X Y, IsRefinementB d'' d ∧ IsRefinementB d'' d'

/-- Equivalence of diagrams is having a common refinement, and `[d]` is the class of `d` for this
relation. -/
def B : Prop :=
  ∀ (X Y : EP.{u}) (d d' : Diagram X Y),
    (Diagram.Equiv d d' ↔ EquivB d d') ∧
    (Quotient.mk (Diagram.setoid X Y) d = Quotient.mk (Diagram.setoid X Y) d' ↔ EquivB d d')

end RoundTrip.V10_37
