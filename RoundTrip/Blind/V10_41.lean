import Polyfold
/-! Blind formalization of V10_41 (the Springer 2021 book, Part II, §10.3, Definition 10.3.9,
p. 489; 2017: Definition 10.8, p. 352): generalized maps and generalized isomorphisms.

Text: a generalized map is a class `[d]`; it is a generalized isomorphism if it has a two-sided
inverse `[d]⁻¹`.

Choices:
- This item is a definition.  The project's generalized maps `X → Y` are the morphisms
  `EPLoc.of X ⟶ EPLoc.of Y` of its `EPLoc`, and `[d]` is `EPLoc.homMk d`; its generalized
  isomorphisms are `EPLoc.IsGeneralizedIso`.  B says: (1) every generalized map is a class
  `[d]`; (2) `[d] = [d']` iff `d`, `d'` have a common refinement (my `EquivB`, the text's
  equivalence of diagrams, copied from `RoundTrip/Blind/V10_37.lean`); (3) `[d]` is a
  generalized isomorphism iff some `[e] : Y → X` has `[e] ∘ [d] = [1_X]` and
  `[d] ∘ [e] = [1_Y]`, where the composition is that of Theorem 10.3.8, the class of the
  composite diagram `X ← A ×_Y B → Z`, the project's `Diagram.comp d e` (docstring: this
  diagram, representing `[e] ∘ [d]`), and `1_X = X ←1 X →1 X` is `Diagram.id X`.  So (3) is
  stated with diagrams and `EquivB`, without the project's category structure on `EPLoc`.
- The notation `[d]⁻¹` (the inverse) carries no further claim; uniqueness of the inverse is not
  asserted.
- Setting: `EP.{u}`, any universe `u`, and the project's `Diagram`, as in
  `RoundTrip/Blind/V10_37.lean`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_41
open Polyfold Polyfold.EPLocalization

universe u

/-- `d'` is a refinement of `d`: an equivalence `H : A' → A` with natural transformations
`F ∘ H ⇒ F'` and `Φ ∘ H ⇒ Φ'`. -/
def IsRefinementB {X Y : EP.{u}} (d' d : Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- `d` and `d'` have a common refinement (`[d] = [d']`). -/
def EquivB {X Y : EP.{u}} (d d' : Diagram X Y) : Prop :=
  ∃ d'' : Diagram X Y, IsRefinementB d'' d ∧ IsRefinementB d'' d'

/-- `[d]` has a two-sided inverse `[e]`: `[e] ∘ [d] = [1_X]`, `[d] ∘ [e] = [1_Y]`. -/
def IsGenIsoB {X Y : EP.{u}} (d : Diagram X Y) : Prop :=
  ∃ e : Diagram Y X, EquivB (d.comp e) (Diagram.id X) ∧ EquivB (e.comp d) (Diagram.id Y)

/-- Generalized maps are the classes `[d]`, and `[d]` is a generalized isomorphism iff it has a
two-sided inverse. -/
def B : Prop :=
  (∀ (X Y : EP.{u}) (f : EPLoc.of X ⟶ EPLoc.of Y), ∃ d : Diagram X Y, EPLoc.homMk d = f) ∧
  (∀ (X Y : EP.{u}) (d d' : Diagram X Y), EPLoc.homMk d = EPLoc.homMk d' ↔ EquivB d d') ∧
  (∀ (X Y : EP.{u}) (d : Diagram X Y), EPLoc.IsGeneralizedIso (EPLoc.homMk d) ↔ IsGenIsoB d)

end RoundTrip.V10_41
