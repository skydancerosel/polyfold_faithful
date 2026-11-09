import Polyfold
/-! Blind formalization of V10_42 (the Springer 2021 book, Part II, §10.3, Theorem 10.3.10,
p. 489; 2017: Theorem 10.4, p. 353; proof in Appendix §10.6.2): generalized isomorphisms.

Text: `[X ←F A →Φ Y]` is a generalized isomorphism iff `Φ` is an equivalence, and the inverse is
`[Y ←Φ A →F X]`.

Choices:
- Setting: `EP.{u}`, any universe `u`, and the project's `Diagram` (`RoundTrip/Blind/V10_37.lean`).
- Generalized isomorphism (2021 Definition 10.3.9): my `IsGenIsoB d`, some diagram `e : Y → X`
  with `[e] ∘ [d] = [1_X]` and `[d] ∘ [e] = [1_Y]`, where `[·] = [·]` is "have a common
  refinement" (`EquivB`, copied from `RoundTrip/Blind/V10_37.lean`), the composite is the
  project's `Diagram.comp` (the weak-fibred-product diagram of Theorem 10.3.8, see
  `RoundTrip/Blind/V10_40.lean`) and `1_X` is `Diagram.id X`.  Stated on representatives, so the
  project's `EPLoc` category is not used.
- "Φ is an equivalence": `EpFunctor.IsEquivalence` (Definition 10.1.1) of the `Φ` of the given
  representative.
- "The inverse is `[Y ←Φ A →F X]`": when `Φ` is an equivalence, the reversed diagram, which I
  build myself with `Diagram.mk d.A d.Φ hΦ d.F` (not the project's `Diagram.symm`), is a
  two-sided inverse of `[d]` (inverses being unique in a category, this is "the" inverse).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_42
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

/-- The reversed diagram `Y ←Φ A →F X`, for `Φ` an equivalence. -/
def revB {X Y : EP.{u}} (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence) : Diagram Y X :=
  Diagram.mk d.A d.Φ hΦ d.F

/-- `[X ←F A →Φ Y]` is a generalized isomorphism iff `Φ` is an equivalence, with inverse
`[Y ←Φ A →F X]`. -/
def B : Prop :=
  ∀ (X Y : EP.{u}) (d : Diagram X Y),
    (IsGenIsoB d ↔ d.Φ.IsEquivalence) ∧
    ∀ hΦ : d.Φ.IsEquivalence,
      EquivB (d.comp (revB d hΦ)) (Diagram.id X) ∧ EquivB ((revB d hΦ).comp d) (Diagram.id Y)

end RoundTrip.V10_42
