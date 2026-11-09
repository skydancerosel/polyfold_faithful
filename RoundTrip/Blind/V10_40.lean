import Polyfold
/-! Blind formalization of V10_40 (the Springer 2021 book, Part II, §10.3, Theorem 10.3.8,
p. 488; 2017: Theorem 10.3, p. 352; proof in Appendix §10.6.1): composition of classes of
diagrams.

Text: the class of `X ← A ×_Y B → Z` depends only on `[d]`, `[d']`; the composition is
associative with units `[1_X]`.

Choices:
- Setting: the project's bundled ep-groupoids `EP.{u}` (any universe `u`) and diagrams
  `EPLocalization.Diagram X Y` (as in `RoundTrip/Blind/V10_37.lean`).
- The composite diagram `X ←(F ∘ π_A) A ×_Y B →(Ψ ∘ π_B) Z` of `d : X ←F A →Φ Y` and
  `d' : Y ←G B →Ψ Z`, `A ×_Y B` the weak fibred product of `Φ` and `G` (§10.2), is the project's
  `Diagram.comp d d'` (docstring: exactly this diagram, representing `[d'] ∘ [d]`).  I do not
  rebuild the weak fibred product (its M-polyfold structure is the content of Theorem 10.2.2);
  this is the one project construction B trusts.  `1_X = X ←1 X →1 X` is the project's
  `Diagram.id X`.
- "The class `[d]`": equivalence of diagrams = having a common refinement (2021 Definitions
  10.3.1, 10.3.3, 10.3.5), my `EquivB`, copied from `RoundTrip/Blind/V10_37.lean`; `[d] = [e]`
  is read `EquivB d e`.  Hence: (1) `EquivB d₁ d₂ → EquivB e₁ e₂ →
  EquivB (d₁.comp e₁) (d₂.comp e₂)`; (2) associativity `[d''] ∘ ([d'] ∘ [d]) =
  ([d''] ∘ [d']) ∘ [d]`; (3) `[1_Y] ∘ [d] = [d] = [d] ∘ [1_X]`.  Associativity and units are
  stated for representatives, which by (1) is the same as for classes.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_40
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

/-- Composition of classes is well defined, associative, and has the units `[1_X]`. -/
def B : Prop :=
  (∀ (X Y Z : EP.{u}) (d₁ d₂ : Diagram X Y) (e₁ e₂ : Diagram Y Z),
      EquivB d₁ d₂ → EquivB e₁ e₂ → EquivB (d₁.comp e₁) (d₂.comp e₂)) ∧
  (∀ (W X Y Z : EP.{u}) (d : Diagram W X) (d' : Diagram X Y) (d'' : Diagram Y Z),
      EquivB ((d.comp d').comp d'') (d.comp (d'.comp d''))) ∧
  (∀ (X Y : EP.{u}) (d : Diagram X Y),
      EquivB (d.comp (Diagram.id Y)) d ∧ EquivB ((Diagram.id X).comp d) d)

end RoundTrip.V10_40
