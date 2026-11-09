import Polyfold
/-! Blind formalization of V10_35 (the text's Part II, §10.3, Definition 10.3.3, p. 485 of the
Springer 2021 book; 2017: Definition 10.5, p. 349).

Text: a common refinement of the pair `(d, d')` of diagrams is a diagram which is a refinement of
both `d` and `d'`.

Choices:
- This item is a definition.  Setting as in my `RoundTrip/Blind/V10_33.lean`: `X`, `Y` objects of
  the project's bundled `EP.{0}` (all spaces in `Type`), diagrams the project's
  `EPLocalization.Diagram X Y`; all three diagrams go from `X` to `Y`.
- "refinement" is my `IsRefinementB` of V10_33 (Definition 10.3.1), copied here.
- B says the project's `Diagram.IsCommonRefinement d'' d d'` (argument order read from its type:
  the candidate first, then the pair) is "`d''` refines `d` and `d''` refines `d'`".
- Nothing looks false to me.
-/
namespace RoundTrip.V10_35
open Polyfold

/-- **Definition 10.3.1**: `d'` is a refinement of `d`: an equivalence `H : A' → A` with
`F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`. -/
def IsRefinementB {X Y : EP.{0}} (d' d : EPLocalization.Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- **Definition 10.3.3**: `d''` is a common refinement of `(d, d')`. -/
def IsCommonRefinementB {X Y : EP.{0}} (d'' d d' : EPLocalization.Diagram X Y) : Prop :=
  IsRefinementB d'' d ∧ IsRefinementB d'' d'

/-- Definition 10.3.3: the project's common refinements are the text's. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (d'' d d' : EPLocalization.Diagram X Y),
    d''.IsCommonRefinement d d' ↔ IsCommonRefinementB d'' d d'

end RoundTrip.V10_35
