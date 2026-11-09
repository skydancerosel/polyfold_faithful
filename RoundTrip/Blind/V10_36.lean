import Polyfold
/-! Blind formalization of V10_36 (the text's Part II, §10.3, Lemma 10.3.4, p. 485 of the
Springer 2021 book; 2017: Lemma 10.4, p. 349).

Text: if the pairs `(d, d')` and `(d', d'')` have common refinements, so has `(d, d'')`; the proof
builds it as the diagram (10.11) over the weak fibred product `W ×_{A'} W'`.

Choices:
- Setting as in my `RoundTrip/Blind/V10_33.lean`: `X`, `Y` objects of the project's bundled
  `EP.{0}` (all spaces in `Type`), diagrams the project's `EPLocalization.Diagram X Y`.  The
  common refinements range over all diagrams `X → Y` with middle groupoid in universe 0, which
  contains the text's `W ×_{A'} W'` (built from universe-0 data).
- "refinement" is my `IsRefinementB` of V10_33 (Definition 10.3.1), "common refinement" my
  `IsCommonRefinementB` of V10_35 (Definition 10.3.3), both copied here; the project's
  `IsRefinement`, `IsCommonRefinement` are not used.
- The claim of the lemma is the existence statement (transitivity of "having a common
  refinement").  "by the diagram (10.11) over `W ×_{A'} W'`" names the proof's construction; the
  quoted statement does not give (10.11) itself, so the construction is not part of B.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_36
open Polyfold

/-- **Definition 10.3.1**: `d'` is a refinement of `d`: an equivalence `H : A' → A` with
`F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`. -/
def IsRefinementB {X Y : EP.{0}} (d' d : EPLocalization.Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- **Definition 10.3.3**: `e` is a common refinement of `(d, d')`. -/
def IsCommonRefinementB {X Y : EP.{0}} (e d d' : EPLocalization.Diagram X Y) : Prop :=
  IsRefinementB e d ∧ IsRefinementB e d'

/-- **Lemma 10.3.4**: if `(d, d')` and `(d', d'')` have common refinements, so has `(d, d'')`. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (d d' d'' : EPLocalization.Diagram X Y),
    (∃ e : EPLocalization.Diagram X Y, IsCommonRefinementB e d d') →
    (∃ e' : EPLocalization.Diagram X Y, IsCommonRefinementB e' d' d'') →
    ∃ e'' : EPLocalization.Diagram X Y, IsCommonRefinementB e'' d d''

end RoundTrip.V10_36
