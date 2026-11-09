import Polyfold
/-! Blind formalization of V10_33 (the text's Part II, §10.3, Definition 10.3.1, p. 484 of the
Springer 2021 book; 2017: Definition 10.4, p. 348).

Text: a diagram `d = (X ←F A →Φ Y)` consists of an ep-groupoid `A`, an equivalence `F : A → X`
and an sc-smooth functor `Φ : A → Y`; the diagram `d' = (X ←F' A' →Φ' Y)` is a refinement of `d`
if there is an equivalence `H : A' → A` with `F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`; two examples follow.

Choices:
- This item is a definition.  Setting: ep-groupoids as objects of the project's bundled `EP`
  (a structure with the two spaces, their instances and an `EpGroupoid`), in universe 0
  (`EP.{0}`, all spaces in `Type`).  The middle groupoid `A` of a diagram is in the same universe
  as `X`, `Y` (nothing in the text restricts it).
- Diagrams are the project's `EPLocalization.Diagram X Y` (fields read with `#print`: `A : EP`,
  `F : EpFunctor A.X X.X`, a proof that `F` is an equivalence, `Φ : EpFunctor A.X Y.X`), exactly
  the text's triples.  "Equivalence" is the project's `EpFunctor.IsEquivalence` (Definition
  10.1.1, characterized in `RoundTrip/Blind/V10_1.lean`), "sc-smooth functor" its `EpFunctor`,
  `F ∘ H` its `EpFunctor.comp` (V7_9), `≃` "there is a natural transformation" with the project's
  `EpNatTrans` (Definition 10.1.4, characterized in `RoundTrip/Blind/V10_4.lean`), in the
  direction `F ∘ H → F'` (the relation is symmetric).
- `IsRefinementB d' d` ("`H : d' → d`") is my reading of the definition; B (b) says the project's
  `Diagram.IsRefinement d' d` is it.
- The two examples are not spelled out in the quoted statement; I formalize the two I believe the
  text gives: (c) for an equivalence `H : A' → A`, `X ←F∘H A' →Φ∘H Y` refines `d` (the proof that
  `F ∘ H` is an equivalence, needed for this to be a diagram, is taken as a hypothesis); (d) a
  diagram `X ←F' A →Φ' Y` on the same `A` with `F ≃ F'`, `Φ ≃ Φ'` refines `d` (via `H = 1_A`;
  this contains "every diagram refines itself").  If the text's examples differ, (c), (d) are my
  guesses (both true).
- (a) records that the left leg of a diagram is an equivalence (part of the definition).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_33
open Polyfold

/-- **Definition 10.3.1**: `d'` is a refinement of `d`: an equivalence `H : A' → A` with
`F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`. -/
def IsRefinementB {X Y : EP.{0}} (d' d : EPLocalization.Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- Definition 10.3.1: diagrams have an equivalence as left leg; the project's refinements are the
text's; the two examples. -/
def B : Prop :=
  ∀ X Y : EP.{0},
    -- (a) the left leg of a diagram is an equivalence
    (∀ d : EPLocalization.Diagram X Y, d.F.IsEquivalence) ∧
    -- (b) the project's refinement relation is the text's
    (∀ d' d : EPLocalization.Diagram X Y, d'.IsRefinement d ↔ IsRefinementB d' d) ∧
    -- (c) first example: precomposition with an equivalence `H : A' → A`
    (∀ (d : EPLocalization.Diagram X Y) (A' : EP.{0}) (H : EpFunctor A'.X d.A.X)
      (hFH : (d.F.comp H).IsEquivalence), H.IsEquivalence →
        IsRefinementB (EPLocalization.Diagram.mk A' (d.F.comp H) hFH (d.Φ.comp H)) d) ∧
    -- (d) second example: naturally equivalent legs on the same `A` (`H = 1_A`)
    (∀ (d : EPLocalization.Diagram X Y) (F' : EpFunctor d.A.X X.X) (hF' : F'.IsEquivalence)
      (Φ' : EpFunctor d.A.X Y.X),
      Nonempty (EpNatTrans d.F F') → Nonempty (EpNatTrans d.Φ Φ') →
        IsRefinementB (EPLocalization.Diagram.mk d.A F' hF' Φ') d)

end RoundTrip.V10_33
