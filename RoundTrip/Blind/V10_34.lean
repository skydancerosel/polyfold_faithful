import Polyfold
/-! Blind formalization of V10_34 (the text's Part II, §10.3, Lemma 10.3.2, p. 484 of the
Springer 2021 book; 2017: Lemma 10.3, p. 348).

Text: a refinement of a refinement of `d` is a refinement of `d`.

Choices:
- Setting as in my `RoundTrip/Blind/V10_33.lean`: ep-groupoids `X`, `Y` as objects of the
  project's bundled `EP.{0}` (all spaces in `Type`), diagrams `X ←F A →Φ Y` the project's
  `EPLocalization.Diagram X Y` (an `EP` `A`, an equivalence `F`, an sc-smooth functor `Φ`).
- "refinement" is my `IsRefinementB` of V10_33 (Definition 10.3.1: an equivalence `H : A' → A`
  with `F ∘ H ≃ F'`, `Φ ∘ H ≃ Φ'`, `≃` meaning there is a project `EpNatTrans`; "equivalence" the
  project's `EpFunctor.IsEquivalence`, `∘` its `EpFunctor.comp`), copied here; the project's
  `Diagram.IsRefinement` is not used.
- Reading: if `d'` refines `d` and `d''` refines `d'`, then `d''` refines `d`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_34
open Polyfold

/-- **Definition 10.3.1**: `d'` is a refinement of `d`: an equivalence `H : A' → A` with
`F ∘ H ≃ F'` and `Φ ∘ H ≃ Φ'`. -/
def IsRefinementB {X Y : EP.{0}} (d' d : EPLocalization.Diagram X Y) : Prop :=
  ∃ H : EpFunctor d'.A.X d.A.X, H.IsEquivalence ∧
    Nonempty (EpNatTrans (d.F.comp H) d'.F) ∧ Nonempty (EpNatTrans (d.Φ.comp H) d'.Φ)

/-- **Lemma 10.3.2**: a refinement of a refinement of `d` is a refinement of `d`. -/
def B : Prop :=
  ∀ (X Y : EP.{0}) (d d' d'' : EPLocalization.Diagram X Y),
    IsRefinementB d' d → IsRefinementB d'' d' → IsRefinementB d'' d

end RoundTrip.V10_34
