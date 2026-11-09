import Polyfold
/-! Blind formalization of V10_50 (the text's Part II, §10.3, Theorem 10.3.21, p. 495 of the
Springer 2021 book; new in the 2021 edition): invariance under generalized isomorphisms.

Text: if one of `X`, `Y` has (LR), (LUC), (SLR), (SLUC) or (ZHOU), so has the other.

Choices:
- `X`, `Y` are ep-groupoids related by a generalized isomorphism `f : X → Y` (the item's title;
  the text's Definition 10.3.9: a morphism of `EP(E⁻¹)` with a two-sided inverse).  Setting:
  universe 0, objects of the project's `EPLoc.{0}` (`EP(E⁻¹)`, 2021 Definition 10.3.12), and the
  project's `EPLoc.IsGeneralizedIso` (read with `#print`: some `g` with `f ≫ g = 𝟙`, `g ≫ f = 𝟙`).
  I quantify over `f` and the hypothesis that it is a generalized isomorphism.
- The five properties are the project's: (LR) `EpGroupoid.IsLR` (2021 Definition 7.4.19),
  (LUC) `EpGroupoid.IsLUC` (2021 Definition 7.2.18), (SLR) `EP.IsSLR` ((LR) for every iterated
  lift `Xⁱ`, 2021 Definition 7.4.23), (SLUC) `EP.IsSLUC` ((LUC) for every `Xⁱ`, 2021 Definition
  7.4.12), (ZHOU) `EpGroupoid.IsZhou` (2021 Definition 7.4.5); all read with `#print`.
- "if one of `X`, `Y` has P, so has the other" is read property by property: `P X ↔ P Y`, for each
  of the five, B being the conjunction.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_50
open Polyfold CategoryTheory

/-- Theorem 10.3.21: a generalized isomorphism `X → Y` preserves and reflects (LR), (LUC),
(SLR), (SLUC) and (ZHOU). -/
def B : Prop :=
  ∀ (X Y : EPLocalization.EPLoc.{0}) (f : X ⟶ Y), EPLocalization.EPLoc.IsGeneralizedIso f →
    (X.toEP.X.IsLR ↔ Y.toEP.X.IsLR) ∧
    (X.toEP.X.IsLUC ↔ Y.toEP.X.IsLUC) ∧
    (X.toEP.IsSLR ↔ Y.toEP.IsSLR) ∧
    (X.toEP.IsSLUC ↔ Y.toEP.IsSLUC) ∧
    (X.toEP.X.IsZhou ↔ Y.toEP.X.IsZhou)

end RoundTrip.V10_50
