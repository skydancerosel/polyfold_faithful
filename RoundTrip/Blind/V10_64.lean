import Polyfold
/-! Blind formalization of V10_64 (the Springer 2021 book, Part II, §10.3, Proposition 10.3.16,
p. 492; new in the 2021 edition): (LR) under generalized isomorphisms.

Text: if `f : X → Y` is a generalized isomorphism and one of `X`, `Y` has the local regularity
property, so has the other.

Choices:
- Setting: universe 0 (all spaces in `Type`), `X`, `Y` objects of the project's category
  `EPLoc.{0}` (`EP(E⁻¹)`, 2021 Definition 10.3.12: the ep-groupoids, with the classes of
  diagrams as morphisms; compared with the text in `RoundTrip/Blind/V10_44.lean`), as in
  `RoundTrip/Blind/V10_50.lean`.
- "generalized isomorphism" (2021 Definition 10.3.9): the project's `EPLoc.IsGeneralizedIso`
  (read with `#print`: some `g : Y → X` with `f ≫ g = 𝟙 X` and `g ≫ f = 𝟙 Y`), the text's
  definition verbatim in the category `EP(E⁻¹)`.
- "(LR)": the project's `EpGroupoid.IsLR` (2021 Definition 7.4.19, read with `#print`; see
  `RoundTrip/Blind/V10_62.lean`) of the underlying ep-groupoid `toEP.X`.
- "if one has (LR), so has the other": `X.IsLR ↔ Y.IsLR`, for every `f` that is a generalized
  isomorphism.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_64
open Polyfold Polyfold.EPLocalization

/-- **Proposition 10.3.16**: a generalized isomorphism `f : X → Y` transports (LR) both ways. -/
def B : Prop :=
  ∀ (X Y : EPLoc.{0}) (f : X ⟶ Y), EPLoc.IsGeneralizedIso f →
    (X.toEP.X.IsLR ↔ Y.toEP.X.IsLR)

end RoundTrip.V10_64
