import Polyfold
/-! Blind formalization of V10_55 (the text's Part II, §10.5, Definition 10.5.1, p. 506 of the
Springer 2021 book; 2017: Definition 10.14, p. 366): the category `SEP(F⁻¹)`.

Text: the category `SEP(F⁻¹)` has the strong bundles over ep-groupoids as objects and the
generalized strong bundle maps as morphisms.

Choices:
- This item is a definition.  Setting: universe 0; strong bundles over ep-groupoids are the
  project's bundled `SEP.{0}`, generalized strong bundle maps `W → W'` the project's
  `GenSBMap A A'` (classes `[D]` of diagrams `W ←Φ W'' →Ψ W'`; V10_51 compares them with the
  text).  `SEP(F⁻¹)` is the project's `SEPLoc.{0}` with the category instance Lean finds.
- "objects": `SEPLoc.toSEP : SEP(F⁻¹) → SEP` is a bijection.  "morphisms": the hom-type
  `⟨A⟩ ⟶ ⟨A'⟩` is `GenSBMap A A'` (a type equality).
- Not in the item's statement but presupposed by "the category": the identity of `W` is the class
  of the identity diagram `W ←1 W →1 W` (stated for every diagram whose middle is `W` and whose
  legs are `1_W`, compared by `HEq`).  The composition (as for ep-groupoids, via weak fibred
  products) is not formalized: I have no independent composite diagram of strong bundles.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_55
open Polyfold CategoryTheory

/-- Definition 10.5.1: `SEP(F⁻¹)` has the strong bundles over ep-groupoids as objects, the
generalized strong bundle maps as morphisms, and the classes `[1_W]` as identities. -/
def B : Prop :=
  Function.Bijective SBLocalization.SEPLoc.toSEP.{0} ∧
  (∀ A A' : SEP.{0},
    (SBLocalization.SEPLoc.of A ⟶ SBLocalization.SEPLoc.of A') = SBLocalization.GenSBMap A A') ∧
  (∀ (A : SEP.{0}) (D : SBLocalization.SDiagram A A),
    D.B = A → HEq D.Φ (𝟙 A) → HEq D.Ψ (𝟙 A) →
    SBLocalization.SEPLoc.homMk D = 𝟙 (SBLocalization.SEPLoc.of A))

end RoundTrip.V10_55
