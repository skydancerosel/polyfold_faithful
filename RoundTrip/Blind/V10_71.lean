import Polyfold
/-! Blind formalization of V10_71 (the Springer 2021 book, Part II, §10.5, Remark 10.5.3, p. 506;
new in the 2021 edition): the strong bundle case of Theorem 10.3.10 (2017: Theorem 10.4,
p. 353), one direction.

Text: in the strong bundle case a result similar to Theorem 10.3.10 can be proved: a generalized
strong bundle map is an isomorphism iff it is represented by a diagram whose two legs are strong
bundle equivalences; it is built into Definition 10.5.2.

Choices:
- "One direction" (the title): I take the direction that justifies the name in Definition 10.5.2:
  a class `[D]` of a diagram `W ←Φ W'' →Ψ W'` whose two legs are strong bundle equivalences is an
  isomorphism of `SEP(F⁻¹)`; following Theorem 10.3.10 (2), its inverse is the class of the
  reversed diagram `W' ←Ψ W'' →Φ W`.  The converse (an isomorphism has such a representative) is
  not claimed.
- Setting: universe 0, `A, A' : SEP.{0}`, diagrams the project's `SDiagram` (see
  `RoundTrip/Blind/V10_69.lean`); `Φ` is a strong bundle equivalence by definition of a diagram,
  and the hypothesis `SEP.equivalences D.Ψ` (2021 Definition 10.4.1, trusted) makes `Ψ` one.  The
  reversed diagram is built by me (`revB`, from the fields of `D`), not the project's
  `SDiagram.symm`.
- "isomorphism": of `SEP(F⁻¹)` (2021 Definition 10.5.1), whose composition and units are those
  of V10_70 (`RoundTrip/Blind/V10_70.lean`): `[E] ∘ [D] = [D.comp E]` (the project's
  `SDiagram.comp`, the weak-fibred-product composite, read with `#print`) and `[1_W]` (the
  project's `SDiagram.id`).  Stated with classes `D.cls` (the project's `GenSBMap`, read with
  `#print`), so the project's (unprinted) category instance on `SEPLoc` is not used: the
  composites of `D` with `revB D h` in both orders are in the classes of the units.  With the
  explicit inverse `[revB D h]` this is `IsIso` together with the description of the inverse.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_71
open Polyfold Polyfold.SBLocalization

/-- The reversed diagram `W' ←Ψ W'' →Φ W` of a diagram whose `Ψ` is a strong bundle
equivalence. -/
def revB {A A' : SEP.{0}} (D : SDiagram A A') (h : SEP.equivalences D.Ψ) : SDiagram A' A :=
  SDiagram.mk D.B D.Ψ h D.Φ

/-- **Theorem 10.3.10 for strong bundles, one direction**: a diagram with both legs strong bundle
equivalences represents an isomorphism of `SEP(F⁻¹)`, inverted by the reversed diagram. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (D : SDiagram A A') (h : SEP.equivalences D.Ψ),
    (D.comp (revB D h)).cls = (SDiagram.id A).cls ∧
    ((revB D h).comp D).cls = (SDiagram.id A').cls

end RoundTrip.V10_71
