import Polyfold
/-! Blind formalization of V10_57 (the text's Part II, §10.5, Remark 10.5.3, p. 506 of the
Springer 2021 book; new in the 2021 edition): the comparison with Theorem 10.3.10.

Text: Theorem 10.3.10 characterizes generalized isomorphisms by diagrams with both legs
equivalences; in the strong bundle case a similar result can be proved, and it is built into
Definition 10.5.2.

Choices:
- B is the conjunction of the two characterizations the remark asserts: (1) Theorem 10.3.10 as the
  remark recalls it, and (2) "a similar result can be proved" for strong bundles, which I read as
  asserting that the analogue holds.  "built into Definition 10.5.2" (the name "generalized strong
  bundle isomorphism" is given to the classes in (2)) is the content of V10_56 and is not repeated.
- (1) Setting: universe 0, ep-groupoids `X Y : EP.{0}`, the project's category `EPLoc` (`EP(E⁻¹)`,
  2021 Definition 10.3.12), the class `[d] = EPLoc.homMk d` of a project `Diagram`
  `X ←F A →Φ Y` (2021 p. 483), equivalences the project's `EpFunctor.IsEquivalence` (2021
  Definition 10.1.1).  "generalized isomorphism" (2021 Definition 10.3.9): an isomorphism of
  `EP(E⁻¹)`, Mathlib's `IsIso`.  "characterizes by diagrams with both legs equivalences": `f` is a
  generalized isomorphism iff `f = [d]` for a diagram `d` with `F` and `Φ` equivalences (read with
  "some representative"; `F` is an equivalence in every diagram, written out anyway).
- (2) Setting: universe 0, the project's `SEP.{0}`, `SDiagram`, the category `SEPLoc`
  (`SEP(F⁻¹)`, 2021 Definition 10.5.1, V10_55), `[D] = SEPLoc.homMk D`, strong bundle
  equivalences the project's `IsStrongBundleEquivalence` (2021 Definition 10.4.1).  A morphism of
  `SEP(F⁻¹)` is an isomorphism (`IsIso`) iff it is `[D]` for a diagram with both legs strong
  bundle equivalences.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_57
open Polyfold CategoryTheory

/-- Remark 10.5.3: generalized isomorphisms of ep-groupoids, and the isomorphisms of `SEP(F⁻¹)`,
are the classes of diagrams with both legs (strong bundle) equivalences. -/
def B : Prop :=
  (∀ (X Y : EP.{0})
      (f : (EPLocalization.EPLoc.of X : EPLocalization.EPLoc) ⟶ EPLocalization.EPLoc.of Y),
    IsIso f ↔
      ∃ d : EPLocalization.Diagram X Y, EPLocalization.EPLoc.homMk d = f ∧
        d.F.IsEquivalence ∧ d.Φ.IsEquivalence) ∧
  (∀ (A A' : SEP.{0})
      (f : (SBLocalization.SEPLoc.of A : SBLocalization.SEPLoc) ⟶ SBLocalization.SEPLoc.of A'),
    IsIso f ↔
      ∃ D : SBLocalization.SDiagram A A', SBLocalization.SEPLoc.homMk D = f ∧
        D.B.E.IsStrongBundleEquivalence A.E D.Φ.ϕ D.Φ.Φ ∧
        D.B.E.IsStrongBundleEquivalence A'.E D.Ψ.ϕ D.Ψ.Φ)

end RoundTrip.V10_57
