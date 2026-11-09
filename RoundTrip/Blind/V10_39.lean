import Polyfold
/-! Blind formalization of V10_39 (the Springer 2021 book, Part II, §10.3, Definition 10.3.7,
p. 488; 2017: Definition 10.7, p. 351): the map `|[d]|` of a class of diagrams.

Text: `|[d]| = |Φ| ∘ |F|⁻¹` for any representative; a homeomorphism if `Φ` is an equivalence.

Choices:
- This item is a definition with one embedded claim.  B says (1) that the project's
  `Diagram.orbitMapQ` (whose docstring cites Definition 10.3.7) takes the value `|Φ| ∘ |F|⁻¹` at
  the class `⟦d⟧` of every representative `d` (the class: the quotient by the project's
  `Diagram.setoid X Y`, compared with "having a common refinement" in
  `RoundTrip/Blind/V10_37.lean`), and (2) that `|[d]|` is a homeomorphism (Mathlib's
  `IsHomeomorph`) whenever the `Φ` of the representative `d` is an equivalence
  (`EpFunctor.IsEquivalence`, Definition 10.1.1).  "For any representative" is the quantifier
  over all `d` with the class `⟦d⟧`.
- The project also has `EPLoc.orbitMap` on the morphisms of `EPLoc` (the same quotient type); B
  is stated for `Diagram.orbitMapQ` only.
- Setting and `|d| = |Φ| ∘ |F|⁻¹` (my `orbB`, with `|F|⁻¹` the inverse of the homeomorphism
  `|F|` of Definition 10.1.1 (2)) as in `RoundTrip/Blind/V10_38.lean`: `EP.{u}`, any universe.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_39
open Polyfold Polyfold.EPLocalization

universe u

/-- `|d| = |Φ| ∘ |F|⁻¹ : |X| → |Y|`, `|F|` being a homeomorphism as `F` is an equivalence. -/
noncomputable def orbB {X Y : EP.{u}} (d : Diagram X Y) : X.X.OrbitSpace → Y.X.OrbitSpace :=
  d.Φ.orbitMap ∘
    (IsHomeomorph.homeomorph d.F.orbitMap d.isEquivalence_F.isHomeomorph_orbitMap).symm

/-- `|[d]| = |Φ| ∘ |F|⁻¹` for every representative `d`, and it is a homeomorphism when `Φ` is an
equivalence. -/
def B : Prop :=
  ∀ (X Y : EP.{u}) (d : Diagram X Y),
    Diagram.orbitMapQ (Quotient.mk (Diagram.setoid X Y) d) = orbB d ∧
    (d.Φ.IsEquivalence → IsHomeomorph (Diagram.orbitMapQ (Quotient.mk (Diagram.setoid X Y) d)))

end RoundTrip.V10_39
