import Polyfold
/-! Blind formalization of V10_56 (the text's Part II, §10.5, Definition 10.5.2, p. 506 of the
Springer 2021 book; 2017: Definition 10.15, p. 366): generalized strong bundle isomorphisms.

Text: a generalized strong bundle isomorphism is a class `[W ←Φ W'' →Ψ W']` of diagrams in which
both `Φ` and `Ψ` are strong bundle equivalences.

Choices:
- This item is a definition.  Setting: universe 0; the project's `SEP.{0}`, diagrams `SDiagram`,
  classes `SDiagram.cls`, generalized strong bundle maps `GenSBMap` (as in V10_51); strong bundle
  equivalences the project's `IsStrongBundleEquivalence` (2021 Definition 10.4.1) of the pair
  `(ϕ, Φ)` of a morphism of `SEP`.
- "a class `[D]` of diagrams in which both `Φ` and `Ψ` are strong bundle equivalences": I read it
  as "the class of some diagram `D` whose two legs are strong bundle equivalences" (not: every
  representative has this property).  B says that the project's `GenSBMap.IsGeneralizedIso` is
  this, for every generalized strong bundle map.  Both legs are written out, although `Φ` is a
  strong bundle equivalence in every diagram.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_56
open Polyfold CategoryTheory

/-- `f` is the class of a diagram whose two legs are strong bundle equivalences. -/
def IsGenIsoB {A A' : SEP.{0}} (f : SBLocalization.GenSBMap A A') : Prop :=
  ∃ D : SBLocalization.SDiagram A A', D.cls = f ∧
    D.B.E.IsStrongBundleEquivalence A.E D.Φ.ϕ D.Φ.Φ ∧
    D.B.E.IsStrongBundleEquivalence A'.E D.Ψ.ϕ D.Ψ.Φ

/-- Definition 10.5.2: the project's generalized strong bundle isomorphisms are the text's. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (f : SBLocalization.GenSBMap A A'), f.IsGeneralizedIso ↔ IsGenIsoB f

end RoundTrip.V10_56
