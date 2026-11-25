import Polyfold
/-! Blind formalization of V19_76 (the text's §19.7, Proposition 19.7.14, p. 914 of the Springer
2021 book; new in the 2021 edition).

Text: the map `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local homeomorphism, for a local covering
functor.

Choices:
- Setting (as in the blind V19_75): universe `0`: groupoidal categories `A`, `B`, a functor
  `P : A → B` which is a finite-to-one covering functor (Definition 19.7.1; vocabulary
  `IsFiniteToOneCovering`), and a basic construction `Bh` for `P` (Definition 19.7.11; vocabulary
  `CoveringBasicConstruction P`).  `Ψ̂, Ψ̂'` range over `Bh.hatU.Unif`.
- "for a local covering functor": I read this as naming the setting (`P` the covering functor of
  §19.7, Definition 19.7.1); I do not know a separate notion "local covering functor" in the
  text, and add no further hypothesis.  No metrizability, `HasClassUniformizers` or
  compatibility hypothesis is assumed; I did not use the vocabulary's `IsCompatible`.
- Topologies: `M(Ψ, Ψ')` carries `T_{Ψ,Ψ'}` (vocabulary `MB`); `M(Ψ̂, Ψ̂')` (vocabulary `MHat`,
  wrapped in the synonym `MT` to avoid the project's instance) carries the topology of Proposition
  19.7.13: the one making the canonical bijection `toFib : M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`,
  `(e, φ̂, e') ↦ (p(e, φ̂, e'), e)`, a homeomorphism, i.e. the topology induced by `toFib` (for a
  bijection the induced topology is the only such one).
- `p` = the vocabulary's `pB` (`(e, φ̂, e') ↦ (τ̂(e), P(φ̂), τ̂'(e'))`, (19.23)); "local
  homeomorphism" = `IsLocalHomeomorph`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V19_76
open Polyfold
open GroupoidalCategory

/-- `M(Ψ̂, Ψ̂')` as a bare type. -/
def MT {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : Type :=
  Bh.MHat x y

/-- The topology of Proposition 19.7.13: induced by `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`. -/
noncomputable instance {A B : GroupoidalCategory.{0}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
    (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif) : TopologicalSpace (MT Bh x y) :=
  TopologicalSpace.induced (Bh.toFib x y) inferInstance

/-- Proposition 19.7.14: `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` is a surjective local homeomorphism. -/
def B : Prop :=
  ∀ (A B : GroupoidalCategory.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr),
    IsFiniteToOneCovering P →
    ∀ (Bh : CoveringBasicConstruction P) (x y : Bh.hatU.Unif),
      Function.Surjective (fun h : MT Bh x y => Bh.pB x y h) ∧
      IsLocalHomeomorph (fun h : MT Bh x y => Bh.pB x y h)

end RoundTrip.V19_76
