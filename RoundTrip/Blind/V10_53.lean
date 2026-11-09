import Polyfold
/-! Blind formalization of V10_53 (the text's Part II, §10.5, the diagrams (10.24) and `|𝒟|`,
pp. 504–505 of the Springer 2021 book; 2017: Remark 10.5, p. 365).

Text: the symbolic diagram (10.24) (`[D] : W → W'` over `[d] : X → X'`, with the projections
`P`, `P'`) becomes, on orbit spaces, the commutative square `|P'| ∘ |[D]| = |[d]| ∘ |P|`.

Choices:
- Setting: universe 0, the project's `SEP.{0}`, `SDiagram`, `GenSBMap` (as in V10_51, V10_52).
  I state the square for the class `[D]` of an arbitrary diagram `D` (every generalized strong
  bundle map is one); `[d]` is the class in `EP(E⁻¹)` of the diagram of the bases covered by `D`
  (`baseDiagB`, mine, as in V10_52: `X ←φ X'' →ψ X'`).
- `|[D]| : |W| → |W'|` is the project's `GenSBMap.orbitMap` (V10_52 compares it with
  `|Ψ| ∘ |Φ|⁻¹`), `|[d]| : |X| → |X'|` the project's `EPLoc.orbitMap` (2021 Definition 10.3.7,
  `|Φ| ∘ |F|⁻¹`); orbit spaces with the project's projections `π`.  `|P| : |W| → |X|` is
  `|w| ↦ |P(w)|`.
- The square is stated pointwise without naming `|P|`, `|P'|`: if `|[D]|(|w|) = |w'|` then
  `|[d]|(|P(w)|) = |P'(w')|` (equivalent, `π` being onto).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_53
open Polyfold CategoryTheory

/-- The diagram `d : X ←φ X'' →ψ X'` of the base ep-groupoids covered by
`D : W ←Φ W'' →Ψ W'`. -/
def baseDiagB {A A' : SEP.{0}} (D : SBLocalization.SDiagram A A') :
    EPLocalization.Diagram A.baseEP A'.baseEP :=
  ⟨D.B.baseEP, D.Φ.ϕ,
    EpStrongBundle.IsStrongBundleEquivalence.isEquivalence_base D.isEquivalence_Φ, D.Ψ.ϕ⟩

/-- The square (10.24) on orbit spaces: `|P'| ∘ |[D]| = |[d]| ∘ |P|`. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (D : SBLocalization.SDiagram A A') (w : A.W) (w' : A'.W),
    D.cls.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w' →
    EPLocalization.EPLoc.orbitMap (EPLocalization.EPLoc.homMk (baseDiagB D)) (A.X.π (A.P w)) =
      A'.X.π (A'.P w')

end RoundTrip.V10_53
