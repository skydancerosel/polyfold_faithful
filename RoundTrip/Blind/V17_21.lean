import Polyfold
/-! Blind formalization of V17_21 (the text's §17.1, Theorem 17.1.18, p. 756 of the Springer 2021
book; 2017: Theorem 17.2).

Text: for covering families `Ψ, Ψ', Ψ''`: `f_{Ψ,Ψ'}` is a generalized isomorphism with
`f_{Ψ,Ψ} = 1`, `f_{Ψ',Ψ''} ∘ f_{Ψ,Ψ'} = f_{Ψ,Ψ''}`, `|Γ_{Ψ'}| ∘ |f_{Ψ,Ψ'}| = |Γ_Ψ|`, and
`|f_{Ψ,Ψ'}|` is a homeomorphism; each `(X_Ψ, |Γ_Ψ|)` is a weak polyfold structure.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` (Definition 17.1.1: groupoidal category with a
  metrizable topology on `|C|`) and a polyfold structure `S : C.PolyfoldConstruction`
  (Definition 17.1.8, `(F, M)`); "covering family" = the project's `S.CoveringFamily` (a family
  `(Ψ_λ)_{λ ∈ Λ}` of uniformizers of `F` whose footprints cover `|C|`, `#print`ed).  No further
  hypothesis (the text has none beyond `(C, F, M)` being a polyfold).
- `X_Ψ` = the project's `S.modelEP c.Ψ` (the ep-groupoid of (17.7), Theorem 17.1.14);
  `Γ_Ψ` = `S.modelFunctor c.Ψ` (the functor (17.10)); `f_{Ψ,Ψ'}` = the project's
  `S.comparison c c'` (the generalized map `[d]` of (17.14)/(17.15)).  These are the text's
  constructions, which I take from the vocabulary rather than rebuilding Chapter 17.
- "generalized isomorphism" = `EPLoc.IsGeneralizedIso` (Definition 10.3.9); `1` = `𝟙` in
  `EP(E⁻¹)`; `∘` = Mathlib's `≫` in reversed order; `|f|` = `EPLoc.orbitMap` (Definition 10.3.7),
  `|Γ_Ψ|` = `GroupoidFunctor.orbitMap`.
- "`(X_Ψ, |Γ_Ψ|)` is a weak polyfold structure" (Definition 17.1.17: an ep-groupoid with a
  homeomorphism `|X| → Z`): read as `|Γ_Ψ| : |X_Ψ| → |C|` is a homeomorphism (`X_Ψ` being an
  ep-groupoid is built into `modelEP`; `|C|` is metrizable, hence paracompact).
- B is the conjunction of all six claims, for all covering families `c c' c''`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_21
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- `|Γ_Ψ| : |X_Ψ| → |C|`. -/
noncomputable def orbitGamma {C : GCT.{0}} (S : C.PolyfoldConstruction) (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.OrbitSpace → C.toGroupoidStr.OrbitSpace :=
  (S.modelFunctor c.Ψ).orbitMap

/-- Theorem 17.1.18: the canonical generalized isomorphisms `f_{Ψ,Ψ'}` between the models. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (c c' c'' : S.CoveringFamily),
    EPLoc.IsGeneralizedIso (S.comparison c c') ∧
    S.comparison c c = 𝟙 _ ∧
    S.comparison c c' ≫ S.comparison c' c'' = S.comparison c c'' ∧
    orbitGamma S c' ∘ EPLoc.orbitMap (S.comparison c c') = orbitGamma S c ∧
    IsHomeomorph (EPLoc.orbitMap (S.comparison c c')) ∧
    IsHomeomorph (orbitGamma S c)

end RoundTrip.V17_21
