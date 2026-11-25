import Polyfold
/-! Blind formalization of V17_112 (the text's Part II, §17.6, Theorem 17.6.6, p. 822 of the
Springer 2021 book; 2017: Theorem 17.6).

Text: the boundary integral `∫_{∂Θ̂}` of `[ω] ∈ Ω^{n-1}_∞(C)` does not depend on the covering
family.

Choices:
- Setting as in my V17_110: universe `0`, `C : GCT.{0}`, `S : C.PolyfoldConstruction`,
  `Θ̂ : S.OrientedSubcategory`, `[ω] ∈ Ω^{n-1}_∞(C)` = `S.catFormsInfty (n - 1)`.  The
  standing hypotheses of §17.6 (carried over from Theorem 17.6.4): `Θ̂` compact
  (`C.IsCompactBranched Θ`), tame, oriented, of dimension `n` on the model of the covering
  family used (`Θ̂.IsTameOrientedVia c n`).  Degree `n - 1` presupposes `n ≥ 1`; I write
  `n = m + 1`.
- "the boundary integral" over a model `X_Ψ`: `∫_{∂(Γ^*Θ̂)} [ω_Ψ]`, the project's
  `Θ̂.boundaryIntegralVia c …` for `m ≥ 1` and `Θ̂.boundaryIntegralDim1Via c …` for `n = 1`
  (the `0`-dimensional boundary, a weighted signed count); these are the text's definitions
  (p. 822), taken from the vocabulary.  B is the conjunction of the two cases.
- "does not depend on the covering family": any two covering families on whose models `Θ̂` is
  compact tame oriented of dimension `n` give the same value.  (That such a family can be
  replaced by any other is part of my V17_110.)
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_112
open Polyfold

/-- Theorem 17.6.6: the boundary integral of `[ω] ∈ Ω^{n-1}_∞(C)` over `∂Θ̂`, computed on the
model of a covering family, does not depend on it (cases `n ≥ 2` and `n = 1`). -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (A : S.OrientedSubcategory)
    (hc : C.IsCompactBranched A.Θ),
    (∀ (m : ℕ) (hm : 0 < m) (c c' : S.CoveringFamily) (ht : A.IsTameOrientedVia c (m + 1))
      (ht' : A.IsTameOrientedVia c' (m + 1)) (ω : S.catFormsInfty m),
      A.boundaryIntegralVia c hm hc ht ω = A.boundaryIntegralVia c' hm hc ht' ω) ∧
    (∀ (c c' : S.CoveringFamily) (ht : A.IsTameOrientedVia c (0 + 1))
      (ht' : A.IsTameOrientedVia c' (0 + 1)) (ω : S.catFormsInfty 0),
      A.boundaryIntegralDim1Via c hc ht ω = A.boundaryIntegralDim1Via c' hc ht' ω)

end RoundTrip.V17_112
