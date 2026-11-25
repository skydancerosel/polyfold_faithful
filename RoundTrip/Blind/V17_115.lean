import Polyfold
/-! Blind formalization of V17_115 (the text's Part II, §17.6, Theorem 17.6.9, p. 824 of the
Springer 2021 book; new in the 2021 edition).

Text: under (LUC), the effective boundary integral is well defined.

Choices:
- Setting as in my V17_112: universe `0`, `C : GCT.{0}`, `S : C.PolyfoldConstruction` with
  (LUC) (`S.IsLUC`, Definition 17.1.22), `Θ̂ : S.OrientedSubcategory`, compact
  (`C.IsCompactBranched Θ`), tame, oriented, of dimension `n = m + 1` on the model of the
  covering family used (`Θ̂.IsTameOrientedVia c (m + 1)`), `[ω] ∈ Ω^m_∞(C)` =
  `S.catFormsInfty m`.
- "the effective boundary integral" over a model: `∮_{∂(Γ^*Θ̂)} [ω_Ψ]`, the project's
  `Θ̂.boundaryIntegralEffVia hL c …` (`m ≥ 1`) and `Θ̂.boundaryIntegralEffDim1Via hL c …`
  (`n = 1`), the text's definitions taken from the vocabulary.  B is the conjunction of the two
  cases.
- "well defined": read, as for Theorem 17.6.6, as "does not depend on the covering family": any
  two covering families on whose models the hypotheses hold give the same value.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_115
open Polyfold

/-- Theorem 17.6.9: under (LUC), the effective boundary integral of `[ω] ∈ Ω^{n-1}_∞(C)` over
`∂Θ̂`, computed on a model, does not depend on the covering family (cases `n ≥ 2`, `n = 1`). -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hL : S.IsLUC) (A : S.OrientedSubcategory)
    (hc : C.IsCompactBranched A.Θ),
    (∀ (m : ℕ) (hm : 0 < m) (c c' : S.CoveringFamily) (ht : A.IsTameOrientedVia c (m + 1))
      (ht' : A.IsTameOrientedVia c' (m + 1)) (ω : S.catFormsInfty m),
      A.boundaryIntegralEffVia hL c hm hc ht ω = A.boundaryIntegralEffVia hL c' hm hc ht' ω) ∧
    (∀ (c c' : S.CoveringFamily) (ht : A.IsTameOrientedVia c (0 + 1))
      (ht' : A.IsTameOrientedVia c' (0 + 1)) (ω : S.catFormsInfty 0),
      A.boundaryIntegralEffDim1Via hL c hc ht ω = A.boundaryIntegralEffDim1Via hL c' hc ht' ω)

end RoundTrip.V17_115
