import Polyfold
/-! Blind formalization of V17_113 (the text's Part II, §17.6, Theorem 17.6.7 and (17.90), p. 823
of the Springer 2021 book; 2017: Theorem 17.7).

Text: Stokes: `∫_{Θ̂} d[ω] = ∫_{∂Θ̂} [ω]` (17.90); the proof is immediate from the ep-groupoid
case.

Choices:
- Setting as in my V17_110 / V17_112: universe `0`, `C : GCT.{0}`,
  `S : C.PolyfoldConstruction`, `Θ̂ : S.OrientedSubcategory`, compact
  (`C.IsCompactBranched Θ`), tame, oriented, of dimension `n` (`Θ̂.IsTameOrientedVia c n` on the
  model of the covering family used), `[ω] ∈ Ω^{n-1}_∞(C)` = `S.catFormsInfty m` with `n = m + 1`
  (degree `n - 1` presupposes `n ≥ 1`).
- `d : Ω^m_∞(C) → Ω^{m+1}_∞(C)` = the project's `S.catFormsInftyD m` (p. 820,
  `d[ω] = [Γ_*d(Γ^*ω)]`).
- `∫_{Θ̂}` and `∫_{∂Θ̂}`: the text defines them on the model of a covering family ((17.89),
  Theorem 17.6.6) and shows the independence (Theorems 17.6.4, 17.6.6).  I state (17.90) on the
  model of EVERY covering family `Ψ` on which the hypotheses hold: the project's
  `Θ̂.integralVia c …` and `Θ̂.boundaryIntegralVia c …` (for `m ≥ 1`) /
  `Θ̂.boundaryIntegralDim1Via c …` (for `n = 1`, `0`-dimensional boundary).  B is the
  conjunction of the two cases.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_113
open Polyfold

/-- Theorem 17.6.7 (Stokes, (17.90)): `∫_{Θ̂} d[ω] = ∫_{∂Θ̂} [ω]` for `Θ̂` compact, tame, oriented
of dimension `m + 1` and `[ω] ∈ Ω^m_∞(C)`, on the model of every covering family. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (A : S.OrientedSubcategory)
    (hc : C.IsCompactBranched A.Θ),
    (∀ (m : ℕ) (hm : 0 < m) (c : S.CoveringFamily) (ht : A.IsTameOrientedVia c (m + 1))
      (ω : S.catFormsInfty m),
      A.integralVia c (Nat.succ_pos m) hc ht (S.catFormsInftyD m ω) =
        A.boundaryIntegralVia c hm hc ht ω) ∧
    (∀ (c : S.CoveringFamily) (ht : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0),
      A.integralVia c (Nat.succ_pos 0) hc ht (S.catFormsInftyD 0 ω) =
        A.boundaryIntegralDim1Via c hc ht ω)

end RoundTrip.V17_113
