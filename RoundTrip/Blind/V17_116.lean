import Polyfold
/-! Blind formalization of V17_116 (the text's Part II, §17.6, Theorem 17.6.10 and (17.92),
p. 824 of the Springer 2021 book; new in the 2021 edition).

Text: effective Stokes under (LUC): (17.92), `∮_{Θ̂} d[ω] = ∮_{∂Θ̂} [ω]`.

Choices:
- Setting as in my V17_113: universe `0`, `C : GCT.{0}`, `S : C.PolyfoldConstruction` with
  (LUC) (`S.IsLUC`, Definition 17.1.22), `Θ̂ : S.OrientedSubcategory`, compact
  (`C.IsCompactBranched Θ`), tame, oriented, of dimension `n = m + 1` on the model of the
  covering family used (`Θ̂.IsTameOrientedVia c (m + 1)`), `[ω] ∈ Ω^m_∞(C)` =
  `S.catFormsInfty m`, `d` = `S.catFormsInftyD m`.
- The statement of (17.92) is not quoted in my source beyond "effective Stokes"; I read it as the
  effective analogue of (17.90): `∮_{Θ̂} d[ω] = ∮_{∂Θ̂} [ω]`.
- `∮_{Θ̂}` = the project's `Θ̂.integralEffVia hL c …` ((17.91)); `∮_{∂Θ̂}` =
  `Θ̂.boundaryIntegralEffVia hL c …` (`m ≥ 1`) / `Θ̂.boundaryIntegralEffDim1Via hL c …`
  (`n = 1`), all computed on the model of a covering family; I state (17.92) on the model of
  EVERY covering family on which the hypotheses hold.  B is the conjunction of the two cases.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_116
open Polyfold

/-- Theorem 17.6.10 (effective Stokes, (17.92)): under (LUC), `∮_{Θ̂} d[ω] = ∮_{∂Θ̂} [ω]` for `Θ̂`
compact, tame, oriented of dimension `m + 1` and `[ω] ∈ Ω^m_∞(C)`, on every model. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hL : S.IsLUC) (A : S.OrientedSubcategory)
    (hc : C.IsCompactBranched A.Θ),
    (∀ (m : ℕ) (hm : 0 < m) (c : S.CoveringFamily) (ht : A.IsTameOrientedVia c (m + 1))
      (ω : S.catFormsInfty m),
      A.integralEffVia hL c (Nat.succ_pos m) hc ht (S.catFormsInftyD m ω) =
        A.boundaryIntegralEffVia hL c hm hc ht ω) ∧
    (∀ (c : S.CoveringFamily) (ht : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0),
      A.integralEffVia hL c (Nat.succ_pos 0) hc ht (S.catFormsInftyD 0 ω) =
        A.boundaryIntegralEffDim1Via hL c hc ht ω)

end RoundTrip.V17_116
