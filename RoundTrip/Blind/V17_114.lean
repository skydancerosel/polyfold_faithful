import Polyfold
/-! Blind formalization of V17_114 (the text's Part II, §17.6, Theorem 17.6.8, p. 823 of the
Springer 2021 book; new in the 2021 edition).

Text: under (LUC), the effective integral over a compact tame oriented `Θ̂` does not depend on the
covering family.

Choices:
- Setting as in my V17_110: universe `0`, `C : GCT.{0}`, `S : C.PolyfoldConstruction`,
  `Θ̂ : S.OrientedSubcategory`, compact (`C.IsCompactBranched Θ`), tame, oriented, of dimension
  `n` on the model of the covering family used (`Θ̂.IsTameOrientedVia c n`),
  `[ω] ∈ Ω^n_∞(C)` = `S.catFormsInfty n`.
- "(LUC)" for `C` = the project's `S.IsLUC` (Definition 17.1.22: some model `X_Ψ` has (LUC),
  Definition 7.2.18).
- "the effective integral" over a model: `∮_{Θ̂_Ψ} [ω_Ψ]` (17.91), the project's
  `Θ̂.integralEffVia hL c …` (the text's definition, taken from the vocabulary).  Available for
  `n ≥ 1` only, so B covers `n ≥ 1`.
- "does not depend on the covering family": any two covering families on whose models `Θ̂` is
  tame oriented of dimension `n` give the same value.  (That the hypotheses pass from one
  covering family to any other is part of my V17_110.)
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_114
open Polyfold

/-- Theorem 17.6.8: under (LUC), the effective integral of `[ω] ∈ Ω^n_∞(C)` over a compact,
tame, oriented `n`-dimensional `Θ̂`, computed on a model, does not depend on the covering
family. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hL : S.IsLUC) (A : S.OrientedSubcategory)
    (n : ℕ) (hn : 0 < n) (hc : C.IsCompactBranched A.Θ)
    (c c' : S.CoveringFamily) (ht : A.IsTameOrientedVia c n)
    (ht' : A.IsTameOrientedVia c' n) (ω : S.catFormsInfty n),
    A.integralEffVia hL c hn hc ht ω = A.integralEffVia hL c' hn hc ht' ω

end RoundTrip.V17_114
