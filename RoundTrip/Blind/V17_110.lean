import Polyfold
/-! Blind formalization of V17_110 (the text's Part II, §17.6, Theorem 17.6.4 and (17.89), p. 821
of the Springer 2021 book; 2017: Theorem 17.5).

Text: for `[ω] ∈ Ω^n_∞(C)` and `Θ̂` tame, oriented, compact, of dimension `n`, the integral
(17.89) over a model does not depend on the covering family.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, an oriented branched ep⁺-subcategory
  `Θ̂ = (Θ, T̂_Θ) : S.OrientedSubcategory` (pp. 820–821; the project's type, which carries the
  orientation on every model `X_Ψ`, compatible with the canonical generalized isomorphisms), and
  `[ω] ∈ Ω^n_∞(C)` = the project's `S.catFormsInfty n` (p. 820: one class `[ω_Ψ]` for every
  covering family, compatible with the `f_{Ψ,Ψ'}^*`).
- "compact" = the project's `C.IsCompactBranched Θ` (Definition 17.5.3 (1): `|supp Θ|` compact
  in `|C|`).  "tame, oriented, of dimension `n`" on the model of a covering family `Ψ` = the
  project's `Θ̂.IsTameOrientedVia c n`.
- "the integral (17.89) over a model": `∫_{Θ̂_Ψ} [ω_Ψ]`, the project's `Θ̂.integralVia c …`
  (the text's definition (17.89), computed on the model `X_Ψ`; taken from the vocabulary, since
  the vocabulary has no Chapter 11 integral of a class `[ω_Ψ]` that I could compose myself).  It
  is only available for `n ≥ 1`, so B covers `n ≥ 1` (the text does not exclude `n = 0`; that
  case is not formalized).
- "does not depend on the covering family": (a) the hypotheses needed for (17.89) hold on every
  model: if `Θ̂` is tame oriented of dimension `n` on the model of one covering family (the
  text's "tame" is Definition 17.5.3 (2), "for a suitable covering family"), then on every one;
  (b) any two covering families give the same integral.  Part (a) is the presupposition that the
  integral over every model is defined; drop it if the text means only (b).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_110
open Polyfold

/-- Theorem 17.6.4: the integral (17.89) of `[ω] ∈ Ω^n_∞(C)` over a compact, tame, oriented
`n`-dimensional `Θ̂`, computed on the model of a covering family, does not depend on it. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (A : S.OrientedSubcategory) (n : ℕ)
    (hn : 0 < n) (hc : C.IsCompactBranched A.Θ),
    ((∃ c₀ : S.CoveringFamily, A.IsTameOrientedVia c₀ n) →
      ∀ c : S.CoveringFamily, A.IsTameOrientedVia c n) ∧
    ∀ (c c' : S.CoveringFamily) (ht : A.IsTameOrientedVia c n)
      (ht' : A.IsTameOrientedVia c' n) (ω : S.catFormsInfty n),
      A.integralVia c hn hc ht ω = A.integralVia c' hn hc ht' ω

end RoundTrip.V17_110
