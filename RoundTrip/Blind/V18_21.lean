import Polyfold
/-! Blind formalization of V18_21 (the text's Part II, §18.1, Theorem 18.1.12, p. 848 of the
Springer 2021 book; 2017: Theorem 18.2).

Text: (1) auxiliary norms exist; (2) with reflexive `(0, 1)`-fibres, every auxiliary norm lies
between two reflexive ones; (3) `C` tame: an auxiliary norm over `∂C` extends to `E`, reflexive
if it is and the fibres are.

Choices:
- Setting: universe `0`; a GCT `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT
  `V` (`P : E → C`) with a strong polyfold bundle construction
  `Q : V.StrongPolyfoldBundleConstruction S`.  Auxiliary norms are functions `N : E → [0, ∞]`
  (`V.EObj → ENNReal`).
- "auxiliary norm" (Definition 18.1.7) and "reflexive auxiliary norm" (Definition 18.1.11): the
  project's `Q.IsAuxNormFunctor` / `Q.IsReflexiveAuxNormFunctor` (`#print`ed: `N` is an auxiliary
  norm, resp. reflexive auxiliary norm, in the model `W_Ψ̄ → X_Ψ` of every covering family of
  strong bundle uniformizers; docstrings: `N` a functor, `+∞` exactly off `E_{0,1}`, and `N ∘ Γ̄`
  an auxiliary norm of the strong bundle over the ep-groupoid, Definitions 12.2.1, 12.2.10).
  This is Definition 18.1.7 read through the text's Lemma 18.1.8 (and Definition 18.1.11 read in
  the models, as the text does before Theorem 18.1.12).  I did not use the literal form
  `IsAuxNormBook` (Definition 18.1.7 as printed, without the continuity of Definition 12.2.1),
  nor `IsAuxNormDirect` / `IsReflexiveAuxNormDirect`; if the literal definition is meant, (1)–(3)
  should be restated with it.
- "reflexive `(0, 1)`-fibres": `Q.HasReflexiveFibers` (Definition 18.1.9 read in the models).
- (2) "lies between": `N₁ ≤ N ≤ N₂` pointwise on `E`, `N₁`, `N₂` reflexive (as in Theorem
  12.2.11).
- (3) "`C` tame": `S.IsTame`.  "an auxiliary norm over `∂C`": the project's
  `Q.IsBoundaryAuxNormIn c N` (docstring: Theorem 18.1.12 (3) read in the covering model `c`:
  `N` constant along morphisms over `∂C`, `+∞` exactly off `W_{0,1}` over `∂X`, `N ∘ Γ̄` an
  auxiliary norm of `W|∂X`), for SOME covering family `c` (the notion should not depend on `c`;
  `∃` is the weaker hypothesis); reflexive: `Q.IsReflexiveBoundaryAuxNormIn c N`.  "extends to
  `E`": an auxiliary norm `N'` (reflexive in the second case) with `N' e = N e` for every `e`
  over `∂C` (`V.base e ∈ S.boundarySet`, Definition 17.1.30).  "reflexive if it is and the fibres
  are": the reflexive case assumes `Q.HasReflexiveFibers` and the tameness.
- B is the conjunction of (1), (2), (3) and the reflexive case of (3).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_21
open Polyfold

/-- Theorem 18.1.12: existence of auxiliary norms, two-sided reflexive bounds, and extension of
(reflexive) auxiliary norms from `∂C` over a tame polyfold. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S),
    -- (1)
    (∃ N : V.EObj → ENNReal, Q.IsAuxNormFunctor N) ∧
    -- (2)
    (Q.HasReflexiveFibers → ∀ N : V.EObj → ENNReal, Q.IsAuxNormFunctor N →
      ∃ N₁ N₂ : V.EObj → ENNReal, Q.IsReflexiveAuxNormFunctor N₁ ∧
        Q.IsReflexiveAuxNormFunctor N₂ ∧ ∀ e : V.EObj, N₁ e ≤ N e ∧ N e ≤ N₂ e) ∧
    -- (3)
    (S.IsTame → ∀ N : V.EObj → ENNReal, (∃ c : Q.BundleCoveringFamily, Q.IsBoundaryAuxNormIn c N) →
      ∃ N' : V.EObj → ENNReal, Q.IsAuxNormFunctor N' ∧
        ∀ e : V.EObj, V.base e ∈ S.boundarySet → N' e = N e) ∧
    -- (3), reflexive case
    (S.IsTame → Q.HasReflexiveFibers → ∀ N : V.EObj → ENNReal,
      (∃ c : Q.BundleCoveringFamily, Q.IsReflexiveBoundaryAuxNormIn c N) →
      ∃ N' : V.EObj → ENNReal, Q.IsReflexiveAuxNormFunctor N' ∧
        ∀ e : V.EObj, V.base e ∈ S.boundarySet → N' e = N e)

end RoundTrip.V18_21
