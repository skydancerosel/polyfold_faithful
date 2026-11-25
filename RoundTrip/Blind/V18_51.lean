import Polyfold
/-! Blind formalization of V18_51 (the text's §18.6, Theorem 18.6.1, pp. 860–861 of the Springer
2021 book; 2017: Theorem 18.8), the perturbation theorem.

Text: `C` tame with sc-smooth bump functions, `f` with compact `|S_f|`, `(N, U)` controlling
compactness, `h : C → (0, 1]` continuous: there is an sc⁺-multisection functor `Λ` with
(1) `N(Λ) < h`, (2) domain support in `C_U`, (3) `T(f, Λ)` onto on `supp(Λ ∘ f)`, (4) kernels in
general position; in particular `Λ ∘ f` is compact, tame and branched; `Λ` can be taken
structurable.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT
  `V` (`P : E → C`), a strong polyfold bundle construction `Q` (vocabulary).  Standing
  hypothesis `Q.HasStrongBundleUniformizers` (`F̄(α) ≠ ∅`).
- "tame" = `S.IsTame`; "sc-smooth bump functions" = `S.AdmitsModelBumpFunctions`
  (Definition 18.4.1).
- `f`: an sc-Fredholm section functor (`Q.IsScFredholmSectionFunctor`, Definition 18.1.1; the
  text's standing `f`, implicit in the quoted statement) with compact `|S_f|`
  (`f.HasCompactModuliSpace`, Definition 18.2.1 (1)).
- `(N, U)` controls compactness (Definition 18.2.3): `N` an auxiliary norm
  (`Q.IsAuxNormBook`, Definition 18.1.7 as printed) and `f.ControlsCompactness N U` (the
  vocabulary's: `U ⊆ |C|` open, `|S_f| ⊆ U`, `cl{z ∈ U | |N|∘|f|(z) ≤ 1}` compact).  I did not
  require `N` reflexive (the quoted statement does not).
- `h : C → (0, 1]` continuous = `S.IsContinuousFunctionFunctor h` with `0 < h ≤ 1`.
- `Λ : E → ℚ⁺`: `Q.IsScPlusMultisectionFunctor` (Definition 18.3.1).
  (1) `N(Λ)(α) < h(α)` for every `α`, `N(Λ)` = the vocabulary's `pointwiseNormFunctor`.
  (2) "domain support in `C_U`" = `|dom-supp(Λ)| ⊆ U` (`orbitDomSupp`, the closure in `|C|`).
  (3) = `Q.IsTransversalFunctor f Λ`, (4) = `Q.IsInGeneralPositionFunctor f Λ` (the
  vocabulary's model-free forms of these two clauses; trusted from their docstrings).
- `Θ = Λ ∘ f : C → ℚ⁺`, `Θ(α) = Λ(f(α))`.  "compact" = `C.IsCompactBranched Θ`
  (Definition 17.5.4 (1), `|supp Θ|` compact); "tame" = `S.IsTameSubcategory Θ`
  (Definition 17.5.4 (3)); "branched" = `S.IsBranchedSubcategory Θ` (Definition 17.5.1).
- "Λ can be taken structurable": a single `Λ` with all the above and `Q.IsStructurableFunctor Λ`
  (this implies the version without structurability).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_51
open Polyfold

/-- Theorem 18.6.1: transversal perturbation by a (structurable) sc⁺-multisection functor. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S),
    Q.HasStrongBundleUniformizers → S.IsTame → S.AdmitsModelBumpFunctions →
    ∀ (f : V.SectionFunctor), Q.IsScFredholmSectionFunctor f → f.HasCompactModuliSpace →
    ∀ (N : V.EObj → ENNReal) (U : Set C.toGroupoidStr.OrbitSpace),
      Q.IsAuxNormBook N → f.ControlsCompactness N U →
    ∀ (h : C.Obj → ℝ), S.IsContinuousFunctionFunctor h → (∀ α, 0 < h α ∧ h α ≤ 1) →
    ∃ Λ : V.EObj → ℚ≥0,
      Q.IsScPlusMultisectionFunctor Λ ∧
      -- (1)
      (∀ α, GCT.VectorBundle.pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) ∧
      -- (2)
      GCT.VectorBundle.orbitDomSupp Λ ⊆ U ∧
      -- (3)
      Q.IsTransversalFunctor f Λ ∧
      -- (4)
      Q.IsInGeneralPositionFunctor f Λ ∧
      -- `Θ = Λ ∘ f` is compact, tame and branched
      C.IsCompactBranched (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) ∧
      S.IsTameSubcategory (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) ∧
      S.IsBranchedSubcategory (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) ∧
      -- structurable
      Q.IsStructurableFunctor Λ

end RoundTrip.V18_51
