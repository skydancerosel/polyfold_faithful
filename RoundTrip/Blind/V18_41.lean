import Polyfold
/-! Blind formalization of V18_41 (the text's §18.4, Theorem 18.4.4, pp. 855–856 of the Springer
2021 book; 2017: Theorem 18.7), the ∂-extension theorem.

Text: `C` tame with sc-smooth partitions of unity, `N` an auxiliary norm, `Λ` structurable over
`∂C` with domain support in an open `U`, `β` continuous with support in `U` and `N(Λ) < β` over
the boundary: there is a structurable `Λ'` with `N(Λ') ≤ β`, domain support in `U`, equal to `Λ`
over `∂C`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT
  `V` (`P : E → C`) and a strong polyfold bundle construction `Q` (vocabulary).  Standing
  hypothesis `Q.HasStrongBundleUniformizers` (`F̄(α) ≠ ∅`; the text's uniformizers cover).
- "tame" = `S.IsTame` (Definition 17.1.8); "admits sc-smooth partitions of unity" =
  `S.AdmitsModelPartitionsOfUnity` (Definition 18.4.1; not the vocabulary's
  `HasModelMPolyfoldPartitionsOfUnity`, which is labelled as the form Theorem 14.1.9 uses).
- "auxiliary norm" = `Q.IsAuxNormBook` (Definition 18.1.7 as printed).  The vocabulary also has
  `IsAuxNormDirect` (with continuity of `|N|`) and `IsAuxNormFunctor` (through Lemma 18.1.8); I
  did not use them.
- `Λ : E|∂C → ℚ⁺` is a function `E → ℚ≥0` whose values over `∂C` (objects of `S.boundarySet`)
  matter; "structurable over `∂C`" = `Q.IsBoundaryStructurableFunctor`; its domain support is the
  vocabulary's `orbitBoundaryDomSupp` (closure in `|C|` of the classes of `α ∈ ∂C` carrying some
  `e ≠ 0` with `Λ(α, e) > 0`), required `⊆ U`, `U ⊆ |C|` open.
- `β : C → [0, ∞)`: a continuous functor (`S.IsContinuousFunctionFunctor`: constant along
  morphisms, continuous in every uniformizer) with `β ≥ 0`; "support in `U`": the closure in
  `|C|` of `{|α| : β(α) ≠ 0}` lies in `U`.
- `N(Λ)(α) = max{N(α, e) | Λ(α, e) > 0}` = the vocabulary's `pointwiseNormFunctor` (a supremum
  in `[0, ∞]`); "`N(Λ) < β` over the boundary": `N(Λ)(α) < β(α)` for every `α ∈ ∂C`.
- Conclusion: `Λ' : E → ℚ⁺` structurable (`Q.IsStructurableFunctor`, Definition 18.3.3),
  `N(Λ')(α) ≤ β(α)` for all `α`, `|dom-supp(Λ')| ⊆ U` (`orbitDomSupp`), and `Λ'(e) = Λ(e)` for
  every `e` over `∂C`.
- Possible issue: read literally, `N(Λ)(α) < β(α)` at a boundary object where `Λ(α, ·)` is the
  zero section gives `0 < β(α)`; so the hypotheses force `β > 0` on all of `∂C`, hence `|∂C| ⊂ U`.
  I formalize it literally anyway.
-/
namespace RoundTrip.V18_41
open Polyfold

/-- Theorem 18.4.4: extension of a structurable sc⁺-multisection functor from `∂C`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S),
    Q.HasStrongBundleUniformizers → S.IsTame → S.AdmitsModelPartitionsOfUnity →
    ∀ (N : V.EObj → ENNReal), Q.IsAuxNormBook N →
    ∀ (Λ : V.EObj → ℚ≥0), Q.IsBoundaryStructurableFunctor Λ →
    ∀ (U : Set C.toGroupoidStr.OrbitSpace), IsOpen U →
      GCT.VectorBundle.orbitBoundaryDomSupp S Λ ⊆ U →
    ∀ (β : C.Obj → ℝ), S.IsContinuousFunctionFunctor β → (∀ α, 0 ≤ β α) →
      closure (C.toGroupoidStr.π '' {α | β α ≠ 0}) ⊆ U →
      (∀ α ∈ S.boundarySet,
        GCT.VectorBundle.pointwiseNormFunctor N Λ α < ENNReal.ofReal (β α)) →
    ∃ Λ' : V.EObj → ℚ≥0,
      Q.IsStructurableFunctor Λ' ∧
      (∀ α, GCT.VectorBundle.pointwiseNormFunctor N Λ' α ≤ ENNReal.ofReal (β α)) ∧
      GCT.VectorBundle.orbitDomSupp Λ' ⊆ U ∧
      (∀ e : V.EObj, e.1 ∈ S.boundarySet → Λ' e = Λ e)

end RoundTrip.V18_41
