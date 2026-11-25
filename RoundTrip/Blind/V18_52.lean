import Polyfold
/-! Blind formalization of V18_52 (the text's §18.6, Theorem 18.6.1, last sentence, p. 861 of the
Springer 2021 book; 2017: Theorem 18.8), the orientation clause.

Text: if `f` is oriented by `o_f`, the tame branched ep⁺-subcategory `Θ = Λ ∘ f` is naturally
oriented.

Choices:
- Setting and hypotheses: those of Theorem 18.6.1 (see V18_51): universe `0`, `C : GCT.{0}`,
  `S`, `V`, `Q` with `Q.HasStrongBundleUniformizers`, `S.IsTame`,
  `S.AdmitsModelBumpFunctions`; `f` an sc-Fredholm section functor with compact `|S_f|`;
  `(N, U)` controlling compactness (`Q.IsAuxNormBook N`, `f.ControlsCompactness N U`);
  `h : C → (0, 1]` a continuous functor.
- `Λ` is any sc⁺-multisection functor with the conclusions (1)–(4) of Theorem 18.6.1 (the
  sentence speaks of the `Λ` of the theorem; I quantify over all `Λ` having (1)–(4), with the
  same vocabulary readings as in V18_51).  `Θ(α) = Λ(f(α))`.
- "`f` is oriented by `o_f`": `o_f` is a section functor `o : C_∞ → O_f` of `σ`
  (`Q.OrSection`) which is an orientation (`Q.IsOrientation`, Definition 18.5.4).  The
  vocabulary's `IsOrientation` takes as arguments `S.AdmitsModelBumpFunctions`, `S.IsTame` and
  `Q.IsScFredholmSectionFunctorTame f` (every representative a tame sc-Fredholm section); the
  first two are hypotheses of the theorem, the third is an extra hypothesis I add only because
  the vocabulary's notion of orientation needs it.  `S.HasUniformizers` is added because the
  vocabulary's orientation of `Θ` needs it (it follows from `F̄(α) ≠ ∅`).
- "`Θ` is naturally oriented": I can only formalize that `Θ` HAS an orientation, an `T̂Θ` with
  `S.IsOrientationC hU Θ T̂Θ` (Definition 17.5.8); the naturality of the construction from `o_f`
  is not captured (the quoted sentence does not describe it).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_52
open Polyfold

/-- Theorem 18.6.1, last sentence: an orientation of `f` orients `Θ = Λ ∘ f`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S)
    (hF : Q.HasStrongBundleUniformizers) (hU : S.HasUniformizers) (ht : S.IsTame)
    (hb : S.AdmitsModelBumpFunctions)
    (f : V.SectionFunctor) (hf : Q.IsScFredholmSectionFunctor f)
    (hfT : Q.IsScFredholmSectionFunctorTame f), f.HasCompactModuliSpace →
    ∀ (N : V.EObj → ENNReal) (U : Set C.toGroupoidStr.OrbitSpace),
      Q.IsAuxNormBook N → f.ControlsCompactness N U →
    ∀ (h : C.Obj → ℝ), S.IsContinuousFunctionFunctor h → (∀ α, 0 < h α ∧ h α ≤ 1) →
    ∀ Λ : V.EObj → ℚ≥0,
      Q.IsScPlusMultisectionFunctor Λ →
      (∀ α, GCT.VectorBundle.pointwiseNormFunctor N Λ α < ENNReal.ofReal (h α)) →
      GCT.VectorBundle.orbitDomSupp Λ ⊆ U →
      Q.IsTransversalFunctor f Λ →
      Q.IsInGeneralPositionFunctor f Λ →
    ∀ o : Q.OrSection hf hF, Q.IsOrientation hf hb ht hfT hF o →
      ∃ T : C.Obj → S.OrTC →₀ ℚ,
        S.IsOrientationC hU (fun α => ((Λ (f.toFun α) : ℚ≥0) : ℚ)) T

end RoundTrip.V18_52
