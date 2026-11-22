import Polyfold.Chapter18.FredholmSectionFunctors
import Polyfold.Chapter17.BundleModelComparison
import Polyfold.Chapter10.StrongBundleLocalizationSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, p. 844: Remark 18.1.2 (a), **`[f̄]_* f^c = f^{c'}`**: the model sections of a section
functor for two covering families correspond under the push-forward along the comparison
generalized strong bundle isomorphism of §17.7 (p. 828).

# Push-forward of model sections along `f̄_{Ψ̄,Ψ̄'}`

## The text, paraphrased

(p. 844) A section functor `f` of `P : E → C` pulls back, by `Γ̄_Ψ̄ : W_Ψ̄ → E` for a covering
family `Ψ̄`, to a section functor `f^Ψ̄` of `W_Ψ̄ → X_Ψ`; the pull-backs for two covering
families are related by the generalized strong bundle isomorphism `[f̄] : W_Ψ̄ → W_Ψ̄'` of
§17.7, so that the various model descriptions of `f` are equivalent.

## What is formalized

* **`pushforward_bundleComparison_modelSection`**: for an sc-smooth section functor `f` and two
  covering families `c`, `c'` of strong bundle uniformizers,
  `[f̄_{c,c'}]_* f^c = f^{c'}` (the push-forward of Theorem 10.5.4).
* `pullback_bundleComparison_modelSection`: `[f̄_{c,c'}]^* f^{c'} = f^c`.
* `orbitMap_pushforward_bundleComparison`: the orbit identity behind it,
  `|Γ̄_{c'}|(|[f̄]_* s (x')|) = |Γ̄_c|(|s(x)|)` for `|Γ_c|(|x|) = |Γ_{c'}|(|x'|)`.

## Readings

* `[f̄]` is the generalized strong bundle isomorphism `bundleComparison c c'`
  (`BundleModelComparison.lean`), and `[f̄]_*` its push-forward
  `GenSBMap.pushforward` (Theorem 10.5.4, independent of the representing diagram).
* The push-forward is taken on `Γ(P, μ)`, the sc-smooth section functors (Definition 8.3.4); `f`
  is sc-smooth in the sense of Remark 18.1.2 (c).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open SBLocalization SBLocalization.SEPLoc

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

/-- **The orbit identity of `[f̄]_*`**: for a section functor `s` of `W_c → X_c`, `x ∈ X_c` and
`x' ∈ X_{c'}` with `|x'|` the image of `|x|` under the base of a representative,
`|Γ̄_{c'}|(|([f̄]_* s)(x')|) = |Γ̄_c|(|s(x)|)`. -/
theorem orbitMap_pushforward_bundleComparison (c c' : Q.BundleCoveringFamily)
    {s : S.ModelObj (Q.modelBase c.Ψ) → Q.ModelW c.Ψ}
    (hs : s ∈ (Q.modelSEP c.Ψ).E.sectionFunctors) (x' : S.ModelObj (Q.modelBase c'.Ψ)) :
    ∃ x : S.ModelObj (Q.modelBase c.Ψ),
      (Q.bundleModelFunctor c'.Ψ).orbitMap ((Q.modelSEP c'.Ψ).E.toEpGroupoid.π
          (GenSBMap.pushforward (Q.isGeneralizedIso_bundleComparison c c') s x')) =
        (Q.bundleModelFunctor c.Ψ).orbitMap ((Q.modelSEP c.Ψ).E.toEpGroupoid.π (s x)) := by
  set hg := Q.isGeneralizedIso_bundleComparison c c'
  set D := GenSBMap.rep hg
  set hΨ := GenSBMap.isEquivalence_rep_Ψ hg
  refine ⟨(SEP.Hom.ϕ D.Φ).obj ((sbe hΨ).preObj x'), ?_⟩
  have hp := D.π_pushforward hΨ hs (D.base_orbitMap_preObj hΨ x')
  have hD : D.orbitMap = GenSBMap.orbitMap (Q.bundleComparison c c') := by
    rw [← GenSBMap.orbitMap_cls, GenSBMap.cls_rep]
  change (Q.bundleModelFunctor c'.Ψ).orbitMap ((Q.modelSEP c'.Ψ).E.toEpGroupoid.π
    (D.pushforward hΨ s x')) = _
  have k := congrArg (Q.bundleModelFunctor c'.Ψ).orbitMap hp
  rw [hD] at k
  exact k.trans (congrFun (Q.orbitMap_bundleComparison c c') _)

/-- `|f(β)| = |f(β')|` for isomorphic `β`, `β'`. -/
theorem π_toFun_eq_of_π_eq {β β' : C.Obj} (h : C.toGroupoidStr.π β = C.toGroupoidStr.π β') :
    V.groupoid.π (f.toFun β) = V.groupoid.π (f.toFun β') := by
  have e := congrArg f.toGroupoidFunctor.orbitMap h
  rwa [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at e

/-- `|e| = |e'|` in `E` gives `|P(e)| = |P(e')|` in `C`. -/
theorem π_base_eq_of_π_eq {e e' : V.EObj} (h : V.groupoid.π e = V.groupoid.π e') :
    C.toGroupoidStr.π (V.base e) = C.toGroupoidStr.π (V.base e') := by
  have k := congrArg V.proj.orbitMap h
  rwa [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at k

/-- **Remark 18.1.2 (a), `[f̄]_* f^c = f^{c'}`** (2021 p. 844 with §17.7, p. 828): for an
sc-smooth section functor `f` and two covering families `c`, `c'` of strong bundle uniformizers,
the push-forward (Theorem 10.5.4) of the model section `f^c` along the comparison generalized
strong bundle isomorphism `[f̄_{c,c'}] : W_c → W_{c'}` is the model section `f^{c'}`. -/
theorem pushforward_bundleComparison_modelSection (c c' : Q.BundleCoveringFamily)
    (hf : Q.IsScSmoothSectionFunctor f) :
    GenSBMap.pushforward (Q.isGeneralizedIso_bundleComparison c c') (Q.modelSection c.Ψ f) =
      Q.modelSection c'.Ψ f := by
  set hg := Q.isGeneralizedIso_bundleComparison c c'
  have hmem : Q.modelSection c.Ψ f ∈ (Q.modelSEP c.Ψ).E.sectionFunctors :=
    (Q.remark_18_1_2_a_model_smooth f c).2 hf
  obtain ⟨hsm', hfun'⟩ := (Q.remark_18_1_2_a_model_smooth f c').2 hf
  obtain ⟨hsmg, -⟩ := ((GenSBMap.theorem_10_5_4 hg).2.1.1 hmem :
    GenSBMap.pushforward hg (Q.modelSection c.Ψ f) ∈ (Q.modelSEP c'.Ψ).E.sectionFunctors)
  have hsg := hsmg.1
  refine (EpStrongBundle.eq_of_forall_π_eq (E := (Q.modelSEP c'.Ψ).E) hfun' hsg
    fun x' => ?_).symm
  obtain ⟨x, hx⟩ := Q.orbitMap_pushforward_bundleComparison c c' hmem x'
  refine (Q.bundleModelFunctor c'.Ψ).injective_orbitMap_of_full
    (Q.bundleModelFunctor_full c'.Ψ) ?_
  -- `Γ_{c'}(x') ≅ Γ_c(x)`, read off from the base points
  have hb := π_base_eq_of_π_eq (V := V) ((GroupoidFunctor.orbitMap_π _ _).symm.trans
    (hx.trans (Q.orbitMap_modelSection c.Ψ f x).symm))
  have e1 : V.base ((Q.bundleModelFunctor c'.Ψ).obj
      (GenSBMap.pushforward hg (Q.modelSection c.Ψ f) x')) =
      (S.modelFunctor (Q.modelBase c'.Ψ)).obj x' := by
    change (S.modelFunctor (Q.modelBase c'.Ψ)).obj (Q.modelP c'.Ψ _) = _
    exact congrArg (S.modelFunctor (Q.modelBase c'.Ψ)).obj (hsg x')
  have hb' : C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c'.Ψ)).obj x') =
      C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) :=
    (congrArg C.toGroupoidStr.π e1).symm.trans (hb.trans (congrArg C.toGroupoidStr.π
      (f.base_toFun _)))
  exact (Q.orbitMap_modelSection c'.Ψ f x').symm.trans ((π_toFun_eq_of_π_eq hb').trans
    ((Q.orbitMap_modelSection c.Ψ f x).trans hx.symm))

/-- **`[f̄]^* f^{c'} = f^c`**, the pull-back form of `pushforward_bundleComparison_modelSection`
(`[f̄]^*` is the inverse of `[f̄]_*`, Theorem 10.5.4). -/
theorem pullback_bundleComparison_modelSection (c c' : Q.BundleCoveringFamily)
    (hf : Q.IsScSmoothSectionFunctor f) :
    GenSBMap.pullback (Q.isGeneralizedIso_bundleComparison c c') (Q.modelSection c'.Ψ f) =
      Q.modelSection c.Ψ f := by
  rw [← Q.pushforward_bundleComparison_modelSection c c' hf]
  exact ((GenSBMap.theorem_10_5_4 (Q.isGeneralizedIso_bundleComparison c c')).2.1.2.2.1).1
    ((Q.remark_18_1_2_a_model_smooth f c).2 hf)

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
