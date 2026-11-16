import Polyfold.Chapter12.OrientationGeneralizedIsoTopology
import Polyfold.Chapter10.StrongBundleLocalizationExamples
import Polyfold.Chapter4.NonVacuityG
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12): an example with non-zero fibres and a
generalized strong bundle isomorphism which is not the identity.

## The text, paraphrased

For a generalized strong bundle isomorphism `f̄ : W → W'` and sc-Fredholm section functors `f`,
`f' = f̄_* f`, the map `|f̄|_* : |O_f| → |O_{f'}|` is a homeomorphism covering `|X_∞| → |X'_∞|`,
and an orientation of `f` has exactly one push-forward orientation of `f'`.  The text gives no
example.

## What is formalized

The hypotheses of `GenSBMap.theorem_12_5_7_one_homeo_cls` and `GenSBMap.theorem_12_5_7_two_cls`
(Part I's hypotheses on the two ends) are jointly satisfiable in the following case, for all
`n`, `k` (so with fibres `ℝᵏ ≠ 0` and base `ℝⁿ ≠ 0`) and every `C^∞` map `φ : ℝⁿ → ℝᵏ`:

* `W' = ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` (`epSEP n k`), `W = (-id)^* W'`
  (`negSEP n k`), `f̄` the class of `W ←1 W →P' W'` with `P'` covering `-id`
  (`negDiagram n k`, Chapter 10);
* `f'` the graph section `x ↦ (x, φ(x))` of `W'`, and `f = (P')^* f'` (`negSection φ`), the
  section `x ↦ (x, (-x, φ(-x)))` of `W`; then `f' = f̄_* f` (`graphSection_eq_pushforward`);
* `isScFredholmSectionFunctor_negSection`, `isScFredholmSectionTame_negSection`: `f` is an
  sc-Fredholm section functor with tame germ data (Theorem 10.4.5, pull-back);
* `admitsBumpFunctions_rn`: `ℝⁿ` admits sc-smooth bump functions (Definition 5.3.1);
  `hasScPlusSectionsThrough_negSEP`, `hasScPlusSectionsThrough_epSEP`: sc⁺-sections through
  smooth fibre points (Lemma 5.3.3);
* `theorem_12_5_7_one_homeo_cls_witness`: Theorem 12.5.7 (1) with the topology for this data;
* `theorem_12_5_7_two_cls_witness`: Theorem 12.5.7 (2) for the representative `negDiagram n k`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-! ### The base `ℝⁿ` -/

/-- `ℝⁿ` admits sc-smooth bump functions (Definition 5.3.1; from sc-smooth partitions of
unity). -/
theorem admitsBumpFunctions_rn (n : ℕ) : (rnPolyfold n).AdmitsBumpFunctions :=
  (rnPolyfold_admitsScPartitionsOfUnity n).admitsBumpFunctions

/-- The object M-polyfold `ℝⁿ` of `W = (-id)^* W'` is tame. -/
theorem isTame_negSEP (n k : ℕ) : (negSEP n k).X.PObj.IsTame := rnPolyfold_isTame

/-- The object M-polyfold `ℝⁿ` of `W' = ℝⁿ × ℝᵏ` is tame. -/
theorem isTame_epSEP (n k : ℕ) : (epSEP n k).X.PObj.IsTame := rnPolyfold_isTame

/-- The object M-polyfold of `W` admits sc-smooth bump functions. -/
theorem admitsBumpFunctions_negSEP (n k : ℕ) : (negSEP n k).X.PObj.AdmitsBumpFunctions :=
  admitsBumpFunctions_rn n

/-- The object M-polyfold of `W'` admits sc-smooth bump functions. -/
theorem admitsBumpFunctions_epSEP (n k : ℕ) : (epSEP n k).X.PObj.AdmitsBumpFunctions :=
  admitsBumpFunctions_rn n

/-- Sc⁺-sections of `W' = ℝⁿ × ℝᵏ` through smooth fibre points (Lemma 5.3.3). -/
theorem hasScPlusSectionsThrough_epSEP (n k : ℕ) : (epSEP n k).B.HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (admitsBumpFunctions_rn n)

/-- Sc⁺-sections of `W = (-id)^* W'` through smooth fibre points (Lemma 5.3.3). -/
theorem hasScPlusSectionsThrough_negSEP (n k : ℕ) : (negSEP n k).B.HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (admitsBumpFunctions_rn n)

/-! ### The section functors -/

/-- The section `f = (P')^* f'` of `W = (-id)^* W'`, `f'` the graph section of `φ`:
`x ↦ (x, (-x, φ(-x)))`. -/
def negSection (φ : (Fin n → ℝ) → (Fin k → ℝ)) : (negSEP n k).Obj → (negSEP n k).W :=
  (sbe (negSEPHom_mem_equivalences n k)).pullback (graphSection φ)

/-- The graph section of a `C^∞` map is an sc-Fredholm section functor of `W'`
(Definition 8.3.4 (3)). -/
theorem isScFredholmSectionFunctor_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (epSEP n k).E.IsScFredholmSectionFunctor (graphSection φ) :=
  graphSection_mem_fredholmSectionFunctors_epBundle hφ

/-- The graph section has tame germ data (Definition 3.6.4). -/
theorem isScFredholmSectionTame_graphSection_epSEP (hφ : ContDiff ℝ ∞ φ) :
    (epSEP n k).B.IsScFredholmSectionTame (graphSection φ) :=
  isScFredholmSectionTame_graphSection hφ

/-- `f = (P')^* f'` is an sc-Fredholm section functor of `W` (Theorem 10.4.5, pull-back). -/
theorem isScFredholmSectionFunctor_negSection (hφ : ContDiff ℝ ∞ φ) :
    (negSEP n k).E.IsScFredholmSectionFunctor (negSection φ) :=
  (theorem_10_4_5_fred (sbe (negSEPHom_mem_equivalences n k))).2.1
    (isScFredholmSectionFunctor_graphSection hφ)

/-- `f = (P')^* f'` has tame germ data (Definition 3.6.5). -/
theorem isScFredholmSectionTame_negSection (hφ : ContDiff ℝ ∞ φ) :
    (negSEP n k).B.IsScFredholmSectionTame (negSection φ) :=
  (sbe (negSEPHom_mem_equivalences n k)).isScFredholmSectionTame_pullback
    (isScFredholmSectionTame_graphSection_epSEP hφ)

/-- **`f' = f̄_* f`**: the graph section is the push-forward of `f = (P')^* f'` along the class
of `W ←1 W →P' W'` (Theorem 10.5.4 and `P'_* (P')^* f' = f'`, Theorem 10.4.5). -/
theorem graphSection_eq_pushforward (hφ : ContDiff ℝ ∞ φ) :
    graphSection φ = GenSBMap.pushforward (isGeneralizedIso_negDiagram n k) (negSection φ) := by
  have hF := isScFredholmSectionFunctor_negSection (n := n) (k := k) hφ
  have hF' := isScFredholmSectionFunctor_graphSection (n := n) (k := k) hφ
  have hΨ : SEP.equivalences (negDiagram n k).Ψ := negSEPHom_mem_equivalences n k
  rw [GenSBMap.pushforward_eq (isGeneralizedIso_negDiagram n k) rfl hΨ hF.1]
  have hp : (negDiagram n k).hΦ.pullback (negSection φ) = negSection φ := by
    funext x
    exact (negDiagram n k).hΦ.obj_pullback hF.1.1.1 x
  change _ = (sbe hΨ).pushforward ((negDiagram n k).hΦ.pullback (negSection φ))
  rw [hp]
  exact ((sbe hΨ).pushforward_pullback hF'.1.1.1 hF'.1.2).symm

/-! ### Theorem 12.5.7 for the example -/

/-- **Theorem 12.5.7 (1) with the topology holds with all its hypotheses in an example with
non-zero fibres**: for `W = (-id)^*(ℝⁿ × ℝᵏ)`, `W' = ℝⁿ × ℝᵏ`, `f̄ = [W ←1 W →P' W']`, `f'` the
graph section of a `C^∞` map and `f = (P')^* f'`, there are homeomorphisms
`|O_f| ≃ₜ |O_{f'}|`, `|X_∞| ≃ₜ |X'_∞|` commuting with `|σ|`, `|σ'|`, with underlying maps
`|f̄|_*` and `|f|`. -/
theorem theorem_12_5_7_one_homeo_cls_witness (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP n k).B
    letI : TopologicalSpace
        (OrSpace (negSection φ) (isScFredholmSectionFunctor_negSection (k := k) hφ).2) :=
      orTopology (orLocalTransport (isTame_negSEP n k)
        (admitsBumpFunctions_negSEP n k) (isScFredholmSectionTame_negSection hφ)
        (hasScPlusSectionsThrough_negSEP n k))
    letI : TopologicalSpace
        (OrSpace (B := (epSEP n k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection hφ).2) :=
      orTopology (orLocalTransport (isTame_epSEP n k)
        (admitsBumpFunctions_epSEP n k) (isScFredholmSectionTame_graphSection_epSEP hφ)
        (hasScPlusSectionsThrough_epSEP n k))
    ∃ (Fh : Quot ((negSEP n k).E.OrRel (isScFredholmSectionFunctor_negSection hφ)
          (hasScPlusSectionsThrough_negSEP n k)) ≃ₜ
        Quot ((epSEP n k).E.OrRel (isScFredholmSectionFunctor_graphSection hφ)
          (hasScPlusSectionsThrough_epSEP n k)))
      (G : Quot (negSEP n k).X.SmoothRel ≃ₜ Quot (epSEP n k).X.SmoothRel),
      (∀ c, (epSEP n k).E.orbitProj (isScFredholmSectionFunctor_graphSection hφ)
          (hasScPlusSectionsThrough_epSEP n k) (Fh c) =
        G ((negSEP n k).E.orbitProj (isScFredholmSectionFunctor_negSection hφ)
          (hasScPlusSectionsThrough_negSEP n k) c)) ∧
      ⇑Fh = GenSBMap.orbitOrMap (isGeneralizedIso_negDiagram n k)
        (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
        (graphSection_eq_pushforward hφ) (hasScPlusSectionsThrough_negSEP n k)
        (hasScPlusSectionsThrough_epSEP n k) ∧
      ⇑G = GenSBMap.smoothOrbitMap (isGeneralizedIso_negDiagram n k) :=
  GenSBMap.theorem_12_5_7_one_homeo_cls (isGeneralizedIso_negDiagram n k)
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
    (graphSection_eq_pushforward hφ) (hasScPlusSectionsThrough_negSEP n k)
    (hasScPlusSectionsThrough_epSEP n k) (isTame_negSEP n k) (admitsBumpFunctions_negSEP n k)
    (isScFredholmSectionTame_negSection hφ) (isTame_epSEP n k) (admitsBumpFunctions_epSEP n k)
    (isScFredholmSectionTame_graphSection_epSEP hφ)

/-- **Theorem 12.5.7 (2) holds with all its hypotheses in the example**, for the representative
`W ←1 W →P' W'`: an orientation `o` of `f = (P')^* f'` (Definition 12.5.4) has exactly one
orientation `o'` of the graph section `f'` corresponding to `o` over the middle `W`. -/
theorem theorem_12_5_7_two_cls_witness (hφ : ContDiff ℝ ∞ φ)
    {o : ∀ a (hs : a ∈ (negSEP n k).X.PObj.smoothSet),
      Orx (negSection φ) (isScFredholmSectionFunctor_negSection (k := k) hφ).2 a hs} :
    haveI := paracompactSpace_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (negSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (negSEP n k).B
    haveI := paracompactSpace_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_pullback (epSEP n k).B
    haveI := paracompactSpace_rn_rn_prod (epSEP n k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (epSEP n k).B
    (negSEP n k).E.definition_12_5_4 (isScFredholmSectionFunctor_negSection hφ)
        (hasScPlusSectionsThrough_negSEP n k)
        (orTopology (orLocalTransport (isTame_negSEP n k) (admitsBumpFunctions_negSEP n k)
          (isScFredholmSectionTame_negSection hφ) (hasScPlusSectionsThrough_negSEP n k))) o →
    ∃! o' : ∀ x (hs : x ∈ (epSEP n k).X.PObj.smoothSet),
        Orx (B := (epSEP n k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection hφ).2 x hs,
      (epSEP n k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection hφ)
          (hasScPlusSectionsThrough_epSEP n k)
          (orTopology (orLocalTransport (isTame_epSEP n k) (admitsBumpFunctions_epSEP n k)
            (isScFredholmSectionTame_graphSection_epSEP hφ)
            (hasScPlusSectionsThrough_epSEP n k))) o' ∧
        ∀ v (hv : v ∈ (negDiagram n k).B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
              (D := negDiagram n k) rfl)).orEqv
              ((negDiagram n k).isScFredholm_pullback (isScFredholmSectionFunctor_negSection hφ))
              (isScFredholmSectionFunctor_graphSection hφ)
              (GenSBMap.pullback_eq_of_cls' (isGeneralizedIso_negDiagram n k) rfl
                (isScFredholmSectionFunctor_negSection hφ).1 (graphSection_eq_pushforward hφ))
              ((negDiagram n k).hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_negSEP n k))
              (hasScPlusSectionsThrough_epSEP n k) v hv
              (o' ((negDiagram n k).Ψ.ϕ.obj v)
                ((sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
                  (D := negDiagram n k) rfl)).smooth_obj hv)) =
            (negDiagram n k).hΦ.orEqv
              ((negDiagram n k).isScFredholm_pullback (isScFredholmSectionFunctor_negSection hφ))
              (isScFredholmSectionFunctor_negSection hφ) rfl
              ((negDiagram n k).hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_negSEP n k))
              (hasScPlusSectionsThrough_negSEP n k) v hv
              (o ((negDiagram n k).Φ.ϕ.obj v) ((negDiagram n k).hΦ.smooth_obj hv)) :=
  GenSBMap.theorem_12_5_7_two_cls (isGeneralizedIso_negDiagram n k)
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
    (graphSection_eq_pushforward hφ) (hasScPlusSectionsThrough_negSEP n k)
    (hasScPlusSectionsThrough_epSEP n k) (isTame_negSEP n k) (admitsBumpFunctions_negSEP n k)
    (isScFredholmSectionTame_negSection hφ) (isTame_epSEP n k) (admitsBumpFunctions_epSEP n k)
    (isScFredholmSectionTame_graphSection_epSEP hφ) (D := negDiagram n k) rfl

end StrongBundleLocalizationExamples

end Polyfold
