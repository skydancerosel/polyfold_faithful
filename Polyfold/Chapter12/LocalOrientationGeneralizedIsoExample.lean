import Polyfold.Chapter12.LocalOrientationGeneralizedIso
import Polyfold.Chapter12.LocalOrientationFunctor
import Polyfold.Chapter12.OrientationGeneralizedIsoOriented

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** for the linearizations made with local sc⁺-sections: an example
with non-zero fibres and a generalized strong bundle isomorphism which is not the identity.

## The text, paraphrased

For a generalized strong bundle isomorphism `f̄ : W → W'` and sc-Fredholm section functors `f`,
`f' = f̄_* f`, the map `|f̄|_* : |O_f| → |O_{f'}|` is a homeomorphism covering `|X_∞| → |X'_∞|`,
and an orientation of `f` has exactly one push-forward orientation of `f'`.  The text gives no
example.

## What is formalized

The hypotheses of `GenSBMap.theorem_12_5_7_one_loc_cls` and
`GenSBMap.theorem_12_5_7_two_loc_cls_unique` (tame object M-polyfolds and tame germ data on the
two ends) hold for all `n`, `k` and every `C^∞` map `φ : ℝⁿ → ℝᵏ` in the example of
`OrientationGeneralizedIsoExample.lean`: `W' = ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of
`ℝⁿ`, `W = (-id)^* W'`, `f̄` the class of `W ←1 W →P' W'` with `P'` covering `-id`, `f'` the
graph section of `φ` and `f = (P')^* f'`.

* `theorem_12_5_7_one_loc_cls_witness`: Theorem 12.5.7 (1) with the topology for this data.
* `theorem_12_5_7_two_loc_cls_witness`: Theorem 12.5.7 (2) for this data.
* `exists_definition_12_5_4_loc_negSection`: `f` has an orientation in the sense of
  Definition 12.5.4 (the path category of `ℝⁿ` has at most one morphism between two points,
  and the morphisms of the ep-groupoid are units), so that Theorem 12.5.7 (2) applies to an
  orientation: `theorem_12_5_7_two_loc_cls_oriented_witness`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- **Theorem 12.5.7 (1) for the local orientation sets holds with all its hypotheses in an
example with non-zero fibres**: for `W = (-id)^*(ℝⁿ × ℝᵏ)`, `W' = ℝⁿ × ℝᵏ`,
`f̄ = [W ←1 W →P' W']`, `f'` the graph section of a `C^∞` map and `f = (P')^* f'`, there are
homeomorphisms `|O_f| ≃ₜ |O_{f'}|`, `|X_∞| ≃ₜ |X'_∞|` commuting with `|σ|`, `|σ'|`, with
underlying maps `|f̄|_*` and `|f|`. -/
theorem theorem_12_5_7_one_loc_cls_witness (hφ : ContDiff ℝ ∞ φ) :
    letI : TopologicalSpace (OrSpaceLoc (isTame_negSEP n k)
        (isScFredholmSectionTame_negSection (k := k) hφ)) := orTopologyLoc _ _
    letI : TopologicalSpace (OrSpaceLoc (isTame_epSEP n k)
        (isScFredholmSectionTame_graphSection_epSEP (k := k) hφ)) := orTopologyLoc _ _
    ∃ (Fh : Quot ((negSEP n k).E.OrRelLoc (isTame_negSEP n k)
          (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ)) ≃ₜ
        Quot ((epSEP n k).E.OrRelLoc (isTame_epSEP n k)
          (isScFredholmSectionFunctor_graphSection hφ)
          (isScFredholmSectionTame_graphSection_epSEP hφ)))
      (G : Quot (negSEP n k).X.SmoothRel ≃ₜ Quot (epSEP n k).X.SmoothRel),
      (∀ c, (epSEP n k).E.orbitProjLoc (isTame_epSEP n k)
          (isScFredholmSectionFunctor_graphSection hφ)
          (isScFredholmSectionTame_graphSection_epSEP hφ) (Fh c) =
        G ((negSEP n k).E.orbitProjLoc (isTame_negSEP n k)
          (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ)
          c)) ∧
      ⇑Fh = GenSBMap.orbitOrMapLoc (isGeneralizedIso_negDiagram n k)
        (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
        (graphSection_eq_pushforward hφ) (isTame_negSEP n k) (isTame_epSEP n k)
        (isScFredholmSectionTame_negSection hφ)
        (isScFredholmSectionTame_graphSection_epSEP hφ) ∧
      ⇑G = GenSBMap.smoothOrbitMap (isGeneralizedIso_negDiagram n k) :=
  GenSBMap.theorem_12_5_7_one_loc_cls (isGeneralizedIso_negDiagram n k)
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
    (graphSection_eq_pushforward hφ) (isTame_negSEP n k) (isTame_epSEP n k)
    (isScFredholmSectionTame_negSection hφ)

/-- **Theorem 12.5.7 (2) for the local orientation sets holds with all its hypotheses in the
example**: an orientation `o` of `f = (P')^* f'` (Definition 12.5.4) has exactly one orientation
`o'` of the graph section `f'` corresponding to `o` over the middle of every diagram
representing `f̄`. -/
theorem theorem_12_5_7_two_loc_cls_witness (hφ : ContDiff ℝ ∞ φ)
    {o : ∀ a (hs : a ∈ (negSEP n k).X.PObj.smoothSet),
      OrxLoc (isScFredholmSectionTame_negSection (k := k) hφ) a hs}
    (ho : (negSEP n k).E.definition_12_5_4_loc (isTame_negSEP n k)
      (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ) o) :
    ∃! o' : ∀ x (hs : x ∈ (epSEP n k).X.PObj.smoothSet),
        OrxLoc (isScFredholmSectionTame_graphSection_epSEP (k := k) hφ) x hs,
      (epSEP n k).E.definition_12_5_4_loc (isTame_epSEP n k)
          (isScFredholmSectionFunctor_graphSection hφ)
          (isScFredholmSectionTame_graphSection_epSEP hφ) o' ∧
        ∀ (D : SDiagram (negSEP n k) (epSEP n k))
          (hD : D.cls = (negDiagram n k).cls) v (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k) hD)).orEqvLoc
              (GenSBMap.pullback_eq_of_cls' (isGeneralizedIso_negDiagram n k) hD
                (isScFredholmSectionFunctor_negSection hφ).1 (graphSection_eq_pushforward hφ))
              (D.isScFredholmSectionTame_pullback (isScFredholmSectionTame_negSection hφ))
              (isScFredholmSectionTame_graphSection_epSEP hφ) v hv
              (o' (D.Ψ.ϕ.obj v)
                ((sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
                  hD)).smooth_obj hv)) =
            D.hΦ.orEqvLoc rfl
              (D.isScFredholmSectionTame_pullback (isScFredholmSectionTame_negSection hφ))
              (isScFredholmSectionTame_negSection hφ) v hv
              (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  GenSBMap.theorem_12_5_7_two_loc_cls_unique (isGeneralizedIso_negDiagram n k)
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionFunctor_graphSection hφ)
    (graphSection_eq_pushforward hφ) (isTame_negSEP n k) (isTame_epSEP n k)
    (isScFredholmSectionTame_negSection hφ) ho

/-- **`f = (P')^* f'` has an orientation** in the sense of Definition 12.5.4, for the local
orientation sets: a family which is carried along by the propagation along all sc-smooth paths
of `ℝⁿ` (any two paths with the same end points are homotopic) and is invariant under the
morphisms (the ep-groupoid is the trivial one of `ℝⁿ`, its morphisms are units, and
`(1_x)_* = Id`). -/
theorem exists_definition_12_5_4_loc_negSection (hφ : ContDiff ℝ ∞ φ) :
    ∃ o : ∀ a (hs : a ∈ (negSEP n k).X.PObj.smoothSet),
        OrxLoc (isScFredholmSectionTame_negSection (k := k) hφ) a hs,
      (negSEP n k).E.definition_12_5_4_loc (isTame_negSEP n k)
        (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ) o := by
  obtain ⟨o, ho⟩ := (exists_isSectionOrientationLoc_iff (isTame_negSEP n k)
    (isScFredholmSectionTame_negSection (k := k) hφ)).2
    (isOrientableSectionLoc_of_hom_eq _ _ PathCat.hom_eq_rn)
  refine ⟨o, ((negSEP n k).E.definition_12_5_4_loc_iff (isTame_negSEP n k)
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ) o).2
    ⟨(isSectionOrientationLoc_iff_isContOn_univ _ _ o).1 ho, fun σ x x' hx hx' hs hs' => ?_⟩⟩
  obtain rfl : σ = x := hx
  obtain rfl : σ = x' := hx'
  exact DFunLike.congr_fun ((negSEP n k).E.orMorLoc_unit
    (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ) rfl rfl
    rfl hs) (o σ hs)

/-- **Theorem 12.5.7 (2) for the local orientation sets in an example with an orientation**:
there are an orientation `o` of `f = (P')^* f'` and exactly one orientation `o'` of the graph
section `f'` which corresponds to `o` over the middle of every diagram representing `f̄`. -/
theorem theorem_12_5_7_two_loc_cls_oriented_witness (hφ : ContDiff ℝ ∞ φ) :
    ∃ o : ∀ a (hs : a ∈ (negSEP n k).X.PObj.smoothSet),
        OrxLoc (isScFredholmSectionTame_negSection (k := k) hφ) a hs,
      (negSEP n k).E.definition_12_5_4_loc (isTame_negSEP n k)
        (isScFredholmSectionFunctor_negSection hφ) (isScFredholmSectionTame_negSection hφ) o ∧
      ∃! o' : ∀ x (hs : x ∈ (epSEP n k).X.PObj.smoothSet),
          OrxLoc (isScFredholmSectionTame_graphSection_epSEP (k := k) hφ) x hs,
        (epSEP n k).E.definition_12_5_4_loc (isTame_epSEP n k)
            (isScFredholmSectionFunctor_graphSection hφ)
            (isScFredholmSectionTame_graphSection_epSEP hφ) o' ∧
          ∀ (D : SDiagram (negSEP n k) (epSEP n k))
            (hD : D.cls = (negDiagram n k).cls) v (hv : v ∈ D.B.X.PObj.smoothSet),
            (sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
                hD)).orEqvLoc
                (GenSBMap.pullback_eq_of_cls' (isGeneralizedIso_negDiagram n k) hD
                  (isScFredholmSectionFunctor_negSection hφ).1 (graphSection_eq_pushforward hφ))
                (D.isScFredholmSectionTame_pullback (isScFredholmSectionTame_negSection hφ))
                (isScFredholmSectionTame_graphSection_epSEP hφ) v hv
                (o' (D.Ψ.ϕ.obj v)
                  ((sbe (GenSBMap.equivalences_Ψ_of_cls (isGeneralizedIso_negDiagram n k)
                    hD)).smooth_obj hv)) =
              D.hΦ.orEqvLoc rfl
                (D.isScFredholmSectionTame_pullback (isScFredholmSectionTame_negSection hφ))
                (isScFredholmSectionTame_negSection hφ) v hv
                (o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  obtain ⟨o, ho⟩ := exists_definition_12_5_4_loc_negSection (k := k) hφ
  exact ⟨o, ho, theorem_12_5_7_two_loc_cls_witness hφ ho⟩

end StrongBundleLocalizationExamples

end Polyfold
