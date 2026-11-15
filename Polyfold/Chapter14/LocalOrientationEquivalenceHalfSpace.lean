import Polyfold.Chapter12.LocalOrientationEquivalenceHomeo
import Polyfold.Chapter14.LocalOrientationBundleHalfSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
Theorem 12.5.7 (p. 595), for the linearizations made with local sc⁺-sections.

# Theorem 12.5.7 with local sc⁺-sections on the half-space bundle

## The text, paraphrased

A generalized strong bundle isomorphism `𝔣 : W → W'` between strong bundles over tame
ep-groupoids with `𝔣_* f = f'` induces a homeomorphism `|O_f| → |O_{f'}|` over
`|X_∞| → |X'_∞|`, and an orientation of `f` has a unique push-forward orientation of `f'`.

## What is formalized

The hypotheses of `theorem_12_5_7_one_loc` and `theorem_12_5_7_two_loc` (tame object
M-polyfolds, sc-Fredholm section functors with tame germ data, a diagram of strong bundle
equivalences with equal pull-backs) hold over a base with non-empty boundary and with non-zero
fibres: the trivial bundle `H × ℝᵏ → H` over the trivial ep-groupoid of the half-space
`H = [0, ∞) × ℝᵐ`, the graph section of a `C^∞` map, and the identity diagram
(`theorem_12_5_7_one_loc_halfSpace`, `theorem_12_5_7_two_loc_halfSpace`).  The equivalences of
this instance are identities; an instance with a generalized strong bundle isomorphism which is
not the identity, over `ℝⁿ`, is in `Chapter12/LocalOrientationGeneralizedIsoExample.lean`.
-/

set_option maxSynthPendingDepth 3

open Set
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- The pull-back of a section by the identity equivalence is the section. -/
theorem eq_pullback_id (hφ : ContDiff ℝ ∞ φ) :
    graphSection φ =
      (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k)).pullback (graphSection φ) :=
  funext fun x =>
    ((EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k)).pullback_eq
      (isScSmoothSection_graphSection hφ).1 ((isScSmoothSection_graphSection hφ).1 x) rfl).symm

/-- **Theorem 12.5.7 (1) for the local orientation sets on the half-space bundle**, for the
identity diagram: a homeomorphism of `|O_f|` and one of `|X_∞|` commuting with `|σ|`. -/
theorem theorem_12_5_7_one_loc_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    letI : TopologicalSpace (OrSpaceLoc (PX := (EpGroupoid.trivial (basePoly m)).PObj)
        (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame) :=
      orTopologyLoc _ _
    ∃ (F : Quot ((epBundleW1 m k).OrRelLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
          (isScFredholmSectionFunctor_graphSection_trivial hφ)
          (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame) ≃ₜ
        Quot ((epBundleW1 m k).OrRelLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
          (isScFredholmSectionFunctor_graphSection_trivial hφ)
          (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame))
      (G : Quot (EpGroupoid.trivial (basePoly m)).SmoothRel ≃ₜ
        Quot (EpGroupoid.trivial (basePoly m)).SmoothRel),
      ∀ c, (epBundleW1 m k).orbitProjLoc _ _ _ (F c) =
        G ((epBundleW1 m k).orbitProjLoc _ _ _ c) := by
  obtain ⟨F, G, h, -, -⟩ := theorem_12_5_7_one_loc
    (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k))
    (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k))
    (isScFredholmSectionFunctor_graphSection_trivial hφ)
    (isScFredholmSectionFunctor_graphSection_trivial hφ)
    (isScFredholmSectionFunctor_graphSection_trivial hφ) (eq_pullback_id hφ) (eq_pullback_id hφ)
    (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m)) (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
  exact ⟨F, G, h⟩

/-- **Theorem 12.5.7 (2) for the local orientation sets on the half-space bundle**, for the
identity diagram: an orientation of the graph section has exactly one orientation corresponding
to it. -/
theorem theorem_12_5_7_two_loc_halfSpace (hφ : ContDiff ℝ ∞ φ)
    {o : ∀ a (hs : a ∈ (EpGroupoid.trivial (basePoly m)).PObj.smoothSet),
      OrxLoc (isScFredholmSectionTame_graphSection_wholeChart (k := k)
        hφ).isScFredholmSectionTame a hs}
    (ho : (epBundleW1 m k).definition_12_5_4_loc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
      (isScFredholmSectionFunctor_graphSection_trivial hφ)
      (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame o) :
    ∃! o' : ∀ x (hs : x ∈ (EpGroupoid.trivial (basePoly m)).PObj.smoothSet),
        OrxLoc (isScFredholmSectionTame_graphSection_wholeChart (k := k)
          hφ).isScFredholmSectionTame x hs,
      (epBundleW1 m k).definition_12_5_4_loc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
          (isScFredholmSectionFunctor_graphSection_trivial hφ)
          (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame o' ∧
        ∀ v (hv : v ∈ (EpGroupoid.trivial (basePoly m)).PObj.smoothSet),
          (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k)).orEqvLoc
              (eq_pullback_id hφ)
              (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
              (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame v hv
              (o' v hv) =
            (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k)).orEqvLoc
              (eq_pullback_id hφ)
              (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
              (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame v hv
              (o v hv) :=
  theorem_12_5_7_two_loc (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k))
    (EpStrongBundle.isStrongBundleEquivalence_id (epBundleW1 m k))
    (isScFredholmSectionFunctor_graphSection_trivial hφ)
    (isScFredholmSectionFunctor_graphSection_trivial hφ)
    (isScFredholmSectionFunctor_graphSection_trivial hφ) (eq_pullback_id hφ) (eq_pullback_id hφ)
    (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m)) (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame ho

end HalfSpaceBundle

end Polyfold
