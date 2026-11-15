import Polyfold.Chapter12.LocalOrientationOrbit
import Polyfold.Chapter14.HalfSpaceBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
Theorem 12.5.3 (p. 594) and Proposition 12.5.6 (p. 595).

# The orientation bundle with local sc⁺-sections on the half-space bundle

## The text, paraphrased

Theorem 12.5.3 gives the orientation bundle `O_f` of an sc-Fredholm section functor `f` of a
strong bundle over a tame ep-groupoid its topology; Proposition 12.5.6 characterizes the
orientability of `f` by the map `|σ| : |O_f| → |X_∞|` of orbit spaces.

## What is formalized

The hypotheses of `theorem_12_5_3_loc` and `proposition_12_5_6_loc` (a tame object M-polyfold,
an sc-Fredholm section functor with tame germ data) hold for the trivial bundle
`H × ℝᵏ → H` over the trivial ep-groupoid of the half-space `H = [0, ∞) × ℝᵐ`, which has
non-empty boundary, and the graph section of a `C^∞` map:
`isScFredholmSectionFunctor_graphSection_trivial`, `theorem_12_5_3_loc_halfSpace`,
`proposition_12_5_6_loc_halfSpace`.
-/

set_option maxSynthPendingDepth 3

open Set
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- The graph section of a `C^∞` map is an sc-Fredholm section functor of `H × ℝᵏ → H` over the
trivial ep-groupoid of `H`. -/
theorem isScFredholmSectionFunctor_graphSection_trivial (hφ : ContDiff ℝ ∞ φ) :
    (epBundleW1 m k).IsScFredholmSectionFunctor (graphSection φ) :=
  EpStrongBundle.mem_fredholmSectionFunctors_trivial.2
    ⟨isScSmoothSection_graphSection hφ,
      (isScFredholmSection_graphSection_wholeChart hφ).isScFredholmSection⟩

/-- **Theorem 12.5.3 for the local orientation sets on the half-space bundle**: the orientation
bundle of the graph section has exactly one topology with the properties of Theorem 6.6.17, and
the fibres of its projection have two points. -/
theorem theorem_12_5_3_loc_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    (∃! t : TopologicalSpace (OrSpaceLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame),
      (orLocalTransportLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart
          hφ).isScFredholmSectionTame).IsOrientationTopology t) ∧
    ∀ x : (basePoly m).SmoothLevel, ∃ p q : OrSpaceLoc
        (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame, p ≠ q ∧
      (orLocalTransportLoc _ _).proj p = x ∧ (orLocalTransportLoc _ _).proj q = x ∧
      ∀ r, (orLocalTransportLoc _ _).proj r = x → r = p ∨ r = q :=
  EpStrongBundle.theorem_12_5_3_loc (X := EpGroupoid.trivial (basePoly m))
    (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

/-- **Proposition 12.5.6 for the local orientation sets on the half-space bundle**: the graph
section is orientable iff `|σ|` is `(2 : 1)` and has a continuous global section. -/
theorem proposition_12_5_6_loc_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    letI : TopologicalSpace (OrSpaceLoc (PX := (EpGroupoid.trivial (basePoly m)).PObj)
        (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame) :=
      orTopologyLoc _ _
    (∃ o, (epBundleW1 m k).definition_12_5_4_loc
        (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionFunctor_graphSection_trivial hφ)
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame o) ↔
      (epBundleW1 m k).IsTwoToOneLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionFunctor_graphSection_trivial hφ)
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame ∧
      ∃ s : Quot (EpGroupoid.trivial (basePoly m)).SmoothRel →
          Quot ((epBundleW1 m k).OrRelLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
            (isScFredholmSectionFunctor_graphSection_trivial hφ)
            (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame),
        Continuous s ∧ ∀ c, (epBundleW1 m k).orbitProjLoc _ _ _ (s c) = c :=
  (epBundleW1 m k).proposition_12_5_6_loc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionFunctor_graphSection_trivial hφ)
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

end HalfSpaceBundle

end Polyfold
