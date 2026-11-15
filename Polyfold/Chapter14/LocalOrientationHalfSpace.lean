import Polyfold.Chapter12.LocalOrientationSpace
import Polyfold.Chapter14.HalfSpaceBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
Theorems 6.6.11 (p. 272) and 6.6.17 (pp. 274–275).

# The orientation space of the local orientation sets on the half-space bundle

## The text, paraphrased

Theorem 6.6.11 gives every smooth point a neighbourhood with the local propagation property;
Theorem 6.6.17 gives the orientation space `O_f` of an sc-Fredholm section `f` of a strong
bundle over a tame M-polyfold its topology, characterized by three properties.

## What is formalized

The theorems for the local orientation sets (`theorem_6_6_11_loc`, `theorem_6_6_17_loc`)
applied to the trivial bundle `H × ℝᵏ → H` over the half-space `H = [0, ∞) × ℝᵐ`, which has
non-empty boundary, and the graph section of a `C^∞` map:
`theorem_6_6_11_loc_halfSpace`, `theorem_6_6_17_loc_halfSpace`.
-/

set_option maxSynthPendingDepth 3

open Set
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- **Theorem 6.6.11 for the local orientation sets on the half-space bundle**: every point of
`H` has a good open neighbourhood for the graph section. -/
theorem theorem_6_6_11_loc_halfSpace (hφ : ContDiff ℝ ∞ φ) (x : H m) :
    ∃ U : Set (H m), IsOpen U ∧ x ∈ U ∧
      (orLocalTransportLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart
          hφ).isScFredholmSectionTame).Good U :=
  theorem_6_6_11_loc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
    (smoothSet_eq_univ (m := m) ▸ mem_univ x)

/-- **Theorem 6.6.17 for the local orientation sets on the half-space bundle**: the orientation
space of the graph section has exactly one topology with the properties of the theorem. -/
theorem theorem_6_6_17_loc_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    ∃! t : TopologicalSpace (OrSpaceLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame),
      (orLocalTransportLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart
          hφ).isScFredholmSectionTame).IsOrientationTopology t :=
  theorem_6_6_17_loc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

end HalfSpaceBundle

end Polyfold
