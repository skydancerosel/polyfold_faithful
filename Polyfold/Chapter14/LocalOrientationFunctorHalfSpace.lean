import Polyfold.Chapter12.LocalOrientationFunctor
import Polyfold.Chapter14.LocalOrientationHalfSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
Theorem 6.6.13 (pp. 273–274) and Definitions 6.6.14–6.6.16 (p. 274).

# The functor `Γ_f` of the local orientation sets on the half-space bundle

## The text, paraphrased

Theorem 6.6.13 gives an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold its
functor `Γ_f` on the classes of sc-smooth paths, determined by property (∗); `f` is orientable
if `Γ_f([φ])` depends only on the end points, equivalently if there is a map `y ↦ o_y` which
near every smooth point is a continuous orientation.

## What is formalized

The statements for the local orientation sets (`theorem_6_6_13_loc`,
`isOrientableSectionLoc_iff`) applied to the trivial bundle `H × ℝᵏ → H` over the half-space
`H = [0, ∞) × ℝᵐ`, which has non-empty boundary, and the graph section of a `C^∞` map:
`theorem_6_6_13_loc_halfSpace`, `isOrientableSectionLoc_iff_halfSpace`.
-/

set_option maxSynthPendingDepth 3

open Set CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- **Theorem 6.6.13 for the local orientation sets on the half-space bundle**: the graph
section has exactly one functor `Γ_f` with property (∗). -/
theorem theorem_6_6_13_loc_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    ∃! G : ∀ x y : PathCat (MPolyfold.quadrantPolyfold 1 (rnSc m)), (x ⟶ y) →
        (OrxLoc (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
            x.pt x.smooth ≃
          OrxLoc (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
            y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat (MPolyfold.quadrantPolyfold 1 (rnSc m))) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarPropertyLoc
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame G :=
  theorem_6_6_13_loc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

/-- **Definitions 6.6.14 and 6.6.15 on the half-space bundle**: the graph section is orientable
iff it has a map `y ↦ o_y` which near every point is a continuous orientation. -/
theorem isOrientableSectionLoc_iff_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    IsOrientableSectionLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame ↔
      ∃ o, IsSectionOrientationLoc (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
        (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame o :=
  isOrientableSectionLoc_iff (MPolyfold.quadrantPolyfold_isTame 1 (rnSc m))
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

end HalfSpaceBundle

end Polyfold
