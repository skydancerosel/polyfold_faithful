import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter3.NonVacuityCorner
import Polyfold.Chapter3.TameVacuityChart
import Polyfold.Chapter3.TameGermsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Definitions 3.11,
3.14, 3.50, 3.51 and 3.53: **the non-vacuity witnesses in the text's germ reading** (phase 2 of the
germ-versus-chart work; Findings, Chapter 3, items 300–309).

# The non-vacuity witnesses satisfy the germ-reading notions

## What is formalized

The witnesses of `NonVacuity.lean` (the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` and the graph section
`x ↦ (x, φ(x))` of a `C^∞` map), of `NonVacuityCorner.lean` (the same over the half-space
`H = [0, ∞) × ℝᵐ`) and of `TameVacuityChart.lean` build whole-chart germ data (a filled version
sc-smooth on the whole chart, an sc⁺-section sc-smooth on the whole chart).  The project's
whole-chart notions imply the germ-reading ones (`TameGermsG.lean`), so the witnesses satisfy the
germ-reading notions as well:

* `TrivialBundle.isScFredholmGermTame_graphSection`, `isGoodPositionGermTame_graphSection`,
  `isScFredholmSection_graphSection`, `isScFredholmSectionTame_graphSection`,
  `hypotheses_theorem_3_57_graphSection`, `hypotheses_theorem_3_57_linear`;
* `HalfSpaceBundle.isScFredholmGermTame_graphSection`, `isGoodPositionGermTame_graphSection`,
  `isScFredholmSection_graphSection`, `isScFredholmSectionTame_graphSection`,
  `hypotheses_theorem_3_57_halfSpace`;
* `TrivialBundle.htame_fails_repaired_holds`.

## What the text leaves implicit, and the choices made

These are one-line corollaries through `IsScFredholmSectionWholeChart.isScFredholmSection` and its tame and
good-position analogues; they show that the germ-reading hypotheses (the targets of the phase-2
redefinition of Definition 3.11) are satisfiable, with boundary points included.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- **Tame germ data of the graph section at every point, germ reading** (Definition 3.50, phase
2): from the whole-chart data (`isScFredholmGermTame_graphSection_wholeChart`). -/
theorem isScFredholmGermTame_graphSection (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    (bundle n k).IsScFredholmGermTame (graphSection φ) x₀ :=
  (isScFredholmGermTame_graphSection_wholeChart hφ x₀).isScFredholmGermTame

/-- **Good position of the graph section in a tame chart at a point where `Dφ` is onto, germ
reading** (Definition 3.53, phase 2). -/
theorem isGoodPositionGermTame_graphSection (hφ : ContDiff ℝ ∞ φ) {x₀ : Fin n → ℝ}
    (hsurj : Surjective (fderiv ℝ φ x₀)) :
    (bundle n k).IsGoodPositionGermTame (graphSection φ) x₀ :=
  (isGoodPositionGermTame_graphSection_wholeChart hφ hsurj).isGoodPositionGermTame

/-- **The graph section of a `C^∞` map is an sc-Fredholm section in the germ reading**
(Definition 3.14, phase 2). -/
theorem isScFredholmSection_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (bundle n k).IsScFredholmSection (graphSection φ) :=
  (isScFredholmSection_graphSection_wholeChart hφ).isScFredholmSection

/-- The graph section has tame germ data at every point, germ reading (Definition 3.51, phase 2). -/
theorem isScFredholmSectionTame_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (bundle n k).IsScFredholmSectionTame (graphSection φ) :=
  (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

/-- **The germ-reading hypotheses of Theorem 3.57 hold** for the graph section of a `C^∞` map with
`0` a regular value (phase 2): sc-Fredholm in the germ reading, and in good position in a tame
chart at every zero. -/
theorem hypotheses_theorem_3_57_graphSection (hφ : ContDiff ℝ ∞ φ)
    (hreg : ∀ x, φ x = 0 → Surjective (fderiv ℝ φ x)) :
    (bundle n k).IsScFredholmSection (graphSection φ) ∧
      ∀ x, IsZeroAt (proj n k) (graphSection φ) x →
        (bundle n k).IsGoodPositionGermTame (graphSection φ) x :=
  ⟨isScFredholmSection_graphSection hφ, fun x hx =>
    isGoodPositionGermTame_graphSection hφ (hreg x (isZeroAt_graphSection_iff.1 hx))⟩

/-- The germ-reading hypotheses hold for every surjective linear map `L : ℝⁿ → ℝᵏ` (phase 2). -/
theorem hypotheses_theorem_3_57_linear (L : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ))
    (hL : Surjective L) :
    (bundle n k).IsScFredholmSection (graphSection L) ∧
      ∀ x, IsZeroAt (proj n k) (graphSection L) x →
        (bundle n k).IsGoodPositionGermTame (graphSection L) x :=
  hypotheses_theorem_3_57_graphSection L.contDiff fun x _ => by rw [L.fderiv]; exact hL

/-- **The trivial bundle separates the old hypothesis `htame` from the repaired hypotheses, germ
reading** (phase 2; the germ form of `htame_fails_repaired_holds_wholeChart`). -/
theorem htame_fails_repaired_holds (L : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ)) (hL : Surjective L) :
    ((bundle n k).IsScFredholmSection (graphSection L) ∧
      ∀ x, IsZeroAt (proj n k) (graphSection L) x →
        (bundle n k).IsGoodPositionGermTame (graphSection L) x) ∧
    ¬ ∀ c : StrongBundleChart (rnPolyfold n) (proj n k), (bundle n k).IsChart c →
      (c.isRetraction.baseRetraction c.relOpen).IsTame :=
  ⟨hypotheses_theorem_3_57_linear L hL, not_forall_isTame_of_isChart⟩

end TrivialBundle

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

/-- **Tame germ data of the graph section at every point of `H`, germ reading** (Definition 3.50,
phase 2). -/
theorem isScFredholmGermTame_graphSection (hφ : ContDiff ℝ ∞ φ) (x₀ : H m) :
    (bundle m k).IsScFredholmGermTame (graphSection φ) x₀ :=
  (isScFredholmGermTame_graphSection_wholeChart hφ x₀).isScFredholmGermTame

/-- **Good position at a regular zero, the boundary included, germ reading** (Definition 3.53,
phase 2). -/
theorem isGoodPositionGermTame_graphSection (hφ : ContDiff ℝ ∞ φ) {x₀ : H m}
    (hsurj : Surjective (fderiv ℝ φ (x₀ : Pm m)))
    (hbd : (x₀ : Pm m).1 0 = 0 → ∃ v, fderiv ℝ φ (x₀ : Pm m) v = 0 ∧ v.1 0 ≠ 0) :
    (bundle m k).IsGoodPositionGermTame (graphSection φ) x₀ :=
  (isGoodPositionGermTame_graphSection_wholeChart hφ hsurj hbd).isGoodPositionGermTame

/-- **The graph section over the half-space is an sc-Fredholm section in the germ reading**
(Definition 3.14, phase 2). -/
theorem isScFredholmSection_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (bundle m k).IsScFredholmSection (graphSection φ) :=
  (isScFredholmSection_graphSection_wholeChart hφ).isScFredholmSection

/-- Tame germ data at every point of `H`, germ reading (Definition 3.51, phase 2). -/
theorem isScFredholmSectionTame_graphSection (hφ : ContDiff ℝ ∞ φ) :
    (bundle m k).IsScFredholmSectionTame (graphSection φ) :=
  (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

/-- **The germ-reading hypotheses of Theorem 3.57 hold over the half-space**, boundary zeros
included (phase 2). -/
theorem hypotheses_theorem_3_57_halfSpace (hφ : ContDiff ℝ ∞ φ)
    (hreg : IsRegularOnHalfSpace φ) :
    (bundle m k).IsScFredholmSection (graphSection φ) ∧
      ∀ x, IsZeroAt (proj m k) (graphSection φ) x →
        (bundle m k).IsGoodPositionGermTame (graphSection φ) x :=
  ⟨isScFredholmSection_graphSection hφ, fun x hx =>
    isGoodPositionGermTame_graphSection hφ (hreg x (isZeroAt_graphSection_iff.1 hx)).1
      (hreg x (isZeroAt_graphSection_iff.1 hx)).2⟩

end HalfSpaceBundle

end Polyfold
