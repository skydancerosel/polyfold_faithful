import Polyfold.Chapter6.ChartOrientationSpace
import Polyfold.Chapter14.HalfSpaceBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
pp. 219–230: the hypotheses of **Theorems 6.6.11, 6.6.13 and 6.6.17** for a strong bundle with a
chart over the whole base hold on the half-space bundle.

# Orientations on the half-space bundle

## The text, paraphrased

Theorems 6.6.11, 6.6.13 and 6.6.17 are stated for an sc-Fredholm section of a strong bundle over
a tame M-polyfold; the sc⁺-sections of the proofs are written in a chart, "assuming `X = U`".

## What is formalized

For the trivial bundle `H × ℝᵏ → H` over the half-space `H = [0, ∞) × ℝᵐ` (non-empty boundary,
non-zero fibres for `k ≥ 1`) and the graph section `x ↦ (x, φ(x))` of a `C^∞` map
`φ : ℝ × ℝᵐ → ℝᵏ`:

* `theorem_6_6_17_of_chart_hypotheses_halfSpace`: `H` is tame, the atlas has a chart over the
  whole base, the graph section has tame germ data, `0 ∈ ∂H`, and the fibres are non-zero.
* `theorem_6_6_11_halfSpace`, `theorem_6_6_13_halfSpace`, `theorem_6_6_17_halfSpace`: the
  conclusions of `theorem_6_6_11_of_chart`, `theorem_6_6_13_of_chart` and
  `theorem_6_6_17_of_chart` for this section.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

variable {m k : ℕ} {φ : Pm m → (Fin k → ℝ)}

variable (m) in
/-- The half-space `H = [0, ∞) × ℝᵐ` is a tame M-polyfold. -/
theorem isTame_basePoly : (basePoly m).IsTame := MPolyfold.quadrantPolyfold_isTame 1 (rnSc m)

variable (m k) in
/-- The atlas of `H × ℝᵏ → H` has a chart over the whole base (its only chart). -/
theorem exists_chart_source_eq_univ :
    ∃ c ∈ (bundle m k).atlas.charts, c.φ.source = univ :=
  ⟨chart₀, mem_singleton _, rfl⟩

/-- **The hypotheses of the theorems of §6.6 for a chart over the whole base hold with
`∂X ≠ ∅` and non-zero fibres**: the half-space `H = [0, ∞) × ℝᵐ` is tame, the atlas of
`H × ℝᵏ → H` has a chart over the whole base, the graph section of a `C^∞` map has tame germ
data, the corner `0` lies on the boundary, and every fibre is a non-zero vector space
(`k ≥ 1`). -/
theorem theorem_6_6_17_of_chart_hypotheses_halfSpace [NeZero k] (hφ : ContDiff ℝ ∞ φ) :
    (basePoly m).IsTame ∧ (∃ c ∈ (bundle m k).atlas.charts, c.φ.source = univ) ∧
      (bundle m k).IsScFredholmSectionTame (graphSection φ) ∧
      (⟨0, fun _ => le_rfl⟩ : H m) ∈ (basePoly m).boundary ∧
      ∀ x : H m, Nontrivial (proj m k ⁻¹' {x}) :=
  ⟨isTame_basePoly m, exists_chart_source_eq_univ m k,
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame,
    zero_mem_boundary_halfSEP m k, nontrivial_fibre_halfSEP m k⟩

/-- **Theorem 6.6.11 on the half-space bundle**: every point of `H` has an open neighbourhood
with the local propagation property for the graph section. -/
theorem theorem_6_6_11_halfSpace (hφ : ContDiff ℝ ∞ φ) (x : H m) :
    haveI := paracompactSpace_rn_prod (basePoly m)
    haveI := paracompactSpace_rn_pullback (bundle m k)
    ∃ (c : StrongBundleChart (basePoly m) (proj m k)) (hc : (bundle m k).IsChart c)
      (U : Set (H m)), IsOpen U ∧ x ∈ U ∧
      HasLocalPropagation (graphSection φ)
        (isScFredholmSectionTame_graphSection_wholeChart
          hφ).isScFredholmSectionTame.toIsScFredholmSection c hc U := by
  have := paracompactSpace_rn_prod (basePoly m)
  have := paracompactSpace_rn_pullback (bundle m k)
  have := paracompactSpace_rn_rn_prod (basePoly m)
  have := paracompactSpace_rn_rn_pullback (bundle m k)
  exact theorem_6_6_11_of_chart (isTame_basePoly m) (exists_chart_source_eq_univ m k)
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame
    (smoothSet_eq_univ (m := m) ▸ mem_univ x)

/-- **Theorem 6.6.13 on the half-space bundle**: the functor `Γ_f` of the graph section exists
and is unique. -/
theorem theorem_6_6_13_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (basePoly m)
    haveI := paracompactSpace_rn_pullback (bundle m k)
    ∃! G : ∀ x y : PathCat (basePoly m), (x ⟶ y) →
        (Orx (graphSection φ) (isScFredholmSectionTame_graphSection_wholeChart
            hφ).isScFredholmSectionTame.toIsScFredholmSection x.pt x.smooth ≃
          Orx (graphSection φ) (isScFredholmSectionTame_graphSection_wholeChart
            hφ).isScFredholmSectionTame.toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat (basePoly m)) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty (graphSection φ) (isScFredholmSectionTame_graphSection_wholeChart
        hφ).isScFredholmSectionTame.toIsScFredholmSection G :=
  theorem_6_6_13_of_chart (isTame_basePoly m) (exists_chart_source_eq_univ m k)
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

/-- **Theorem 6.6.17 on the half-space bundle**: the orientation space `O_f` of the graph
section has exactly one Hausdorff topology with properties (1), (2) and (3). -/
theorem theorem_6_6_17_halfSpace (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (basePoly m)
    haveI := paracompactSpace_rn_pullback (bundle m k)
    ∃! t : TopologicalSpace (OrSpace (graphSection φ)
        (isScFredholmSectionTame_graphSection_wholeChart
          hφ).isScFredholmSectionTame.toIsScFredholmSection),
      IsOrientationTopology (graphSection φ) (isScFredholmSectionTame_graphSection_wholeChart
        hφ).isScFredholmSectionTame.toIsScFredholmSection t :=
  theorem_6_6_17_of_chart (isTame_basePoly m) (exists_chart_source_eq_univ m k)
    (isScFredholmSectionTame_graphSection_wholeChart hφ).isScFredholmSectionTame

end HalfSpaceBundle

end Polyfold
