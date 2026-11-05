import Polyfold.Chapter3.TameGermsG
import Polyfold.Chapter3.FredholmSectionsG
import Polyfold.Chapter3.LinearizationChartsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**Theorem 3.15 for tame germ data** (Definitions 3.50, 3.51) and **the reading of good position
(Definition 3.53) in a tame chart**, in the text's germ reading of Definition 3.11 (phase 2;
Findings, Chapter 3, items 300–309).

# Tame germ data under sc⁺-perturbation, and good position in a tame chart, germ reading

## The text, paraphrased

(Definition 3.50) The data of Definition 3.11 in a strong bundle chart whose local strong bundle
`K → O` is tame.  (Definition 3.51) An sc-Fredholm section of a tame strong bundle with such data at
every smooth point.  (Theorem 3.15) `f ∈ Fred(P)`, `s ∈ Γ⁺(P)` imply `f + s ∈ Fred(P)`; the proof
does not change the chart.  (Definition 3.53, proof of Theorem 3.54) Good position at a zero is a
property of the linearization `f'(y)`, read in any chart.

## What is formalized

* `Polyfold.StrongBundle.IsGoodPositionGerm.toTame`: **good position can be read in the tame chart
  of the germ data** (germ form of `IsGoodPositionGermWholeChart.toTame`): if `(f, y)`, `f(y) = 0`, is in good
  position in the germ reading (`IsGoodPositionGerm`, some centred chart) and has tame germ data
  (`IsScFredholmGermTame`), it is in good position in the tame chart (`IsGoodPositionGermTame`).
* `Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd` and
  **`Polyfold.theorem_3_15_tame`**:
  Theorem 3.15 for tame germ data in the germ reading (the chart step
  `StrongBundle.sectionAdd_chartData_germ` keeps the chart, hence its tameness).

## What the text leaves implicit, and the choices made

* In `IsGoodPositionGerm.toTame` the chart `c₁` of the good position is centred at `y`, so the
  point of the non-centred-chart assembly (`isGoodPositionAtGerm_of_chart`) is `z = 0`, which lies
  in every germ; the surjectivity onto `K_0 = ρ(0)F` is condition (1) of good position in `c₁`, so
  no Fredholm input (Proposition 3.52) is needed — the old proof went through the dense form
  `isGoodPositionAt_of_chart_dense`, which needs the closed range in the target chart.
* The good position in the tame chart is stated for the derivative family `scDerivGerm G g` of the
  filling germ `g` of the tame chart on its own germ `G`; by `IsGoodPositionAtGerm.of_isSc1GermWith`
  it holds for every family on every germ.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

open StrongRetr

namespace StrongBundle

/-- **Good position in the tame chart of the germ data, germ reading** (phase 2; the germ form of
`IsGoodPositionGermWholeChart.toTame`, Definition 3.53 with Definition 3.50): if `(f, y)`, `f(y) = 0`, is in
good position in the germ reading (`IsGoodPositionGerm`, in some centred chart `c₁` with a filling
germ `g₁` and a derivative family `Dg₁`) and has germ data in a tame chart
(`IsScFredholmGermTame`), then it is in good position in that tame chart
(`IsGoodPositionGermTame`).  In `c₁`, `Dg₁(0)` maps `T₀O₁` onto `K₀ = ρ(0)F` and
`ker Dg₁(0) ⊆ T₀O₁` is in good position to `C = C₀`; the non-centred assembly
`isGoodPositionAtGerm_of_chart` (with `z = 0`) carries both to the tame chart. -/
theorem IsGoodPositionGerm.toTame (hf : B.IsScSmoothSection f) {y : X}
    (hg : B.IsGoodPositionGerm f y) (hy : B.IsScFredholmGermTame f y) (hy0 : IsZeroAt P f y) :
    B.IsGoodPositionGermTame f y := by
  obtain ⟨-, c₁, hc₁, hyV₁, hφ0₁, h0U₁, g₁, s₁, hfill₁, -, -, -, G₁, Dg₁, -, hDg₁, hgp₁⟩ := hg
  obtain ⟨hys, c, hct, hyV, hφ0, h0U, g, s, hfill, hs, hs0, hconj⟩ := hy
  obtain ⟨G, hGU, hgsm, -⟩ := hfill.germ
  have hDg : IsSc1GermWith G g (scDerivGerm G g) := (hgsm 1).isSc1.isSc1GermWith_scDerivGerm
  obtain ⟨n, Wq, T, hT⟩ := c₁.φ.model.isPartialQuadrant
  have hz : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ y := by rw [map_zero, hφ0₁]
  have h0O₁ : (0 : c₁.φ.model.E 0) ∈ r c₁.R '' c₁.U := by
    rw [c₁.r_image, ← hφ0₁]; exact c₁.φ.mapsTo_model y hyV₁
  refine ⟨hys, c, hct, hyV, hφ0, h0U, g, s, hfill, hs, hs0, hconj, G, scDerivGerm G g, hGU, hDg,
    ?_⟩
  refine StrongBundle.isGoodPositionAtGerm_of_chart hf hy0 hc₁ hyV₁ hz h0U₁ h0O₁ hDg₁
    (G₁.zero_mem 1) ?_ T hT ?_ ?_ hct.1 hyV hφ0 h0U hfill hGU hDg
  · -- `f̂ = g₁` on `O` near `φ₁(y) = 0`
    have h1 := hfill₁.eq_on
    rw [c₁.r_image] at h1
    rw [hφ0₁]
    exact h1
  · -- `K₀ = ρ(0)F = Dg₁(0)(T₀O)`
    intro k hk
    rw [hφ0₁] at hk
    exact hgp₁.surj k ⟨k, ρ_eq_self_of_mem_K c₁.isRetraction h0U₁ hk⟩
  · -- the kernel condition at `0`, where `C_0 = C` and `ker Dg₁(0) ⊆ T₀O`
    rw [hφ0₁, partialQuadrantAtWith_zero, ← hT, inf_eq_left.2 hgp₁.kernel.le]
    exact hgp₁.kernel

/-- **Theorem 3.15, the germ property, in a tame chart, germ reading** (phase 2; the germ form of
`IsScFredholmGermTameWholeChart.sectionAdd`): if `(f, x)` has germ data in a tame chart in the germ reading
and `s` is an sc⁺-section, then `(f + s, x)` has germ data in the same tame chart (filling germ
`g + ŝ ∘ r`, sc⁺-germ `ŝ₁ ∘ r + t₀`, `sectionAdd_chartData_germ`). -/
theorem IsScFredholmGermTame.sectionAdd {x : X} (hfs : IsSection P f)
    (hg : B.IsScFredholmGermTame f x) (hs : B.IsScPlusSection s) :
    B.IsScFredholmGermTame (Polyfold.sectionAdd P f s) x := by
  obtain ⟨hxs, c, hct, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := sectionAdd_chartData_germ hfs hs hct.1 h0U hfill ht₀ ht₀0 hconj
  exact ⟨hxs, c, hct, hxV, h0, h0U, _, _, h1, h2, h3, h4⟩

end StrongBundle

/-- **Theorem 3.15 for a tame strong bundle, germ reading** (phase 2; the germ form of
`theorem_3_15_tame_wholeChart`, Definition 3.51): if `f` is an sc-Fredholm section with tame germ data in the
germ reading (`IsScFredholmSectionTame`) and `s` is an sc⁺-section, then `f + s` is one
(`theorem_3_15`, and the germ data in the same tame chart,
`IsScFredholmGermTame.sectionAdd`). -/
theorem theorem_3_15_tame (hf : B.IsScFredholmSectionTame f) (hs : B.IsScPlusSection s) :
    B.IsScFredholmSectionTame (sectionAdd P f s) where
  toIsScFredholmSection := theorem_3_15 hf.toIsScFredholmSection hs
  germTame x hx := (hf.germTame x hx).sectionAdd hf.isScSmooth.1 hs

end Polyfold
