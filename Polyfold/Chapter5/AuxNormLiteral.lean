import Polyfold.Chapter3.StrongBundleMaximalAtlas
import Polyfold.Chapter5.AuxNorm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.1,
**Lemma 5.2** in the text's literal form *(book 2017: Lemma 5.1; see `BookConcordance.md`)*.

# Lemma 5.2 with the bounds on the whole domain of the chart

## The text, paraphrased

(Lemma 5.2) For a continuous `N : Y_{0,1} → ℝ` which is a complete norm on every fibre, (i) `N`
is an auxiliary norm iff (ii) every `x` has a strong bundle isomorphism `Φ : Y|V → K` and
constants `0 < c < C` with `c·N(w) ≤ |h|₁ ≤ C·N(w)` for `w ∈ P⁻¹(V)`, `Φ(w) = (p, h)`.

## What is formalized

* `Polyfold.lemma_5_2_literal`: (ii) with `V` the domain of the base chart of `Φ`, as the text
  states it.  From `Polyfold.lemma_5_2` (where the bounds hold on a neighbourhood `V ⊆ dom φ` of
  `x`) by restricting the chart to `V` (`StrongBundleChart.restrict`,
  `StrongBundle.IsChart.restrict`; the norm `|h|₁` does not change,
  `StrongBundleChart.liftOne_restrict`).

## What the text leaves implicit, and the choices made

* The text's proof only gives the bounds "for `P(w)` close to `x`"; to have them on the domain of
  `Φ` the chart must be shrunk, which the text does silently (round-trip item V5.4).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **Lemma 5.2, in the text's literal form**: for a continuous `N : Y_{0,1} → ℝ` which is a
complete norm on every fibre, `N` is an auxiliary norm if and only if every `x ∈ X` lies in the
domain `V` of (the base chart of) a strong bundle chart `Φ` of `P` with constants `0 < a < A` such
that `a·N(w) ≤ |h|₁ ≤ A·N(w)` for **all** `w ∈ Y_{0,1}` with `P(w) ∈ V`, `Φ(w) = (p, h)`.  From
`Polyfold.lemma_5_2` by restricting the chart to the neighbourhood on which the bounds hold
(`StrongBundle.IsChart.restrict`; round-trip item V5.4). -/
theorem lemma_5_2_literal {N : B.One → ℝ} (hcont : Continuous N)
    (hfib : ∀ x, B.IsCompleteFiberNorm N x) :
    B.IsAuxNorm N ↔ ∀ x, ∃ c : StrongBundleChart PX P, B.IsChart c ∧ x ∈ c.φ.source ∧
      ∃ a A : ℝ, 0 < a ∧ a < A ∧ ∀ w : B.One, P (B.oneVal w) ∈ c.φ.source →
        a * N w ≤ ‖(c.liftOne (B.oneVal w)).2‖ ∧ ‖(c.liftOne (B.oneVal w)).2‖ ≤ A * N w := by
  rw [lemma_5_2 hcont hfib]
  constructor
  · intro H x
    obtain ⟨c, hc, V, hVo, hxV, hVc, a, A, ha, haA, hb⟩ := H x
    exact ⟨c.restrict hVc hVo, hc.restrict hVc hVo, hxV, a, A, ha, haA, fun w hw => hb w hw⟩
  · intro H x
    obtain ⟨c, hc, hx, a, A, ha, haA, hb⟩ := H x
    exact ⟨c, hc, c.φ.source, c.φ.isOpen_source, hx, subset_rfl, a, A, ha, haA, hb⟩

end Polyfold
