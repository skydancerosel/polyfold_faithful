import Polyfold.Chapter9.GapP2_E1_SheetIntegration
import Polyfold.Chapter9.GapP2_DSheetEssential
import Mathlib.MeasureTheory.Function.Jacobian

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445: the data from which the integral
`∫_K ω|(M, o)` of an sc-differential `n`-form over a measurable subset of an oriented
`n`-dimensional submanifold is built (gap G.107).  Numbers and pages are the 2021 text's.

# Graph charts of a sheet and the pointwise evaluation of forms

## What is formalized

* `MPolyfold.GraphChart P n N`: the submanifold `N` lies in the domain of one chart `φ` of the
  M-polyfold and is, in this chart, a graph over `ℝⁿ`: a continuous linear `p : E₀ → ℝⁿ` is
  injective on `φ(N)`, the inverse `u ↦ φ(q(u))` is differentiable within `p(φ(N))` (level-`0`
  norm), with derivative `L_y` at `p(φ(y))`, a linear isomorphism of `ℝⁿ` onto the chart image of
  `T_yN`, depending continuously on `y ∈ N`.  Its existence near every point of an
  `n`-dimensional submanifold is in `GapP2_E3_GraphChartExists.lean`.
* `EpGroupoid.FormEval X n Ω`: the values `ω(α₁, …, αₙ)` of the forms `ω ∈ Ω` on `n` tangent
  vectors, with the properties used for the integral: linear in `ω`; on the tangent space of a
  submanifold, alternating and multilinear (stated through determinants, `ev_det`); invariant
  under the tangent maps `Tψ` of the morphisms (Definition 8.2.1); continuous along continuous
  frame fields of a submanifold.
* `integral_image_eq_of_det`: the change of variables in `ℝⁿ` on a measurable set, with a sign.

## The choices made

A graph chart is a chart of the sheet read in a chart of the ambient M-polyfold; no corner
structure of the sheet is used, and derivatives are taken within `p(φ(N))`, which need not be
open (boundary and corner points).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u

/-! ### The change of variables on a measurable set -/

/-- **Change of variables with a sign**: `τ` injective on the measurable set `A ⊆ ℝⁿ`,
differentiable within `A` with derivative `D u`, `s · det D u > 0` on `A` (`s = ±1`), and
`ρ(u) = det(D u) ρ'(τ u)` on `A`.  Then `∫_{τ(A)} ρ' = s ∫_A ρ`. -/
theorem integral_image_eq_of_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {A : Set E} (hA : MeasurableSet A) {τ : E → E} {D : E → E →L[ℝ] E}
    (hD : ∀ u ∈ A, HasFDerivWithinAt τ (D u) A u) (hinj : InjOn τ A) {ρ ρ' : E → ℝ} {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hdet : ∀ u ∈ A, 0 < s * (D u).det)
    (hρ : ∀ u ∈ A, ρ u = (D u).det * ρ' (τ u)) :
    ∫ v in τ '' A, ρ' v ∂μ = s * ∫ u in A, ρ u ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hA hD hinj, ← integral_const_mul]
  refine setIntegral_congr_fun hA fun u hu => ?_
  have h1 := hdet u hu
  have habs : |(D u).det| = s * (D u).det := by
    rcases hs with rfl | rfl
    · rw [one_mul] at h1 ⊢; exact abs_of_pos h1
    · rw [neg_one_mul] at h1 ⊢; exact abs_of_neg (by linarith)
  change |(D u).det| • ρ' (τ u) = s * ρ u
  rw [hρ u hu, habs, smul_eq_mul]; ring

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **A graph chart of the submanifold `N`** (of dimension `n`): `N` lies in the domain of the
chart `φ`, the continuous linear map `p : E₀ → ℝⁿ` is injective on `φ(N)` with inverse
`u ↦ φ(q(u))`, differentiable within `p(φ(N))` at `p(φ(y))` with derivative `L y`, a right inverse
of `p` with range the chart image of `T_yN`; `y ↦ L y` is continuous on `N`. -/
structure GraphChart (P : MPolyfold X) (n : ℕ) (N : Set X) where
  /-- The chart of the ambient M-polyfold. -/
  φ : MChart X
  isChart : P.IsChart φ
  subset_source : N ⊆ φ.source
  /-- The projection to `ℝⁿ`. -/
  p : φ.model.E 0 →L[ℝ] EuclideanSpace ℝ (Fin n)
  /-- The parametrization of `N`, inverse to `y ↦ p (φ y)` on `N`. -/
  q : EuclideanSpace ℝ (Fin n) → X
  q_coord : ∀ y ∈ N, q (p (φ y)) = y
  /-- The derivative of `u ↦ φ (q u)` at `p (φ y)`. -/
  L : X → EuclideanSpace ℝ (Fin n) →L[ℝ] φ.model.E 0
  measurableSet_dom : MeasurableSet ((fun y => p (φ y)) '' N)
  p_L : ∀ y ∈ N, ∀ v, p (L y v) = v
  range_L : ∀ y ∈ N, range (L y) = P.chartTangent isChart N y
  hasFDerivWithinAt : ∀ y ∈ N,
    HasFDerivWithinAt (fun u => φ (q u)) (L y) ((fun y => p (φ y)) '' N) (p (φ y))
  continuousOn_L : ContinuousOn L N

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **The values of the forms of `Ω` on `n` tangent vectors** (2021 Definition 8.2.1, p. 281, for
the forms; §9.5 for the use): `ev ω α = ω(α₁, …, αₙ)` for tangent vectors `αᵢ` over one point.
On the tangent space `T_yN` of a submanifold the value is alternating and multilinear: if the
chart vectors of `β` are the combinations `∑ᵢ Mᵢⱼ αᵢ` of those of `α`, then
`ω(β) = det M · ω(α)`.  The value is invariant under the tangent maps of the morphisms, and
continuous along the frame fields of a submanifold whose chart vectors are continuous. -/
structure FormEval (X : EpGroupoid Obj Mor) (n : ℕ) (Ω : Type*) [AddCommGroup Ω] [Module ℝ Ω]
    where
  /-- `ω(α₁, …, αₙ)`. -/
  ev : Ω → (Fin n → X.PObj.TangentSpace) → ℝ
  ev_add : ∀ ω τ α, ev (ω + τ) α = ev ω α + ev τ α
  ev_smul : ∀ (c : ℝ) ω α, ev (c • ω) α = c * ev ω α
  ev_det : ∀ ω {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ {φ : MChart Obj} (hφ : X.PObj.IsChart φ), y ∈ φ.source →
    ∀ (α β : Fin n → X.PObj.TangentSpace), (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
    (∀ i, β i ∈ X.PObj.submanifoldTangent N y) → ∀ M : Matrix (Fin n) (Fin n) ℝ,
    (∀ j, MPolyfold.chartVec hφ (β j) = ∑ i, M i j • MPolyfold.chartVec hφ (α i)) →
    ev ω β = M.det * ev ω α
  ev_mor : ∀ ω {N : Set Obj}, X.PObj.IsSmoothSubmanifold N → ∀ {y : Obj}, y ∈ N →
    ∀ ψ : Mor, X.src ψ = y → ∀ α : Fin n → X.PObj.TangentSpace,
    (∀ i, α i ∈ X.PObj.submanifoldTangent N y) →
    ev ω (fun i => X.tangentMor ψ (α i)) = ev ω α
  ev_continuousOn : ∀ ω {N : Set Obj}, X.PObj.IsSmoothSubmanifold N →
    ∀ {φ : MChart Obj} (hφ : X.PObj.IsChart φ) {K : Set Obj}, K ⊆ N ∩ φ.source →
    ∀ e : Obj → Fin n → X.PObj.TangentSpace,
    (∀ z ∈ K, ∀ i, e z i ∈ X.PObj.submanifoldTangent N z) →
    ContinuousOn (fun z i => MPolyfold.chartVec hφ (e z i)) K →
    ContinuousOn (fun z => ev ω (e z)) K

end EpGroupoid

end Polyfold
