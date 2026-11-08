import Polyfold.Chapter9.Orientation
import Polyfold.Chapter9.AppendixSlices
import Polyfold.Chapter6.OrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations", on `ℝᵐ` and under graph hypotheses: **Lemma 9.3.4**
(2021 pp. 423–424; 2017: Lemma 9.10), the oriented form of **Proposition 9.2.8** (2021 p. 413;
2017: Proposition 9.1) used in its proof, and the witnesses of **Definition 9.3.2** (2021 p. 423;
2017: Definition 9.8), **Remark 9.3.3** (2021 p. 423; 2017: Remark 9.8) and **Example 9.3.5**
(2021 p. 425; 2017: Example 9.1) with **Theorem 9.2.1**'s independence (2021 p. 409; 2017:
Theorem 9.1) discharged.  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# Orientations on `ℝᵐ`

## The text, paraphrased

Definition 9.3.2 orients `Θ` by oriented local branching structures whose oriented tangent sums
`∑ σᵢ T_x(Mᵢ, oᵢ)` do not depend on the structure; the unoriented sums are independent by
Theorem 9.2.1.  Lemma 9.3.4: two orientations of `Θ` which agree at the good points agree.  Its
proof, at a bad point `x`, groups the oriented submanifolds by their tangent spaces at `x`, takes
good points converging to `x` that lie on exactly one block of each class (Proposition 9.2.8),
and passes to the limit using the continuity of the orientations.

## What is formalized

* Theorem 9.2.1's independence discharged on `ℝᵐ` (by `hasIndependentTangentSums_rn`) in the
  witnesses: `isOrientation_sum_trivial_rn`, `isOrientation_sum_trivial_rn'`,
  `isOrientationOfDim_sum_trivial_rn`, `orientedSection_comp_grForgetFunctor_obj_rn`,
  `orientedLift1/2_isOrientation_rn`, `orientedLift1/2_isOrientationOfDim_rn`,
  **Example 9.3.5**: `example_9_3_5_rn`, and `lemma_9_3_4_mixed_dim_rn`.
* Bridges between the chart notions of `OrientationTangent` and `TangentSlices` (all `rfl`):
  `chartVec_eq_tangentChartMap_snd`, `chartVec_image_eq_chartTangent`, `injOn_chartVec_iff`.
* Relative orientations are locally constant:
  `SubmanifoldOrientation.exists_isOpen_tangent_eq_iff`, from determinants of frames read in one
  chart (`frameDet`, `orientation_eq_iff_frameDet`, `frames_eq_iff_frameDet`) and chart changes of
  frame fields (`continuousOn_chartVec_of_continuousOn`), under `HasContinuousLevelOneOn`
  (satisfied on `ℝᵐ`: `hasContinuousLevelOneOn_rn`).
* `IsGraphBallAt`, `HasGraphBallAt`: the graph representation over a neighbourhood of `0` in the
  tangent space.  It gives the ray form of `TangentSlices` (`IsGraphBallAt.isGraphChartAt`,
  `HasGraphBallAt.hasGraphChartsAt`) and holds on `ℝᵐ` (`isGraphBallAt_rn`, `hasGraphBallAt_rn`).
* **Proposition 9.2.8 for oriented families**: `hasOrientedGoodPointsAt_of_hasGraphBallAt`; on
  `ℝᵐ` at every point and in every dimension: `hasOrientedGoodPointsAt_rn`.
* **Lemma 9.3.4**: `lemma_9_3_4_of_hasGraphBallAt`, and on `ℝᵐ` without further hypotheses
  `lemma_9_3_4_rn`; applied to Example 9.3.5: `exists_goodSet_exampleT1_ne_exampleT2`.

## What the text leaves implicit, and the choices made

* The good points on a prescribed block come from the genericity argument of Lemma 9.2.7 (2)
  (2021 pp. 412–413), which moves the foot point in an open subset of `T_xM`.  The ray form
  `IsGraphChartAt` (Lemmas 9.2.10, 9.2.11) gives points over the rays `t v`, `v ∈ K`, only, which
  does not seem to suffice for this; we use the ball form `HasGraphBallAt` (every direction
  admissible, as at points of `ℝᵐ`).
* The continuity of orientations is given by frame fields in charts depending on the submanifold;
  comparing the fields of two sheets in one chart uses the continuity of the level-`1`
  coordinates along the sheet (`HasContinuousLevelOneOn`).
* For `n = 0` the good point is `x` itself.

## Not formalized, and why

* `HasGraphBallAt` and `HasContinuousLevelOneOn` on general M-polyfolds: at boundary points only
  a cone of directions is admissible (a cone form of the ball would be needed), and the second is
  the `sc⁺`-retraction argument for finite-dimensional submanifolds.
* The continuity of the boundary orientation `o_{∂M}` (Definitions 9.3.8, 9.3.10) and
  `T_y∂M = T^R_yM` with the outward direction from the cones `C_yM` in place of the data `K`, `e`:
  on `ℝᵐ` the boundary is empty, so a witness needs an M-polyfold with boundary.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

section Witnesses

variable {n : ℕ}

open scoped Classical in
/-- **The witness of Definition 9.3.2 on `ℝⁿ`** (2021 p. 423), with Theorem 9.2.1's independence
discharged: for finitely many closed oriented submanifolds `(Mᵢ, oᵢ)` of `ℝⁿ` with weights
`σᵢ > 0`, the oriented sum is an orientation of `Θ = ∑ σᵢ 1_{Mᵢ}`. -/
theorem isOrientation_sum_trivial_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i)) :
    (trivial (rnPolyfold n)).IsOrientation (fun y => ∑ i with y ∈ M i, σ i)
      (orientedSumRn M σ o) :=
  isOrientation_sum_rn M σ hσ hM hc o (hasIndependentTangentSums_rn rfl _)

open scoped Classical in
/-- `isOrientation_sum_trivial_rn` for any `Θ` equal to `∑ σᵢ 1_{Mᵢ}` (Definition 9.3.2,
2021 p. 423). -/
theorem isOrientation_sum_trivial_rn' {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {dim : ι → ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) (dim i)) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) (dim i)) {Θ : (Fin n → ℝ) → ℚ}
    (hΘ : Θ = fun y => ∑ i with y ∈ M i, σ i) :
    (trivial (rnPolyfold n)).IsOrientation Θ (orientedSumRn M σ o) :=
  isOrientation_sum_rn' M σ hσ hM hc o hΘ (hasIndependentTangentSums_rn rfl _)

open scoped Classical in
/-- **An `m`-dimensional orientation on `ℝⁿ`** (the setting of Lemma 9.3.4, 2021 p. 423), with
Theorem 9.2.1's independence discharged. -/
theorem isOrientationOfDim_sum_trivial_rn {ι : Type} [Fintype ι] (M : ι → Set (Fin n → ℝ))
    (σ : ι → ℚ) (hσ : ∀ i, 0 < σ i) {m : ℕ}
    (hM : ∀ i, (rnPolyfold n).IsSubmanifoldOfDim (M i) m) (hc : ∀ i, IsClosed (M i))
    (o : ∀ i, (rnPolyfold n).SubmanifoldOrientation (M i) m) {Θ : (Fin n → ℝ) → ℚ}
    (hΘ : Θ = fun y => ∑ i with y ∈ M i, σ i) :
    (trivial (rnPolyfold n)).IsOrientationOfDim Θ m (orientedSumRn M σ o) :=
  isOrientationOfDim_sum_rn M σ hσ hM hc o hΘ (hasIndependentTangentSums_rn rfl _)

/-- **The oriented section forgets to the tangent section** (Definition 9.3.2 and
Theorem 9.2.1, 2021 pp. 409, 423) for ep-groupoids with object M-polyfold `ℝᵐ`, with the
independence discharged. -/
theorem orientedSection_comp_grForgetFunctor_obj_rn {m : ℕ} {Mor : Type} [TopologicalSpace Mor]
    [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid (Fin m → ℝ) Mor}
    (hX : X.PObj = rnPolyfold m) {Θ : (Fin m → ℝ) → ℚ} {T : (Fin m → ℝ) → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (hΘ : X.IsBranchedEpSubgroupoid Θ) (x : X.SmoothCat) :
    (X.orientedSection hT ⋙ X.grForgetFunctor).obj x =
      (X.tangentSection hΘ (hasIndependentTangentSums_rn hX Θ)).obj x :=
  orientedSection_comp_grForgetFunctor_obj hT hΘ _ x

end Witnesses

end EpGroupoid

open MPolyfold EpGroupoid

/-- The lift `T̂¹` of Example 9.3.5 (2021 p. 425) is an orientation, with Theorem 9.2.1's
independence discharged. -/
theorem orientedLift1_isOrientation_rn (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (orientedLift1 ε) :=
  orientedLift1_isOrientation (hasIndependentTangentSums_rn rfl _) ε

/-- The lift `T̂²` of Example 9.3.5 (2021 p. 425) is an orientation, with Theorem 9.2.1's
independence discharged. -/
theorem orientedLift2_isOrientation_rn (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientation example935Theta (orientedLift2 ε) :=
  orientedLift2_isOrientation (hasIndependentTangentSums_rn rfl _) ε

/-- The lift `T̂¹` of Example 9.3.5 is a `1`-dimensional orientation (independence
discharged). -/
theorem orientedLift1_isOrientationOfDim_rn (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift1 ε) :=
  orientedLift1_isOrientationOfDim (hasIndependentTangentSums_rn rfl _) ε

/-- The lift `T̂²` of Example 9.3.5 is a `1`-dimensional orientation (independence
discharged). -/
theorem orientedLift2_isOrientationOfDim_rn (ε : Bool → Bool) :
    (trivial (rnPolyfold 2)).IsOrientationOfDim example935Theta 1 (orientedLift2 ε) :=
  orientedLift2_isOrientationOfDim (hasIndependentTangentSums_rn rfl _) ε

/-- **Example 9.3.5, 2021 p. 425 (2017: Example 9.1)**, the claims of `example_9_3_5` with
Theorem 9.2.1's independence discharged: `Θ` is a branched ep⁺-subgroupoid with the two
orientations `T̂¹`, `T̂²`, equal at `0` and different at `(s, β⁺⁺(s))`, `s > 0`, and no lift
`T̂²_δ` equals `T̂¹` on both branches. -/
theorem example_9_3_5_rn :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid example935Theta ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT1 ∧
    (trivial (rnPolyfold 2)).IsOrientation example935Theta exampleT2 ∧
    exampleT1 0 = exampleT2 0 ∧
    (∀ s : ℝ, 0 < s → exampleT1 (ptPP s) ≠ exampleT2 (ptPP s)) ∧
    ∀ (δ : Bool → Bool) (s : ℝ), 0 < s →
      orientedLift2 δ (ptPP s) ≠ exampleT1 (ptPP s) ∨
        orientedLift2 δ (ptMM (-s)) ≠ exampleT1 (ptMM (-s)) :=
  example_9_3_5 (hasIndependentTangentSums_rn rfl _)

/-- **Lemma 9.3.4 without equidimensionality** (`lemma_9_3_4_mixed_dim`, 2021 pp. 423–424) with
the independence discharged: two orientations of `Θ = 1_{ℝ × 0} + 1_{(0,0)}` agree at the good
points and differ at `0`, so the statement for mixed dimensions does not hold as we read it. -/
theorem lemma_9_3_4_mixed_dim_rn :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid mixedTheta ∧
    ∃ T₁ T₂ : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ,
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₁ ∧
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₂ ∧
      (∀ y ∈ (trivial (rnPolyfold 2)).goodSet mixedTheta, T₁ y = T₂ y) ∧ T₁ 0 ≠ T₂ 0 :=
  lemma_9_3_4_mixed_dim (hasIndependentTangentSums_rn rfl _)

/-! ### Bridges between the chart notions -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X} (hφ : P.IsChart φ)

/-- The chart vector `chartVec` of `OrientationTangent` is the second component of the tangent
chart `tangentChartMap` of `TangentSlices`. -/
theorem chartVec_eq_tangentChartMap_snd (α : P.TangentSpace) :
    chartVec hφ α = (tangentChartMap hφ α).2 := rfl

/-- The chart image of `T_yA` in `OrientationBasic` (`chartVec_image_submanifoldTangent`) is the
`chartTangent` of `TangentSlices`. -/
theorem chartVec_image_eq_chartTangent (A : Set X) (y : X) :
    chartVec hφ '' P.submanifoldTangent A y = P.chartTangent hφ A y := rfl

/-- Injectivity of `chartVec` is injectivity of the second component of `tangentChartMap`. -/
theorem injOn_chartVec_iff (s : Set P.TangentSpace) :
    InjOn (chartVec hφ) s ↔ InjOn (fun α => (tangentChartMap hφ α).2) s := Iff.rfl

/-- `chartVec_injOn` and `injOn_tangentChartMap_snd` are the same statement. -/
example {y : X} (hyφ : y ∈ φ.source) : chartVec_injOn hφ hyφ = injOn_tangentChartMap_snd hφ hyφ :=
  rfl

end MPolyfold

section FrameDet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The determinant `det (Λ w₁, …, Λ wₙ)` of a frame `w` read through `Λ : E → ℝⁿ`. -/
def frameDet (Λ : E →L[ℝ] (Fin n → ℝ)) (w : Fin n → E) : ℝ :=
  Matrix.det (Matrix.of fun i j => Λ (w i) j)

/-- `frameDet` is the determinant of `Λ ∘ w` in the standard basis of `ℝⁿ`. -/
theorem frameDet_eq (Λ : E →L[ℝ] (Fin n → ℝ)) (w : Fin n → E) :
    frameDet Λ w = (Pi.basisFun ℝ (Fin n)).det (fun i => Λ (w i)) := by
  rw [Pi.basisFun_det]
  rfl

/-- `frameDet Λ` of a continuous frame field is continuous. -/
theorem ContinuousOn.frameDet {Z : Type*} [TopologicalSpace Z] (Λ : E →L[ℝ] (Fin n → ℝ))
    {w : Z → Fin n → E} {S : Set Z} (hw : ContinuousOn w S) :
    ContinuousOn (fun z => frameDet Λ (w z)) S := by
  have h : ContinuousOn (fun z => Matrix.of fun i j => Λ (w z i) j) S := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact (continuous_apply j).comp_continuousOn
      (Λ.continuous.comp_continuousOn ((continuous_apply i).comp_continuousOn hw))
  exact (continuous_id.matrix_det).comp_continuousOn h

/-- Two bases of `ℝⁿ` have the same orientation iff their determinants have the same sign. -/
theorem orientation_eq_iff_det_pos_iff (c c' : Basis (Fin n) ℝ (Fin n → ℝ)) :
    c.orientation = c'.orientation ↔
      (0 < (Pi.basisFun ℝ (Fin n)).det c ↔ 0 < (Pi.basisFun ℝ (Fin n)).det c') := by
  set e := Pi.basisFun ℝ (Fin n)
  have hc : c.orientation = e.orientation ↔ 0 < e.det c := by
    rw [eq_comm]; exact e.orientation_eq_iff_det_pos c
  have hc' : c'.orientation = e.orientation ↔ 0 < e.det c' := by
    rw [eq_comm]; exact e.orientation_eq_iff_det_pos c'
  rcases e.orientation_eq_or_eq_neg c.orientation with h | h <;>
    rcases e.orientation_eq_or_eq_neg c'.orientation with h' | h'
  · rw [h, h']; exact iff_of_true rfl (iff_of_true (hc.1 h) (hc'.1 h'))
  · rw [h, h']
    have h1 : ¬ 0 < e.det c' := fun hp => Module.Ray.ne_neg_self e.orientation
      (h'.symm.trans (hc'.2 hp)).symm
    exact iff_of_false (Module.Ray.ne_neg_self _) (fun hh => h1 (hh.1 (hc.1 h)))
  · rw [h, h']
    have h1 : ¬ 0 < e.det c := fun hp => Module.Ray.ne_neg_self e.orientation
      (h.symm.trans (hc.2 hp)).symm
    exact iff_of_false (fun hh => Module.Ray.ne_neg_self _ hh.symm)
      (fun hh => h1 (hh.2 (hc'.1 h')))
  · rw [h, h']
    have h1 : ¬ 0 < e.det c := fun hp => Module.Ray.ne_neg_self e.orientation
      (h.symm.trans (hc.2 hp)).symm
    have h2 : ¬ 0 < e.det c' := fun hp => Module.Ray.ne_neg_self e.orientation
      (h'.symm.trans (hc'.2 hp)).symm
    exact iff_of_true rfl (iff_of_false h1 h2)

/-- **Relative orientation through a linear map**: for bases `b₁`, `b₂` of a subspace `N` and a
continuous linear `Λ : E → ℝⁿ` with `det (Λ b₁) ≠ 0`, `b₁` and `b₂` have the same orientation iff
`det (Λ b₁)` and `det (Λ b₂)` have the same sign. -/
theorem orientation_eq_iff_frameDet {N : Submodule ℝ E} (Λ : E →L[ℝ] (Fin n → ℝ))
    (b₁ b₂ : Basis (Fin n) ℝ N) (hΛ : frameDet Λ (fun i => (b₁ i : E)) ≠ 0) :
    b₁.orientation = b₂.orientation ↔
      (0 < frameDet Λ (fun i => (b₁ i : E)) ↔ 0 < frameDet Λ (fun i => (b₂ i : E))) := by
  set f : N →ₗ[ℝ] (Fin n → ℝ) := (Λ : E →ₗ[ℝ] (Fin n → ℝ)).comp N.subtype with hfdef
  set e := Pi.basisFun ℝ (Fin n)
  have hli : LinearIndependent ℝ (fun i => f (b₁ i)) := by
    rw [frameDet_eq] at hΛ
    exact ((e.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hΛ)).1
  have hcard : Fintype.card (Fin n) = finrank ℝ (Fin n → ℝ) := by simp
  set c₁ := basisOfLinearIndependentOfCardEqFinrank' (fun i => f (b₁ i)) hli hcard
  have hc₁ : ∀ i, c₁ i = f (b₁ i) := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) _ hli hcard]
  let g : N ≃ₗ[ℝ] (Fin n → ℝ) := b₁.equiv c₁ (Equiv.refl _)
  have hgf : ∀ v, g v = f v := fun v => by
    have : (g : N →ₗ[ℝ] (Fin n → ℝ)) = f := b₁.ext fun i => by
      simp only [g, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, hc₁]
    exact LinearMap.congr_fun this v
  have hmap : ∀ b : Basis (Fin n) ℝ N, ⇑(b.map g) = fun i => Λ (b i : E) := fun b => by
    funext i; rw [Basis.map_apply, hgf]; rfl
  rw [← (Orientation.map (Fin n) g).injective.eq_iff, ← Basis.orientation_map,
    ← Basis.orientation_map, orientation_eq_iff_det_pos_iff, frameDet_eq, frameDet_eq, hmap,
    hmap]

end FrameDet

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **Two orientations of a tangent set compared in a chart**: for orientations `O₁`, `O₂` of
`L ⊆ T_yX` with positive frames `v₁ ∈ O₁`, `v₂ ∈ O₂`, and a continuous linear `Λ : E₀ → ℝⁿ` with
`det (Λ ∘ chartVec ∘ v₁) ≠ 0`, `O₁ = O₂` iff the two determinants have the same sign. -/
theorem frames_eq_iff_frameDet {y : X} {n : ℕ} {L : Set P.TangentSpace}
    {O₁ O₂ : Set (Fin n → P.TangentSpace)} (h₁ : P.IsOrientedAt y ⟨n, L, O₁⟩)
    (h₂ : P.IsOrientedAt y ⟨n, L, O₂⟩) {ψ : MChart X} (hψ : P.IsChart ψ) (hyψ : y ∈ ψ.source)
    (Λ : ψ.model.E 0 →L[ℝ] (Fin n → ℝ)) {v₁ v₂ : Fin n → P.TangentSpace} (hv₁ : v₁ ∈ O₁)
    (hv₂ : v₂ ∈ O₂) (hΛ : frameDet Λ (fun i => chartVec hψ (v₁ i)) ≠ 0) :
    O₁ = O₂ ↔ (0 < frameDet Λ (fun i => chartVec hψ (v₁ i)) ↔
      0 < frameDet Λ (fun i => chartVec hψ (v₂ i))) := by
  obtain ⟨N₁, hN₁, -, -, ω₁, hO₁⟩ := h₁.isChartOrientation hψ hyψ
  obtain ⟨N₂, hN₂, -, -, ω₂, hO₂⟩ := h₂.isChartOrientation hψ hyψ
  have hNN : N₂ = N₁ := SetLike.coe_injective (hN₂.trans hN₁.symm)
  subst hNN
  change O₁ = chartFrames hψ L N₂ ω₁ at hO₁
  change O₂ = chartFrames hψ L N₂ ω₂ at hO₂
  have hv₁' := hv₁
  rw [hO₁] at hv₁'
  obtain ⟨-, b₁, hb₁, hbo₁⟩ := hv₁'
  have hv₂' := hv₂
  rw [hO₂] at hv₂'
  obtain ⟨-, b₂, hb₂, hbo₂⟩ := hv₂'
  have hf₁ : (fun i => chartVec hψ (v₁ i)) = fun i => (b₁ i : ψ.model.E 0) :=
    funext fun i => (hb₁ i).symm
  have hf₂ : (fun i => chartVec hψ (v₂ i)) = fun i => (b₂ i : ψ.model.E 0) :=
    funext fun i => (hb₂ i).symm
  rw [hf₁] at hΛ ⊢
  rw [hf₂, ← orientation_eq_iff_frameDet Λ b₁ b₂ hΛ, hbo₁, hbo₂]
  constructor
  · intro hO
    have h1 := hv₁
    rw [hO, hO₂] at h1
    obtain ⟨-, b, hb, hbo⟩ := h1
    have hbb : b = b₁ := Basis.eq_of_apply_eq fun i => Subtype.ext ((hb i).trans (hb₁ i).symm)
    rw [← hbo, hbb, hbo₁]
  · intro hω
    rw [hO₁, hO₂, hω]

/-- **Chart changes preserve the continuity of tangent fields** along a set `S` on which the
level-`1` coordinates `levelLift φ 1` are continuous: if the chart vectors of `α(z) ∈ T_zX` in
`φ` depend continuously on `z ∈ S`, so do those in `ψ` (`α` is continuous into `TX`, and `Tψ` is a
chart of `TX`). -/
theorem continuousOn_chartVec_of_continuousOn {φ ψ : MChart X} (hφ : P.IsChart φ)
    (hψ : P.IsChart ψ) {S : Set X} (hSφ : S ⊆ φ.source) (hSψ : S ⊆ ψ.source)
    (hlev : ContinuousOn (levelLift φ 1) S) {α : X → P.TangentSpace}
    (hα : ∀ z ∈ S, P.levelVal 1 (P.tangentProj (α z)) = z)
    (hc : ContinuousOn (fun z => chartVec hφ (α z)) S) :
    ContinuousOn (fun z => chartVec hψ (α z)) S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact continuousOn_empty _
  have hαφ : ∀ z ∈ S, α z ∈ tangentChartSet φ := fun z hz => by
    change _ ∈ φ.source; rw [hα z hz]; exact hSφ hz
  have hαψ : ∀ z ∈ S, α z ∈ tangentChartSet ψ := fun z hz => by
    change _ ∈ ψ.source; rw [hα z hz]; exact hSψ hz
  have h1 : ContinuousOn (fun z => tangentChartMap hφ (α z)) S := by
    refine (hlev.prodMk hc).congr fun z hz => ?_
    refine Prod.ext ?_ rfl
    rw [tangentChartMap_fst hφ (hαφ z hz), hα z hz]
  set χ := tangentChart hφ (α z₀)
  have h2 : ContinuousOn α S := by
    have hc2 : ContinuousOn (fun z => χ.toPartialEquiv.symm (tangentChartMap hφ (α z))) S :=
      χ.continuousOn_invFun.comp h1 fun z hz => tangentChartMap_mem hφ (hαφ z hz)
    exact hc2.congr fun z hz => (χ.toPartialEquiv.left_inv (hαφ z hz)).symm
  have h3 : ContinuousOn (fun z => tangentChartMap hψ (α z)) S :=
    (tangentChart hψ (α z₀)).continuousOn_toFun.comp h2 hαψ
  exact continuous_snd.comp_continuousOn h3

/-- If `Λ` restricts on `N` to the coordinates of a basis `b₀` of `N`, then `det (Λ b) ≠ 0` for
every basis `b` of `N`. -/
theorem frameDet_ne_zero_of_basis {N : Submodule ℝ E'} {n : ℕ} (b₀ : Basis (Fin n) ℝ N)
    (Λ : E' →L[ℝ] (Fin n → ℝ)) (hΛ : ∀ v : N, Λ v = b₀.equivFun v) (b : Basis (Fin n) ℝ N) :
    frameDet Λ (fun i => (b i : E')) ≠ 0 := by
  rw [frameDet_eq]
  have h : (fun i => Λ (b i : E')) = ⇑(b.map b₀.equivFun) := funext fun i => by
    rw [Basis.map_apply, hΛ]
  rw [h]
  exact ((Pi.basisFun ℝ (Fin n)).isUnit_det _).ne_zero

variable (P) in
/-- **The level-`1` coordinates are continuous along `A`**: in every chart `φ`, `y ↦ φ(y) ∈ E₁`
is continuous on `A ∩ dom φ` (for finite-dimensional submanifolds this is the effect of the
`sc⁺`-retraction; in `ℝᵐ` it holds for every set, `hasContinuousLevelOneOn_rn`). -/
def HasContinuousLevelOneOn (A : Set X) : Prop :=
  ∀ (φ : MChart X), P.IsChart φ → ContinuousOn (levelLift φ 1) (A ∩ φ.source)

/-- A continuous function nonzero at `x` keeps its sign near `x`. -/
theorem exists_isOpen_sign_eq {Z : Type*} [TopologicalSpace Z] {S : Set Z} {D : Z → ℝ}
    (hD : ContinuousOn D S) {x : Z} (hxS : x ∈ S) (hDx : D x ≠ 0) :
    ∃ U : Set Z, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ S ∩ U, D z ≠ 0 ∧ (0 < D z ↔ 0 < D x) := by
  by_cases hpos : 0 < D x
  · obtain ⟨U, hU, hxU, hUS⟩ := mem_nhdsWithin.1
      ((hD x hxS).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds (show D x ∈ Ioi 0 from hpos)))
    exact ⟨U, hU, hxU, fun z hz => ⟨(hUS ⟨hz.2, hz.1⟩ : 0 < D z).ne',
      iff_of_true (hUS ⟨hz.2, hz.1⟩) hpos⟩⟩
  · have hneg : D x < 0 := lt_of_le_of_ne (not_lt.1 hpos) hDx
    obtain ⟨U, hU, hxU, hUS⟩ := mem_nhdsWithin.1
      ((hD x hxS).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds (show D x ∈ Iio 0 from hneg)))
    exact ⟨U, hU, hxU, fun z hz => ⟨(hUS ⟨hz.2, hz.1⟩ : D z < 0).ne,
      iff_of_false (not_lt.2 (hUS ⟨hz.2, hz.1⟩ : D z < 0).le) hpos⟩⟩

/-- Oriented tangent spaces of two oriented submanifolds with the same tangent set at `y` agree
iff the frames agree. -/
theorem SubmanifoldOrientation.tangent_eq_iff {A₁ A₂ : Set X} {n : ℕ}
    (o₁ : P.SubmanifoldOrientation A₁ n) (o₂ : P.SubmanifoldOrientation A₂ n) {y : X}
    (hT : P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y) :
    o₁.tangent y = o₂.tangent y ↔ o₁.frames y = o₂.frames y := by
  simp only [SubmanifoldOrientation.tangent, hT, OrTangent.mk.injEq, heq_eq_eq, true_and]

/-- **Relative orientations are locally constant** (the continuity of orientations used in the
proof of Lemma 9.3.4, 2021 p. 424): for oriented `n`-dimensional `(A₁, o₁)`, `(A₂, o₂)` with
`T_xA₁ = T_xA₂`, `n > 0`, there is a neighbourhood `O` of `x` such that at every common point
`z ∈ O` with `T_zA₁ = T_zA₂`, `o₁` and `o₂` agree at `z` iff they agree at `x`.  (The positive
frame fields of `o₁`, `o₂` are read in one chart; the sign of `det (Λ e₁)` and `det (Λ e₂)` is
constant near `x`.) -/
theorem SubmanifoldOrientation.exists_isOpen_tangent_eq_iff {A₁ A₂ : Set X} {n : ℕ}
    (hn : 0 < n) (o₁ : P.SubmanifoldOrientation A₁ n) (o₂ : P.SubmanifoldOrientation A₂ n)
    (hl₂ : P.HasContinuousLevelOneOn A₂) {x : X} (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
    (hT : P.submanifoldTangent A₁ x = P.submanifoldTangent A₂ x) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ z ∈ A₁ ∩ A₂ ∩ O,
      P.submanifoldTangent A₁ z = P.submanifoldTangent A₂ z →
        (o₁.tangent z = o₂.tangent z ↔ o₁.tangent x = o₂.tangent x) := by
  obtain ⟨φ₁, hφ₁, V₁, hV₁, hxV₁, hV₁φ, e₁, he₁, hc₁⟩ := o₁.continuous hn x hx₁
  obtain ⟨φ₂, hφ₂, V₂, hV₂, hxV₂, hV₂φ, e₂, he₂, hc₂⟩ := o₂.continuous hn x hx₂
  set S₂ : Set X := A₂ ∩ (V₂ ∩ φ₁.source) with hS₂
  have hfib₂ : ∀ z ∈ A₂ ∩ V₂, ∀ i, P.levelVal 1 (P.tangentProj (e₂ z i)) = z := fun z hz i =>
    ((o₂.isOrientedAt z hz.1).mem_carrier (he₂ z hz) i).1
  have hc₂' : ContinuousOn (fun z i => chartVec hφ₁ (e₂ z i)) S₂ :=
    continuousOn_pi.2 fun i => continuousOn_chartVec_of_continuousOn hφ₂ hφ₁ (S := S₂)
      (fun z hz => hV₂φ hz.2.1) (fun z hz => hz.2.2)
      ((hl₂ φ₂ hφ₂).mono fun z hz => ⟨hz.1, hV₂φ hz.2.1⟩) (α := fun z => e₂ z i)
      (fun z hz => hfib₂ z ⟨hz.1, hz.2.1⟩ i)
      ((continuousOn_pi.1 hc₂ i).mono fun z hz => ⟨hz.1, hz.2.1⟩)
  -- the map `Λ`
  obtain ⟨N, hN, hfin, hrank, ωx, hO⟩ := (o₁.isOrientedAt x hx₁).isChartOrientation hφ₁
    (hV₁φ hxV₁)
  have := hfin
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional N
  let b₀ : Basis (Fin n) ℝ N := Module.finBasisOfFinrankEq ℝ N hrank
  let Λ : φ₁.model.E 0 →L[ℝ] (Fin n → ℝ) :=
    (b₀.equivFunL : N →L[ℝ] (Fin n → ℝ)).comp Q'
  have hΛN : ∀ v : N, Λ v = b₀.equivFun v := fun v => by
    change b₀.equivFunL (Q' v) = _
    rw [hQ' v]; rfl
  set D₁ : X → ℝ := fun z => frameDet Λ (fun i => chartVec hφ₁ (e₁ z i)) with hD₁
  set D₂ : X → ℝ := fun z => frameDet Λ (fun i => chartVec hφ₁ (e₂ z i)) with hD₂
  have hD₁c : ContinuousOn D₁ (A₁ ∩ V₁) := ContinuousOn.frameDet Λ hc₁
  have hD₂c : ContinuousOn D₂ S₂ := ContinuousOn.frameDet Λ hc₂'
  have hD₁x : D₁ x ≠ 0 := by
    have h := he₁ x ⟨hx₁, hxV₁⟩
    change e₁ x ∈ o₁.frames x at h
    rw [show o₁.frames x = chartFrames hφ₁ (P.submanifoldTangent A₁ x) N ωx from hO] at h
    obtain ⟨-, b, hb, -⟩ := h
    have : D₁ x = frameDet Λ (fun i => (b i : φ₁.model.E 0)) := by
      simp only [hD₁, hb]
    rw [this]
    exact frameDet_ne_zero_of_basis b₀ Λ hΛN b
  have hD₂x : D₂ x ≠ 0 := by
    obtain ⟨N₂, hN₂, -, -, ω₂, hO₂⟩ := (o₂.isOrientedAt x hx₂).isChartOrientation hφ₁
      (hV₁φ hxV₁)
    have hNN : N₂ = N := SetLike.coe_injective (by
      rw [hN₂, hN]
      change chartVec hφ₁ '' P.submanifoldTangent A₂ x = chartVec hφ₁ '' P.submanifoldTangent A₁ x
      rw [hT])
    subst hNN
    have h := he₂ x ⟨hx₂, hxV₂⟩
    change e₂ x ∈ o₂.frames x at h
    rw [show o₂.frames x = chartFrames hφ₁ (P.submanifoldTangent A₂ x) N₂ ω₂ from hO₂] at h
    obtain ⟨-, b, hb, -⟩ := h
    have : D₂ x = frameDet Λ (fun i => (b i : φ₁.model.E 0)) := by
      simp only [hD₂, hb]
    rw [this]
    exact frameDet_ne_zero_of_basis b₀ Λ hΛN b
  obtain ⟨U₁, hU₁, hxU₁, hU₁s⟩ := exists_isOpen_sign_eq hD₁c ⟨hx₁, hxV₁⟩ hD₁x
  obtain ⟨U₂, hU₂, hxU₂, hU₂s⟩ := exists_isOpen_sign_eq hD₂c ⟨hx₂, hxV₂, hV₁φ hxV₁⟩ hD₂x
  have key : ∀ y, y ∈ A₁ ∩ V₁ → y ∈ S₂ →
      P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y → D₁ y ≠ 0 →
        (o₁.tangent y = o₂.tangent y ↔ (0 < D₁ y ↔ 0 < D₂ y)) := by
    intro y hy₁ hy₂ hTy hDy
    rw [SubmanifoldOrientation.tangent_eq_iff o₁ o₂ hTy]
    have h₁ := o₁.isOrientedAt y hy₁.1
    rw [hTy] at h₁
    exact frames_eq_iff_frameDet h₁ (o₂.isOrientedAt y hy₂.1) hφ₁ hy₂.2.2 Λ
      (he₁ y hy₁) (he₂ y ⟨hy₂.1, hy₂.2.1⟩) hDy
  refine ⟨U₁ ∩ U₂ ∩ V₁ ∩ V₂, ((hU₁.inter hU₂).inter hV₁).inter hV₂,
    ⟨⟨⟨hxU₁, hxU₂⟩, hxV₁⟩, hxV₂⟩, fun z hz hTz => ?_⟩
  obtain ⟨⟨hzA₁, hzA₂⟩, ⟨⟨hzU₁, hzU₂⟩, hzV₁⟩, hzV₂⟩ := hz
  have hz₁ : z ∈ A₁ ∩ V₁ := ⟨hzA₁, hzV₁⟩
  have hz₂ : z ∈ S₂ := ⟨hzA₂, hzV₂, hV₁φ hzV₁⟩
  obtain ⟨hDz₁, hsz₁⟩ := hU₁s z ⟨hz₁, hzU₁⟩
  obtain ⟨-, hsz₂⟩ := hU₂s z ⟨hz₂, hzU₂⟩
  rw [key z hz₁ hz₂ hTz hDz₁, key x ⟨hx₁, hxV₁⟩ ⟨hx₂, hxV₂, hV₁φ hxV₁⟩ hT hD₁x, hsz₁, hsz₂]

end MPolyfold

/-- **The level-`1` coordinates are continuous on `ℝᵐ`** (witness of `HasContinuousLevelOneOn`). -/
theorem hasContinuousLevelOneOn_rn {m : ℕ} (A : Set (Fin m → ℝ)) :
    (rnPolyfold m).HasContinuousLevelOneOn A := fun _ hφ =>
  (continuousOn_levelLift_comp MPolyfold.isScSmoothMap_id hφ 1).mono fun _ hz => hz.2



section GraphBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Lipschitz bound of the graph representation: `‖w‖ ≤ 2 ‖Q w‖` once `w` is
`1 / (2 (‖Q‖ + 1))`-close to the range `T` of the projection `Q` relative to `‖w‖`. -/
theorem norm_le_two_mul_of_approx {Q : E →L[ℝ] E} {T : Set E} (hQid : ∀ v ∈ T, Q v = v)
    {w v : E} (hv : v ∈ T) (hwv : ‖w - v‖ ≤ 1 / (2 * (‖Q‖ + 1)) * ‖w‖) : ‖w‖ ≤ 2 * ‖Q w‖ := by
  have h1 : w - Q w = (w - v) - Q (w - v) := by rw [map_sub, hQid v hv]; abel
  have hq : 0 < ‖Q‖ + 1 := by positivity
  have h2 : ‖w - Q w‖ ≤ (‖Q‖ + 1) * ‖w - v‖ := by
    rw [h1]
    calc ‖(w - v) - Q (w - v)‖ ≤ ‖w - v‖ + ‖Q (w - v)‖ := norm_sub_le _ _
      _ ≤ ‖w - v‖ + ‖Q‖ * ‖w - v‖ := by linarith [Q.le_opNorm (w - v)]
      _ = (‖Q‖ + 1) * ‖w - v‖ := by ring
  have h3 : (‖Q‖ + 1) * ‖w - v‖ ≤ ‖w‖ / 2 := by
    calc (‖Q‖ + 1) * ‖w - v‖ ≤ (‖Q‖ + 1) * (1 / (2 * (‖Q‖ + 1)) * ‖w‖) :=
          mul_le_mul_of_nonneg_left hwv hq.le
      _ = ‖w‖ / 2 := by field_simp
  have h4 : ‖w‖ ≤ ‖Q w‖ + ‖w - Q w‖ := by
    calc ‖w‖ = ‖Q w + (w - Q w)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

end GraphBall

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **The graph representation over a full neighbourhood of `0` in `T_xA`** (the form of
Lemmas 9.2.10, 9.2.11 at points where every direction is admissible, `C = E`): in the chart `φ`,
`A` is uniformly close to `T = T_xA` near `x` (`approx`, as in `IsGraphChartAt`), and for every
projection `Q` onto `T` every small `u ∈ T` is `Q(φ(a) − φ(x))` for some `a ∈ A` with
`‖φ(a) − φ(x) − u‖ ≤ ε ‖u‖` (`ball`).  Satisfied in `ℝᵐ` (`isGraphBallAt_rn`). -/
structure IsGraphBallAt {φ : MChart X} (hφ : P.IsChart φ) (A : Set X) (x : X) : Prop where
  approx : ∀ ε > 0, ∃ δ > 0, ∀ a ∈ A ∩ φ.source, ∀ b ∈ A ∩ φ.source,
    ‖φ a - φ x‖ < δ → ‖φ b - φ x‖ < δ →
      ∃ v ∈ P.chartTangent hφ A x, ‖(φ a - φ b) - v‖ ≤ ε * ‖φ a - φ b‖
  ball : ∀ Q : φ.model.E 0 →L[ℝ] φ.model.E 0, (∀ v, Q v ∈ P.chartTangent hφ A x) →
    (∀ v ∈ P.chartTangent hφ A x, Q v = v) → ∀ ε > 0, ∃ r > 0,
      ∀ u ∈ P.chartTangent hφ A x, ‖u‖ < r → ∃ a ∈ A ∩ φ.source,
        Q (φ a - φ x) = u ∧ ‖(φ a - φ x) - u‖ ≤ ε * ‖u‖

variable (P) in
/-- **One chart at `x` with the graph representation over a full neighbourhood** for every
`n`-dimensional submanifold through `x` (`IsGraphBallAt`).  Satisfied at every point of `ℝᵐ`
(`hasGraphBallAt_rn`). -/
def HasGraphBallAt (x : X) (n : ℕ) : Prop :=
  ∃ (φ : MChart X) (hφ : P.IsChart φ), x ∈ φ.source ∧
    ∀ A : Set X, P.IsSubmanifoldOfDim A n → x ∈ A → P.IsGraphBallAt hφ A x

/-- **The ball form gives the ray form** `IsGraphChartAt` with every direction admissible. -/
theorem IsGraphBallAt.isGraphChartAt {φ : MChart X} {hφ : P.IsChart φ} {A : Set X} {x : X}
    (h : P.IsGraphBallAt hφ A x) (hA : P.IsSmoothSubmanifold A) (hx : x ∈ A)
    (hxφ : x ∈ φ.source) : P.IsGraphChartAt hφ univ A x := by
  obtain ⟨N, hN, -⟩ := exists_submodule_chartTangent hφ hA hx hxφ
  refine ⟨⟨0, by rw [← hN]; exact N.zero_mem, 1, one_pos, fun _ _ _ => mem_univ _⟩, h.approx,
    fun Q hQT hQid v hv _ ε hε => ?_⟩
  obtain ⟨r, hr, hball⟩ := h.ball Q hQT hQid (ε / (‖v‖ + 1)) (by positivity)
  refine ⟨r / (‖v‖ + 1), by positivity, fun t ht htt => ?_⟩
  have hu : t • v ∈ P.chartTangent hφ A x := by
    rw [← hN] at hv ⊢; exact N.smul_mem t hv
  have hur : ‖t • v‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    calc t * ‖v‖ ≤ t * (‖v‖ + 1) := by nlinarith
      _ < r := by rwa [lt_div_iff₀ (by positivity)] at htt
  obtain ⟨a, ha, hQa, hest⟩ := hball _ hu hur
  refine ⟨a, ha, hQa, hest.trans ?_⟩
  rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg v, mul_pos hε ht]

/-- **The ball form gives the ray form of `TangentSlices`** (the hypothesis `HasGraphChartsAt` of
Lemmas 9.2.10, 9.2.11, 2021 pp. 414–417), with `K = E`. -/
theorem HasGraphBallAt.hasGraphChartsAt {x : X} {n : ℕ} (h : P.HasGraphBallAt x n) :
    P.HasGraphChartsAt x n := by
  obtain ⟨φ, hφ, hxφ, hA⟩ := h
  exact ⟨φ, hφ, hxφ, univ, fun A hAn hx => (hA A hAn hx).isGraphChartAt hAn.1 hx hxφ⟩

end MPolyfold

/-- **The graph representation over a ball in `ℝᵐ`**: every smooth submanifold `A` of `ℝᵐ`
through `x` is, in the chart `id`, the graph over a neighbourhood of `0` in `T_xA` (the inverse
function theorem, `exists_mem_graph_of_hasStrictFDerivAt`). -/
theorem isGraphBallAt_rn {m : ℕ} {A : Set (Fin m → ℝ)} (hA : (rnPolyfold m).IsSmoothSubmanifold A)
    {x : Fin m → ℝ} (hx : x ∈ A) :
    (rnPolyfold m).IsGraphBallAt (isChart_rnChart 0) A x := by
  obtain ⟨W, hWo, hxW, s, hsm, -, hidem, himg, hT⟩ := MPolyfold.rn_exists_retraction hA hx
  refine ⟨(MPolyfold.isGraphChartAt_rn hA hx).approx, fun Q hQT hQid ε hε => ?_⟩
  have hfix : ∀ a ∈ W ∩ A, s a = a := fun a ha => by
    rw [← himg] at ha
    obtain ⟨w, hw, rfl⟩ := ha
    exact hidem w hw
  have hsx : s x = x := hfix x ⟨hxW, hx⟩
  obtain ⟨hstrict, hDfix⟩ := MPolyfold.rn_retraction_deriv hWo hxW hsm hidem hsx
  rw [hT] at hQT hQid
  set D := fderiv ℝ s x with hDdef
  set N : Submodule ℝ (Fin m → ℝ) := LinearMap.range (D : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    with hNdef
  have hmemN : ∀ v, v ∈ N ↔ v ∈ range D := fun v => by
    rw [hNdef, LinearMap.mem_range]; rfl
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hWo x hxW
  obtain ⟨r, hr, hgr⟩ := exists_mem_graph_of_hasStrictFDerivAt hstrict hsx (N := N)
    (fun c hc => hDfix c ((hmemN c).1 hc)) (fun v => (hmemN _).2 (hQT v))
    (fun v hv => hQid v ((hmemN v).1 hv)) hε hρ
  refine ⟨r, hr, fun u hu hur => ?_⟩
  rw [hT] at hu
  obtain ⟨c, -, hcρ, hQc, hest⟩ := hgr u ((hmemN u).2 hu) hur
  have hxc : x + c ∈ W := hρW (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hcρ)
  have haA : s (x + c) ∈ A := by
    have : s (x + c) ∈ s '' W := ⟨x + c, hxc, rfl⟩
    rw [himg] at this
    exact this.2
  refine ⟨s (x + c), ⟨haA, mem_univ _⟩, ?_, ?_⟩
  · rw [MPolyfold.rnChart_zero_apply', MPolyfold.rnChart_zero_apply']; exact hQc
  · rw [MPolyfold.rnChart_zero_apply', MPolyfold.rnChart_zero_apply']; exact hest

/-- **`HasGraphBallAt` holds at every point of `ℝᵐ`**, in every dimension. -/
theorem hasGraphBallAt_rn {m : ℕ} (x : Fin m → ℝ) (n : ℕ) : (rnPolyfold m).HasGraphBallAt x n :=
  ⟨rnChart m 0, isChart_rnChart 0, mem_univ x, fun _ hA hx => isGraphBallAt_rn hA.1 hx⟩


namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

open scoped Classical in
/-- **The good-point input of Lemma 9.3.4 from the graph representation** (Proposition 9.2.8
for oriented families, 2021 p. 413, with the continuity of orientations): if one chart at `x`
represents every `n`-dimensional submanifold through `x` as a graph over a neighbourhood of `0`
in its tangent space (`HasGraphBallAt`), and level-`1` coordinates are continuous along these
submanifolds, then `HasOrientedGoodPointsAt x n` holds.

The sheets `A_k` tangent to `A_{k₀}` are graphs `u ↦ g_k(u)` over `T = T_xA_{k₀}`.  For `u` in a
small ball `S` around `t h₀` (`h₀ ∈ T` off the other tangent spaces) the points `g_k(u)` miss the
other sheets; by `exists_isOpen_subset_inter_eq_empty_or_subset` there is an open `S' ⊆ S` on
which each coincidence set `{g_k = g_{k'}}` is empty or everything.  For `v ∈ S'` the distinct
points among the `g_k(v)` are the `y_e`; near `y_e` the sheets through it coincide (they are the
graphs of the same map over `S'`), and the relative orientations are those at `x` by
`SubmanifoldOrientation.exists_isOpen_tangent_eq_iff`. -/
theorem hasOrientedGoodPointsAt_of_hasGraphBallAt {x : X} {n : ℕ} (hG : P.HasGraphBallAt x n)
    (hlev : ∀ A : Set X, P.IsSubmanifoldOfDim A n → x ∈ A → P.HasContinuousLevelOneOn A) :
    P.HasOrientedGoodPointsAt x n := by
  intro κ _ A d o hd hA hx k₀ W hW hxW
  obtain rfl : d = fun _ => n := funext hd
  obtain ⟨φ, hφ, hxφ, hGA⟩ := hG
  have hGk : ∀ k, P.IsGraphBallAt hφ (A k) x := fun k => hGA (A k) (hA k) (hx k)
  -- the tangent spaces
  choose N hN hfin using fun k => exists_submodule_chartTangent hφ (hA k).1 (hx k) hxφ
  have hrank : ∀ k, finrank ℝ (N k) = n := fun k =>
    finrank_chartTangent hφ ((hA k).2 x (hx k)) (hA k).1 hxφ (hN k)
  set C : κ → Prop := fun k =>
    P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x with hCdef
  have hC₀ : C k₀ := rfl
  have hCN : ∀ k, C k ↔ N k = N k₀ := fun k => by
    change P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x ↔ _
    rw [← chartTangent_eq_iff hφ hxφ, ← hN k, ← hN k₀, SetLike.coe_set_eq]
  set N₀ := N k₀ with hN₀def
  have : FiniteDimensional ℝ N₀ := hfin k₀
  have hTC : ∀ k, C k → P.chartTangent hφ (A k) x = (N₀ : Set (φ.model.E 0)) := fun k hk => by
    rw [← hN k, (hCN k).1 hk]
  -- the projection `Q` onto `T`
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional N₀
  set Q : φ.model.E 0 →L[ℝ] φ.model.E 0 := N₀.subtypeL.comp Q' with hQdef
  have hQN : ∀ v, Q v ∈ N₀ := fun v => (Q' v).2
  have hQid : ∀ v ∈ N₀, Q v = v := fun v hv => congrArg Subtype.val (hQ' ⟨v, hv⟩)
  set η : ℝ := 1 / (2 * (‖Q‖ + 1)) with hηdef
  have hη : 0 < η := by positivity
  -- the direction `h₀` and the distances `ρ k` to the other tangent spaces
  have hnle : ∀ k, ¬ C k → ¬ N₀ ≤ N k := fun k hk hle => by
    have := hfin k
    exact hk ((hCN k).2 (Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, hrank])).symm)
  have hclosed : ∀ k, IsClosed (N k : Set (φ.model.E 0)) := fun k => by
    have := hfin k
    exact Submodule.closed_of_finiteDimensional _
  obtain ⟨h₀, hh₀N, -, hh₀S⟩ := exists_mem_ball_forall_not_mem (N := N₀) (ι := {k // ¬ C k})
    (fun k => N k.1) (fun k => hclosed k.1) (fun k => hnle k.1 k.2) N₀.zero_mem one_pos
  have hrad : ∀ k, ¬ C k → ∃ ρ > 0, ∀ v ∈ N k, ρ ≤ ‖h₀ - v‖ := fun k hk => by
    have hmem : h₀ ∈ (N k : Set (φ.model.E 0))ᶜ := hh₀S ⟨k, hk⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hclosed k).isOpen_compl h₀ hmem
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hv
  choose! ρ hρ hρv using hrad
  have hρev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 ∧ ∀ k, ¬ C k → ε ≤ ρ k := by
    refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)
    · exact ((eventually_lt_nhds one_pos).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    · by_cases hk : ¬ C k
      · exact ((eventually_lt_nhds (hρ k hk)).mono fun _ h _ => h.le).filter_mono
          nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
  obtain ⟨ρ₀, ⟨hρ₀1, hρ₀ρ⟩, hρ₀⟩ := (hρev.and self_mem_nhdsWithin).exists
  have hρ₀ : (0 : ℝ) < ρ₀ := hρ₀
  -- the constants
  set H : ℝ := ‖h₀‖ + 1 with hHdef
  have hH : 0 < H := by positivity
  set τ : ℝ := ρ₀ / 3 with hτdef
  set εg : ℝ := min 1 (ρ₀ / (3 * H)) with hεgdef
  have hεg : 0 < εg := lt_min one_pos (by positivity)
  have hεg1 : εg ≤ 1 := min_le_left _ _
  have hεgH : εg * H ≤ ρ₀ / 3 := by
    calc εg * H ≤ ρ₀ / (3 * H) * H := mul_le_mul_of_nonneg_right (min_le_right _ _) hH.le
      _ = ρ₀ / 3 := by field_simp
  set ε₁ : ℝ := ρ₀ / (6 * H) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  -- the graph maps, the approximation radii
  have hgr : ∀ k, C k → ∃ r > 0, ∀ u ∈ N₀, ‖u‖ < r → ∃ a ∈ A k ∩ φ.source,
      Q (φ a - φ x) = u ∧ ‖(φ a - φ x) - u‖ ≤ εg * ‖u‖ := fun k hk => by
    obtain ⟨r, hr, h⟩ := (hGk k).ball Q (fun v => by rw [hTC k hk]; exact hQN v)
      (fun v hv => hQid v (by rw [hTC k hk] at hv; exact hv)) εg hεg
    exact ⟨r, hr, fun u hu hur => h u (by rw [hTC k hk]; exact hu) hur⟩
  choose! r hr hgr using hgr
  choose δ₁ hδ₁ happ₁ using fun k => (hGk k).approx η hη
  choose δ₂ hδ₂ happ₂ using fun k => (hGk k).approx ε₁ hε₁
  have hlip : ∀ k, C k → ∀ a ∈ A k ∩ φ.source, ∀ b ∈ A k ∩ φ.source,
      ‖φ a - φ x‖ < δ₁ k → ‖φ b - φ x‖ < δ₁ k →
        ‖φ a - φ b‖ ≤ 2 * ‖Q (φ a - φ x) - Q (φ b - φ x)‖ := by
    intro k hk a ha b hb hax hbx
    obtain ⟨v, hv, hvab⟩ := happ₁ k a ha b hb hax hbx
    rw [hTC k hk] at hv
    have h := norm_le_two_mul_of_approx hQid hv hvab
    rwa [show Q (φ a - φ b) = Q (φ a - φ x) - Q (φ b - φ x) by
      rw [← map_sub]; congr 1; abel] at h
  -- the orientation neighbourhoods
  have hor : ∀ k k', ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ (0 < n → C k → C k' →
      ∀ z ∈ A k ∩ A k' ∩ O, P.submanifoldTangent (A k) z = P.submanifoldTangent (A k') z →
        ((o k).tangent z = (o k').tangent z ↔ (o k).tangent x = (o k').tangent x)) := by
    intro k k'
    by_cases h : 0 < n ∧ C k ∧ C k'
    · obtain ⟨O, hO, hxO, hOp⟩ := SubmanifoldOrientation.exists_isOpen_tangent_eq_iff h.1
        (o k) (o k') (hlev _ (hA k') (hx k')) (hx k) (hx k') (h.2.1.trans h.2.2.symm)
      exact ⟨O, hO, hxO, fun _ _ _ => hOp⟩
    · exact ⟨univ, isOpen_univ, mem_univ x, fun hn hk hk' => (h ⟨hn, hk, hk'⟩).elim⟩
  choose O hO hxO hOp using hor
  set W₁ : Set X := W ∩ ⋂ k, ⋂ k', O k k' with hW₁def
  have hW₁ : IsOpen W₁ := hW.inter (isOpen_iInter_of_finite fun k =>
    isOpen_iInter_of_finite fun k' => hO k k')
  have hxW₁ : x ∈ W₁ := ⟨hxW, mem_iInter.2 fun k => mem_iInter.2 fun k' => hxO k k'⟩
  obtain ⟨ρW, hρW, hρWsub⟩ := exists_pos_forall_mem_of_mem_nhds hxφ (hW₁.mem_nhds hxW₁)
  -- the radius `R` and the parameter `t`
  have hRev : ∀ᶠ R in 𝓝[>] (0 : ℝ), (∀ k, C k → R < r k) ∧ (∀ k, R < δ₁ k) ∧
      (∀ k, R < δ₂ k) ∧ R < ρW := by
    refine (Filter.eventually_all.2 fun k => ?_).and ((Filter.eventually_all.2 fun k => ?_).and
      ((Filter.eventually_all.2 fun k => ?_).and ?_))
    · by_cases hk : C k
      · exact ((eventually_lt_nhds (hr k hk)).mono fun _ h _ => h).filter_mono nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
    · exact (eventually_lt_nhds (hδ₁ k)).filter_mono nhdsWithin_le_nhds
    · exact (eventually_lt_nhds (hδ₂ k)).filter_mono nhdsWithin_le_nhds
    · exact (eventually_lt_nhds hρW).filter_mono nhdsWithin_le_nhds
  obtain ⟨R, ⟨hRr, hRδ₁, hRδ₂, hRW⟩, hR0⟩ := (hRev.and self_mem_nhdsWithin).exists
  have hR0 : (0 : ℝ) < R := hR0
  set t : ℝ := R / (2 * H) with htdef
  have ht : 0 < t := by positivity
  have htH : 2 * (t * H) = R := by rw [htdef]; field_simp
  -- the parameter set `S`
  set S : Set N₀ := {u | ‖(u : φ.model.E 0) - t • h₀‖ < τ * t} with hSdef
  have hSo : IsOpen S := isOpen_lt ((continuous_subtype_val.sub continuous_const).norm)
    continuous_const
  have hSnorm : ∀ u ∈ S, ‖(u : φ.model.E 0)‖ < t * H := fun u hu => by
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    have hτ1 : τ ≤ 1 := by rw [hτdef]; linarith
    calc ‖(u : φ.model.E 0)‖ = ‖((u : φ.model.E 0) - t • h₀) + t • h₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖(u : φ.model.E 0) - t • h₀‖ + ‖t • h₀‖ := norm_add_le _ _
      _ < τ * t + t * ‖h₀‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]; linarith
      _ ≤ t * H := by rw [hHdef]; nlinarith
  have hg : ∀ k, C k → ∀ u : N₀, u ∈ S → ∃ a ∈ A k ∩ φ.source,
      Q (φ a - φ x) = u ∧ ‖(φ a - φ x) - u‖ ≤ εg * ‖(u : φ.model.E 0)‖ := fun k hk u hu =>
    hgr k hk u u.2 ((hSnorm u hu).trans (by linarith [hRr k hk]))
  have : Nonempty X := ⟨x⟩
  choose! g hgA hgQ hgest using hg
  have hgnorm : ∀ k, C k → ∀ u ∈ S, ‖φ (g k u) - φ x‖ ≤ 2 * ‖(u : φ.model.E 0)‖ := by
    intro k hk u hu
    have h1 := hgest k hk u hu
    calc ‖φ (g k u) - φ x‖ = ‖((φ (g k u) - φ x) - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖(φ (g k u) - φ x) - u‖ + ‖(u : φ.model.E 0)‖ := norm_add_le _ _
      _ ≤ 2 * ‖(u : φ.model.E 0)‖ := by nlinarith [norm_nonneg (u : φ.model.E 0)]
  have hgR : ∀ k, C k → ∀ u ∈ S, ‖φ (g k u) - φ x‖ < R := fun k hk u hu => by
    linarith [hgnorm k hk u hu, hSnorm u hu]
  -- uniqueness of the graph point
  have huniq : ∀ k, C k → ∀ u ∈ S, ∀ a ∈ A k ∩ φ.source, ‖φ a - φ x‖ < R →
      Q (φ a - φ x) = u → a = g k u := by
    intro k hk u hu a ha haR hQa
    have h := hlip k hk a ha (g k u) (hgA k hk u hu) (haR.trans (hRδ₁ k))
      ((hgR k hk u hu).trans (hRδ₁ k))
    rw [hQa, hgQ k hk u hu, sub_self, norm_zero, mul_zero] at h
    exact φ.toPartialEquiv.injOn ha.2 (hgA k hk u hu).2 (sub_eq_zero.1 (norm_le_zero_iff.1 h))
  -- the graph points over `S` miss the sheets of the other classes
  have havoid : ∀ j, C j → ∀ u ∈ S, ∀ k, ¬ C k → g j u ∉ A k := by
    intro j hj u hu k hk hjk
    set a := g j u with hadef
    have hxA : x ∈ A k ∩ φ.source := ⟨hx k, hxφ⟩
    obtain ⟨w, hw, hwa⟩ := happ₂ k a ⟨hjk, (hgA j hj u hu).2⟩ x hxA
      ((hgR j hj u hu).trans (hRδ₂ k)) (by rw [sub_self, norm_zero]; exact hδ₂ k)
    rw [← hN k] at hw
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    have hun := hSnorm u hu
    have h1 : ‖(φ a - φ x) - w‖ ≤ ε₁ * (2 * (t * H)) := by
      calc ‖(φ a - φ x) - w‖ ≤ ε₁ * ‖φ a - φ x‖ := hwa
        _ ≤ ε₁ * (2 * ‖(u : φ.model.E 0)‖) :=
            mul_le_mul_of_nonneg_left (hgnorm j hj u hu) hε₁.le
        _ ≤ ε₁ * (2 * (t * H)) := by nlinarith
    have h1' : ε₁ * (2 * (t * H)) = ρ₀ / 3 * t := by rw [hε₁def]; field_simp; ring
    have h2 : ‖(φ a - φ x) - u‖ ≤ ρ₀ / 3 * t := by
      calc ‖(φ a - φ x) - u‖ ≤ εg * ‖(u : φ.model.E 0)‖ := hgest j hj u hu
        _ ≤ εg * (t * H) := mul_le_mul_of_nonneg_left hun.le hεg.le
        _ = εg * H * t := by ring
        _ ≤ ρ₀ / 3 * t := mul_le_mul_of_nonneg_right hεgH ht.le
    have h3 : ‖t • h₀ - w‖ < ρ₀ * t := by
      calc ‖t • h₀ - w‖ = ‖(t • h₀ - u) + (u - (φ a - φ x)) + ((φ a - φ x) - w)‖ := by
            congr 1; abel
        _ ≤ ‖t • h₀ - u‖ + ‖(u : φ.model.E 0) - (φ a - φ x)‖ + ‖(φ a - φ x) - w‖ :=
            norm_add₃_le
        _ < τ * t + ρ₀ / 3 * t + ρ₀ / 3 * t := by
            have e1 : ‖t • h₀ - u‖ = ‖(u : φ.model.E 0) - t • h₀‖ := norm_sub_rev _ _
            have e2 : ‖(u : φ.model.E 0) - (φ a - φ x)‖ = ‖(φ a - φ x) - u‖ := norm_sub_rev _ _
            linarith
        _ = ρ₀ * t := by rw [hτdef]; ring
    have hw' : t⁻¹ • w ∈ N k := (N k).smul_mem _ hw
    have h4 := hρv k hk _ hw'
    have h5 : ‖h₀ - t⁻¹ • w‖ = t⁻¹ * ‖t • h₀ - w‖ := by
      have : h₀ - t⁻¹ • w = t⁻¹ • (t • h₀ - w) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
    have h6 : t⁻¹ * ‖t • h₀ - w‖ < ρ₀ := by rw [inv_mul_lt_iff₀ ht]; linarith
    linarith [hρ₀ρ k hk]
  -- continuity of the graph maps on `S`
  have hGc : ∀ k, C k → ContinuousOn (fun u => φ (g k u)) S := by
    intro k hk
    refine Metric.continuousOn_iff.2 fun u hu ε hε => ⟨ε / 2, by positivity, fun u' hu' hd => ?_⟩
    have h := hlip k hk (g k u') (hgA k hk u' hu') (g k u) (hgA k hk u hu)
      ((hgR k hk u' hu').trans (hRδ₁ k)) ((hgR k hk u hu).trans (hRδ₁ k))
    rw [hgQ k hk u' hu', hgQ k hk u hu] at h
    rw [Subtype.dist_eq, dist_eq_norm] at hd
    rw [dist_eq_norm]
    linarith
  -- the shrinking step
  let ι := {p : κ × κ // C p.1 ∧ C p.2}
  let M : ι → Set N₀ := fun p => {u | φ (g p.1.1 u) = φ (g p.1.2 u)}
  have hMo : ∀ p : ι, IsOpen (S \ M p) := fun p => by
    have hc := (hGc p.1.1 p.2.1).sub (hGc p.1.2 p.2.2)
    have h := hc.isOpen_inter_preimage hSo (isOpen_compl_singleton (x := (0 : φ.model.E 0)))
    convert h using 1
    ext u
    simp only [M, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff, Pi.sub_apply, sub_eq_zero]
  have hS0 : (⟨t • h₀, N₀.smul_mem t hh₀N⟩ : N₀) ∈ S := by
    change ‖t • h₀ - t • h₀‖ < τ * t
    rw [sub_self, norm_zero]; positivity
  obtain ⟨S', hS'S, hS'o, ⟨v, hvS', -⟩, hS'M⟩ :=
    exists_isOpen_subset_inter_eq_empty_or_subset M hMo hSo subset_rfl
      (Y := univ) ⟨_, hS0, mem_univ _⟩
  have hvS : v ∈ S := hS'S hvS'
  -- the points `y_e`
  set pts : Finset X := (Finset.univ.filter C).image (fun k => g k v) with hptsdef
  have hmem : ∀ k, C k → g k v ∈ pts := fun k hk =>
    Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩, rfl⟩
  set enum := pts.equivFin with henum
  refine ⟨pts.card, fun k => if hk : C k then enum ⟨g k v, hmem k hk⟩
    else enum ⟨g k₀ v, hmem k₀ hC₀⟩, fun e => (enum.symm e : X), fun e => ?_⟩
  obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 (enum.symm e).2
  have hjC : C j := (Finset.mem_filter.1 hj).2
  set ye : X := (enum.symm e : X) with hyedef
  have hyeA : ye ∈ A j ∩ φ.source := hjv ▸ hgA j hjC v hvS
  have hyeQ : Q (φ ye - φ x) = v := hjv ▸ hgQ j hjC v hvS
  have hyeR : ‖φ ye - φ x‖ < R := hjv ▸ hgR j hjC v hvS
  have hyeW₁ : ye ∈ W₁ := hρWsub ye hyeA.2 (hyeR.trans hRW)
  -- the sheets through `y_e`
  have hsheet : ∀ k, ye ∈ A k ↔ C k ∧ (if hk : C k then enum ⟨g k v, hmem k hk⟩
      else enum ⟨g k₀ v, hmem k₀ hC₀⟩) = e := by
    intro k
    constructor
    · intro hk
      by_cases hCk : C k
      · have hyk : ye = g k v := huniq k hCk v hvS ye ⟨hk, hyeA.2⟩ hyeR hyeQ
        refine ⟨hCk, ?_⟩
        rw [dif_pos hCk]
        have : (⟨g k v, hmem k hCk⟩ : pts) = enum.symm e := Subtype.ext hyk.symm
        rw [this, Equiv.apply_symm_apply]
      · exact absurd (hjv ▸ hk) (havoid j hjC v hvS k hCk)
    · rintro ⟨hCk, hbk⟩
      rw [dif_pos hCk] at hbk
      have h1 : (⟨g k v, hmem k hCk⟩ : pts) = enum.symm e := by
        rw [← hbk, Equiv.symm_apply_apply]
      have h2 : g k v = ye := congrArg Subtype.val h1
      rw [← h2]
      exact (hgA k hCk v hvS).1
  have hsame : ∀ k, ye ∈ A k → C k ∧ g k v = ye := fun k hk =>
    have hCk := ((hsheet k).1 hk).1
    ⟨hCk, (huniq k hCk v hvS ye ⟨hk, hyeA.2⟩ hyeR hyeQ).symm⟩
  -- the neighbourhood `V` of `y_e`
  obtain ⟨G, hGo, hGS'⟩ := isOpen_induced_iff.1 hS'o
  set G' : Set (φ.model.E 0) := {w | ‖w - φ x‖ < R ∧ Q (w - φ x) ∈ G} with hG'def
  have hG'o : IsOpen G' := (isOpen_lt (continuous_id.sub continuous_const).norm
    continuous_const).inter (hGo.preimage (Q.continuous.comp (continuous_id.sub continuous_const)))
  set V : Set X := φ.source ∩ φ ⁻¹' G' with hVdef
  have hVo : IsOpen V := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hG'o
  have hmemS' : ∀ u : N₀, (u : φ.model.E 0) ∈ G ↔ u ∈ S' := fun u => by
    rw [← hGS']; rfl
  have hyeV : ye ∈ V := ⟨hyeA.2, hyeR, by rw [hyeQ]; exact (hmemS' v).2 hvS'⟩
  have hcoinc : ∀ k k', ye ∈ A k → ye ∈ A k' → V ∩ A k ⊆ A k' := by
    intro k k' hk hk' a ⟨haV, hak⟩
    obtain ⟨hCk, hgk⟩ := hsame k hk
    obtain ⟨hCk', hgk'⟩ := hsame k' hk'
    have hM : S' ∩ univ ⊆ M ⟨(k, k'), hCk, hCk'⟩ := by
      rcases hS'M ⟨(k, k'), hCk, hCk'⟩ with h | h
      · exact absurd h (Set.nonempty_iff_ne_empty.1 ⟨v, ⟨hvS', mem_univ _⟩,
          show φ (g k v) = φ (g k' v) by rw [hgk, hgk']⟩)
      · exact h
    set u : N₀ := ⟨Q (φ a - φ x), hQN _⟩
    have huS' : u ∈ S' := (hmemS' u).1 haV.2.2
    have huS : u ∈ S := hS'S huS'
    have ha : a = g k u := huniq k hCk u huS a ⟨hak, haV.1⟩ haV.2.1 rfl
    have hkk' : φ (g k u) = φ (g k' u) := hM ⟨huS', mem_univ _⟩
    have hgg : g k u = g k' u :=
      φ.toPartialEquiv.injOn (hgA k hCk u huS).2 (hgA k' hCk' u huS).2 hkk'
    rw [ha, hgg]
    exact (hgA k' hCk' u huS).1
  have hVeq : ∀ k k', ye ∈ A k → ye ∈ A k' → V ∩ A k = V ∩ A k' := fun k k' hk hk' =>
    Subset.antisymm (fun a ha => ⟨ha.1, hcoinc k k' hk hk' ha⟩)
      (fun a ha => ⟨ha.1, hcoinc k' k hk' hk ha⟩)
  refine ⟨hyeW₁.1, hsheet, ⟨V, hVo, hyeV, hVeq⟩, fun k k' hk hk' => ?_⟩
  -- the relative orientations
  by_cases hn : n = 0
  · have hv0 : (v : φ.model.E 0) = 0 := by
      have : Subsingleton N₀ := Module.finrank_zero_iff.1 ((hrank k₀).trans hn)
      rw [Subsingleton.elim v 0]; rfl
    have hye : ye = x := by
      have h1 := hgest j hjC v hvS
      rw [hv0, norm_zero, mul_zero, sub_zero] at h1
      have h2 := φ.toPartialEquiv.injOn (hgA j hjC v hvS).2 hxφ
        (sub_eq_zero.1 (norm_le_zero_iff.1 h1))
      rw [← hjv]
      exact h2
    change (o k).tangent ye = (o k').tangent ye ↔ _
    rw [hye]
  · have hTye : P.submanifoldTangent (A k) ye = P.submanifoldTangent (A k') ye := by
      rw [← submanifoldTangent_inter_isOpen hVo hyeV, ← submanifoldTangent_inter_isOpen hVo hyeV
        (A := A k'), inter_comm, hVeq k k' hk hk', inter_comm]
    exact hOp k k' (Nat.pos_of_ne_zero hn) (hsame k hk).1 (hsame k' hk').1 ye
      ⟨⟨hk, hk'⟩, mem_iInter.1 (mem_iInter.1 hyeW₁.2 k) k'⟩ hTye

end MPolyfold


/-- **`HasOrientedGoodPointsAt` holds at every point of `ℝᵐ`, in every dimension** (Proposition
9.2.8 for oriented families with the continuity of orientations, the input of Lemma 9.3.4). -/
theorem hasOrientedGoodPointsAt_rn {m : ℕ} (x : Fin m → ℝ) (n : ℕ) :
    (rnPolyfold m).HasOrientedGoodPointsAt x n :=
  MPolyfold.hasOrientedGoodPointsAt_of_hasGraphBallAt (hasGraphBallAt_rn x n)
    fun A _ _ => hasContinuousLevelOneOn_rn A

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
variable {Θ : Obj → ℚ}

/-- **Lemma 9.3.4 from the graph representation**: two `n`-dimensional orientations which agree
at the good points agree on `X_∞`, if at every point of `supp(Θ)` one chart represents the
`n`-dimensional submanifolds as graphs over neighbourhoods in their tangent spaces and level-`1`
coordinates are continuous along them. -/
theorem lemma_9_3_4_of_hasGraphBallAt (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂) (hG : ∀ x ∈ supp Θ, X.PObj.HasGraphBallAt x n)
    (hlev : ∀ A : Set Obj, X.PObj.IsSmoothSubmanifold A → X.PObj.HasContinuousLevelOneOn A)
    (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  lemma_9_3_4 hΘ h₁ h₂ (fun x hx => MPolyfold.hasOrientedGoodPointsAt_of_hasGraphBallAt (hG x hx)
    fun A hA _ => hlev A hA.1) hagree

end EpGroupoid

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor} {Θ : (Fin m → ℝ) → ℚ}

/-- **Lemma 9.3.4 on `ℝᵐ`, 2021 pp. 423–424 (2017: Lemma 9.10), without hypotheses**: for a
branched ep⁺-subgroupoid `Θ` of an ep-groupoid with object M-polyfold `ℝᵐ`, two `n`-dimensional
orientations which agree at the good points agree on `X_∞`. -/
theorem lemma_9_3_4_rn (hX : X.PObj = rnPolyfold m) (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : (Fin m → ℝ) → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂) (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  lemma_9_3_4 hΘ h₁ h₂ (fun x _ => by rw [hX]; exact hasOrientedGoodPointsAt_rn x n) hagree

end EpGroupoid


/-- **Lemma 9.3.4 applied to Example 9.3.5**: since the orientations `T̂¹`, `T̂²` differ at
`(s, β⁺⁺(s))`, `s > 0`, they differ at some good point of `Θ`. -/
theorem exists_goodSet_exampleT1_ne_exampleT2 :
    ∃ y ∈ (trivial (rnPolyfold 2)).goodSet example935Theta, exampleT1 y ≠ exampleT2 y := by
  by_contra h
  push Not at h
  have hsm : ptPP 1 ∈ (trivial (rnPolyfold 2)).PObj.smoothSet :=
    mem_iInter.2 fun k => by
      change ptPP 1 ∈ (rnPolyfold 2).levelSet k
      rw [rnPolyfold_levelSet]; exact mem_univ _
  exact example_9_3_5_ne_of_pos one_pos (lemma_9_3_4_rn rfl example935Theta_isBranched
    (orientedLift1_isOrientationOfDim_rn id) (orientedLift2_isOrientationOfDim_rn id) h _ hsm)

end Polyfold
