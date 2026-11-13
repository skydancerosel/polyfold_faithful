import Polyfold.Chapter9.GraphCoord

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# The change of graph charts on a common subset of two sheets

For graph charts `c`, `c'` of two submanifolds `N`, `N'` and a point `y ∈ N ∩ N'` with
`T_yN = T_yN'`, the coordinate change `c'.coord ∘ c.q` is differentiable at `c.coord y` within
the coordinate image of `N ∩ N'`, and its derivative `D` expresses the frame of `c` in the frame
of `c'` (`GraphChart.exists_transition`).  Consequently
(`GraphChart.setIntegral_coord_image_eq`) densities `ρ`, `ρ'` on a common measurable subset `A`
which transform with `|det D|` have the same integral in the two coordinates.  Both sheets may
coincide (independence of the chart), and no smoothness of `N ∩ N'` is needed: the change of
variables is the one for maps differentiable on a measurable set.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped NNReal symmDiff

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

namespace GraphChart

variable {n : ℕ} {N N' : Set X} (c : P.GraphChart n N) (c' : P.GraphChart n N')

/-- The matrix of a linear map of `ℝⁿ` in the standard basis has its determinant. -/
theorem det_matrix_bvec (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (Matrix.of fun i j => D (bvec j) i).det = D.det := by
  change _ = LinearMap.det (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin n))]
  refine congrArg Matrix.det ?_
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.of_apply, PiLp.basisFun_apply, PiLp.basisFun_repr]
  rfl

/-- **The coordinate change at a point where the tangent spaces agree.** -/
theorem exists_transition (hN : P.IsSmoothSubmanifold N) {y : X} (hy : y ∈ N) (hy' : y ∈ N')
    (hT : P.submanifoldTangent N y = P.submanifoldTangent N' y) :
    ∃ D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      HasFDerivWithinAt (fun u => c'.coord (c.q u)) D (c.coord '' (N ∩ N')) (c.coord y) ∧
      ∀ j, chartVec c'.isChart (c.tvec y j) =
        ∑ i, D (bvec j) i • chartVec c'.isChart (c'.tvec y i) := by
  obtain ⟨Λ, hΛ, hΛv⟩ := exists_transition_deriv_chartVec c.isChart c'.isChart hN hy
    (c.subset_source hy) (c'.subset_source hy')
  have hf : HasFDerivWithinAt (fun u => c.φ (c.q u)) (c.L y) (c.coord '' (N ∩ N'))
      (c.coord y) := (c.hasFDerivWithinAt y hy).mono (image_mono inter_subset_left)
  have hpt : (fun u => c.φ (c.q u)) (c.coord y) = c.φ y := congrArg c.φ (c.q_coord' hy)
  have hmaps : MapsTo (fun u => c.φ (c.q u)) (c.coord '' (N ∩ N'))
      (c.φ '' (N ∩ c'.φ.source ∩ c.φ.source)) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w, ⟨⟨hw.1, c'.subset_source hw.2⟩, c.subset_source hw.1⟩, ?_⟩
    exact (congrArg c.φ (c.q_coord' hw.1)).symm
  have hΛ' : HasFDerivWithinAt (c.φ.transition c'.φ) Λ (c.φ '' (N ∩ c'.φ.source ∩ c.φ.source))
      ((fun u => c.φ (c.q u)) (c.coord y)) := by rw [hpt]; exact hΛ
  have h1 := HasFDerivWithinAt.comp (c.coord y) hΛ' hf hmaps
  have h2 := c'.p.hasFDerivAt.comp_hasFDerivWithinAt (c.coord y) h1
  refine ⟨c'.p.comp (Λ.comp (c.L y)), h2.congr (fun u hu => ?_) ?_, fun j => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hu
    change c'.p (c'.φ (c.q (c.coord w))) = c'.p (c.φ.transition c'.φ (c.φ (c.q (c.coord w))))
    rw [c.q_coord' hw.1, c.φ.transition_apply c'.φ (c.subset_source hw.1)]
  · change c'.p (c'.φ (c.q (c.coord y))) = c'.p (c.φ.transition c'.φ (c.φ (c.q (c.coord y))))
    rw [c.q_coord' hy, c.φ.transition_apply c'.φ (c.subset_source hy)]
  · have hw : chartVec c'.isChart (c.tvec y j) = Λ (c.L y (bvec j)) := by
      rw [hΛv _ (levelVal_tangentProj_of_mem (c.tvec_mem hy j)), c.chartVec_tvec hy]
    have hmem : chartVec c'.isChart (c.tvec y j) ∈ P.chartTangent c'.isChart N' y :=
      ⟨c.tvec y j, hT ▸ c.tvec_mem hy j, rfl⟩
    rw [← c'.L_p_of_mem hy' hmem, c'.L_apply hy', hw]
    rfl

/-- **The integrals in two graph charts agree**: `A ⊆ N ∩ N'` with Lebesgue measurable
coordinate image in `c`, the tangent spaces of `N` and `N'` agree along `A`, and the densities
transform by `ρ(y) = |det D| ρ'(y)` whenever `D` expresses the frame of `c` in the frame of
`c'`.  Then `∫_{c'(A)} ρ' ∘ c'.q = ∫_{c(A)} ρ ∘ c.q`. -/
theorem setIntegral_coord_image_eq (hN : P.IsSmoothSubmanifold N) {A : Set X}
    (hA : A ⊆ N ∩ N') (hAm : NullMeasurableSet (c.coord '' A) volume)
    (hT : ∀ y ∈ A, P.submanifoldTangent N y = P.submanifoldTangent N' y) {ρ ρ' : X → ℝ}
    (hρ : ∀ y ∈ A, ∀ D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ j, chartVec c'.isChart (c.tvec y j) =
        ∑ i, D (bvec j) i • chartVec c'.isChart (c'.tvec y i)) → ρ y = |D.det| * ρ' y) :
    ∫ u in c'.coord '' A, ρ' (c'.q u) = ∫ u in c.coord '' A, ρ (c.q u) := by
  classical
  obtain ⟨A₀, hA₀sub, hA₀m, hA₀ae⟩ := hAm.exists_measurable_subset_ae_eq
  set A₁ : Set X := c.q '' A₀ with hA₁
  have hA₁A : A₁ ⊆ A := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hA₀sub hu
    rw [c.q_coord' (hA hy).1]; exact hy
  have hcA₁ : c.coord '' A₁ = A₀ := by
    rw [hA₁, image_image]
    refine (image_congr fun u hu => ?_).trans (image_id' A₀)
    obtain ⟨y, hy, rfl⟩ := hA₀sub hu
    rw [c.q_coord' (hA hy).1]
  -- the part of `A` outside `A₁` is null in both charts
  have hdiff : c.coord '' (A \ A₁) ⊆ c.coord '' A \ A₀ := by
    rintro _ ⟨y, ⟨hy, hny⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hy, fun h => hny ?_⟩
    exact ⟨c.coord y, h, c.q_coord' (hA hy).1⟩
  have hnull : volume (c.coord '' (A \ A₁)) = 0 :=
    measure_mono_null hdiff (ae_le_set.1 hA₀ae.symm.le)
  have hH : P.IsHNull n (A \ A₁) :=
    c.isHNull_of_volume_coord_image hN (fun y hy => (hA hy.1).1) hnull
  have hnull' : volume (c'.coord '' (A \ A₁)) = 0 :=
    c'.volume_coord_image_eq_zero (fun y hy => (hA hy.1).2) hH
  have hae' : (c'.coord '' A₁ : Set _) =ᵐ[volume] (c'.coord '' A : Set _) := by
    refine measure_symmDiff_eq_zero_iff.1 (measure_mono_null ?_ hnull')
    rintro u (⟨⟨y, hy, rfl⟩, hn⟩ | ⟨⟨y, hy, rfl⟩, hn⟩)
    · exact (hn ⟨y, hA₁A hy, rfl⟩).elim
    · exact ⟨y, ⟨hy, fun hc => hn ⟨y, hc, rfl⟩⟩, rfl⟩
  rw [← setIntegral_congr_set hae', ← setIntegral_congr_set hA₀ae, ← hcA₁]
  -- the measurable case
  have hex : ∀ y ∈ A₁, ∃ D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      HasFDerivWithinAt (fun u => c'.coord (c.q u)) D (c.coord '' (N ∩ N')) (c.coord y) ∧
      ∀ j, chartVec c'.isChart (c.tvec y j) =
        ∑ i, D (bvec j) i • chartVec c'.isChart (c'.tvec y i) := fun y hy =>
    c.exists_transition c' hN (hA (hA₁A hy)).1 (hA (hA₁A hy)).2 (hT y (hA₁A hy))
  let Df : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun u => if h : c.q u ∈ A₁ then (hex (c.q u) h).choose else 0
  have hDf : ∀ (y : X) (hy : y ∈ A₁), Df (c.coord y) = (hex y hy).choose := fun y hy => by
    have hq : c.q (c.coord y) = y := c.q_coord' (hA (hA₁A hy)).1
    have hmem : c.q (c.coord y) ∈ A₁ := by rw [hq]; exact hy
    simp only [Df, dif_pos hmem]
    congr 1
    simp [hq]
  have hderiv : ∀ u ∈ c.coord '' A₁, HasFDerivWithinAt (fun u => c'.coord (c.q u)) (Df u)
      (c.coord '' A₁) u := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hDf y hy]
    exact (hex y hy).choose_spec.1.mono (image_mono (hA₁A.trans hA))
  have hinj : InjOn (fun u => c'.coord (c.q u)) (c.coord '' A₁) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩ h
    simp only [c.q_coord' (hA (hA₁A hy)).1, c.q_coord' (hA (hA₁A hw)).1] at h
    rw [c'.injOn_coord (hA (hA₁A hy)).2 (hA (hA₁A hw)).2 h]
  have himg : (fun u => c'.coord (c.q u)) '' (c.coord '' A₁) = c'.coord '' A₁ := by
    rw [image_image]
    exact image_congr fun y hy => by rw [c.q_coord' (hA (hA₁A hy)).1]
  have hm : MeasurableSet (c.coord '' A₁) := hcA₁ ▸ hA₀m
  rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hm hderiv hinj]
  refine setIntegral_congr_fun hm ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyN : y ∈ N := (hA (hA₁A hy)).1
  have hyN' : y ∈ N' := (hA (hA₁A hy)).2
  change |(Df (c.coord y)).det| • ρ' (c'.q (c'.coord (c.q (c.coord y)))) = ρ (c.q (c.coord y))
  rw [c.q_coord' hyN, c'.q_coord' hyN', hDf y hy, smul_eq_mul]
  exact (hρ y (hA₁A hy) _ (hex y hy).choose_spec.2).symm

end GraphChart

end MPolyfold

end Polyfold
