import Polyfold.Chapter9.GraphChartTransition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 (Definition 9.3.3, p. 422) and §9.5, pp. 438–445 (gap G.107).

# The sign of the frame of a graph chart for an orientation

For a graph chart `c` of a submanifold `N` with an orientation `o` (Definition 9.3.3): the set
of points where the frame `c.tvec y` is positive is relatively open in `N`, and so is its
complement in `N`; the matrix expressing the frame of `c` in the frame of a second graph chart
`c'` is continuous along `N ∩ N'`; a smooth finite-dimensional submanifold is a Borel set.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The frame `α` (of `n` vectors) is a positive frame of the oriented tangent set `g`. -/
def OrTangent.IsPos {n : ℕ} (g : OrTangent P) (α : Fin n → P.TangentSpace) : Prop :=
  ∃ h : g.dim = n, (fun i => α (Fin.cast h i)) ∈ g.frames

theorem OrTangent.isPos_mk {n : ℕ} {L : Set P.TangentSpace} {O : Set (Fin n → P.TangentSpace)}
    {α : Fin n → P.TangentSpace} : (⟨n, L, O⟩ : OrTangent P).IsPos α ↔ α ∈ O :=
  ⟨fun ⟨_, hm⟩ => hm, fun h => ⟨rfl, h⟩⟩

theorem SubmanifoldOrientation.isPos_tangent {M : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation M n) (y : X) (α : Fin n → P.TangentSpace) :
    (o.tangent y).IsPos α ↔ α ∈ o.frames y :=
  OrTangent.isPos_mk

/-- Linear independence of chart vectors over a point does not depend on the chart. -/
theorem linearIndependent_chartVec_of_chart {φ ψ : MChart X} (hφ : P.IsChart φ)
    (hψ : P.IsChart ψ) {y : X} (hyφ : y ∈ φ.source) (hyψ : y ∈ ψ.source) {n : ℕ}
    {α : Fin n → P.TangentSpace} (hα : ∀ i, P.levelVal 1 (P.tangentProj (α i)) = y)
    (h : LinearIndependent ℝ fun i => chartVec hφ (α i)) :
    LinearIndependent ℝ fun i => chartVec hψ (α i) := by
  obtain ⟨Λ, hΛ⟩ := exists_clm_chartVec hψ hφ hyψ hyφ
  refine LinearIndependent.of_comp (Λ : ψ.model.E 0 →ₗ[ℝ] φ.model.E 0) ?_
  convert h using 1
  funext i
  exact (hΛ _ (hα i)).symm

/-- A positive frame of an oriented tangent set has linearly independent chart vectors. -/
theorem IsOrientedAt.linearIndependent_chartVec {y : X} {g : OrTangent P}
    (hg : P.IsOrientedAt y g) {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y ∈ φ.source)
    {α : Fin g.dim → P.TangentSpace} (hα : α ∈ g.frames) :
    LinearIndependent ℝ fun i => chartVec hφ (α i) := by
  obtain ⟨N₀, -, -, -, ω, hO⟩ := hg.isChartOrientation hφ hyφ
  rw [hO] at hα
  obtain ⟨-, b, hb, -⟩ := hα
  have := b.linearIndependent.map' N₀.subtype (Submodule.ker_subtype _)
  have h2 : (fun i => chartVec hφ (α i)) = N₀.subtype ∘ b := funext fun i => (hb i).symm
  rw [h2]
  exact this

omit [T2Space X] [ParacompactSpace X] in
/-- A subset `Q ⊆ N` each of whose points has an open neighbourhood `U` with `N ∩ U ⊆ Q` is the
trace on `N` of an open set. -/
theorem exists_isOpen_eq_inter_of_local {N Q : Set X} (hQ : Q ⊆ N)
    (h : ∀ y ∈ Q, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ N ∩ U ⊆ Q) :
    ∃ W : Set X, IsOpen W ∧ Q = N ∩ W := by
  refine ⟨⋃₀ {U | IsOpen U ∧ N ∩ U ⊆ Q}, isOpen_sUnion fun U hU => hU.1, ?_⟩
  refine Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨U, hU, hyU, hUQ⟩ := h y hy
    exact ⟨hQ hy, U, ⟨hU, hUQ⟩, hyU⟩
  · rintro y ⟨hyN, U, ⟨-, hUQ⟩, hyU⟩
    exact hUQ ⟨hyN, hyU⟩

/-- **Two frames of an oriented tangent space of a submanifold are in the same class iff the
matrix between them has positive determinant.** -/
theorem IsOrientedAt.frames_iff_frames_iff_det_pos {A : Set X} {n : ℕ}
    (hA : P.IsSubmanifoldOfDim A n) {y : X} (hy : y ∈ A) {O : Set (Fin n → P.TangentSpace)}
    (hO : P.IsOrientedAt y ⟨n, P.submanifoldTangent A y, O⟩) {φ : MChart X} (hφ : P.IsChart φ)
    (hyφ : y ∈ φ.source) {α β : Fin n → P.TangentSpace}
    (hα : ∀ i, α i ∈ P.submanifoldTangent A y) (hβ : ∀ i, β i ∈ P.submanifoldTangent A y)
    (hαli : LinearIndependent ℝ fun i => chartVec hφ (α i))
    (hβli : LinearIndependent ℝ fun i => chartVec hφ (β i)) (M : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ j, chartVec hφ (β j) = ∑ i, M i j • chartVec hφ (α i)) :
    (β ∈ O ↔ α ∈ O) ↔ 0 < M.det := by
  obtain ⟨O₁, O₂, hne, hiff⟩ := exists_two_orientations_submanifoldTangent hA hy
  by_cases hαO : α ∈ O
  · have h1 := IsOrientedAt.mem_frames_iff_det_pos hO hφ hyφ hαO hβ M h
    rw [← h1]
    exact ⟨fun hh => hh.2 hαO, fun hb => ⟨fun _ => hαO, fun _ => hb⟩⟩
  · obtain ⟨O', hO', hne'⟩ : ∃ O' : Set (Fin n → P.TangentSpace),
        P.IsOrientedAt y ⟨n, P.submanifoldTangent A y, O'⟩ ∧ O ≠ O' := by
      rcases (hiff O).1 hO with rfl | rfl
      · exact ⟨O₂, (hiff O₂).2 (Or.inr rfl), hne⟩
      · exact ⟨O₁, (hiff O₁).2 (Or.inl rfl), hne.symm⟩
    have hα' : α ∈ O' := by
      by_contra hc
      exact hαO ((IsOrientedAt.mem_frames_iff_notMem hO hO' hne' hφ hyφ hα hαli).2 hc)
    have h1 := IsOrientedAt.mem_frames_iff_det_pos hO' hφ hyφ hα' hβ M h
    have h2 := IsOrientedAt.mem_frames_iff_notMem hO hO' hne' hφ hyφ hβ hβli
    rw [← h1]
    constructor
    · intro hh
      by_contra hc
      exact hαO (hh.1 (h2.2 hc))
    · intro hb
      exact ⟨fun hbO => absurd hb (h2.1 hbO), fun ha => absurd ha hαO⟩

namespace GraphChart

variable {n : ℕ} {N N' : Set X} (c : P.GraphChart n N) (c' : P.GraphChart n N')

include c in
/-- An orientation of a nonempty submanifold with a graph chart over `ℝⁿ` has dimension `n`. -/
theorem dim_eq_of_orientation {m : ℕ} (o : P.SubmanifoldOrientation N m) {y : X} (hy : y ∈ N) :
    m = n := by
  obtain ⟨N₀, hN₀, hfin, hrank, -⟩ :=
    (o.isOrientedAt y hy).isChartOrientation c.isChart (c.subset_source hy)
  have hrange : N₀ = LinearMap.range (c.L y : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0) :=
    SetLike.coe_injective (hN₀.trans (c.range_L y hy).symm)
  rw [hrange, LinearMap.finrank_range_of_inj (c.L_injective hy), finrank_euclideanSpace_fin]
    at hrank
  exact hrank.symm

/-- The frame of a graph chart has linearly independent chart vectors in every chart. -/
theorem linearIndependent_chartVec_tvec_of_chart {y : X} (hy : y ∈ N) {ψ : MChart X}
    (hψ : P.IsChart ψ) (hyψ : y ∈ ψ.source) :
    LinearIndependent ℝ fun i => chartVec hψ (c.tvec y i) :=
  linearIndependent_chartVec_of_chart c.isChart hψ (c.subset_source hy) hyψ
    (fun i => levelVal_tangentProj_of_mem (c.tvec_mem hy i)) (c.linearIndependent_chartVec_tvec hy)

/-- **The sign of the frame of a graph chart, locally**: near each point of `N` there is a
continuous nowhere vanishing function `d` on `N ∩ V` with `c.tvec z` positive iff `d z > 0`
(the determinant of a continuous positive frame field in the coordinates of the chart). -/
theorem exists_local_sign (hN : P.IsSmoothSubmanifold N) (hn : 0 < n)
    (o : P.SubmanifoldOrientation N n) {y₀ : X} (hy₀ : y₀ ∈ N) :
    ∃ (V : Set X) (d : X → ℝ), IsOpen V ∧ y₀ ∈ V ∧ ContinuousOn d (N ∩ V) ∧
      ∀ z ∈ N ∩ V, d z ≠ 0 ∧ (c.tvec z ∈ o.frames z ↔ 0 < d z) := by
  classical
  obtain ⟨φ₁, hφ₁, V, hV, hyV, hVφ, e, he, hc⟩ := o.continuous hn y₀ hy₀
  have hK : N ∩ V ⊆ N ∩ φ₁.source ∩ c.φ.source := fun z hz =>
    ⟨⟨hz.1, hVφ hz.2⟩, c.subset_source hz.1⟩
  have he' : ∀ z ∈ N ∩ V, ∀ i, e z i ∈ P.submanifoldTangent N z := fun z hz i =>
    (o.isOrientedAt z hz.1).mem_carrier (he z hz) i
  have hc' := continuousOn_chartVec_of_chart hφ₁ c.isChart hN hK e he' hc
  let B : X → Matrix (Fin n) (Fin n) ℝ := fun z =>
    Matrix.of fun i j => c.p (chartVec c.isChart (e z j)) i
  have hB : ContinuousOn B (N ∩ V) := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact ((EuclideanSpace.proj i).continuous.comp c.p.continuous).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hc')
  refine ⟨V, fun z => (B z).det, hV, hyV,
    (continuous_id.matrix_det).comp_continuousOn hB, fun z hz => ?_⟩
  set w : Fin n → c.φ.model.E 0 := fun i => chartVec c.isChart (e z i) with hwdef
  set T : Fin n → c.φ.model.E 0 := fun k => chartVec c.isChart (c.tvec z k) with hTdef
  have hwmem : ∀ i, w i ∈ P.chartTangent c.isChart N z := fun i => ⟨e z i, he' z hz i, rfl⟩
  have hw : ∀ i, w i = ∑ k, B z k i • T k := fun i => by
    refine (c.L_p_of_mem hz.1 (hwmem i)).symm.trans ?_
    rw [c.L_apply hz.1]
    rfl
  have hli : LinearIndependent ℝ w :=
    IsOrientedAt.linearIndependent_chartVec (o.isOrientedAt z hz.1) c.isChart
      (c.subset_source hz.1) (he z hz)
  have hTli : LinearIndependent ℝ T := c.linearIndependent_chartVec_tvec hz.1
  have hinj : Function.Injective (B z).mulVecLin := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h0 : ∑ i, v i • w i = 0 := by
      have e1 : ∑ i, v i • w i = ∑ k, ((B z).mulVec v) k • T k := by
        simp_rw [hw, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
        exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
      rw [e1]
      have hv' : (B z).mulVec v = 0 := hv
      simp [hv']
    funext i
    exact (Fintype.linearIndependent_iff.1 hli v h0 i)
  have hunit : IsUnit (B z) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (B z).det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have hBM : B z * (B z)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hident : ∀ j, chartVec c.isChart (c.tvec z j) =
      ∑ i, (B z)⁻¹ i j • chartVec c.isChart (e z i) := by
    intro j
    change T j = ∑ i, (B z)⁻¹ i j • w i
    have e1 : ∑ i, (B z)⁻¹ i j • w i = ∑ k, (∑ i, B z k i * (B z)⁻¹ i j) • T k := by
      simp_rw [hw, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    rw [e1]
    have e2 : ∀ k, ∑ i, B z k i * (B z)⁻¹ i j = (1 : Matrix (Fin n) (Fin n) ℝ) k j := fun k => by
      rw [← hBM, Matrix.mul_apply]
    simp_rw [e2, Matrix.one_apply]
    simp
  have hpos := IsOrientedAt.mem_frames_iff_det_pos (o.isOrientedAt z hz.1) c.isChart
    (c.subset_source hz.1) (he z hz) (fun i => c.tvec_mem hz.1 i) (B z)⁻¹ hident
  refine ⟨hdet.ne_zero, hpos.trans ?_⟩
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_pos]

/-- **The points of `N` where the frame of the graph chart is positive for `o` form a relatively
open subset of `N`.** -/
theorem exists_isOpen_isPos (hN : P.IsSmoothSubmanifold N) (hn : 0 < n)
    (o : P.SubmanifoldOrientation N n) :
    ∃ W : Set X, IsOpen W ∧ {y | y ∈ N ∧ c.tvec y ∈ o.frames y} = N ∩ W := by
  refine exists_isOpen_eq_inter_of_local (fun y hy => hy.1) fun y₀ hy₀ => ?_
  obtain ⟨V, d, hV, hyV, hd, hsign⟩ := c.exists_local_sign hN hn o hy₀.1
  obtain ⟨O, hO, hOe⟩ := (continuousOn_iff'.1 hd) (Ioi 0) isOpen_Ioi
  have hy₀O : y₀ ∈ O ∩ (N ∩ V) := by
    rw [← hOe]; exact ⟨(hsign y₀ ⟨hy₀.1, hyV⟩).2.1 hy₀.2, hy₀.1, hyV⟩
  refine ⟨V ∩ O, hV.inter hO, ⟨hyV, hy₀O.1⟩, fun z hz => ⟨hz.1, ?_⟩⟩
  have hzO : z ∈ O ∩ (N ∩ V) := ⟨hz.2.2, hz.1, hz.2.1⟩
  rw [← hOe] at hzO
  exact (hsign z ⟨hz.1, hz.2.1⟩).2.2 hzO.1

/-- **The points of `N` where the frame of the graph chart is not positive for `o` form a
relatively open subset of `N`.** -/
theorem exists_isOpen_not_isPos (hN : P.IsSmoothSubmanifold N) (hn : 0 < n)
    (o : P.SubmanifoldOrientation N n) :
    ∃ W : Set X, IsOpen W ∧ {y | y ∈ N ∧ c.tvec y ∉ o.frames y} = N ∩ W := by
  refine exists_isOpen_eq_inter_of_local (fun y hy => hy.1) fun y₀ hy₀ => ?_
  obtain ⟨V, d, hV, hyV, hd, hsign⟩ := c.exists_local_sign hN hn o hy₀.1
  obtain ⟨O, hO, hOe⟩ := (continuousOn_iff'.1 hd) (Iio 0) isOpen_Iio
  have hneg : ∀ z ∈ N ∩ V, (c.tvec z ∉ o.frames z ↔ d z < 0) := fun z hz => by
    rw [(hsign z hz).2, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hsign z hz).1, le_of_lt⟩
  have hy₀O : y₀ ∈ O ∩ (N ∩ V) := by
    rw [← hOe]; exact ⟨(hneg y₀ ⟨hy₀.1, hyV⟩).1 hy₀.2, hy₀.1, hyV⟩
  refine ⟨V ∩ O, hV.inter hO, ⟨hyV, hy₀O.1⟩, fun z hz => ⟨hz.1, ?_⟩⟩
  have hzO : z ∈ O ∩ (N ∩ V) := ⟨hz.2.2, hz.1, hz.2.1⟩
  rw [← hOe] at hzO
  exact (hneg z ⟨hz.1, hz.2.1⟩).2 hzO.1

/-- The matrix of the frame of `c` in the coordinates of `c'`. -/
def transMatrix (y : X) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => c'.p (chartVec c'.isChart (c.tvec y j)) i

/-- Where the tangent spaces agree, `transMatrix` expresses the frame of `c` in the frame of
`c'`. -/
theorem chartVec_tvec_eq_sum_transMatrix {y : X} (hy : y ∈ N) (hy' : y ∈ N')
    (hT : P.submanifoldTangent N y = P.submanifoldTangent N' y) (j : Fin n) :
    chartVec c'.isChart (c.tvec y j) =
      ∑ i, c.transMatrix c' y i j • chartVec c'.isChart (c'.tvec y i) := by
  have hmem : chartVec c'.isChart (c.tvec y j) ∈ P.chartTangent c'.isChart N' y :=
    ⟨c.tvec y j, hT ▸ c.tvec_mem hy j, rfl⟩
  refine (c'.L_p_of_mem hy' hmem).symm.trans ?_
  rw [c'.L_apply hy']
  rfl

/-- The set of points of `N ∩ N'` where the transition matrix has positive determinant is
relatively open in `N ∩ N'`. -/
theorem exists_isOpen_transMatrix_det_pos (hN : P.IsSmoothSubmanifold N) :
    ∃ W : Set X, IsOpen W ∧
      {y | y ∈ N ∩ N' ∧ 0 < (c.transMatrix c' y).det} = (N ∩ N') ∩ W := by
  have hK : N ∩ c'.φ.source ⊆ N ∩ c.φ.source ∩ c'.φ.source := fun z hz =>
    ⟨⟨hz.1, c.subset_source hz.1⟩, hz.2⟩
  have hc : ContinuousOn (fun z i => chartVec c.isChart (c.tvec z i)) (N ∩ c'.φ.source) := by
    have h1 : ContinuousOn (fun z (i : Fin n) => c.L z (bvec i)) N :=
      continuousOn_pi.2 fun i =>
        (ContinuousLinearMap.apply ℝ _ (bvec i)).continuous.comp_continuousOn c.continuousOn_L
    refine (h1.mono inter_subset_left).congr fun z hz => ?_
    funext i
    exact c.chartVec_tvec hz.1 i
  have hc' := continuousOn_chartVec_of_chart c.isChart c'.isChart hN hK c.tvec
    (fun z hz i => c.tvec_mem hz.1 i) hc
  have hB : ContinuousOn (c.transMatrix c') (N ∩ c'.φ.source) := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact ((EuclideanSpace.proj i).continuous.comp c'.p.continuous).comp_continuousOn
      ((continuous_apply j).comp_continuousOn hc')
  have hd : ContinuousOn (fun z => (c.transMatrix c' z).det) (N ∩ c'.φ.source) :=
    (continuous_id.matrix_det).comp_continuousOn hB
  obtain ⟨O, hO, hOe⟩ := (continuousOn_iff'.1 hd) (Ioi 0) isOpen_Ioi
  refine ⟨O, hO, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hpos⟩
    have : y ∈ O ∩ (N ∩ c'.φ.source) := by
      rw [← hOe]; exact ⟨hpos, hy.1, c'.subset_source hy.2⟩
    exact ⟨hy, this.1⟩
  · rintro ⟨hy, hyO⟩
    have : y ∈ O ∩ (N ∩ c'.φ.source) := ⟨hyO, hy.1, c'.subset_source hy.2⟩
    rw [← hOe] at this
    exact ⟨hy, this.1⟩

end GraphChart

/-- **A smooth finite-dimensional submanifold is a Borel set** (it is locally closed: near each
of its points it is the fixed point set of a retraction). -/
theorem IsSmoothSubmanifold.measurableSet_borel {N : Set X} (hN : P.IsSmoothSubmanifold N) :
    MeasurableSet[borel X] N := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hN.proposition_4_2_3_two
  exact hU.measurableSet.inter hZ.measurableSet

end MPolyfold

end Polyfold
