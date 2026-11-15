import Polyfold.Chapter9.BoundaryEndFaces
import Polyfold.Chapter4.BoundaryIntegralEnds
import Polyfold.Chapter6.CornerSmoothMaps
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 4.1.1
(p. 173), Theorem 4.4.7 (p. 199) and the proof of Theorem 6.7.1 (p. 278).

# Face chart pairs of an end without faces

Let `Z` be an M-polyfold with a corner structure of dimension `n + 1` and `j : A → Z` an
embedding of an M-polyfold `A` with a corner structure of dimension `n`, with closed range,
`d_Z(j x) = d_A(x) + 1`, and `range j` relatively open in `\{d_Z = 1\}`.  No condition is put on
the faces of `Z`.

## What is formalized

* `exists_endCoordinate`: in every coordinate corner chart `κ` of `Z` at a point of `range j`
  there are a coordinate `i₀` and an open neighbourhood `B` of the point on which `range j` is
  the coordinate face `\{y_{i₀} = 0\}`.
* `quadrantFaceIncl`, `quadrantFaceProj`: the face `\{xᵢ = 0\}` of `[0, ∞)ⁿ⁺¹` and its
  projection; the inclusion is `C^∞`.
* `EndChartData`, `EndChartData.toChart`, `EndChartData.toFaceChartPair`: a chart `e` of `Z`, a
  coordinate `i`, an open set `B` on which `range j = \{xᵢ = 0\}`, and a `C^∞` left inverse `g`
  of `j` on `B` give the chart `π_i ∘ e ∘ j` of `A` (inverse `g ∘ e⁻¹ ∘ ιᵢ`) and a face chart
  pair of `j` in the chart `e`.
* `contMDiffOn_of_isScSmoothOn`: a map sc-smooth on an open set between finite-dimensional
  M-polyfolds with corner structures is `C^∞` there.
* **`isAdaptedEnd_of_localInverse`**: if every point of `range j_b` has a `C^∞` local left inverse
  of `j_b`, the end `j_b` is adapted (`IsAdaptedEnd`) for the corner charted space of `Z`.
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### The faces of the quadrant -/

section QuadrantFace

variable {n : ℕ}

/-- The face `\{xᵢ = 0\}` of `[0, ∞)ⁿ⁺¹`: `w ↦ (w₀, …, 0, …, w_{n-1})`. -/
def quadrantFaceIncl (i : Fin (n + 1)) (w : EuclideanQuadrant n) : EuclideanQuadrant (n + 1) :=
  ⟨faceEmbedding i w.1, fun k => by
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
    · simp [faceEmbedding_apply]
    · simpa [faceEmbedding_apply] using w.2 l⟩

/-- The projection `[0, ∞)ⁿ⁺¹ → [0, ∞)ⁿ` forgetting the coordinate `xᵢ`. -/
def quadrantFaceProj (i : Fin (n + 1)) (v : EuclideanQuadrant (n + 1)) : EuclideanQuadrant n :=
  ⟨faceProjection i v.1, fun k => by
    simpa [faceProjection, Fin.removeNth] using v.2 (i.succAbove k)⟩

theorem quadrantFaceIncl_apply_self (i : Fin (n + 1)) (w : EuclideanQuadrant n) :
    (quadrantFaceIncl i w).1 i = 0 := by
  simp [quadrantFaceIncl, faceEmbedding_apply]

theorem quadrantFaceProj_incl (i : Fin (n + 1)) (w : EuclideanQuadrant n) :
    quadrantFaceProj i (quadrantFaceIncl i w) = w :=
  Subtype.ext (faceProjection_faceEmbedding i w.1)

theorem quadrantFaceIncl_proj {i : Fin (n + 1)} {v : EuclideanQuadrant (n + 1)} (hv : v.1 i = 0) :
    quadrantFaceIncl i (quadrantFaceProj i v) = v :=
  Subtype.ext (faceEmbedding_faceProjection hv)

theorem continuous_quadrantFaceIncl (i : Fin (n + 1)) : Continuous (quadrantFaceIncl (n := n) i) :=
  ((faceEmbedding i).continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_quadrantFaceProj (i : Fin (n + 1)) : Continuous (quadrantFaceProj (n := n) i) :=
  ((faceProjection i).continuous.comp continuous_subtype_val).subtype_mk _

/-- The inclusion of the face `\{xᵢ = 0\}` is `C^∞` (it is linear in the model). -/
theorem contMDiff_quadrantFaceIncl (i : Fin (n + 1)) :
    ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ (quadrantFaceIncl i) := by
  rw [contMDiff_iff_target]
  refine ⟨continuous_quadrantFaceIncl i, fun y => ?_⟩
  rw [extChartAt_self_eq]
  exact ((faceEmbedding i).contDiff.contMDiff.comp (𝓠 n).contMDiff).contMDiffOn

end QuadrantFace

/-! ### Charts of an end from a local left inverse -/

section EndChart

variable {n : ℕ} {Z : Type*} [TopologicalSpace Z] {A : Type*} [TopologicalSpace A]

variable (n) in
/-- **The data of a chart of an end**: a chart `e` of `Z`, a coordinate `i`, an open set
`B ⊆ dom e` on which `range j` is the face `\{xᵢ = 0\}` of `e`, and a left inverse `g` of `j`
on `B`. -/
structure EndChartData (j : A → Z) where
  /-- The chart of `Z`. -/
  e : OpenPartialHomeomorph Z (EuclideanQuadrant (n + 1))
  /-- The coordinate of the face. -/
  i : Fin (n + 1)
  /-- The open set on which `range j` is the face. -/
  B : Set Z
  isOpen_B : IsOpen B
  subset_source : B ⊆ e.source
  mem_range_iff : ∀ y ∈ B, y ∈ range j ↔ (e y).1 i = 0
  /-- The left inverse of `j`. -/
  g : Z → A
  continuousOn_g : ContinuousOn g B
  g_j : ∀ q, j q ∈ B → g (j q) = q

namespace EndChartData

variable {j : A → Z} (D : EndChartData n j)

theorem j_g {y : Z} (hy : y ∈ B D) (h0 : (D.e y).1 D.i = 0) : j (D.g y) = y := by
  obtain ⟨q, rfl⟩ := (D.mem_range_iff y hy).2 h0
  rw [D.g_j q hy]

theorem e_j_apply {q : A} (hq : j q ∈ D.B) : (D.e (j q)).1 D.i = 0 :=
  (D.mem_range_iff _ hq).1 ⟨q, rfl⟩

/-- **The chart of `A`**: `q ↦ π_i (e (j q))` on `j⁻¹(B)`, with inverse `w ↦ g (e⁻¹ (ιᵢ w))`. -/
def toChart (hj : Continuous j) : OpenPartialHomeomorph A (EuclideanQuadrant n) where
  toFun q := quadrantFaceProj D.i (D.e (j q))
  invFun w := D.g (D.e.symm (quadrantFaceIncl D.i w))
  source := j ⁻¹' D.B
  target := quadrantFaceIncl D.i ⁻¹' (D.e.target ∩ D.e.symm ⁻¹' D.B)
  map_source' q hq := by
    change quadrantFaceIncl D.i (quadrantFaceProj D.i (D.e (j q))) ∈
      D.e.target ∩ D.e.symm ⁻¹' D.B
    rw [quadrantFaceIncl_proj (D.e_j_apply hq)]
    refine ⟨D.e.map_source (D.subset_source hq), ?_⟩
    rw [mem_preimage, D.e.left_inv (D.subset_source hq)]
    exact hq
  map_target' w hw := by
    change j (D.g (D.e.symm (quadrantFaceIncl D.i w))) ∈ D.B
    rw [D.j_g hw.2 (by rw [D.e.right_inv hw.1]; exact quadrantFaceIncl_apply_self _ _)]
    exact hw.2
  left_inv' q hq := by
    rw [quadrantFaceIncl_proj (D.e_j_apply hq), D.e.left_inv (D.subset_source hq), D.g_j q hq]
  right_inv' w hw := by
    rw [D.j_g hw.2 (by rw [D.e.right_inv hw.1]; exact quadrantFaceIncl_apply_self _ _),
      D.e.right_inv hw.1, quadrantFaceProj_incl]
  open_source := D.isOpen_B.preimage hj
  open_target := (D.e.isOpen_inter_preimage_symm D.isOpen_B).preimage
    (continuous_quadrantFaceIncl D.i)
  continuousOn_toFun := (continuous_quadrantFaceProj D.i).comp_continuousOn
    (D.e.continuousOn.comp hj.continuousOn fun _ hq => D.subset_source hq)
  continuousOn_invFun := D.continuousOn_g.comp
    (D.e.continuousOn_symm.comp (continuous_quadrantFaceIncl D.i).continuousOn
      fun _ hw => hw.1) fun _ hw => hw.2

theorem toChart_source (hj : Continuous j) : (D.toChart hj).source = j ⁻¹' D.B := rfl

variable [ChartedSpace (EuclideanQuadrant (n + 1)) Z]
  [ChartedSpace (EuclideanQuadrant n) A] [IsManifold (𝓠 n) ∞ A]

/-- **The chart of `A` is in the maximal atlas** if `e` is, `j` is `C^∞`, and `g` is `C^∞` on
`B`. -/
theorem toChart_mem_maximalAtlas (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j)
    (he : D.e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ Z)
    (hgs : ContMDiffOn (𝓠 (n + 1)) (𝓠 n) ∞ D.g D.B) :
    D.toChart hjs.continuous ∈ IsManifold.maximalAtlas (𝓠 n) ∞ A := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · rw [contMDiffOn_iff_target]
    refine ⟨(D.toChart hjs.continuous).continuousOn, fun y => ?_⟩
    rw [extChartAt_self_eq]
    have hsm : ContMDiffOn (𝓠 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun x => faceProjection D.i (D.e.extend (𝓠 (n + 1)) (j x))) (j ⁻¹' D.e.source) :=
      (faceProjection D.i).contMDiff.comp_contMDiffOn
        ((D.e.contMDiffOn_extend he).comp hjs.contMDiffOn fun x hx => hx)
    exact (hsm.mono fun x hx => D.subset_source hx.1).congr fun x _ => rfl
  · exact hgs.comp ((contMDiffOn_symm_of_mem_maximalAtlas he).comp
      (contMDiff_quadrantFaceIncl D.i).contMDiffOn fun _ hw => hw.1) fun _ hw => hw.2

/-- **The face chart pair of the end** in the chart `e`, with the coordinate `i`. -/
def toFaceChartPair (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j)
    (he : D.e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ Z)
    (hgs : ContMDiffOn (𝓠 (n + 1)) (𝓠 n) ∞ D.g D.B) : FaceChartPair n j where
  eN := D.toChart hjs.continuous
  e := D.e
  i := D.i
  mem_N := D.toChart_mem_maximalAtlas hjs he hgs
  mem_M := he
  mapsTo := fun _ hp => D.subset_source hp
  extend_eq := fun _ hp => (faceEmbedding_faceProjection (D.e_j_apply hp)).symm

end EndChartData

end EndChart

/-! ### The end is a coordinate face -/

namespace MPolyfold

universe u

section EndCoordinate

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {PA : MPolyfold A}
  {j : A → Z}

/-- A point of degeneracy index `1` has exactly one vanishing coordinate. -/
theorem CornerCoords.exists_unique_coord_eq_zero {m : ℕ} (κ : CornerCoords Q m) {w : Z}
    (hw : w ∈ κ.s) (h1 : Q.degIndex w = 1) :
    ∃ i, κ.coord w i = 0 ∧ ∀ k, k ≠ i → 0 < κ.coord w k := by
  rw [κ.degIndex_eq_card hw, Finset.card_eq_one] at h1
  obtain ⟨i, hi⟩ := h1
  have hmem : ∀ k, κ.coord w k = 0 ↔ k = i := fun k => by
    simpa using Finset.ext_iff.1 hi k
  exact ⟨i, (hmem i).2 rfl, fun k hk =>
    lt_of_le_of_ne (κ.coord_nonneg hw k) fun h => hk ((hmem k).1 h.symm)⟩

/-- A point with all coordinates positive has degeneracy index `0`. -/
theorem CornerCoords.degIndex_eq_zero_of_coord_pos {m : ℕ} (κ : CornerCoords Q m) {w : Z}
    (hw : w ∈ κ.s) (hpos : ∀ k, 0 < κ.coord w k) : Q.degIndex w = 0 := by
  rw [κ.degIndex_eq_card hw, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun k _ => (hpos k).ne'

/-- **Near a point of `range j`, `range j` is a coordinate face of every corner chart**
(2021, Theorem 4.4.7 and the proof of Theorem 6.7.1, without faces): for `j` an embedding with
closed range, `d_Z ∘ j = d_A + 1` and `range j` relatively open in `\{d_Z = 1\}`, and for every
coordinate corner chart `κ` of `Z` at `z ∈ range j`, there are a coordinate `i₀` and an open
`B ∋ z` with `B ∩ range j = B ∩ \{y_{i₀} = 0\}`.  The points of `range j` with `d_Z = 1` near
`z` form a preconnected set (`exists_isPreconnected_end`), so they lie on one coordinate face;
conversely the points of that face with `d_Z = 1` near `z` form a preconnected set meeting
`range j`, in which `range j` is open and closed. -/
theorem exists_endCoordinate (hj : IsEmbedding j) (hjc : IsClosed (range j))
    (hcsA : PA.HasCornerStructureOfDim n) (hd : ∀ x, Q.degIndex (j x) = PA.degIndex x + 1)
    (hE1 : ∀ p ∈ range j, Q.degIndex p = 1 → ∀ᶠ z in 𝓝 p, Q.degIndex z = 1 → z ∈ range j)
    (κ : CornerCoords Q (n + 1)) {z : Z} (hz : z ∈ range j) (hzκ : z ∈ κ.s) :
    ∃ (i₀ : Fin (n + 1)) (B : Set Z), IsOpen B ∧ z ∈ B ∧ B ⊆ κ.s ∧
      ∀ y ∈ B, (y ∈ range j ↔ κ.coord y i₀ = 0) := by
  obtain ⟨O, hO, hzO, hOs, hRc, hzR⟩ :=
    exists_isPreconnected_end (Q := Q) hj hcsA hd hz κ.isOpen_s hzκ
  have hRne : (range j ∩ O ∩ {w | Q.degIndex w = 1}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hzR
    exact hzR
  obtain ⟨w₀, hw₀⟩ := hRne
  obtain ⟨i₀, hw₀0, -⟩ := κ.exists_unique_coord_eq_zero (hOs hw₀.1.2) hw₀.2
  -- the open pieces `V = \{y_k > 0, k ≠ i₀\}` and `V' = \{y_{i₀} > 0\}`
  set V := κ.s ∩ κ.coord ⁻¹' {y | ∀ k, k ≠ i₀ → 0 < y k} with hV
  set V' := κ.s ∩ κ.coord ⁻¹' {y | 0 < y i₀} with hV'
  have hVo : IsOpen V := by
    refine κ.isOpen_inter_preimage_coord ?_
    have : {y : Fin (n + 1) → ℝ | ∀ k, k ≠ i₀ → 0 < y k} =
        ⋂ k ∈ ({i₀}ᶜ : Set (Fin (n + 1))), {y | 0 < y k} := by
      ext y; simp
    rw [this]
    exact (Set.toFinite _).isOpen_biInter fun k _ => isOpen_lt continuous_const (continuous_apply k)
  have hV'o : IsOpen V' :=
    κ.isOpen_inter_preimage_coord (isOpen_lt continuous_const (continuous_apply i₀))
  have hRV : range j ∩ O ∩ {w | Q.degIndex w = 1} ⊆ V := by
    have hsub : range j ∩ O ∩ {w | Q.degIndex w = 1} ⊆ V ∪ V' := fun w hw => by
      have hws := hOs hw.1.2
      obtain ⟨i, -, hipos⟩ := κ.exists_unique_coord_eq_zero hws hw.2
      by_cases hi : i = i₀
      · subst hi; exact Or.inl ⟨hws, hipos⟩
      · exact Or.inr ⟨hws, hipos i₀ (Ne.symm hi)⟩
    have hdisj : (range j ∩ O ∩ {w | Q.degIndex w = 1}) ∩ (V ∩ V') = ∅ :=
      eq_empty_iff_forall_notMem.2 fun w hw => by
        have h0 := κ.degIndex_eq_zero_of_coord_pos hw.2.1.1 fun k => by
          by_cases hk : k = i₀
          · subst hk; exact hw.2.2.2
          · exact hw.2.1.2 k hk
        have h1 : Q.degIndex w = 1 := hw.1.2
        omega
    rcases isPreconnected_iff_subset_of_disjoint.1 hRc V V' hVo hV'o hsub hdisj with h | h
    · exact h
    · exact absurd (h hw₀).2 (by change ¬ 0 < κ.coord w₀ i₀; rw [hw₀0]; exact lt_irrefl 0)
  have hR0 : ∀ w ∈ range j ∩ O ∩ {w | Q.degIndex w = 1}, κ.coord w i₀ = 0 := fun w hw => by
    obtain ⟨i, hi0, -⟩ := κ.exists_unique_coord_eq_zero (hOs hw.1.2) hw.2
    by_cases hi : i = i₀
    · exact hi ▸ hi0
    · exact absurd hi0 ((hRV hw).2 i hi).ne'
  -- the coordinate ball `B ⊆ O`
  have hcK : κ.coord z ∈ κ.W ∩ {y | ∀ i, 0 ≤ y i} := ⟨κ.coord_mem_W hzκ, κ.coord_nonneg hzκ⟩
  have hφ : ContinuousWithinAt κ.coordInv (κ.W ∩ {y | ∀ i, 0 ≤ y i}) (κ.coord z) :=
    κ.continuousOn_coordInv _ hcK
  have h1 : ∀ᶠ y in 𝓝[κ.W ∩ {y | ∀ i, 0 ≤ y i}] κ.coord z, κ.coordInv y ∈ O :=
    hφ.preimage_mem_nhdsWithin (hO.mem_nhds (by rw [κ.coordInv_coord hzκ]; exact hzO))
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.mem_nhdsWithin_iff.1 h1
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.isOpen_iff.1 κ.isOpen_W _ hcK.1
  set ρ := min r₁ r₂
  have hρ : 0 < ρ := lt_min hr₁ hr₂
  have hballW : Metric.ball (κ.coord z) ρ ⊆ κ.W :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hr₂'
  set B := κ.s ∩ κ.coord ⁻¹' Metric.ball (κ.coord z) ρ with hB
  have hBo : IsOpen B := κ.isOpen_inter_preimage_coord Metric.isOpen_ball
  have hzB : z ∈ B := ⟨hzκ, Metric.mem_ball_self hρ⟩
  have hBO : B ⊆ O := fun w hw => by
    have : κ.coordInv (κ.coord w) ∈ O :=
      hr₁' ⟨Metric.ball_subset_ball (min_le_left _ _) hw.2, hballW hw.2, κ.coord_nonneg hw.1⟩
    rwa [κ.coordInv_coord hw.1] at this
  -- `range j ∩ B ⊆ \{y_{i₀} = 0\}`
  have hfwd : ∀ y ∈ B, y ∈ range j → κ.coord y i₀ = 0 := by
    intro y hyB hyj
    obtain ⟨O', -, -, hO'O, -, hycl⟩ :=
      exists_isPreconnected_end (Q := Q) hj hcsA hd hyj hO (hBO hyB)
    have hsub : range j ∩ O' ∩ {w | Q.degIndex w = 1} ⊆
        range j ∩ O ∩ {w | Q.degIndex w = 1} := fun w hw => ⟨⟨hw.1.1, hO'O hw.1.2⟩, hw.2⟩
    have hcl := closure_mono hsub hycl
    by_contra hne
    have hN : κ.s ∩ κ.coord ⁻¹' {u | u i₀ ≠ 0} ∈ 𝓝 y :=
      (κ.isOpen_inter_preimage_coord (isOpen_ne_fun (continuous_apply i₀)
        continuous_const)).mem_nhds ⟨hyB.1, hne⟩
    obtain ⟨w, hwN, hwR⟩ := mem_closure_iff_nhds.1 hcl _ hN
    exact hwN.2 (hR0 w hwR)
  -- the face piece `F = κ⁻¹(ball ∩ \{u_{i₀} = 0, u_k > 0\})` lies in `range j`
  set P' := Metric.ball (κ.coord z) ρ ∩
    {u : Fin (n + 1) → ℝ | u i₀ = 0 ∧ ∀ k, k ≠ i₀ → 0 < u k} with hP'
  have hP'K : P' ⊆ κ.W ∩ {y | ∀ i, 0 ≤ y i} := fun u hu => ⟨hballW hu.1, fun k => by
    by_cases hk : k = i₀
    · rw [hk, hu.2.1]
    · exact (hu.2.2 k hk).le⟩
  have hconv : Convex ℝ P' := by
    refine (convex_ball _ _).inter ?_
    intro u hu u' hu' a b ha hb hab
    refine ⟨by simp [hu.1, hu'.1], fun k hk => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hu'.2 k hk
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hu.2 k hk)) (mul_nonneg hb (hu'.2 k hk).le)
  have hFc : IsPreconnected (κ.coordInv '' P') :=
    hconv.isPreconnected.image _ (κ.continuousOn_coordInv.mono hP'K)
  have hFmem : ∀ w ∈ κ.coordInv '' P', Q.degIndex w = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    have hmem := κ.coordInv_mem (hP'K hu).1 (hP'K hu).2
    have hcu := κ.coord_coordInv (hP'K hu).1 (hP'K hu).2
    exact κ.degIndex_eq_one hmem (by rw [hcu]; exact hu.2.1) fun k hk => by
      rw [hcu]; exact (hu.2.2 k hk).ne'
  obtain ⟨w₁, hw₁B, hw₁R⟩ := mem_closure_iff_nhds.1 hzR B (hBo.mem_nhds hzB)
  have hw₁F : w₁ ∈ κ.coordInv '' P' := by
    have hs := hOs hw₁R.1.2
    obtain ⟨i, hi0, hipos⟩ := κ.exists_unique_coord_eq_zero hs hw₁R.2
    have hi : i = i₀ := by
      by_contra hne
      exact absurd (hR0 w₁ hw₁R) (hipos i₀ (Ne.symm hne)).ne'
    subst hi
    exact ⟨κ.coord w₁, ⟨hw₁B.2, hi0, hipos⟩, κ.coordInv_coord hs⟩
  have hFj : κ.coordInv '' P' ⊆ range j := by
    have hO1 : IsOpen {w | ∀ᶠ v in 𝓝 w, Q.degIndex v = 1 → v ∈ range j} :=
      isOpen_setOfPred_eventually_nhds
    have hsub : κ.coordInv '' P' ⊆
        {w | ∀ᶠ v in 𝓝 w, Q.degIndex v = 1 → v ∈ range j} ∪ (range j)ᶜ := fun w hw => by
      by_cases hwj : w ∈ range j
      · exact Or.inl (hE1 w hwj (hFmem w hw))
      · exact Or.inr hwj
    have hdisj : κ.coordInv '' P' ∩
        ({w | ∀ᶠ v in 𝓝 w, Q.degIndex v = 1 → v ∈ range j} ∩ (range j)ᶜ) = ∅ :=
      eq_empty_iff_forall_notMem.2 fun w hw => hw.2.2 (hw.2.1.self_of_nhds (hFmem w hw.1))
    rcases isPreconnected_iff_subset_of_disjoint.1 hFc _ _ hO1 hjc.isOpen_compl hsub hdisj
      with h | h
    · exact fun w hw => (h hw).self_of_nhds (hFmem w hw)
    · exact absurd hw₁R.1.1 (h hw₁F)
  -- `B ∩ \{y_{i₀} = 0\} ⊆ closure F ⊆ range j`
  have hbwd : ∀ y ∈ B, κ.coord y i₀ = 0 → y ∈ range j := by
    intro y hyB hy0
    have huK : κ.coord y ∈ κ.W ∩ {y | ∀ i, 0 ≤ y i} :=
      ⟨κ.coord_mem_W hyB.1, κ.coord_nonneg hyB.1⟩
    set v : Fin (n + 1) → ℝ := fun k => if k = i₀ then 0 else 1 with hv
    have hlin : Tendsto (fun ε : ℝ => κ.coord y + ε • v) (𝓝 0) (𝓝 (κ.coord y)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 _ (by simp)
    have hpath : Tendsto (fun ε : ℝ => κ.coord y + ε • v) (𝓝[>] 0) (𝓝[P'] (κ.coord y)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlin.mono_left nhdsWithin_le_nhds, ?_⟩
      have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), κ.coord y + ε • v ∈ Metric.ball (κ.coord z) ρ :=
        (hlin.mono_left nhdsWithin_le_nhds).eventually (Metric.isOpen_ball.mem_nhds hyB.2)
      filter_upwards [hb, self_mem_nhdsWithin] with ε hε hεpos
      refine ⟨hε, by simp [hv, hy0], fun k hk => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, if_neg hk, mul_one]
      exact add_pos_of_nonneg_of_pos (κ.coord_nonneg hyB.1 k) hεpos
    have hcy : ContinuousWithinAt κ.coordInv P' (κ.coord y) :=
      (κ.continuousOn_coordInv _ huK).mono hP'K
    have ht : Tendsto (fun ε : ℝ => κ.coordInv (κ.coord y + ε • v)) (𝓝[>] 0) (𝓝 y) := by
      have := hcy.tendsto.comp hpath
      rwa [κ.coordInv_coord hyB.1] at this
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), κ.coordInv (κ.coord y + ε • v) ∈ κ.coordInv '' P' :=
      (tendsto_nhdsWithin_iff.1 hpath).2.mono fun ε hε => mem_image_of_mem _ hε
    exact closure_minimal hFj hjc (mem_closure_of_tendsto ht hev)
  exact ⟨i₀, B, hBo, hzB, fun w hw => hw.1, fun y hy => ⟨hfwd y hy, hbwd y hy⟩⟩

end EndCoordinate

/-! ### Maps sc-smooth on an open set -/

/-- **A map sc-smooth on an open set between finite-dimensional M-polyfolds with corner
structures is `C^∞` there** (2021 Definition 4.1.1, p. 173, with Corollary 1.2.5): for the
Mathlib manifolds with corners `cornerChartedSpace` of dimensions `n` and `n'`
(`contMDiff_of_isScSmoothMap` on an open set). -/
theorem contMDiffOn_of_isScSmoothOn {M N : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
    {Q : MPolyfold M} {Q' : MPolyfold N} {n n' : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]
    (hch : inst = Q.cornerChartedSpace hcs)
    (hcs' : Q'.HasCornerStructureOfDim n') [inst' : ChartedSpace (EuclideanQuadrant n') N]
    (hch' : inst' = Q'.cornerChartedSpace hcs')
    {G : M → N} {U : Set M} (hG : Q.IsScSmoothOn Q' G U) : ContMDiffOn (𝓠 n) (𝓠 n') ∞ G U := by
  intro x hxU
  refine ContMDiffAt.contMDiffWithinAt ?_
  set κ := hcs.coords x
  set κ' := hcs'.coords (G x)
  have hc : extChartAt (𝓠 n) x = κ.toQuadrantChart.extend (𝓠 n) := by
    rw [extChartAt, chartAt_eq_of_eq hcs hch x]
    rfl
  have hc' : extChartAt (𝓠 n') (G x) = κ'.toQuadrantChart.extend (𝓠 n') := by
    rw [extChartAt, chartAt_eq_of_eq hcs' hch' (G x)]
    rfl
  have hGc : ContinuousAt G x := hG.continuousOn.continuousAt (hG.isOpen.mem_nhds hxU)
  rw [contMDiffAt_iff]
  refine ⟨hGc, ?_⟩
  rw [hc, hc']
  have := κ.isCornerChart.finiteDimensional
  have := κ'.isCornerChart.finiteDimensional
  have hso := TangentPre.isOpen_fdomOn hG κ.χ κ'.χ
  have hU := relOpen_image_fdom κ.isCornerChart (TangentPre.fdomOn_subset _ _ _ _) hso
  have hsc : IsScSmooth (κ.χ '' TangentPre.fdomOn U κ.χ G κ'.χ) (κ'.χ ∘ G ∘ κ.χ.symm) :=
    (TangentPre.isScSmoothRetractMap_coordOn hG κ.isChart κ'.isChart subset_rfl
      hso).comp_isScSmooth (ScRetraction.id hU) (image_id _)
  have hcd := contDiffOn_of_finiteDim hU.isScDomain hsc
  have haff : ContDiff ℝ ∞ κ.aff := by
    have : κ.aff = fun y => κ.lin y + κ.aff 0 := funext κ.aff_eq
    rw [this]
    exact κ.lin.contDiff.add contDiff_const
  have hout : ContDiff ℝ ∞ fun z : κ'.χ.model.E 0 =>
      (WithLp.toLp 2 (κ'.Ψ z + κ'.c) : EuclideanSpace ℝ (Fin n')) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm.contDiff.comp
      (κ'.Ψ.contDiff.add contDiff_const)
  have hx : x ∈ κ.toQuadrantChart.source := hcs.mem_coords x
  have hxt : κ.toQuadrantChart.extend (𝓠 n) x ∈ (κ.toQuadrantChart.extend (𝓠 n)).target :=
    (κ.toQuadrantChart.extend (𝓠 n)).map_source (by rwa [κ.toQuadrantChart.extend_source])
  have hsx : (κ.toQuadrantChart.extend (𝓠 n)).symm (κ.toQuadrantChart.extend (𝓠 n) x) = x :=
    κ.toQuadrantChart.extend_left_inv hx
  set T : Set (EuclideanSpace ℝ (Fin n)) := (κ.toQuadrantChart.extend (𝓠 n)).target ∩
    (κ.toQuadrantChart.extend (𝓠 n)).symm ⁻¹' (U ∩ G ⁻¹' κ'.s) with hT
  have hon : ContDiffOn ℝ ∞ (κ'.toQuadrantChart.extend (𝓠 n') ∘ G ∘
      (κ.toQuadrantChart.extend (𝓠 n)).symm) T := by
    refine (hout.comp_contDiffOn (hcd.comp haff.contDiffOn fun y hy => ?_)).congr fun y hy => ?_
    · obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy.1
      exact h2 ▸ ⟨_, ⟨⟨hy.2.1, κ.s_subset h1⟩, κ'.s_subset hy.2.2⟩, rfl⟩
    · obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy.1
      simp only [Function.comp_apply]
      rw [κ'.extend_eq_toLp_coord hy.2.2, h2, κ.χ.symm_apply_apply (κ.s_subset h1)]
      rfl
  have hmem : κ.toQuadrantChart.extend (𝓠 n) x ∈ T := by
    refine ⟨hxt, ?_⟩
    change (κ.toQuadrantChart.extend (𝓠 n)).symm (κ.toQuadrantChart.extend (𝓠 n) x) ∈
      U ∩ G ⁻¹' κ'.s
    rw [hsx]
    exact ⟨hxU, hcs'.mem_coords (G x)⟩
  have htn := κ.toQuadrantChart.extend_target_mem_nhdsWithin (I := 𝓠 n) hx
  have hTn : T ∈ 𝓝[range (𝓠 n)] (κ.toQuadrantChart.extend (𝓠 n) x) := by
    refine inter_mem htn (nhdsWithin_le_of_mem htn ?_)
    have hcont := κ.toQuadrantChart.continuousOn_extend_symm (I := 𝓠 n) _ hxt
    refine hcont.preimage_mem_nhdsWithin ?_
    rw [hsx]
    exact inter_mem (hG.isOpen.mem_nhds hxU)
      (hGc.preimage_mem_nhds (κ'.isOpen_s.mem_nhds (hcs'.mem_coords (G x))))
  exact (hon _ hmem).mono_of_mem_nhdsWithin hTn

/-! ### Adapted ends -/

section Adapted

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} {N : Bool → Type u} [∀ b, TopologicalSpace (N b)] [∀ b, T2Space (N b)]
  [∀ b, ParacompactSpace (N b)] {PN : ∀ b, MPolyfold (N b)} {j : ∀ b, N b → Z}

/-- **An end with smooth local left inverses is adapted** (`IsAdaptedEnd`, for the corner
charted space of `Z`; 2021, Theorem 4.4.7 and the proof of Theorem 6.7.1, without faces): if
`j_b` is a `C^∞` embedding with closed range, `d_Z ∘ j_b = d_{N_b} + 1`, `range j_b` is
relatively open in `\{d_Z = 1\}`, and `j_b` has `C^∞` left inverses near every point of its
range, then at every `p` the chart `chartAt (j_b p)` has a coordinate face equal to `range j_b`
near `j_b p` (`exists_endCoordinate`) and gives a face chart pair of `j_b`
(`EndChartData.toFaceChartPair`). -/
theorem isAdaptedEnd_of_localInverse (hcs : Q.HasCornerStructureOfDim (n + 1))
    [inst : ChartedSpace (EuclideanQuadrant (n + 1)) Z] (hch : inst = Q.cornerChartedSpace hcs)
    [∀ b, ChartedSpace (EuclideanQuadrant n) (N b)] [∀ b, IsManifold (𝓠 n) ∞ (N b)] (b : Bool)
    (hcsN : (PN b).HasCornerStructureOfDim n) (hj : IsEmbedding (j b))
    (hjc : IsClosed (range (j b))) (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ (j b))
    (hd : ∀ x, Q.degIndex (j b x) = (PN b).degIndex x + 1)
    (hE1 : ∀ p ∈ range (j b), Q.degIndex p = 1 →
      ∀ᶠ z in 𝓝 p, Q.degIndex z = 1 → z ∈ range (j b))
    (hinv : ∀ p, ∃ (U : Set Z) (g : Z → N b), IsOpen U ∧ j b p ∈ U ∧
      ContMDiffOn (𝓠 (n + 1)) (𝓠 n) ∞ g U ∧ ∀ q, j b q ∈ U → g (j b q) = q) :
    IsAdaptedEnd n j b := by
  intro p
  set κ := (hcs.exists_cornerCoords (j b p)).choose
  have hchart : chartAt (EuclideanQuadrant (n + 1)) (j b p) = κ.toQuadrantChart :=
    chartAt_eq_of_eq hcs hch _
  have hzκ : j b p ∈ κ.s := (hcs.exists_cornerCoords (j b p)).choose_spec
  obtain ⟨i₀, B, hBo, hzB, hBs, hBiff⟩ := exists_endCoordinate hj hjc hcsN hd hE1 κ ⟨p, rfl⟩ hzκ
  obtain ⟨U, g, hUo, hzU, hgs, hgj⟩ := hinv p
  have hcoord : ∀ y ∈ B ∩ U, (y ∈ range (j b) ↔ (κ.toQuadrantChart y).1 i₀ = 0) := by
    intro y hy
    rw [hBiff y hy.1]
    change _ ↔ (κ.toQuadrantChart.extend (𝓠 (n + 1)) y) i₀ = 0
    rw [κ.extend_eq_toLp_coord (hBs hy.1)]
  let D : EndChartData n (j b) :=
    { e := κ.toQuadrantChart
      i := i₀
      B := B ∩ U
      isOpen_B := hBo.inter hUo
      subset_source := fun y hy => hBs hy.1
      mem_range_iff := hcoord
      g := g
      continuousOn_g := hgs.continuousOn.mono inter_subset_right
      g_j := fun q hq => hgj q hq.2 }
  have := isManifold_of_eq hcs hch
  refine ⟨D.toFaceChartPair hjs (mem_maximalAtlas_of_eq hcs hch κ)
    (hgs.mono inter_subset_right), hchart.symm, B ∩ U, hBo.inter hUo, ⟨hzB, hzU⟩, ?_, ?_,
    fun q hq => hq⟩
  · rw [hchart]
    exact fun y hy => hBs hy.1
  · intro y hy
    rw [hchart]
    exact hcoord y hy

end Adapted

end MPolyfold

end Polyfold
