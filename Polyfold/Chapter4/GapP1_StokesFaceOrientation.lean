import Polyfold.Chapter4.ManifoldFaceForms2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199; preprint Theorem 4.28): "whose boundary `∂N`, a union of smooth
faces `F`, is equipped with the induced orientation" (gap G.40, second step).

# The induced orientation of a face

`M` is a manifold modelled on `[0,∞)ⁿ⁺¹`, `N` one modelled on `[0,∞)ⁿ`, and `j : N → M` a map
which in suitable charts is a coordinate face embedding:

* `FaceChartPair n j`: charts `e_N` of `N` and `e` of `M` (maximal atlases) and a coordinate `i`
  with `e(j p) = ιᵢ(e_N p)` on the source of `e_N` (`ιᵢ = faceEmbedding i`, `{xᵢ = 0}`).
  For the faces of `N ⊆ X` these are the face charts of `GapP1_StokesFaceCharts`.
* `FaceChartPair.chartChangeDeriv_face`: the chart change of two face charts of `N` has the
  derivative `faceRestrict A i i'`, `A` the chart change derivative of `M`;
  `FaceChartPair.face_zero`, `FaceChartPair.inward`: `A` maps `{xᵢ = 0}` into `{x_{i'} = 0}` and
  `eᵢ` to an inward vector, **at every point** of `N`, also at the corners of `M`.
* `IsInducedOrientation j o o_N`: in every face chart pair, `o_N` reads as
  `orSign b · faceSign i` times the standard orientation, `b` the sign of `o` in `e` (outward
  vector first, Definition 9.3.8: `(−eᵢ, ιᵢe₁, …, ιᵢeₙ)` has determinant `faceSign i`,
  `det_cons_neg_stdFrame_faceFrame`).  The charts of the boundary integral
  (`chartBoundaryIntegral`) carry exactly these signs.
* **`inducedOrientation`**: if every point of `N` lies in a face chart pair, an induced orientation
  exists (`isInducedOrientation_inducedOrientation`), it is continuous
  (`isContinuous_inducedOrientation`) and unique (`IsInducedOrientation.unique`).
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### Signs -/

section Signs

open Classical in
/-- The sign `faceSign i` as a `Bool` (`orSign (faceBool i) = faceSign i`). -/
def faceBool {n : ℕ} (i : Fin (n + 1)) : Bool := decide (faceSign i = 1)

theorem orSign_faceBool {n : ℕ} (i : Fin (n + 1)) : orSign (faceBool i) = faceSign i := by
  unfold faceBool
  rcases neg_one_pow_eq_or ℝ ((i : ℕ) + 1) with h | h
  · rw [faceSign, h]; simp
  · rw [faceSign, h]; norm_num

theorem orSign_beq (b c : Bool) : orSign (b == c) = orSign b * orSign c := by
  cases b <;> cases c <;> norm_num [orSign]

open Classical in
/-- Every orientation of `ℝᵐ` is `± ` the standard one. -/
theorem eq_signedOr_decide {m : ℕ} (r : Orientation ℝ (EuclideanSpace ℝ (Fin m)) (Fin m)) :
    r = signedOr (decide (r = stdOrientation m)) (stdOrientation m) := by
  by_cases h : r = stdOrientation m
  · simp [h]
  · simp only [h, decide_false, signedOr_false]
    exact (r.eq_or_eq_neg (stdOrientation m) (by simp)).resolve_left h

/-- If `orSign c · orSign c' · det B > 0`, `B` moves `signedOr c ρ` to `signedOr c' ρ`. -/
theorem signMap_signedOr {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {ι : Type*} {B : E →L[ℝ] E} {c c' : Bool} (h : 0 < orSign c * orSign c' * B.det)
    (ρ : Orientation ℝ E ι) : signMap B (signedOr c ρ) = signedOr c' ρ := by
  cases c <;> cases c' <;> simp only [orSign_true, orSign_false, signedOr_true,
    signedOr_false] at h ⊢
  · rw [signMap_neg, signMap_of_pos (by linarith) ρ]
  · rw [signMap_neg, signMap_of_neg (by linarith) ρ]; exact neg_neg ρ
  · rw [signMap_of_neg (by linarith) ρ]
  · rw [signMap_of_pos (by linarith) ρ]

end Signs

/-! ### Face chart pairs -/

section FaceChartPair

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant n) N]

theorem mapsTo_faceEmbedding_range (i : Fin (n + 1)) :
    MapsTo (faceEmbedding i) (range (𝓠 n)) (range (𝓠 (n + 1))) := by
  intro z hz
  rw [range_modelWithCornersEuclideanQuadrant] at hz ⊢
  have h := preimage_faceEmbedding_quadrant (n := n) univ i
  rw [preimage_univ] at h
  rw [← mem_preimage, h]
  exact hz

theorem mapsTo_extendCoordChange_range {m : ℕ} {Q : Type*} [TopologicalSpace Q]
    (e e' : OpenPartialHomeomorph Q (EuclideanQuadrant m)) :
    MapsTo ((𝓠 m).extendCoordChange e e') univ (closedQuadrant univ) := fun z _ => by
  rw [← range_modelWithCornersEuclideanQuadrant]
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
    OpenPartialHomeomorph.extend_coe]
  exact mem_range_self _

variable (n) (j : N → M) in
/-- **A face chart pair** for `j : N → M`: a chart `e_N` of `N` and a chart `e` of `M` (maximal
atlases) and a coordinate `i` such that `j` reads as the face embedding `ιᵢ` (`{xᵢ = 0}`):
`e(j p) = ιᵢ(e_N(p))` on the source of `e_N`. -/
structure FaceChartPair where
  /-- The chart of `N`. -/
  eN : OpenPartialHomeomorph N (EuclideanQuadrant n)
  /-- The chart of `M`. -/
  e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))
  /-- The coordinate of the face. -/
  i : Fin (n + 1)
  mem_N : eN ∈ IsManifold.maximalAtlas (𝓠 n) ∞ N
  mem_M : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M
  mapsTo : ∀ p ∈ eN.source, j p ∈ e.source
  extend_eq : ∀ p ∈ eN.source,
    e.extend (𝓠 (n + 1)) (j p) = faceEmbedding i (eN.extend (𝓠 n) p)

namespace FaceChartPair

variable {j : N → M} (P : FaceChartPair n j)

theorem symm_eq {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (P.eN.extend (𝓠 n)).target) :
    (P.e.extend (𝓠 (n + 1))).symm (faceEmbedding P.i z) = j ((P.eN.extend (𝓠 n)).symm z) := by
  have hp : (P.eN.extend (𝓠 n)).symm z ∈ P.eN.source := by
    rw [← P.eN.extend_source (I := 𝓠 n)]; exact (P.eN.extend (𝓠 n)).map_target hz
  have h := P.extend_eq _ hp
  rw [(P.eN.extend (𝓠 n)).right_inv hz] at h
  rw [← h, P.e.extend_left_inv (P.mapsTo _ hp)]

theorem faceEmbedding_mem_target {p : N} (hp : p ∈ P.eN.source) :
    faceEmbedding P.i (P.eN.extend (𝓠 n) p) ∈ (P.e.extend (𝓠 (n + 1))).target := by
  rw [← P.extend_eq p hp]
  exact (P.e.extend (𝓠 (n + 1))).map_source (by rw [P.e.extend_source]; exact P.mapsTo p hp)

theorem extend_coord_eq_zero {p : N} (hp : p ∈ P.eN.source) :
    P.e.extend (𝓠 (n + 1)) (j p) P.i = 0 := by
  rw [P.extend_eq p hp]; exact faceEmbedding_apply_self _ _

variable (P' : FaceChartPair n j)

omit [ChartedSpace (EuclideanQuadrant n) N] in
theorem _root_.Polyfold.exists_extend_eq_of_mem {m : ℕ} [ChartedSpace (EuclideanQuadrant m) N]
    {e e' : OpenPartialHomeomorph N (EuclideanQuadrant m)} {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ ((𝓠 m).extendCoordChange e e').source) :
    ∃ q ∈ e.source ∩ e'.source, e.extend (𝓠 m) q = z := by
  rw [ModelWithCorners.extendCoordChange_source] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
  refine ⟨e.symm w, ⟨e.map_target hw.1, hw.2⟩, ?_⟩
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, e.right_inv hw.1]

theorem extendCoordChange_apply {q : N} (hq : q ∈ P.eN.source) (hq' : q ∈ P'.eN.source) :
    (𝓠 (n + 1)).extendCoordChange P.e P'.e (faceEmbedding P.i (P.eN.extend (𝓠 n) q)) =
      faceEmbedding P'.i (P'.eN.extend (𝓠 n) q) := by
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
  rw [← P.extend_eq q hq, P.e.extend_left_inv (P.mapsTo q hq), P'.extend_eq q hq']

/-- **The chart change of two face charts is a face transition** near `e_N(p)`:
`e'_N ∘ e_N⁻¹ = π_{i'} ∘ (e' ∘ e⁻¹) ∘ ιᵢ`. -/
theorem extendCoordChange_eventuallyEq {p : N} (hp : p ∈ P.eN.source)
    (hp' : p ∈ P'.eN.source) :
    (𝓠 n).extendCoordChange P.eN P'.eN =ᶠ[𝓝[range (𝓠 n)] (P.eN.extend (𝓠 n) p)]
      fun z => faceProjection P'.i
        ((𝓠 (n + 1)).extendCoordChange P.e P'.e (faceEmbedding P.i z)) := by
  filter_upwards [(𝓠 n).extendCoordChange_source_mem_nhdsWithin' hp hp'] with z hz
  obtain ⟨q, hq, rfl⟩ := exists_extend_eq_of_mem hz
  rw [P.extendCoordChange_apply P' hq.1 hq.2, faceProjection_faceEmbedding]
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
  rw [P.eN.extend_left_inv hq.1]

/-- The values of `e' ∘ e⁻¹ ∘ ιᵢ` near `e_N(p)` lie on the face `{x_{i'} = 0}`. -/
theorem eventually_coord_eq_zero {p : N} (hp : p ∈ P.eN.source) (hp' : p ∈ P'.eN.source) :
    (fun z => (𝓠 (n + 1)).extendCoordChange P.e P'.e (faceEmbedding P.i z) P'.i)
      =ᶠ[𝓝[range (𝓠 n)] (P.eN.extend (𝓠 n) p)] fun _ => 0 := by
  filter_upwards [(𝓠 n).extendCoordChange_source_mem_nhdsWithin' hp hp'] with z hz
  obtain ⟨q, hq, rfl⟩ := exists_extend_eq_of_mem hz
  rw [P.extendCoordChange_apply P' hq.1 hq.2]
  exact faceEmbedding_apply_self _ _

theorem hasFDerivWithinAt_e {p : N} (hp : p ∈ P.eN.source) (hp' : p ∈ P'.eN.source) :
    HasFDerivWithinAt ((𝓠 (n + 1)).extendCoordChange P.e P'.e)
      (chartChangeDeriv (𝓠 (n + 1)) P.e P'.e (j p)) (range (𝓠 (n + 1)))
      (faceEmbedding P.i (P.eN.extend (𝓠 n) p)) := by
  rw [← P.extend_eq p hp]
  exact hasFDerivWithinAt_chartChangeDeriv (by simp) P.mem_M P'.mem_M (P.mapsTo p hp)
    (P'.mapsTo p hp')

/-- **The derivative of the chart change of two face charts** is `faceRestrict A i i'`, `A` the
derivative of the chart change of `M`. -/
theorem chartChangeDeriv_face {p : N} (hp : p ∈ P.eN.source) (hp' : p ∈ P'.eN.source) :
    chartChangeDeriv (𝓠 n) P.eN P'.eN p =
      faceRestrict (chartChangeDeriv (𝓠 (n + 1)) P.e P'.e (j p)) P.i P'.i := by
  have hev := P.extendCoordChange_eventuallyEq P' hp hp'
  have hz : P.eN.extend (𝓠 n) p ∈ range (𝓠 n) := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  have hd := (hasFDerivWithinAt_faceTransition (j := P'.i) (P.hasFDerivWithinAt_e P' hp hp')).mono
    (mapsTo_faceEmbedding_range P.i)
  unfold chartChangeDeriv
  rw [hev.fderivWithin_eq (hev.eq_of_nhdsWithin hz)]
  exact hd.fderivWithin ((𝓠 n).uniqueDiffOn _ hz)

/-- **The chart change of `M` maps the face into the face**: `(A ιᵢ y)_{i'} = 0`, at every point
of `N` (also at the corners of `M`): `e' ∘ e⁻¹ ∘ ιᵢ` has its `i'`-th coordinate `0` near `e_N(p)`
and derivatives within the quadrant are unique. -/
theorem face_zero {p : N} (hp : p ∈ P.eN.source) (hp' : p ∈ P'.eN.source)
    (y : EuclideanSpace ℝ (Fin n)) :
    chartChangeDeriv (𝓠 (n + 1)) P.e P'.e (j p) (faceEmbedding P.i y) P'.i = 0 := by
  have hz : P.eN.extend (𝓠 n) p ∈ range (𝓠 n) := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  have h0 := P.eventually_coord_eq_zero P' hp hp'
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) P'.i).hasFDerivAt.comp_hasFDerivWithinAt _
    ((P.hasFDerivWithinAt_e P' hp hp').comp _ (faceEmbedding P.i).hasFDerivWithinAt
      (mapsTo_faceEmbedding_range P.i))
  have hd0 : HasFDerivWithinAt
      (fun z => (𝓠 (n + 1)).extendCoordChange P.e P'.e (faceEmbedding P.i z) P'.i)
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (range (𝓠 n)) (P.eN.extend (𝓠 n) p) :=
    (hasFDerivWithinAt_const (0 : ℝ) _ _).congr_of_eventuallyEq h0 (h0.eq_of_nhdsWithin hz)
  have := ((𝓠 n).uniqueDiffOn _ hz).eq hd hd0
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L y) this

/-- **The chart change of `M` maps `eᵢ` to an inward vector**: `(A eᵢ)_{i'} > 0`. -/
theorem inward {p : N} (hp : p ∈ P.eN.source) (hp' : p ∈ P'.eN.source) :
    0 < chartChangeDeriv (𝓠 (n + 1)) P.e P'.e (j p) (stdFrame (n + 1) P.i) P'.i := by
  have hQ := range_modelWithCornersEuclideanQuadrant (m := n + 1)
  have hy : faceEmbedding P.i (P.eN.extend (𝓠 n) p) ∈ closedQuadrant univ := by
    rw [← hQ, ← P.extend_eq p hp, OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  have hnn : 0 ≤ chartChangeDeriv (𝓠 (n + 1)) P.e P'.e (j p) (stdFrame (n + 1) P.i) P'.i := by
    refine nonneg_apply_of_hasFDerivWithinAt (P.hasFDerivWithinAt_e P' hp hp')
      ((mapsTo_extendCoordChange_range P.e P'.e).mono_left (subset_univ _)) hy
      (by rw [hQ]; exact self_mem_nhdsWithin) ?_ fun l _ => ?_
    · rw [P.extendCoordChange_apply P' hp hp']; exact faceEmbedding_apply_self _ _
    · rw [stdFrame_apply_apply]; split_ifs <;> norm_num
  refine lt_of_le_of_ne hnn fun h0 => ?_
  -- then `A` maps everything into `{x_{i'} = 0}`
  have hall : ∀ v, chartChangeDeriv (𝓠 (n + 1)) P.e P'.e (j p) v P'.i = 0 := fun v => by
    have hdec : v = v P.i • stdFrame (n + 1) P.i +
        faceEmbedding P.i (faceProjection P.i (v - v P.i • stdFrame (n + 1) P.i)) := by
      rw [faceEmbedding_faceProjection (by simp [stdFrame_apply_apply])]; abel
    rw [hdec, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, ← h0, smul_eq_mul, mul_zero,
      zero_add, P.face_zero P' hp hp']
  have hinv := chartChangeDeriv_comp_self (by simp) P'.mem_M P.mem_M (P'.mapsTo p hp')
    (P.mapsTo p hp)
  have h1 := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (n + 1)) => L (stdFrame (n + 1) P'.i) P'.i) hinv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1
  rw [hall, stdFrame_apply_apply, if_pos rfl] at h1
  exact zero_ne_one h1

end FaceChartPair

end FaceChartPair

/-! ### The induced orientation -/

section Induced

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant n) N] [IsManifold (𝓠 n) ∞ N]
  {j : N → M} (o : TangentOrientation (𝓠 (n + 1)) M (n + 1))

open Classical in
/-- **The sign of the boundary orientation in a face chart** at `p`: `orSign` of it is
`orSign b · faceSign i`, `b` the sign of `o` in the chart `e` at `j p` (outward vector first,
`det_cons_neg_stdFrame_faceFrame`). -/
def FaceChartPair.boundarySign (P : FaceChartPair n j) (p : N) : Bool :=
  decide (orientationIn P.e (j p) (o (j p)) = stdOrientation (n + 1)) == faceBool P.i

variable (j) in
/-- **The induced orientation of `N`** (2021 Theorem 4.4.7, "equipped with the induced
orientation"; Definition 9.3.8, outward vector first): in every face chart pair `(e_N, e, i)` the
orientation `o_N` reads as `orSign b · faceSign i` times the standard orientation of `ℝⁿ`, where
`o` reads as `orSign b` times the standard orientation of `ℝⁿ⁺¹` in `e`. -/
def IsInducedOrientation (oN : TangentOrientation (𝓠 n) N n) : Prop :=
  ∀ P : FaceChartPair n j, ∀ p ∈ P.eN.source,
    orientationIn P.eN p (oN p) = signedOr (P.boundarySign o p) (stdOrientation n)

omit [IsManifold (𝓠 n) ∞ N] in
/-- **The boundary sign is compatible with the chart changes of the faces.** -/
theorem FaceChartPair.signMap_boundarySign (P P' : FaceChartPair n j) {p : N}
    (hp : p ∈ P.eN.source) (hp' : p ∈ P'.eN.source) :
    signMap (chartChangeDeriv (𝓠 n) P.eN P'.eN p)
        (signedOr (P.boundarySign o p) (stdOrientation n)) =
      signedOr (P'.boundarySign o p) (stdOrientation n) := by
  rw [P.chartChangeDeriv_face P' hp hp']
  refine signMap_signedOr ?_ _
  have hdet := orSign_mul_det_chartChangeDeriv_pos (o := o) P.mem_M P'.mem_M (P.mapsTo p hp)
    (P'.mapsTo p hp') (eq_signedOr_decide _) (eq_signedOr_decide _)
  have h1 := orSign_faceSign_mul_det_faceRestrict_pos (fun y => P.face_zero P' hp hp' y)
    (P.inward P' hp hp') hdet
  unfold FaceChartPair.boundarySign
  rw [orSign_beq, orSign_beq, orSign_faceBool, orSign_faceBool]
  exact h1

variable (hcover : ∀ p : N, ∃ P : FaceChartPair n j, p ∈ P.eN.source)

/-- **The induced orientation**, defined at `p` through a chosen face chart pair at `p`. -/
def inducedOrientation : TangentOrientation (𝓠 n) N n := fun p =>
  modelOrToTangent p (signMap (chartChangeDeriv (𝓠 n) (hcover p).choose.eN
    (chartAt (EuclideanQuadrant n) p) p)
    (signedOr ((hcover p).choose.boundarySign o p) (stdOrientation n)))

theorem orientationIn_inducedOrientation (P : FaceChartPair n j) {p : N} (hp : p ∈ P.eN.source) :
    orientationIn P.eN p (inducedOrientation o hcover p) =
      signedOr (P.boundarySign o p) (stdOrientation n) := by
  set P₀ := (hcover p).choose
  have hp₀ : p ∈ P₀.eN.source := (hcover p).choose_spec
  have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓠 n) (n := ∞) p
  have hpc := mem_chart_source (EuclideanQuadrant n) p
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  unfold orientationIn inducedOrientation
  rw [tangentOrToModel_modelOrToTangent,
    signMap_signMap (det_chartChangeDeriv_ne_zero hn P₀.mem_N hc hp₀ hpc)
      (det_chartChangeDeriv_ne_zero hn hc P.mem_N hpc hp),
    chartChangeDeriv_comp hn P₀.mem_N hc P.mem_N hp₀ hpc hp]
  exact P₀.signMap_boundarySign o P hp₀ hp

/-- **The induced orientation exists** when every point of `N` lies in a face chart pair. -/
theorem isInducedOrientation_inducedOrientation :
    IsInducedOrientation j o (inducedOrientation o hcover) :=
  fun P _ hp => orientationIn_inducedOrientation o hcover P hp

/-- **The induced orientation is continuous**: in a face chart pair it reads as
`orSign b · faceSign i`, and `b` is locally constant since `o` is continuous. -/
theorem isContinuous_inducedOrientation (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (hj : Continuous j) : (inducedOrientation o hcover).IsContinuous (𝓠 n) ∞ := by
  refine TangentOrientation.isContinuous_of_forall (by exact_mod_cast le_top) fun p => ?_
  set P₀ := (hcover p).choose
  have hp₀ : p ∈ P₀.eN.source := (hcover p).choose_spec
  refine ⟨P₀.eN, P₀.mem_N, hp₀, ?_⟩
  have hev := ho P₀.e P₀.mem_M (j p) (P₀.mapsTo p hp₀)
  filter_upwards [P₀.eN.open_source.mem_nhds hp₀, hj.continuousAt.preimage_mem_nhds hev]
    with q hq hq'
  rw [orientationIn_inducedOrientation o hcover P₀ hq,
    orientationIn_inducedOrientation o hcover P₀ hp₀]
  unfold FaceChartPair.boundarySign
  rw [show orientationIn P₀.e (j q) (o (j q)) = orientationIn P₀.e (j p) (o (j p)) from hq']

omit [IsManifold (𝓠 (n + 1)) ∞ M] [IsManifold (𝓠 n) ∞ N] in
include hcover in
/-- **The induced orientation is unique.** -/
theorem IsInducedOrientation.unique {oN oN' : TangentOrientation (𝓠 n) N n}
    (h : IsInducedOrientation j o oN) (h' : IsInducedOrientation j o oN') : oN = oN' := by
  funext p
  obtain ⟨P, hp⟩ := hcover p
  have := (h P p hp).trans (h' P p hp).symm
  exact tangentOrToModel_injective p (signMap_injective this)

end Induced

end Polyfold
