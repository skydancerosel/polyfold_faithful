import Polyfold.Chapter9.GapP2_E8F_FaceFrame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps G.109, G.110).  Numbers and pages are
the 2021 text's.

# The open faces of a corner chart parametrize the boundary stratum

For corner coordinates `κ` of a tame `(m+1)`-dimensional sheet `M` and a face index `l`, the
open face piece `faceSet κ l = {u ∈ ℝᵐ | ιₗ u ∈ κ(dom κ), all uₖ > 0}` (`ιₗ = faceEmbedding l`)
is mapped by `facePt κ l = κ⁻¹ ∘ ιₗ` onto the points of `dom κ` with `d_M = 1` and `yₗ = 0`.

## What is formalized

* `CornerCoords.faceSet`, `CornerCoords.facePt`; `facePt_mem_facePiece`, `coord_facePt_self`,
  `degIndex_facePt` (`d = 1`), `facePt_injOn`, `eq_of_facePt_eq` (the pieces of different faces
  are disjoint), `exists_facePt` (every point of `dom κ` with `d = 1` is on some piece),
  `isOpen_faceSet`, `continuousOn_facePt`, `measurableSet_faceSet_inter_preimage`.
* `hasFDerivWithinAt_coord_facePt`: a graph chart of the stratum composed with `facePt` is
  differentiable within the face piece, with derivative `c.p ∘ Dι ∘ ιₗ`.
* **`FormEval.face_change`**: the change of variables between a graph chart `c` of a piece
  `∂₁M ∩ V` of the boundary stratum and a face piece, with a weight `f`:
  `∫_{c(facePt(A))} f · density = ∫_A f(facePt u) · faceDensity(facePt u) du`, integrability
  passing both ways.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold WithLp

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

namespace CornerCoords

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {m : ℕ} (κ : CornerCoords Q (m + 1)) (l : Fin (m + 1))

/-- **The open face piece** of the face `{yₗ = 0}` in the coordinates `κ`: the parameters
`u ∈ ℝᵐ` with all coordinates positive whose image `ιₗ u` lies in the chart image. -/
def faceSet : Set (EuclideanSpace ℝ (Fin m)) :=
  {u | faceEmbedding l u ∈ (κ.toQuadrantChart.extend (𝓠 (m + 1))).target ∧ ∀ k, 0 < u k}

/-- **The point `κ⁻¹(ιₗ u)`** of the face `{yₗ = 0}`. -/
def facePt (u : EuclideanSpace ℝ (Fin m)) : Z :=
  (κ.toQuadrantChart.extend (𝓠 (m + 1))).symm (faceEmbedding l u)

variable {κ l}

theorem facePt_mem_s {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    κ.facePt l u ∈ κ.s := by
  have := (κ.toQuadrantChart.extend (𝓠 (m + 1))).map_target hu.1
  rwa [κ.toQuadrantChart.extend_source] at this

theorem extend_facePt {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    κ.toQuadrantChart.extend (𝓠 (m + 1)) (κ.facePt l u) = faceEmbedding l u :=
  (κ.toQuadrantChart.extend (𝓠 (m + 1))).right_inv hu.1

theorem extend_eq_toLp {y : Z} (hy : y ∈ κ.s) :
    κ.toQuadrantChart.extend (𝓠 (m + 1)) y = toLp 2 (κ.coord y) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, κ.toQuadrantChart_apply]
  exact quadrant_right_inv fun i => κ.coord_nonneg hy i

theorem coord_facePt {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) (j : Fin (m + 1)) :
    κ.coord (κ.facePt l u) j = faceEmbedding l u j := by
  have h := extend_facePt hu
  rw [extend_eq_toLp (facePt_mem_s hu)] at h
  rw [← h]

theorem coord_facePt_self {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    κ.coord (κ.facePt l u) l = 0 := by
  rw [coord_facePt hu]; simp

theorem coord_facePt_succAbove {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l)
    (k : Fin m) : κ.coord (κ.facePt l u) (l.succAbove k) = u k := by
  rw [coord_facePt hu]; simp

/-- The points of a face piece have degeneracy index `1`. -/
theorem degIndex_facePt {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    Q.degIndex (κ.facePt l u) = 1 :=
  κ.degIndex_eq_one (facePt_mem_s hu) (coord_facePt_self hu) fun j hj => by
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [coord_facePt_succAbove hu]
    exact (hu.2 k).ne'

theorem facePt_mem_facePiece {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    κ.facePt l u ∈ κ.facePiece l :=
  κ.mem_facePiece_of_degIndex_eq_one (facePt_mem_s hu) (degIndex_facePt hu)
    (coord_facePt_self hu)

theorem facePt_injOn : InjOn (κ.facePt l) (κ.faceSet l) := fun u hu u' hu' h =>
  MPolyfold.faceEmbedding_injective l ((extend_facePt hu).symm.trans
    (by rw [h, extend_facePt hu']))

/-- **The pieces of two faces are disjoint.** -/
theorem eq_of_facePt_eq {l' : Fin (m + 1)} {u u' : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ κ.faceSet l) (hu' : u' ∈ κ.faceSet l') (h : κ.facePt l u = κ.facePt l' u') :
    l = l' := by
  by_contra hne
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  have h1 := coord_facePt_self hu
  rw [h, ← hk, coord_facePt_succAbove hu'] at h1
  exact (hu'.2 k).ne' h1

/-- **Every point of `dom κ` with `d = 1` lies on a face piece.** -/
theorem exists_facePt {y : Z} (hy : y ∈ κ.s) (hd : Q.degIndex y = 1) :
    ∃ l : Fin (m + 1), ∃ u ∈ κ.faceSet l, κ.facePt l u = y := by
  have hcard : (Finset.univ.filter fun j => κ.coord y j = 0).card = 1 := by
    rw [← κ.degIndex_eq_card hy]; exact hd
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hcard
  have hmem : ∀ j, κ.coord y j = 0 ↔ j = l := fun j => by
    have : j ∈ Finset.univ.filter (fun j => κ.coord y j = 0) ↔ j ∈ ({l} : Finset _) := by
      rw [hl]
    simpa using this
  set x := κ.toQuadrantChart.extend (𝓠 (m + 1)) y with hx
  have hxt : x ∈ (κ.toQuadrantChart.extend (𝓠 (m + 1))).target :=
    (κ.toQuadrantChart.extend (𝓠 (m + 1))).map_source (by
      rw [κ.toQuadrantChart.extend_source]; exact hy)
  have hxj : ∀ j, x j = κ.coord y j := fun j => by rw [hx, extend_eq_toLp hy]
  have hxl : x l = 0 := by rw [hxj]; exact (hmem l).2 rfl
  refine ⟨l, toLp 2 (l.removeNth (ofLp x)), ⟨?_, fun k => ?_⟩, ?_⟩
  · rw [faceEmbedding_removeNth hxl]; exact hxt
  · change 0 < x (l.succAbove k)
    rw [hxj]
    exact lt_of_le_of_ne (κ.coord_nonneg hy _) fun h0 =>
      Fin.succAbove_ne l k ((hmem _).1 h0.symm)
  · unfold facePt
    rw [faceEmbedding_removeNth hxl, hx]
    exact (κ.toQuadrantChart.extend (𝓠 (m + 1))).left_inv (by
      rw [κ.toQuadrantChart.extend_source]; exact hy)

variable (κ l)

theorem isOpen_faceSet : IsOpen (κ.faceSet l) := by
  have e : κ.faceSet l = faceEmbedding l ⁻¹' ((𝓠 (m + 1)).symm ⁻¹' κ.toQuadrantChart.target) ∩
      {u | ∀ k, 0 < u k} := by
    ext u
    simp only [faceSet, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.extend_target]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ⟨⟨faceEmbedding l u, fun j => ?_⟩, rfl⟩⟩, h2⟩
      rcases Fin.eq_self_or_eq_succAbove l j with rfl | ⟨k, rfl⟩
      · simp
      · simp only [faceEmbedding_apply_succAbove]; exact (h2 k).le
  rw [e]
  refine ((κ.toQuadrantChart.open_target.preimage (𝓠 (m + 1)).continuous_symm).preimage
    (faceEmbedding l).continuous).inter ?_
  have : {u : EuclideanSpace ℝ (Fin m) | ∀ k, 0 < u k} = ⋂ k, {u | 0 < u k} := by
    ext u; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt continuous_const (PiLp.continuous_apply 2 _ k)

theorem continuousOn_facePt : ContinuousOn (κ.facePt l) (κ.faceSet l) :=
  (κ.toQuadrantChart.continuousOn_extend_symm (I := 𝓠 (m + 1))).comp
    (faceEmbedding l).continuous.continuousOn fun _ hu => hu.1

end CornerCoords

/-! ### The face pieces of a tame sheet -/

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} [ParacompactSpace M] {m : ℕ} {hY : P.IsSubMPolyfold M}

/-- The points of a face piece lie in the boundary stratum. -/
theorem facePt_mem_boundaryStratum (hM : P.IsSmoothSubmanifold M)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) (m + 1))
    {l : Fin (m + 1)} {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    (κ.facePt l u).1 ∈ P.boundaryStratum M := by
  rw [← stratumOne_eq_boundaryStratum hM ht]
  exact (val_mem_stratumOne_iff hM _).2 (CornerCoords.degIndex_facePt hu)

/-- A point of the boundary stratum in `dom κ` lies on a face piece. -/
theorem exists_facePt_of_mem_boundaryStratum (hM : P.IsSmoothSubmanifold M)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) (m + 1)) {y : M}
    (hy : y ∈ κ.s) (hyb : y.1 ∈ P.boundaryStratum M) :
    ∃ l : Fin (m + 1), ∃ u ∈ κ.faceSet l, κ.facePt l u = y := by
  rw [← stratumOne_eq_boundaryStratum hM ht] at hyb
  exact κ.exists_facePt hy ((val_mem_stratumOne_iff hM y).1 hyb)

/-- The trace on a face piece of the preimage of a Borel set is measurable. -/
theorem measurableSet_faceSet_inter_preimage (κ : CornerCoords (subPolyfold hY) (m + 1))
    (l : Fin (m + 1)) {B : Set X} (hB : MeasurableSet[borel X] B) :
    MeasurableSet (κ.faceSet l ∩ (fun u => (κ.facePt l u).1) ⁻¹' B) := by
  classical
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have hc : ContinuousOn (fun u => (κ.facePt l u).1) (κ.faceSet l) :=
    continuous_subtype_val.comp_continuousOn (κ.continuousOn_facePt l)
  have hS := (κ.isOpen_faceSet l).measurableSet
  have hm := hc.measurable_piecewise
    (continuous_const (y := (κ.facePt l 0).1)).continuousOn hS
  have e : κ.faceSet l ∩ (fun u => (κ.facePt l u).1) ⁻¹' B =
      κ.faceSet l ∩ ((κ.faceSet l).piecewise (fun u => (κ.facePt l u).1)
        fun _ => (κ.facePt l 0).1) ⁻¹' B := by
    ext u
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hu, h⟩; exact ⟨hu, by rwa [piecewise_eq_of_mem _ _ _ hu]⟩
    · rintro ⟨hu, h⟩; exact ⟨hu, by rwa [piecewise_eq_of_mem _ _ _ hu] at h⟩
  rw [e]
  exact hS.inter (hm hB)

variable {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}

include hcs in
/-- **A graph chart composed with the face parametrization is differentiable**, with derivative
`c.p ∘ Dι ∘ ιₗ`. -/
theorem hasFDerivWithinAt_coord_facePt {N : Set X} (c : P.GraphChart m N)
    (hM : P.IsSmoothSubmanifold M) (κ : CornerCoords (subPolyfold hY) (m + 1))
    (l : Fin (m + 1)) {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l)
    (hyφ : (κ.facePt l u).1 ∈ c.φ.source) :
    HasFDerivWithinAt (fun u => c.coord (κ.facePt l u).1)
      (c.p.comp ((modelDeriv κ c.isChart (hM.data (κ.facePt l u).2).toSubData (κ.facePt l u)
        (levelLift κ.χ 1 (κ.facePt l u))).comp (faceEmbedding l))) (κ.faceSet l) u := by
  set y := κ.facePt l u with hydef
  have hy : y ∈ κ.s := CornerCoords.facePt_mem_s hu
  set d := (hM.data y.2).toSubData
  have hyσ : y ∈ (subChart d c.isChart y).source :=
    d.mem_shrink c.φ y.2 (hM.mem_data_V y.2) hyφ
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hy) (levelVal_mem (hcs.levelOne y))
  have h1 := hasFDerivWithinAt_incl κ c.isChart d y hy hyσ hz
  rw [CornerCoords.extend_facePt hu] at h1
  have hmaps : MapsTo (faceEmbedding l) (κ.faceSet l) (range (𝓠 (m + 1))) := fun v hv =>
    κ.toQuadrantChart.extend_target_subset_range (I := 𝓠 (m + 1)) hv.1
  have h2 := h1.comp u (faceEmbedding l).hasFDerivAt.hasFDerivWithinAt hmaps
  exact c.p.hasFDerivAt.comp_hasFDerivWithinAt u h2

end MPolyfold

/-! ### The change of variables -/

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {m : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M} {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}

/-- **Change of variables between a graph chart of the boundary stratum and a face piece**:
for a graph chart `c` of `∂₁M ∩ V`, an orientation `o'` of `∂₁M ∩ V`, a weight `f` and a
measurable `A` in the face piece of `{yₗ = 0}` mapped into `V`,
`∫_{c(facePt A)} f · density = ∫_A f(facePt u) · faceDensity(facePt u) du`, and integrability
passes both ways. -/
theorem FormEval.face_change (F : X.FormEval m Ω) (hM : X.PObj.IsSubmanifoldOfDim M (m + 1))
    (ht : X.PObj.HasTameInducedStructure M) {V : Set Obj} (hV : IsOpen V)
    (c : X.PObj.GraphChart m (X.PObj.boundaryStratum M ∩ V))
    (o' : X.PObj.SubmanifoldOrientation (X.PObj.boundaryStratum M ∩ V) m) (ω : Ω)
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1)) (f : Obj → ℝ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ⊆ κ.faceSet l) (hAm : MeasurableSet A)
    (hAV : ∀ u ∈ A, (κ.facePt l u).1 ∈ V) :
    MeasurableSet (c.coord '' ((fun u => (κ.facePt l u).1) '' A)) ∧
    (∫ v in c.coord '' ((fun u => (κ.facePt l u).1) '' A),
        f (c.q v) * F.density c ω o'.tangent (c.q v)) =
      (∫ u in A, f (κ.facePt l u).1 * F.faceDensity hcs o'.frames ω κ l (κ.facePt l u)) ∧
    (IntegrableOn (fun u => f (κ.facePt l u).1 * F.faceDensity hcs o'.frames ω κ l
        (κ.facePt l u)) A ↔
      IntegrableOn (fun v => f (c.q v) * F.density c ω o'.tangent (c.q v))
        (c.coord '' ((fun u => (κ.facePt l u).1) '' A))) := by
  have hN : X.PObj.IsSubmanifoldOfDim (X.PObj.boundaryStratum M ∩ V) m :=
    (isSubmanifoldOfDim_boundaryStratum hM ht).inter_isOpen hV
  have hyN : ∀ u ∈ A, (κ.facePt l u).1 ∈ X.PObj.boundaryStratum M ∩ V := fun u hu =>
    ⟨facePt_mem_boundaryStratum hM.1 ht κ (hA hu), hAV u hu⟩
  set τ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun u => c.coord (κ.facePt l u).1 with hτ
  let DN : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    fun u => c.p.comp ((modelDeriv κ c.isChart (hM.1.data (κ.facePt l u).2).toSubData
      (κ.facePt l u) (levelLift κ.χ 1 (κ.facePt l u))).comp (faceEmbedding l))
  have hderiv : ∀ u ∈ A, HasFDerivWithinAt τ (DN u) A u := fun u hu =>
    (hasFDerivWithinAt_coord_facePt (hcs := hcs) c hM.1 κ l (hA hu)
      (c.subset_source (hyN u hu))).mono hA
  have hinj : InjOn τ A := by
    intro u hu u' hu' h
    have h1 := c.injOn_coord (hyN u hu) (hyN u' hu') h
    exact CornerCoords.facePt_injOn (hA hu) (hA hu') (Subtype.ext h1)
  have himg : τ '' A = c.coord '' ((fun u => (κ.facePt l u).1) '' A) := by
    rw [image_image]
  have hpt : EqOn (fun u => |(DN u).det| • (f (c.q (τ u)) * F.density c ω o'.tangent (c.q (τ u))))
      (fun u => f (κ.facePt l u).1 * F.faceDensity hcs o'.frames ω κ l (κ.facePt l u)) A := by
    intro u hu
    have hu' := hA hu
    set y := κ.facePt l u with hydef
    have hy : y ∈ κ.s := CornerCoords.facePt_mem_s hu'
    have hpiece : y ∈ κ.facePiece l := CornerCoords.facePt_mem_facePiece hu'
    have hyl : κ.coord y l = 0 := CornerCoords.coord_facePt_self hu'
    have hyV : y.1 ∈ V := hAV u hu
    simp only [hτ, smul_eq_mul]
    rw [c.q_coord' (hyN u hu), FormEval.faceDensity, dif_pos hy]
    have hβ : ∀ k, faceFrame hcs κ hy l k ∈
        X.PObj.submanifoldTangent (X.PObj.boundaryStratum M ∩ V) y.1 := fun k => by
      rw [submanifoldTangent_inter_isOpen hV hyV]
      exact faceFrame_mem_tangent hM ht κ hpiece hyl k
    have hli := linearIndependent_chartVec_faceFrame (hcs := hcs) hM.1 κ hy l c.isChart
      (c.subset_source (hyN u hu))
    rw [F.sgn_mul_ev_of_frame hN c o' ω (hyN u hu) _ hβ hli]
    have hσ : y ∈ (subChart (hM.1.data y.2).toSubData c.isChart y).source :=
      (hM.1.data y.2).toSubData.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2)
        (c.subset_source (hyN u hu))
    have hdet : (Matrix.of fun i j =>
        c.p (chartVec c.isChart (faceFrame hcs κ hy l j)) i).det = (DN u).det := by
      rw [← GraphChart.det_matrix_bvec (DN u)]
      congr 1
      ext i j
      simp only [Matrix.of_apply, DN, ContinuousLinearMap.comp_apply]
      unfold faceFrame
      rw [chartVec_incFrame (hcs := hcs) κ hy _ c.isChart _ y hσ]
      have hb : stdFrame m j = GraphChart.bvec j := by simp [stdFrame_apply, GraphChart.bvec]
      rw [hb]
    rw [hdet]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← himg]; exact measurable_image_of_fderivWithin hAm hderiv hinj
  · rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hAm hderiv hinj]
    exact setIntegral_congr_fun hAm hpt
  · rw [← himg, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hAm hderiv hinj]
    exact (integrableOn_congr_fun hpt hAm).symm

end EpGroupoid

end Polyfold
