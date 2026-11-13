import Polyfold.Chapter9.FaceIntegrand
import Polyfold.Chapter9.MultiChartIntegration

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps G.109, G.110).  Numbers and pages are
the 2021 text's.

# Part I's boundary integral is the integral over the boundary stratum

For a tame `(m+1)`-dimensional sheet `M` of the class of an integration of `m`-forms, oriented
by `o` (Definition 9.3.3), and a `C¹` Mathlib form `η` on `M` with compact support which is the
restriction of `ω`: Part I's boundary integral `∫_{∂M} η` (a partition of unity over signed
corner charts, `faceSign l` times the integrals over the faces `{yₗ = 0}` of the charts) is the
integral `∫_{∂₁M} ω|(∂₁M, o_{∂M})` over the boundary stratum `∂₁M = {d_M = 1}` with the boundary
orientation of Definition 9.3.8, computed in countably many graph charts (`FormEval.msInteg`).

## What is formalized

* `CornerCoords.faceSet_ae_eq`: the open face piece and Part I's face domain `ιₗ⁻¹(κ(U))`
  differ by a null set (the corners).
* `FormEval.face_term_eq`: one term of Part I's boundary integral (one chart, one face) is the
  integral over the open face piece of the weight times the face density.
* `FormEval.integral_density_eq_sum_face`: a weighted integral over a piece of a graph chart of
  the stratum, the weight vanishing off a corner chart `κ`, is the sum over the faces of `κ` of
  the integrals over the face pieces.
* `FormEval.density_eq_zero_of_restrict_eq_zero`: the density vanishes where `η` does.
* **`FormEval.boundaryIntegral_eq_msInteg`**: `∫_{∂M} η = ∫_{∂₁M} ω|(∂₁M, o_{∂M})`, if `∂₁M`
  lies in the class `F.msheets` whenever it is nonempty (when it is empty both sides vanish:
  every face point is a corner, a null set of the face).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold.CornerCoords

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {m : ℕ} (κ : CornerCoords Q (m + 1)) (l : Fin (m + 1))

/-- **The open face piece is Part I's face domain up to a null set** (the points of the face
with another vanishing coordinate). -/
theorem faceSet_ae_eq :
    κ.faceSet l =ᵐ[volume] faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (m + 1))).target := by
  set F1 := faceEmbedding l ⁻¹' ((𝓠 (m + 1)).symm ⁻¹' κ.toQuadrantChart.target)
  set S : Set (Fin m) := l.succAbove ⁻¹' ((Finset.univ : Finset (Fin (m + 1))) : Set _)
  have h1 : κ.faceSet l = F1 ∩ openQuadrant S := by
    ext u
    simp only [faceSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, F1, S, mem_openQuadrant,
      Finset.coe_univ, preimage_univ, mem_univ, forall_const,
      ManifoldForm.extend_target_eq_inter_quadrant]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rw [← mem_preimage, preimage_faceEmbedding_quadrant]
      intro k _
      exact (h2 k).le
  have h2 : faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (m + 1))).target =
      F1 ∩ closedQuadrant S := by
    rw [ManifoldForm.extend_target_eq_inter_quadrant, preimage_inter,
      preimage_faceEmbedding_quadrant]
  rw [h1, h2]
  exact (ae_eq_refl F1).inter openQuadrant_ae_eq_quadrant

end MPolyfold.CornerCoords

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {m : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M} {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}

/-- **A weighted integral over a piece of a graph chart of the boundary stratum, split over the
faces of a corner chart**: for a weight `f` vanishing off the domain of the corner coordinates
`κ` with `f · faceDensity` integrable on every face piece, and a Borel `B`,
`∫_{c(B ∩ ∂₁M ∩ V)} f · density = ∑ₗ ∫_{faceSet l ∩ facePt⁻¹(B ∩ ∂₁M ∩ V)} f · faceDensity`. -/
theorem FormEval.integral_density_eq_sum_face (F : X.FormEval m Ω)
    (hM : X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : X.PObj.HasTameInducedStructure M)
    {V : Set Obj} (hV : IsOpen V) (c : X.PObj.GraphChart m (X.PObj.boundaryStratum M ∩ V))
    (o' : X.PObj.SubmanifoldOrientation (X.PObj.boundaryStratum M ∩ V) m) (ω : Ω)
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (f : Obj → ℝ)
    (hf0 : ∀ y : M, y ∉ κ.s → f y.1 = 0) {B : Set Obj} (hB : MeasurableSet[borel Obj] B)
    (hint : ∀ l, IntegrableOn (fun u => f (κ.facePt l u).1 *
      F.faceDensity hcs o'.frames ω κ l (κ.facePt l u)) (κ.faceSet l)) :
    IntegrableOn (fun v => f (c.q v) * F.density c ω o'.tangent (c.q v))
        (c.coord '' (B ∩ (X.PObj.boundaryStratum M ∩ V))) ∧
      (∫ v in c.coord '' (B ∩ (X.PObj.boundaryStratum M ∩ V)),
          f (c.q v) * F.density c ω o'.tangent (c.q v)) =
        ∑ l, ∫ u in κ.faceSet l ∩ (fun u => (κ.facePt l u).1) ⁻¹'
            (B ∩ (X.PObj.boundaryStratum M ∩ V)),
          f (κ.facePt l u).1 * F.faceDensity hcs o'.frames ω κ l (κ.facePt l u) := by
  set S := B ∩ (X.PObj.boundaryStratum M ∩ V) with hS
  have hSb : MeasurableSet[borel Obj] S :=
    @MeasurableSet.inter Obj (borel Obj) _ _ hB (@MeasurableSet.inter Obj (borel Obj) _ _
      (isSubmanifoldOfDim_boundaryStratum hM ht).1.measurableSet_borel
      (MeasurableSpace.measurableSet_generateFrom hV))
  set A : Fin (m + 1) → Set (EuclideanSpace ℝ (Fin m)) :=
    fun l => κ.faceSet l ∩ (fun u => (κ.facePt l u).1) ⁻¹' S with hA
  have hAm : ∀ l, MeasurableSet (A l) := fun l => measurableSet_faceSet_inter_preimage κ l hSb
  have hc := fun l => F.face_change (hcs := hcs) hM ht hV c o' ω κ l f
    (A := A l) inter_subset_left (hAm l) fun u hu => hu.2.2.2
  set Qs : Fin (m + 1) → Set (EuclideanSpace ℝ (Fin m)) :=
    fun l => c.coord '' ((fun u => (κ.facePt l u).1) '' A l) with hQs
  have hQsub : (⋃ l, Qs l) ⊆ c.coord '' S := iUnion_subset fun l =>
    image_mono (image_subset_iff.2 fun u hu => hu.2)
  have hdisj : Pairwise (Function.onFun Disjoint Qs) := by
    intro l l' hll'
    refine disjoint_left.2 ?_
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ ⟨_, ⟨u', hu', rfl⟩, h⟩
    have h1 := c.injOn_coord hu'.2.2 hu.2.2 h
    exact hll' (CornerCoords.eq_of_facePt_eq hu.1 hu'.1 (Subtype.ext h1.symm))
  have hmeas : MeasurableSet (c.coord '' S) := c.measurableSet_coord_image_borel hB
  have hzero : ∀ v ∈ c.coord '' S \ ⋃ l, Qs l,
      f (c.q v) * F.density c ω o'.tangent (c.q v) = 0 := by
    rintro _ ⟨⟨y, hy, rfl⟩, hnot⟩
    rw [c.q_coord' hy.2]
    have hyM : y ∈ M := hy.2.1.1
    by_cases hyκ : (⟨y, hyM⟩ : M) ∈ κ.s
    · obtain ⟨l, u, hu, heq⟩ :=
        exists_facePt_of_mem_boundaryStratum hM.1 ht κ hyκ hy.2.1
      have hS' : (κ.facePt l u).1 ∈ S := by rw [heq]; exact hy
      have hmem : c.coord y ∈ Qs l := ⟨y, ⟨u, ⟨hu, hS'⟩, congrArg Subtype.val heq⟩, rfl⟩
      exact absurd (mem_iUnion.2 ⟨l, hmem⟩) hnot
    · rw [hf0 ⟨y, hyM⟩ hyκ, zero_mul]
  have hintQ : ∀ l, IntegrableOn (fun v => f (c.q v) * F.density c ω o'.tangent (c.q v)) (Qs l) :=
    fun l => (hc l).2.2.1 ((hint l).mono_set inter_subset_left)
  refine ⟨IntegrableOn.of_forall_sdiff_eq_zero (integrableOn_finite_iUnion.2 hintQ) hmeas hzero,
    ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hQsub hzero,
    integral_iUnion_fintype (fun l => (hc l).1) hdisj hintQ]
  exact Finset.sum_congr rfl fun l _ => (hc l).2.1

variable [inst : ChartedSpace (EuclideanQuadrant (m + 1)) M]

/-- **The density vanishes where the restriction `η` of `ω` vanishes.** -/
theorem FormEval.density_eq_zero_of_restrict_eq_zero (F : X.FormEval m Ω)
    (hM : X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : X.PObj.HasTameInducedStructure M)
    {V : Set Obj} (hV : IsOpen V) (c : X.PObj.GraphChart m (X.PObj.boundaryStratum M ∩ V))
    (o' : X.PObj.SubmanifoldOrientation (X.PObj.boundaryStratum M ∩ V) m) (ω : Ω)
    (η : ManifoldForm (𝓠 (m + 1)) M m)
    (hη : ∀ (y : M) (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    {y : M} (hyN : y.1 ∈ X.PObj.boundaryStratum M ∩ V) (h0 : η y = 0) :
    F.density c ω o'.tangent y.1 = 0 := by
  have hy : y ∈ (hcs.coords y).s := hcs.mem_coords y
  obtain ⟨l, u, hu, heq⟩ := exists_facePt_of_mem_boundaryStratum hM.1 ht (hcs.coords y) hy hyN.1
  have hpiece : y ∈ (hcs.coords y).facePiece l := by
    have := CornerCoords.facePt_mem_facePiece hu; rwa [heq] at this
  have hyl : (hcs.coords y).coord y l = 0 := by
    have := CornerCoords.coord_facePt_self hu; rwa [heq] at this
  have hN : X.PObj.IsSubmanifoldOfDim (X.PObj.boundaryStratum M ∩ V) m :=
    (isSubmanifoldOfDim_boundaryStratum hM ht).inter_isOpen hV
  have hβ : ∀ k, faceFrame hcs (hcs.coords y) hy l k ∈
      X.PObj.submanifoldTangent (X.PObj.boundaryStratum M ∩ V) y.1 := fun k => by
    rw [submanifoldTangent_inter_isOpen hV hyN.2]
    exact faceFrame_mem_tangent hM ht (hcs.coords y) hpiece hyl k
  have hli := linearIndependent_chartVec_faceFrame (hcs := hcs) hM.1 (hcs.coords y) hy l
    c.isChart (c.subset_source hyN)
  have hev : F.ev ω (faceFrame hcs (hcs.coords y) hy l) = 0 := by
    have e := hη y fun k => faceEmbedding l (stdFrame m k)
    rw [h0] at e
    exact e.symm.trans rfl
  exact F.density_eq_zero_of_frame hN c o' ω hyN _ hβ hli hev

variable (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **One term of Part I's boundary integral** (one chart, one face): for a weight `ρ` supported
in a region `R` in which `bridgeOrientation o` reads in `κ` as `signedOr b` of the standard
orientation, `orSign b · faceSign l · ∫_{ιₗ⁻¹(κ(U))} ιₗ^*(κ⁻¹)^*(ρ η)` is the integral over the
open face piece of `ρ` times the face density for `o_{∂M}`, which is integrable there. -/
theorem FormEval.face_term_eq (F : X.FormEval m Ω) (hM : X.PObj.IsSubmanifoldOfDim M (m + 1))
    (ht : X.PObj.HasTameInducedStructure M) (o : X.PObj.SubmanifoldOrientation M (m + 1))
    (ω : Ω) (η : ManifoldForm (𝓠 (m + 1)) M m)
    (hη : ∀ (y : M) (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1)) (ρ : M → ℝ) (ρ' : Obj → ℝ)
    (hρ' : ∀ y : M, ρ' y.1 = ρ y) {R : Set M} (b : Bool)
    (hb : ∀ y ∈ R, orientationIn κ.toQuadrantChart y (bridgeOrientation hcs o y) =
      signedOr b (stdOrientation (m + 1)))
    (hρR : tsupport ρ ⊆ R)
    (hint : IntegrableOn (fun u => facePullback l (ManifoldForm.chartForm (𝓠 (m + 1))
      κ.toQuadrantChart (ManifoldForm.smulFun ρ η)) u (stdFrame m))
      (faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (m + 1))).target)) :
    IntegrableOn (fun u => ρ' (κ.facePt l u).1 *
        F.faceDensity hcs (o.stratumOrientation hM ht).frames ω κ l (κ.facePt l u))
        (κ.faceSet l) ∧
      orSign b * (faceSign l * topFormIntegral
        (faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (m + 1))).target)
        (facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart
          (ManifoldForm.smulFun ρ η)))) =
        ∫ u in κ.faceSet l, ρ' (κ.facePt l u).1 *
          F.faceDensity hcs (o.stratumOrientation hM ht).frames ω κ l (κ.facePt l u) := by
  have hpt : EqOn (fun u => orSign b * faceSign l * facePullback l (ManifoldForm.chartForm
      (𝓠 (m + 1)) κ.toQuadrantChart (ManifoldForm.smulFun ρ η)) u (stdFrame m))
      (fun u => ρ' (κ.facePt l u).1 *
        F.faceDensity hcs (o.stratumOrientation hM ht).frames ω κ l (κ.facePt l u))
      (κ.faceSet l) := by
    intro u hu
    have e1 : facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart
        (ManifoldForm.smulFun ρ η)) u (stdFrame m) = ρ (κ.facePt l u) *
        facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart η) u
          (stdFrame m) := by
      simp only [facePullback, formPullback_apply, ManifoldForm.chartForm_smulFun]
      rfl
    simp only
    rw [e1, hρ']
    by_cases hr : κ.facePt l u ∈ R
    · rw [← F.orSign_mul_faceSign_mul_facePullback_eq hch hM ht o ω η hη κ l hu b (hb _ hr)]
      ring
    · have h0 : ρ (κ.facePt l u) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hr (hρR h)
      have h1 := F.orSign_mul_faceSign_mul_facePullback_eq hch hM ht o ω η hη κ l hu b
      rw [h0]
      simp
  have hSm : MeasurableSet (κ.faceSet l) := (κ.isOpen_faceSet l).measurableSet
  have hS : κ.faceSet l ⊆ faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (m + 1))).target :=
    fun u hu => hu.1
  refine ⟨IntegrableOn.congr_fun ((hint.mono_set hS).const_mul (orSign b * faceSign l)) hpt hSm,
    ?_⟩
  rw [topFormIntegral_def, ← setIntegral_congr_set (κ.faceSet_ae_eq l), ← mul_assoc,
    ← integral_const_mul]
  exact setIntegral_congr_fun hSm hpt

end EpGroupoid

end Polyfold
