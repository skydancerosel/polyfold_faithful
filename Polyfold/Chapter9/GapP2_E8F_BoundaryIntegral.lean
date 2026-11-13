import Polyfold.Chapter9.GapP2_E8F_FaceSum
import Polyfold.Chapter9.GapP2_E5_StokesSheet
import Polyfold.Chapter9.GapP2_E6_BoundarySheets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, proof of Theorem 9.5.18 (pp. 450–451; gap G.110), with Definition 9.3.8
(boundary orientation, p. 426) and Part I, Theorem 4.4.7 (p. 199).  Numbers and pages are the
2021 text's.

# Part I's boundary integral over a sheet is the integral of §9.5 over its boundary stratum

The last equality of the display on p. 451 identifies the classical boundary integral
`∫_{∂(Mᵢ, oᵢ)} ω` (Part I: a partition of unity over signed corner charts, the faces
`{yₗ = 0}` with the signs `faceSign l`) with the integral `∫_{∂₁Mᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` of §9.5
over the boundary stratum with the boundary orientation of Definition 9.3.8.

## What is formalized

* `FormEval.boundaryIntegral_eq_msInteg`: for a tame `(m+1)`-dimensional sheet `M` oriented by
  `o`, and a `C¹` Mathlib `m`-form `η` on `M` with compact support which is the restriction of
  `ω` (its values are those of `ω` on the frames `Tι(v)`),
  `∫_{∂M} η = ∫_{∂₁M} ω|(∂₁M, o_{∂M})`, when `∂₁M` lies in the class `F.msheets` (countably many
  graph charts) whenever it is nonempty.
* **`EP.boundaryIntegral_eq_msInteg`**: the same for the sheets `Mᵢ` of an oriented tame
  structure and a class `a ∈ Ωᵐ_{ep,∞}(X)` vanishing on `Mᵢ` off a closed `K` with `Mᵢ ∩ K`
  compact: `∫_{∂(Mᵢ,oᵢ)} a = ∫_{∂₁Mᵢ} a|(∂₁Mᵢ, o_{∂Mᵢ})`.

The hypothesis `hb` (the boundary sheet lies in the class `msheets` of sheets covered by
countably many graph charts with `∫ |ω| < ∞`) is the standing hypothesis under which the integral
of §9.5 over `∂₁Mᵢ` is defined by charts; when `∂₁Mᵢ = ∅` both sides vanish.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {m : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M} {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}
  [inst : ChartedSpace (EuclideanQuadrant (m + 1)) M]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **Part I's boundary integral is the integral over the boundary stratum** (proof of
Theorem 9.5.18, 2021 p. 451, last equality of the display; Definition 9.3.8, p. 426): for a tame
`(m+1)`-dimensional sheet `M` oriented by `o` (Definition 9.3.3) and a `C¹` Mathlib `m`-form `η`
on `M` with compact support whose values are those of `ω` on the frames `Tι(v)`,
`∫_{∂(M, bridgeOrientation o)} η = ∫_{∂₁M} ω|(∂₁M, o_{∂M})`, provided `∂₁M` lies in the class
`F.msheets` when it is nonempty. -/
theorem FormEval.boundaryIntegral_eq_msInteg [IsManifold (𝓠 (m + 1)) ∞ M] [T2Space M]
    [SigmaCompactSpace M] (F : X.FormEval m Ω) (hm : 0 < m)
    (hM : X.PObj.IsSubmanifoldOfDim M (m + 1)) (ht : X.PObj.HasTameInducedStructure M)
    (o : X.PObj.SubmanifoldOrientation M (m + 1)) (ω : Ω) (η : ManifoldForm (𝓠 (m + 1)) M m)
    (hη1 : ManifoldForm.ContMDiffForm (𝓠 (m + 1)) 1 η)
    (hc : IsCompact (ManifoldForm.tsupport η))
    (hη : ∀ (y : M) (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    (hb : (X.PObj.boundaryStratum M).Nonempty → X.PObj.boundaryStratum M ∈ F.msheets) :
    ManifoldForm.boundaryIntegral (bridgeOrientation hcs o) η =
      F.msInteg ω (X.PObj.boundaryStratum M) (o.stratumOrientation hM ht).tangent
        (X.PObj.boundaryStratum M) := by
  classical
  have ho := isContinuous_bridgeOrientation hch (Nat.succ_pos m) hM o
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [ManifoldForm.boundaryIntegral_eq_integrationData ho hη1 hc D subset_rfl]
  set bS := X.PObj.boundaryStratum M with hbS
  set o' := o.stratumOrientation hM ht with ho'
  let ρ' : {x // x ∈ T} → Obj → ℝ := fun j x => if h : x ∈ M then D.ρ j ⟨x, h⟩ else 0
  have hρ' : ∀ j (y : M), ρ' j y.1 = D.ρ j y := fun j y => by
    simp only [ρ', dif_pos y.2]
  let κ : {x // x ∈ T} → CornerCoords (subPolyfold hY) (m + 1) :=
    fun j => hcs.coords (D.center j)
  have hchart : ∀ j, chartAt (EuclideanQuadrant (m + 1)) (D.center j) = (κ j).toQuadrantChart :=
    fun j => chartAt_eq_of_eq hcs hch _
  have hρ0 : ∀ j (y : M), y ∉ (κ j).s → ρ' j y.1 = 0 := fun j y hy => by
    rw [hρ' j y]
    exact image_eq_zero_of_notMem_tsupport fun h => hy (by
      have := D.region_subset j (D.tsupport_subset j h)
      rw [hchart j] at this; exact this)
  set g : {x // x ∈ T} → Fin (m + 1) → EuclideanSpace ℝ (Fin m) → ℝ :=
    fun j l u => ρ' j ((κ j).facePt l u).1 *
      F.faceDensity hcs o'.frames ω (κ j) l ((κ j).facePt l u) with hg
  -- one chart, one face
  have hJ : ∀ j l, IntegrableOn (g j l) ((κ j).faceSet l) ∧
      orSign (D.sign j) * (faceSign l * topFormIntegral
        (faceEmbedding l ⁻¹' ((κ j).toQuadrantChart.extend (𝓠 (m + 1))).target)
        (facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) (κ j).toQuadrantChart
          (ManifoldForm.smulFun (D.ρ j) η)))) = ∫ u in (κ j).faceSet l, g j l u := by
    intro j l
    set K := tsupport (D.ρ j) ∩ ManifoldForm.tsupport η with hK
    have hKc : IsCompact K := hc.inter_left (isClosed_tsupport _)
    have hKe : K ⊆ (κ j).toQuadrantChart.source := fun x hx => by
      have := D.region_subset j (D.tsupport_subset j hx.1)
      rw [hchart j] at this; exact this
    have hz : ∀ x ∉ K, ManifoldForm.smulFun (D.ρ j) η x = 0 := fun x hx => by
      by_cases h1 : x ∈ tsupport (D.ρ j)
      · have h2 : x ∉ ManifoldForm.tsupport η := fun h2 => hx ⟨h1, h2⟩
        rw [ManifoldForm.smulFun_apply, ManifoldForm.eq_zero_of_notMem_tsupport h2, smul_zero]
      · rw [ManifoldForm.smulFun_apply, image_eq_zero_of_notMem_tsupport h1, zero_smul]
    have hcont : ContinuousOn (ManifoldForm.chartForm (𝓠 (m + 1))
        (chartAt (EuclideanQuadrant (m + 1)) (D.center j)) (ManifoldForm.smulFun (D.ρ j) η))
        ((chartAt (EuclideanQuadrant (m + 1)) (D.center j)).extend (𝓠 (m + 1))).target :=
      (D.contMDiffForm_smulFun (r := 0) (by simp) j
      (hη1.of_le (r' := 0) zero_le_one) (D.center j)).continuousOn
    rw [hchart j] at hcont
    have hint := ManifoldForm.integrableOn_facePullback_chartForm hcont hKc hKe hz l
    exact F.face_term_eq hch hM ht o ω η hη (κ j) l (D.ρ j) (ρ' j) (hρ' j) (D.sign j)
      (fun y hy => by have := D.orientationIn_eq j y hy; rwa [hchart j] at this)
      (D.tsupport_subset j) hint
  have hL : D.boundaryIntegral η = ∑ j, ∑ l, ∫ u in (κ j).faceSet l, g j l u := by
    unfold IntegrationData.boundaryIntegral
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show D.chart j = (κ j).toQuadrantChart from hchart j,
      ManifoldForm.chartBoundaryIntegral, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (hJ j l).2
  rw [hL]
  by_cases hne : bS.Nonempty
  swap
  · rw [FormEval.msInteg_of_inter_eq_empty (F := F) ω _
      (by rw [inter_self]; exact not_nonempty_iff_eq_empty.1 hne)]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
    have he : (κ j).faceSet l = ∅ := eq_empty_of_forall_notMem fun u hu =>
      hne ⟨_, facePt_mem_boundaryStratum hM.1 ht (κ j) hu⟩
    rw [he, Measure.restrict_empty, integral_zero_measure]
  have hN := hb hne
  obtain ⟨D', hD'⟩ := hN.2
  have hNb : MeasurableSet[borel Obj] bS := hN.1.1.measurableSet_borel
  rw [FormEval.msInteg_eq hm hN D' hD' o' ω (SheetNullSets.isMeasIn_of_borel hNb)]
  have hBk : ∀ k, MeasurableSet[borel Obj] (bS ∩ D'.P k) := fun k =>
    @MeasurableSet.inter Obj (borel Obj) _ _ hNb (D'.measurableSet_P hNb k)
  have hBk' : ∀ k, MeasurableSet[borel Obj] ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k)) := fun k =>
    @MeasurableSet.inter Obj (borel Obj) _ _ (hBk k) (@MeasurableSet.inter Obj (borel Obj) _ _
      hNb (MeasurableSpace.measurableSet_generateFrom (D'.isOpen k)))
  -- the terms of the glued integral
  have hterm : ∀ k, F.integ ω (bS ∩ D'.V k) (o'.restrict (D'.isOpen k)).tangent (bS ∩ D'.P k) =
      ∑ j, ∑ l, ∫ u in (κ j).faceSet l ∩ (fun u => ((κ j).facePt l u).1) ⁻¹'
        ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k)), g j l u := by
    intro k
    set c := chart (D'.mem k) with hcdef
    set ok := o'.restrict (D'.isOpen k) with hok
    rw [integ_eq (D'.mem k) ok ω]
    unfold chartInteg
    have hmeas : MeasurableSet (c.coord '' ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k))) :=
      c.measurableSet_coord_image_borel (hBk k)
    have H := fun j => F.integral_density_eq_sum_face (hcs := hcs) hM ht (D'.isOpen k) c ok ω
      (κ j) (ρ' j) (hρ0 j) (hBk k) fun l => (hJ j l).1
    have e1 : (∫ u in c.coord '' ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k)),
        F.density c ω ok.tangent (c.q u)) =
        ∫ u in c.coord '' ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k)),
          ∑ j, ρ' j (c.q u) * F.density c ω ok.tangent (c.q u) := by
      refine setIntegral_congr_fun hmeas ?_
      rintro _ ⟨y, hy, rfl⟩
      change F.density c ω ok.tangent (c.q (c.coord y)) =
        ∑ j, ρ' j (c.q (c.coord y)) * F.density c ω ok.tangent (c.q (c.coord y))
      rw [c.q_coord' hy.2, ← Finset.sum_mul]
      have hyM : y ∈ M := hy.2.1.1
      simp only [hρ' _ ⟨y, hyM⟩]
      by_cases hs : (⟨y, hyM⟩ : M) ∈ ManifoldForm.tsupport η
      · rw [D.sum_eq_one _ hs, one_mul]
      · rw [F.density_eq_zero_of_restrict_eq_zero hM ht (D'.isOpen k) c ok ω η hη
          (y := ⟨y, hyM⟩) hy.2 (ManifoldForm.eq_zero_of_notMem_tsupport hs), mul_zero]
    rw [e1, integral_finsetSum _ fun j _ => (H j).1]
    exact Finset.sum_congr rfl fun j _ => (H j).2
  -- each face integral is the sum over the pieces
  have hsum : ∀ j l, HasSum (fun k => ∫ u in (κ j).faceSet l ∩
      (fun u => ((κ j).facePt l u).1) ⁻¹' ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k)), g j l u)
      (∫ u in (κ j).faceSet l, g j l u) := by
    intro j l
    have hU : ⋃ k, ((κ j).faceSet l ∩ (fun u => ((κ j).facePt l u).1) ⁻¹'
        ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k))) = (κ j).faceSet l := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨k, hu, -⟩; exact hu
      · intro hu
        have hb' := facePt_mem_boundaryStratum hM.1 ht (κ j) hu
        obtain ⟨k, hk⟩ := D'.exists_mem_P hb'
        exact ⟨k, hu, ⟨hb', hk⟩, hb', (D'.P_subset k hk).2⟩
    have hd : Pairwise (Function.onFun Disjoint fun k => (κ j).faceSet l ∩
        (fun u => ((κ j).facePt l u).1) ⁻¹' ((bS ∩ D'.P k) ∩ (bS ∩ D'.V k))) :=
      fun k k' hkk' => disjoint_left.2 fun u hu hu' =>
        disjoint_left.1 (D'.disjoint_P hkk') hu.2.1.2 hu'.2.1.2
    have h := hasSum_integral_iUnion
      (fun k => measurableSet_faceSet_inter_preimage (κ j) l (hBk' k)) hd
      (by rw [hU]; exact (hJ j l).1)
    rwa [hU] at h
  have hfin := hasSum_sum (s := Finset.univ) fun j _ =>
    hasSum_sum (s := Finset.univ) fun l _ => hsum j l
  unfold ChartCover.gInteg ChartCover.term
  exact ((tsum_congr hterm).trans hfin.tsum_eq).symm

end EpGroupoid

namespace EP

open MPolyfold

/-- **Part I's boundary integral over a sheet `Mᵢ` is the integral of §9.5 over its boundary
sheet** (proof of Theorem 9.5.18, 2021 p. 451, last equality of the display; Definition 9.3.8,
p. 426): for an oriented tame structure `C` of dimension `m + 1` at `x` with sheets in the class
of §9.5, a class `a ∈ Ωᵐ_{ep,∞}(X)` vanishing on `Mᵢ` off a closed `K` with `Mᵢ ∩ K` compact,
and `∂₁Mᵢ` in the class `msheets` when it is nonempty,
`∫_{∂(Mᵢ,oᵢ)} a = ∫_{∂₁Mᵢ} a|(∂₁Mᵢ, o_{∂Mᵢ})`. -/
theorem boundaryIntegral_eq_msInteg (A : EP.{u}) {m : ℕ} (hm : 0 < m) {Θ : A.Obj → ℚ}
    {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) (i : C.ι)
    (hb : (C.boundarySheet i).Nonempty →
      C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets)
    (a : A.epFormsInfty m) {K : Set A.Obj} (hK : IsClosed K) (hKc : IsCompact (C.M i ∩ K))
    (h0 : (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).VanishesOff K
      (A.epFormsInftyToObj m a)) :
    (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).boundaryIntegral
        (A.epFormsInftyToObj m a) =
      (A.epFormsInftyEval m).msInteg a (C.boundarySheet i) (C.boundaryOrient i).tangent
        (C.boundarySheet i) := by
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  have := EpGroupoid.FormEval.sigmaCompactSpace_of_mem_sheets (hS i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).isManifold_cornerChartedSpace
    hcs
  have hc : IsCompact (ManifoldForm.tsupport (formsInftyRestrict m hcs
      (A.epFormsInftyToObj m a))) := by
    have hcl : IsClosed ((↑) ⁻¹' K : Set (C.M i)) := hK.preimage continuous_subtype_val
    have hcp : IsCompact ((↑) ⁻¹' K : Set (C.M i)) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
      exact hKc
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (h0 y hyC)
  have hC1 : ManifoldForm.ContMDiffForm (𝓠 (m + 1)) 1
      (formsInftyRestrict m hcs (A.epFormsInftyToObj m a)) :=
    (contMDiffForm_formsInftyRestrict (hcs := hcs) rfl (A.epFormsInftyToObj m a)).of_le
      (by exact_mod_cast le_top)
  have key := (A.epFormsInftyEval m).boundaryIntegral_eq_msInteg (M := C.M i) (hcs := hcs) rfl hm
    (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i) (C.orient i) a
    (formsInftyRestrict m hcs (A.epFormsInftyToObj m a)) hC1 hc
    (fun y v => A.formsInftyRestrict_epFormsInftyToObj hm (C.isSubmanifoldOfDim i).1 a y v) hb
  exact key

end EP

end Polyfold
