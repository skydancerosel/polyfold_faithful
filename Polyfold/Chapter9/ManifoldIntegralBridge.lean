import Polyfold.Chapter9.ManifoldBridge
import Polyfold.Chapter9.FormEvalInfty

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, pp. 438–451 (gaps G.107, G.110).  Numbers and pages are the 2021
text's.

# The integral over an oriented tame sheet is the manifold integral of Part I

For a tame `n`-dimensional sheet `N` of the class `F.sheets` (one graph chart, integrable forms),
oriented by `o` (Definition 9.3.3), and a form `ω` whose restriction `η` to the manifold `N` is
continuous with compact support: `∫_N ω|(N, o)` (`FormEval.integ`) is the integral
`ManifoldForm.integral` of `η` over the manifold with corners `N` oriented by
`bridgeOrientation o` (`FormEval.integ_eq_manifoldIntegral`).

The proof compares, chart by chart of an integration datum of Part I (a finite partition of unity
in signed corner charts), the Lebesgue integral of `ρⱼ ·` density in the graph chart with the
one in corner coordinates (change of variables), and sums.

(2026-11-13) The corollaries below are for classes of `Ωⁿ_{ep,∞}(X)` represented on level `0`; for
classes represented on any level see `EP.epFormsInftyEval_integ_eq_integral`
(`LevelRestrict.lean`).
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
  {n : ℕ} {N : Set Obj} [ParacompactSpace N] {hY : X.PObj.IsSubMPolyfold N}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim n}
  {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

/-- **Weighted change of variables between a graph chart and corner coordinates**: for a weight
`f` and `A ⊆ κ.s` with measurable coordinate image, the integrals of `f ·` density agree, and
integrability passes from the corner coordinates to the graph chart. -/
theorem weighted_corner (hN : X.PObj.IsSubmanifoldOfDim N n) (c : X.PObj.GraphChart n N)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (κ : CornerCoords (subPolyfold hY) n) (f : Obj → ℝ) {A : Set N} (hA : A ⊆ κ.s)
    (hAm : MeasurableSet (κ.toQuadrantChart.extend (𝓠 n) '' A)) :
    (∫ u in c.coord '' (Subtype.val '' A), f (c.q u) * F.density c ω o.tangent (c.q u)) =
      (∫ u in κ.toQuadrantChart.extend (𝓠 n) '' A,
        f ((κ.toQuadrantChart.extend (𝓠 n)).symm u).1 *
          F.cornerDensity hcs o ω κ ((κ.toQuadrantChart.extend (𝓠 n)).symm u)) ∧
    (IntegrableOn (fun u => f ((κ.toQuadrantChart.extend (𝓠 n)).symm u).1 *
        F.cornerDensity hcs o ω κ ((κ.toQuadrantChart.extend (𝓠 n)).symm u))
        (κ.toQuadrantChart.extend (𝓠 n) '' A) →
      IntegrableOn (fun u => f (c.q u) * F.density c ω o.tangent (c.q u))
        (c.coord '' (Subtype.val '' A))) := by
  set ext := κ.toQuadrantChart.extend (𝓠 n) with hext
  have hleft : ∀ y ∈ κ.s, ext.symm (ext y) = y := fun y hy =>
    κ.toQuadrantChart.extend_left_inv (I := 𝓠 n) hy
  let DN : N → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun y =>
    c.p.comp (modelDeriv κ c.isChart (hN.1.data y.2).toSubData y (levelLift κ.χ 1 y))
  have hσ : ∀ y : N, y ∈ (subChart (hN.1.data y.2).toSubData c.isChart y).source :=
    fun y => (hN.1.data y.2).toSubData.mem_shrink c.φ y.2 (hN.1.mem_data_V y.2)
      (c.subset_source y.2)
  set τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => c.coord (ext.symm u).1 with hτ
  have hsub : ext '' A ⊆ range (𝓠 n) := by
    rintro _ ⟨y, -, rfl⟩
    rw [hext, OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hderiv : ∀ u ∈ ext '' A, HasFDerivWithinAt τ (DN (ext.symm u)) (ext '' A) u := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hleft y (hA hy)]
    exact (hasFDerivWithinAt_coord_corner (hcs := hcs) c κ (hA hy) _ y (hσ y)).mono hsub
  have hinj : InjOn τ (ext '' A) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩ h
    simp only [hτ, hleft y (hA hy), hleft w (hA hw)] at h
    rw [Subtype.ext (c.injOn_coord y.2 w.2 h)]
  have himg : τ '' (ext '' A) = c.coord '' (Subtype.val '' A) := by
    rw [image_image, image_image]
    exact image_congr fun y hy => by simp only [hτ, hleft y (hA hy)]
  have hpt : EqOn (fun u => |(DN (ext.symm u)).det| •
      (f (c.q (τ u)) * F.density c ω o.tangent (c.q (τ u))))
      (fun u => f (ext.symm u).1 * F.cornerDensity hcs o ω κ (ext.symm u)) (ext '' A) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyκ := hA hy
    simp only [hτ, hleft y hyκ, smul_eq_mul]
    rw [c.q_coord' y.2, FormEval.cornerDensity, dif_pos hyκ,
      F.sgn_mul_ev_incFrame (hcs := hcs) hN c o ω κ hyκ (stdBasis n)]
    have hdet : (Matrix.of fun i j =>
        c.p (chartVec c.isChart (incFrame hcs κ hyκ (stdBasis n j))) i).det = (DN y).det := by
      rw [← GraphChart.det_matrix_bvec (DN y)]
      congr 1
      ext i j
      simp only [Matrix.of_apply, DN, ContinuousLinearMap.comp_apply]
      rw [← chartVec_incFrame (hcs := hcs) κ hyκ _ c.isChart _ y (hσ y)]
      have hb : stdBasis n j = GraphChart.bvec j := by simp [stdBasis, GraphChart.bvec]
      rw [hb]
    rw [hdet]; ring
  refine ⟨?_, fun hint => ?_⟩
  · rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume hAm hderiv hinj]
    exact setIntegral_congr_fun hAm hpt
  · rw [← himg, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hAm hderiv hinj]
    exact (integrableOn_congr_fun hpt hAm).2 hint

/-- If `ω` vanishes on the corner frame at `y`, the density of a graph chart vanishes at `y`. -/
theorem density_eq_zero_of_ev_eq_zero (hN : X.PObj.IsSubmanifoldOfDim N n)
    (c : X.PObj.GraphChart n N) (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s)
    (h0 : F.ev ω (fun i => incFrame hcs κ hy (stdBasis n i)) = 0) :
    F.density c ω o.tangent y = 0 := by
  have h := F.sgn_mul_ev_incFrame (hcs := hcs) hN c o ω κ hy (stdBasis n)
  rw [h0, mul_zero] at h
  refine (mul_eq_zero.1 h.symm).resolve_left (abs_ne_zero.2 fun hdet => ?_)
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hli := linearIndependent_chartVec_incFrame (hcs := hcs) hN.1 κ hy (stdBasis n) c.isChart
    (c.subset_source y.2)
  rw [Fintype.linearIndependent_iff] at hli
  refine hv (funext fun j => hli v ?_ j)
  have hD : ∀ j, chartVec c.isChart (incFrame hcs κ hy (stdBasis n j)) =
      ∑ i, c.p (chartVec c.isChart (incFrame hcs κ hy (stdBasis n j))) i •
        chartVec c.isChart (c.tvec y.1 i) := fun j =>
    chartVec_incFrame_eq_sum_tvec hN.1 c κ hy (stdBasis n j)
  calc ∑ j, v j • chartVec c.isChart (incFrame hcs κ hy (stdBasis n j))
      = ∑ j, ∑ i, (v j * c.p (chartVec c.isChart (incFrame hcs κ hy (stdBasis n j))) i) •
          chartVec c.isChart (c.tvec y.1 i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [hD j]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    _ = ∑ i, (∑ j, v j * c.p (chartVec c.isChart (incFrame hcs κ hy (stdBasis n j))) i) •
          chartVec c.isChart (c.tvec y.1 i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have := congrFun hMv i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
        rw [show (∑ j, v j * c.p (chartVec c.isChart (incFrame hcs κ hy (stdBasis n j))) i) = 0
          from by rw [← this]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _, zero_smul]

section Charted

variable [inst : ChartedSpace (EuclideanQuadrant n) N]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

open Classical in
/-- **Part I's chart integrand is the corner density**: for a Mathlib form `η` on `N` which is
the restriction of `ω`, in the chart of corner coordinates `κ`, at a point where the tangent
orientation reads as `± ` the standard one. -/
theorem orSign_mul_chartForm_eq (hn : 0 < n) (hN : X.PObj.IsSubmanifoldOfDim N n)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω) (η : ManifoldForm (𝓠 n) N n)
    (hη : ∀ (y : N) (v : Fin n → EuclideanSpace ℝ (Fin n)),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    (κ : CornerCoords (subPolyfold hY) n) {y : N} (hy : y ∈ κ.s) (b : Bool)
    (hb : orientationIn κ.toQuadrantChart y (bridgeOrientation hcs o y) =
      signedOr b (stdOrientation n)) :
    orSign b * ManifoldForm.chartForm (𝓠 n) κ.toQuadrantChart η
        (κ.toQuadrantChart.extend (𝓠 n) y) (stdFrame n) = F.cornerDensity hcs o ω κ y := by
  subst hch
  let _ : ChartedSpace (EuclideanQuadrant n) N := (subPolyfold hY).cornerChartedSpace hcs
  have hleft : (κ.toQuadrantChart.extend (𝓠 n)).symm (κ.toQuadrantChart.extend (𝓠 n) y) = y :=
    κ.toQuadrantChart.extend_left_inv (I := 𝓠 n) hy
  have hyy : y ∈ (hcs.coords y).s := hcs.mem_coords y
  have hval : ManifoldForm.chartForm (𝓠 n) κ.toQuadrantChart η
      (κ.toQuadrantChart.extend (𝓠 n) y) (stdFrame n) =
      F.ev ω fun i => incFrame hcs κ hy (stdBasis n i) := by
    rw [ManifoldForm.chartForm_apply, hleft]
    refine (hη y _).trans ?_
    congr 1
    funext i
    have h1 := fiberMap_chartChange (hcs := hcs) rfl κ (hcs.coords y) hy hyy (stdFrame n i)
    change MPolyfold.tangentMap (subPolyfold_inclusion_isScSmooth hY) ((hcs.coords y).fiberMap (x := hcs.levelOne y) _
      (chartChangeDeriv (𝓠 n) κ.toQuadrantChart (hcs.coords y).toQuadrantChart y
        (stdFrame n i))).1 = MPolyfold.tangentMap (subPolyfold_inclusion_isScSmooth hY) (κ.fiberMap (x := hcs.levelOne y) _ (stdBasis n i)).1
    rw [h1]
    rfl
  rw [hval, FormEval.cornerDensity, dif_pos hy]
  rw [orientationIn_bridgeOrientation rfl hn hN o κ hy] at hb
  have hiff := orientation_eq_orIn_iff (hcs := hcs) hn hN o κ hy (stdBasis n)
  have hstd : (stdBasis n).orientation = stdOrientation n := rfl
  cases b
  · have hne : (fun i => incFrame hcs κ hy (stdBasis n i)) ∉ o.frames y := fun h => by
      have h1 := hiff.2 h
      rw [hb, hstd, signedOr_false] at h1
      exact Module.Ray.ne_neg_self _ h1
    rw [if_neg hne, orSign_false]
  · rw [if_pos (hiff.1 (by rw [hb, hstd, signedOr_true])), orSign_true]

/-- **The integral over an oriented tame sheet is the manifold integral of Part I**: for a sheet
`N` of the class `F.sheets` with a corner structure, a Hausdorff σ-compact manifold, oriented by
`o` (Definition 9.3.3), and a continuous compactly supported Mathlib `n`-form `η` on `N` which is
the restriction of `ω` (its values are those of `ω` on the frames `Tι(v)`),
`∫_N ω|(N, o) = ∫_N η` for the tangent orientation `bridgeOrientation o`. -/
theorem integ_eq_manifoldIntegral [IsManifold (𝓠 n) ∞ N] [T2Space N] [SigmaCompactSpace N]
    (hn : 0 < n) (hN : N ∈ F.sheets) (o : X.PObj.SubmanifoldOrientation N n) (ω : Ω)
    (η : ManifoldForm (𝓠 n) N n) (hηc : ManifoldForm.ContMDiffForm (𝓠 n) 0 η)
    (hc : IsCompact (ManifoldForm.tsupport η))
    (hη : ∀ (y : N) (v : Fin n → EuclideanSpace ℝ (Fin n)),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i)) :
    F.integ ω N o.tangent N = ManifoldForm.integral (bridgeOrientation hcs o) η := by
  classical
  have ho := isContinuous_bridgeOrientation hch hn hN.1 o
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [ManifoldForm.integral_eq_integrationData ho hηc hc D subset_rfl, integ_eq hN o]
  set c := chart hN with hcdef
  let ρ' : {x // x ∈ T} → Obj → ℝ := fun j x => if h : x ∈ N then D.ρ j ⟨x, h⟩ else 0
  have hρ' : ∀ j (y : N), ρ' j y.1 = D.ρ j y := fun j y => by
    simp only [ρ', dif_pos y.2]
  let κ : {x // x ∈ T} → CornerCoords (subPolyfold hY) n := fun j => hcs.coords (D.center j)
  have hchart : ∀ j, chartAt (EuclideanQuadrant n) (D.center j) = (κ j).toQuadrantChart :=
    fun j => chartAt_eq_of_eq hcs hch _
  have hρ0 : ∀ j (y : N), y ∉ (κ j).s → D.ρ j y = 0 := fun j y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (by
      have := D.region_subset j (D.tsupport_subset j h)
      rw [hchart j] at this; exact this)
  have hdens := F.integrableOn_density hn hN.1.1 c o ω (integrableOn_chart hN ω)
  -- one chart of the datum
  have hJ : ∀ j, IntegrableOn (fun u => ρ' j (c.q u) * F.density c ω o.tangent (c.q u)) c.dom ∧
      orSign (D.sign j) * ManifoldForm.chartIntegral (D.chart j)
        (ManifoldForm.smulFun (D.ρ j) η) =
      ∫ u in c.dom, ρ' j (c.q u) * F.density c ω o.tangent (c.q u) := by
    intro j
    set e := (κ j).toQuadrantChart with he
    set ext := e.extend (𝓠 n) with hext
    have htgt : ext '' (κ j).s = ext.target := by
      rw [← ext.image_source_eq_target, hext, e.extend_source]; rfl
    have hAm : MeasurableSet (ext '' (κ j).s) := by
      rw [htgt]; exact ManifoldForm.measurableSet_extend_target e
    -- the corner integrand is Part I's integrand
    have hpt : EqOn (fun u => orSign (D.sign j) *
        ManifoldForm.chartForm (𝓠 n) e (ManifoldForm.smulFun (D.ρ j) η) u (stdFrame n))
        (fun u => ρ' j (ext.symm u).1 * F.cornerDensity hcs o ω (κ j) (ext.symm u))
        ext.target := by
      intro u hu
      have hy : ext.symm u ∈ (κ j).s := by
        have := ext.map_target hu
        rwa [hext, e.extend_source] at this
      have hu' : ext (ext.symm u) = u := ext.right_inv hu
      simp only
      rw [ManifoldForm.chartForm_smulFun, hρ']
      change orSign (D.sign j) * (D.ρ j (ext.symm u) *
        ManifoldForm.chartForm (𝓠 n) e η u (stdFrame n)) = _
      by_cases hr : ext.symm u ∈ D.region j
      · have hb := D.orientationIn_eq j _ hr
        rw [hchart j] at hb
        have h2 := F.orSign_mul_chartForm_eq hch hn hN.1 o ω η hη (κ j) hy (D.sign j) hb
        rw [hu'] at h2
        rw [← h2]; ring
      · have h0 : D.ρ j (ext.symm u) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hr (D.tsupport_subset j h)
        rw [h0]; ring
    have hcorner : IntegrableOn (fun u => ρ' j (ext.symm u).1 *
        F.cornerDensity hcs o ω (κ j) (ext.symm u)) (ext '' (κ j).s) := by
      rw [htgt]
      set K := tsupport (D.ρ j) ∩ ManifoldForm.tsupport η with hK
      have hKc : IsCompact K := hc.inter_left (isClosed_tsupport _)
      have hKe : K ⊆ e.source := fun x hx => by
        have := D.region_subset j (D.tsupport_subset j hx.1)
        rw [hchart j] at this; exact this
      have hz : ∀ x ∉ K, ManifoldForm.smulFun (D.ρ j) η x = 0 := fun x hx => by
        by_cases h1 : x ∈ tsupport (D.ρ j)
        · have h2 : x ∉ ManifoldForm.tsupport η := fun h2 => hx ⟨h1, h2⟩
          rw [ManifoldForm.smulFun_apply, ManifoldForm.eq_zero_of_notMem_tsupport h2, smul_zero]
        · rw [ManifoldForm.smulFun_apply, image_eq_zero_of_notMem_tsupport h1, zero_smul]
      have hcont := D.continuousOn_chartForm_smulFun hηc j (D.center j)
      rw [hchart j] at hcont
      have h1 := (ManifoldForm.integrableOn_chartForm hcont hKc hKe hz).const_mul
        (orSign (D.sign j))
      exact (integrableOn_congr_fun hpt (ManifoldForm.measurableSet_extend_target e)).1 h1
    obtain ⟨hint_eq, hint⟩ := F.weighted_corner (hcs := hcs) hN.1 c o ω (κ j) (ρ' j)
      (A := (κ j).s) subset_rfl hAm
    have hsubdom : c.coord '' (Subtype.val '' (κ j).s) ⊆ c.dom := by
      rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact c.coord_mem_dom y.2
    have hzero : ∀ u ∈ c.dom \ c.coord '' (Subtype.val '' (κ j).s),
        ρ' j (c.q u) * F.density c ω o.tangent (c.q u) = 0 := by
      rintro u ⟨hu, hnu⟩
      have hq := c.q_mem hu
      have : (⟨c.q u, hq⟩ : N) ∉ (κ j).s := fun h =>
        hnu ⟨c.q u, ⟨⟨c.q u, hq⟩, h, rfl⟩, c.coord_q hu⟩
      rw [hρ' j ⟨c.q u, hq⟩, hρ0 j _ this, zero_mul]
    refine ⟨IntegrableOn.of_forall_sdiff_eq_zero (hint hcorner) c.measurableSet_dom' hzero, ?_⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero c.measurableSet_dom' hsubdom hzero,
      hint_eq, htgt]
    change orSign (D.sign j) * ManifoldForm.chartIntegral
      (chartAt (EuclideanQuadrant n) (D.center j)) (ManifoldForm.smulFun (D.ρ j) η) = _
    rw [hchart j, ManifoldForm.chartIntegral, topFormIntegral_def, ← integral_const_mul]
    exact setIntegral_congr_fun (ManifoldForm.measurableSet_extend_target e) hpt
  -- summation
  unfold IntegrationData.integral
  simp only [(hJ _).2]
  rw [← integral_finsetSum _ fun j _ => (hJ j).1]
  unfold chartInteg
  rw [inter_self]
  refine setIntegral_congr_fun c.measurableSet_dom' fun u hu => ?_
  have hq := c.q_mem hu
  simp only [hρ' _ ⟨c.q u, hq⟩]
  rw [← Finset.sum_mul]
  by_cases hs : (⟨c.q u, hq⟩ : N) ∈ ManifoldForm.tsupport η
  · rw [D.sum_eq_one _ hs, one_mul]
  · have h0 : F.density c ω o.tangent (c.q u) = 0 := by
      refine F.density_eq_zero_of_ev_eq_zero (hcs := hcs) hN.1 c o ω
        (hcs.coords ⟨c.q u, hq⟩) (y := ⟨c.q u, hq⟩) (hcs.mem_coords _) ?_
      rw [← hη, ManifoldForm.eq_zero_of_notMem_tsupport hs]
      rfl
    rw [h0, mul_zero]

end Charted

end FormEval

/-- **Definition 8.2.1 forms**: for `ω ∈ Ωⁿ_ep(X)` whose restriction `ω|_N` (Part I's
`scFormRestrict`) has compact support in the tame sheet `N`,
`∫_N ω|(N, o) = ∫_N ω|_N`, the manifold integral of Part I for the tangent orientation
`bridgeOrientation o`. -/
theorem epFormEval_integ_eq_integral_scFormRestrict
    [inst : ChartedSpace (EuclideanQuadrant n) N]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) [IsManifold (𝓠 n) ∞ N] [T2Space N]
    [SigmaCompactSpace N] (hn : 0 < n) (hN : N ∈ (X.epFormEval n).sheets)
    (o : X.PObj.SubmanifoldOrientation N n) (ω : X.epForms n)
    (hc : IsCompact (ManifoldForm.tsupport
      (scFormRestrict n hcs 0 (⟨ω.1, ω.2.1⟩ : (BundledMPolyfold.of X.PObj).forms n 0)))) :
    (X.epFormEval n).integ ω N o.tangent N =
      ManifoldForm.integral (bridgeOrientation hcs o)
        (scFormRestrict n hcs 0 (⟨ω.1, ω.2.1⟩ : (BundledMPolyfold.of X.PObj).forms n 0)) :=
  FormEval.integ_eq_manifoldIntegral (X.epFormEval n) hch hn hN o ω _
    ((contMDiffForm_scFormRestrict hch 0 _).of_le (by simp)) hc fun y v =>
    (epFormEval_ev_incFrame (hcs := hcs) hn ω (hcs.coords y) (hcs.mem_coords y) v).symm

/-- **For the oriented sheets of the Stokes file** (`MPolyfold.OrientedSheet`,
`StokesLocalFormulas.lean`): if the tangent orientation of the sheet `S` is the one given by an
orientation `o` of Definition 9.3.3, then for the class in `Ωⁿ⁺¹_∞(X)` of a form
`ω ∈ Ωⁿ⁺¹_ep(X)` with `ω|_S` of compact support, `OrientedSheet.integral` is `∫_S ω|(S, o)`. -/
theorem orientedSheet_integral_eq {m : ℕ} (S : MPolyfold.OrientedSheet X.PObj m)
    (hS : S.carrier ∈ (X.epFormEval (m + 1)).sheets)
    (o : X.PObj.SubmanifoldOrientation S.carrier (m + 1))
    (ho : S.o = @bridgeOrientation _ _ _ _ _ _ _ _ _ S.hcs
      ((subPolyfold S.isSub).cornerChartedSpace S.hcs) o) (ω : X.epForms (m + 1))
    (hc : letI := (subPolyfold S.isSub).cornerChartedSpace S.hcs
      IsCompact (ManifoldForm.tsupport (scFormRestrict (m + 1) S.hcs 0
        (⟨ω.1, ω.2.1⟩ : (BundledMPolyfold.of X.PObj).forms (m + 1) 0)))) :
    S.integral ((BundledMPolyfold.of X.PObj).formsInftyOf (m + 1) 0 ⟨ω.1, ω.2.1⟩) =
      (X.epFormEval (m + 1)).integ ω S.carrier o.tangent S.carrier := by
  let _ := (subPolyfold S.isSub).cornerChartedSpace S.hcs
  have := (subPolyfold S.isSub).isManifold_cornerChartedSpace S.hcs
  unfold MPolyfold.OrientedSheet.integral
  rw [formsInftyRestrict_of, ho]
  exact (epFormEval_integ_eq_integral_scFormRestrict (hcs := S.hcs) rfl (Nat.succ_pos m) hS o ω
    hc).symm

end EpGroupoid

namespace EP

open MPolyfold EpGroupoid

/-- **Classes in `Ωⁿ_{ep,∞}(X)`**: for the class `[ω]` of `ω ∈ Ωⁿ_ep(X)` with `ω|_N` of compact
support in the tame sheet `N`, `∫_N [ω]|(N, o) = ∫_N ω|_N` (the manifold integral of Part I). -/
theorem epFormsInftyEval_integ_eq_integral_scFormRestrict (A : EP.{u}) {n : ℕ}
    {N : Set A.Obj} [ParacompactSpace N] {hY : A.X.PObj.IsSubMPolyfold N}
    {hcs : (subPolyfold hY).HasCornerStructureOfDim n}
    [inst : ChartedSpace (EuclideanQuadrant n) N]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) [IsManifold (𝓠 n) ∞ N] [T2Space N]
    [SigmaCompactSpace N] (hn : 0 < n) (hN : N ∈ (A.epFormsInftyEval n).sheets)
    (o : A.X.PObj.SubmanifoldOrientation N n) (ω : A.epForms n 0)
    (hc : IsCompact (ManifoldForm.tsupport
      (scFormRestrict n hcs 0 (⟨ω.1, ω.2.1⟩ : (BundledMPolyfold.of A.X.PObj).forms n 0)))) :
    (A.epFormsInftyEval n).integ (A.epFormsInftyOf n 0 ω) N o.tangent N =
      ManifoldForm.integral (bridgeOrientation hcs o)
        (scFormRestrict n hcs 0 (⟨ω.1, ω.2.1⟩ : (BundledMPolyfold.of A.X.PObj).forms n 0)) :=
  FormEval.integ_eq_manifoldIntegral (A.epFormsInftyEval n) hch hn hN o _ _
    ((contMDiffForm_scFormRestrict hch 0 _).of_le (by simp)) hc fun y v =>
    ((A.epFormsInftyEval_of_zero n ω hN.1.1 y.2 fun i =>
      incFrame_mem hN.1.1 (hcs.coords y) (hcs.mem_coords y) (v i)).trans
      (epFormEval_ev_incFrame (hcs := hcs) hn ω (hcs.coords y) (hcs.mem_coords y) v)).symm

end EP

end Polyfold
