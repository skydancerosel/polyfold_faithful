import Polyfold.Chapter9.BoundaryIntegralStratum

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, Theorems 9.5.15–9.5.18 (pp. 448–451; gaps G.109, G.110).  Numbers and pages are
the 2021 text's.

# Boundary strata near compact pieces lie in the class `msheets`

The text integrates `ω` over the boundary strata `∂₁Mᵢ = {d_{Mᵢ} = 1}` of the sheets of a tame
structure (pp. 448–451) without comment on the finiteness of `∫ |ω|` near the corners of `Mᵢ`
(the points with `d ≥ 2`, which are not in `∂₁Mᵢ`).  Here this finiteness is proved: if
`∂₁M ∩ V` lies in a compact subset of `M`, then `∂₁M ∩ V` is in E4's class `F.msheets`
(countably many graph charts, `∑ ∫ |ω| < ∞`), for every evaluation `F` whose forms restrict to
continuous Mathlib forms on `M` (Part I's restriction, `formsInftyRestrict`).

## The proof

* Cover the compact set by finitely many corner charts `κ_j` of `M` (Part I's corner structure of
  a tame sheet), each with a compact `L_j ⊆ dom κ_j` whose interior contains the given point.
* `∂₁M ∩ V` is Lindelöf (it is a finite union of continuous images of subsets of the open face
  pieces `faceSet κ_j l ⊆ ℝᵐ`), so it has a countable chart cover `D`
  (`exists_chartCover_of_isLindelof`).
* For a piece `P_k` of `D` and a face `l` of `κ_j`, the change of variables between the graph chart
  of `∂₁M ∩ V_k` and the face parameters (E8F's `face_change`, here with `|·|` and
  `lintegral`) gives `∫_{P_k ∩ ...} |ω| = ∫_{A_{kjl}} |ιₗ^*(κ_j⁻¹)^*η|`, where `η` is the
  restriction of `ω` to `M` (`abs_ev_faceFrame`, `facePullback_eq_ev_faceFrame`).
* The face integrand is continuous on the closed face (corners included: it is the chart form of
  the continuous form `η`), the sets `A_{kjl}` (`k ∈ ℕ`) are disjoint and lie in the compact set
  `ιₗ⁻¹(κ_j(L_j))`; hence `∑ₖ ∫_{P_k} |ω| < ∞` (`isFinite_of_corner`).

## Main results

* `FormEval.boundaryStratum_inter_mem_msheets`: the generic statement.
* `EP.boundaryStratum_inter_mem_msheets`: for `Ωᵐ_{ep,∞}(X)` (`A.epFormsInftyEval m`, `m > 0`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

/-- The closed quadrant is a closed subset of `ℝⁿ`. -/
theorem k1_isClosedEmbedding_quadrant (n : ℕ) :
    Topology.IsClosedEmbedding (Subtype.val : EuclideanQuadrant n → EuclideanSpace ℝ (Fin n)) := by
  have h : IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
    have e : {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} := by
      ext x; simp
    rw [e]
    exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)
  exact h.isClosedEmbedding_subtypeVal

theorem k1_locallyCompactSpace_quadrant (n : ℕ) : LocallyCompactSpace (EuclideanQuadrant n) :=
  (k1_isClosedEmbedding_quadrant n).locallyCompactSpace

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace FormEval

/-- **A Lindelöf `n`-dimensional submanifold has a countable chart cover** (as E4's
`exists_chartCover`, with the Lindelöf property given). -/
theorem exists_chartCover_of_isLindelof {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
    {F : X.FormEval n Ω} {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N n) (hne : N.Nonempty)
    (hL : IsLindelof N) : Nonempty (F.ChartCover N) := by
  choose Vf hVo hyV hVs using fun y : N => exists_mem_sheets (F := F) hN y.2
  obtain ⟨r, hrc, hr⟩ := hL.elim_countable_subcover Vf hVo
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyV _⟩)
  have hrne : r.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz, -⟩ := mem_iUnion₂.1 (hr hy)
    exact ⟨z, hz⟩
  obtain ⟨f, hf⟩ := hrc.exists_eq_range hrne
  exact ⟨{ V := fun k => Vf (f k)
           isOpen := fun k => hVo _
           cover := fun y hy => by
             obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hr hy)
             rw [hf] at hz
             obtain ⟨k, rfl⟩ := hz
             exact mem_iUnion.2 ⟨k, hyz⟩
           mem := fun k => hVs _ }⟩

end FormEval

variable {m : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M} {hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1)}

/-- **`|ω|` on a face frame and in a graph chart**: for a graph chart `c` of an `m`-dimensional
`N` through a point `y = κ⁻¹(ιₗ u)` of the open face piece whose face frame lies in `T_yN`,
`|ω(Tι(ιₗ e₁), …, Tι(ιₗ e_m))| = |det Dτ(u)| · |ω(c.tvec y)|`, `τ = c ∘ κ⁻¹ ∘ ιₗ`. -/
theorem FormEval.abs_ev_faceFrame (F : X.FormEval m Ω) (hM : X.PObj.IsSubmanifoldOfDim M (m + 1))
    {N : Set Obj} (hN : X.PObj.IsSubmanifoldOfDim N m) (c : X.PObj.GraphChart m N) (ω : Ω)
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1)) {u : EuclideanSpace ℝ (Fin m)}
    (hu : u ∈ κ.faceSet l) (hyN : (κ.facePt l u).1 ∈ N)
    (hβ : ∀ k, faceFrame hcs κ (CornerCoords.facePt_mem_s hu) l k ∈
      X.PObj.submanifoldTangent N (κ.facePt l u).1) :
    |F.ev ω (faceFrame hcs κ (CornerCoords.facePt_mem_s hu) l)| =
      |(c.p.comp ((modelDeriv κ c.isChart (hM.1.data (κ.facePt l u).2).toSubData (κ.facePt l u)
        (levelLift κ.χ 1 (κ.facePt l u))).comp (faceEmbedding l))).det| *
      |F.ev ω (c.tvec (κ.facePt l u).1)| := by
  set y := κ.facePt l u with hydef
  have hy : y ∈ κ.s := CornerCoords.facePt_mem_s hu
  set β := faceFrame hcs κ hy l with hβdef
  set Mx : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => c.p (chartVec c.isChart (β j)) i
    with hMx
  have hD : ∀ j, chartVec c.isChart (β j) = ∑ i, Mx i j • chartVec c.isChart (c.tvec y.1 i) :=
    fun j => FormEval.chartVec_eq_sum_tvec c hyN (hβ j)
  have hev : F.ev ω β = Mx.det * F.ev ω (c.tvec y.1) :=
    F.ev_det ω hN.1 hyN c.isChart (c.subset_source hyN) (c.tvec y.1) β (c.tvec_mem hyN) hβ Mx hD
  have hσ : y ∈ (subChart (hM.1.data y.2).toSubData c.isChart y).source :=
    (hM.1.data y.2).toSubData.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2) (c.subset_source hyN)
  have hdet : Mx.det = (c.p.comp ((modelDeriv κ c.isChart (hM.1.data y.2).toSubData y
      (levelLift κ.χ 1 y)).comp (faceEmbedding l))).det := by
    rw [← GraphChart.det_matrix_bvec]
    congr 1
    ext i j
    simp only [hMx, Matrix.of_apply, ContinuousLinearMap.comp_apply, hβdef]
    unfold faceFrame
    rw [chartVec_incFrame (hcs := hcs) κ hy _ c.isChart _ y hσ]
    have hb : stdFrame m j = GraphChart.bvec j := by simp [stdFrame_apply, GraphChart.bvec]
    rw [hb]
  rw [hev, abs_mul, hdet]

variable [inst : ChartedSpace (EuclideanQuadrant (m + 1)) M]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **Part I's face integrand is `ω` on the face frame**: for a Mathlib `m`-form `η` on `M`
which is the restriction of `ω`, `ιₗ^*(κ⁻¹)^*η (u)(e₁, …, e_m) = ω(Tι(ιₗ e₁), …, Tι(ιₗ e_m))` at
a point `u` of the open face piece (the computation inside E8F's
`orSign_mul_faceSign_mul_facePullback_eq`, without the orientation). -/
theorem FormEval.facePullback_eq_ev_faceFrame (F : X.FormEval m Ω) (ω : Ω)
    (η : ManifoldForm (𝓠 (m + 1)) M m)
    (hη : ∀ (y : M) (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))),
      η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1))
    {u : EuclideanSpace ℝ (Fin m)} (hu : u ∈ κ.faceSet l) :
    facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart η) u (stdFrame m) =
      F.ev ω (faceFrame hcs κ (CornerCoords.facePt_mem_s hu) l) := by
  subst hch
  let _ : ChartedSpace (EuclideanQuadrant (m + 1)) M := (subPolyfold hY).cornerChartedSpace hcs
  set y := κ.facePt l u with hydef
  have hy : y ∈ κ.s := CornerCoords.facePt_mem_s hu
  have hyy : y ∈ (hcs.coords y).s := hcs.mem_coords y
  rw [facePullback, formPullback_apply, ManifoldForm.chartForm_apply]
  refine (hη y _).trans ?_
  congr 1
  funext k
  have h1 := fiberMap_chartChange (hcs := hcs) rfl κ (hcs.coords y) hy hyy
    (faceEmbedding l (stdFrame m k))
  change MPolyfold.tangentMap (subPolyfold_inclusion_isScSmooth hY)
    ((hcs.coords y).fiberMap (x := hcs.levelOne y) _
      (chartChangeDeriv (𝓠 (m + 1)) κ.toQuadrantChart (hcs.coords y).toQuadrantChart y
        (faceEmbedding l (stdFrame m k)))).1 =
    MPolyfold.tangentMap (subPolyfold_inclusion_isScSmooth hY)
      (κ.fiberMap (x := hcs.levelOne y) _ (faceEmbedding l (stdFrame m k))).1
  rw [h1]

/-- **The face integrand is integrable over the face parameters of a compact part of a corner
chart**, corners included: for a continuous Mathlib form `η` on `M`, corner coordinates `κ` and a
compact `L ⊆ dom κ`, `u ↦ ιₗ^*(κ⁻¹)^*η (u)(e₁, …, e_m)` is integrable on `ιₗ⁻¹(κ(L))`. -/
theorem integrableOn_facePullback_of_isCompact [IsManifold (𝓠 (m + 1)) ∞ M]
    {η : ManifoldForm (𝓠 (m + 1)) M m} (hη0 : ManifoldForm.ContMDiffForm (𝓠 (m + 1)) 0 η)
    (κ : CornerCoords (subPolyfold hY) (m + 1)) (l : Fin (m + 1)) {L : Set M} (hL : IsCompact L)
    (hLs : L ⊆ κ.s) :
    IntegrableOn (fun u => facePullback l (ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart η)
      u (stdFrame m)) (faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (m + 1)) '' L)) := by
  have ha : κ.toQuadrantChart ∈ atlas (EuclideanQuadrant (m + 1)) M := by
    subst hch
    exact ⟨κ, rfl⟩
  have he : κ.toQuadrantChart ∈ IsManifold.maximalAtlas (𝓠 (m + 1)) ∞ M :=
    IsManifold.subset_maximalAtlas ha
  have hω := hη0.continuousOn_chartForm he
  set T := (κ.toQuadrantChart.extend (𝓠 (m + 1))).target
  have hCK : IsCompact (κ.toQuadrantChart.extend (𝓠 (m + 1)) '' L) :=
    hL.image_of_continuousOn (κ.toQuadrantChart.continuousOn_extend.mono
      (by rw [κ.toQuadrantChart.extend_source]; exact hLs))
  have hCt : κ.toQuadrantChart.extend (𝓠 (m + 1)) '' L ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (κ.toQuadrantChart.extend (𝓠 (m + 1))).map_source
      (by rw [κ.toQuadrantChart.extend_source]; exact hLs hx)
  have hemb : Topology.IsClosedEmbedding (faceEmbedding l) :=
    LinearMap.isClosedEmbedding_of_injective (f := (faceEmbedding l :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
      (LinearMap.ker_eq_bot.2 (MPolyfold.faceEmbedding_injective l))
  have hCK' := hemb.isCompact_preimage hCK
  have hc : ContinuousOn (fun u => facePullback l (ManifoldForm.chartForm (𝓠 (m + 1))
      κ.toQuadrantChart η) u (stdFrame m)) (faceEmbedding l ⁻¹' T) := by
    have h1 : ContinuousOn (fun u => ManifoldForm.chartForm (𝓠 (m + 1)) κ.toQuadrantChart η
        (faceEmbedding l u)) (faceEmbedding l ⁻¹' T) :=
      hω.comp (faceEmbedding l).continuous.continuousOn fun _ hu => hu
    exact (ContinuousAlternatingMap.apply ℝ _ ℝ
      (faceEmbedding l ∘ stdFrame m)).continuous.comp_continuousOn h1
  exact (hc.mono fun u hu => hCt hu).integrableOn_compact hCK'

/-- **The boundary stratum near a compact part of a tame sheet lies in the class `F.msheets`**
(the finiteness of `∫ |ω|` over `∂₁M` used tacitly on pp. 448–451): let `M` be a tame
`(m+1)`-dimensional submanifold, `F` an evaluation of `m`-forms whose forms restrict to
continuous Mathlib forms on `M` (`hη`), `V` open and `K ⊆ M` compact with `∂₁M ∩ V ⊆ K`.  Then
the nonempty `∂₁M ∩ V` is covered by countably many graph charts with `∑ ∫ |ω| < ∞`. -/
theorem FormEval.boundaryStratum_inter_mem_msheets [IsManifold (𝓠 (m + 1)) ∞ M]
    (F : X.FormEval m Ω) (hM : X.PObj.IsSubmanifoldOfDim M (m + 1))
    (ht : X.PObj.HasTameInducedStructure M)
    (hη : ∀ ω : Ω, ∃ η : ManifoldForm (𝓠 (m + 1)) M m,
      ManifoldForm.ContMDiffForm (𝓠 (m + 1)) 0 η ∧
        ∀ (y : M) (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))),
          η y v = F.ev ω fun i => incFrame hcs (hcs.coords y) (hcs.mem_coords y) (v i))
    {V : Set Obj} (hV : IsOpen V) {K : Set Obj} (hK : IsCompact K) (hKM : K ⊆ M)
    (hNK : X.PObj.boundaryStratum M ∩ V ⊆ K) (hne : (X.PObj.boundaryStratum M ∩ V).Nonempty) :
    X.PObj.boundaryStratum M ∩ V ∈ F.msheets := by
  classical
  set N := X.PObj.boundaryStratum M ∩ V with hNdef
  have hNs : X.PObj.IsSubmanifoldOfDim N m :=
    (isSubmanifoldOfDim_boundaryStratum hM ht).inter_isOpen hV
  have := k1_locallyCompactSpace_quadrant (m + 1)
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanQuadrant (m + 1)) M
  -- finitely many corner charts with compact parts covering `K`
  let κ : K → CornerCoords (subPolyfold hY) (m + 1) := fun z => hcs.coords ⟨z.1, hKM z.2⟩
  have hzκ : ∀ z : K, (⟨z.1, hKM z.2⟩ : M) ∈ (κ z).s := fun z => hcs.mem_coords _
  choose L hLc hzL hLs using fun z : K =>
    exists_compact_subset (κ z).toQuadrantChart.open_source (hzκ z)
  choose G hGo hGpre using fun z : K => isOpen_induced_iff.1 (isOpen_interior (s := L z))
  have hzG : ∀ z : K, z.1 ∈ G z := fun z => by
    have : (⟨z.1, hKM z.2⟩ : M) ∈ Subtype.val ⁻¹' G z := by rw [hGpre z]; exact hzL z
    exact this
  obtain ⟨t, htK⟩ := hK.elim_finite_subcover G hGo fun z hz =>
    mem_iUnion.2 ⟨⟨z, hz⟩, hzG ⟨z, hz⟩⟩
  have hmemL : ∀ (z : K) (y : M), y.1 ∈ G z → y ∈ interior (L z) := fun z y hy => by
    have : y ∈ Subtype.val ⁻¹' G z := hy
    rwa [hGpre z] at this
  have hcover : ∀ y ∈ N, ∃ p : t × Fin (m + 1), ∃ u ∈ (κ p.1.1).faceSet p.2,
      ((κ p.1.1).facePt p.2 u).1 = y ∧ y ∈ G p.1.1 := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (htK (hNK hy))
    have hyM : y ∈ M := hy.1.1
    have hyL := hmemL z ⟨y, hyM⟩ hyz
    obtain ⟨l, u, hu, heq⟩ := exists_facePt_of_mem_boundaryStratum hM.1 ht (κ z)
      (hLs z (interior_subset hyL)) hy.1
    exact ⟨(⟨z, hz⟩, l), u, hu, congrArg Subtype.val heq, hyz⟩
  -- a countable chart cover
  have hL : IsLindelof N := by
    have e : N = ⋃ p : t × Fin (m + 1), (fun u => ((κ p.1.1).facePt p.2 u).1) ''
        ((κ p.1.1).faceSet p.2 ∩ (fun u => ((κ p.1.1).facePt p.2 u).1) ⁻¹' N) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨p, u, hu, hyu, -⟩ := hcover y hy
        refine mem_iUnion.2 ⟨p, u, ⟨hu, ?_⟩, hyu⟩
        change ((κ p.1.1).facePt p.2 u).1 ∈ N
        rw [hyu]; exact hy
      · obtain ⟨p, hp⟩ := mem_iUnion.1 hy
        obtain ⟨u, hu, rfl⟩ := hp
        exact hu.2
    rw [e]
    exact isLindelof_iUnion fun p =>
      (HereditarilyLindelofSpace.isLindelof _).image_of_continuousOn
        (continuous_subtype_val.comp_continuousOn
          (((κ p.1.1).continuousOn_facePt p.2).mono inter_subset_left))
  obtain ⟨D⟩ := FormEval.exists_chartCover_of_isLindelof (F := F) hNs hne hL
  refine ⟨hNs, D, fun ω => ?_⟩
  obtain ⟨η, hη0, hηv⟩ := hη ω
  set g : t × Fin (m + 1) → EuclideanSpace ℝ (Fin m) → ℝ := fun p u =>
    facePullback p.2 (ManifoldForm.chartForm (𝓠 (m + 1)) (κ p.1.1).toQuadrantChart η) u
      (stdFrame m) with hg
  set S : t × Fin (m + 1) → Set (EuclideanSpace ℝ (Fin m)) := fun p =>
    faceEmbedding p.2 ⁻¹' ((κ p.1.1).toQuadrantChart.extend (𝓠 (m + 1)) '' L p.1.1) with hS
  have hgS : ∀ p, ∫⁻ u in S p, ENNReal.ofReal |g p u| < ⊤ := fun p => by
    have hI := integrableOn_facePullback_of_isCompact hch hη0 (κ p.1.1) p.2 (hLc p.1.1)
      (hLs p.1.1)
    have h2 := (hasFiniteIntegral_iff_norm _).1 hI.hasFiniteIntegral
    simpa only [Real.norm_eq_abs] using h2
  have hNb : MeasurableSet[borel Obj] N := hNs.1.measurableSet_borel
  set A : ℕ → t × Fin (m + 1) → Set (EuclideanSpace ℝ (Fin m)) := fun k p =>
    (κ p.1.1).faceSet p.2 ∩ (fun u => ((κ p.1.1).facePt p.2 u).1) ⁻¹' (D.P k ∩ G p.1.1)
    with hA
  have hAm : ∀ k p, MeasurableSet (A k p) := fun k p =>
    measurableSet_faceSet_inter_preimage (κ p.1.1) p.2
      (@MeasurableSet.inter Obj (borel Obj) _ _ (D.measurableSet_P hNb k)
        (MeasurableSpace.measurableSet_generateFrom (hGo p.1.1)))
  have hAS : ∀ k p, A k p ⊆ S p := fun k p u hu =>
    ⟨(κ p.1.1).facePt p.2 u, interior_subset (hmemL p.1.1 _ hu.2.2),
      CornerCoords.extend_facePt hu.1⟩
  have hdisj : ∀ p, Pairwise (Function.onFun Disjoint fun k => A k p) := fun p k k' hkk' =>
    disjoint_left.2 fun u hu hu' => disjoint_left.1 (D.disjoint_P hkk') hu.2.1 hu'.2.1
  -- the change of variables, one piece and one face at a time
  have hcv : ∀ k p, ∫⁻ v in (fun u => (chart (D.mem k)).coord ((κ p.1.1).facePt p.2 u).1) ''
      A k p, ENNReal.ofReal |F.ev ω ((chart (D.mem k)).tvec ((chart (D.mem k)).q v))| =
      ∫⁻ u in A k p, ENNReal.ofReal |g p u| := by
    intro k p
    set c := chart (D.mem k) with hc
    set κp := κ p.1.1 with hκp
    set l := p.2 with hl
    have hyN : ∀ u ∈ A k p, (κp.facePt l u).1 ∈ N ∩ D.V k := fun u hu => D.P_subset k hu.2.1
    let DN : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      fun u => c.p.comp ((modelDeriv κp c.isChart (hM.1.data (κp.facePt l u).2).toSubData
        (κp.facePt l u) (levelLift κp.χ 1 (κp.facePt l u))).comp (faceEmbedding l))
    have hderiv : ∀ u ∈ A k p, HasFDerivWithinAt (fun u => c.coord (κp.facePt l u).1) (DN u)
        (A k p) u := fun u hu =>
      (hasFDerivWithinAt_coord_facePt (hcs := hcs) c hM.1 κp l hu.1
        (c.subset_source (hyN u hu))).mono inter_subset_left
    have hinj : InjOn (fun u => c.coord (κp.facePt l u).1) (A k p) := by
      intro u hu u' hu' h
      have h1 := c.injOn_coord (hyN u hu) (hyN u' hu') h
      exact CornerCoords.facePt_injOn hu.1 hu'.1 (Subtype.ext h1)
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hAm k p) hderiv hinj]
    refine setLIntegral_congr_fun (hAm k p) fun u hu => ?_
    have hβ : ∀ j, faceFrame hcs κp (CornerCoords.facePt_mem_s hu.1) l j ∈
        X.PObj.submanifoldTangent (N ∩ D.V k) (κp.facePt l u).1 := fun j => by
      have hyV : (κp.facePt l u).1 ∈ V ∩ D.V k := ⟨(hyN u hu).1.2, (hyN u hu).2⟩
      have e : N ∩ D.V k = X.PObj.boundaryStratum M ∩ (V ∩ D.V k) := inter_assoc _ _ _
      rw [e, submanifoldTangent_inter_isOpen (hV.inter (D.isOpen k)) hyV]
      exact faceFrame_mem_tangent hM ht κp (CornerCoords.facePt_mem_facePiece hu.1)
        (CornerCoords.coord_facePt_self hu.1) j
    have h1 := F.abs_ev_faceFrame hM (D.mem k).1 c ω κp l hu.1 (hyN u hu) hβ
    have h2 := F.facePullback_eq_ev_faceFrame hch ω η hηv κp l hu.1
    simp only [c.q_coord' (hyN u hu)]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← h1]
    change _ = ENNReal.ofReal |facePullback l (ManifoldForm.chartForm (𝓠 (m + 1))
      κp.toQuadrantChart η) u (stdFrame m)|
    rw [h2]
  -- the bound
  set a : ℕ → ENNReal := fun k => ∫⁻ v in (chart (D.mem k)).coord '' (D.P k ∩ (N ∩ D.V k)),
    ENNReal.ofReal |F.ev ω ((chart (D.mem k)).tvec ((chart (D.mem k)).q v))| with ha_def
  have hcovk : ∀ k, (chart (D.mem k)).coord '' (D.P k ∩ (N ∩ D.V k)) ⊆
      ⋃ p : t × Fin (m + 1),
        (fun u => (chart (D.mem k)).coord ((κ p.1.1).facePt p.2 u).1) '' A k p := by
    rintro k _ ⟨y, hy, rfl⟩
    obtain ⟨p, u, hu, hyu, hyG⟩ := hcover y (D.P_subset k hy.1).1
    refine mem_iUnion.2 ⟨p, u, ⟨hu, ?_⟩, ?_⟩
    · change ((κ p.1.1).facePt p.2 u).1 ∈ D.P k ∩ G p.1.1
      rw [hyu]; exact ⟨hy.1, hyG⟩
    · change (chart (D.mem k)).coord ((κ p.1.1).facePt p.2 u).1 = _
      rw [hyu]
  have ha : ∀ k, a k ≤ ∑' p : t × Fin (m + 1), ∫⁻ u in A k p, ENNReal.ofReal |g p u| :=
    fun k => (lintegral_mono_set (hcovk k)).trans ((lintegral_iUnion_le _ _).trans
      (le_of_eq (tsum_congr fun p => hcv k p)))
  have hp : ∀ p : t × Fin (m + 1),
      ∑' k, ∫⁻ u in A k p, ENNReal.ofReal |g p u| ≤ ∫⁻ u in S p, ENNReal.ofReal |g p u| :=
    fun p => by
      rw [← lintegral_iUnion (fun k => hAm k p) (hdisj p)]
      exact lintegral_mono_set (iUnion_subset fun k => hAS k p)
  have hsum : ∑' k, a k ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum ha)
    rw [ENNReal.tsum_comm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hp)
    rw [tsum_fintype]
    exact (ENNReal.sum_lt_top.2 fun p _ => hgS p).ne
  have hEq : ∀ k, F.chartAbs (chart (D.mem k)) ω (D.P k) = (a k).toReal := fun k => by
    unfold chartAbs
    refine integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => abs_nonneg _) ?_
    exact ((integrableOn_chart (D.mem k) ω).mono_set
      (image_mono inter_subset_right)).abs.aestronglyMeasurable
  exact (ENNReal.summable_toReal hsum).congr fun k => (hEq k).symm

end EpGroupoid

end Polyfold
