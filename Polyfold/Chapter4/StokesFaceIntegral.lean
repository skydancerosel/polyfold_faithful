import Polyfold.Chapter4.StokesFaceOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199; preprint Theorem 4.28): the boundary term `∑_F ∫_F ω`
(gap G.40, third step), for Mathlib manifolds.

# The boundary integral is the sum of the face integrals

`M` is a manifold modelled on `[0,∞)ⁿ⁺¹`, and `j a : N a → M` (`a` in a finite type) are maps of
manifolds modelled on `[0,∞)ⁿ` which in suitable charts are coordinate face embedding
(`FaceChartPair`, `StokesFaceOrientation`).

* `restrictForm j ω`: the pull-back `j^*ω` (`p ↦ ω(j p) ∘ T_p j`, Mathlib's `mfderiv`);
  `FaceChartPair.mfderiv_eq` computes `T_p j` in a face chart pair, and
  `FaceChartPair.chartForm_restrictForm`: the expression of `j^*ω` in `e_N` is `ιᵢ^*` of the
  expression of `ω` in `e`, the integrand of `chartBoundaryIntegral`.
* `GoodRegion`: an open set `G` in a chart `e` of `M`, signed for `o`, such that the faces `j a`
  meeting `G` read in `e` as distinct coordinate faces `{x_{iₐ} = 0}`, and every point of `G` with
  exactly one vanishing coordinate lies on a face.
* **`sum_integral_restrictForm_eq_boundaryIntegral`**: if every point has a good region, then for
  a `C¹` `n`-form `ω` with compact support
  `∑ₐ ∫_{N a} j_a^*ω = ∫_{∂M} ω` (`ManifoldForm.boundaryIntegral`), each `N a` with the induced
  orientation (`IsInducedOrientation`).
-/

open Set Filter Topology Manifold Module MeasureTheory

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### Forms in the charts of the maximal atlas -/

namespace ManifoldForm

section MaxAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ}

/-- **A `C^r` form is `C^r` in every chart of the maximal atlas** (within `range I`). -/
theorem ContMDiffForm.contDiffWithinAt_of_mem_maximalAtlas {r : WithTop ℕ∞} (hr : r ≤ ∞)
    {ω : ManifoldForm I M k} (hω : ContMDiffForm I r ω) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {p : M} (hp : p ∈ e.source) :
    ContDiffWithinAt ℝ r (chartForm I e ω) (range I) (e.extend I p) := by
  set c := chartAt H p
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) p
  have hpc := mem_chart_source H p
  have hev := chartForm_eventuallyEq_formPullback he hc ω hp hpc
  have hφ := I.contDiffWithinAt_extendCoordChange' (n := ∞) he hc hp hpc
  have hfx : I.extendCoordChange e c (e.extend I p) = c.extend I p := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hp]
  have hmaps : MapsTo (I.extendCoordChange e c) (range I) (range I) := fun z _ => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hyI : e.extend I p ∈ range I := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  have hd : ContDiffWithinAt ℝ r (chartForm I c ω) (range I) (c.extend I p) :=
    hω.contDiffWithinAt p (mem_extChartAt_target p)
  have h1 : ContDiffWithinAt ℝ r (fun z => chartForm I c ω (I.extendCoordChange e c z))
      (range I) (e.extend I p) := by
    rw [← hfx] at hd
    exact hd.comp _ (hφ.of_le hr) hmaps
  have h2 := hφ.fderivWithin_right I.uniqueDiffOn (add_one_le_infty hr) hyI
  exact (ContDiffWithinAt.formPullback' h1 h2).congr_of_eventuallyEq hev
    (hev.self_of_nhdsWithin hyI)

/-- **A continuous form is continuous in every chart of the maximal atlas.** -/
theorem ContMDiffForm.continuousOn_chartForm {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I 0 ω) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContinuousOn (chartForm I e ω) (e.extend I).target := fun y hy => by
  have hp : (e.extend I).symm y ∈ e.source := by
    rw [← e.extend_source (I := I)]; exact (e.extend I).map_target hy
  have h := (hω.contDiffWithinAt_of_mem_maximalAtlas (by simp) he hp).continuousWithinAt
  rw [(e.extend I).right_inv hy] at h
  exact h.mono e.extend_target_subset_range

end MaxAtlas

end ManifoldForm

open ManifoldForm

/-! ### The restriction of a form to a face -/

section Restrict

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant n) N] {k : ℕ}

/-- **The restriction `j^*ω` of a form along `j : N → M`** (2021 Theorem 4.4.7, `∫_F ω`):
`p ↦ ω(j p)(T_p j ·, …, T_p j ·)`, `T_p j` Mathlib's `mfderiv`. -/
def restrictForm (j : N → M) (ω : ManifoldForm (𝓠 (n + 1)) M k) : ManifoldForm (𝓠 n) N k :=
  fun p => (ω (j p)).compContinuousLinearMap (mfderiv (𝓠 n) (𝓠 (n + 1)) j p)

theorem restrictForm_apply (j : N → M) (ω : ManifoldForm (𝓠 (n + 1)) M k) (p : N)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    restrictForm j ω p v = ω (j p) (mfderiv (𝓠 n) (𝓠 (n + 1)) j p ∘ v) := rfl

theorem restrictForm_finsetSum (j : N → M) {ι : Type*} (u : Finset ι)
    (ω : ι → ManifoldForm (𝓠 (n + 1)) M k) :
    restrictForm j (∑ i ∈ u, ω i) = ∑ i ∈ u, restrictForm j (ω i) := by
  funext p
  ext v
  simp [restrictForm]

theorem restrictForm_eq_zero (j : N → M) {ω : ManifoldForm (𝓠 (n + 1)) M k} {p : N}
    (h : ω (j p) = 0) : restrictForm j ω p = 0 := by
  change (ω (j p)).compContinuousLinearMap _ = 0
  rw [h]
  ext v
  rfl

namespace FaceChartPair

variable [IsManifold (𝓠 (n + 1)) ∞ M] [IsManifold (𝓠 n) ∞ N] {j : N → M} (P : FaceChartPair n j)

/-- **The derivative of `j` in a face chart pair**: `T_q j = D(c ∘ e⁻¹) ∘ ιᵢ ∘ D(e_N ∘ c_q⁻¹)`,
`c`, `c_q` the charts at `j q`, `q` in which the tangent spaces are read. -/
theorem mfderiv_eq {q : N} (hj : ContinuousAt j q) (hq : q ∈ P.eN.source) :
    mfderiv (𝓠 n) (𝓠 (n + 1)) j q =
      (chartChangeDeriv (𝓠 (n + 1)) P.e (chartAt (EuclideanQuadrant (n + 1)) (j q)) (j q)).comp
        ((faceEmbedding P.i).comp
          (chartChangeDeriv (𝓠 n) (chartAt (EuclideanQuadrant n) q) P.eN q)) := by
  set cq := chartAt (EuclideanQuadrant n) q
  set cj := chartAt (EuclideanQuadrant (n + 1)) (j q)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hqc : q ∈ cq.source := mem_chart_source _ q
  have hcq := IsManifold.chart_mem_maximalAtlas (I := 𝓠 n) (n := ∞) q
  have hcj := IsManifold.chart_mem_maximalAtlas (I := 𝓠 (n + 1)) (n := ∞) (j q)
  have h1 := hasFDerivWithinAt_chartChangeDeriv hn hcq P.mem_N hqc hq
  have h3 := hasFDerivWithinAt_chartChangeDeriv hn P.mem_M hcj (P.mapsTo q hq)
    (mem_chart_source _ (j q))
  have hpt : faceEmbedding P.i ((𝓠 n).extendCoordChange cq P.eN (cq.extend (𝓠 n) q)) =
      P.e.extend (𝓠 (n + 1)) (j q) := by
    rw [P.extend_eq q hq]
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [cq.extend_left_inv hqc]
  rw [← hpt] at h3
  have hmaps : MapsTo (fun y => faceEmbedding P.i ((𝓠 n).extendCoordChange cq P.eN y))
      (range (𝓠 n)) (range (𝓠 (n + 1))) := fun y _ => mapsTo_faceEmbedding_range P.i (by
    rw [range_modelWithCornersEuclideanQuadrant]
    exact mapsTo_extendCoordChange_range cq P.eN (mem_univ y))
  have hcomp := h3.comp (cq.extend (𝓠 n) q)
    ((faceEmbedding P.i).hasFDerivAt.comp_hasFDerivWithinAt _ h1) hmaps
  have hy0 : cq.extend (𝓠 n) q ∈ range (𝓠 n) := by
    rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _
  have hev : writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) q j =ᶠ[𝓝[range (𝓠 n)] (cq.extend (𝓠 n) q)]
      fun y => (𝓠 (n + 1)).extendCoordChange P.e cj
        (faceEmbedding P.i ((𝓠 n).extendCoordChange cq P.eN y)) := by
    filter_upwards [nhdsWithin_le_nhds
      (cq.extend_preimage_mem_nhds (I := 𝓠 n) hqc (P.eN.open_source.mem_nhds hq))] with y hy
    simp only [writtenInExtChartAt, extChartAt, ModelWithCorners.extendCoordChange,
      PartialEquiv.coe_trans, Function.comp_apply]
    rw [← P.extend_eq _ hy, P.e.extend_left_inv (P.mapsTo _ hy)]
  have hd : HasFDerivWithinAt (writtenInExtChartAt (𝓠 n) (𝓠 (n + 1)) q j)
      ((chartChangeDeriv (𝓠 (n + 1)) P.e cj (j q)).comp
        ((faceEmbedding P.i).comp (chartChangeDeriv (𝓠 n) cq P.eN q)))
      (range (𝓠 n)) (cq.extend (𝓠 n) q) :=
    hcomp.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hy0)
  have hmd : MDifferentiableAt (𝓠 n) (𝓠 (n + 1)) j q :=
    (mdifferentiableAt_iff j q).2 ⟨hj, hd.differentiableWithinAt⟩
  rw [hmd.mfderiv]
  exact hd.fderivWithin (𝓠 n).uniqueDiffWithinAt_image

/-- **The expression of `j^*ω` in a face chart `e_N`** is `ιᵢ^*` of the expression of `ω` in `e`,
on the target of `e_N`. -/
theorem chartForm_restrictForm (hj : Continuous j) (ω : ManifoldForm (𝓠 (n + 1)) M k)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ (P.eN.extend (𝓠 n)).target) :
    chartForm (𝓠 n) P.eN (restrictForm j ω) z =
      formPullback (faceEmbedding P.i) (fun _ => faceEmbedding P.i)
        (chartForm (𝓠 (n + 1)) P.e ω) z := by
  set q := (P.eN.extend (𝓠 n)).symm z with hq_def
  have hq : q ∈ P.eN.source := by
    rw [← P.eN.extend_source (I := 𝓠 n)]; exact (P.eN.extend (𝓠 n)).map_target hz
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcq := IsManifold.chart_mem_maximalAtlas (I := 𝓠 n) (n := ∞) q
  have hcomp := chartChangeDeriv_comp_self hn P.mem_N hcq hq (mem_chart_source _ q)
  have hm := P.mfderiv_eq hj.continuousAt hq
  have key : ∀ v, mfderiv (𝓠 n) (𝓠 (n + 1)) j q
      (chartChangeDeriv (𝓠 n) P.eN (chartAt (EuclideanQuadrant n) q) q v) =
      chartChangeDeriv (𝓠 (n + 1)) P.e (chartAt (EuclideanQuadrant (n + 1)) (j q)) (j q)
        (faceEmbedding P.i v) := fun v => by
    have hBv : chartChangeDeriv (𝓠 n) (chartAt (EuclideanQuadrant n) q) P.eN q
        (chartChangeDeriv (𝓠 n) P.eN (chartAt (EuclideanQuadrant n) q) q v) = v :=
      congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => L v) hcomp
    rw [hm]
    exact congrArg (fun w => chartChangeDeriv (𝓠 (n + 1)) P.e
      (chartAt (EuclideanQuadrant (n + 1)) (j q)) (j q) (faceEmbedding P.i w)) hBv
  ext v
  rw [chartForm_apply, formPullback_apply, chartForm_apply, P.symm_eq hz, ← hq_def]
  exact congrArg (ω (j q)) (funext fun l => key (v l))

/-- **The restriction of a continuous form is continuous**, if `N` is covered by face chart
pairs. -/
theorem _root_.Polyfold.contMDiffForm_restrictForm (hj : Continuous j)
    (hcover : ∀ p : N, ∃ P : FaceChartPair n j, p ∈ P.eN.source)
    {ω : ManifoldForm (𝓠 (n + 1)) M k} (hω : ContMDiffForm (𝓠 (n + 1)) 0 ω) :
    ContMDiffForm (𝓠 n) 0 (restrictForm j ω) := by
  refine contMDiffForm_of_local (by simp) fun p => ?_
  obtain ⟨P, hp⟩ := hcover p
  refine ⟨P.eN, P.mem_N, hp, ?_⟩
  have hz : P.eN.extend (𝓠 n) p ∈ (P.eN.extend (𝓠 n)).target :=
    (P.eN.extend (𝓠 n)).map_source (by rw [P.eN.extend_source]; exact hp)
  have hT := P.eN.extend_target_mem_nhdsWithin (I := 𝓠 n) hp
  have hc := hω.contDiffWithinAt_of_mem_maximalAtlas (by simp) P.mem_M (P.mapsTo p hp)
  rw [P.extend_eq p hp] at hc
  have h1 : ContDiffWithinAt ℝ 0 (fun z => chartForm (𝓠 (n + 1)) P.e ω (faceEmbedding P.i z))
      (range (𝓠 n)) (P.eN.extend (𝓠 n) p) :=
    hc.comp _ (faceEmbedding P.i).contDiff.contDiffWithinAt (mapsTo_faceEmbedding_range P.i)
  refine (ContDiffWithinAt.formPullback' h1 contDiffWithinAt_const).congr_of_eventuallyEq ?_
    (P.chartForm_restrictForm hj ω hz)
  filter_upwards [hT] with z hz' using P.chartForm_restrictForm hj ω hz'

end FaceChartPair

end Restrict

/-! ### Integrals in the charts of the maximal atlas -/

namespace ManifoldForm

section IntegralMaxAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

theorem chartIntegral_eq_zero {ω : ManifoldForm (𝓠 n) M n} (h : ∀ x, ω x = 0)
    (e : OpenPartialHomeomorph M (EuclideanQuadrant n)) : chartIntegral e ω = 0 := by
  have h0 : ∀ y, chartForm (𝓠 n) e ω y = 0 := fun y =>
    chartForm_eq_zero_of_notMem (K := ∅) (fun x _ => h x) e (notMem_empty _)
  simp [chartIntegral, topFormIntegral, h0]

/-- The integral of the zero form vanishes. -/
theorem integral_eq_zero {o : TangentOrientation (𝓠 n) M n} {ω : ManifoldForm (𝓠 n) M n}
    (h : ∀ x, ω x = 0) : integral o ω = 0 := by
  unfold integral
  split_ifs with hD
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [chartIntegral_eq_zero (fun x => by rw [smulFun_apply, h x, smul_zero]), mul_zero]
  · rfl

variable [IsManifold (𝓠 n) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {o : TangentOrientation (𝓠 n) M n}

/-- **A form supported in a signed chart of the maximal atlas**: if `ω` (continuous) vanishes
outside a compact `K` inside a region `V` of a chart `e` of the maximal atlas on which `o` reads
as `signedOr b (stdOrientation n)`, then `∫_M ω = orSign b · ∫_e ω` (`integral_eq_chartIntegral`
for the charts `chartAt`). -/
theorem integral_eq_chartIntegral_of_mem_maximalAtlas (ho : o.IsContinuous (𝓠 n) ∞)
    {ω : ManifoldForm (𝓠 n) M n} (hω : ContMDiffForm (𝓠 n) 0 ω)
    {e : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M) {V : Set M} (hV : V ⊆ e.source) {b : Bool}
    (hb : ∀ x ∈ V, orientationIn e x (o x) = signedOr b (stdOrientation n))
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V) (hω0 : ∀ x ∉ K, ω x = 0) :
    integral o ω = orSign b * chartIntegral e ω := by
  have hsK : tsupport ω ⊆ K :=
    closure_minimal (fun x hx => by_contra fun h => hx (hω0 x h)) hK.isClosed
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hK
  rw [integral_eq_integrationData ho hω (hK.of_isClosed_subset isClosed_closure hsK) D hsK]
  have step : ∀ k, orSign (D.sign k) * chartIntegral (D.chart k) (smulFun (D.ρ k) ω) =
      orSign b * chartIntegral e (smulFun (D.ρ k) ω) :=
    fun k => orSign_mul_chartIntegral_eq he (IsManifold.chart_mem_maximalAtlas (D.center k))
      (K := _root_.tsupport (D.ρ k) ∩ K)
      (fun x hx => ⟨hV (hKV hx.2), D.region_subset k (D.tsupport_subset k hx.1)⟩)
      (fun x hx => smulFun_eq_zero_of_notMem hω0 hx) (fun x hx => hb x (hKV hx.2))
      (fun x hx => D.orientationIn_eq k x (D.tsupport_subset k hx.1))
  rw [IntegrationData.integral, Finset.sum_congr rfl fun k _ => step k, ← Finset.mul_sum,
    ← chartIntegral_finsetSum Finset.univ
      (fun k _ => (D.contMDiffForm_smulFun (by simp) k hω).continuousOn_chartForm he)
      (fun k _ => hK.inter_left (isClosed_tsupport (D.ρ k)))
      (fun k _ => fun x hx => hV (hKV hx.2))
      (fun k _ => fun x hx => smulFun_eq_zero_of_notMem hω0 hx),
    finsetSum_smulFun_eq_self Finset.univ D.sum_eq_one subset_rfl hω0]

omit [IsManifold (𝓠 n) ∞ M] [T2Space M] [SigmaCompactSpace M] in
/-- **Integration data with prescribed signed regions**: if every `x` has an open neighbourhood
`V x` in the source of `chartAt x` on which `o` reads as `signedOr (b x) (stdOrientation n)`,
there are integration data on a compact `s` whose charts, regions and signs are
`chartAt x`, `V x`, `b x` (the proof of `exists_integrationData`). -/
theorem exists_integrationData_of_regions [IsManifold (𝓠 n) ∞ M] [T2Space M]
    [SigmaCompactSpace M] {s : Set M} (hs : IsCompact s) (V : M → Set M)
    (hVo : ∀ x, IsOpen (V x)) (hxV : ∀ x, x ∈ V x)
    (hV : ∀ x, V x ⊆ (chartAt (EuclideanQuadrant n) x).source) (b : M → Bool)
    (hb : ∀ x, ∀ y ∈ V x, orientationIn (chartAt (EuclideanQuadrant n) x) y (o y) =
      signedOr (b x) (stdOrientation n)) :
    ∃ T : Finset M, ∃ D : IntegrationData M o s {x // x ∈ T},
      ∀ k, D.center k = k.1 ∧ D.region k = V k.1 ∧ D.sign k = b k.1 := by
  classical
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓠 n) isClosed_univ V hVo
    fun x _ => mem_iUnion.2 ⟨x, hxV x⟩
  have hT := f.locallyFinite.finite_nonempty_inter_compact hs
  refine ⟨hT.toFinset, {
    center := fun k => k.1
    region := fun k => V k.1
    region_subset := fun k => hV k.1
    sign := fun k => b k.1
    orientationIn_eq := fun k => hb k.1
    ρ := fun k => f k.1
    contMDiff_ρ := fun k => (f k.1).contMDiff
    tsupport_subset := fun k => hf k.1
    sum_eq_one := fun x hx => ?_ }, fun k => ⟨rfl, rfl, rfl⟩⟩
  rw [Finset.sum_coe_sort hT.toFinset (fun i => f i x), ← f.sum_eq_one (mem_univ x)]
  refine (finsum_eq_sum_of_support_subset _ fun i hi => ?_).symm
  rw [Set.Finite.coe_toFinset]
  exact ⟨x, hi, hx⟩

end IntegralMaxAtlas

end ManifoldForm

/-! ### Good regions -/

section Good

open Classical in
theorem decide_signedOr_stdOrientation (m : ℕ) (b : Bool) :
    decide (signedOr b (stdOrientation m) = stdOrientation m) = b := by
  cases b
  · rw [signedOr_false]
    exact decide_eq_false fun (h : -stdOrientation m = stdOrientation m) =>
      Module.Ray.ne_neg_self (stdOrientation m) h.symm
  · simp

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  {α : Type*} {N : α → Type*} [∀ a, TopologicalSpace (N a)]
  [∀ a, ChartedSpace (EuclideanQuadrant n) (N a)]

theorem FaceChartPair.boundarySign_eq {N' : Type*} [TopologicalSpace N']
    [ChartedSpace (EuclideanQuadrant n) N'] {j' : N' → M}
    (o : TangentOrientation (𝓠 (n + 1)) M (n + 1)) (P : FaceChartPair n j') {p : N'} {b : Bool}
    (h : orientationIn P.e (j' p) (o (j' p)) = signedOr b (stdOrientation (n + 1))) :
    P.boundarySign o p = (b == faceBool P.i) := by
  unfold FaceChartPair.boundarySign
  rw [h, decide_signedOr_stdOrientation]

variable (o : TangentOrientation (𝓠 (n + 1)) M (n + 1)) (j : ∀ a, N a → M)
  (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (G : Set M)

/-- **A good region** `G` of a chart `e` of `M` for the faces `j a : N a → M`: `o` reads in `e` on
`G` as `orSign b` times the standard orientation; the faces meeting `G` (a finite set `faces`)
have face chart pairs `(e_{N a}, e, iₐ)` whose sources contain `j_a⁻¹(G)`, with distinct
coordinates `iₐ`; and every point of `G` with exactly one vanishing coordinate in `e` lies on a
face.  (For the faces of a compact tame `N ⊆ X` these are the small neighbourhoods built in
`StokesFaceSum` from 2021 Proposition 2.7.5 and Lemma 2.5.12.) -/
structure GoodRegion where
  /-- The sign of `o` in `e` on `G`. -/
  sign : Bool
  orientationIn_eq : ∀ x ∈ G, orientationIn e x (o x) = signedOr sign (stdOrientation (n + 1))
  subset_source : G ⊆ e.source
  /-- The faces meeting `G`. -/
  faces : Finset α
  /-- Their face chart pairs. -/
  pair : ∀ a ∈ faces, FaceChartPair n (j a)
  pair_e : ∀ a (h : a ∈ faces), (pair a h).e = e
  src : ∀ a (h : a ∈ faces) (p : N a), j a p ∈ G → p ∈ (pair a h).eN.source
  miss : ∀ a ∉ faces, ∀ p : N a, j a p ∉ G
  inj : ∀ a (h : a ∈ faces) a' (h' : a' ∈ faces), (pair a h).i = (pair a' h').i → a = a'
  cover : ∀ x ∈ G, ∀ i : Fin (n + 1), e.extend (𝓠 (n + 1)) x i = 0 →
    (∀ l ≠ i, 0 < e.extend (𝓠 (n + 1)) x l) → ∃ a, ∃ p : N a, j a p = x

namespace GoodRegion

variable {o j e G} (g : GoodRegion o j e G) {η : ManifoldForm (𝓠 (n + 1)) M n} {K : Set M}
  (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0)
include hKG hη0

/-- A point of the open face `i` of `e` where the integrand of the boundary integral does not
vanish is `e_{N a}(p)` for the face `a` with `iₐ = i`. -/
theorem exists_of_ne_zero {i : Fin (n + 1)} {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ openFaceDomain e i) (hne : facePullback i (chartForm (𝓠 (n + 1)) e η) z ≠ 0) :
    ∃ a, ∃ h : a ∈ g.faces, (g.pair a h).i = i ∧
      ∃ p ∈ (g.pair a h).eN.source, (g.pair a h).eN.extend (𝓠 n) p = z := by
  have hzD : z ∈ faceDomain e i := openFaceDomain_subset e i hz
  have hx : facePoint e i z ∈ K := by
    by_contra hK
    apply hne
    ext v
    rw [facePullback, formPullback_apply,
      chartForm_eq_zero_of_notMem (y := faceEmbedding i z) hη0 e hK]
    rfl
  have hxe := extend_facePoint hzD
  obtain ⟨a, p, hp⟩ := g.cover _ (hKG hx) i (by rw [hxe]; exact faceEmbedding_apply_self _ _)
    fun l hl => by
      rw [hxe]
      obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hl
      rw [faceEmbedding_apply_succAbove]
      exact hz.2 m (mem_univ m)
  have hpG : j a p ∈ G := hp ▸ hKG hx
  have ha : a ∈ g.faces := by
    by_contra h
    exact g.miss a h p hpG
  have hpP := g.src a ha p hpG
  have hext := (g.pair a ha).extend_eq p hpP
  rw [g.pair_e a ha, hp, hxe] at hext
  have hi : (g.pair a ha).i = i := by
    have h0 : faceEmbedding i z (g.pair a ha).i = 0 := by
      rw [hext]; exact faceEmbedding_apply_self _ _
    exact (faceEmbedding_eq_zero_iff hz _).1 h0
  refine ⟨a, ha, hi, p, hpP, ?_⟩
  rw [hi] at hext
  have := congrArg (faceProjection i) hext
  rwa [faceProjection_faceEmbedding, faceProjection_faceEmbedding, eq_comm] at this

/-- The boundary integral over the open face `iₐ` of `e` is the integral over the target of the
face chart `e_{N a}`. -/
theorem faceIntegral_eq (a : α) (ha : a ∈ g.faces) :
    topFormIntegral (openFaceDomain e (g.pair a ha).i)
        (facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η)) =
      topFormIntegral ((g.pair a ha).eN.extend (𝓠 n)).target
        (facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η)) := by
  have hW : ((g.pair a ha).eN.extend (𝓠 n)).target ∩ openQuadrant univ ⊆
      openFaceDomain e (g.pair a ha).i := fun z hz => by
    have hp : ((g.pair a ha).eN.extend (𝓠 n)).symm z ∈ (g.pair a ha).eN.source := by
      rw [← (g.pair a ha).eN.extend_source (I := 𝓠 n)]
      exact ((g.pair a ha).eN.extend (𝓠 n)).map_target hz.1
    have h := (g.pair a ha).faceEmbedding_mem_target hp
    rw [((g.pair a ha).eN.extend (𝓠 n)).right_inv hz.1, g.pair_e a ha, e.extend_target] at h
    exact ⟨h.1, hz.2⟩
  rw [topFormIntegral_eq_of_subset (isOpen_openFaceDomain e _).measurableSet hW fun z hz => by
    by_contra hne
    obtain ⟨a', ha', hi', p, hp, rfl⟩ := g.exists_of_ne_zero hKG hη0 hz.1 hne
    obtain rfl : a' = a := g.inj a' ha' a ha hi'
    exact hz.2 ⟨PartialEquiv.map_source _ (by rw [OpenPartialHomeomorph.extend_source]; exact hp),
      hz.1.2⟩]
  unfold topFormIntegral
  refine setIntegral_congr_set ?_
  have hsub : ((g.pair a ha).eN.extend (𝓠 n)).target ⊆ closedQuadrant univ := by
    rw [← range_modelWithCornersEuclideanQuadrant]
    exact (g.pair a ha).eN.extend_target_subset_range
  have h := (EventuallyEq.refl (ae volume) ((g.pair a ha).eN.extend (𝓠 n)).target).inter
    (openQuadrant_ae_eq_quadrant (S := univ))
  rwa [inter_eq_left.2 hsub] at h

/-- The boundary integral over an open face of `e` which is no `iₐ` vanishes. -/
theorem faceIntegral_eq_zero (i : Fin (n + 1)) (hi : ∀ a (h : a ∈ g.faces), (g.pair a h).i ≠ i) :
    topFormIntegral (openFaceDomain e i) (facePullback i (chartForm (𝓠 (n + 1)) e η)) = 0 := by
  rw [topFormIntegral_eq_of_subset (isOpen_openFaceDomain e i).measurableSet (empty_subset _)
    fun z hz => by_contra fun hne => by
      obtain ⟨a, ha, hi', -⟩ := g.exists_of_ne_zero hKG hη0 hz.1 hne
      exact hi a ha hi']
  simp [topFormIntegral]

omit hKG hη0

variable [IsManifold (𝓠 (n + 1)) ∞ M] [∀ a, IsManifold (𝓠 n) ∞ (N a)] [T2Space M]
  [∀ a, T2Space (N a)] [∀ a, CompactSpace (N a)] (hj : ∀ a, Continuous (j a))
  (hcover : ∀ a (p : N a), ∃ P : FaceChartPair n (j a), p ∈ P.eN.source)
  {oN : ∀ a, TangentOrientation (𝓠 n) (N a) n} (hoN : ∀ a, IsInducedOrientation (j a) o (oN a))
  (hoNc : ∀ a, (oN a).IsContinuous (𝓠 n) ∞)
include hj hcover hoN hoNc

/-- The integral over the face `a` of the restriction of a form supported in `G` is
`orSign b · faceSign iₐ` times the integral of its expression over the face chart target. -/
theorem integral_restrictForm_eq (hη : ContMDiffForm (𝓠 (n + 1)) 0 η) (hK : IsCompact K)
    (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) (a : α) (ha : a ∈ g.faces) :
    integral (oN a) (restrictForm (j a) η) = orSign g.sign * faceSign (g.pair a ha).i *
      topFormIntegral ((g.pair a ha).eN.extend (𝓠 n)).target
        (facePullback (g.pair a ha).i (chartForm (𝓠 (n + 1)) e η)) := by
  have hb : ∀ p ∈ (g.pair a ha).eN.source ∩ j a ⁻¹' G,
      orientationIn (g.pair a ha).eN p (oN a p) =
        signedOr (g.sign == faceBool (g.pair a ha).i) (stdOrientation n) := fun p hp => by
    rw [hoN a (g.pair a ha) p hp.1, (g.pair a ha).boundarySign_eq o (b := g.sign)]
    rw [g.pair_e a ha]
    exact g.orientationIn_eq _ hp.2
  have hK' : IsCompact (j a ⁻¹' K) := (hK.isClosed.preimage (hj a)).isCompact
  rw [integral_eq_chartIntegral_of_mem_maximalAtlas (hoNc a)
    (contMDiffForm_restrictForm (hj a) (hcover a) hη) (g.pair a ha).mem_N inter_subset_left hb
    hK' (fun p hp => ⟨g.src a ha p (hKG hp), hKG hp⟩)
    (fun p hp => restrictForm_eq_zero _ (hη0 _ hp)), orSign_beq, orSign_faceBool, chartIntegral,
    topFormIntegral_congr (measurableSet_extend_target (g.pair a ha).eN)
      fun z hz => (g.pair a ha).chartForm_restrictForm (hj a) η hz, g.pair_e a ha]
  rfl

/-- **The local identity**: for a continuous `n`-form `η` vanishing outside a compact subset of
the good region `G`, `∑ₐ ∫_{N a} j_a^*η = orSign b · ∑ᵢ faceSign i ∫ ιᵢ^*(e⁻¹)^*η`. -/
theorem sum_integral_eq [Fintype α] (hη : ContMDiffForm (𝓠 (n + 1)) 0 η) (hK : IsCompact K)
    (hKG : K ⊆ G) (hη0 : ∀ x ∉ K, η x = 0) :
    ∑ a, integral (oN a) (restrictForm (j a) η) = orSign g.sign * chartBoundaryIntegral e η := by
  classical
  set f : Fin (n + 1) → ℝ := fun i => faceSign i *
    topFormIntegral (openFaceDomain e i) (facePullback i (chartForm (𝓠 (n + 1)) e η)) with hf
  have hsplit : ∑ a, integral (oN a) (restrictForm (j a) η) =
      ∑ a ∈ g.faces, integral (oN a) (restrictForm (j a) η) :=
    (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => integral_eq_zero fun p =>
      restrictForm_eq_zero _ (hη0 _ fun hpK => g.miss a ha p (hKG hpK))).symm
  have hterm : ∀ a : g.faces, integral (oN a) (restrictForm (j a) η) =
      orSign g.sign * f (g.pair a.1 a.2).i := fun a => by
    rw [g.integral_restrictForm_eq hj hcover hoN hoNc hη hK hKG hη0 a.1 a.2,
      ← g.faceIntegral_eq hKG hη0 a.1 a.2, hf, mul_assoc]
  rw [hsplit, ← Finset.sum_attach, Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
    chartBoundaryIntegral_eq_sum_openQuadrant]
  congr 1
  have hinj : Set.InjOn (fun a : g.faces => (g.pair a.1 a.2).i) g.faces.attach := by
    intro a _ a' _ h
    exact Subtype.ext (g.inj _ _ _ _ h)
  rw [← Finset.sum_image hinj]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  change faceSign i * _ = 0
  rw [g.faceIntegral_eq_zero hKG hη0 i fun a ha h =>
    hi (Finset.mem_image.2 ⟨⟨a, ha⟩, Finset.mem_attach _ _, h⟩), mul_zero]

end GoodRegion

/-- **The faces cover `N`**: every point of `N a` lies in a face chart pair (of the good region
at its image). -/
theorem exists_faceChartPair_of_goodRegion {G : M → Set M} (hxG : ∀ x, x ∈ G x)
    (good : ∀ x, GoodRegion o j (chartAt (EuclideanQuadrant (n + 1)) x) (G x)) (a : α)
    (p : N a) : ∃ P : FaceChartPair n (j a), p ∈ P.eN.source := by
  have ha : a ∈ (good (j a p)).faces := by
    by_contra h
    exact (good (j a p)).miss a h p (hxG _)
  exact ⟨(good (j a p)).pair a ha, (good (j a p)).src a ha p (hxG _)⟩

variable [IsManifold (𝓠 (n + 1)) ∞ M] [∀ a, IsManifold (𝓠 n) ∞ (N a)] [T2Space M]
  [SigmaCompactSpace M] [∀ a, T2Space (N a)] [∀ a, CompactSpace (N a)] [Fintype α]

/-- **The boundary integral is the sum of the face integrals** (the right-hand side of 2021
Theorem 4.4.7, p. 199; preprint Theorem 4.28): if every point of `M` has a good region for the
faces `j a : N a → M` (compact, with the induced orientations `o_N a`), then for a `C¹` `n`-form
`ω` with compact support, `∑ₐ ∫_{N a} j_a^*ω = ∫_{∂M} ω`. -/
theorem sum_integral_restrictForm_eq_boundaryIntegral (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    (hj : ∀ a, Continuous (j a)) {oN : ∀ a, TangentOrientation (𝓠 n) (N a) n}
    (hoN : ∀ a, IsInducedOrientation (j a) o (oN a)) (hoNc : ∀ a, (oN a).IsContinuous (𝓠 n) ∞)
    (G : M → Set M) (hGo : ∀ x, IsOpen (G x)) (hxG : ∀ x, x ∈ G x)
    (good : ∀ x, GoodRegion o j (chartAt (EuclideanQuadrant (n + 1)) x) (G x))
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hc : IsCompact (tsupport ω)) :
    ∑ a, integral (oN a) (restrictForm (j a) ω) = boundaryIntegral o ω := by
  have hcover := exists_faceChartPair_of_goodRegion o j hxG good
  obtain ⟨T, D, hD⟩ := exists_integrationData_of_regions (o := o) hc G hGo hxG
    (fun x => (good x).subset_source) (fun x => (good x).sign)
    (fun x => (good x).orientationIn_eq)
  rw [boundaryIntegral_eq_integrationData ho hω hc D subset_rfl, IntegrationData.boundaryIntegral]
  have hω0 : ∀ x ∉ tsupport ω, ω x = 0 := fun x hx => eq_zero_of_notMem_tsupport hx
  have hC0 : ∀ k, ContMDiffForm (𝓠 (n + 1)) 0 (smulFun (D.ρ k) ω) := fun k =>
    D.contMDiffForm_smulFun (by simp) k (hω.of_le zero_le_one)
  have hlin : ∀ a, integral (oN a) (restrictForm (j a) ω) =
      ∑ k, integral (oN a) (restrictForm (j a) (smulFun (D.ρ k) ω)) := fun a => by
    have hs := finsetSum_smulFun_eq_self Finset.univ D.sum_eq_one subset_rfl hω0
    conv_lhs => rw [← hs, restrictForm_finsetSum]
    exact integral_finsetSum (hoNc a) Finset.univ
      (fun k _ => contMDiffForm_restrictForm (hj a) (hcover a) (hC0 k))
      (fun k _ => isClosed_closure.isCompact)
  rw [Finset.sum_congr rfl fun a _ => hlin a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨hck, hrk, hsk⟩ := hD k
  have hloc := (good k.1).sum_integral_eq hj hcover hoN hoNc (hC0 k)
    (hc.inter_left (isClosed_tsupport (D.ρ k)))
    (fun x hx => hrk ▸ D.tsupport_subset k hx.1) (fun x hx => smulFun_eq_zero_of_notMem hω0 hx)
  rw [hloc, hsk, IntegrationData.chart, hck]

end Good

end Polyfold
