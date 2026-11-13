import Polyfold.Chapter9.BoundaryIntegralStratum
import Polyfold.Chapter9.ZeroFormValues

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, proof of Theorem 9.5.18 (pp. 450–451; gap G.110) for `n = 1`, with Definition
9.3.8 (boundary orientation, p. 426) and Part I, Theorem 4.4.7 (p. 199).  Numbers and pages are
the 2021 text's.

# Part I's boundary integral of a `0`-form over a `1`-dimensional sheet

For `n = 1` the last equality of the display on p. 451 reads: Part I's boundary integral
`∫_{∂(M, o)} f` of a function (a `0`-form) over a tame `1`-dimensional sheet `M` is `±f(p)` when
the boundary stratum `∂₁M` is one point `p`, the sign `+` iff the boundary orientation
`o_{∂M}` of Definition 9.3.8 at `p` is positive, and `0` when `∂₁M = ∅`.  This is E1's integral
over oriented points (`EpGroupoid.pointInteg`).  E8F's `FormEval.boundaryIntegral_eq_msInteg`
needs `0 < m`: an `m`-form evaluation `FormEval` reads a `0`-form on the empty frame, which
carries no base point.  Here the `0`-form is a function `f` on the objects.

* `setIntegral_euclideanSpace_fin_zero`: `∫_S g = g(0)` or `0` on `ℝ⁰` (Lebesgue measure on
  `ℝ⁰` is the Dirac measure).
* `orSign_mul_faceSign_mul_facePullback_eq_dim1`, `face_term_eq_dim1`: one chart, one face.
* **`boundaryIntegral_eq_pointInteg`**: `∫_{∂(M, o)} η = ∫_{∂₁M} f|(∂₁M, o_{∂M})` for a `C¹`
  Mathlib `0`-form `η` on `M` with compact support and values `f`, when `∂₁M` has at most one
  point.
* **`EP.boundaryIntegral_eq_zeroFormIntegration`**: the same for the sheets `Mᵢ` of an oriented
  tame structure of dimension `1` and `a ∈ Ω⁰_{ep,∞}(X)`, with E1's integral over oriented points
  (`EP.zeroFormIntegration`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

open scoped Classical in
/-- **Lebesgue measure on `ℝ⁰` is the Dirac measure at `0`**: `∫_S g = g(0)` if `0 ∈ S`, and `0`
otherwise. -/
theorem setIntegral_euclideanSpace_fin_zero (S : Set (EuclideanSpace ℝ (Fin 0)))
    (g : EuclideanSpace ℝ (Fin 0) → ℝ) :
    ∫ u in S, g u = if (0 : EuclideanSpace ℝ (Fin 0)) ∈ S then g 0 else 0 := by
  have hE : ∀ u u' : EuclideanSpace ℝ (Fin 0), u = u' := fun u u' => by ext i; exact i.elim0
  have hg : g = fun _ => g 0 := funext fun u => congrArg g (hE u 0)
  rw [hg, setIntegral_const]
  split_ifs with h
  · have : S = univ := eq_univ_of_forall fun u => hE 0 u ▸ h
    rw [this, volume_euclideanSpace_eq_dirac]; simp
  · have : S = ∅ := eq_empty_of_forall_notMem fun u hu => h (hE u 0 ▸ hu)
    rw [this]; simp

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {M : Set Obj} [ParacompactSpace M]
  {hY : X.PObj.IsSubMPolyfold M} {hcs : (subPolyfold hY).HasCornerStructureOfDim (0 + 1)}
  [inst : ChartedSpace (EuclideanQuadrant (0 + 1)) M]
  (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
include hch

/-- **Part I's face integrand of a `0`-form is `±` its value** (`n = 1`): for a Mathlib `0`-form
`η` on `M` with values `f`, a point `u` of the face piece at which `bridgeOrientation o` reads in
`κ` as `signedOr b` of the standard orientation,
`orSign b · faceSign l · ιₗ^*(κ⁻¹)^*η (u) = ±f(κ⁻¹(ιₗ u))`, the sign that of `o_{∂M}`. -/
theorem orSign_mul_faceSign_mul_facePullback_eq_dim1 (hM : X.PObj.IsSubmanifoldOfDim M (0 + 1))
    (ht : X.PObj.HasTameInducedStructure M) (o : X.PObj.SubmanifoldOrientation M (0 + 1))
    (f : Obj → ℝ) (η : ManifoldForm (𝓠 (0 + 1)) M 0)
    (hη : ∀ (y : M) (v : Fin 0 → EuclideanSpace ℝ (Fin (0 + 1))), η y v = f y.1)
    (κ : CornerCoords (subPolyfold hY) (0 + 1)) (l : Fin (0 + 1))
    {u : EuclideanSpace ℝ (Fin 0)} (hu : u ∈ κ.faceSet l) (b : Bool)
    (hb : orientationIn κ.toQuadrantChart (κ.facePt l u)
      (bridgeOrientation hcs o (κ.facePt l u)) = signedOr b (stdOrientation (0 + 1))) :
    orSign b * faceSign l *
        facePullback l (ManifoldForm.chartForm (𝓠 (0 + 1)) κ.toQuadrantChart η) u (stdFrame 0) =
      frameSign ((o.stratumOrientation hM ht).tangent (κ.facePt l u).1) * f (κ.facePt l u).1 := by
  have hb' := hb
  rw [orientationIn_bridgeOrientation hch (Nat.succ_pos 0) hM o κ
    (CornerCoords.facePt_mem_s hu)] at hb'
  subst hch
  let _ : ChartedSpace (EuclideanQuadrant (0 + 1)) M := (subPolyfold hY).cornerChartedSpace hcs
  set y := κ.facePt l u with hydef
  have hy : y ∈ κ.s := CornerCoords.facePt_mem_s hu
  have hpiece : y ∈ κ.facePiece l := CornerCoords.facePt_mem_facePiece hu
  have hyl : κ.coord y l = 0 := CornerCoords.coord_facePt_self hu
  have hval : facePullback l (ManifoldForm.chartForm (𝓠 (0 + 1)) κ.toQuadrantChart η) u
      (stdFrame 0) = f y.1 := by
    rw [facePullback, formPullback_apply, ManifoldForm.chartForm_apply]
    exact hη _ _
  rw [hval, orSign_mul_faceSign]
  have hiff := faceFrame_mem_stratumOrientation_iff hM ht o κ hpiece hyl b hb'
  have hfr : faceFrame hcs κ hy l ∈ (o.stratumOrientation hM ht).frames y.1 ↔
      ((o.stratumOrientation hM ht).tangent y.1).frames.Nonempty := by
    refine ⟨fun h => ⟨_, h⟩, fun ⟨v, hv⟩ => ?_⟩
    have hv' : v = faceFrame hcs κ hy l := funext fun k => k.elim0
    rw [← hv']; exact hv
  unfold frameSign
  by_cases h : (b == faceBool l) = true
  · rw [if_pos h, if_pos (hfr.1 (hiff.2 h))]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 (hfr.2 h')))]

/-- **One term of Part I's boundary integral of a `0`-form** (one chart, one face; `n = 1`): as
E8F's `FormEval.face_term_eq`, with the face density `±f`. -/
theorem face_term_eq_dim1 (hM : X.PObj.IsSubmanifoldOfDim M (0 + 1))
    (ht : X.PObj.HasTameInducedStructure M) (o : X.PObj.SubmanifoldOrientation M (0 + 1))
    (f : Obj → ℝ) (η : ManifoldForm (𝓠 (0 + 1)) M 0)
    (hη : ∀ (y : M) (v : Fin 0 → EuclideanSpace ℝ (Fin (0 + 1))), η y v = f y.1)
    (κ : CornerCoords (subPolyfold hY) (0 + 1)) (l : Fin (0 + 1)) (ρ : M → ℝ) (ρ' : Obj → ℝ)
    (hρ' : ∀ y : M, ρ' y.1 = ρ y) {R : Set M} (b : Bool)
    (hb : ∀ y ∈ R, orientationIn κ.toQuadrantChart y (bridgeOrientation hcs o y) =
      signedOr b (stdOrientation (0 + 1)))
    (hρR : tsupport ρ ⊆ R) :
    orSign b * (faceSign l * topFormIntegral
        (faceEmbedding l ⁻¹' (κ.toQuadrantChart.extend (𝓠 (0 + 1))).target)
        (facePullback l (ManifoldForm.chartForm (𝓠 (0 + 1)) κ.toQuadrantChart
          (ManifoldForm.smulFun ρ η)))) =
      ∫ u in κ.faceSet l, ρ' (κ.facePt l u).1 *
        (frameSign ((o.stratumOrientation hM ht).tangent (κ.facePt l u).1) *
          f (κ.facePt l u).1) := by
  have hpt : EqOn (fun u => orSign b * faceSign l * facePullback l (ManifoldForm.chartForm
      (𝓠 (0 + 1)) κ.toQuadrantChart (ManifoldForm.smulFun ρ η)) u (stdFrame 0))
      (fun u => ρ' (κ.facePt l u).1 *
        (frameSign ((o.stratumOrientation hM ht).tangent (κ.facePt l u).1) *
          f (κ.facePt l u).1))
      (κ.faceSet l) := by
    intro u hu
    have e1 : facePullback l (ManifoldForm.chartForm (𝓠 (0 + 1)) κ.toQuadrantChart
        (ManifoldForm.smulFun ρ η)) u (stdFrame 0) = ρ (κ.facePt l u) *
        facePullback l (ManifoldForm.chartForm (𝓠 (0 + 1)) κ.toQuadrantChart η) u
          (stdFrame 0) := by
      simp only [facePullback, formPullback_apply, ManifoldForm.chartForm_smulFun]
      rfl
    simp only
    rw [e1, hρ']
    by_cases hr : κ.facePt l u ∈ R
    · rw [← orSign_mul_faceSign_mul_facePullback_eq_dim1 hch hM ht o f η hη κ l hu b (hb _ hr)]
      ring
    · have h0 : ρ (κ.facePt l u) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hr (hρR h)
      rw [h0]
      simp
  have hSm : MeasurableSet (κ.faceSet l) := (κ.isOpen_faceSet l).measurableSet
  rw [topFormIntegral_def, ← setIntegral_congr_set (κ.faceSet_ae_eq l), ← mul_assoc,
    ← integral_const_mul]
  exact setIntegral_congr_fun hSm hpt

/-- **Part I's boundary integral of a `0`-form over a `1`-dimensional sheet is the integral over
the oriented boundary points** (proof of Theorem 9.5.18, 2021 p. 451, last equality of the display,
for `n = 1`; Definition 9.3.8, p. 426): for a tame `1`-dimensional sheet `M` oriented by `o` whose
boundary stratum `∂₁M` has at most one point, and a `C¹` Mathlib `0`-form `η` on `M` with compact
support and values `f`, `∫_{∂(M, o)} η = ∫_{∂₁M} f|(∂₁M, o_{∂M})`, i.e. `±f(p)` if `∂₁M = {p}`
and `0` if `∂₁M = ∅`. -/
theorem boundaryIntegral_eq_pointInteg [IsManifold (𝓠 (0 + 1)) ∞ M] [T2Space M]
    [SigmaCompactSpace M] (hM : X.PObj.IsSubmanifoldOfDim M (0 + 1))
    (ht : X.PObj.HasTameInducedStructure M) (o : X.PObj.SubmanifoldOrientation M (0 + 1))
    (f : Obj → ℝ) (η : ManifoldForm (𝓠 (0 + 1)) M 0)
    (hη1 : ManifoldForm.ContMDiffForm (𝓠 (0 + 1)) 1 η)
    (hc : IsCompact (ManifoldForm.tsupport η))
    (hη : ∀ (y : M) (v : Fin 0 → EuclideanSpace ℝ (Fin (0 + 1))), η y v = f y.1)
    (hs : (X.PObj.boundaryStratum M).Subsingleton) :
    ManifoldForm.boundaryIntegral (bridgeOrientation hcs o) η =
      pointInteg f (X.PObj.boundaryStratum M) (o.stratumOrientation hM ht).tangent
        (X.PObj.boundaryStratum M) := by
  classical
  have ho := isContinuous_bridgeOrientation hch (Nat.succ_pos 0) hM o
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [ManifoldForm.boundaryIntegral_eq_integrationData ho hη1 hc D subset_rfl]
  set bS := X.PObj.boundaryStratum M with hbS
  set o' := o.stratumOrientation hM ht with ho'
  let ρ' : {x // x ∈ T} → Obj → ℝ := fun j x => if h : x ∈ M then D.ρ j ⟨x, h⟩ else 0
  have hρ' : ∀ j (y : M), ρ' j y.1 = D.ρ j y := fun j y => by
    simp only [ρ', dif_pos y.2]
  let κ : {x // x ∈ T} → CornerCoords (subPolyfold hY) (0 + 1) :=
    fun j => hcs.coords (D.center j)
  have hchart : ∀ j, chartAt (EuclideanQuadrant (0 + 1)) (D.center j) = (κ j).toQuadrantChart :=
    fun j => chartAt_eq_of_eq hcs hch _
  have hρ0 : ∀ j (y : M), y ∉ (κ j).s → ρ' j y.1 = 0 := fun j y hy => by
    rw [hρ' j y]
    exact image_eq_zero_of_notMem_tsupport fun h => hy (by
      have := D.region_subset j (D.tsupport_subset j h)
      rw [hchart j] at this; exact this)
  set g : {x // x ∈ T} → Fin (0 + 1) → EuclideanSpace ℝ (Fin 0) → ℝ :=
    fun j l u => ρ' j ((κ j).facePt l u).1 *
      (frameSign (o'.tangent ((κ j).facePt l u).1) * f ((κ j).facePt l u).1) with hg
  have hJ : ∀ j l, orSign (D.sign j) * (faceSign l * topFormIntegral
        (faceEmbedding l ⁻¹' ((κ j).toQuadrantChart.extend (𝓠 (0 + 1))).target)
        (facePullback l (ManifoldForm.chartForm (𝓠 (0 + 1)) (κ j).toQuadrantChart
          (ManifoldForm.smulFun (D.ρ j) η)))) = ∫ u in (κ j).faceSet l, g j l u := by
    intro j l
    exact face_term_eq_dim1 hch hM ht o f η hη (κ j) l (D.ρ j) (ρ' j) (hρ' j) (D.sign j)
      (fun y hy => by have := D.orientationIn_eq j y hy; rwa [hchart j] at this)
      (D.tsupport_subset j)
  have hL : D.boundaryIntegral η = ∑ j, ∑ l, ∫ u in (κ j).faceSet l, g j l u := by
    unfold IntegrationData.boundaryIntegral
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show D.chart j = (κ j).toQuadrantChart from hchart j,
      ManifoldForm.chartBoundaryIntegral, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => hJ j l
  rw [hL]
  by_cases hne : bS.Nonempty
  swap
  · rw [pointInteg_of_empty (by rw [inter_self]; exact not_nonempty_iff_eq_empty.1 hne)]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
    have he : (κ j).faceSet l = ∅ := eq_empty_of_forall_notMem fun u hu =>
      hne ⟨_, facePt_mem_boundaryStratum hM.1 ht (κ j) hu⟩
    rw [he, Measure.restrict_empty, integral_zero_measure]
  obtain ⟨p, hp⟩ := hne
  have hpM : p ∈ M := hp.1
  rw [pointInteg_of_mem hs ⟨hp, hp⟩]
  have hE : ∀ u u' : EuclideanSpace ℝ (Fin 0), u = u' := fun u u' => by ext i; exact i.elim0
  set c := frameSign (o'.tangent p) * f p with hc'
  have hterm : ∀ j l, ∫ u in (κ j).faceSet l, g j l u = ρ' j p * c := by
    intro j l
    rw [setIntegral_euclideanSpace_fin_zero]
    split_ifs with h0
    · have hb := facePt_mem_boundaryStratum hM.1 ht (κ j) h0
      have hpe : ((κ j).facePt l 0).1 = p := hs hb hp
      simp only [hg, hpe, hc']
    · by_contra hne
      have hρne : ρ' j p ≠ 0 := fun h => hne (by rw [h, zero_mul])
      have hs' : (⟨p, hpM⟩ : M) ∈ (κ j).s := by
        by_contra hns
        exact hρne (hρ0 j ⟨p, hpM⟩ hns)
      obtain ⟨l', u', hu', -⟩ := exists_facePt_of_mem_boundaryStratum hM.1 ht (κ j) hs' hp
      have hl : l' = l := Fin.ext (by have := l.isLt; have := l'.isLt; omega)
      subst hl
      exact h0 (hE u' 0 ▸ hu')
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, zero_add, one_smul]
  rw [← Finset.sum_mul]
  by_cases hsupp : (⟨p, hpM⟩ : M) ∈ ManifoldForm.tsupport η
  · simp only [hρ' _ ⟨p, hpM⟩]
    rw [D.sum_eq_one _ hsupp, one_mul]
  · have hf : f p = 0 := by
      have := hη ⟨p, hpM⟩ (fun k => k.elim0)
      rw [ManifoldForm.eq_zero_of_notMem_tsupport hsupp] at this
      exact this.symm
    rw [hc', hf, mul_zero, mul_zero]

end EpGroupoid

namespace EP

open MPolyfold

/-- **Part I's boundary integral of a `0`-form over a sheet `Mᵢ` is the integral over its
oriented boundary point** (proof of Theorem 9.5.18, 2021 p. 451, last equality of the display,
for `n = 1`; Definition 9.3.8, p. 426): for an oriented tame structure `C` of dimension `1` at `x`
with sheets in the class of §9.5, a sheet `Mᵢ` whose boundary sheet `∂₁Mᵢ` has at most one point,
and `a ∈ Ω⁰_{ep,∞}(X)` vanishing on `Mᵢ` off a closed `K` with `Mᵢ ∩ K` compact,
`∫_{∂(Mᵢ,oᵢ)} a = ∫_{∂₁Mᵢ} a|(∂₁Mᵢ, o_{∂Mᵢ})` (`= ±a(p)` if `∂₁Mᵢ = {p}`, `0` if empty). -/
theorem boundaryIntegral_eq_zeroFormIntegration (A : EP.{u}) {Θ : A.Obj → ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x)
    (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (0 + 1)).sheets) (i : C.ι)
    (hs : (C.boundarySheet i).Subsingleton)
    (a : A.epFormsInfty 0) {K : Set A.Obj} (hK : IsClosed K) (hKc : IsCompact (C.M i ∩ K))
    (h0 : (C.orientedSheet (A.epFormsInftyEval (0 + 1)) hS i).VanishesOff K
      (A.epFormsInftyToObj 0 a)) :
    (C.orientedSheet (A.epFormsInftyEval (0 + 1)) hS i).boundaryIntegral
        (A.epFormsInftyToObj 0 a) =
      A.zeroFormIntegration.integ a (C.boundarySheet i) (C.boundaryOrient i).tangent
        (C.boundarySheet i) := by
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  have := EpGroupoid.FormEval.sigmaCompactSpace_of_mem_sheets (hS i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).isManifold_cornerChartedSpace
    hcs
  have hc : IsCompact (ManifoldForm.tsupport (formsInftyRestrict 0 hcs
      (A.epFormsInftyToObj 0 a))) := by
    have hcl : IsClosed ((↑) ⁻¹' K : Set (C.M i)) := hK.preimage continuous_subtype_val
    have hcp : IsCompact ((↑) ⁻¹' K : Set (C.M i)) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
      exact hKc
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (h0 y hyC)
  have hC1 : ManifoldForm.ContMDiffForm (𝓠 (0 + 1)) 1
      (formsInftyRestrict 0 hcs (A.epFormsInftyToObj 0 a)) :=
    (contMDiffForm_formsInftyRestrict (hcs := hcs) rfl (A.epFormsInftyToObj 0 a)).of_le
      (by exact_mod_cast le_top)
  have hsm : ∀ y : C.M i, y.1 ∈ A.X.PObj.smoothSet := fun y =>
    hΘ.support_subset (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i y.2)
  have key := EpGroupoid.boundaryIntegral_eq_pointInteg (M := C.M i) (hcs := hcs) rfl
    (C.isSubmanifoldOfDim i) (C.hasTameInducedStructure i) (C.orient i) (A.zeroFormEval a)
    (formsInftyRestrict 0 hcs (A.epFormsInftyToObj 0 a)) hC1 hc
    (fun y v => A.formsInftyRestrict_zero_eq a y (hsm y) v) hs
  exact key

end EP

end Polyfold
