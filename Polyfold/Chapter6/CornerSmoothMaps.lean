import Polyfold.Chapter6.IntervalEndInclusion
import Polyfold.Chapter4.StokesFaceIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.1 (Definition 4.1.1,
p. 173) and the proof of **Theorem 6.7.1** (p. 278): sc-smooth maps between finite-dimensional
M-polyfolds with corner structures are classically smooth.

# Sc-smooth maps between manifolds with corners are `C^∞`

## The text, paraphrased

(Definition 4.1.1 and the lines after it) A finite-dimensional M-polyfold all of whose charts
are corner charts is a smooth manifold with boundary and corners; sc-smoothness between such
spaces is classical smoothness (Corollary 1.2.5 in the charts).  The proof of Theorem 6.7.1 uses
this for the inclusions of the ends `S_{F_i} → S_F` of a cobordism.

## What is formalized

* **`MPolyfold.contMDiff_of_isScSmoothMap`**: let `Q`, `Q'` be M-polyfolds with corner
  structures of dimensions `n`, `n'`, with the Mathlib charted spaces `cornerChartedSpace`.
  An sc-smooth map `G : Q → Q'` is `C^∞` (`ContMDiff`) for the models `[0, ∞)ⁿ`, `[0, ∞)^{n'}`.
  In corner coordinates `κ` at `x` and `κ'` at `G(x)` the map reads
  `y ↦ Ψ'((χ' ∘ G ∘ χ⁻¹)(Ψ⁻¹(y − c))) + c'`, and `χ' ∘ G ∘ χ⁻¹` is sc-smooth on a relatively
  open subset of a partial quadrant in a finite-dimensional space, hence `C^∞` there.
* `MPolyfold.hasFDerivWithinAt_cornerCoord`, **`MPolyfold.lin_mfderiv_of_isScSmoothMap`**: the
  derivative of the coordinate map is `Ψ' ∘ D ∘ Ψ⁻¹` for any derivative `D` of `χ' ∘ G ∘ χ⁻¹`;
  so Mathlib's derivative `T_xG` (`mfderiv`) satisfies `Ψ'⁻¹(T_xG · v) = D(Ψ⁻¹ v)`.
* **`MPolyfold.tangentMap_fiberMap_eq_mfderiv`**: the tangent map `TG` (§2.3) of the tangent
  vector at `x` with corner coordinates `v` is the tangent vector at `G(x)` with corner
  coordinates `T_xG · v`.
* `MPolyfold.cornerForm_formPullback_eq_restrictForm`, `MPolyfold.restrictForm_formsAlong`,
  **`MPolyfold.restrictForm_formsInftyAlong`**: for `j : Q → Q'` sc-smooth between corner
  structures of dimensions `n`, `n + 1`, `g : Q' → X` and `τ ∈ Ωᵏ_∞(X)`, the pull-back along `j`
  (`restrictForm`, the integrand of the face integrals of Theorem 4.4.7) of the Mathlib form of
  `τ` along `g` is the Mathlib form of `τ` along `g ∘ j`.
* **`contMDiff_sliceInclusion`**: for `F = f̃ + S` over `[0, 1] × X` and `t ∈ [0, 1]`, if the
  solution sets `S_{F_t} ⊆ X` and `S_F ⊆ [0, 1] × X` are sub-M-polyfolds with corner structures
  of dimensions `k` and `d`, the inclusion `j_t : S_{F_t} → S_F`, `x ↦ (t, x)`, is `C^∞` between
  the Mathlib manifolds with corners.
* **`restrictForm_sliceInclusion_pullback`**: `j_t^*((pr₂^*α)|_{S_F}) = α|_{S_{F_t}}` as Mathlib
  forms, for `α ∈ Ωᵐ_∞(X)`: the integrand of `∫_{∂S_F} pr₂^*α` on the end `\{t\} × S_{F_t}` is
  the integrand of `∫_{S_{F_t}} α`.

## Reading

The decomposition of `∫_{∂S_F}` into the integrals over the two ends and over the part of
`∂S_F` over `[0, 1] × ∂X` is not formalized here; this file gives the smoothness of the
inclusions of the ends, their derivatives and the integrand on the ends.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

namespace MPolyfold

/-- **An sc-smooth map between finite-dimensional M-polyfolds with corner structures is `C^∞`**
(2021 Definition 4.1.1, p. 173, with Corollary 1.2.5): for the Mathlib manifolds with corners
`cornerChartedSpace` of dimensions `n` and `n'`. -/
theorem contMDiff_of_isScSmoothMap {M N : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
    {Q : MPolyfold M} {Q' : MPolyfold N} {n n' : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]
    (hch : inst = Q.cornerChartedSpace hcs)
    (hcs' : Q'.HasCornerStructureOfDim n') [inst' : ChartedSpace (EuclideanQuadrant n') N]
    (hch' : inst' = Q'.cornerChartedSpace hcs')
    {G : M → N} (hG : Q.IsScSmoothMap Q' G) : ContMDiff (𝓠 n) (𝓠 n') ∞ G := by
  intro x
  set κ := hcs.coords x
  set κ' := hcs'.coords (G x)
  have hc : extChartAt (𝓠 n) x = κ.toQuadrantChart.extend (𝓠 n) := by
    rw [extChartAt, chartAt_eq_of_eq hcs hch x]
    rfl
  have hc' : extChartAt (𝓠 n') (G x) = κ'.toQuadrantChart.extend (𝓠 n') := by
    rw [extChartAt, chartAt_eq_of_eq hcs' hch' (G x)]
    rfl
  have hGc : ContinuousAt G x := (hG.continuousOn.mono (subset_univ _)).continuousAt univ_mem
  rw [contMDiffAt_iff]
  refine ⟨hGc, ?_⟩
  rw [hc, hc']
  have := κ.isCornerChart.finiteDimensional
  have := κ'.isCornerChart.finiteDimensional
  have hso := TangentPre.isOpen_fdom hG κ.χ κ'.χ
  have hU := relOpen_image_fdom κ.isCornerChart inter_subset_left hso
  have hsc : IsScSmooth (κ.χ '' TangentPre.fdom κ.χ G κ'.χ) (κ'.χ ∘ G ∘ κ.χ.symm) :=
    (TangentPre.isScSmoothRetractMap_coord hG κ.isChart κ'.isChart subset_rfl
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
    (κ.toQuadrantChart.extend (𝓠 n)).symm ⁻¹' (G ⁻¹' κ'.s) with hT
  have hon : ContDiffOn ℝ ∞ (κ'.toQuadrantChart.extend (𝓠 n') ∘ G ∘
      (κ.toQuadrantChart.extend (𝓠 n)).symm) T := by
    refine (hout.comp_contDiffOn (hcd.comp haff.contDiffOn fun y hy => ?_)).congr fun y hy => ?_
    · obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy.1
      exact h2 ▸ ⟨_, ⟨κ.s_subset h1, κ'.s_subset hy.2⟩, rfl⟩
    · obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy.1
      simp only [Function.comp_apply]
      rw [κ'.extend_eq_toLp_coord hy.2, h2, κ.χ.symm_apply_apply (κ.s_subset h1)]
      rfl
  have hmem : κ.toQuadrantChart.extend (𝓠 n) x ∈ T := by
    refine ⟨hxt, ?_⟩
    change G ((κ.toQuadrantChart.extend (𝓠 n)).symm (κ.toQuadrantChart.extend (𝓠 n) x)) ∈ κ'.s
    rw [hsx]
    exact hcs'.mem_coords (G x)
  have htn := κ.toQuadrantChart.extend_target_mem_nhdsWithin (I := 𝓠 n) hx
  have hTn : T ∈ 𝓝[range (𝓠 n)] (κ.toQuadrantChart.extend (𝓠 n) x) := by
    refine inter_mem htn (nhdsWithin_le_of_mem htn ?_)
    have hcont := κ.toQuadrantChart.continuousOn_extend_symm (I := 𝓠 n) _ hxt
    refine hcont.preimage_mem_nhdsWithin ?_
    rw [hsx]
    exact hGc.preimage_mem_nhds (κ'.isOpen_s.mem_nhds (hcs'.mem_coords (G x)))
  exact (hon _ hmem).mono_of_mem_nhdsWithin hTn

/-- **The derivative of an sc-smooth map in corner coordinates**: in corner coordinates `κ`
around `x` and `κ'` around `G(x)`, the coordinate map `κ' ∘ G ∘ κ⁻¹` has at `κ(x)`, within
`[0, ∞)ⁿ`, the derivative `Ψ' ∘ D ∘ Ψ⁻¹`, for any derivative `D` of `χ' ∘ G ∘ χ⁻¹` at `χ(x)`
(`Ψ`, `Ψ'` the linear parts of the coordinates). -/
theorem hasFDerivWithinAt_cornerCoord {M N : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
    {Q : MPolyfold M} {Q' : MPolyfold N} {n n' : ℕ}
    {G : M → N} (hG : Q.IsScSmoothMap Q' G) {x : M}
    (κ : CornerCoords Q n) (κ' : CornerCoords Q' n') (hx : x ∈ κ.s) (hGx : G x ∈ κ'.s)
    {D : κ.χ.model.E 0 →L[ℝ] κ'.χ.model.E 0}
    (hD : HasFDerivWithinAt (κ'.χ ∘ G ∘ κ.χ.symm) D
      (κ.χ '' TangentPre.fdom κ.χ G κ'.χ) (κ.χ x)) :
    HasFDerivWithinAt (κ'.toQuadrantChart.extend (𝓠 n') ∘ G ∘
        (κ.toQuadrantChart.extend (𝓠 n)).symm)
      ((((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm :
          (Fin n' → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n')).comp
        (κ'.Ψ : κ'.χ.model.E 0 →L[ℝ] (Fin n' → ℝ))).comp (D.comp κ.lin))
      (range (𝓠 n)) (κ.toQuadrantChart.extend (𝓠 n) x) := by
  have hGc : ContinuousAt G x := (hG.continuousOn.mono (subset_univ _)).continuousAt univ_mem
  have hxt : κ.toQuadrantChart.extend (𝓠 n) x ∈ (κ.toQuadrantChart.extend (𝓠 n)).target :=
    (κ.toQuadrantChart.extend (𝓠 n)).map_source (by rwa [κ.toQuadrantChart.extend_source])
  have hsx : (κ.toQuadrantChart.extend (𝓠 n)).symm (κ.toQuadrantChart.extend (𝓠 n) x) = x :=
    κ.toQuadrantChart.extend_left_inv hx
  set T : Set (EuclideanSpace ℝ (Fin n)) := (κ.toQuadrantChart.extend (𝓠 n)).target ∩
    (κ.toQuadrantChart.extend (𝓠 n)).symm ⁻¹' (G ⁻¹' κ'.s) with hT
  have hmem : κ.toQuadrantChart.extend (𝓠 n) x ∈ T := by
    refine ⟨hxt, ?_⟩
    change G ((κ.toQuadrantChart.extend (𝓠 n)).symm (κ.toQuadrantChart.extend (𝓠 n) x)) ∈ κ'.s
    rw [hsx]
    exact hGx
  have htn := κ.toQuadrantChart.extend_target_mem_nhdsWithin (I := 𝓠 n) hx
  have hTn : T ∈ 𝓝[range (𝓠 n)] (κ.toQuadrantChart.extend (𝓠 n) x) := by
    refine inter_mem htn (nhdsWithin_le_of_mem htn ?_)
    have hcont := κ.toQuadrantChart.continuousOn_extend_symm (I := 𝓠 n) _ hxt
    refine hcont.preimage_mem_nhdsWithin ?_
    rw [hsx]
    exact hGc.preimage_mem_nhds (κ'.isOpen_s.mem_nhds hGx)
  have hmaps : MapsTo κ.aff T (κ.χ '' TangentPre.fdom κ.χ G κ'.χ) := fun y hy => by
    obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy.1
    exact h2 ▸ ⟨_, ⟨κ.s_subset h1, κ'.s_subset hy.2⟩, rfl⟩
  have haffx : κ.aff (κ.toQuadrantChart.extend (𝓠 n) x) = κ.χ x := κ.aff_extend hx
  have hD' : HasFDerivWithinAt (κ'.χ ∘ G ∘ κ.χ.symm) D
      (κ.χ '' TangentPre.fdom κ.χ G κ'.χ) (κ.aff (κ.toQuadrantChart.extend (𝓠 n) x)) := by
    rw [haffx]
    exact hD
  have h1 : HasFDerivWithinAt ((κ'.χ ∘ G ∘ κ.χ.symm) ∘ κ.aff) (D.comp κ.lin) T
      (κ.toQuadrantChart.extend (𝓠 n) x) :=
    hD'.comp _ (κ.hasFDerivAt_aff _).hasFDerivWithinAt hmaps
  have hout : HasFDerivAt (fun z : κ'.χ.model.E 0 =>
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm (κ'.Ψ z + κ'.c))
      (((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm :
          (Fin n' → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n')).comp
        (κ'.Ψ : κ'.χ.model.E 0 →L[ℝ] (Fin n' → ℝ)))
      (((κ'.χ ∘ G ∘ κ.χ.symm) ∘ κ.aff) (κ.toQuadrantChart.extend (𝓠 n) x)) :=
    ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm :
      (Fin n' → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n')).hasFDerivAt.comp _
      ((κ'.Ψ : κ'.χ.model.E 0 →L[ℝ] (Fin n' → ℝ)).hasFDerivAt.add_const κ'.c)
  have h2 := HasFDerivAt.comp_hasFDerivWithinAt (f := (κ'.χ ∘ G ∘ κ.χ.symm) ∘ κ.aff)
    (κ.toQuadrantChart.extend (𝓠 n) x) hout h1
  have heq : EqOn (κ'.toQuadrantChart.extend (𝓠 n') ∘ G ∘ (κ.toQuadrantChart.extend (𝓠 n)).symm)
      ((fun z : κ'.χ.model.E 0 =>
        (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm (κ'.Ψ z + κ'.c)) ∘
        ((κ'.χ ∘ G ∘ κ.χ.symm) ∘ κ.aff)) T := fun y hy => by
    obtain ⟨h1, h2⟩ := κ.symm_mem_and_aff_eq hy.1
    simp only [Function.comp_apply]
    rw [κ'.extend_eq_toLp_coord hy.2, h2, κ.χ.symm_apply_apply (κ.s_subset h1)]
    rfl
  exact (h2.congr heq (heq hmem)).mono_of_mem_nhdsWithin hTn

/-- **Mathlib's derivative of an sc-smooth map in corner coordinates**: for the corner
coordinates `κ` at `x` and `κ'` at `G(x)` (the charts of `cornerChartedSpace`) and any derivative
`D` of `χ' ∘ G ∘ χ⁻¹` at `χ(x)`: `Ψ'⁻¹(T_xG · v) = D(Ψ⁻¹ v)`, `T_xG` Mathlib's `mfderiv`. -/
theorem lin_mfderiv_of_isScSmoothMap {M N : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
    {Q : MPolyfold M} {Q' : MPolyfold N} {n n' : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]
    (hch : inst = Q.cornerChartedSpace hcs)
    (hcs' : Q'.HasCornerStructureOfDim n') [inst' : ChartedSpace (EuclideanQuadrant n') N]
    (hch' : inst' = Q'.cornerChartedSpace hcs')
    {G : M → N} (hG : Q.IsScSmoothMap Q' G) (x : M)
    {D : (hcs.coords x).χ.model.E 0 →L[ℝ] (hcs'.coords (G x)).χ.model.E 0}
    (hD : HasFDerivWithinAt ((hcs'.coords (G x)).χ ∘ G ∘ (hcs.coords x).χ.symm) D
      ((hcs.coords x).χ '' TangentPre.fdom (hcs.coords x).χ G (hcs'.coords (G x)).χ)
      ((hcs.coords x).χ x)) (v : EuclideanSpace ℝ (Fin n)) :
    (hcs'.coords (G x)).lin (mfderiv (𝓠 n) (𝓠 n') G x v) = D ((hcs.coords x).lin v) := by
  have hc : extChartAt (𝓠 n) x = (hcs.coords x).toQuadrantChart.extend (𝓠 n) := by
    rw [extChartAt, chartAt_eq_of_eq hcs hch x]
    rfl
  have hc' : extChartAt (𝓠 n') (G x) = (hcs'.coords (G x)).toQuadrantChart.extend (𝓠 n') := by
    rw [extChartAt, chartAt_eq_of_eq hcs' hch' (G x)]
    rfl
  have hmd : MDifferentiableAt (𝓠 n) (𝓠 n') G x :=
    (contMDiff_of_isScSmoothMap hcs hch hcs' hch' hG x).mdifferentiableAt (by simp)
  have hder := hasFDerivWithinAt_cornerCoord hG (hcs.coords x) (hcs'.coords (G x))
    (hcs.mem_coords x) (hcs'.mem_coords (G x)) hD
  have hy0 : (hcs.coords x).toQuadrantChart.extend (𝓠 n) x ∈ range (𝓠 n) := by
    rw [OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hfd : mfderiv (𝓠 n) (𝓠 n') G x =
      (((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n' => ℝ).symm :
          (Fin n' → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n')).comp
        ((hcs'.coords (G x)).Ψ : (hcs'.coords (G x)).χ.model.E 0 →L[ℝ] (Fin n' → ℝ))).comp
        (D.comp (hcs.coords x).lin) := by
    rw [hmd.mfderiv]
    unfold writtenInExtChartAt
    rw [hc, hc']
    exact hder.fderivWithin ((𝓠 n).uniqueDiffOn _ hy0)
  rw [hfd]
  exact (hcs'.coords (G x)).Ψ.symm_apply_apply _

/-- **The tangent map of an sc-smooth map between manifolds with corners is Mathlib's
derivative** (2021 Definition 4.1.1 with §2.3; used for the inclusions `S_{F_i} → S_F` in the
proof of Theorem 6.7.1): the tangent map `TG` of the tangent vector at `x` with corner
coordinates `v ∈ ℝⁿ` is the tangent vector at `G(x)` with corner coordinates
`T_xG · v ∈ ℝ^{n'}` (`mfderiv`). -/
theorem tangentMap_fiberMap_eq_mfderiv {M N : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
    {Q : MPolyfold M} {Q' : MPolyfold N} {n n' : ℕ}
    (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]
    (hch : inst = Q.cornerChartedSpace hcs)
    (hcs' : Q'.HasCornerStructureOfDim n') [inst' : ChartedSpace (EuclideanQuadrant n') N]
    (hch' : inst' = Q'.cornerChartedSpace hcs')
    {G : M → N} (hG : Q.IsScSmoothMap Q' G) (x : M) (v : EuclideanSpace ℝ (Fin n)) :
    tangentMap hG ((hcs.coords x).fiberMap (hcs.levelOne_mem_coords x) v).1 =
      ((hcs'.coords (G x)).fiberMap (hcs'.levelOne_mem_coords (G x))
        (mfderiv (𝓠 n) (𝓠 n') G x v)).1 := by
  have hxκ : Q.levelVal 1 (hcs.levelOne x) ∈ (hcs.coords x).χ.source :=
    hcs.levelOne_mem_coords x
  have hyκ' : Q'.levelVal 1 (hcs'.levelOne (G x)) ∈ (hcs'.coords (G x)).χ.source :=
    hcs'.levelOne_mem_coords (G x)
  have hL := tangentMap_mapsTo_fiber hG (hcs.levelOne x) (hcs'.levelOne (G x)) rfl
    ((hcs.coords x).fiberMap hxκ v).2
  have hR := ((hcs'.coords (G x)).fiberMap hyκ' (mfderiv (𝓠 n) (𝓠 n') G x v)).2
  refine tangentChartMap_injOn (hcs'.coords (G x)).isChart
    (mem_tangentChartSet_of_mem_fiber hyκ' hL) (mem_tangentChartSet_of_mem_fiber hyκ' hR)
    (Prod.ext ?_ ?_)
  · rw [tangentChartMap_fst_of_mem_fiber (hcs'.coords (G x)).isChart hyκ' hL,
      tangentChartMap_fst_of_mem_fiber (hcs'.coords (G x)).isChart hyκ' hR]
  have hGψ : G (Q.levelVal 1 (hcs.levelOne x)) ∈ (hcs'.coords (G x)).χ.source := hyκ'
  obtain ⟨D, hD⟩ := exists_hasFDerivWithinAt_coord hG (hcs.coords x).isChart
    (hcs.coords x).isCornerChart (hcs'.coords (G x)).isChart hxκ hGψ
  rw [tangentChartMap_tangentMap_eq_of_hasFDerivWithinAt hG (hcs.coords x).isChart
    (hcs.coords x).isCornerChart (hcs'.coords (G x)).isChart
    ((hcs.coords x).fiberMap hxκ v).2 hxκ hGψ hD, (hcs.coords x).tangentChartMap_fiberMap hxκ v]
  exact (lin_mfderiv_of_isScSmoothMap hcs hch hcs' hch' hG x hD v).symm.trans
    ((hcs'.coords (G x)).tangentChartMap_fiberMap hyκ' _).symm

/-! ### Forms along a composition -/

section AlongComp

universe w

open ManifoldForm

variable {M N : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M]
  [TopologicalSpace N] [T2Space N] [ParacompactSpace N] {Q : MPolyfold M} {Q' : MPolyfold N}
  {n k : ℕ} (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) M]
  (hch : inst = Q.cornerChartedSpace hcs)
  (hcs' : Q'.HasCornerStructureOfDim (n + 1))
  [inst' : ChartedSpace (EuclideanQuadrant (n + 1)) N]
  (hch' : inst' = Q'.cornerChartedSpace hcs') (j : ScMap Q Q')

include hch hch' in
/-- **The Mathlib form of a pull-back is the pull-back of the Mathlib form**: for an sc-smooth
map `j : Q → Q'` between M-polyfolds with corner structures of dimensions `n` and `n + 1` and a
family `θ` of alternating forms on the tangent spaces of `Q'`, the Mathlib form of `j^*θ`
(`formPullback`, 2021 p. 198) is `j^*` of the Mathlib form of `θ` (`restrictForm`, with
Mathlib's derivative `T_p j`). -/
theorem cornerForm_formPullback_eq_restrictForm
    (θ : ∀ y : Q'.Level 1, Q'.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    cornerForm hcs (formPullback j.isScSmoothMap θ) = restrictForm j (cornerForm hcs' θ) := by
  funext x
  ext v
  exact formPullback_eq j.isScSmoothMap θ
    (fun i => (hcs.coords x).fiberMap (hcs.levelOne_mem_coords x) (v i))
    (y := hcs'.levelOne (j x)) rfl
    (fun i => (hcs'.coords (j x)).fiberMap (hcs'.levelOne_mem_coords (j x))
      (mfderiv (𝓠 n) (𝓠 (n + 1)) j x (v i)))
    fun i => tangentMap_fiberMap_eq_mfderiv hcs hch hcs' hch' j.isScSmoothMap x (v i)

variable {A : BundledMPolyfold.{w}} (g : ScMap Q' A.P)

include hch hch' in
/-- **`j^*((g^i)^*τ)_N = (((g ∘ j)^i)^*τ)_M`** for an sc-form `τ` on `X^i`. -/
theorem restrictForm_formsAlong (i : ℕ) (τ : A.forms k i) :
    restrictForm j (formsAlong hcs' g i τ) = formsAlong hcs (g.comp j) i τ := by
  rw [formsAlong_apply, formsAlong_apply,
    ← cornerForm_formPullback_eq_restrictForm hcs hch hcs' hch' j, ← formPullback_comp]
  exact congrArg (cornerForm hcs) (formPullback_congr _ _
    (fun x => (alongLift_comp hcs hcs' g j i x).symm) τ.1)

include hch hch' in
/-- **The pull-back of forms along a composition, on `Ωᵏ_∞`** (the proof of 2021 Theorem
6.7.1, p. 278: the restriction of a form to a face of a cobordism): for sc-smooth
`j : Q → Q'` between M-polyfolds with corner structures of dimensions `n`, `n + 1`,
`g : Q' → X` and `τ ∈ Ωᵏ_∞(X)`: the pull-back along `j` (`restrictForm`, Mathlib's derivative)
of the form of `τ` along `g` is the form of `τ` along `g ∘ j`. -/
theorem restrictForm_formsInftyAlong (τ : A.formsInfty k) :
    restrictForm j (formsInftyAlong k hcs' g τ) = formsInftyAlong k hcs (g.comp j) τ := by
  obtain ⟨i, τ', rfl⟩ := Module.DirectLimit.exists_of τ
  exact (congrArg (restrictForm j) (formsInftyAlong_of hcs' g i τ')).trans
    ((restrictForm_formsAlong hcs hch hcs' hch' j g i τ').trans
      (formsInftyAlong_of hcs (g.comp j) i τ').symm)

end AlongComp

end MPolyfold

section Inclusion

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {f : X → Y}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]

omit [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- **The inclusion of a slice into the cobordism is `C^∞`** (the proof of 2021 Theorem 6.7.1,
p. 278): if `S_{F_t} ⊆ X` and `S_F ⊆ [0, 1] × X` are sub-M-polyfolds with corner structures of
dimensions `k` and `d`, then `j_t : S_{F_t} → S_F`, `x ↦ (t, x)`, is `C^∞` between the Mathlib
manifolds with corners. -/
theorem contMDiff_sliceInclusion (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)))
    (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S t))))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))]
    [ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S t)))] {k d : ℕ}
    (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim k)
    [inst : ChartedSpace (EuclideanQuadrant k)
      (solutionSet P (sectionAdd P f (prodSlice S t)))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim d)
    [inst' : ChartedSpace (EuclideanQuadrant d) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs') :
    ContMDiff (𝓠 k) (𝓠 d) ∞ (sliceInclusion hf hS t) :=
  MPolyfold.contMDiff_of_isScSmoothMap hcs hch hcs' hch'
    (isScSmoothMap_sliceInclusion hf hS t hSm hSt)

omit [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- **The integrand on an end of the cobordism** (the proof of 2021 Theorem 6.7.1, p. 278):
for `F = f̃ + S` over `[0, 1] × X`, `t ∈ [0, 1]`, corner structures of dimensions `n` on
`S_{F_t}` and `n + 1` on `S_F`, and `α ∈ Ωᵐ_∞(X)`: the pull-back along the inclusion
`j_t : S_{F_t} → S_F` (Mathlib's derivative, `restrictForm`) of the Mathlib form
`(pr₂^*α)|_{S_F}` is the Mathlib form `α|_{S_{F_t}}`. -/
theorem restrictForm_sliceInclusion_pullback (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval)
    (hSm : ((cubePolyfold 1).prod PX).IsSubMPolyfold (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)))
    (hSt : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f (prodSlice S t))))
    [ParacompactSpace (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))]
    [ParacompactSpace (solutionSet P (sectionAdd P f (prodSlice S t)))] {n m : ℕ}
    (hcs : (MPolyfold.subPolyfold hSt).HasCornerStructureOfDim n)
    [inst : ChartedSpace (EuclideanQuadrant n)
      (solutionSet P (sectionAdd P f (prodSlice S t)))]
    (hch : inst = (MPolyfold.subPolyfold hSt).cornerChartedSpace hcs)
    (hcs' : (MPolyfold.subPolyfold hSm).HasCornerStructureOfDim (n + 1))
    [inst' : ChartedSpace (EuclideanQuadrant (n + 1)) (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S))]
    (hch' : inst' = (MPolyfold.subPolyfold hSm).cornerChartedSpace hcs')
    (α : (BundledMPolyfold.of PX).formsInfty m) :
    restrictForm (sliceInclusion hf hS t)
        (formsInftyRestrict m hcs'
          (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) m α)) =
      formsInftyRestrict m hcs α := by
  have h := MPolyfold.restrictForm_formsInftyAlong hcs hch hcs' hch'
    ⟨sliceInclusion hf hS t, isScSmoothMap_sliceInclusion hf hS t hSm hSt⟩
    (A := BundledMPolyfold.of ((cubePolyfold 1).prod PX)) (subInclScMap hSm)
    (BundledMPolyfold.formsInftyPullback (ivPrScMap PX) m α)
  exact h.trans (formsInftyAlong_sliceIntoCube_pullback hcs t α)

end Inclusion

end Polyfold
