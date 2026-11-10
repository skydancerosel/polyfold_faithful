import Polyfold.Chapter4.ManifoldBoundary2021

/-!
# Forms on the faces of a manifold with corners and their integral (2021 pp. 198–199, 276–279)

Theorem 6.7.1 (2021 p. 277, preprint Theorem 6.43) integrates the second component `τ` of a
relative form `(ω, τ)` over the boundary `∂S` of a solution set; `τ` is a form on `∂X`, which the
text introduces (2021 p. 198) by noting that local faces and their intersections are tame, so that
"it makes sense to talk about differential forms on `∂X`".  This file provides the
finite-dimensional side: forms given only on the faces of a Mathlib manifold with corners `M`
modelled on `[0,∞)ⁿ⁺¹` (`modelWithCornersEuclideanQuadrant`), their exterior derivative, their
integral over `∂M`, and `∫_{∂M} dτ = 0`.

## The reading

A `k`-form on the faces of `M` (`IsChartFaceForm`, `ChartFaceForm M n k`, a real vector space)
is a family of `k`-forms `σ x i` on the parameter sets `faceDomain (chartAt x) i ⊆ ℝⁿ` of the faces
`{xᵢ = 0}` of the charts `chartAt x`, which are
* `C^∞`;
* compatible under chart changes at the points of degeneracy index `1` (the face transition with
  derivative `faceRestrict A i i'`, `A` the chart change derivative);
* in agreement at the corners: on two faces `{xᵢ = 0}`, `{x_j = 0}` of one chart, the two face
  forms agree on vectors tangent to both faces.
Every `C^∞` form `β` on `M` gives one, `j^*β = faceRestriction β` (`ChartFaceForm.ofForm`), so the
conditions are satisfiable; the data are indexed by the charts `chartAt x` only, so no hypothesis
quantifies over all charts of the maximal atlas.

## Main results

* `ManifoldForm.extDeriv_extDeriv`: `d ∘ d = 0` for `C²` forms on `M` (any model with corners).
* `exists_extension`: a compactly supported form on the faces of a Hausdorff σ-compact `M` is
  `j^*β` for a compactly supported `C^∞` form `β` on `M` (`IsExtendedBy σ β`): inclusion–exclusion
  over the faces in box charts (`inclExcl`, `facePullback_inclExcl`, `exists_box`), glued by a
  smooth partition of unity.
* `boundaryIntegral_congr_face`: forms with the same face restrictions have the same `∫_{∂M}`.
* `ChartFaceForm.integral` (`faceIntegral`): `∫_{∂M} τ := ∫_{∂M} β` for any extension `β`
  (`faceIntegral_eq`), additive, homogeneous and local (`ChartFaceForm.integral_add`,
  `integral_smul`, `integral_congr`, `integralₗ` for compact `M`); `∫_{∂M} j^*β = ∫_{∂M} β`
  (`faceIntegral_faceRestriction`, `ChartFaceForm.integral_ofForm`).
* `ChartFaceForm.d` (face by face, `extDerivWithin` on the face parameters), with
  `j^*(dβ) = d(j^*β)` (`faceRestriction_extDeriv`) and `IsExtendedBy.extDeriv`.
* `ChartFaceForm.integral_d_eq_zero`: `∫_{∂M} dτ = 0` for a compactly supported `τ`
  (`∫_{∂M} dβ = ∫_M ddβ = 0`, Stokes `integral_extDeriv_eq_boundaryIntegral`).

## Dimensions `0` and `1`

The model `[0,∞)ⁿ⁺¹` has at least one coordinate, so a manifold of dimension `0` has no faces and
its boundary integral is `0` by convention downstream.  In dimension `1` (`n = 0`) the faces are
points: the face parameter space `ℝ⁰` has volume `1` (`volume_univ_fin_zero`), and the integral of
a `0`-form over a face is its value (`topFormIntegral_univ_fin_zero`), so `∫_{∂M} τ` is a signed sum
of point values; all constructions are uniform in `n`.
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

section CompCLM

variable {E F G X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup X]
  [NormedSpace ℝ X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The alternatization `f ↦ ∑_σ sign σ · f ∘ σ` of continuous multilinear maps, as a continuous
linear map. -/
def alternatizationCLM :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) G →L[ℝ] E [⋀^ι]→L[ℝ] G :=
  LinearMap.mkContinuous
    { toFun := ContinuousMultilinearMap.alternatization
      map_add' := map_add _
      map_smul' := fun c f => by
        ext v
        simp only [ContinuousMultilinearMap.alternatization_apply_apply, RingHom.id_apply,
          ContinuousAlternatingMap.smul_apply, smul_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _ }
    (Fintype.card (Equiv.Perm ι)) fun f => by
      refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousMultilinearMap.alternatization_apply_apply]
      calc ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ)‖
          ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f (v ∘ σ)‖ := norm_sum_le _ _
        _ ≤ ∑ _σ : Equiv.Perm ι, ‖f‖ * ∏ i, ‖v i‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have h1 : ‖Equiv.Perm.sign σ • f (v ∘ σ)‖ = ‖f (v ∘ σ)‖ := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [h1]
          refine (f.le_opNorm _).trans (le_of_eq ?_)
          congr 1
          exact Equiv.prod_comp σ (fun i => ‖v i‖)
        _ = _ := by simp [mul_assoc]

theorem alternatizationCLM_apply (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) G)
    (v : ι → E) :
    alternatizationCLM f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ) :=
  ContinuousMultilinearMap.alternatization_apply_apply f v

/-- The alternatization of an alternating map is `card (Perm ι)` times the map. -/
theorem alternatizationCLM_toContinuousMultilinearMap (f : E [⋀^ι]→L[ℝ] G) :
    alternatizationCLM f.toContinuousMultilinearMap =
      (Fintype.card (Equiv.Perm ι) : ℝ) • f := by
  ext v
  rw [alternatizationCLM_apply, ContinuousAlternatingMap.smul_apply]
  have : ∀ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.toContinuousMultilinearMap (v ∘ σ) = f v :=
    fun σ => by
      rw [ContinuousAlternatingMap.coe_toContinuousMultilinearMap]
      change Equiv.Perm.sign σ • f.toAlternatingMap (v ∘ σ) = f.toAlternatingMap v
      rw [f.toAlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]

omit [DecidableEq ι] in
/-- **The pull-back of alternating maps is smooth**: `(f, g) ↦ f ∘ (g × ⋯ × g)` is `C^∞` (it is
linear in `f` and a homogeneous polynomial in `g`). -/
theorem contDiff_compContinuousLinearMap {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun p : (F [⋀^ι]→L[ℝ] G) × (E →L[ℝ] F) => p.1.compContinuousLinearMap p.2) := by
  classical
  have hc : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by positivity
  have key : (fun p : (F [⋀^ι]→L[ℝ] G) × (E →L[ℝ] F) => p.1.compContinuousLinearMap p.2) =
      fun p => (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • alternatizationCLM
        (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : ι => E) (fun _ : ι => F) G (fun _ => p.2) p.1.toContinuousMultilinearMap) := by
    funext p
    rw [ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]
    have : p.1.toContinuousMultilinearMap.compContinuousLinearMap (fun _ => p.2) =
        (p.1.compContinuousLinearMap p.2).toContinuousMultilinearMap := rfl
    rw [this, alternatizationCLM_toContinuousMultilinearMap, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  rw [key]
  have h : ContDiff ℝ r fun p : (F [⋀^ι]→L[ℝ] G) × (E →L[ℝ] F) =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : ι => E) (fun _ : ι => F) G (fun _ => p.2) p.1.toContinuousMultilinearMap :=
    ContDiff.clm_apply ((ContinuousMultilinearMap.contDiff _).comp
      (contDiff_pi.2 fun _ => contDiff_snd))
      ((ContinuousAlternatingMap.toContinuousMultilinearMapLI (𝕜 := ℝ) (E := F) (F := G)
        (ι := ι)).contDiff.comp contDiff_fst)
  exact ((alternatizationCLM (ι := ι) (E := E) (G := G)).contDiff.comp h).const_smul _

omit [DecidableEq ι] in
theorem ContDiffWithinAt.compContinuousLinearMap' {r : WithTop ℕ∞} {f : X → F [⋀^ι]→L[ℝ] G}
    {g : X → E →L[ℝ] F} {s : Set X} {x : X} (hf : ContDiffWithinAt ℝ r f s x)
    (hg : ContDiffWithinAt ℝ r g s x) :
    ContDiffWithinAt ℝ r (fun y => (f y).compContinuousLinearMap (g y)) s x :=
  contDiff_compContinuousLinearMap.contDiffAt.comp_contDiffWithinAt x (hf.prodMk hg)

omit [DecidableEq ι] in
theorem ContDiffOn.compContinuousLinearMap' {r : WithTop ℕ∞} {f : X → F [⋀^ι]→L[ℝ] G}
    {g : X → E →L[ℝ] F} {s : Set X} (hf : ContDiffOn ℝ r f s) (hg : ContDiffOn ℝ r g s) :
    ContDiffOn ℝ r (fun y => (f y).compContinuousLinearMap (g y)) s :=
  fun x hx => ContDiffWithinAt.compContinuousLinearMap' (hf x hx) (hg x hx)

end CompCLM

theorem add_one_le_infty {r : WithTop ℕ∞} (hr : r ≤ ∞) : r + 1 ≤ ∞ := by
  induction r using WithTop.recTopCoe with
  | top => exact absurd hr (by decide)
  | coe r => exact WithTop.coe_le_coe.2 le_top

/-- The pull-back of a `C^r` form by a map with a `C^r` derivative field is `C^r`. -/
theorem ContDiffWithinAt.formPullback' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {r : WithTop ℕ∞}
    {ω : F → F [⋀^Fin k]→L[ℝ] ℝ} {φ : E → F} {φ' : E → E →L[ℝ] F} {s : Set E} {x : E}
    (hω : ContDiffWithinAt ℝ r (fun y => ω (φ y)) s x) (hφ' : ContDiffWithinAt ℝ r φ' s x) :
    ContDiffWithinAt ℝ r (formPullback φ φ' ω) s x :=
  ContDiffWithinAt.compContinuousLinearMap' hω hφ'

namespace ManifoldForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ}

/-! ### `d` lowers the regularity by one, and `d ∘ d = 0` -/

/-- **`d` of a `C^{r+1}` form is `C^r`.** -/
theorem ContMDiffForm.extDeriv {r : WithTop ℕ∞} {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I (r + 1) ω) : ContMDiffForm I r (extDeriv ω) := fun x => by
  have h1 : ContMDiffForm I 1 ω := hω.of_le le_add_self
  refine ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp_contDiffOn
    ((hω x).fderivWithin (uniqueDiffOn_extChartAt_target x) le_rfl)).congr fun y hy => ?_
  exact chartForm_extDeriv_of_mem_target (IsManifold.chart_mem_maximalAtlas x) h1 hy

/-- **`d ∘ d = 0`** (2021 p. 198, the identity behind the relative complex, here for classical
forms) for a `C²` form on a manifold with corners (Mathlib's
`extDerivWithin_extDerivWithin_apply` in the chart at each point; the chart target is contained in
the closure of its interior). -/
theorem extDeriv_extDeriv {ω : ManifoldForm I M k} (hω : ContMDiffForm I 2 ω) :
    extDeriv (extDeriv ω) = 0 := by
  funext x
  have he := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x
  have hxT := mem_extChartAt_target (I := I) x
  have h1 : ContMDiffForm I 1 ω := hω.of_le (by norm_num)
  have hEq : chartForm I (chartAt H x) (extDeriv ω) =ᶠ[𝓝[range I] (extChartAt I x x)]
      extDerivWithin (chartForm I (chartAt H x) ω) (extChartAt I x).target := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    exact chartForm_extDeriv_of_mem_target he h1 hy
  rw [extDeriv_apply, hEq.extDerivWithin_eq (chartForm_extDeriv_of_mem_target he h1 hxT),
    ← extDerivWithin_extend_target _ (chartAt H x) hxT]
  exact extDerivWithin_extDerivWithin_apply ((hω x).contDiffWithinAt hxT)
    (by rw [minSmoothness_of_isRCLikeNormedField]) (uniqueDiffOn_extChartAt_target x)
    (extChartAt_target_subset_closure_interior hxT) hxT

/-! ### Forms given in one chart -/

/-- **The form on `M` with expression `η` in the chart `e`** (on `e.source`; outside it the
value is irrelevant in the uses, where the form is multiplied by a function supported in
`e.source`): `p ↦ η(e p) ∘ D(e ∘ c_p⁻¹)`, `c_p = chartAt H p`. -/
def ofChartForm (e : OpenPartialHomeomorph M H) (η : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    ManifoldForm I M k :=
  fun p => ((η (e.extend I p)).compContinuousLinearMap (chartChangeDeriv I (chartAt H p) e p) :
    E [⋀^Fin k]→L[ℝ] ℝ)

/-- The expression of `ofChartForm e η` in a chart `e'` at a point of both sources. -/
theorem chartForm_ofChartForm_apply {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    {p : M} (hp : p ∈ e.source) (hp' : p ∈ e'.source) (η : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (v : Fin k → E) :
    chartForm I e' (ofChartForm e η) (e'.extend I p) v =
      η (e.extend I p) (chartChangeDeriv I e' e p ∘ v) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  rw [chartForm_apply, e'.extend_left_inv hp']
  change η (e.extend I p) (chartChangeDeriv I (chartAt H p) e p ∘
    (chartChangeDeriv I e' (chartAt H p) p ∘ v)) = _
  congr 1
  funext l
  exact chartChangeDeriv_comp_apply hn he' (IsManifold.chart_mem_maximalAtlas p) he hp'
    (mem_chart_source H p) hp (v l)

/-- In its own chart, `ofChartForm e η` reads as `η`. -/
theorem chartForm_ofChartForm_self {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (η : E → E [⋀^Fin k]→L[ℝ] ℝ) {y : E}
    (hy : y ∈ (e.extend I).target) : chartForm I e (ofChartForm e η) y = η y := by
  have hp : (e.extend I).symm y ∈ e.source := by
    rw [← e.extend_source (I := I)]; exact (e.extend I).map_target hy
  ext v
  have := chartForm_ofChartForm_apply he he hp hp η v
  rw [(e.extend I).right_inv hy, chartChangeDeriv_self hp] at this
  exact this

/-- In a second chart, `ofChartForm e η` is the pull-back of `η` by the chart change. -/
theorem chartForm_ofChartForm_eventuallyEq {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    {p : M} (hp : p ∈ e.source) (hp' : p ∈ e'.source) (η : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    chartForm I e' (ofChartForm e η) =ᶠ[𝓝[range I] (e'.extend I p)]
      formPullback (I.extendCoordChange e' e) (fderivWithin ℝ (I.extendCoordChange e' e) (range I))
        η := by
  filter_upwards [I.extendCoordChange_source_mem_nhdsWithin' hp' hp] with z hz
  rw [← OpenPartialHomeomorph.extend_image_source_inter] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  ext v
  rw [chartForm_ofChartForm_apply he he' hq.2 hq.1, formPullback_apply]
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
    e'.extend_left_inv hq.1]
  rfl

/-! ### Smoothness is local -/

omit [IsManifold I ∞ M] in
/-- A form vanishing near `p` has a smooth expression near `e(p)` in every chart. -/
theorem contDiffWithinAt_chartForm_of_eventually_eq_zero {ω : ManifoldForm I M k} {p : M}
    (h : ∀ᶠ q in 𝓝 p, ω q = 0) {e : OpenPartialHomeomorph M H} (hp : p ∈ e.source)
    {r : WithTop ℕ∞} {s : Set E} : ContDiffWithinAt ℝ r (chartForm I e ω) s (e.extend I p) := by
  have h' : chartForm I e ω =ᶠ[𝓝 (e.extend I p)] fun _ => 0 := by
    filter_upwards [e.extend_preimage_mem_nhds (I := I) hp h] with y hy
    ext v
    rw [chartForm_apply, mem_preimage.1 hy]
    rfl
  exact (contDiffAt_const.congr_of_eventuallyEq h').contDiffWithinAt

/-- **Smoothness of forms is local**: a form whose expression is `C^r` (`r ≤ ∞`) near every
point in some chart of the maximal atlas is `C^r`. -/
theorem contMDiffForm_of_local {r : WithTop ℕ∞} (hr : r ≤ ∞) {ω : ManifoldForm I M k}
    (h : ∀ p : M, ∃ e ∈ IsManifold.maximalAtlas I ∞ M, p ∈ e.source ∧
      ContDiffWithinAt ℝ r (chartForm I e ω) (range I) (e.extend I p)) :
    ContMDiffForm I r ω := fun x y hy => by
  set c := chartAt H x
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) x
  set p := (extChartAt I x).symm y
  have hp : p ∈ c.source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I x).map_target hy
  have hy' : c.extend I p = y := (extChartAt I x).right_inv hy
  obtain ⟨e, he, hpe, hd⟩ := h p
  have hev := chartForm_eventuallyEq_formPullback hc he ω hp hpe
  rw [hy'] at hev
  have hφ := I.contDiffWithinAt_extendCoordChange' (n := ∞) hc he hp hpe
  rw [hy'] at hφ
  have hfx : I.extendCoordChange c e y = e.extend I p := by
    rw [← hy']
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [c.extend_left_inv hp]
  have hmaps : MapsTo (I.extendCoordChange c e) (range I) (range I) := fun z _ => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hyI : y ∈ range I := extChartAt_target_subset_range x hy
  have h1 : ContDiffWithinAt ℝ r (fun z => chartForm I e ω (I.extendCoordChange c e z))
      (range I) y := by
    rw [← hfx] at hd
    exact hd.comp y (hφ.of_le hr) hmaps
  have h2 : ContDiffWithinAt ℝ r (fderivWithin ℝ (I.extendCoordChange c e) (range I))
      (range I) y := hφ.fderivWithin_right I.uniqueDiffOn (add_one_le_infty hr) hyI
  exact ((ContDiffWithinAt.formPullback' h1 h2).congr_of_eventuallyEq hev
    (hev.self_of_nhdsWithin hyI)).mono (extChartAt_target_subset_range x)

/-- **A function times a form given in one chart is smooth**: if `η` is `C^∞` on a relatively
open subset `N` of `range I` and `ρ` is a smooth function with `tsupport ρ ⊆ e⁻¹(N)`, then
`ρ · ofChartForm e η` is a `C^∞` form on `M`. -/
theorem contMDiffForm_smulFun_ofChartForm {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {η : E → E [⋀^Fin k]→L[ℝ] ℝ} {N : Set E}
    (hN : ∀ y ∈ N, N ∈ 𝓝[range I] y) (hη : ContDiffOn ℝ ∞ η N) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hsupp : _root_.tsupport ρ ⊆ e.source ∩ e.extend I ⁻¹' N) :
    ContMDiffForm I ∞ (smulFun ρ (ofChartForm e η)) := by
  refine contMDiffForm_of_local le_rfl fun p => ?_
  by_cases hp : p ∈ _root_.tsupport ρ
  · refine ⟨e, he, (hsupp hp).1, ?_⟩
    have hpN : e.extend I p ∈ N := (hsupp hp).2
    have hT := e.extend_target_mem_nhdsWithin (I := I) (hsupp hp).1
    have hρ' : ContDiffWithinAt ℝ ∞ (ρ ∘ (e.extend I).symm) (range I) (e.extend I p) := by
      have := contMDiffOn_iff_contDiffOn.1 (hρ.comp_contMDiffOn (contMDiffOn_extend_symm he))
      rw [← e.extend_target'] at this
      exact (this _ ((e.extend I).map_source (by rw [e.extend_source]; exact (hsupp hp).1)))
        |>.mono_of_mem_nhdsWithin hT
    have hη' : ContDiffWithinAt ℝ ∞ η (range I) (e.extend I p) :=
      (hη _ hpN).mono_of_mem_nhdsWithin (hN _ hpN)
    refine (hρ'.smul hη').congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hT] with z hz
      rw [chartForm_smulFun, chartForm_ofChartForm_self he η hz]
      rfl
    · rw [chartForm_smulFun, chartForm_ofChartForm_self he η
        ((e.extend I).map_source (by rw [e.extend_source]; exact (hsupp hp).1))]
      rfl
  · refine ⟨chartAt H p, IsManifold.chart_mem_maximalAtlas p, mem_chart_source H p, ?_⟩
    refine contDiffWithinAt_chartForm_of_eventually_eq_zero ?_ (mem_chart_source H p)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hp] with q hq
    rw [smulFun_apply, hq, Pi.zero_apply, zero_smul]

end ManifoldForm

section FaceEuclid

variable {n k : ℕ}

theorem faceEmbedding_faceProjection {j : Fin (n + 1)} {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x j = 0) : faceEmbedding j (faceProjection j x) = x :=
  faceEmbedding_removeNth hx

@[simp]
theorem faceProjection_faceEmbedding (i : Fin (n + 1)) (u : EuclideanSpace ℝ (Fin n)) :
    faceProjection i (faceEmbedding i u) = u := by
  ext l
  simp [faceProjection_apply]

/-- **The restriction of a form to the face `{xᵢ = 0}`**, in the face parameters: the pull-back
`ιᵢ^*ω` by the face embedding, for forms of any degree (`facePullback` is the top-degree case,
`restrictFace_eq_facePullback`). -/
def restrictFace (i : Fin (n + 1))
    (ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ :=
  formPullback (faceEmbedding i) (fun _ => faceEmbedding i) ω

theorem restrictFace_apply (i : Fin (n + 1))
    (ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    restrictFace i ω u w = ω (faceEmbedding i u) (faceEmbedding i ∘ w) := rfl

theorem restrictFace_eq_facePullback (i : Fin (n + 1))
    (ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ) :
    restrictFace i ω = facePullback i ω := rfl

/-- **The lift of a form on a face parameter space**: a form `σ` on the parameter space `ℝⁿ` of
the face `{xᵢ = 0}` read on `ℝⁿ⁺¹` through the projection `x ↦ (x_j)_{j ≠ i}`; on the face and
for vectors tangent to it, this is `σ` itself. -/
def faceLift (i : Fin (n + 1))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ :=
  formPullback (faceProjection i) (fun _ => faceProjection i) σ

theorem faceLift_apply (i : Fin (n + 1))
    (σ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) (v : Fin k → EuclideanSpace ℝ (Fin (n + 1))) :
    faceLift i σ y v = σ (faceProjection i y) (faceProjection i ∘ v) := rfl

/-- On the face, the face pull-back of a form reads through `faceLift`. -/
theorem faceLift_facePullback (i : Fin (n + 1))
    (ω : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ)
    {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y i = 0)
    {v : Fin k → EuclideanSpace ℝ (Fin (n + 1))} (hv : ∀ l, v l i = 0) :
    faceLift i (restrictFace i ω) y v = ω y v := by
  rw [faceLift_apply, restrictFace_apply, faceEmbedding_faceProjection hy]
  congr 1
  funext l
  exact faceEmbedding_faceProjection (hv l)

/-- The map setting the coordinates in `I` to `0`. -/
def zeroCoords {m : ℕ} (I : Finset (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun j => if j ∈ I then 0 else y j
      map_add' := fun y z => by ext j; by_cases h : j ∈ I <;> simp [h]
      map_smul' := fun c y => by ext j; by_cases h : j ∈ I <;> simp [h] }

theorem zeroCoords_apply {m : ℕ} (I : Finset (Fin m)) (y : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    zeroCoords I y j = if j ∈ I then 0 else y j := rfl

theorem zeroCoords_insert_of_eq_zero {m : ℕ} {I : Finset (Fin m)} {b : Fin m}
    {y : EuclideanSpace ℝ (Fin m)} (hy : y b = 0) : zeroCoords (insert b I) y = zeroCoords I y := by
  ext j
  simp only [zeroCoords_apply, Finset.mem_insert]
  by_cases hj : j = b
  · subst hj; simp [hy]
  · simp [hj]

/-- The least element of a nonempty finset of faces (`0` for `∅`). -/
def leastFace (I : Finset (Fin (n + 1))) : Fin (n + 1) :=
  if h : I.Nonempty then I.min' h else 0

theorem leastFace_mem {I : Finset (Fin (n + 1))} (h : I.Nonempty) : leastFace I ∈ I := by
  rw [leastFace, dif_pos h]; exact I.min'_mem h

/-- The inclusion–exclusion coefficient `(-1)^(|I|+1)` (`0` for `I = ∅`). -/
def inclExclCoeff (I : Finset (Fin (n + 1))) : ℝ :=
  if I.Nonempty then (-1) ^ (I.card + 1) else 0

/-- The term of `I` of the inclusion–exclusion extension: the face form of the least face `a` of
`I`, read through `y ↦ π_a (π_I y)` (`π_I` zeroes the coordinates in `I`). -/
def inclExclTerm (σ : Fin (n + 1) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) (I : Finset (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ :=
  formPullback (fun y => faceProjection (leastFace I) (zeroCoords I y))
    (fun _ => (faceProjection (leastFace I)).comp (zeroCoords I)) (σ (leastFace I))

theorem inclExclTerm_apply (σ : Fin (n + 1) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) (I : Finset (Fin (n + 1)))
    (y : EuclideanSpace ℝ (Fin (n + 1))) (v : Fin k → EuclideanSpace ℝ (Fin (n + 1))) :
    inclExclTerm σ I y v =
      faceLift (leastFace I) (σ (leastFace I)) (zeroCoords I y) (zeroCoords I ∘ v) := rfl

/-- **The inclusion–exclusion extension** of forms `σ b` given on the faces `{x_b = 0}`, `b ∈ J`:
`∑_{∅ ≠ I ⊆ J} (-1)^(|I|+1) (π_a ∘ π_I)^* σ_a`, `a` the least element of `I`. -/
def inclExcl (J : Finset (Fin (n + 1))) (σ : Fin (n + 1) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ :=
  fun y => ∑ I ∈ J.powerset, inclExclCoeff I • inclExclTerm σ I y

/-- **The inclusion–exclusion extension restricts to the given face forms**: on a set `N` stable
under the maps `π_I`, `I ⊆ J`, if the face forms agree on the corners (their lifts agree at the
points of `N` on two faces, on vectors tangent to both), then the face pull-back of the extension
to every face `{x_b = 0}`, `b ∈ J`, is `σ b`.  (The terms of `I` and `I ∪ {b}` cancel.) -/
theorem facePullback_inclExcl {N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {J : Finset (Fin (n + 1))} {σ : Fin (n + 1) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ}
    (hJ : ∀ I ⊆ J, MapsTo (zeroCoords I) N N)
    (hcorner : ∀ a b, ∀ y ∈ N, y a = 0 → y b = 0 → ∀ v : Fin k → EuclideanSpace ℝ (Fin (n + 1)),
      (∀ l, v l a = 0) → (∀ l, v l b = 0) → faceLift a (σ a) y v = faceLift b (σ b) y v)
    {b : Fin (n + 1)} (hb : b ∈ J) {u : EuclideanSpace ℝ (Fin n)}
    (hu : faceEmbedding b u ∈ N) : restrictFace b (inclExcl J σ) u = σ b u := by
  classical
  ext w
  set z := faceEmbedding b u
  set v := faceEmbedding b ∘ w
  have hzb : z b = 0 := faceEmbedding_apply_self b u
  have hvb : ∀ l, v l b = 0 := fun l => faceEmbedding_apply_self b (w l)
  rw [restrictFace_apply]
  change (∑ I ∈ J.powerset, inclExclCoeff I • inclExclTerm σ I z) v = σ b u w
  rw [ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply]
  have hJb : J = insert b (J.erase b) := (Finset.insert_erase hb).symm
  rw [hJb, Finset.sum_powerset_insert (Finset.notMem_erase b J)]
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (∅ : Finset (Fin (n + 1)))]
  · -- the term of `∅` and of `{b}`
    have h1 : inclExclCoeff (∅ : Finset (Fin (n + 1))) = 0 := by simp [inclExclCoeff]
    have h2 : inclExclCoeff ({b} : Finset (Fin (n + 1))) = 1 := by simp [inclExclCoeff]
    have h3 : leastFace ({b} : Finset (Fin (n + 1))) = b := by simp [leastFace]
    rw [insert_empty_eq, h1, h2, zero_smul, one_smul, zero_add, inclExclTerm_apply, h3,
      faceLift_apply]
    have hz : zeroCoords {b} z = z := by
      rw [← insert_empty_eq b, zeroCoords_insert_of_eq_zero hzb]; ext j; simp [zeroCoords_apply]
    have hv : ∀ l, zeroCoords {b} (v l) = v l := fun l => by
      rw [← insert_empty_eq b, zeroCoords_insert_of_eq_zero (hvb l)]; ext j; simp [zeroCoords_apply]
    rw [hz]
    congr 1
    · exact congrArg (σ b) (faceProjection_faceEmbedding b u)
    · funext l
      simp only [Function.comp_apply]
      rw [hv l]
      exact faceProjection_faceEmbedding b (w l)
  · -- the terms of `I ≠ ∅` and of `insert b I` cancel
    intro I hI hI0
    have hIJ : I ⊆ J := (Finset.mem_powerset.1 hI).trans (Finset.erase_subset b J)
    have hbI : b ∉ I := fun h => Finset.notMem_erase b J (Finset.mem_powerset.1 hI h)
    have hne : I.Nonempty := Finset.nonempty_iff_ne_empty.2 hI0
    have hc : inclExclCoeff (insert b I) = -inclExclCoeff I := by
      simp only [inclExclCoeff, if_pos hne, if_pos (Finset.insert_nonempty b I),
        Finset.card_insert_of_notMem hbI, pow_succ]
      ring
    have ht : inclExclTerm σ (insert b I) z v = inclExclTerm σ I z v := by
      rw [inclExclTerm_apply, inclExclTerm_apply, zeroCoords_insert_of_eq_zero hzb]
      have hv' : zeroCoords (insert b I) ∘ v = zeroCoords I ∘ v := by
        funext l; exact zeroCoords_insert_of_eq_zero (hvb l)
      rw [hv']
      have hy : zeroCoords I z ∈ N := hJ I hIJ hu
      have hmem : ∀ a ∈ insert b I, zeroCoords I z a = 0 := fun a ha => by
        rcases Finset.mem_insert.1 ha with rfl | ha
        · rw [zeroCoords_apply, if_neg hbI, hzb]
        · rw [zeroCoords_apply, if_pos ha]
      have hmemv : ∀ a ∈ insert b I, ∀ l, (zeroCoords I ∘ v) l a = 0 := fun a ha l => by
        rcases Finset.mem_insert.1 ha with rfl | ha
        · simp only [Function.comp_apply]; rw [zeroCoords_apply, if_neg hbI, hvb l]
        · simp only [Function.comp_apply]; rw [zeroCoords_apply, if_pos ha]
      have hA := leastFace_mem (Finset.insert_nonempty b I)
      have hB : leastFace I ∈ insert b I := Finset.mem_insert_of_mem (leastFace_mem hne)
      exact hcorner _ _ _ hy (hmem _ hA) (hmem _ hB) _ (hmemv _ hA) (hmemv _ hB)
    rw [hc, ht, neg_smul, add_neg_cancel]
  · intro h
    exact absurd (Finset.empty_mem_powerset _) h

/-- **The inclusion–exclusion extension is smooth** on a set `N` stable under the `π_I`,
`I ⊆ J`, if each face form `σ a`, `a ∈ J`, is smooth on the face parameters of `N`. -/
theorem contDiffOn_inclExcl {N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {J : Finset (Fin (n + 1))} {σ : Fin (n + 1) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ}
    (hJ : ∀ I ⊆ J, MapsTo (zeroCoords I) N N)
    (hσ : ∀ a ∈ J, ContDiffOn ℝ ∞ (σ a) (faceEmbedding a ⁻¹' N)) :
    ContDiffOn ℝ ∞ (inclExcl J σ) N := by
  refine ContDiffOn.sum fun I hI => ?_
  by_cases hne : I.Nonempty
  · have hIJ := Finset.mem_powerset.1 hI
    have ha := hIJ (leastFace_mem hne)
    refine ContDiffOn.const_smul _ ?_
    set L := (faceProjection (leastFace I)).comp (zeroCoords I)
    have hmaps : MapsTo L N (faceEmbedding (leastFace I) ⁻¹' N) := fun y hy => by
      rw [mem_preimage]
      have h0 : zeroCoords I y (leastFace I) = 0 := by
        rw [zeroCoords_apply, if_pos (leastFace_mem hne)]
      change faceEmbedding (leastFace I) (faceProjection (leastFace I) (zeroCoords I y)) ∈ N
      rw [faceEmbedding_faceProjection h0]
      exact hJ I hIJ hy
    exact ContDiffOn.compContinuousLinearMap' ((hσ _ ha).comp L.contDiff.contDiffOn hmaps)
      contDiffOn_const
  · have : inclExclCoeff I = 0 := by simp [inclExclCoeff, hne]
    simp only [this, zero_smul]
    exact contDiffOn_const

end FaceEuclid

section Box

variable {m : ℕ}

/-- A coordinate box around `y₀` is contained in the Euclidean ball of radius `m δ`. -/
theorem dist_le_of_forall_abs_sub_le {y y₀ : EuclideanSpace ℝ (Fin m)} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ j, |y j - y₀ j| ≤ δ) : dist y y₀ ≤ m * δ := by
  rw [EuclideanSpace.dist_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc ∑ j, dist (y j) (y₀ j) ^ 2 ≤ ∑ _j : Fin m, δ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
    _ = m * δ ^ 2 := by simp
    _ ≤ (m * δ) ^ 2 := by
        rw [mul_pow]
        rcases Nat.eq_zero_or_pos m with hm | hm
        · simp [hm]
        · have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
            have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith
          exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **Box neighbourhoods in the quadrant.**  For `y₀` in `U ∩ [0,∞)ᵐ`, `U` open, there are an
open set `O ∋ y₀`, a set of faces `J` and a compact `C` with `O ∩ [0,∞)ᵐ ⊆ C ⊆ U ∩ [0,∞)ᵐ`, such
that `N = O ∩ [0,∞)ᵐ` is mapped into itself by every `π_I`, `I ⊆ J` (setting the coordinates in
`I` to `0`), and the points of `N` lie only on the faces `{x_b = 0}`, `b ∈ J`. -/
theorem exists_box {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    {y₀ : EuclideanSpace ℝ (Fin m)} (hy₀U : y₀ ∈ U) (hy₀ : y₀ ∈ closedQuadrant univ) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin m))) (J : Finset (Fin m))
      (C : Set (EuclideanSpace ℝ (Fin m))),
      IsOpen O ∧ y₀ ∈ O ∧ IsCompact C ∧ O ∩ closedQuadrant univ ⊆ C ∧
      C ⊆ U ∩ closedQuadrant univ ∧
      (∀ I ⊆ J, MapsTo (zeroCoords I) (O ∩ closedQuadrant univ) (O ∩ closedQuadrant univ)) ∧
      (∀ y ∈ O ∩ closedQuadrant univ, ∀ b, y b = 0 → b ∈ J) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y₀ hy₀U
  set δ : ℝ := ε / (2 * (m + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hmδ : (m : ℝ) * δ < ε := by
    rw [hδ_def, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  set J : Finset (Fin m) := Finset.univ.filter fun j => y₀ j < δ
  set O : Set (EuclideanSpace ℝ (Fin m)) :=
    {y | ∀ j, y j < y₀ j + δ ∧ (j ∉ J → y₀ j - δ < y j)}
  set C : Set (EuclideanSpace ℝ (Fin m)) :=
    {y | y ∈ closedQuadrant univ ∧ ∀ j, |y j - y₀ j| ≤ δ}
  have hy₀j : ∀ j, 0 ≤ y₀ j := fun j => hy₀ j (mem_univ j)
  refine ⟨O, J, C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : O = ⋂ j, ({y : EuclideanSpace ℝ (Fin m) | y j < y₀ j + δ} ∩
        {y | j ∉ J → y₀ j - δ < y j}) := by
      ext y; simp [O, forall_and]
    rw [this]
    refine isOpen_iInter_of_finite fun j => ?_
    refine (isOpen_lt (PiLp.continuous_apply 2 _ j) continuous_const).inter ?_
    by_cases hj : j ∈ J
    · simp [hj]
    · simpa [hj] using isOpen_lt continuous_const (PiLp.continuous_apply 2 _ j)
  · intro j; exact ⟨by linarith, fun _ => by linarith⟩
  · refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have : C = closedQuadrant univ ∩ ⋂ j, {y : EuclideanSpace ℝ (Fin m) | |y j - y₀ j| ≤ δ} := by
        ext y; simp [C]
      rw [this]
      exact isClosed_quadrant.inter (isClosed_iInter fun j =>
        isClosed_le ((PiLp.continuous_apply 2 _ j).sub continuous_const).abs continuous_const)
    · refine (Metric.isBounded_closedBall (x := y₀) (r := m * δ)).subset fun y hy => ?_
      exact Metric.mem_closedBall.2 (dist_le_of_forall_abs_sub_le hδ.le hy.2)
  · rintro y ⟨hyO, hyQ⟩
    refine ⟨hyQ, fun j => abs_le.2 ⟨?_, by linarith [(hyO j).1]⟩⟩
    by_cases hj : j ∈ J
    · have h1 : y₀ j < δ := (Finset.mem_filter.1 hj).2
      have h2 : 0 ≤ y j := hyQ j (mem_univ j)
      linarith
    · linarith [(hyO j).2 hj]
  · intro y hy
    refine ⟨hball ?_, hy.1⟩
    exact lt_of_le_of_lt (dist_le_of_forall_abs_sub_le hδ.le hy.2) hmδ
  · intro I hI y hy
    refine ⟨fun j => ?_, fun j _ => ?_⟩
    · rw [zeroCoords_apply]
      split_ifs with hj
      · exact ⟨by linarith [hy₀j j], fun h => absurd (hI hj) h⟩
      · exact hy.1 j
    · rw [zeroCoords_apply]
      split_ifs
      · exact le_rfl
      · exact hy.2 j (mem_univ j)
  · intro y hy b hb
    by_contra hbJ
    have := (hy.1 b).2 hbJ
    rw [hb] at this
    exact hbJ (Finset.mem_filter.2 ⟨Finset.mem_univ b, by linarith⟩)

end Box

/-! ### The faces of a chart -/

section FaceDomain

variable {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- **The parameter set of the face `{xᵢ = 0}` of a chart** `e`: the `u ∈ ℝⁿ` with `ιᵢ u` in the
chart target. -/
def faceDomain (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (i : Fin (n + 1)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  faceEmbedding i ⁻¹' (e.extend (𝓠 (n + 1))).target

/-- The face parameters of the points of the face `{xᵢ = 0}` of `e` on no other face (the points
of degeneracy index `1`, `image_faceEmbedding_openQuadrant`), the set over which
`chartBoundaryIntegral_eq_sum_openQuadrant` integrates. -/
def openFaceDomain (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (i : Fin (n + 1)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  faceEmbedding i ⁻¹' ((𝓠 (n + 1)).symm ⁻¹' e.target) ∩ openQuadrant univ

/-- The point of `M` with face parameter `u` on the face `{xᵢ = 0}` of `e`. -/
def facePoint (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) : M :=
  (e.extend (𝓠 (n + 1))).symm (faceEmbedding i u)

variable (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (i : Fin (n + 1))

theorem isOpen_preimage_faceEmbedding_target :
    IsOpen (faceEmbedding i ⁻¹' ((𝓠 (n + 1)).symm ⁻¹' e.target)) :=
  (e.open_target.preimage (𝓠 (n + 1)).continuous_symm).preimage (faceEmbedding i).continuous

theorem faceDomain_eq : faceDomain e i =
    faceEmbedding i ⁻¹' ((𝓠 (n + 1)).symm ⁻¹' e.target) ∩ closedQuadrant univ := by
  rw [faceDomain, ManifoldForm.extend_target_eq_inter_quadrant, preimage_inter,
    preimage_faceEmbedding_quadrant, Finset.coe_univ, preimage_univ]

theorem openFaceDomain_subset : openFaceDomain e i ⊆ faceDomain e i := by
  rw [faceDomain_eq]; exact inter_subset_inter_right _ openQuadrant_subset_quadrant

theorem isOpen_openFaceDomain : IsOpen (openFaceDomain e i) :=
  (isOpen_preimage_faceEmbedding_target e i).inter isOpen_openQuadrant

theorem quadrant_subset_closure_openQuadrant {m : ℕ} :
    closedQuadrant (univ : Set (Fin m)) ⊆ closure (openQuadrant univ) := by
  rw [← interior_closedQuadrant, convex_quadrant.closure_interior_eq_closure_of_nonempty_interior
    ⟨WithLp.toLp 2 fun _ => 1, by simp [interior_closedQuadrant, openQuadrant]⟩]
  exact subset_closure

/-- The points of degeneracy index `1` are dense in each face. -/
theorem faceDomain_subset_closure : faceDomain e i ⊆ closure (openFaceDomain e i) := by
  rw [faceDomain_eq]
  exact (inter_subset_inter_right _ quadrant_subset_closure_openQuadrant).trans
    (isOpen_preimage_faceEmbedding_target e i).inter_closure

theorem uniqueDiffOn_faceDomain : UniqueDiffOn ℝ (faceDomain e i) := by
  rw [faceDomain_eq, inter_comm]
  exact uniqueDiffOn_quadrant.inter (isOpen_preimage_faceEmbedding_target e i)

theorem faceDomain_subset_closure_interior :
    faceDomain e i ⊆ closure (interior (faceDomain e i)) :=
  (faceDomain_subset_closure e i).trans (closure_mono
    ((isOpen_openFaceDomain e i).subset_interior_iff.2 (openFaceDomain_subset e i)))

variable {e i}

theorem faceEmbedding_eq_zero_iff {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ openFaceDomain e i)
    (l : Fin (n + 1)) : faceEmbedding i u l = 0 ↔ l = i := by
  have h : faceEmbedding i u ∈ faceEmbedding i '' openQuadrant (i.succAbove ⁻¹' univ) :=
    mem_image_of_mem _ (by rw [preimage_univ]; exact hu.2)
  rw [image_faceEmbedding_openQuadrant (mem_univ i)] at h
  exact h.2 l (mem_univ l)

theorem facePoint_mem_source {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain e i) :
    facePoint e i u ∈ e.source := by
  rw [← e.extend_source (I := 𝓠 (n + 1))]; exact (e.extend _).map_target hu

theorem extend_facePoint {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain e i) :
    e.extend (𝓠 (n + 1)) (facePoint e i u) = faceEmbedding i u :=
  (e.extend _).right_inv hu

theorem facePoint_faceProjection {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y i = 0) :
    facePoint e i (faceProjection i y) = (e.extend (𝓠 (n + 1))).symm y := by
  rw [facePoint, faceEmbedding_faceProjection hy]

theorem facePoint_faceProjection_extend {p : M} (hp : p ∈ e.source)
    (hpi : e.extend (𝓠 (n + 1)) p i = 0) :
    facePoint e i (faceProjection i (e.extend (𝓠 (n + 1)) p)) = p := by
  rw [facePoint_faceProjection hpi, e.extend_left_inv hp]

theorem faceProjection_mem_faceDomain {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hy : y ∈ (e.extend (𝓠 (n + 1))).target) (hyi : y i = 0) :
    faceProjection i y ∈ faceDomain e i := by
  rw [faceDomain, mem_preimage, faceEmbedding_faceProjection hyi]; exact hy

theorem faceProjection_extend_mem_faceDomain {p : M} (hp : p ∈ e.source)
    (hpi : e.extend (𝓠 (n + 1)) p i = 0) :
    faceProjection i (e.extend (𝓠 (n + 1)) p) ∈ faceDomain e i :=
  faceProjection_mem_faceDomain ((e.extend _).map_source (by rwa [e.extend_source])) hpi

variable (e i) in
theorem continuousOn_facePoint : ContinuousOn (facePoint e i) (faceDomain e i) :=
  (e.continuousOn_extend_symm (I := 𝓠 (n + 1))).comp (faceEmbedding i).continuous.continuousOn
    (mapsTo_preimage _ _)

end FaceDomain

/-! ### Forms on the faces -/

section FaceForms

variable (M : Type*) (n k : ℕ)

/-- **Face data of degree `k`** on a manifold modelled on `[0,∞)ⁿ⁺¹`: for each point `x` and
each face `{xᵢ = 0}` of the chart at `x`, a `k`-form on the face parameters `ℝⁿ` (only its values
on `faceDomain (chartAt x) i` enter). -/
abbrev FaceFormData : Type _ :=
  M → Fin (n + 1) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) [⋀^Fin k]→L[ℝ] ℝ

variable {M n k} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

/-- **A `k`-form on the faces of `M`** (the reading of "differential forms on `∂X`", 2021
p. 198, for a manifold with corners), as data in the charts `chartAt x`: each face form is `C^∞`;
at a boundary point `p` of degeneracy index `1`, on the face `{xᵢ = 0}` of the chart at `x` and
on the face `{x_{i'} = 0}` of the chart at `x'`, the two face forms correspond under the face
transition (derivative `faceRestrict A i i'`, `A` the chart change derivative); and at a corner,
on two faces `{xᵢ = 0}`, `{x_j = 0}` of one chart, the two face forms agree on the vectors tangent
to both faces. -/
structure IsChartFaceForm (σ : FaceFormData M n k) : Prop where
  smooth : ∀ x i, ContDiffOn ℝ ∞ (σ x i) (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)
  chartChange : ∀ (x x' p : M), p ∈ (chartAt (EuclideanQuadrant (n + 1)) x).source →
    p ∈ (chartAt (EuclideanQuadrant (n + 1)) x').source → ∀ i i' : Fin (n + 1),
    (∀ l, (chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1)) p l = 0 ↔ l = i) →
    (∀ l, (chartAt (EuclideanQuadrant (n + 1)) x').extend (𝓠 (n + 1)) p l = 0 ↔ l = i') →
    ∀ w : Fin k → EuclideanSpace ℝ (Fin n),
      σ x' i' (faceProjection i' ((chartAt (EuclideanQuadrant (n + 1)) x').extend (𝓠 (n + 1)) p))
        (faceRestrict (chartChangeDeriv (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) x)
          (chartAt (EuclideanQuadrant (n + 1)) x') p) i i' ∘ w) =
      σ x i (faceProjection i ((chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1)) p)) w
  corner : ∀ (x : M) (i j : Fin (n + 1)),
    ∀ y ∈ ((chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1))).target, y i = 0 →
    y j = 0 → ∀ v : Fin k → EuclideanSpace ℝ (Fin (n + 1)), (∀ l, v l i = 0) →
    (∀ l, v l j = 0) → faceLift i (σ x i) y v = faceLift j (σ x j) y v

variable (M n k) in
/-- **The space `Ω^k(∂M)` of `k`-forms on the faces of `M`**, a real vector space. -/
def chartFaceForms : Submodule ℝ (FaceFormData M n k) where
  carrier := {σ | IsChartFaceForm σ}
  zero_mem' := ⟨fun _ _ => contDiffOn_const, fun _ _ _ _ _ _ _ _ _ _ => by simp,
    fun _ _ _ _ _ _ _ _ _ _ => by simp [faceLift_apply]⟩
  add_mem' := fun {σ τ} hσ hτ => by
    refine ⟨fun x i => (hσ.smooth x i).add (hτ.smooth x i), fun x x' p hp hp' i i' hi hi' w => ?_,
      fun x i j y hy hyi hyj v hvi hvj => ?_⟩
    · simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply]
      rw [hσ.chartChange x x' p hp hp' i i' hi hi' w, hτ.chartChange x x' p hp hp' i i' hi hi' w]
    · have h1 := hσ.corner x i j y hy hyi hyj v hvi hvj
      have h2 := hτ.corner x i j y hy hyi hyj v hvi hvj
      simp only [faceLift_apply, Pi.add_apply, ContinuousAlternatingMap.add_apply] at h1 h2 ⊢
      rw [h1, h2]
  smul_mem' := fun a σ hσ => by
    refine ⟨fun x i => (hσ.smooth x i).const_smul a, fun x x' p hp hp' i i' hi hi' w => ?_,
      fun x i j y hy hyi hyj v hvi hvj => ?_⟩
    · simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
      rw [hσ.chartChange x x' p hp hp' i i' hi hi' w]
    · have h1 := hσ.corner x i j y hy hyi hyj v hvi hvj
      simp only [faceLift_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply] at h1 ⊢
      rw [h1]

variable (M n k) in
/-- **A `k`-form on the faces of `M`** (`Ω^k(∂M)`, see `IsChartFaceForm`). -/
abbrev ChartFaceForm : Type _ := ↥(chartFaceForms M n k)

/-! ### The restriction `j^*β` of a form on `M` -/

/-- **The restriction `j^*β` of a form on `M` to the faces** (the map `j^*` of the relative
complex, 2021 p. 198, for `M`): in the chart at `x`, the pull-back of the expression of `β` by
the face embedding `ιᵢ`. -/
def faceRestriction (β : ManifoldForm (𝓠 (n + 1)) M k) : FaceFormData M n k :=
  fun x i => restrictFace i
    (ManifoldForm.chartForm (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) x) β)

theorem faceRestriction_apply (β : ManifoldForm (𝓠 (n + 1)) M k) (x : M) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    faceRestriction β x i u w = ManifoldForm.chartForm (𝓠 (n + 1))
      (chartAt (EuclideanQuadrant (n + 1)) x) β (faceEmbedding i u) (faceEmbedding i ∘ w) := rfl

theorem faceRestriction_add (β β' : ManifoldForm (𝓠 (n + 1)) M k) :
    faceRestriction (β + β') = faceRestriction β + faceRestriction β' := by
  funext x i u; ext w; rfl

theorem faceRestriction_smul (a : ℝ) (β : ManifoldForm (𝓠 (n + 1)) M k) :
    faceRestriction (a • β) = a • faceRestriction β := by
  funext x i u; ext w; rfl

theorem faceRestriction_zero : faceRestriction (0 : ManifoldForm (𝓠 (n + 1)) M k) = 0 := by
  funext x i u; ext w; rfl

/-- The face forms of `j^*β` are as smooth as `β`. -/
theorem contDiffOn_faceRestriction {r : WithTop ℕ∞} {β : ManifoldForm (𝓠 (n + 1)) M k}
    (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) r β) (x : M) (i : Fin (n + 1)) :
    ContDiffOn ℝ r (faceRestriction β x i)
      (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) := by
  have h1 : ContDiffOn ℝ r (fun u => ManifoldForm.chartForm (𝓠 (n + 1))
      (chartAt (EuclideanQuadrant (n + 1)) x) β (faceEmbedding i u))
      (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) :=
    (hβ x).comp (faceEmbedding i).contDiff.contDiffOn (mapsTo_preimage _ _)
  exact fun u hu => ContDiffWithinAt.formPullback' (h1 u hu) contDiffWithinAt_const

variable [IsManifold (𝓠 (n + 1)) ∞ M]

omit [ChartedSpace (EuclideanQuadrant (n + 1)) M] [IsManifold (𝓠 (n + 1)) ∞ M] in
/-- At a point of degeneracy index `1`, on the face `{xᵢ = 0}` of `e` and `{x_{i'} = 0}` of `e'`,
a form evaluated on the image under the chart change derivative `A` of vectors tangent to the face
is its face restriction evaluated on `faceRestrict A i i'`. -/
theorem restrictFace_chartChange [ChartedSpace (EuclideanQuadrant (n + 1)) M]
    [IsManifold (𝓠 (n + 1)) ∞ M] {e e' : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M) {p : M} (hp : p ∈ e.source)
    (hp' : p ∈ e'.source) {i i' : Fin (n + 1)}
    (hi : ∀ l, e.extend (𝓠 (n + 1)) p l = 0 ↔ l = i)
    (hi' : ∀ l, e'.extend (𝓠 (n + 1)) p l = 0 ↔ l = i')
    (η : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) :
    η (e'.extend (𝓠 (n + 1)) p) (chartChangeDeriv (𝓠 (n + 1)) e e' p ∘ faceEmbedding i ∘ w) =
      restrictFace i' η (faceProjection i' (e'.extend (𝓠 (n + 1)) p))
        (faceRestrict (chartChangeDeriv (𝓠 (n + 1)) e e' p) i i' ∘ w) := by
  obtain ⟨j, hj, h1, -⟩ := exists_face_chartChange he he' hp hp' hi
  obtain rfl : j = i' := (hi' j).1 ((hj j).2 rfl)
  rw [restrictFace_apply, faceEmbedding_faceProjection ((hi' j).2 rfl)]
  congr 1
  funext l
  exact apply_faceEmbedding_eq (fun y => h1 _ (faceEmbedding_apply_self i y)) (w l)

omit [ChartedSpace (EuclideanQuadrant (n + 1)) M] [IsManifold (𝓠 (n + 1)) ∞ M] in
/-- The expression of a form in a chart `e'`, on the image of vectors under the chart change
derivative `D(e' ∘ e⁻¹)`, is its expression in `e`. -/
theorem chartForm_chartChangeDeriv_apply [ChartedSpace (EuclideanQuadrant (n + 1)) M]
    [IsManifold (𝓠 (n + 1)) ∞ M] {e e' : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ M) (β : ManifoldForm (𝓠 (n + 1)) M k)
    {p : M} (hp : p ∈ e.source) (hp' : p ∈ e'.source)
    (v : Fin k → EuclideanSpace ℝ (Fin (n + 1))) :
    ManifoldForm.chartForm (𝓠 (n + 1)) e' β (e'.extend (𝓠 (n + 1)) p)
        (chartChangeDeriv (𝓠 (n + 1)) e e' p ∘ v) =
      ManifoldForm.chartForm (𝓠 (n + 1)) e β (e.extend (𝓠 (n + 1)) p) v := by
  rw [ManifoldForm.chartForm_apply, ManifoldForm.chartForm_apply, e.extend_left_inv hp,
    e'.extend_left_inv hp']
  congr 1
  funext l
  exact chartChangeDeriv_comp_apply (by simp) he he'
    (IsManifold.chart_mem_maximalAtlas p) hp hp' (mem_chart_source _ p) (v l)

/-- **`j^*β` is a form on the faces** for every `C^∞` form `β` on `M` (in particular the
conditions of `IsChartFaceForm` are satisfiable). -/
theorem isChartFaceForm_faceRestriction {β : ManifoldForm (𝓠 (n + 1)) M k}
    (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) ∞ β) : IsChartFaceForm (faceRestriction β) where
  smooth := contDiffOn_faceRestriction hβ
  chartChange x x' p hp hp' i i' hi hi' w := by
    have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓠 (n + 1)) (n := ∞) x
    have hc' := IsManifold.chart_mem_maximalAtlas (I := 𝓠 (n + 1)) (n := ∞) x'
    rw [faceRestriction, ← restrictFace_chartChange hc hc' hp hp' hi hi',
      chartForm_chartChangeDeriv_apply hc hc' β hp hp', faceRestriction_apply,
      faceEmbedding_faceProjection ((hi i).2 rfl)]
  corner x i j y _ hyi hyj v hvi hvj :=
    (faceLift_facePullback i _ hyi hvi).trans (faceLift_facePullback j _ hyj hvj).symm

/-- **The face form `j^*β`** of a `C^∞` form `β` on `M`. -/
def ChartFaceForm.ofForm {β : ManifoldForm (𝓠 (n + 1)) M k}
    (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) ∞ β) : ChartFaceForm M n k :=
  ⟨faceRestriction β, isChartFaceForm_faceRestriction hβ⟩

end FaceForms

section Extension

variable {M : Type*} {n k : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

/-- **A form `β` on `M` extends the face data `σ`**: `j^*β = σ` on every face of every chart
`chartAt x`. -/
def IsExtendedBy (σ : FaceFormData M n k) (β : ManifoldForm (𝓠 (n + 1)) M k) : Prop :=
  ∀ x i, EqOn (faceRestriction β x i) (σ x i)
    (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)

theorem isExtendedBy_faceRestriction (β : ManifoldForm (𝓠 (n + 1)) M k) :
    IsExtendedBy (faceRestriction β) β := fun _ _ => eqOn_refl _ _

theorem IsExtendedBy.add {σ σ' : FaceFormData M n k} {β β' : ManifoldForm (𝓠 (n + 1)) M k}
    (h : IsExtendedBy σ β) (h' : IsExtendedBy σ' β') : IsExtendedBy (σ + σ') (β + β') :=
  fun x i u hu => by
    rw [faceRestriction_add]; simp only [Pi.add_apply]; rw [h x i hu, h' x i hu]

theorem IsExtendedBy.smul {σ : FaceFormData M n k} {β : ManifoldForm (𝓠 (n + 1)) M k} (a : ℝ)
    (h : IsExtendedBy σ β) : IsExtendedBy (a • σ) (a • β) := fun x i u hu => by
  rw [faceRestriction_smul]; simp only [Pi.smul_apply]; rw [h x i hu]

/-- **Agreement at the points of degeneracy index `1` suffices** for continuous data. -/
theorem isExtendedBy_of_openFaceDomain {σ : FaceFormData M n k}
    {β : ManifoldForm (𝓠 (n + 1)) M k}
    (hσ : ∀ x i, ContinuousOn (σ x i) (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i))
    (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 0 β)
    (h : ∀ x i, EqOn (faceRestriction β x i) (σ x i)
      (openFaceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)) : IsExtendedBy σ β :=
  fun x i => (h x i).of_subset_closure (contDiffOn_faceRestriction hβ x i).continuousOn (hσ x i)
    (openFaceDomain_subset _ _) (faceDomain_subset_closure _ _)

/-! ### Compact support -/

/-- **Face data with compact support**: all face forms vanish at the points outside a compact
subset `K` of `M`. -/
def HasCompactFaceSupport (σ : FaceFormData M n k) : Prop :=
  ∃ K : Set M, IsCompact K ∧ ∀ x i, ∀ u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i,
    facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u ∉ K → σ x i u = 0

theorem hasCompactFaceSupport_of_compactSpace [CompactSpace M] (σ : FaceFormData M n k) :
    HasCompactFaceSupport σ :=
  ⟨univ, isCompact_univ, fun _ _ _ _ h => absurd (mem_univ _) h⟩

theorem hasCompactFaceSupport_faceRestriction {β : ManifoldForm (𝓠 (n + 1)) M k}
    (hc : IsCompact (ManifoldForm.tsupport β)) : HasCompactFaceSupport (faceRestriction β) :=
  ⟨_, hc, fun x i u _ hu => by
    ext w
    rw [faceRestriction_apply, ManifoldForm.chartForm_eq_zero_of_notMem
      (fun _ => ManifoldForm.eq_zero_of_notMem_tsupport) _ hu]
    rfl⟩

theorem HasCompactFaceSupport.add {σ σ' : FaceFormData M n k} (h : HasCompactFaceSupport σ)
    (h' : HasCompactFaceSupport σ') : HasCompactFaceSupport (σ + σ') := by
  obtain ⟨K, hK, hK0⟩ := h
  obtain ⟨K', hK', hK'0⟩ := h'
  refine ⟨K ∪ K', hK.union hK', fun x i u hu hp => ?_⟩
  rw [mem_union, not_or] at hp
  simp only [Pi.add_apply, hK0 x i u hu hp.1, hK'0 x i u hu hp.2, add_zero]

theorem HasCompactFaceSupport.smul {σ : FaceFormData M n k} (a : ℝ)
    (h : HasCompactFaceSupport σ) : HasCompactFaceSupport (a • σ) := by
  obtain ⟨K, hK, hK0⟩ := h
  exact ⟨K, hK, fun x i u hu hp => by simp only [Pi.smul_apply, hK0 x i u hu hp, smul_zero]⟩

/-! ### Multiplication by functions -/

/-- The face data `σ` multiplied by a function `f` on `M`. -/
def smulFace (f : M → ℝ) (σ : FaceFormData M n k) : FaceFormData M n k :=
  fun x i u => f (facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u) • σ x i u

theorem faceRestriction_smulFun (f : M → ℝ) (β : ManifoldForm (𝓠 (n + 1)) M k) :
    faceRestriction (ManifoldForm.smulFun f β) = smulFace f (faceRestriction β) := by
  funext x i u; ext w; rfl

theorem IsExtendedBy.smulFun {σ : FaceFormData M n k} {β : ManifoldForm (𝓠 (n + 1)) M k}
    (f : M → ℝ) (h : IsExtendedBy σ β) :
    IsExtendedBy (smulFace f σ) (ManifoldForm.smulFun f β) := fun x i u hu => by
  rw [faceRestriction_smulFun]; simp only [smulFace]; rw [h x i hu]

theorem hasCompactFaceSupport_smulFace {f : M → ℝ} (hf : HasCompactSupport f)
    (σ : FaceFormData M n k) : HasCompactFaceSupport (smulFace f σ) :=
  ⟨_root_.tsupport f, hf, fun x i u _ hu => by
    simp only [smulFace, image_eq_zero_of_notMem_tsupport hu, zero_smul]⟩

variable [IsManifold (𝓠 (n + 1)) ∞ M]

theorem isChartFaceForm_smulFace {f : M → ℝ} (hf : ContMDiff (𝓠 (n + 1)) 𝓘(ℝ) ∞ f)
    {σ : FaceFormData M n k} (hσ : IsChartFaceForm σ) : IsChartFaceForm (smulFace f σ) where
  smooth x i := by
    have hf' : ContDiffOn ℝ ∞ (f ∘ (extChartAt (𝓠 (n + 1)) x).symm)
        (extChartAt (𝓠 (n + 1)) x).target :=
      contMDiffOn_iff_contDiffOn.1 (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))
    exact (hf'.comp (faceEmbedding i).contDiff.contDiffOn (mapsTo_preimage _ _)).smul
      (hσ.smooth x i)
  chartChange x x' p hp hp' i i' hi hi' w := by
    simp only [smulFace, ContinuousAlternatingMap.smul_apply]
    rw [facePoint_faceProjection_extend hp' ((hi' i').2 rfl),
      facePoint_faceProjection_extend hp ((hi i).2 rfl), hσ.chartChange x x' p hp hp' i i' hi hi' w]
  corner x i j y hy hyi hyj v hvi hvj := by
    have h1 := hσ.corner x i j y hy hyi hyj v hvi hvj
    simp only [faceLift_apply] at h1 ⊢
    simp only [smulFace, ContinuousAlternatingMap.smul_apply]
    rw [facePoint_faceProjection hyi, facePoint_faceProjection hyj, h1]

/-! ### The extension -/

omit [IsManifold (𝓠 (n + 1)) ∞ M] in
/-- **Local extension in a box chart**: near `e(x₀)`, `e = chartAt x₀`, the inclusion–exclusion
sum of the face forms of `e` is a smooth form on a box `N = O ∩ [0,∞)ⁿ⁺¹` (contained in a compact
`C` inside the chart target) whose restriction to each face is the given face form. -/
theorem exists_local_extension {σ : FaceFormData M n k} (hσ : IsChartFaceForm σ) (x₀ : M) :
    ∃ (O C : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (η : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ),
      IsOpen O ∧ (chartAt (EuclideanQuadrant (n + 1)) x₀).extend (𝓠 (n + 1)) x₀ ∈ O ∧
      IsCompact C ∧ O ∩ closedQuadrant univ ⊆ C ∧
      C ⊆ ((chartAt (EuclideanQuadrant (n + 1)) x₀).extend (𝓠 (n + 1))).target ∧
      ContDiffOn ℝ ∞ η (O ∩ closedQuadrant univ) ∧
      ∀ b u, faceEmbedding b u ∈ O ∩ closedQuadrant univ → restrictFace b η u = σ x₀ b u := by
  set c := chartAt (EuclideanQuadrant (n + 1)) x₀
  set U := (𝓠 (n + 1)).symm ⁻¹' c.target
  have hU : IsOpen U := c.open_target.preimage (𝓠 (n + 1)).continuous_symm
  have hT : (c.extend (𝓠 (n + 1))).target = U ∩ closedQuadrant univ := by
    rw [ManifoldForm.extend_target_eq_inter_quadrant, Finset.coe_univ]
  have hy₀ : c.extend (𝓠 (n + 1)) x₀ ∈ U ∩ closedQuadrant univ := by
    rw [← hT]; exact (c.extend _).map_source (by rw [c.extend_source]; exact mem_chart_source _ x₀)
  obtain ⟨O, J, C, hO, hy₀O, hC, hOC, hCU, hJ, hface⟩ := exists_box hU hy₀.1 hy₀.2
  have hNT : O ∩ closedQuadrant univ ⊆ (c.extend (𝓠 (n + 1))).target := hT ▸ hOC.trans hCU
  refine ⟨O, C, inclExcl J (σ x₀), hO, hy₀O, hC, hOC, hT ▸ hCU,
    contDiffOn_inclExcl hJ fun a _ => (hσ.smooth x₀ a).mono (preimage_mono hNT),
    fun b u hu => ?_⟩
  exact facePullback_inclExcl hJ (fun a b' y hy => hσ.corner x₀ a b' y (hNT hy))
    (hface _ hu b (faceEmbedding_apply_self b u)) hu

omit [ChartedSpace (EuclideanQuadrant (n + 1)) M] [IsManifold (𝓠 (n + 1)) ∞ M] in
/-- A point of a box `O` of a chart lies in the quadrant part of the box. -/
theorem extend_mem_inter_quadrant {e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))}
    {O : Set (EuclideanSpace ℝ (Fin (n + 1)))} {p : M}
    (hp : p ∈ e.source ∩ e.extend (𝓠 (n + 1)) ⁻¹' O) :
    e.extend (𝓠 (n + 1)) p ∈ O ∩ closedQuadrant univ := by
  refine ⟨hp.2, ?_⟩
  rw [← range_modelWithCornersEuclideanQuadrant, e.extend_coe]
  exact mem_range_self _

/-- The face restriction of `ρ · (form with expression η in the chart at x₀)`, at a point of
degeneracy index `1` of the face `{xᵢ = 0}` of the chart at `x`: `ρ(p) σ`, when `η` restricts to
the face forms of the chart at `x₀` on the box `N` and `ρ` is supported in the box. -/
theorem faceRestriction_smulFun_ofChartForm {σ : FaceFormData M n k} (hσ : IsChartFaceForm σ)
    {x₀ : M} {N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {η : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin k]→L[ℝ] ℝ}
    (hη : ∀ b u, faceEmbedding b u ∈ N → restrictFace b η u = σ x₀ b u) {ρ : M → ℝ}
    (hρ : _root_.tsupport ρ ⊆ (chartAt (EuclideanQuadrant (n + 1)) x₀).source ∩
      (chartAt (EuclideanQuadrant (n + 1)) x₀).extend (𝓠 (n + 1)) ⁻¹' N)
    {x : M} {i : Fin (n + 1)} {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ openFaceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) :
    faceRestriction (ManifoldForm.smulFun ρ (ManifoldForm.ofChartForm
      (chartAt (EuclideanQuadrant (n + 1)) x₀) η)) x i u =
      ρ (facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u) • σ x i u := by
  set c := chartAt (EuclideanQuadrant (n + 1)) x
  set c₀ := chartAt (EuclideanQuadrant (n + 1)) x₀
  have hu' := openFaceDomain_subset _ _ hu
  set p := facePoint c i u
  have hp : p ∈ c.source := facePoint_mem_source hu'
  have hpe : c.extend (𝓠 (n + 1)) p = faceEmbedding i u := extend_facePoint hu'
  have hi : ∀ l, c.extend (𝓠 (n + 1)) p l = 0 ↔ l = i := by
    rw [hpe]; exact faceEmbedding_eq_zero_iff hu
  rw [faceRestriction_smulFun]
  simp only [smulFace]
  by_cases hρp : ρ p = 0
  · simp only [p] at hρp; rw [hρp, zero_smul, zero_smul]
  congr 1
  have hpN := hρ (subset_tsupport _ hρp)
  have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓠 (n + 1)) (n := ∞) x
  have hc₀ := IsManifold.chart_mem_maximalAtlas (I := 𝓠 (n + 1)) (n := ∞) x₀
  obtain ⟨i', hi', -, -⟩ := exists_face_chartChange hc hc₀ hp hpN.1 hi
  ext w
  rw [faceRestriction_apply, ← hpe, ManifoldForm.chartForm_ofChartForm_apply hc₀ hc hpN.1 hp,
    restrictFace_chartChange hc hc₀ hp hpN.1 hi hi',
    hη i' _ (by rw [faceEmbedding_faceProjection ((hi' i').2 rfl)]; exact hpN.2),
    hσ.chartChange x x₀ p hp hpN.1 i i' hi hi' w, hpe, faceProjection_faceEmbedding]

/-- **Existence of extensions** (for the reading of forms on `∂X`, 2021 p. 198, and their
integral in Theorem 6.7.1, 2021 p. 277): every
compactly supported form on the faces of a Hausdorff σ-compact manifold with corners `M` is the
face restriction `j^*β` of a `C^∞` form `β` on `M` with compact support (inclusion–exclusion in box
charts, `exists_local_extension`, glued by a partition of unity). -/
theorem exists_extension [T2Space M] [SigmaCompactSpace M] {σ : FaceFormData M n k}
    (hσ : IsChartFaceForm σ) (hc : HasCompactFaceSupport σ) :
    ∃ β : ManifoldForm (𝓠 (n + 1)) M k, ManifoldForm.ContMDiffForm (𝓠 (n + 1)) ∞ β ∧
      IsCompact (ManifoldForm.tsupport β) ∧ IsExtendedBy σ β := by
  classical
  obtain ⟨K, hK, hK0⟩ := hc
  choose O C η hO hxO hC hOC hCT hη hres using exists_local_extension hσ
  set V : M → Set M := fun x => (chartAt (EuclideanQuadrant (n + 1)) x).source ∩
    (chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1)) ⁻¹' O x with hV
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    (chartAt (EuclideanQuadrant (n + 1)) x).isOpen_extend_preimage (hO x)
  have hxV : ∀ x, x ∈ V x := fun x => ⟨mem_chart_source _ x, hxO x⟩
  have hVN : ∀ x, V x ⊆ (chartAt (EuclideanQuadrant (n + 1)) x).source ∩
      (chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1)) ⁻¹' (O x ∩ closedQuadrant univ) :=
    fun x p hp => ⟨hp.1, extend_mem_inter_quadrant hp⟩
  have hVK : ∀ x, V x ⊆ ((chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1))).symm '' C x :=
    fun x p hp => ⟨_, hOC x (extend_mem_inter_quadrant hp),
      (chartAt (EuclideanQuadrant (n + 1)) x).extend_left_inv hp.1⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓠 (n + 1)) isClosed_univ V hVo
    fun x _ => mem_iUnion.2 ⟨x, hxV x⟩
  have hfK : ∀ j, IsCompact (_root_.tsupport (f j)) := fun j =>
    ((hC j).image_of_continuousOn
      (((chartAt (EuclideanQuadrant (n + 1)) j).continuousOn_extend_symm).mono
        (hCT j))).of_isClosed_subset (isClosed_tsupport _) ((hf j).trans (hVK j))
  have hT := f.locallyFinite.finite_nonempty_inter_compact hK
  set T := hT.toFinset
  set β : ManifoldForm (𝓠 (n + 1)) M k := ∑ j ∈ T, ManifoldForm.smulFun (f j)
    (ManifoldForm.ofChartForm (chartAt (EuclideanQuadrant (n + 1)) j) (η j)) with hβ_def
  have hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) ∞ β :=
    ManifoldForm.ContMDiffForm.finsetSum T fun j _ =>
      ManifoldForm.contMDiffForm_smulFun_ofChartForm (IsManifold.chart_mem_maximalAtlas j)
        (fun y hy => by
          rw [range_modelWithCornersEuclideanQuadrant]
          exact inter_mem (mem_nhdsWithin_of_mem_nhds ((hO j).mem_nhds hy.1)) self_mem_nhdsWithin)
        (hη j) (f j).contMDiff ((hf j).trans (hVN j))
  refine ⟨β, hβ, ?_, ?_⟩
  · refine (T.isCompact_biUnion fun j _ => hfK j).of_isClosed_subset isClosed_closure
      ((ManifoldForm.tsupport_finsetSum_subset T _).trans
        (iUnion₂_mono fun j _ => (ManifoldForm.tsupport_smulFun_subset _ _).trans
          inter_subset_left))
  refine isExtendedBy_of_openFaceDomain (fun x i => (hσ.smooth x i).continuousOn)
    (hβ.of_le (by norm_num)) fun x i u hu => ?_
  have hu' := openFaceDomain_subset _ _ hu
  set p := facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u
  have hsum : faceRestriction β x i u = (∑ j ∈ T, f j p) • σ x i u := by
    rw [hβ_def, Finset.sum_smul]
    have : faceRestriction (∑ j ∈ T, ManifoldForm.smulFun (f j)
        (ManifoldForm.ofChartForm (chartAt (EuclideanQuadrant (n + 1)) j) (η j))) x i u =
        ∑ j ∈ T, faceRestriction (ManifoldForm.smulFun (f j)
          (ManifoldForm.ofChartForm (chartAt (EuclideanQuadrant (n + 1)) j) (η j))) x i u := by
      ext w
      simp only [faceRestriction_apply, ManifoldForm.chartForm_finsetSum,
        ContinuousAlternatingMap.sum_apply, Finset.sum_apply]
    rw [this]
    exact Finset.sum_congr rfl fun j _ =>
      faceRestriction_smulFun_ofChartForm hσ (hres j) ((hf j).trans (hVN j)) hu
  rw [hsum]
  by_cases hpK : p ∈ K
  · have h1 : ∑ j ∈ T, f j p = 1 := by
      rw [← f.sum_eq_one (mem_univ p)]
      refine (finsum_eq_sum_of_support_subset _ fun j hj => ?_).symm
      rw [Set.Finite.coe_toFinset]
      exact ⟨p, hj, hpK⟩
    rw [h1, one_smul]
  · rw [hK0 x i u hu' hpK, smul_zero]

end Extension

section FaceD

variable {M : Type*} {n k : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

open Classical in
/-- **The exterior derivative of face data**, face by face: `d` within the face parameter set
(`0` outside it, so that `d` is linear and `d ∘ d = 0` hold exactly, `FaceFormData.d_add`,
`FaceFormData.d_d`). -/
def FaceFormData.d (σ : FaceFormData M n k) : FaceFormData M n (k + 1) :=
  fun x i u => if u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i then
    extDerivWithin (σ x i) (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) u else 0

theorem FaceFormData.d_apply_of_mem (σ : FaceFormData M n k) {x : M} {i : Fin (n + 1)}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) :
    FaceFormData.d σ x i u =
      extDerivWithin (σ x i) (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) u := by
  simp only [FaceFormData.d, if_pos hu]

theorem FaceFormData.d_apply_of_notMem (σ : FaceFormData M n k) {x : M} {i : Fin (n + 1)}
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∉ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) :
    FaceFormData.d σ x i u = 0 := by
  simp only [FaceFormData.d, if_neg hu]

variable [IsManifold (𝓠 (n + 1)) ∞ M]

/-- **`j^*(dβ) = d(j^*β)`** (2021 p. 198, `d(ω, τ) = (dω, j^*ω − dτ)` needs it): the face
restriction commutes with `d` (`extDerivWithin_pullback` along the linear face embedding). -/
theorem faceRestriction_extDeriv {β : ManifoldForm (𝓠 (n + 1)) M k}
    (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β) (x : M) (i : Fin (n + 1)) :
    EqOn (faceRestriction (ManifoldForm.extDeriv β) x i) (FaceFormData.d (faceRestriction β) x i)
      (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i) := by
  intro u hu
  set c := chartAt (EuclideanQuadrant (n + 1)) x
  have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓠 (n + 1)) (n := ∞) x
  have hD := uniqueDiffOn_faceDomain c i
  have hω : DifferentiableWithinAt ℝ (ManifoldForm.chartForm (𝓠 (n + 1)) c β)
      (c.extend (𝓠 (n + 1))).target (faceEmbedding i u) :=
    ((hβ x).differentiableOn one_ne_zero) _ hu
  have key := extDerivWithin_pullback hω ((faceEmbedding i).contDiff (n := 2)).contDiffWithinAt
    (by rw [minSmoothness_of_isRCLikeNormedField]) hD (faceDomain_subset_closure_interior c i hu)
    hu (mapsTo_preimage _ _)
  rw [(faceEmbedding i).fderivWithin (hD u hu)] at key
  have h1 : faceRestriction (ManifoldForm.extDeriv β) x i u =
      (extDerivWithin (ManifoldForm.chartForm (𝓠 (n + 1)) c β) (c.extend (𝓠 (n + 1))).target
        (faceEmbedding i u)).compContinuousLinearMap (faceEmbedding i) := by
    rw [← ManifoldForm.chartForm_extDeriv_of_mem_target hc hβ hu]; rfl
  rw [FaceFormData.d_apply_of_mem _ hu, h1, ← key]
  exact extDerivWithin_congr' (fun u' hu' => by
    change _ = formPullback (faceEmbedding i) (fun _ => faceEmbedding i) _ u'
    rw [formPullback, (faceEmbedding i).fderivWithin (hD u' hu')]) hu

/-- **`IsExtendedBy` commutes with `d`.** -/
theorem IsExtendedBy.extDeriv {σ : FaceFormData M n k} {β : ManifoldForm (𝓠 (n + 1)) M k}
    (h : IsExtendedBy σ β) (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β) :
    IsExtendedBy (FaceFormData.d σ) (ManifoldForm.extDeriv β) := fun x i _ hu =>
  (faceRestriction_extDeriv hβ x i hu).trans (by
    rw [FaceFormData.d_apply_of_mem _ hu, FaceFormData.d_apply_of_mem _ hu]
    exact extDerivWithin_congr' (h x i) hu)

variable [T2Space M] [SigmaCompactSpace M]

/-- **`d` of face forms is local**: near every point `q`, the face data `dσ` are the face
restriction of `dβ` for a `C^∞` form `β` (an extension of `χ σ`, `χ` a bump function at `q`). -/
theorem exists_d_eq_faceRestriction {σ : FaceFormData M n k} (hσ : IsChartFaceForm σ) (q : M) :
    ∃ (β : ManifoldForm (𝓠 (n + 1)) M k) (W : Set M),
      ManifoldForm.ContMDiffForm (𝓠 (n + 1)) ∞ β ∧ IsOpen W ∧ q ∈ W ∧
      ∀ x i, ∀ u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i,
        facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u ∈ W →
        FaceFormData.d σ x i u = faceRestriction (ManifoldForm.extDeriv β) x i u := by
  let χ : SmoothBumpFunction (𝓠 (n + 1)) q := Classical.arbitrary _
  obtain ⟨W, hWsub, hWo, hqW⟩ := mem_nhds_iff.1 χ.eventuallyEq_one
  obtain ⟨β, hβ, -, hext⟩ := exists_extension (isChartFaceForm_smulFace χ.contMDiff hσ)
    (hasCompactFaceSupport_smulFace χ.hasCompactSupport σ)
  refine ⟨β, W, hβ, hWo, hqW, fun x i u hu hpW => ?_⟩
  have hev : smulFace χ σ x i =ᶠ[𝓝[faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i] u]
      σ x i := by
    filter_upwards [(continuousOn_facePoint _ i u hu).preimage_mem_nhdsWithin
      (hWo.mem_nhds hpW)] with u' hu'
    have : χ (facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u') = 1 := hWsub hu'
    simp only [smulFace, this, one_smul]
  rw [(hext.extDeriv (hβ.of_le (by norm_num))) x i hu, FaceFormData.d_apply_of_mem _ hu,
    FaceFormData.d_apply_of_mem _ hu]
  exact (hev.extDerivWithin_eq_of_mem hu).symm

/-- **`dσ` is a form on the faces** for every form `σ` on the faces. -/
theorem isChartFaceForm_d {σ : FaceFormData M n k} (hσ : IsChartFaceForm σ) :
    IsChartFaceForm (FaceFormData.d σ) where
  smooth x i u hu := by
    obtain ⟨β, W, hβ, hWo, hqW, hβeq⟩ := exists_d_eq_faceRestriction hσ
      (facePoint (chartAt (EuclideanQuadrant (n + 1)) x) i u)
    have hev : FaceFormData.d σ x i =ᶠ[𝓝[faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i] u]
        faceRestriction (ManifoldForm.extDeriv β) x i := by
      filter_upwards [(continuousOn_facePoint _ i u hu).preimage_mem_nhdsWithin
        (hWo.mem_nhds hqW), self_mem_nhdsWithin] with u' hu' hu'D
      exact hβeq x i u' hu'D hu'
    exact ((contDiffOn_faceRestriction ((hβ.of_le (add_one_le_infty le_rfl)).extDeriv) x i) u
      hu).congr_of_eventuallyEq hev (hβeq x i u hu hqW)
  chartChange x x' p hp hp' i i' hi hi' w := by
    obtain ⟨β, W, hβ, -, hqW, hβeq⟩ := exists_d_eq_faceRestriction hσ p
    rw [hβeq x' i' _ (faceProjection_extend_mem_faceDomain hp' ((hi' i').2 rfl))
        (by rw [facePoint_faceProjection_extend hp' ((hi' i').2 rfl)]; exact hqW),
      hβeq x i _ (faceProjection_extend_mem_faceDomain hp ((hi i).2 rfl))
        (by rw [facePoint_faceProjection_extend hp ((hi i).2 rfl)]; exact hqW)]
    exact (isChartFaceForm_faceRestriction
      ((hβ.of_le (add_one_le_infty le_rfl)).extDeriv)).chartChange x x' p hp hp' i i' hi hi' w
  corner x i j y hy hyi hyj v hvi hvj := by
    obtain ⟨β, W, hβ, -, hqW, hβeq⟩ := exists_d_eq_faceRestriction hσ
      (((chartAt (EuclideanQuadrant (n + 1)) x).extend (𝓠 (n + 1))).symm y)
    have := (isChartFaceForm_faceRestriction
      ((hβ.of_le (add_one_le_infty le_rfl)).extDeriv)).corner x i j y hy hyi hyj v hvi hvj
    simp only [faceLift_apply] at this ⊢
    rw [hβeq x i _ (faceProjection_mem_faceDomain hy hyi)
        (by rw [facePoint_faceProjection hyi]; exact hqW),
      hβeq x j _ (faceProjection_mem_faceDomain hy hyj)
        (by rw [facePoint_faceProjection hyj]; exact hqW), this]

omit [IsManifold (𝓠 (n + 1)) ∞ M] [SigmaCompactSpace M] in
/-- `dσ` has compact support if `σ` has. -/
theorem HasCompactFaceSupport.d {σ : FaceFormData M n k} (h : HasCompactFaceSupport σ) :
    HasCompactFaceSupport (FaceFormData.d σ) := by
  obtain ⟨K, hK, hK0⟩ := h
  refine ⟨K, hK, fun x i u hu hpK => ?_⟩
  have hev : σ x i =ᶠ[𝓝[faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i] u] 0 := by
    filter_upwards [(continuousOn_facePoint _ i u hu).preimage_mem_nhdsWithin
      (hK.isClosed.isOpen_compl.mem_nhds hpK), self_mem_nhdsWithin] with u' hu' hu'D
    exact hK0 x i u' hu'D hu'
  rw [FaceFormData.d_apply_of_mem _ hu, hev.extDerivWithin_eq_of_mem hu]
  ext v
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

/-- **The exterior derivative `d : Ω^k(∂M) → Ω^{k+1}(∂M)`** of forms on the faces (2021 p. 198,
`d` on `Ω*(∂X)`, here for the faces of `M`). -/
def ChartFaceForm.d (τ : ChartFaceForm M n k) : ChartFaceForm M n (k + 1) :=
  ⟨FaceFormData.d τ, isChartFaceForm_d τ.2⟩

theorem ChartFaceForm.coe_d (τ : ChartFaceForm M n k) :
    ((ChartFaceForm.d τ : ChartFaceForm M n (k + 1)) : FaceFormData M n (k + 1)) =
      FaceFormData.d τ := rfl

omit [IsManifold (𝓠 (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem FaceFormData.d_add {σ σ' : FaceFormData M n k} (hσ : IsChartFaceForm σ)
    (hσ' : IsChartFaceForm σ') :
    FaceFormData.d (σ + σ') = FaceFormData.d σ + FaceFormData.d σ' := by
  funext x i u
  simp only [Pi.add_apply]
  by_cases hu : u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i
  · rw [FaceFormData.d_apply_of_mem _ hu, FaceFormData.d_apply_of_mem _ hu,
      FaceFormData.d_apply_of_mem _ hu]
    exact extDerivWithin_add (uniqueDiffOn_faceDomain _ i u hu)
      ((hσ.smooth x i).differentiableOn (by simp) u hu)
      ((hσ'.smooth x i).differentiableOn (by simp) u hu)
  · rw [FaceFormData.d_apply_of_notMem _ hu, FaceFormData.d_apply_of_notMem _ hu,
      FaceFormData.d_apply_of_notMem _ hu, add_zero]

omit [IsManifold (𝓠 (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem FaceFormData.d_smul (a : ℝ) (σ : FaceFormData M n k) :
    FaceFormData.d (a • σ) = a • FaceFormData.d σ := by
  funext x i u
  simp only [Pi.smul_apply]
  by_cases hu : u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i
  · rw [FaceFormData.d_apply_of_mem _ hu, FaceFormData.d_apply_of_mem _ hu]
    exact extDerivWithin_smul a (σ x i) (uniqueDiffOn_faceDomain _ i u hu)
  · rw [FaceFormData.d_apply_of_notMem _ hu, FaceFormData.d_apply_of_notMem _ hu, smul_zero]

omit [IsManifold (𝓠 (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M] in
/-- **`d ∘ d = 0` on the faces.** -/
theorem FaceFormData.d_d {σ : FaceFormData M n k} (hσ : IsChartFaceForm σ) :
    FaceFormData.d (FaceFormData.d σ) = 0 := by
  funext x i u
  by_cases hu : u ∈ faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i
  · rw [FaceFormData.d_apply_of_mem _ hu,
      extDerivWithin_congr' (fun u' hu' => FaceFormData.d_apply_of_mem σ hu') hu]
    exact extDerivWithin_extDerivWithin_apply ((hσ.smooth x i) u hu)
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
      (uniqueDiffOn_faceDomain _ i) (faceDomain_subset_closure_interior _ i hu) hu
  · exact FaceFormData.d_apply_of_notMem _ hu

theorem ChartFaceForm.d_add (τ τ' : ChartFaceForm M n k) :
    ChartFaceForm.d (τ + τ') = ChartFaceForm.d τ + ChartFaceForm.d τ' :=
  Subtype.ext (FaceFormData.d_add τ.2 τ'.2)

theorem ChartFaceForm.d_smul (a : ℝ) (τ : ChartFaceForm M n k) :
    ChartFaceForm.d (a • τ) = a • ChartFaceForm.d τ :=
  Subtype.ext (FaceFormData.d_smul a (τ : FaceFormData M n k))

/-- **`d : Ω^k(∂M) → Ω^{k+1}(∂M)` as a linear map.** -/
def ChartFaceForm.dₗ : ChartFaceForm M n k →ₗ[ℝ] ChartFaceForm M n (k + 1) where
  toFun := ChartFaceForm.d
  map_add' := ChartFaceForm.d_add
  map_smul' := ChartFaceForm.d_smul

/-- **`d ∘ d = 0` on `Ω^*(∂M)`.** -/
theorem ChartFaceForm.d_d (τ : ChartFaceForm M n k) :
    ChartFaceForm.d (ChartFaceForm.d τ) = 0 :=
  Subtype.ext (FaceFormData.d_d τ.2)

end FaceD

open MeasureTheory

/-! ### Linearity of the boundary integral of forms on `M` -/

section BoundaryLinear

variable {M : Type*} {n k : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]

theorem chartForm_const_smul (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1))) (a : ℝ)
    (ω : ManifoldForm (𝓠 (n + 1)) M k) :
    ManifoldForm.chartForm (𝓠 (n + 1)) e (a • ω) = a • ManifoldForm.chartForm (𝓠 (n + 1)) e ω := by
  funext y; ext v; rfl

theorem contMDiffForm_const_smul {r : WithTop ℕ∞} (a : ℝ) {ω : ManifoldForm (𝓠 (n + 1)) M k}
    (hω : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) r ω) :
    ManifoldForm.ContMDiffForm (𝓠 (n + 1)) r (a • ω) := fun x => by
  rw [chartForm_const_smul]; exact (hω x).const_smul a

theorem tsupport_const_smul_subset (a : ℝ) (ω : ManifoldForm (𝓠 (n + 1)) M k) :
    ManifoldForm.tsupport (a • ω) ⊆ ManifoldForm.tsupport ω :=
  closure_mono fun x hx h => hx (by
    change a • ω x = 0
    rw [show ω x = 0 from h, smul_zero])

theorem tsupport_add_subset (ω ω' : ManifoldForm (𝓠 (n + 1)) M k) :
    ManifoldForm.tsupport (ω + ω') ⊆ ManifoldForm.tsupport ω ∪ ManifoldForm.tsupport ω' := by
  refine (closure_mono fun x hx => ?_).trans closure_union.subset
  by_contra h
  rw [mem_union, not_or] at h
  have h1 : ω x = 0 := not_not.1 h.1
  have h2 : ω' x = 0 := not_not.1 h.2
  exact hx (show ω x + ω' x = 0 by rw [h1, h2, add_zero])

theorem chartBoundaryIntegral_const_smul (e : OpenPartialHomeomorph M (EuclideanQuadrant (n + 1)))
    (a : ℝ) (ω : ManifoldForm (𝓠 (n + 1)) M n) :
    ManifoldForm.chartBoundaryIntegral e (a • ω) = a * ManifoldForm.chartBoundaryIntegral e ω := by
  simp only [ManifoldForm.chartBoundaryIntegral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  congr 1
  rw [topFormIntegral, topFormIntegral, ← integral_const_mul]
  rfl

variable [IsManifold (𝓠 (n + 1)) ∞ M]

omit [IsManifold (𝓠 (n + 1)) ∞ M] in
theorem IntegrationData.boundaryIntegral_const_smul
    {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)} {s : Set M} {ι : Type*} [Fintype ι]
    (D : IntegrationData M o s ι) (a : ℝ) (ω : ManifoldForm (𝓠 (n + 1)) M n) :
    D.boundaryIntegral (a • ω) = a * D.boundaryIntegral ω := by
  simp only [IntegrationData.boundaryIntegral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ManifoldForm.smulFun (D.ρ j) (a • ω) = a • ManifoldForm.smulFun (D.ρ j) ω := by
    funext x
    change D.ρ j x • (a • ω x) = a • (D.ρ j x • ω x)
    exact smul_comm _ _ _
  rw [this, chartBoundaryIntegral_const_smul, mul_left_comm]

variable [T2Space M] [SigmaCompactSpace M] {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)}

/-- `∫_{∂M}` is homogeneous on `C¹` compactly supported forms. -/
theorem boundaryIntegral_const_smul (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {ω : ManifoldForm (𝓠 (n + 1)) M n} (hω : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hc : IsCompact (ManifoldForm.tsupport ω)) (a : ℝ) :
    ManifoldForm.boundaryIntegral o (a • ω) = a * ManifoldForm.boundaryIntegral o ω := by
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [ManifoldForm.boundaryIntegral_eq_integrationData ho (contMDiffForm_const_smul a hω)
      (hc.of_isClosed_subset isClosed_closure (tsupport_const_smul_subset a ω)) D
      (tsupport_const_smul_subset a ω),
    ManifoldForm.boundaryIntegral_eq_integrationData ho hω hc D subset_rfl,
    D.boundaryIntegral_const_smul]

/-- `∫_{∂M}` is additive on `C¹` compactly supported forms (both sides are `∫_M d(·)`). -/
theorem boundaryIntegral_add (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {ω ω' : ManifoldForm (𝓠 (n + 1)) M n} (hω : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 ω)
    (hω' : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 ω')
    (hc : IsCompact (ManifoldForm.tsupport ω)) (hc' : IsCompact (ManifoldForm.tsupport ω')) :
    ManifoldForm.boundaryIntegral o (ω + ω') =
      ManifoldForm.boundaryIntegral o ω + ManifoldForm.boundaryIntegral o ω' := by
  have hcs := (hc.union hc').of_isClosed_subset isClosed_closure (tsupport_add_subset ω ω')
  have hd : ∀ {η : ManifoldForm (𝓠 (n + 1)) M n}, IsCompact (ManifoldForm.tsupport η) →
      IsCompact (ManifoldForm.tsupport (ManifoldForm.extDeriv η)) := fun h =>
    h.of_isClosed_subset isClosed_closure (ManifoldForm.tsupport_extDeriv_subset _)
  rw [← ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho (hω.add hω') hcs,
    ← ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho hω hc,
    ← ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho hω' hc',
    ManifoldForm.extDeriv_add hω hω']
  exact ManifoldForm.integral_add ho (ManifoldForm.contMDiffForm_zero_extDeriv hω)
    (ManifoldForm.contMDiffForm_zero_extDeriv hω') (hd hc) (hd hc')

/-- **Agreement on the faces gives the same boundary integral** (for Theorem 6.7.1, 2021 p. 277):
two `C¹` compactly supported `n`-forms whose face restrictions agree at the points of degeneracy
index `1` of every face of every chart `chartAt x` have the same integral over `∂M`. -/
theorem boundaryIntegral_congr_face (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {β β' : ManifoldForm (𝓠 (n + 1)) M n} (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β)
    (hβ' : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β')
    (hc : IsCompact (ManifoldForm.tsupport β)) (hc' : IsCompact (ManifoldForm.tsupport β'))
    (h : ∀ x i, EqOn (faceRestriction β x i) (faceRestriction β' x i)
      (openFaceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)) :
    ManifoldForm.boundaryIntegral o β = ManifoldForm.boundaryIntegral o β' := by
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho (hc.union hc')
  rw [ManifoldForm.boundaryIntegral_eq_integrationData ho hβ hc D subset_union_left,
    ManifoldForm.boundaryIntegral_eq_integrationData ho hβ' hc' D subset_union_right,
    IntegrationData.boundaryIntegral, IntegrationData.boundaryIntegral]
  refine Finset.sum_congr rfl fun j _ => congrArg _ ?_
  rw [ManifoldForm.chartBoundaryIntegral_eq_sum_openQuadrant,
    ManifoldForm.chartBoundaryIntegral_eq_sum_openQuadrant]
  refine Finset.sum_congr rfl fun i _ => congrArg _
    (topFormIntegral_congr (isOpen_openFaceDomain _ i).measurableSet fun u hu => ?_)
  ext w
  have := congrArg (fun φ => φ w) (h (D.center j) i hu)
  simp only [faceRestriction_apply] at this
  change ManifoldForm.chartForm (𝓠 (n + 1)) (D.chart j) (ManifoldForm.smulFun (D.ρ j) β)
      (faceEmbedding i u) (faceEmbedding i ∘ w) =
    ManifoldForm.chartForm (𝓠 (n + 1)) (D.chart j) (ManifoldForm.smulFun (D.ρ j) β')
      (faceEmbedding i u) (faceEmbedding i ∘ w)
  rw [ManifoldForm.chartForm_smulFun, ManifoldForm.chartForm_smulFun,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply, this]

end BoundaryLinear

/-! ### The integral over `∂M` of forms on the faces -/

section FaceIntegral

variable {M : Type*} {n : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1)) M]
  [IsManifold (𝓠 (n + 1)) ∞ M]

open Classical in
/-- **The integral `∫_{∂M} σ` of top-degree face data** (Theorem 6.7.1, 2021 p. 277, uses it for
`∂S`): the boundary integral `∫_{∂M} β` (outward vector first, Definition 9.3.8) of a `C¹`
compactly supported extension `β` of `σ` (`0` if there is none).  It does not depend on the
extension (`faceIntegral_eq`). -/
def faceIntegral (o : TangentOrientation (𝓠 (n + 1)) M (n + 1)) (σ : FaceFormData M n n) : ℝ :=
  if h : ∃ β : ManifoldForm (𝓠 (n + 1)) M n, ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β ∧
      IsCompact (ManifoldForm.tsupport β) ∧ IsExtendedBy σ β then
    ManifoldForm.boundaryIntegral o h.choose
  else 0

/-- **The integral `∫_{∂M} τ` of a top-degree form on the faces.** -/
def ChartFaceForm.integral (o : TangentOrientation (𝓠 (n + 1)) M (n + 1))
    (τ : ChartFaceForm M n n) : ℝ :=
  faceIntegral o τ

variable [T2Space M] [SigmaCompactSpace M] {o : TangentOrientation (𝓠 (n + 1)) M (n + 1)}

/-- `∫_{∂M} σ = ∫_{∂M} β` for every `C¹` compactly supported extension `β` of `σ`. -/
theorem faceIntegral_eq (ho : o.IsContinuous (𝓠 (n + 1)) ∞) {σ : FaceFormData M n n}
    {β : ManifoldForm (𝓠 (n + 1)) M n} (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β)
    (hc : IsCompact (ManifoldForm.tsupport β)) (h : IsExtendedBy σ β) :
    faceIntegral o σ = ManifoldForm.boundaryIntegral o β := by
  have hex : ∃ β : ManifoldForm (𝓠 (n + 1)) M n, ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β ∧
      IsCompact (ManifoldForm.tsupport β) ∧ IsExtendedBy σ β := ⟨β, hβ, hc, h⟩
  rw [faceIntegral, dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact boundaryIntegral_congr_face ho h1 hβ h2 hc fun x i u hu =>
    (h3 x i (openFaceDomain_subset _ _ hu)).trans (h x i (openFaceDomain_subset _ _ hu)).symm

/-- **The boundary integral of `j^*β` is `∫_{∂M} β`.** -/
theorem faceIntegral_faceRestriction (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {β : ManifoldForm (𝓠 (n + 1)) M n} (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β)
    (hc : IsCompact (ManifoldForm.tsupport β)) :
    faceIntegral o (faceRestriction β) = ManifoldForm.boundaryIntegral o β :=
  faceIntegral_eq ho hβ hc (isExtendedBy_faceRestriction β)

/-- **Stokes' theorem with the boundary term as a face integral** (Theorem 4.4.7, 2021 p. 199,
for classical forms): `∫_M dβ = ∫_{∂M} j^*β`. -/
theorem integral_extDeriv_eq_faceIntegral (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {β : ManifoldForm (𝓠 (n + 1)) M n} (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β)
    (hc : IsCompact (ManifoldForm.tsupport β)) :
    ManifoldForm.integral o (ManifoldForm.extDeriv β) = faceIntegral o (faceRestriction β) := by
  rw [faceIntegral_faceRestriction ho hβ hc]
  exact ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho hβ hc

theorem ChartFaceForm.integral_ofForm (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {β : ManifoldForm (𝓠 (n + 1)) M n} (hβ : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) ∞ β)
    (hc : IsCompact (ManifoldForm.tsupport β)) :
    (ChartFaceForm.ofForm hβ).integral o = ManifoldForm.boundaryIntegral o β :=
  faceIntegral_faceRestriction ho (hβ.of_le (by norm_num)) hc

theorem IsExtendedBy.congr {M : Type*} {n k : ℕ} [TopologicalSpace M]
    [ChartedSpace (EuclideanQuadrant (n + 1)) M] {σ σ' : FaceFormData M n k}
    {β : ManifoldForm (𝓠 (n + 1)) M k} (h : IsExtendedBy σ β)
    (hσ : ∀ x i, EqOn (σ x i) (σ' x i) (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)) :
    IsExtendedBy σ' β := fun x i _ hu => (h x i hu).trans (hσ x i hu)

/-- The integral depends only on the values on the faces. -/
theorem faceIntegral_congr (ho : o.IsContinuous (𝓠 (n + 1)) ∞) {σ σ' : FaceFormData M n n}
    (hσ : ∀ x i, EqOn (σ x i) (σ' x i) (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)) :
    faceIntegral o σ = faceIntegral o σ' := by
  by_cases h1 : ∃ β : ManifoldForm (𝓠 (n + 1)) M n, ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β ∧
      IsCompact (ManifoldForm.tsupport β) ∧ IsExtendedBy σ β
  · obtain ⟨β, hβ, hc, he⟩ := h1
    rw [faceIntegral_eq ho hβ hc he, faceIntegral_eq ho hβ hc (he.congr hσ)]
  · have h2 : ¬ ∃ β : ManifoldForm (𝓠 (n + 1)) M n, ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 β ∧
        IsCompact (ManifoldForm.tsupport β) ∧ IsExtendedBy σ' β := fun ⟨β, hβ, hc, he⟩ =>
      h1 ⟨β, hβ, hc, he.congr fun x i _ hu => (hσ x i hu).symm⟩
    rw [faceIntegral, dif_neg h1, faceIntegral, dif_neg h2]

theorem faceIntegral_add (ho : o.IsContinuous (𝓠 (n + 1)) ∞) {σ σ' : FaceFormData M n n}
    (hσ : IsChartFaceForm σ) (hσ' : IsChartFaceForm σ') (hc : HasCompactFaceSupport σ)
    (hc' : HasCompactFaceSupport σ') :
    faceIntegral o (σ + σ') = faceIntegral o σ + faceIntegral o σ' := by
  obtain ⟨β, hβ, hβc, hβe⟩ := exists_extension hσ hc
  obtain ⟨β', hβ', hβc', hβe'⟩ := exists_extension hσ' hc'
  have h1 := hβ.of_le (r' := 1) (by norm_num)
  have h1' := hβ'.of_le (r' := 1) (by norm_num)
  rw [faceIntegral_eq ho (h1.add h1') ((hβc.union hβc').of_isClosed_subset isClosed_closure
      (tsupport_add_subset β β')) (hβe.add hβe'), faceIntegral_eq ho h1 hβc hβe,
    faceIntegral_eq ho h1' hβc' hβe', boundaryIntegral_add ho h1 h1' hβc hβc']

theorem faceIntegral_smul (ho : o.IsContinuous (𝓠 (n + 1)) ∞) {σ : FaceFormData M n n}
    (hσ : IsChartFaceForm σ) (hc : HasCompactFaceSupport σ) (a : ℝ) :
    faceIntegral o (a • σ) = a * faceIntegral o σ := by
  obtain ⟨β, hβ, hβc, hβe⟩ := exists_extension hσ hc
  have h1 := hβ.of_le (r' := 1) (by norm_num)
  rw [faceIntegral_eq ho (contMDiffForm_const_smul a h1)
      (hβc.of_isClosed_subset isClosed_closure (tsupport_const_smul_subset a β)) (hβe.smul a),
    faceIntegral_eq ho h1 hβc hβe, boundaryIntegral_const_smul ho h1 hβc]

theorem ChartFaceForm.integral_add (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {τ τ' : ChartFaceForm M n n} (hc : HasCompactFaceSupport (τ : FaceFormData M n n))
    (hc' : HasCompactFaceSupport (τ' : FaceFormData M n n)) :
    (τ + τ').integral o = τ.integral o + τ'.integral o :=
  faceIntegral_add ho τ.2 τ'.2 hc hc'

theorem ChartFaceForm.integral_smul (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {τ : ChartFaceForm M n n} (hc : HasCompactFaceSupport (τ : FaceFormData M n n)) (a : ℝ) :
    (a • τ).integral o = a * τ.integral o :=
  faceIntegral_smul ho τ.2 hc a

theorem ChartFaceForm.integral_congr (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
    {τ τ' : ChartFaceForm M n n}
    (h : ∀ x i, EqOn ((τ : FaceFormData M n n) x i) ((τ' : FaceFormData M n n) x i)
      (faceDomain (chartAt (EuclideanQuadrant (n + 1)) x) i)) :
    τ.integral o = τ'.integral o :=
  faceIntegral_congr ho h

/-- **For compact `M`, `∫_{∂M}` is a linear map `Ω^n(∂M) → ℝ`.** -/
def ChartFaceForm.integralₗ [CompactSpace M] (ho : o.IsContinuous (𝓠 (n + 1)) ∞) :
    ChartFaceForm M n n →ₗ[ℝ] ℝ where
  toFun τ := τ.integral o
  map_add' _ _ := ChartFaceForm.integral_add ho (hasCompactFaceSupport_of_compactSpace _)
    (hasCompactFaceSupport_of_compactSpace _)
  map_smul' a _ := ChartFaceForm.integral_smul ho (hasCompactFaceSupport_of_compactSpace _) a

end FaceIntegral

/-! ### `∫_{∂M} dτ = 0` -/

section Stokes

variable {M : Type*} {k : ℕ} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (k + 1 + 1)) M]
  [IsManifold (𝓠 (k + 1 + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {o : TangentOrientation (𝓠 (k + 1 + 1)) M (k + 1 + 1)}

omit [T2Space M] [SigmaCompactSpace M] in
theorem integral_zero_form' [T2Space M] [SigmaCompactSpace M]
    (ho : o.IsContinuous (𝓠 (k + 1 + 1)) ∞) :
    ManifoldForm.integral o (0 : ManifoldForm (𝓠 (k + 1 + 1)) M (k + 1 + 1)) = 0 := by
  have h0 : IsCompact (ManifoldForm.tsupport (0 : ManifoldForm (𝓠 (k + 1 + 1)) M (k + 1 + 1))) := by
    have : ManifoldForm.tsupport (0 : ManifoldForm (𝓠 (k + 1 + 1)) M (k + 1 + 1)) = ∅ := by
      simp [ManifoldForm.tsupport, ManifoldForm.support]
    rw [this]; exact isCompact_empty
  have h := ManifoldForm.integral_add ho (ManifoldForm.contMDiffForm_zero_form 0)
    (ManifoldForm.contMDiffForm_zero_form 0) h0 h0 (o := o)
  rw [add_zero] at h
  linarith

/-- **`∫_{∂M} dτ = 0`** (used in the proof of Theorem 6.7.1, 2021 pp. 277–278, for
`∫_{∂S} (j^*α − dβ)`) for a compactly supported form `τ` on the faces of a Hausdorff σ-compact
manifold with corners `M` with a continuous orientation (the face-wise Stokes theorem with the
corner terms cancelling, here by `∫_{∂M} dβ = ∫_M ddβ = 0` for an extension `β` of `τ`). -/
theorem faceIntegral_d_eq_zero (ho : o.IsContinuous (𝓠 (k + 1 + 1)) ∞)
    {σ : FaceFormData M (k + 1) k} (hσ : IsChartFaceForm σ) (hc : HasCompactFaceSupport σ) :
    faceIntegral o (FaceFormData.d σ) = 0 := by
  obtain ⟨β, hβ, hβc, hβe⟩ := exists_extension hσ hc
  have hdβ : ManifoldForm.ContMDiffForm (𝓠 (k + 1 + 1)) ∞ (ManifoldForm.extDeriv β) :=
    (hβ.of_le (add_one_le_infty le_rfl)).extDeriv
  have hdβc : IsCompact (ManifoldForm.tsupport (ManifoldForm.extDeriv β)) :=
    hβc.of_isClosed_subset isClosed_closure (ManifoldForm.tsupport_extDeriv_subset β)
  rw [faceIntegral_eq ho (hdβ.of_le (by norm_num)) hdβc (hβe.extDeriv (hβ.of_le (by norm_num))),
    ← ManifoldForm.integral_extDeriv_eq_boundaryIntegral ho (hdβ.of_le (by norm_num)) hdβc,
    ManifoldForm.extDeriv_extDeriv (hβ.of_le (WithTop.coe_le_coe.2 le_top))]
  exact integral_zero_form' ho

/-- **`∫_{∂M} dτ = 0`** (`integral_d_eq_zero`) for a compactly supported `k`-form `τ` on the faces
of `M`, `dim M = k + 2`. -/
theorem ChartFaceForm.integral_d_eq_zero (ho : o.IsContinuous (𝓠 (k + 1 + 1)) ∞)
    (τ : ChartFaceForm M (k + 1) k) (hc : HasCompactFaceSupport (τ : FaceFormData M (k + 1) k)) :
    (ChartFaceForm.d τ).integral o = 0 :=
  faceIntegral_d_eq_zero ho τ.2 hc

/-- **`∫_{∂M} dτ = 0` on a compact manifold with corners.** -/
theorem ChartFaceForm.integral_d_eq_zero_of_compactSpace [CompactSpace M]
    (ho : o.IsContinuous (𝓠 (k + 1 + 1)) ∞) (τ : ChartFaceForm M (k + 1) k) :
    (ChartFaceForm.d τ).integral o = 0 :=
  τ.integral_d_eq_zero ho (hasCompactFaceSupport_of_compactSpace _)

end Stokes

/-! ### Dimension `1`: the faces are points -/

section DimOne

/-- The face parameter space `ℝ⁰` of a `1`-dimensional manifold with corners has volume `1`. -/
theorem volume_univ_fin_zero : (volume : Measure (EuclideanSpace ℝ (Fin 0))) univ = 1 := by
  have h := (EuclideanSpace.basisFun (Fin 0) ℝ).volume_parallelepiped
  convert h
  ext x
  simp only [mem_univ, true_iff, mem_parallelepiped_iff]
  exact ⟨0, by simp, Subsingleton.elim _ _⟩

/-- **In dimension `1` the faces are points**: the integral of a `0`-form over the face parameter
space `ℝ⁰` is its value at the point, so `∫_{∂M}` is a signed sum of point values. -/
theorem topFormIntegral_univ_fin_zero
    (ω : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0) [⋀^Fin 0]→L[ℝ] ℝ) :
    topFormIntegral univ ω = ω 0 (stdFrame 0) := by
  rw [topFormIntegral, Measure.restrict_univ]
  have : ∀ x : EuclideanSpace ℝ (Fin 0), ω x (stdFrame 0) = ω 0 (stdFrame 0) := fun x => by
    rw [Subsingleton.elim x 0]
  simp only [this, integral_const, smul_eq_mul]
  rw [measureReal_def, volume_univ_fin_zero]
  simp

end DimOne

end Polyfold
