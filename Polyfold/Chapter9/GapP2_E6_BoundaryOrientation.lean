import Polyfold.Chapter9.GapP2_E6_StratumTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, Definition 9.3.8, p. 427 (2017: Definition 9.9), Figure 9.1.

# The boundary orientation `o_{∂M}` on the stratum `{d_M = 1}`, and in corner coordinates

For an oriented `(m+1)`-dimensional submanifold `(M, o)` with tame induced structure:

* **`SubmanifoldOrientation.stratumOrientation`**: `o_{∂M}` of Definition 9.3.8 is an orientation,
  in the sense of Definition 9.3.3, of the `m`-dimensional submanifold `∂₁M = {d_M = 1}`
  (`isSubmanifoldOfDim_boundaryStratum`), with `T_y(∂M, o_{∂M}) = boundaryOp (T_y(M, o))`
  (`stratumOrientation_tangent`).
* In corner coordinates `κ` of `M` in which only the `i`-th coordinate of `y` vanishes:
  `Tι(v)` lies in `C_yM` iff `vᵢ ≥ 0` (`isInwardVec_incFrame_iff`), so `Tι(-eᵢ)` is outward, and
  a frame `Tι(v₁), …, Tι(v_m)` of the hyperplane `{vᵢ = 0}` is positive for `o_{∂M}` iff
  `(Tι(-eᵢ), Tι(v₁), …, Tι(v_m))` is positive for `o` (**`incFrame_mem_boundaryFramesAt_iff`**).
  This is the rule "outward normal first" by which Part I orients the faces of a manifold with
  corners (`IsInducedOrientation`, `faceOrientation`), read in the ambient M-polyfold.

Not formalized here: the statement with `faceOrientation` itself (Mathlib's
`TangentOrientation` of the face manifold of a face-structured sheet).  (2026-11-13) It is in
`GapP2_D3FaceOrientation.lean` (`faceOrientation_eq_iff_mem_stratumOrientation`,
`figure_9_1_existsUnique_faceOrientation`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module Manifold WithLp

noncomputable section

namespace Polyfold

universe u

section Param

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {F : E → G} {D : E →L[ℝ] G} {R S : Set E} {u₀ : E}

/-- If a ray `u₀ + t w`, `t ≥ 0` small, lies in `S ⊆ R` and the functional `ℓ ∘ F` has its
minimum on `S` at `u₀`, then `ℓ (D w) ≥ 0`. -/
theorem clm_deriv_nonneg_of_ray (hF : HasFDerivWithinAt F D R u₀) (hSR : S ⊆ R)
    {w : E} (hw : ∀ᶠ t : ℝ in 𝓝[≥] 0, u₀ + t • w ∈ S) (ℓ : G →L[ℝ] ℝ)
    (hℓ : ∀ u ∈ S, ℓ (F u₀) ≤ ℓ (F u)) : 0 ≤ ℓ (D w) := by
  set γ : ℝ → E := fun t => u₀ + t • w with hγ
  have hγ0 : γ 0 = u₀ := by simp [hγ]
  have hγd : HasDerivAt γ w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u₀
    rw [one_smul] at this
    exact this
  have hF' : HasFDerivWithinAt F D S (γ 0) := by rw [hγ0]; exact hF.mono hSR
  set s : Set ℝ := {t | γ t ∈ S} with hs
  have h1 : HasDerivWithinAt (F ∘ γ) (D w) s 0 :=
    hF'.comp_hasDerivWithinAt 0 hγd.hasDerivWithinAt fun t ht => ht
  have h3 : HasDerivWithinAt (ℓ ∘ F ∘ γ) (ℓ (D w)) s 0 :=
    ℓ.hasFDerivAt.comp_hasDerivWithinAt 0 h1
  have h4 := hasDerivWithinAt_iff_tendsto_slope.1 h3
  have hw' : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ s \ {0} := by
    filter_upwards [nhdsWithin_mono _ Ioi_subset_Ici_self hw, self_mem_nhdsWithin] with t ht ht0
    exact ⟨ht, (ne_of_gt ht0 : t ≠ 0)⟩
  have h5 : Tendsto (slope (ℓ ∘ F ∘ γ) 0) (𝓝[>] 0) (𝓝 (ℓ (D w))) :=
    h4.mono_left (nhdsWithin_le_iff.2 hw')
  refine ge_of_tendsto h5 ?_
  filter_upwards [hw', self_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, sub_zero]
  refine div_nonneg (sub_nonneg.2 ?_) (le_of_lt ht0)
  simp only [Function.comp_apply, hγ0]
  exact hℓ _ ht.1

end Param

namespace MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} [ParacompactSpace M] {n : ℕ} {hY : P.IsSubMPolyfold M}

/-- The part of the target of the quadrant chart lying over the domain of `φ`. -/
def quadDom (κ : CornerCoords (subPolyfold hY) n) (φ : MChart X) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {u | u ∈ (κ.toQuadrantChart.extend (𝓠 n)).target ∧
    ((κ.toQuadrantChart.extend (𝓠 n)).symm u).1 ∈ φ.source}

theorem quadDom_subset_range (κ : CornerCoords (subPolyfold hY) n) (φ : MChart X) :
    quadDom κ φ ⊆ range (𝓠 n) := fun _ hu =>
  κ.toQuadrantChart.extend_target_subset_range hu.1

/-- Rays from `κ(y)` pointing into the quadrant stay in the coordinate domain. -/
theorem eventually_ray_mem_quadDom (κ : CornerCoords (subPolyfold hY) n) {i : Fin n}
    {φ : MChart X} {y : M} (hy : y ∈ κ.facePiece i) (hyφ : y.1 ∈ φ.source)
    {w : EuclideanSpace ℝ (Fin n)} (hw : 0 ≤ w i) :
    ∀ᶠ t : ℝ in 𝓝[≥] 0, κ.toQuadrantChart.extend (𝓠 n) y + t • w ∈ quadDom κ φ := by
  set e := κ.toQuadrantChart with he
  set u₀ := e.extend (𝓠 n) y with hu₀
  have hys : y ∈ e.source := hy.1
  have hG : IsOpen {b : M | b.1 ∈ φ.source} := φ.isOpen_source.preimage continuous_subtype_val
  have hleft : (e.extend (𝓠 n)).symm u₀ = y := e.extend_left_inv hys
  have A1 : {u | u ∈ (e.extend (𝓠 n)).target ∧
      (e.extend (𝓠 n)).symm u ∈ {b : M | b.1 ∈ φ.source}} ∈ 𝓝[range (𝓠 n)] u₀ :=
    inter_mem (e.extend_target_mem_nhdsWithin hys)
      (nhdsWithin_le_nhds ((e.continuousAt_extend_symm hys).preimage_mem_nhds
        (hG.mem_nhds (by rw [hleft]; exact hyφ))))
  obtain ⟨O, hO, hOsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 A1
  have hO' : IsOpen {u : EuclideanSpace ℝ (Fin n) | ∀ l, l ≠ i → 0 < u l} :=
    (isOpen_setOf_forall_ne_pos i).preimage (PiLp.continuous_ofLp 2 _)
  have hu₀O' : u₀ ∈ {u : EuclideanSpace ℝ (Fin n) | ∀ l, l ≠ i → 0 < u l} := fun l hl => by
    rw [hu₀, κ.extend_apply hy.1]; exact hy.2.1 l hl
  have hcont : Tendsto (fun t : ℝ => u₀ + t • w) (𝓝 0) (𝓝 u₀) := by
    have : Continuous fun t : ℝ => u₀ + t • w := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [nhdsWithin_le_nhds (hcont (inter_mem hO (hO'.mem_nhds hu₀O'))),
    self_mem_nhdsWithin] with t ht ht0
  have hu₀i : 0 ≤ u₀ i := by rw [hu₀, κ.extend_apply hy.1]; exact κ.coord_nonneg hy.1 i
  have hrange : u₀ + t • w ∈ range (𝓠 n) := by
    refine ⟨⟨u₀ + t • w, fun l => ?_⟩, rfl⟩
    by_cases hl : l = i
    · rw [hl, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact add_nonneg hu₀i (mul_nonneg ht0 hw)
    · exact (ht.2 l hl).le
  exact hOsub ⟨ht.1, hrange⟩

variable (hcs : (subPolyfold hY).HasCornerStructureOfDim n)

include hcs in
/-- **`Dι(κ(y)) w ∈ C_{φ(y)}` for `wᵢ ≥ 0`**: the derivative of the inclusion maps the half-space
`{vᵢ ≥ 0}` into the chart form of the partial cone `C_yX`. -/
theorem modelDeriv_mem_cone (hM : P.IsSubmanifoldOfDim M n)
    (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (c : P.PresentedChart y.1)
    {w : EuclideanSpace ℝ (Fin n)} (hw : 0 ≤ w i) :
    modelDeriv κ c.isChart (hM.1.data y.2).toSubData y (levelLift κ.χ 1 y) w ∈ c.cone := by
  set d := (hM.1.data y.2).toSubData with hd
  set e := κ.toQuadrantChart with he
  have hys : y ∈ κ.s := hy.1
  have hyσ : y ∈ (subChart d c.isChart y).source :=
    d.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2) c.mem_source
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hys) (levelVal_mem (hcs.levelOne y))
  have hF := hasFDerivWithinAt_incl κ c.isChart d y hys hyσ hz
  have hleft : (e.extend (𝓠 n)).symm (e.extend (𝓠 n) y) = y := e.extend_left_inv hys
  intro j hj
  let T₀ : c.φ.model.E 0 ≃L[ℝ] (Fin c.n → ℝ) × c.W 0 := c.T 0
  let ℓ : c.φ.model.E 0 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin c.n => ℝ) j).comp
      ((ContinuousLinearMap.fst ℝ (Fin c.n → ℝ) (c.W 0)).comp (T₀ : c.φ.model.E 0 →L[ℝ] _))
  have key := clm_deriv_nonneg_of_ray hF (quadDom_subset_range κ c.φ)
    (eventually_ray_mem_quadDom κ hy c.mem_source hw) ℓ ?_
  · exact key
  · intro u hu
    have h0 : ℓ (((fun b : M => c.φ b.1) ∘ (e.extend (𝓠 n)).symm) (e.extend (𝓠 n) y)) = 0 := by
      simp only [Function.comp_apply, hleft]
      exact hj
    rw [h0]
    have hC : c.φ ((e.extend (𝓠 n)).symm u).1 ∈ c.φ.model.C := c.φ.apply_mem_C hu.2
    rw [c.hT] at hC
    exact hC j

/-- `v - vᵢ eᵢ` lies in the hyperplane `{vᵢ = 0}`. -/
theorem sub_single_mem_coordHyperplane {i : Fin n} (v : EuclideanSpace ℝ (Fin n)) :
    v - v i • EuclideanSpace.single i (1 : ℝ) ∈ coordHyperplane i := by
  rw [mem_coordHyperplane]
  simp

include hcs in
/-- The derivative of the inclusion in the normal direction `eᵢ` is not in `E_{φ(y)}`
(`d_M(y) = 1`). -/
theorem modelDeriv_single_not_mem_red (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) (c : P.PresentedChart y.1) :
    modelDeriv κ c.isChart (hM.1.data y.2).toSubData y (levelLift κ.χ 1 y)
      (EuclideanSpace.single i (1 : ℝ)) ∉ c.red := by
  intro hred
  set d := (hM.1.data y.2).toSubData with hd
  have hys : y ∈ κ.s := hy.1
  have hyσ : y ∈ (subChart d c.isChart y).source :=
    d.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2) c.mem_source
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hys) (levelVal_mem (hcs.levelOne y))
  set D := modelDeriv κ c.isChart d y (levelLift κ.χ 1 y) with hD
  have hinj : Function.Injective D := modelDeriv_injective κ c.isChart d y hys hyσ hz
  obtain ⟨NM, hNM, hfin⟩ := exists_submodule_chartTangent c.isChart hM.1 y.2 c.mem_source
  have := hfin
  have hrange : LinearMap.range (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0) ≤ NM := by
    rintro _ ⟨v, rfl⟩
    rw [← SetLike.mem_coe, hNM]
    exact modelDeriv_mem_chartTangent (hcs := hcs) hM.1 κ hys v c.isChart c.mem_source
  have hNMn : finrank ℝ NM = n :=
    finrank_chartTangent c.isChart (hM.2 y.1 y.2) hM.1 c.mem_source hNM
  have hrn : finrank ℝ (LinearMap.range (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0)) =
      n := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  have hreq : LinearMap.range (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0) = NM :=
    Submodule.eq_of_le_of_finrank_eq hrange (by rw [hrn, hNMn])
  have hle : NM ≤ c.red := by
    rw [← hreq]
    rintro _ ⟨v, rfl⟩
    have hv : v = (v - v i • EuclideanSpace.single i (1 : ℝ)) +
        v i • EuclideanSpace.single i (1 : ℝ) := by abel
    change D v ∈ c.red
    rw [hv, map_add, map_smul]
    exact c.red.add_mem (modelDeriv_mem_red hcs hM κ hy hyi c (sub_single_mem_coordHyperplane v))
      (c.red.smul_mem _ hred)
  have h := subDegIndex_eq_quotDim_span hM.1 ht y.2 c
  have h1 : P.subDegIndex hM.1.isSubMPolyfold ⟨y.1, y.2⟩ = 1 :=
    (CornerCoords.degIndex_eq_one_iff hy).2 hyi
  have hv : c.vec '' P.submanifoldTangent M y.1 = (NM : Set (c.φ.model.E 0)) := hNM.symm
  rw [h1, hv, Submodule.span_eq, quotDim_eq_zero_of_le hle] at h
  exact one_ne_zero h

include hcs in
/-- **`Tι(v) ∈ C_yM` iff `vᵢ ≥ 0`** (Definition 9.3.8: the outward vectors of `T_yM` at a point
with `d_M(y) = 1`, in corner coordinates whose `i`-th coordinate vanishes at `y`). -/
theorem isInwardVec_incFrame_iff (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) (v : EuclideanSpace ℝ (Fin n)) :
    P.IsInwardVec y.1 (incFrame hcs κ hy.1 v) ↔ 0 ≤ v i := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y.1
  set d := (hM.1.data y.2).toSubData with hd
  have hyσ : y ∈ (subChart d c.isChart y).source :=
    d.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2) c.mem_source
  set D := modelDeriv κ c.isChart d y (levelLift κ.χ 1 y) with hD
  have hvec : c.vec (incFrame hcs κ hy.1 v) = D v :=
    chartVec_incFrame (hcs := hcs) κ hy.1 v c.isChart d y hyσ
  rw [isInwardVec_iff c (levelVal_tangentProj_incFrame κ hy.1 v), hvec]
  refine ⟨fun hcone => ?_, fun h => modelDeriv_mem_cone hcs hM κ hy c h⟩
  by_contra hneg
  have hvi : v i < 0 := lt_of_not_ge hneg
  have hv' := modelDeriv_mem_red hcs hM κ hy hyi c (sub_single_mem_coordHyperplane (i := i) v)
  have hdec : D (v - v i • EuclideanSpace.single i (1 : ℝ)) =
      D v - v i • D (EuclideanSpace.single i (1 : ℝ)) := by
    rw [map_sub, map_smul]
  rw [← hD, hdec] at hv'
  have hneg' : -(D v - v i • D (EuclideanSpace.single i (1 : ℝ))) ∈ c.cone :=
    c.red_subset_cone (c.red.neg_mem hv')
  have hsum := c.add_mem_cone hcone hneg'
  have h2 := c.smul_mem_cone (t := 1 / (-v i)) (one_div_nonneg.2 (by linarith)) hsum
  have h3 : (1 / (-v i)) • (D v + -(D v - v i • D (EuclideanSpace.single i (1 : ℝ)))) =
      -D (EuclideanSpace.single i (1 : ℝ)) := by
    have hne : v i ≠ 0 := ne_of_lt hvi
    have e1 : D v + -(D v - v i • D (EuclideanSpace.single i (1 : ℝ))) =
        v i • D (EuclideanSpace.single i (1 : ℝ)) := by abel
    have e2 : 1 / (-v i) * v i = -1 := by field_simp
    rw [e1, smul_smul, e2, neg_one_smul]
  rw [h3] at h2
  have h4 : D (EuclideanSpace.single i (1 : ℝ)) ∈ c.cone :=
    modelDeriv_mem_cone hcs hM κ hy c (by simp)
  exact modelDeriv_single_not_mem_red hcs hM ht κ hy hyi c (c.mem_red_of_mem_cone h4 h2)

include hcs in
/-- `Tι(-eᵢ)` points outward. -/
theorem isOutwardTangent_incFrame_neg_single (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) :
    ¬ P.IsInwardVec y.1 (incFrame hcs κ hy.1 (-EuclideanSpace.single i (1 : ℝ))) := by
  rw [isInwardVec_incFrame_iff hcs hM ht κ hy hyi]
  simp

end MPolyfold

/-! ### The boundary orientation in corner coordinates, and on the stratum -/

namespace MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X}

section Coord

variable [ParacompactSpace M] {m : ℕ} {hY : P.IsSubMPolyfold M}
  (hcs : (subPolyfold hY).HasCornerStructureOfDim (m + 1))

include hcs in
/-- **Definition 9.3.8 in corner coordinates: outward normal first** (2021 p. 427; Figure 9.1):
for an oriented `(m+1)`-dimensional submanifold `(M, o)` with tame induced structure, corner
coordinates `κ` of `M` in which only the `i`-th coordinate of `y` vanishes, and vectors
`v₁, …, v_m` of the hyperplane `{vᵢ = 0}`, the frame `Tι(v₁), …, Tι(v_m)` is positive for the
boundary orientation `o_{∂M}` at `y` iff `(Tι(-eᵢ), Tι(v₁), …, Tι(v_m))` is positive for `o`. -/
theorem incFrame_mem_boundaryFramesAt_iff (hM : P.IsSubmanifoldOfDim M (m + 1))
    (ht : P.HasTameInducedStructure M) (o : P.SubmanifoldOrientation M (m + 1))
    (κ : CornerCoords (subPolyfold hY) (m + 1)) {i : Fin (m + 1)} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0)
    (v : Fin m → EuclideanSpace ℝ (Fin (m + 1))) (hv : ∀ j, v j ∈ coordHyperplane i) :
    (fun j => incFrame hcs κ hy.1 (v j)) ∈ o.boundaryFramesAt y.1 ↔
      (Fin.cons (incFrame hcs κ hy.1 (-EuclideanSpace.single i (1 : ℝ)))
        (fun j => incFrame hcs κ hy.1 (v j)) : Fin (m + 1) → P.TangentSpace) ∈ o.frames y.1 := by
  have hyS : y.1 ∈ P.stratumOne M := (val_mem_stratumOne_iff hM.1 y).2
    ((CornerCoords.degIndex_eq_one_iff hy).2 hyi)
  have hyB : y.1 ∈ P.boundaryStratum M := stratumOne_eq_boundaryStratum hM.1 ht ▸ hyS
  have hO : P.IsOrientedAt y.1 ⟨m + 1, P.submanifoldTangent M y.1, o.frames y.1⟩ :=
    o.isOrientedAt y.1 y.2
  have hadm : P.IsBoundaryAdmissible y.1 ⟨m + 1, P.submanifoldTangent M y.1, o.frames y.1⟩ :=
    isBoundaryAdmissible_of_submanifold hM.1 y.2 hO rfl
      ((o.hasReducedCodim_iff_mem_boundaryStratum y.2).2 hyB)
  have he : incFrame hcs κ hy.1 (-EuclideanSpace.single i (1 : ℝ)) ∈
      P.submanifoldTangent M y.1 := incFrame_mem hM.1 κ hy.1 _
  have hop := boundaryOp_eq hO hadm he
    (isOutwardTangent_incFrame_neg_single hcs hM ht κ hy hyi)
  have hfr : o.boundaryFramesAt y.1 = boundaryFrames (o.frames y.1)
      (P.boundaryCarrier (P.submanifoldTangent M y.1))
      (incFrame hcs κ hy.1 (-EuclideanSpace.single i (1 : ℝ))) := by
    have h : (⟨m, P.boundaryCarrier (P.submanifoldTangent M y.1), o.boundaryFramesAt y.1⟩ :
        OrTangent P) = _ := hop
    simpa using h
  rw [hfr]
  refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
  rw [← submanifoldTangent_stratumOne hM ht hyS]
  exact incFrame_mem_submanifoldTangent_stratumOne hcs hM ht κ hy hyi (hv j)

end Coord

/-- **Definition 9.3.8, 2021 p. 427 (2017: Definition 9.9): `(∂M, o_{∂M})` as an oriented
submanifold.**  For an oriented `(m+1)`-dimensional submanifold `(M, o)` of an M-polyfold with
tame induced structure, the boundary orientation `o_{∂M}` is an orientation, in the sense of
Definition 9.3.3 (`SubmanifoldOrientation`: orientations of the tangent spaces with continuous
positive frame fields), of the `m`-dimensional submanifold `{d_M = 1}`
(`isSubmanifoldOfDim_boundaryStratum`). -/
def SubmanifoldOrientation.stratumOrientation {m : ℕ}
    (o : P.SubmanifoldOrientation M (m + 1)) (hM : P.IsSubmanifoldOfDim M (m + 1))
    (ht : P.HasTameInducedStructure M) : P.SubmanifoldOrientation (P.boundaryStratum M) m :=
  (o.boundaryOrientation hM.1).toSubmanifoldOrientation subset_rfl fun _ hy =>
    submanifoldTangent_boundaryStratum hM ht hy

theorem SubmanifoldOrientation.stratumOrientation_frames {m : ℕ}
    (o : P.SubmanifoldOrientation M (m + 1)) (hM : P.IsSubmanifoldOfDim M (m + 1))
    (ht : P.HasTameInducedStructure M) (y : X) :
    (o.stratumOrientation hM ht).frames y = o.boundaryFramesAt y := rfl

/-- **`T_y(∂M, o_{∂M}) = boundaryOp (T_y(M, o))`** at the points with `d_M(y) = 1`: the oriented
tangent space of the stratum is the boundary operation of Definition 9.3.8 applied to the
oriented tangent space of `M`. -/
theorem SubmanifoldOrientation.stratumOrientation_tangent {m : ℕ}
    (o : P.SubmanifoldOrientation M (m + 1)) (hM : P.IsSubmanifoldOfDim M (m + 1))
    (ht : P.HasTameInducedStructure M) {y : X} (hy : y ∈ P.boundaryStratum M) :
    (o.stratumOrientation hM ht).tangent y = P.boundaryOp (o.tangent y) := by
  rw [o.boundaryOp_tangent_eq y]
  unfold SubmanifoldOrientation.tangent
  rw [submanifoldTangent_boundaryStratum hM ht hy]
  rfl

end MPolyfold

end Polyfold
