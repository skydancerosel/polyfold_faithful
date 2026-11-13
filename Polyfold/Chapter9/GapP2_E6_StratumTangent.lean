import Polyfold.Chapter9.GapP2_E6_StratumRetraction
import Polyfold.Chapter9.GapP2_E3_ManifoldBridge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, Definition 9.3.8, p. 427 (2017: Definition 9.9), and §9.5, Theorem 9.5.15, p. 448.

# The stratum `{d_M = 1}` of a tame sheet: dimension and tangent spaces

For an `n`-dimensional submanifold `M` of an M-polyfold with tame induced structure, the stratum
`∂₁M = {d_M = 1}` (a smooth submanifold, `isSmoothSubmanifold_stratumOne`) has dimension `n - 1`,
and its tangent space at `y` is `T_y∂M = T^R_yM` of Definition 9.3.8 (`boundaryCarrier (T_yM)`).

## What is formalized

* `tangentConeAt_subset_map_of_param`, `deriv_mem_span_tangentConeAt_of_line`,
  `clm_deriv_eq_zero_of_line`: three facts on a map `F` differentiable within a set with an
  injective derivative `D` (the tangent cone of the image of a piece of an affine subspace
  `u₀ + H₀` is `D(H₀)`; a functional with a minimum along the image has `ℓ ∘ D = 0` on `H₀`).
* `MPolyfold.chartTangent_stratumOne_eq`: in a chart `φ` of `X` and corner coordinates `κ` of `M`
  in which only the `i`-th coordinate of `y` vanishes, the chart image of `T_y∂₁M` is
  `Dι(κ(y)) {v | vᵢ = 0}`.
* **`MPolyfold.isSubmanifoldOfDim_stratumOne`**: `∂₁M` is an `(n-1)`-dimensional submanifold.
* **`MPolyfold.submanifoldTangent_stratumOne`**: `T_y∂₁M = boundaryCarrier (T_yM)`.
* `MPolyfold.incFrame_mem_submanifoldTangent_stratumOne`: the frames `Tι(v)`, `vᵢ = 0`, are
  tangent to the stratum.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module Manifold WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

/-! ### Three facts on differentiable parametrizations -/

section Param

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {F : E → G} {D : E →L[ℝ] G} {R S : Set E} {u₀ : E}

/-- **The tangent cone of a parametrized piece of an affine subspace**: `F` differentiable within
`R` at `u₀` with injective derivative `D` (`E` finite-dimensional), `S ⊆ R ∩ (u₀ + H₀)`, and a set
`K` whose points `k` are `F(g k)` with `g k ∈ S`, `g k → u₀` as `k → F(u₀)`.  Then the tangent
cone of `K` at `F(u₀)` lies in `D(H₀)`. -/
theorem tangentConeAt_subset_map_of_param [FiniteDimensional ℝ E] (hD : Function.Injective D)
    (hF : HasFDerivWithinAt F D R u₀) (H₀ : Submodule ℝ E) (hSR : S ⊆ R)
    (hSH : ∀ u ∈ S, u - u₀ ∈ H₀) {K : Set G} {g : G → E}
    (hg : Tendsto g (𝓝[K] (F u₀)) (𝓝 u₀)) (hgS : ∀ k ∈ K, g k ∈ S ∧ F (g k) = k) :
    tangentConeAt ℝ K (F u₀) ⊆ (H₀.map (D : E →ₗ[ℝ] G) : Set G) := by
  intro v hv
  obtain ⟨c, d, hd0, hds, hcd⟩ := mem_tangentConeAt_iff_exists_seq.1 hv
  have hclosed : IsClosed (H₀.map (D : E →ₗ[ℝ] G) : Set G) :=
    Submodule.closed_of_finiteDimensional _
  obtain ⟨Kc, hKc, hanti⟩ := (D : E →ₗ[ℝ] G).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hD)
  have hK0 : (0 : ℝ) < Kc := hKc
  have hbd : ∀ e : E, ‖e‖ ≤ Kc * ‖D e‖ := fun e => by
    have := hanti.le_mul_dist e 0
    simpa [dist_eq_norm] using this
  set u : ℕ → E := fun k => g (F u₀ + d k) with hu_def
  have hlim : Tendsto (fun k => F u₀ + d k) atTop (𝓝[K] (F u₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd0, hds⟩
  have hu : Tendsto u atTop (𝓝 u₀) := hg.comp hlim
  have hev : ∀ᶠ k in atTop, u k ∈ S ∧ F (u k) = F u₀ + d k := hds.mono fun k hk => hgS _ hk
  have hu' : Tendsto u atTop (𝓝[R] u₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, hev.mono fun k h => hSR h.1⟩
  have ho := hF.isLittleO.comp_tendsto hu'
  have hzero : Tendsto (fun k => c k • d k - D (c k • (u k - u₀))) atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro δ hδ
    set B : ℝ := ‖v‖ + 1 with hB
    have hBpos : 0 < B := by positivity
    set ε : ℝ := min (1 / (2 * Kc)) (δ / (4 * Kc * B)) with hε
    have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
    have hnorm : ∀ᶠ k in atTop, ‖c k • d k‖ < B :=
      (hcd.norm).eventually (gt_mem_nhds (by rw [hB]; linarith))
    filter_upwards [ho.def hεpos, hev, hnorm] with k h1 h2 h3
    simp only [Function.comp_apply] at h1
    rw [h2.2, add_sub_cancel_left] at h1
    -- `h1 : ‖d k - D (u k - u₀)‖ ≤ ε * ‖u k - u₀‖`
    set e := u k - u₀ with he
    have hε1 : ε ≤ 1 / (2 * Kc) := min_le_left _ _
    have hε2 : ε ≤ δ / (4 * Kc * B) := min_le_right _ _
    have hDe : ‖D e‖ ≤ ‖d k‖ + ε * ‖e‖ := by
      have : D e = d k - (d k - D e) := by abel
      calc ‖D e‖ = ‖d k - (d k - D e)‖ := by rw [← this]
        _ ≤ ‖d k‖ + ‖d k - D e‖ := norm_sub_le _ _
        _ ≤ ‖d k‖ + ε * ‖e‖ := by linarith
    have hKε : Kc * ε ≤ 1 / 2 := by
      calc (Kc : ℝ) * ε ≤ Kc * (1 / (2 * Kc)) := mul_le_mul_of_nonneg_left hε1 hK0.le
        _ = 1 / 2 := by field_simp
    have he2 : ‖e‖ ≤ 2 * Kc * ‖d k‖ := by
      have h4 := hbd e
      have h5 : (Kc : ℝ) * ‖D e‖ ≤ Kc * ‖d k‖ + Kc * ε * ‖e‖ := by
        calc (Kc : ℝ) * ‖D e‖ ≤ Kc * (‖d k‖ + ε * ‖e‖) := mul_le_mul_of_nonneg_left hDe hK0.le
          _ = Kc * ‖d k‖ + Kc * ε * ‖e‖ := by ring
      have h6 : (Kc : ℝ) * ε * ‖e‖ ≤ 1 / 2 * ‖e‖ :=
        mul_le_mul_of_nonneg_right hKε (norm_nonneg _)
      linarith
    have hcalc : ‖c k • d k - D (c k • e)‖ = ‖c k‖ * ‖d k - D e‖ := by
      rw [map_smul, ← smul_sub, norm_smul]
    rw [hcalc]
    have h7 : ‖c k‖ * ‖d k - D e‖ ≤ ‖c k‖ * (ε * (2 * Kc * ‖d k‖)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left he2 hεpos.le))
        (norm_nonneg _)
    have h8 : ‖c k‖ * (ε * (2 * Kc * ‖d k‖)) = 2 * Kc * ε * ‖c k • d k‖ := by
      rw [norm_smul]; ring
    have h9 : 2 * Kc * ε * ‖c k • d k‖ ≤ 2 * Kc * ε * B :=
      mul_le_mul_of_nonneg_left h3.le (by positivity)
    have h10 : 2 * Kc * ε * B ≤ δ / 2 := by
      calc 2 * Kc * ε * B ≤ 2 * Kc * (δ / (4 * Kc * B)) * B := by
            have : 2 * (Kc : ℝ) * ε ≤ 2 * Kc * (δ / (4 * Kc * B)) :=
              mul_le_mul_of_nonneg_left hε2 (by positivity)
            exact mul_le_mul_of_nonneg_right this hBpos.le
        _ = δ / 2 := by field_simp; ring
    linarith
  have hDlim : Tendsto (fun k => D (c k • (u k - u₀))) atTop (𝓝 v) := by
    have := hcd.sub hzero
    simpa using this
  refine hclosed.mem_of_tendsto hDlim (hev.mono fun k hk => ?_)
  exact ⟨c k • (u k - u₀), H₀.smul_mem _ (hSH _ hk.1), rfl⟩

/-- If a segment `u₀ + t w`, `|t|` small, lies in `S ⊆ R`, then `D w` is in the span of the
tangent cone of `F(S)` at `F(u₀)`. -/
theorem deriv_mem_span_tangentConeAt_of_line (hF : HasFDerivWithinAt F D R u₀) (hSR : S ⊆ R)
    {w : E} (hw : ∀ᶠ t : ℝ in 𝓝 0, u₀ + t • w ∈ S) :
    D w ∈ Submodule.span ℝ (tangentConeAt ℝ (F '' S) (F u₀)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hw
  have hseg : openSegment ℝ u₀ (u₀ + (ε / 2) • w) ⊆ S := by
    rw [openSegment_eq_image']
    rintro _ ⟨θ, hθ, rfl⟩
    have : u₀ + θ • (u₀ + (ε / 2) • w - u₀) = u₀ + (θ * (ε / 2)) • w := by
      rw [add_sub_cancel_left, smul_smul]
    change u₀ + θ • (u₀ + (ε / 2) • w - u₀) ∈ S
    rw [this]
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos hθ.1 (by positivity))]
    nlinarith [hθ.1, hθ.2]
  have h1 := mem_tangentConeAt_of_openSegment_subset hseg
  rw [add_sub_cancel_left] at h1
  have h2 := (hF.mono hSR).mapsTo_tangent_cone h1
  have h3 : D w = (2 / ε) • D ((ε / 2) • w) := by
    rw [map_smul, smul_smul]
    have : 2 / ε * (ε / 2) = 1 := by field_simp
    rw [this, one_smul]
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h2)

/-- If a segment `u₀ + t w`, `|t|` small, lies in `S ⊆ R` and the functional `ℓ ∘ F` has its
minimum on `S` at `u₀`, then `ℓ (D w) = 0`. -/
theorem clm_deriv_eq_zero_of_line (hF : HasFDerivWithinAt F D R u₀) (hSR : S ⊆ R)
    {w : E} (hw : ∀ᶠ t : ℝ in 𝓝 0, u₀ + t • w ∈ S) (ℓ : G →L[ℝ] ℝ)
    (hℓ : ∀ u ∈ S, ℓ (F u₀) ≤ ℓ (F u)) : ℓ (D w) = 0 := by
  set γ : ℝ → E := fun t => u₀ + t • w with hγ
  have hγ0 : γ 0 = u₀ := by simp [hγ]
  have hγd : HasDerivAt γ w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u₀
    rw [one_smul] at this
    exact this
  have hF' : HasFDerivWithinAt F D S (γ 0) := by rw [hγ0]; exact hF.mono hSR
  have h1 : HasDerivWithinAt (F ∘ γ) (D w) {t | γ t ∈ S} 0 :=
    hF'.comp_hasDerivWithinAt 0 hγd.hasDerivWithinAt fun t ht => ht
  have h2 : HasDerivAt (F ∘ γ) (D w) 0 := h1.hasDerivAt hw
  have h3 : HasDerivAt (ℓ ∘ F ∘ γ) (ℓ (D w)) 0 := ℓ.hasFDerivAt.comp_hasDerivAt 0 h2
  have hmin : IsLocalMin (ℓ ∘ F ∘ γ) 0 := by
    filter_upwards [hw] with t ht
    simp only [Function.comp_apply, hγ0]
    exact hℓ _ ht
  exact hmin.hasDerivAt_eq_zero h3

end Param

namespace MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

/-- The hyperplane `{v | vᵢ = 0}` of `ℝⁿ`. -/
def coordHyperplane {n : ℕ} (i : Fin n) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.ker ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)

theorem mem_coordHyperplane {n : ℕ} {i : Fin n} {v : EuclideanSpace ℝ (Fin n)} :
    v ∈ coordHyperplane i ↔ v i = 0 := Iff.rfl

theorem finrank_coordHyperplane {n : ℕ} (i : Fin n) :
    finrank ℝ (coordHyperplane i) + 1 = n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ)
  have hsurj : Function.Surjective ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) := fun t =>
    ⟨EuclideanSpace.single i t, by simp⟩
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
    finrank_euclideanSpace_fin] at h
  unfold coordHyperplane
  omega

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} [ParacompactSpace M] {n : ℕ} {hY : P.IsSubMPolyfold M}

theorem val_mem_stratumOne_iff (hM : P.IsSmoothSubmanifold M) (b : M) :
    b.1 ∈ P.stratumOne M ↔ (subPolyfold hY).degIndex b = 1 :=
  mem_stratumOne_iff hM b.2

/-- The coordinate domain of the stratum near a point: the points of `{uᵢ = 0}` in the target of
the quadrant chart whose preimage lies in the face piece and in the domain of `φ`. -/
def stratumDom (κ : CornerCoords (subPolyfold hY) n) (i : Fin n) (φ : MChart X) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {u | u ∈ (κ.toQuadrantChart.extend (𝓠 n)).target ∧
    (κ.toQuadrantChart.extend (𝓠 n)).symm u ∈ κ.facePiece i ∧
    ((κ.toQuadrantChart.extend (𝓠 n)).symm u).1 ∈ φ.source ∧ u i = 0}

section Dom

variable (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {φ : MChart X}

theorem stratumDom_subset_range : stratumDom κ i φ ⊆ range (𝓠 n) := fun _ hu =>
  κ.toQuadrantChart.extend_target_subset_range hu.1

theorem coord_symm_of_mem_stratumDom {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ stratumDom κ i φ) :
    κ.coord ((κ.toQuadrantChart.extend (𝓠 n)).symm u) i = 0 := by
  have h : toLp 2 (κ.coord ((κ.toQuadrantChart.extend (𝓠 n)).symm u)) = u :=
    (κ.extend_apply hu.2.1.1).symm.trans ((κ.toQuadrantChart.extend (𝓠 n)).right_inv hu.1)
  have h2 := hu.2.2.2
  rw [← h] at h2
  exact h2

theorem image_stratumDom_subset (hM : P.IsSmoothSubmanifold M) :
    ((fun b : M => φ b.1) ∘ (κ.toQuadrantChart.extend (𝓠 n)).symm) '' stratumDom κ i φ ⊆
      φ '' (P.stratumOne M ∩ φ.source) := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨_, ⟨(val_mem_stratumOne_iff hM _).2 ((CornerCoords.degIndex_eq_one_iff hu.2.1).2
    (coord_symm_of_mem_stratumDom κ hu)), hu.2.2.1⟩, rfl⟩

variable {y : M} (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) (hyφ : y.1 ∈ φ.source)
include hy hyi

theorem extend_apply_self_eq_zero : (κ.toQuadrantChart.extend (𝓠 n) y) i = 0 := by
  rw [κ.extend_apply hy.1]; exact hyi

theorem sub_mem_coordHyperplane {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ stratumDom κ i φ) :
    u - κ.toQuadrantChart.extend (𝓠 n) y ∈ coordHyperplane i := by
  rw [mem_coordHyperplane, PiLp.sub_apply, hu.2.2.2, extend_apply_self_eq_zero κ hy hyi, sub_zero]

include hyφ in
/-- Segments through `κ(y)` in the hyperplane stay in the coordinate domain of the stratum. -/
theorem eventually_line_mem_stratumDom {w : EuclideanSpace ℝ (Fin n)}
    (hw : w ∈ coordHyperplane i) :
    ∀ᶠ t : ℝ in 𝓝 0, κ.toQuadrantChart.extend (𝓠 n) y + t • w ∈ stratumDom κ i φ := by
  set e := κ.toQuadrantChart with he
  set u₀ := e.extend (𝓠 n) y with hu₀
  have hys : y ∈ e.source := hy.1
  have hG : IsOpen (κ.facePiece i ∩ {b : M | b.1 ∈ φ.source}) :=
    (κ.isOpen_facePiece i).inter (φ.isOpen_source.preimage continuous_subtype_val)
  have hleft : (e.extend (𝓠 n)).symm u₀ = y := e.extend_left_inv hys
  have A1 : {u | u ∈ (e.extend (𝓠 n)).target ∧
      (e.extend (𝓠 n)).symm u ∈ κ.facePiece i ∩ {b : M | b.1 ∈ φ.source}} ∈
      𝓝[range (𝓠 n)] u₀ :=
    inter_mem (e.extend_target_mem_nhdsWithin hys)
      (nhdsWithin_le_nhds ((e.continuousAt_extend_symm hys).preimage_mem_nhds
        (hG.mem_nhds (by rw [hleft]; exact ⟨hy, hyφ⟩))))
  obtain ⟨O, hO, hOsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 A1
  have hO' : IsOpen {u : EuclideanSpace ℝ (Fin n) | ∀ l, l ≠ i → 0 < u l} :=
    (isOpen_setOf_forall_ne_pos i).preimage (PiLp.continuous_ofLp 2 _)
  have hu₀O' : u₀ ∈ {u : EuclideanSpace ℝ (Fin n) | ∀ l, l ≠ i → 0 < u l} := fun l hl => by
    rw [hu₀, κ.extend_apply hy.1]; exact hy.2.1 l hl
  have hcont : Tendsto (fun t : ℝ => u₀ + t • w) (𝓝 0) (𝓝 u₀) := by
    have : Continuous fun t : ℝ => u₀ + t • w := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [hcont (inter_mem hO (hO'.mem_nhds hu₀O'))] with t ht
  have hi : (u₀ + t • w) i = 0 := by
    rw [PiLp.add_apply, PiLp.smul_apply, mem_coordHyperplane.1 hw,
      extend_apply_self_eq_zero κ hy hyi, smul_zero, add_zero]
  have hrange : u₀ + t • w ∈ range (𝓠 n) := by
    refine ⟨⟨u₀ + t • w, fun l => ?_⟩, rfl⟩
    by_cases hl : l = i
    · rw [hl, hi]
    · exact (ht.2 l hl).le
  have h := hOsub ⟨ht.1, hrange⟩
  exact ⟨h.1, h.2.1, h.2.2, hi⟩

end Dom

/-! ### The chart image of `T_y∂₁M` -/

variable (hcs : (subPolyfold hY).HasCornerStructureOfDim n)

include hcs in
/-- **`T_y∂₁M` in a chart**: for corner coordinates `κ` of `M` in which only the `i`-th coordinate
of `y` vanishes and a chart `φ` of `X` at `y`, the chart image of the tangent space of the
stratum `{d_M = 1}` is the image of the hyperplane `{vᵢ = 0}` under the derivative `modelDeriv`
of the inclusion. -/
theorem chartTangent_stratumOne_eq (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) {φ : MChart X} (hφ : P.IsChart φ)
    (hyφ : y.1 ∈ φ.source) :
    P.chartTangent hφ (P.stratumOne M) y.1 =
      ((coordHyperplane i).map
        (modelDeriv κ hφ (hM.1.data y.2).toSubData y (levelLift κ.χ 1 y) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0) : Set (φ.model.E 0)) := by
  set d := (hM.1.data y.2).toSubData with hd
  set e := κ.toQuadrantChart with he
  set u₀ := e.extend (𝓠 n) y with hu₀
  have hys : y ∈ κ.s := hy.1
  have hyσ : y ∈ (subChart d hφ y).source := d.mem_shrink φ y.2 (hM.1.mem_data_V y.2) hyφ
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hys) (levelVal_mem (hcs.levelOne y))
  set D := modelDeriv κ hφ d y (levelLift κ.χ 1 y) with hD
  set F : EuclideanSpace ℝ (Fin n) → φ.model.E 0 :=
    (fun b : M => φ b.1) ∘ (e.extend (𝓠 n)).symm with hFdef
  have hF : HasFDerivWithinAt F D (range (𝓠 n)) u₀ :=
    hasFDerivWithinAt_incl κ hφ d y hys hyσ hz
  have hinj : Function.Injective D := modelDeriv_injective κ hφ d y hys hyσ hz
  have hleft : (e.extend (𝓠 n)).symm u₀ = y := e.extend_left_inv hys
  have hFu₀ : F u₀ = φ y.1 := by simp only [hFdef, Function.comp_apply, hleft]
  set B := P.stratumOne M with hBdef
  have hB : P.IsSmoothSubmanifold B := isSmoothSubmanifold_stratumOne hM ht
  have hyB : y.1 ∈ B := (val_mem_stratumOne_iff hM.1 y).2
    ((CornerCoords.degIndex_eq_one_iff hy).2 hyi)
  -- the lower bound
  have hlow : (coordHyperplane i).map (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0) ≤
      P.chartRelTangent hφ B y.1 := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := deriv_mem_span_tangentConeAt_of_line hF (stratumDom_subset_range κ)
      (eventually_line_mem_stratumDom κ hy hyi hyφ hw)
    rw [hFu₀] at h1
    exact Submodule.span_mono (tangentConeAt_mono (image_stratumDom_subset κ hM.1)) h1
  -- the upper bound
  obtain ⟨GX, hGXo, hGX⟩ := isOpen_induced_iff.1 (κ.isOpen_facePiece i)
  have hyGX : y.1 ∈ GX := by
    have : y ∈ Subtype.val ⁻¹' GX := by rw [hGX]; exact hy
    exact this
  set Kset : Set (φ.model.E 0) := φ '' (B ∩ φ.source ∩ GX) with hK
  classical
  set cX : X → EuclideanSpace ℝ (Fin n) :=
    fun x => if h : x ∈ M then e.extend (𝓠 n) ⟨x, h⟩ else u₀ with hcX
  have hcXM : ∀ b : M, cX b.1 = e.extend (𝓠 n) b := fun b => by
    simp only [hcX, dif_pos b.2]
  have hgS : ∀ k ∈ Kset, (cX ∘ φ.symm) k ∈ stratumDom κ i φ ∧ F ((cX ∘ φ.symm) k) = k := by
    rintro _ ⟨b, ⟨⟨hbB, hbφ⟩, hbG⟩, rfl⟩
    have hbM : b ∈ M := stratumOne_subset M hbB
    have hbp : (⟨b, hbM⟩ : M) ∈ κ.facePiece i := by
      have : (⟨b, hbM⟩ : M) ∈ Subtype.val ⁻¹' GX := hbG
      rwa [hGX] at this
    have hval : (cX ∘ φ.symm) (φ b) = e.extend (𝓠 n) ⟨b, hbM⟩ := by
      rw [Function.comp_apply, φ.symm_apply_apply hbφ]
      exact hcXM ⟨b, hbM⟩
    have hl : (e.extend (𝓠 n)).symm (e.extend (𝓠 n) ⟨b, hbM⟩) = ⟨b, hbM⟩ :=
      e.extend_left_inv hbp.1
    have hb0 : κ.coord ⟨b, hbM⟩ i = 0 :=
      (CornerCoords.degIndex_eq_one_iff hbp).1 ((val_mem_stratumOne_iff hM.1 ⟨b, hbM⟩).1 hbB)
    rw [hval]
    refine ⟨⟨(e.extend (𝓠 n)).map_source (by rw [e.extend_source]; exact hbp.1), ?_, ?_, ?_⟩,
      ?_⟩
    · rw [hl]; exact hbp
    · rw [hl]; exact hbφ
    · rw [κ.extend_apply hbp.1]; exact hb0
    · simp only [hFdef, Function.comp_apply, hl]
  have hg : Tendsto (cX ∘ φ.symm) (𝓝[Kset] (F u₀)) (𝓝 u₀) := by
    rw [hFu₀]
    have h1 : Tendsto φ.symm (𝓝[Kset] (φ y.1)) (𝓝 y.1) :=
      tendsto_symm_nhdsWithin_image φ (D := B ∩ φ.source ∩ GX) (fun _ h => h.1.2) hyφ
    have h1' : Tendsto φ.symm (𝓝[Kset] (φ y.1)) (𝓝[M] y.1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨h1, eventually_mem_nhdsWithin.mono ?_⟩
      rintro _ ⟨b, ⟨⟨hbB, hbφ⟩, -⟩, rfl⟩
      rw [φ.symm_apply_apply hbφ]
      exact stratumOne_subset M hbB
    have hc : ContinuousWithinAt cX M y.1 := by
      rw [continuousWithinAt_iff_continuousAt_domRestrict cX y.2]
      have : M.domRestrict cX = e.extend (𝓠 n) := funext fun b => hcXM b
      rw [this]
      exact e.continuousAt_extend hys
    have h2 : Tendsto cX (𝓝[M] y.1) (𝓝 u₀) := by
      have := hc.tendsto
      rwa [hcXM y] at this
    exact h2.comp h1'
  have hKnhds : Kset ∈ 𝓝[φ '' (B ∩ φ.source)] (φ y.1) := by
    have h1 : Tendsto φ.symm (𝓝[φ '' (B ∩ φ.source)] (φ y.1)) (𝓝 y.1) :=
      tendsto_symm_nhdsWithin_image φ (D := B ∩ φ.source) (fun _ h => h.2) hyφ
    filter_upwards [h1 (hGXo.mem_nhds hyGX), self_mem_nhdsWithin] with k hk1 hk2
    obtain ⟨b, hb, rfl⟩ := hk2
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    have := hk1
    rwa [mem_preimage, φ.symm_apply_apply hb.2] at this
  have hup : tangentConeAt ℝ (φ '' (B ∩ φ.source)) (φ y.1) ⊆
      ((coordHyperplane i).map (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] φ.model.E 0) :
        Set (φ.model.E 0)) := by
    refine (tangentConeAt_mono_nhds (nhdsWithin_le_iff.2 hKnhds)).trans ?_
    have := tangentConeAt_subset_map_of_param hinj hF (coordHyperplane i)
      (stratumDom_subset_range κ) (fun u hu => sub_mem_coordHyperplane κ hy hyi hu) hg hgS
    rwa [hFu₀] at this
  have hfull := isRelTangentFull_self hB hyB φ hφ hyφ
  rw [← hfull]
  exact congrArg _ (le_antisymm (Submodule.span_le.2 hup) hlow)

include hcs in
/-- **`Dι(κ(y)) w ∈ E_{φ(y)}` for `wᵢ = 0`**: the derivative of the inclusion maps the hyperplane
`{vᵢ = 0}` into the chart form of `T^R_yX` (the coordinates of the partial quadrant of `X` that
vanish at `y` are `≥ 0` along the stratum and vanish at `y`). -/
theorem modelDeriv_mem_red (hM : P.IsSubmanifoldOfDim M n)
    (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) (c : P.PresentedChart y.1)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ coordHyperplane i) :
    modelDeriv κ c.isChart (hM.1.data y.2).toSubData y (levelLift κ.χ 1 y) w ∈ c.red := by
  set d := (hM.1.data y.2).toSubData with hd
  set e := κ.toQuadrantChart with he
  have hys : y ∈ κ.s := hy.1
  have hyσ : y ∈ (subChart d c.isChart y).source :=
    d.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2) c.mem_source
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hys) (levelVal_mem (hcs.levelOne y))
  have hF := hasFDerivWithinAt_incl κ c.isChart d y hys hyσ hz
  have hleft : (e.extend (𝓠 n)).symm (e.extend (𝓠 n) y) = y := e.extend_left_inv hys
  refine (mem_minimalSubspaceWith c.T).2 fun j hj => ?_
  let T₀ : c.φ.model.E 0 ≃L[ℝ] (Fin c.n → ℝ) × c.W 0 := c.T 0
  let ℓ : c.φ.model.E 0 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin c.n => ℝ) j).comp
      ((ContinuousLinearMap.fst ℝ (Fin c.n → ℝ) (c.W 0)).comp (T₀ : c.φ.model.E 0 →L[ℝ] _))
  have key := clm_deriv_eq_zero_of_line hF (stratumDom_subset_range κ)
    (eventually_line_mem_stratumDom κ hy hyi c.mem_source hw) ℓ ?_
  · exact key
  · intro u hu
    have h0 : ℓ (((fun b : M => c.φ b.1) ∘ (e.extend (𝓠 n)).symm) (e.extend (𝓠 n) y)) = 0 := by
      simp only [Function.comp_apply, hleft]
      exact hj
    rw [h0]
    have hC : c.φ ((e.extend (𝓠 n)).symm u).1 ∈ c.φ.model.C := c.φ.apply_mem_C hu.2.2.1
    rw [c.hT] at hC
    exact hC j

include hcs in
/-- The chart computation behind `submanifoldTangent_stratumOne` and
`isSubmanifoldOfDim_stratumOne`. -/
theorem stratumOne_tangent_aux (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) :
    P.submanifoldTangent (P.stratumOne M) y.1 =
        P.boundaryCarrier (P.submanifoldTangent M y.1) ∧
      P.HasDimAt (P.stratumOne M) y.1 (n - 1) := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y.1
  set d := (hM.1.data y.2).toSubData with hd
  have hys : y ∈ κ.s := hy.1
  have hyσ : y ∈ (subChart d c.isChart y).source :=
    d.mem_shrink c.φ y.2 (hM.1.mem_data_V y.2) c.mem_source
  have hz : κ.χ.model.E.toBase 1 (levelLift κ.χ 1 y) = κ.χ y :=
    (subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset hys) (levelVal_mem (hcs.levelOne y))
  set D := modelDeriv κ c.isChart d y (levelLift κ.χ 1 y) with hD
  have hinj : Function.Injective D := modelDeriv_injective κ c.isChart d y hys hyσ hz
  set T' := (coordHyperplane i).map (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0) with hT'
  obtain ⟨NM, hNM, hfin⟩ := exists_submodule_chartTangent c.isChart hM.1 y.2 c.mem_source
  have := hfin
  have hrange : LinearMap.range (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0) ≤ NM := by
    rintro _ ⟨v, rfl⟩
    rw [← SetLike.mem_coe, hNM]
    exact modelDeriv_mem_chartTangent (hcs := hcs) hM.1 κ hys v c.isChart c.mem_source
  have hNMn : finrank ℝ NM = n :=
    finrank_chartTangent c.isChart (hM.2 y.1 y.2) hM.1 c.mem_source hNM
  have hq : quotDim NM c.red = 1 := by
    have h := subDegIndex_eq_quotDim_span hM.1 ht y.2 c
    have h1 : P.subDegIndex hM.1.isSubMPolyfold ⟨y.1, y.2⟩ = 1 :=
      (CornerCoords.degIndex_eq_one_iff hy).2 hyi
    have hv : c.vec '' P.submanifoldTangent M y.1 = (NM : Set (c.φ.model.E 0)) := hNM.symm
    rw [h1, hv, Submodule.span_eq] at h
    exact h.symm
  have hfin2 := finrank_inf_eq_of_quotDim_eq_one hq
  have hT'le : T' ≤ NM ⊓ c.red := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hrange ⟨w, rfl⟩, modelDeriv_mem_red hcs hM κ hy hyi c hw⟩
  have hT'fin : finrank ℝ T' = finrank ℝ (coordHyperplane (n := n) i) :=
    (Submodule.equivMapOfInjective (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0) hinj
      (coordHyperplane i)).finrank_eq.symm
  have hH := finrank_coordHyperplane i
  have hT'eq : T' = NM ⊓ c.red := Submodule.eq_of_le_of_finrank_eq hT'le (by omega)
  have hB : P.IsSmoothSubmanifold (P.stratumOne M) := isSmoothSubmanifold_stratumOne hM ht
  have hyB : y.1 ∈ P.stratumOne M := (val_mem_stratumOne_iff hM.1 y).2
    ((CornerCoords.degIndex_eq_one_iff hy).2 hyi)
  have h11 : P.chartTangent c.isChart (P.stratumOne M) y.1 = (T' : Set (c.φ.model.E 0)) :=
    chartTangent_stratumOne_eq hcs hM ht κ hy hyi c.isChart c.mem_source
  have h12 : c.vec '' P.boundaryCarrier (P.submanifoldTangent M y.1) =
      (T' : Set (c.φ.model.E 0)) := by
    rw [c.vec_image_boundaryCarrier (fun α hα => hα.1), hT'eq, Submodule.coe_inf]
    congr 1
    exact hNM.symm
  constructor
  · refine ((chartVec_injOn c.isChart c.mem_source).image_eq_image_iff
      (submanifoldTangent_subset_fiber _ _) (fun α hα => hα.1.1)).1 ?_
    exact h11.trans h12.symm
  · obtain ⟨k, hk⟩ := hB.exists_hasDimAt hyB
    have hk' : finrank ℝ T' = k := finrank_chartTangent c.isChart hk hB c.mem_source h11.symm
    have : k = n - 1 := by omega
    exact this ▸ hk

include hcs in
/-- **The frames `Tι(v)`, `vᵢ = 0`, are tangent to the stratum.** -/
theorem incFrame_mem_submanifoldTangent_stratumOne (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) (κ : CornerCoords (subPolyfold hY) n) {i : Fin n} {y : M}
    (hy : y ∈ κ.facePiece i) (hyi : κ.coord y i = 0) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ coordHyperplane i) :
    incFrame hcs κ hy.1 v ∈ P.submanifoldTangent (P.stratumOne M) y.1 := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y.1
  have hyσ : y ∈ (subChart (hM.1.data y.2).toSubData hφ y).source :=
    (hM.1.data y.2).toSubData.mem_shrink φ y.2 (hM.1.mem_data_V y.2) hyφ
  have h : chartVec hφ (incFrame hcs κ hy.1 v) ∈ P.chartTangent hφ (P.stratumOne M) y.1 := by
    rw [chartTangent_stratumOne_eq hcs hM ht κ hy hyi hφ hyφ,
      chartVec_incFrame (hcs := hcs) κ hy.1 v hφ _ y hyσ]
    exact ⟨v, hv, rfl⟩
  obtain ⟨α, hα, hαv⟩ := h
  have : incFrame hcs κ hy.1 v = α :=
    chartVec_injOn hφ hyφ (levelVal_tangentProj_incFrame κ hy.1 v) hα.1 hαv.symm
  rw [this]; exact hα

end MPolyfold

/-! ### The statements for a tame sheet -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {n : ℕ}

/-- **`T_y∂₁M = T_y∂M` of Definition 9.3.8** (2021 p. 427; 2017: Definition 9.9): for an
`n`-dimensional submanifold `M` with tame induced structure and `y` with `d_M(y) = 1`, the
tangent space at `y` of the stratum `{d_M = 1}` (a smooth submanifold of `X`,
`isSmoothSubmanifold_stratumOne`) is `T^R_yM = boundaryCarrier (T_yM)`. -/
theorem submanifoldTangent_stratumOne (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) {y : X} (hy : y ∈ P.stratumOne M) :
    P.submanifoldTangent (P.stratumOne M) y = P.boundaryCarrier (P.submanifoldTangent M y) := by
  have := P.paracompactSpace_subtype M
  obtain ⟨_, hyM, h1⟩ := hy
  obtain ⟨κ, i, hyp, hyi⟩ := exists_stratum_coords hM ht hyM h1
  exact (stratumOne_tangent_aux (hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht) hM ht
    κ hyp hyi).1

/-- **The stratum `∂₁M = {d_M = 1}` of a tame `n`-dimensional sheet is an `(n-1)`-dimensional
submanifold of `X`** (for Definition 9.3.8, 2021 p. 427, and the boundary integrals of
Theorem 9.5.15, p. 448). -/
theorem isSubmanifoldOfDim_stratumOne (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) : P.IsSubmanifoldOfDim (P.stratumOne M) (n - 1) := by
  refine ⟨isSmoothSubmanifold_stratumOne hM ht, fun y hy => ?_⟩
  have := P.paracompactSpace_subtype M
  obtain ⟨_, hyM, h1⟩ := hy
  obtain ⟨κ, i, hyp, hyi⟩ := exists_stratum_coords hM ht hyM h1
  exact (stratumOne_tangent_aux (hM.hasCornerStructureOfDim_of_hasTameInducedStructure ht) hM ht
    κ hyp hyi).2

/-- The same for `boundaryStratum M`, the domain of
`SubmanifoldOrientation.boundaryOrientation`. -/
theorem isSubmanifoldOfDim_boundaryStratum (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) : P.IsSubmanifoldOfDim (P.boundaryStratum M) (n - 1) :=
  stratumOne_eq_boundaryStratum hM.1 ht ▸ isSubmanifoldOfDim_stratumOne hM ht

theorem submanifoldTangent_boundaryStratum (hM : P.IsSubmanifoldOfDim M n)
    (ht : P.HasTameInducedStructure M) {y : X} (hy : y ∈ P.boundaryStratum M) :
    P.submanifoldTangent (P.boundaryStratum M) y =
      P.boundaryCarrier (P.submanifoldTangent M y) := by
  rw [← stratumOne_eq_boundaryStratum hM.1 ht] at hy ⊢
  exact submanifoldTangent_stratumOne hM ht hy

end MPolyfold

end Polyfold
