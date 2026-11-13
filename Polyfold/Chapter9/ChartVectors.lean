import Polyfold.Chapter9.SheetChartChange
import Polyfold.Chapter9.BoundaryOrientationContinuity2021
import Polyfold.Chapter9.SheetEssentialChart2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.3
(Definition 9.3.3, p. 422) and §9.5: chart changes along a finite-dimensional submanifold, for
the integration of forms over oriented sheets (gap G.107).

# Chart vectors along a submanifold, and frames of an oriented tangent space
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The chart vectors in a second chart, through the derivative of the chart change composed
with a retraction onto the overlap. -/
theorem chartVec_eq_scDeriv_transition {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    {R : ScRetraction φ.model.E φ.model.C} (hR : R.retract = φ.overlap ψ) {z : X}
    (hzφ : z ∈ φ.source) (hzψ : z ∈ ψ.source) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = z) :
    chartVec hψ α = scDeriv R.U (φ.transition ψ ∘ R) (levelLift φ 1 z) (chartVec hφ α) := by
  have hf := (hφ.compatible hψ (P := P)).1
  have hαφ : α ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hα]; exact hzφ
  have hmem := tangentChartMap_mem hφ hαφ
  have hfst : (tangentChartMap hφ α).1 = levelLift φ 1 z := by
    rw [tangentChartMap_fst hφ hαφ, hα]
  have hz1 : z ∈ P.levelSet 1 := hα ▸ (P.tangentProj α).2
  have hov : (tangentChartMap hφ α) ∈ retractTangent φ.model.E φ.model.C (φ.overlap ψ) := by
    have hsub : φ.source ∩ ψ.source ⊆ φ.source := inter_subset_left
    refine (TangentPre.mem_retractTangent_image_iff hsub (φ.isOpen_source.inter ψ.isOpen_source)
      ?_).2 hmem
    rw [hfst, P.toBase_levelLift hφ hzφ hz1]
    exact ⟨z, ⟨hzφ, hzψ⟩, rfl⟩
  have h1 := tangentChartMap_mk_ofVec_of_mem hφ hψ hmem hov
  rw [mk_ofVec_tangentChartMap hφ hαφ] at h1
  unfold chartVec
  rw [h1, retractTangentMap_apply hf R hR hov, hfst]

/-- **The derivative of the chart change along a submanifold acts on the chart vectors**: for
charts `φ`, `ψ` at `z ∈ M` there is one continuous linear `L` which is the derivative of
`ψ ∘ φ⁻¹` at `φ(z)` within `φ(M ∩ dom ψ ∩ dom φ)` (level-`0` norms) and carries the chart vectors
of the tangent vectors over `z`. -/
theorem exists_transition_deriv_chartVec {φ ψ : MChart X} (hφ : P.IsChart φ)
    (hψ : P.IsChart ψ) {M : Set X} (hM : P.IsSmoothSubmanifold M) {z : X} (hz : z ∈ M)
    (hzφ : z ∈ φ.source) (hzψ : z ∈ ψ.source) :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
      HasFDerivWithinAt (φ.transition ψ) L (φ '' (M ∩ ψ.source ∩ φ.source)) (φ z) ∧
      ∀ α : P.TangentSpace, P.levelVal 1 (P.tangentProj α) = z →
        chartVec hψ α = L (chartVec hφ α) := by
  obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
  refine ⟨scDeriv R.U (φ.transition ψ ∘ R) (levelLift φ 1 z), ?_,
    fun α hα => chartVec_eq_scDeriv_transition hφ hψ hR hzφ hzψ hα⟩
  set d := hM.data hz
  have hzV : z ∈ d.V := hM.mem_data_V hz
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hz hzV
  obtain ⟨hz1, hzt, -⟩ := chartTangent_eq_range hφ d ht hz hzV hzφ
  have hf : IsScSmooth R.U (φ.transition ψ ∘ R) :=
    (hφ.compatible hψ (P := P)).1.comp_isScSmooth R hR
  have hzR : φ z ∈ R.retract := hR ▸ φ.mem_overlap ψ hzφ hzψ
  have hd := ScRetraction.hasFDerivWithinAt_of_isSc1 htp R.isScDomain hf.isSc1
    (z := levelLift φ 1 z) (by rw [hz1]; exact hzt) (by rw [hz1]; exact R.retract_subset hzR)
    (S := t.retract ∩ R.retract) (fun a ha => ⟨ha.1, R.retract_subset ha.2⟩)
  rw [hz1] at hd
  refine (hd.congr (fun a ha => ?_) ?_).mono_of_mem_nhdsWithin ?_
  · change φ.transition ψ a = φ.transition ψ (R a)
    rw [R.apply_eq_self_of_mem_retract ha.2]
  · change φ.transition ψ (φ z) = φ.transition ψ (R (φ z))
    rw [R.apply_eq_self_of_mem_retract hzR]
  · have hev := eventually_mem_retract d ht (K := M ∩ ψ.source) inter_subset_left
      (d.toSubData.mem_shrink φ hz hzV hzφ) hzφ
    filter_upwards [hev, self_mem_nhdsWithin] with p hp hpS
    refine ⟨hp, ?_⟩
    obtain ⟨k, hk, rfl⟩ := hpS
    rw [hR]
    exact φ.mem_overlap ψ hk.2 hk.1.2

/-- **Continuity of a frame field of a submanifold does not depend on the chart.** -/
theorem continuousOn_chartVec_of_chart {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    {M : Set X} (hM : P.IsSmoothSubmanifold M) {K : Set X} (hK : K ⊆ M ∩ φ.source ∩ ψ.source)
    {n : ℕ} (e : X → Fin n → P.TangentSpace)
    (he : ∀ z ∈ K, ∀ i, e z i ∈ P.submanifoldTangent M z)
    (hc : ContinuousOn (fun z i => chartVec hφ (e z i)) K) :
    ContinuousOn (fun z i => chartVec hψ (e z i)) K := by
  obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
  have hf : IsScSmooth R.U (φ.transition ψ ∘ R) :=
    (hφ.compatible hψ (P := P)).1.comp_isScSmooth R hR
  have hD := hf.isSc1.isSc1With_scDeriv.continuousOn_deriv
  intro z₀ hz₀
  have hz₀M : z₀ ∈ M := (hK hz₀).1.1
  set d := hM.data hz₀M
  have hzV : z₀ ∈ d.V := hM.mem_data_V hz₀M
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hz₀M hzV
  set W := d.toSubData.shrink φ with hW
  have hWo : IsOpen W := d.toSubData.isOpen_shrink φ
  have hz₀W : z₀ ∈ W := d.toSubData.mem_shrink φ hz₀M hzV (hK hz₀).1.2
  have hlift : ∀ z ∈ K ∩ W, levelLift φ 1 z = t.plusLift (φ z) := fun z hz =>
    levelLift_eq_plusLift hφ d ht (hK hz.1).1.1 (d.toSubData.shrink_subset_V φ hz.2)
      (hK hz.1).1.2
  have hret : ∀ z ∈ K ∩ W, φ z ∈ t.retract := fun z hz => by
    rw [ht]; exact ⟨z, ⟨hz.2, (hK hz.1).1.1⟩, rfl⟩
  have hφc : ContinuousOn φ (K ∩ W) :=
    φ.continuousOn_toFun.mono fun z hz => (hK hz.1).1.2
  have hl : ContinuousOn (fun z => levelLift φ 1 z) (K ∩ W) :=
    ((ScRetraction.continuousOn_plusLift htp).comp hφc fun z hz =>
      t.retract_subset (hret z hz)).congr hlift
  have key : ContinuousOn (fun z i => chartVec hψ (e z i)) (K ∩ W) := by
    refine continuousOn_pi.2 fun i => ?_
    have hci : ContinuousOn (fun z => chartVec hφ (e z i)) (K ∩ W) :=
      ((continuous_apply i).comp_continuousOn hc).mono inter_subset_left
    have hcomp := hD.comp (hl.prodMk hci) (fun z hz => by
      change levelLift φ 1 z ∈ φ.model.E.lvlSet R.U 1
      have hz1 : z ∈ P.levelSet 1 := by
        have := he z hz.1 i
        rw [← this.1]; exact levelVal_mem _
      rw [ScBanach.mem_lvlSet, P.toBase_levelLift hφ (hK hz.1).1.2 hz1]
      exact R.retract_subset (hR ▸ φ.mem_overlap ψ (hK hz.1).1.2 (hK hz.1).2))
    refine hcomp.congr fun z hz => ?_
    exact chartVec_eq_scDeriv_transition hφ hψ hR (hK hz.1).1.2 (hK hz.1).2 (he z hz.1 i).1
  exact (key z₀ ⟨hz₀, hz₀W⟩).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin K (hWo.mem_nhds hz₀W))

/-- **Frames of an oriented tangent space and determinants**: if `α` is a positive frame and the
chart vectors of `β ∈ Lⁿ` are the combinations `∑ᵢ Mᵢⱼ αᵢ`, then `β` is a positive frame iff
`det M > 0`. -/
theorem IsOrientedAt.mem_frames_iff_det_pos {y : X} {g : OrTangent P} (hg : P.IsOrientedAt y g)
    {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) {α β : Fin g.dim → P.TangentSpace}
    (hα : α ∈ g.frames) (hβ : ∀ i, β i ∈ g.carrier) (M : Matrix (Fin g.dim) (Fin g.dim) ℝ)
    (h : ∀ j, chartVec hφ (β j) = ∑ i, M i j • chartVec hφ (α i)) :
    β ∈ g.frames ↔ 0 < M.det := by
  obtain ⟨N, hN, hfin, hrank, ω, hO⟩ := hg.isChartOrientation hφ hyφ
  have := hfin
  have hα' := hα
  rw [hO] at hα'
  obtain ⟨-, b₁, hb₁, hbo₁⟩ := hα'
  let w : Fin g.dim → N := fun j => ∑ i, M i j • b₁ i
  have hw : ∀ j, (w j : φ.model.E 0) = chartVec hφ (β j) := fun j => by
    rw [h j]
    simp only [w, Submodule.coe_sum, Submodule.coe_smul, hb₁]
  have hdet : b₁.det w = M.det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    simp only [Basis.toMatrix_apply, w, map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
    simp
  rw [hO]
  constructor
  · rintro ⟨-, b, hb, hbo⟩
    have hbw : (b : Fin g.dim → N) = w := funext fun j => Subtype.ext ((hb j).trans (hw j).symm)
    rw [← hdet, ← hbw]
    exact (b₁.orientation_eq_iff_det_pos b).1 (hbo₁.trans hbo.symm)
  · intro hpos
    have hunit : IsUnit (b₁.det w) := by rw [hdet]; exact isUnit_iff_ne_zero.2 hpos.ne'
    obtain ⟨hli, hsp⟩ := b₁.is_basis_iff_det.2 hunit
    set b := Basis.mk hli hsp.ge with hbdef
    have hbw : (b : Fin g.dim → N) = w := Basis.coe_mk hli hsp.ge
    refine ⟨hβ, b, fun j => by rw [hbw]; exact hw j, ?_⟩
    rw [← hbo₁]
    refine ((b₁.orientation_eq_iff_det_pos b).2 ?_).symm
    rw [hbw, hdet]; exact hpos

/-- **The two orientations of a tangent space**: for two different orientations of `L`, a frame
of `L` with linearly independent chart vectors is positive for exactly one of them. -/
theorem IsOrientedAt.mem_frames_iff_notMem {y : X} {n : ℕ} {L : Set P.TangentSpace}
    {O O' : Set (Fin n → P.TangentSpace)} (h : P.IsOrientedAt y ⟨n, L, O⟩)
    (h' : P.IsOrientedAt y ⟨n, L, O'⟩) (hne : O ≠ O') {φ : MChart X} (hφ : P.IsChart φ)
    (hyφ : y ∈ φ.source) {α : Fin n → P.TangentSpace} (hα : ∀ i, α i ∈ L)
    (hli : LinearIndependent ℝ fun i => chartVec hφ (α i)) : α ∈ O ↔ α ∉ O' := by
  obtain ⟨N, hN, hfin, hrank, ω, hOω⟩ := h.isChartOrientation hφ hyφ
  obtain ⟨N', hN', -, -, ω', hOω'⟩ := h'.isChartOrientation hφ hyφ
  have hNN : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
  subst hNN
  have := hfin
  change O = chartFrames hφ L N' ω at hOω
  change O' = chartFrames hφ L N' ω' at hOω'
  have hcard : Fintype.card (Fin n) = finrank ℝ N' := by rw [Fintype.card_fin]; exact hrank.symm
  have hωne : ω ≠ ω' := fun hω => hne (by rw [hOω, hOω', hω])
  have hω' : ω' = -ω := (ω'.eq_or_eq_neg ω hcard).resolve_left (Ne.symm hωne)
  have hmem : ∀ i, chartVec hφ (α i) ∈ N' := fun i => by
    rw [← SetLike.mem_coe, hN]; exact ⟨α i, hα i, rfl⟩
  let w : Fin n → N' := fun i => ⟨chartVec hφ (α i), hmem i⟩
  have hliw : LinearIndependent ℝ w := LinearIndependent.of_comp N'.subtype hli
  set b := basisOfLinearIndependentOfCardEqFinrank' w hliw hcard
  have hb : ∀ i, (b i : φ.model.E 0) = chartVec hφ (α i) := fun i => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank', w]
  have key : ∀ ρ : Orientation ℝ N' (Fin n), α ∈ chartFrames hφ L N' ρ ↔ b.orientation = ρ := by
    intro ρ
    constructor
    · rintro ⟨-, b', hb', hbo'⟩
      have : b' = b := Basis.eq_of_apply_eq fun i => Subtype.ext ((hb' i).trans (hb i).symm)
      rw [← this]; exact hbo'
    · intro hρ
      exact ⟨hα, b, hb, hρ⟩
  rw [hOω, hOω', key, key, hω']
  constructor
  · intro h1 h2
    exact Module.Ray.ne_neg_self ω (h1.symm.trans h2)
  · intro h2
    exact (b.orientation.eq_or_eq_neg ω hcard).resolve_right h2

end MPolyfold

end Polyfold
