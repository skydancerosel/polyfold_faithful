import Polyfold.Examples.Classical.DetSign

/-!
# The sign of an orientation at block isomorphisms, in Banach spaces

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6 and
Theorem 16.6.6 (2021 p. 739).  For an orientation `o` of `DET` over a convex set `C` of Fredholm
operators `E → F` between Banach spaces, read through isomorphisms `E ≅ V × W ≅ F` with `V`
finite-dimensional, and for isomorphisms `A₀, A₁` of `V`: `o` is the ray of the unit
`1 ⊗ 1* ∈ det = λ(0) ⊗ λ*(0)` at `A₁ ⊕ id_W` iff (it is the ray of the unit at `A₀ ⊕ id_W` iff
`det A₀` and `det A₁` have the same sign).  This extends `DetSign.lean` (finite-dimensional `E`,
`F`) to operators of the form `A ⊕ id_W`, such as those on `ℝⁿ × ℓ²`.

The finite-dimensional proof uses one chart with `P = 0`, which is not a good left projection in
infinite dimensions.  Here two kinds of charts are used.

* Near an isomorphism `T₀` the chart with `P = id` has `ker(P T₀) = 0` and `F / R(P) = 0`, so the
  coordinate of the unit is `1` at every isomorphism of its ball: whether `o` is the ray of the
  unit is locally constant on the isomorphisms of `C`.  Along `λ ↦ λ A ⊕ id_W`, `λ ∈ [s, 1]`, it
  does not change.
* The block chart is centred at `0 ⊕ id_W` with `P` the projection onto the `W`-part of `F`; then
  `ker(P T) = V × 0` and `P (A ⊕ id_W) = P (0 ⊕ id_W)` for every `A`, so `k(A ⊕ id_W) = k` and by
  formula (91) the coordinate of the unit at `A ⊕ id_W` is `(det A · t)⁻¹` with `t ≠ 0` independent
  of `A`.  For small `s` the operators `s A₀ ⊕ id_W`, `s A₁ ⊕ id_W` lie in its ball, and the sign
  of an orientation in the chart is constant on the convex set `C ∩ ball`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `detUnit'`, `unitRay'`: the unit of `det S` and its ray, for an isomorphism `S` between Banach
  spaces; `surjRay_unitRay'`, `conjDet_detUnit'`, `ray_map_conjDet_unitRay'`.
* `coord_detUnit'`: the coordinate of the unit in a chart is the inverse of the determinant
  `chartDet` of `k ↦ [S k(S)]` in the frames of the chart.
* `ray_eq_unitRay_iff_chart`: the comparison at two isomorphisms in the ball of one chart;
  `exists_ball_unitRay_iff`: local constancy near an isomorphism.
* `blk eT eK A = A ⊕ id_W`, `bijective_blk`, the block chart (`projW`, `isGoodLeftProj_blk`,
  `chartDet_blk`), `unitAt_smul_iff`.
* **`ray_eq_unitRay_iff_blk`**: the sign comparison at `A₀ ⊕ id_W` and `A₁ ⊕ id_W`.
* `isPos_iff_eq_unitRay'` (without finite dimension of `T_zO`, `K_z`), **`isPos_iff_blk`**,
  `isPos_iff_blk_of_isPos`: the forms at a chart point.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Module Topology Function Bundle TensorProduct

noncomputable section

namespace Polyfold.Examples.Classical.Product

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem finrank_ker_of_injective' {S : E →L[ℝ] F} (hS : Injective S) :
    finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)) = 0 := by
  rw [LinearMap.ker_eq_bot.2 hS, finrank_bot]

theorem finiteDimensional_ker_of_injective {S : E →L[ℝ] F} (hS : Injective S) :
    FiniteDimensional ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)) := by
  rw [LinearMap.ker_eq_bot.2 hS]; infer_instance

theorem finiteDimensional_coker_of_surjective {S : E →L[ℝ] F} (hS : Surjective S) :
    FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := by
  have : Subsingleton (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) :=
    Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hS)
  infer_instance

/-- **The unit of `det S`** for an isomorphism `S` between Banach spaces: `det S = λ(0) ⊗ λ*(0)`
and the unit is the empty wedge tensored with the dual of the empty wedge. -/
def detUnit' {S : E →L[ℝ] F} (hS : Bijective S) : fredholmDet S :=
  emptyWedge _ (finrank_ker_of_injective' hS.1) ⊗ₜ
    dualVec (emptyWedge _ (finrank_coker_of_surjective hS.2))

theorem detEquivOfSurjective_detUnit' {S : E →L[ℝ] F} (hS : Bijective S) :
    detEquivOfSurjective hS.2 (detUnit' hS) = emptyWedge _ (finrank_ker_of_injective' hS.1) := by
  have := finiteDimensional_coker_of_surjective hS.2
  rw [detUnit', detEquivOfSurjective_tmul,
    dualVec_self finrank_maxPow (emptyWedge_ne_zero _ _), one_smul]

theorem detUnit'_ne_zero {S : E →L[ℝ] F} (hS : Bijective S) : detUnit' hS ≠ 0 := fun h =>
  have := finiteDimensional_ker_of_injective hS.1
  emptyWedge_ne_zero _ (finrank_ker_of_injective' hS.1)
    (by rw [← detEquivOfSurjective_detUnit' hS, h, LinearEquiv.map_zero])

/-- The ray of the unit of `det S`, for an isomorphism `S` between Banach spaces. -/
def unitRay' {S : E →L[ℝ] F} (hS : Bijective S) : Module.Ray ℝ (fredholmDet S) :=
  rayOfNeZero ℝ _ (detUnit'_ne_zero hS)

theorem map_detEquivOfSurjective_unitRay' {S : E →L[ℝ] F} (hS : Bijective S) :
    Module.Ray.map (detEquivOfSurjective hS.2) (unitRay' hS) =
      haveI := finiteDimensional_ker_of_injective hS.1
      emptyRay _ (finrank_ker_of_injective' hS.1) := by
  rw [unitRay', Module.Ray.map_apply]
  exact rayOfNeZero_congr (detEquivOfSurjective_detUnit' hS) _ _

/-- `surjRay` maps the ray of the unit to the ray of the empty wedge. -/
theorem surjRay_unitRay' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {S : E →L[ℝ] F}
    (hS : Bijective S) (j : E →L[ℝ] V) (hj : Injective j) {N : Submodule ℝ V}
    (hN : (LinearMap.ker (S : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N) [FiniteDimensional ℝ N]
    (hN0 : finrank ℝ N = 0) :
    surjRay hS.2 j hj hN (unitRay' hS) = emptyRay N hN0 := by
  have := finiteDimensional_ker_of_injective hS.1
  rw [surjRay, Equiv.trans_apply, map_detEquivOfSurjective_unitRay' hS]
  exact ray_map_maxPowEquiv_emptyRay _ _ _

/-- **The coordinate of the unit in a chart**: for an isomorphism `S` in the ball,
`γ^P_S(1 ⊗ 1*) = (k(S) ∧ …) ⊗ (S k(S) ∧ …)*` (formula (91)), so the coordinate is the inverse of
the determinant of `k ↦ [S k]` in the frames of the chart. -/
theorem coord_detUnit' (c : LocalDetChart E F) {S : FredholmOp E F} (hS' : ‖S.1 - c.T‖ < c.ε)
    (hb : Bijective S.1)
    (h : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = finrank ℝ c.K) :
    c.coord S (detUnit' hb) =
      ((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).det
        (fun i => Submodule.Quotient.mk
          (S.1 (c.kerMap S.1 (Module.finBasis ℝ c.K (Fin.cast h i) : E)))))⁻¹ := by
  refine (c.coord_apply hS' _).trans ?_
  have hP := c.isGoodLeftProj_of_lt S.1 hS'
  have := c.finiteDimensional_coker S.1 hS'
  have := c.finiteDimensional_ker S.1 hS'
  have hj : 0 + finrank ℝ c.K =
      finrank ℝ (LinearMap.ker ((c.P ∘L S.1 : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
    rw [zero_add]; exact (c.kerEquiv S.1 hS').finrank_eq
  have hC : 0 + finrank ℝ c.K =
      finrank ℝ (F ⧸ LinearMap.range ((c.P ∘L S.1 : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
    rw [zero_add, ← h]; exact (cokerCompEquiv hP).symm.finrank_eq
  have hJ : (projSeqJ S.1 c.P ∘ (Fin.elim0 : Fin 0 → LinearMap.ker (S.1 : E →ₗ[ℝ] F))) =
      Fin.elim0 := funext fun i => i.elim0
  have hb' : LinearIndependent ℝ (Fin.append (projSeqJ S.1 c.P ∘
      (Fin.elim0 : Fin 0 → LinearMap.ker (S.1 : E →ₗ[ℝ] F))) (c.kerFrame S.1 hS')) := by
    rw [hJ, Fin.elim0_append]
    exact (c.kerFrame_linearIndependent S.1 hS').comp _ (Fin.cast_injective _)
  have key := gammaProj_wedge_tmul S.2 hP (a := Fin.elim0) linearIndependent_empty_type
    (finrank_ker_of_injective' hb.1).symm (d := Fin.elim0) linearIndependent_empty_type
    (finrank_coker_of_surjective hb.2).symm hb' hj (c := Fin.elim0) (fun i => i.elim0) hC
  rw [show detUnit' hb = wedge (Fin.elim0 : Fin 0 → LinearMap.ker (S.1 : E →ₗ[ℝ] F))
      (finrank_ker_of_injective' hb.1).symm ⊗ₜ dualVec (wedge
        (Fin.elim0 : Fin 0 → F ⧸ LinearMap.range (S.1 : E →ₗ[ℝ] F))
        (finrank_coker_of_surjective hb.2).symm) from rfl, key]
  have hk : wedge (Fin.append (projSeqJ S.1 c.P ∘
      (Fin.elim0 : Fin 0 → LinearMap.ker (S.1 : E →ₗ[ℝ] F))) (c.kerFrame S.1 hS')) hj =
      wedge (c.kerFrame S.1 hS') (c.kerEquiv S.1 hS').finrank_eq := by
    rw [hJ, Fin.elim0_append]
    exact wedge_cast _ _ _
  have hkk : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = 0 + finrank ℝ c.K := by
    rw [zero_add]; exact h
  have hfr : wedge (c.kerFrame S.1 hS') (c.kerEquiv S.1 hS').finrank_eq ⊗ₜ
      dualVec (wedge (c.cokerFrame S.1 hS') (cokerCompEquiv hP).symm.finrank_eq) =
        c.frame S.1 hS' := rfl
  rw [hk, c.dualVec_wedge_eq_inv_det_smul S.1 hS' _ hC hkk, TensorProduct.tmul_smul, hfr,
    LinearMap.map_smul,
    dualVec_self (finrank_fredholmDet (hP.isFredholm_comp S.2)) (c.frame_ne_zero S.1 hS'),
    smul_eq_mul, mul_one, Basis.det_reindex]
  congr 2
  funext i
  simp only [Function.comp_apply, Fin.elim0_append, LinearEquiv.apply_symm_apply]
  rfl

/-- The determinant of `k ↦ [S k(S)]` in the frames of a chart (`k(S) = k + y(k, S)`), whose
inverse is the coordinate of the unit (`coord_detUnit'`). -/
def chartDet (c : LocalDetChart E F)
    (h : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = finrank ℝ c.K) (S : E →L[ℝ] F) : ℝ :=
  (Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).det
    (fun i => Submodule.Quotient.mk (S (c.kerMap S (Module.finBasis ℝ c.K (Fin.cast h i) : E))))

theorem coord_detUnit'_eq (c : LocalDetChart E F) {S : FredholmOp E F} (hS' : ‖S.1 - c.T‖ < c.ε)
    (hb : Bijective S.1)
    (h : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = finrank ℝ c.K) :
    c.coord S (detUnit' hb) = (chartDet c h S.1)⁻¹ :=
  coord_detUnit' c hS' hb h

theorem chartDet_ne_zero (c : LocalDetChart E F) {S : FredholmOp E F} (hS' : ‖S.1 - c.T‖ < c.ε)
    (hb : Bijective S.1)
    (h : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = finrank ℝ c.K) :
    chartDet c h S.1 ≠ 0 := by
  intro h0
  have h1 := c.coordInv_coord hS' (detUnit' hb)
  rw [coord_detUnit'_eq c hS' hb h, h0, inv_zero, map_zero] at h1
  exact detUnit'_ne_zero hb h1.symm

/-- **Sign of an orientation of `DET` at two isomorphisms in one chart**: for an orientation `o`
of `DET` over a convex set `C` and two isomorphisms `T₀, T₁ ∈ C` in the ball of a chart, `o` is
the ray of the unit at `T₁` iff (it is the ray of the unit at `T₀` iff the determinants of
`k ↦ [T₀ k(T₀)]` and `k ↦ [T₁ k(T₁)]` in the frames of the chart have the same sign). -/
theorem ray_eq_unitRay_iff_chart (ch : LocalDetChart E F)
    (hF0 : finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)) = finrank ℝ ch.K)
    {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    (hC : ∀ T ∈ C, T.IsFredholm) (o : LineOrientation (DetOn C hC)) {T₀ T₁ : E →L[ℝ] F}
    (h₀ : T₀ ∈ C) (h₁ : T₁ ∈ C) (hb₀ : Bijective T₀) (hb₁ : Bijective T₁)
    (hε₀ : ‖T₀ - ch.T‖ < ch.ε) (hε₁ : ‖T₁ - ch.T‖ < ch.ε) :
    o ⟨T₁, h₁⟩ = unitRay' hb₁ ↔ (o ⟨T₀, h₀⟩ = unitRay' hb₀ ↔
      0 < chartDet ch hF0 T₀ * chartDet ch hF0 T₁) := by
  classical
  have hmem : ch.pretriv ∈ (detPrebundle E F).pretrivializationAtlas := ⟨ch, rfl⟩
  let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas hmem
  have : e.IsLinear ℝ := (detPrebundle E F).linear_trivializationOfMemPretrivializationAtlas hmem
  let e' := e.pullback (fredholmIncl hC)
  have hbase : ∀ T (hT : T ∈ C), ‖T - ch.T‖ < ch.ε → (⟨T, hT⟩ : C) ∈ e'.baseSet :=
    fun _ _ h => h
  let U : Set C := {T | ‖T.1 - ch.T‖ < ch.ε}
  have hU : IsPreconnected U := by
    have himg : Subtype.val '' U = C ∩ Metric.ball ch.T ch.ε := by
      ext T
      simp only [U, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        mem_inter_iff, Metric.mem_ball, dist_eq_norm]
      tauto
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
    exact (hconv.inter (convex_ball ch.T ch.ε)).isPreconnected
  have hcont : ContinuousOn (fun T : C => decide (PosRay e' T (o T))) U := by
    rintro ⟨T, hTC⟩ hT
    have := o.2.eventually_posRay_iff e' (hbase T hTC hT)
    have hev : ∀ᶠ T' in 𝓝 (⟨T, hTC⟩ : C), decide (PosRay e' ⟨T, hTC⟩ (o ⟨T, hTC⟩)) =
        decide (PosRay e' T' (o T')) :=
      this.mono fun T' hT' => (decide_eq_decide.2 hT').symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  have hU₀ : (⟨T₀, h₀⟩ : C) ∈ U := hε₀
  have hU₁ : (⟨T₁, h₁⟩ : C) ∈ U := hε₁
  have hconst := decide_eq_decide.1 (hU.constant hcont hU₀ hU₁)
  have hpos : ∀ T (hT : T ∈ C) (hb : Bijective T), ‖T - ch.T‖ < ch.ε →
      (PosRay e' ⟨T, hT⟩ (unitRay' hb) ↔ 0 < (chartDet ch hF0 T)⁻¹) := by
    intro T hT hb hTε
    refine (posRay_ray_iff e' (hbase _ _ hTε) (detUnit'_ne_zero hb)).trans ?_
    rw [← coord_detUnit'_eq ch (S := ⟨T, hC T hT⟩) hTε hb hF0]
    rfl
  have hne : ∀ T (hT : T ∈ C) (hb : Bijective T), ‖T - ch.T‖ < ch.ε →
      chartDet ch hF0 T ≠ 0 := fun T hT hb hTε =>
    chartDet_ne_zero ch (S := ⟨T, hC T hT⟩) hTε hb hF0
  have key : (0 < (chartDet ch hF0 T₀)⁻¹ ↔ 0 < (chartDet ch hF0 T₁)⁻¹) ↔
      0 < chartDet ch hF0 T₀ * chartDet ch hF0 T₁ := by
    rw [← mul_pos_iff_of_ne (inv_ne_zero (hne T₀ h₀ hb₀ hε₀)) (inv_ne_zero (hne T₁ h₁ hb₁ hε₁)),
      ← mul_inv, inv_pos]
  have i1 := (eq_iff_posRay_iff e' (hbase T₁ h₁ hε₁) (o ⟨T₁, h₁⟩) (unitRay' hb₁)).trans
    (iff_congr Iff.rfl (hpos T₁ h₁ hb₁ hε₁))
  have i0 := (eq_iff_posRay_iff e' (hbase T₀ h₀ hε₀) (o ⟨T₀, h₀⟩) (unitRay' hb₀)).trans
    (iff_congr Iff.rfl (hpos T₀ h₀ hb₀ hε₀))
  have fin : ∀ X₀ X₁ K₀ K₁ D : Prop, (X₀ ↔ X₁) → ((K₀ ↔ K₁) ↔ D) →
      ((X₁ ↔ K₁) ↔ ((X₀ ↔ K₀) ↔ D)) := by
    intro X₀ X₁ K₀ K₁ D h hk
    rw [← hk, h]
    by_cases hX : X₁ <;> by_cases h0 : K₀ <;> by_cases h1 : K₁ <;> simp [hX, h0, h1]
  exact i1.trans ((fin _ _ _ _ _ hconst key).trans (iff_congr i0.symm Iff.rfl))

/-- **Near an isomorphism the unit ray is locally constant**: in the chart with `P = id` centred
at an isomorphism `T₀ ∈ C` the coordinate of the unit is `1` at every isomorphism of the ball, so
`o` is the ray of the unit at an isomorphism `T₁ ∈ C` close to `T₀` iff it is at `T₀`. -/
theorem exists_ball_unitRay_iff {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    (hC : ∀ T ∈ C, T.IsFredholm) (o : LineOrientation (DetOn C hC)) {T₀ : E →L[ℝ] F}
    (h₀ : T₀ ∈ C) (hb₀ : Bijective T₀) :
    ∃ ε > 0, ∀ T₁ (h₁ : T₁ ∈ C) (hb₁ : Bijective T₁), ‖T₁ - T₀‖ < ε →
      (o ⟨T₁, h₁⟩ = unitRay' hb₁ ↔ o ⟨T₀, h₀⟩ = unitRay' hb₀) := by
  have hid : ((ContinuousLinearMap.id ℝ F) ∘L T₀ : E →L[ℝ] F) = T₀ :=
    ContinuousLinearMap.id_comp _
  have hP : IsGoodLeftProj T₀ (ContinuousLinearMap.id ℝ F) := by
    refine ⟨ContinuousLinearMap.id_comp _, finiteDimensional_coker_of_surjective
      (S := ContinuousLinearMap.id ℝ F) Function.surjective_id, ?_⟩
    rw [hid, LinearMap.range_eq_top.2 hb₀.2]
    exact (LinearMap.range_eq_top.2 Function.surjective_id).symm
  have hinj : Injective ((ContinuousLinearMap.id ℝ F) ∘L T₀ : E →L[ℝ] F) := by
    rw [hid]; exact hb₀.1
  have := finiteDimensional_ker_of_injective hinj
  obtain ⟨Y, hY⟩ := (Submodule.ClosedComplemented.of_finiteDimensional
    (LinearMap.ker (((ContinuousLinearMap.id ℝ F) ∘L T₀ : E →L[ℝ] F) : E →ₗ[ℝ] F))).exists_isTopCompl
  obtain ⟨ε, hε, h⟩ := lemma_6_5_1 hP hY
  let ch : LocalDetChart E F := ⟨T₀, hC T₀ h₀, ContinuousLinearMap.id ℝ F, hP, Y, hY, ε, hε,
    fun S hS => (h S hS).1, fun S hS => (h S hS).2⟩
  have hq : finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)) = 0 :=
    finrank_coker_of_surjective (T := ContinuousLinearMap.id ℝ F) Function.surjective_id
  have hF0 : finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)) = finrank ℝ ch.K :=
    hq.trans (finrank_ker_of_injective' hinj).symm
  have h1 : ∀ T, chartDet ch hF0 T = 1 := by
    intro T
    have : IsEmpty (Fin (finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)))) := by
      rw [hq]; infer_instance
    rw [chartDet, Basis.det_apply, Matrix.det_isEmpty]
  refine ⟨ε, hε, fun T₁ h₁ hb₁ hT₁ => ?_⟩
  have h00 : ‖T₀ - ch.T‖ < ch.ε := by
    change ‖T₀ - T₀‖ < ε
    rw [sub_self, norm_zero]; exact hε
  have key := ray_eq_unitRay_iff_chart ch hF0 hconv hC o h₀ h₁ hb₀ hb₁ h00 hT₁
  rw [h1, h1, mul_one] at key
  rw [key]
  simp

end Abstract

/-- A determinant of `q ∘ S₀ ∘ A` on a basis is `det A` times the one of `q ∘ S₀`. -/
theorem basis_det_comp_endo' {Q G V : Type*} [AddCommGroup Q] [Module ℝ Q] [AddCommGroup G]
    [Module ℝ G] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {m : ℕ}
    (B : Basis (Fin m) ℝ Q) (q : G →ₗ[ℝ] Q) {g : Fin m → V} (hg : LinearIndependent ℝ g)
    (hm : Fintype.card (Fin m) = finrank ℝ V) (S₀ : V →ₗ[ℝ] G) (A : V →ₗ[ℝ] V) :
    B.det (fun i => q (S₀ (A (g i)))) = LinearMap.det A * B.det (fun i => q (S₀ (g i))) := by
  set β := basisOfLinearIndependentOfCardEqFinrank' g hg hm
  have hβ : ⇑β = g := coe_basisOfLinearIndependentOfCardEqFinrank' g hg hm
  have key := alternatingMap_eq_det_smul (B.det.compLinearMap (q ∘ₗ S₀)) β (A ∘ β)
  simp only [AlternatingMap.compLinearMap_apply, Basis.det_comp, Basis.det_self, mul_one,
    smul_eq_mul] at key
  rw [hβ] at key
  exact key

section Block

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  (eT : E ≃L[ℝ] V × W) (eK : F ≃L[ℝ] V × W)

/-- **The block operator `A ⊕ id_W`**, read through `E ≅ V × W` and `F ≅ V × W`. -/
def blk (A : V →L[ℝ] V) : E →L[ℝ] F :=
  (eK.symm : V × W →L[ℝ] F) ∘L (A.prodMap (ContinuousLinearMap.id ℝ W)) ∘L
    (eT : E →L[ℝ] V × W)

@[simp] theorem blk_apply (A : V →L[ℝ] V) (x : E) :
    blk eT eK A x = eK.symm (A (eT x).1, (eT x).2) := rfl

theorem bijective_blk {A : V →L[ℝ] V} (hA : Bijective A) : Bijective (blk eT eK A) :=
  eK.symm.bijective.comp ((hA.prodMap bijective_id).comp eT.bijective)

theorem bijective_smul {A : V →L[ℝ] V} (hA : Bijective A) {s : ℝ} (hs : s ≠ 0) :
    Bijective (s • A) := by
  refine ⟨fun x y hxy => hA.1 ?_, fun y => ?_⟩
  · have h : s • A x = s • A y := hxy
    exact smul_right_injective V hs h
  · obtain ⟨x, hx⟩ := hA.2 (s⁻¹ • y)
    refine ⟨x, ?_⟩
    change s • A x = y
    rw [hx, smul_inv_smul₀ hs]

theorem norm_blk_sub_le (A A' : V →L[ℝ] V) :
    ‖blk eT eK A - blk eT eK A'‖ ≤
      ‖(eK.symm : V × W →L[ℝ] F)‖ * ‖A - A'‖ * ‖(eT : E →L[ℝ] V × W)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h : (blk eT eK A - blk eT eK A') x = eK.symm ((A - A') (eT x).1, 0) := by
    change blk eT eK A x - blk eT eK A' x = _
    rw [blk_apply, blk_apply, ← map_sub]
    congr 1
    ext <;> simp
  rw [h]
  have h1 : ‖(((A - A') (eT x).1, 0) : V × W)‖ ≤ ‖A - A'‖ * ‖(eT : E →L[ℝ] V × W)‖ * ‖x‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    calc ‖(A - A') (eT x).1‖ ≤ ‖A - A'‖ * ‖(eT x).1‖ := (A - A').le_opNorm _
      _ ≤ ‖A - A'‖ * ‖eT x‖ := by gcongr; exact norm_fst_le _
      _ ≤ ‖A - A'‖ * (‖(eT : E →L[ℝ] V × W)‖ * ‖x‖) := by
          gcongr; exact (eT : E →L[ℝ] V × W).le_opNorm x
      _ = _ := by ring
  calc ‖eK.symm ((A - A') (eT x).1, 0)‖
      ≤ ‖(eK.symm : V × W →L[ℝ] F)‖ * ‖(((A - A') (eT x).1, 0) : V × W)‖ :=
        (eK.symm : V × W →L[ℝ] F).le_opNorm _
    _ ≤ ‖(eK.symm : V × W →L[ℝ] F)‖ * (‖A - A'‖ * ‖(eT : E →L[ℝ] V × W)‖ * ‖x‖) := by
        gcongr
    _ = _ := by ring

theorem continuous_blk : Continuous (blk (F := F) (W := W) eT eK) := by
  refine (LipschitzWith.of_dist_le_mul (K := ‖(eK.symm : V × W →L[ℝ] F)‖₊ *
    ‖(eT : E →L[ℝ] V × W)‖₊) fun A A' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  calc ‖blk eT eK A - blk eT eK A'‖ ≤
      ‖(eK.symm : V × W →L[ℝ] F)‖ * ‖A - A'‖ * ‖(eT : E →L[ℝ] V × W)‖ := norm_blk_sub_le eT eK A A'
    _ = _ := by ring

theorem bijective_of_bijective_blk {A : V →L[ℝ] V} (hb : Bijective (blk eT eK A)) :
    Bijective A := by
  refine ⟨fun v v' h => ?_, fun y => ?_⟩
  · have h1 : blk eT eK A (eT.symm (v, 0)) = blk eT eK A (eT.symm (v', 0)) := by simp [h]
    have h2 := congrArg (fun x => (eT x).1) (hb.1 h1)
    simpa using h2
  · obtain ⟨x, hx⟩ := hb.2 (eK.symm (y, 0))
    refine ⟨(eT x).1, ?_⟩
    have h1 := congrArg (fun z => (eK z).1) hx
    simpa using h1

/-! ### The block chart -/

/-- The projection `(v, w) ↦ (0, w)` of `F ≅ V × W` onto its `W`-part. -/
def projW : F →L[ℝ] F :=
  (eK.symm : V × W →L[ℝ] F) ∘L ((0 : V →L[ℝ] V).prodMap (ContinuousLinearMap.id ℝ W)) ∘L
    (eK : F →L[ℝ] V × W)

@[simp] theorem projW_apply (y : F) : projW eK y = eK.symm (0, (eK y).2) := rfl

theorem range_projW : LinearMap.range (projW eK : F →ₗ[ℝ] F) =
    LinearMap.ker ((LinearMap.fst ℝ V W) ∘ₗ (eK : F →ₗ[ℝ] V × W)) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hy
    refine ⟨y, ?_⟩
    have hy' : (eK y).1 = 0 := hy
    apply eK.injective
    change eK (projW eK y) = eK y
    rw [projW_apply, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext hy'.symm rfl

/-- `F / R(P) ≅ V` for the projection `P` onto the `W`-part. -/
def cokerW : (F ⧸ LinearMap.range (projW eK : F →ₗ[ℝ] F)) ≃ₗ[ℝ] V :=
  (Submodule.quotEquivOfEq _ _ (range_projW eK)).trans
    (LinearMap.quotKerEquivOfSurjective ((LinearMap.fst ℝ V W) ∘ₗ (eK : F →ₗ[ℝ] V × W))
      fun v => ⟨eK.symm (v, 0), by simp⟩)

/-- The projection onto the `W`-part is a good left projection for every block operator. -/
theorem isGoodLeftProj_blk (A : V →L[ℝ] V) : IsGoodLeftProj (blk eT eK A) (projW eK) := by
  refine ⟨?_, (cokerW eK).symm.finiteDimensional, ?_⟩
  · ext y; simp
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨blk eT eK A x, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨eT.symm (0, (eK z).2), by simp⟩

theorem mem_ker_projW_blk (A : V →L[ℝ] V) (x : E) :
    x ∈ LinearMap.ker ((projW eK ∘L blk eT eK A : E →L[ℝ] F) : E →ₗ[ℝ] F) ↔ (eT x).2 = 0 := by
  simp

/-- `ker(P ∘ (A ⊕ id_W)) ≅ V`, `x ↦ (e_T x)_V`. -/
def kerW (A : V →L[ℝ] V) :
    LinearMap.ker ((projW eK ∘L blk eT eK A : E →L[ℝ] F) : E →ₗ[ℝ] F) ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective ((LinearMap.fst ℝ V W) ∘ₗ (eT : E →ₗ[ℝ] V × W) ∘ₗ
    (LinearMap.ker ((projW eK ∘L blk eT eK A : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype)
    ⟨fun a b hab => Subtype.ext (eT.injective (Prod.ext hab (by
        rw [(mem_ker_projW_blk eT eK A _).1 a.2, (mem_ker_projW_blk eT eK A _).1 b.2]))),
      fun v => ⟨⟨eT.symm (v, 0), (mem_ker_projW_blk eT eK A _).2 (by simp)⟩,
        show (eT (eT.symm (v, 0))).1 = v by simp⟩⟩

/-- **The determinant of a block operator in a block chart**: in a chart whose projection is the
projection onto the `W`-part and whose `ker(P T)` is the `V`-part of `E`, the determinant of
`k ↦ [(A ⊕ id_W) k(A ⊕ id_W)]` is `det A` times the one of the identity. -/
theorem chartDet_blk (ch : LocalDetChart E F) (hP : ∀ y, ch.P y = eK.symm (0, (eK y).2))
    (hK : ∀ x, x ∈ ch.K ↔ (eT x).2 = 0)
    (hF0 : finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)) = finrank ℝ ch.K)
    (A : V →L[ℝ] V) :
    chartDet ch hF0 (blk eT eK A) =
      LinearMap.det (A : V →ₗ[ℝ] V) * chartDet ch hF0 (blk eT eK (ContinuousLinearMap.id ℝ V)) := by
  have hker : ∀ B : V →L[ℝ] V, ∀ k ∈ ch.K, ch.kerMap (blk eT eK B) k = k := by
    intro B k hk
    have h0 : ch.projComp (blk eT eK B) k = 0 := by
      apply Subtype.ext
      rw [LocalDetChart.coe_projComp_apply, hP]
      simp [(hK k).1 hk]
    simp [LocalDetChart.kerMap, LocalDetChart.ySol, h0]
  set g : Fin (finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F))) → E :=
    fun i => (Module.finBasis ℝ ch.K (Fin.cast hF0 i) : E) with hg_def
  have hg : ∀ i, g i ∈ ch.K := fun i => (Module.finBasis ℝ ch.K (Fin.cast hF0 i)).2
  let f : ch.K →ₗ[ℝ] V := (LinearMap.fst ℝ V W) ∘ₗ (eT : E →ₗ[ℝ] V × W) ∘ₗ ch.K.subtype
  have hf : LinearMap.ker f = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun a b hab => Subtype.ext (eT.injective (Prod.ext hab ?_))
    rw [(hK a).1 a.2, (hK b).1 b.2]
  have hfs : Surjective f := fun w => ⟨⟨eT.symm (w, 0), (hK _).2 (by simp)⟩, by simp [f]⟩
  set v : Fin (finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F))) → V :=
    fun i => (eT (g i)).1 with hv_def
  have hv : LinearIndependent ℝ v :=
    ((Module.finBasis ℝ ch.K).linearIndependent.map' f hf).comp _ (Fin.cast_injective _)
  have hm : Fintype.card (Fin (finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)))) =
      finrank ℝ V := by
    rw [Fintype.card_fin, hF0]
    exact (LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.1 hf, hfs⟩).finrank_eq
  let S₀ : V →ₗ[ℝ] F := (eK.symm : V × W →ₗ[ℝ] F) ∘ₗ LinearMap.inl ℝ V W
  have hblkg : ∀ B : V →L[ℝ] V, ∀ i, blk eT eK B (ch.kerMap (blk eT eK B) (g i)) =
      S₀ (B (v i)) := by
    intro B i
    rw [hker B _ (hg i), blk_apply, (hK _).1 (hg i)]
    rfl
  have e1 : ∀ B : V →L[ℝ] V, chartDet ch hF0 (blk eT eK B) =
      (Module.finBasis ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F))).det
        (fun i => (LinearMap.range (ch.P : F →ₗ[ℝ] F)).mkQ (S₀ ((B : V →ₗ[ℝ] V) (v i)))) := by
    intro B
    unfold chartDet
    congr 1
    funext i
    exact congrArg (LinearMap.range (ch.P : F →ₗ[ℝ] F)).mkQ (hblkg B i)
  rw [e1, e1]
  exact basis_det_comp_endo' _ _ hv hm S₀ (A : V →ₗ[ℝ] V)

/-- Whether `o` is the ray of the unit at the block operator `A ⊕ id_W` (an isomorphism). -/
def UnitAt {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm} (o : LineOrientation (DetOn C hC))
    (hblk : ∀ A : V →L[ℝ] V, blk eT eK A ∈ C) (A : V →L[ℝ] V) : Prop :=
  ∃ hb : Bijective (blk eT eK A), o ⟨blk eT eK A, hblk A⟩ = unitRay' hb

theorem unitAt_iff {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
    (o : LineOrientation (DetOn C hC)) (hblk : ∀ A : V →L[ℝ] V, blk eT eK A ∈ C)
    {A : V →L[ℝ] V} (hb : Bijective (blk eT eK A)) :
    UnitAt eT eK o hblk A ↔ o ⟨blk eT eK A, hblk A⟩ = unitRay' hb :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hb, h⟩⟩

/-- **Scaling a block isomorphism**: along `λ ↦ λ A ⊕ id_W`, `λ ∈ [s, 1]`, all operators are
isomorphisms, so whether `o` is the ray of the unit does not change. -/
theorem unitAt_smul_iff {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    (hC : ∀ T ∈ C, T.IsFredholm) (o : LineOrientation (DetOn C hC))
    (hblk : ∀ A : V →L[ℝ] V, blk eT eK A ∈ C) {A : V →L[ℝ] V} (hA : Bijective A) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    UnitAt eT eK o hblk (s • A) ↔ UnitAt eT eK o hblk A := by
  classical
  let γ : ℝ → E →L[ℝ] F := fun l => blk eT eK (l • A)
  have hγ : Continuous γ := (continuous_blk eT eK).comp (continuous_id.smul continuous_const)
  have hcont : ContinuousOn (fun l : ℝ => decide (UnitAt eT eK o hblk (l • A))) (Icc s 1) := by
    intro l hl
    have hl0 : 0 < l := hs.trans_le hl.1
    have hbl := bijective_blk eT eK (bijective_smul hA hl0.ne')
    obtain ⟨ε, hε, hball⟩ := exists_ball_unitRay_iff hconv hC o (hblk (l • A)) hbl
    have h1 : ∀ᶠ l' in 𝓝 l, γ l' ∈ Metric.ball (γ l) ε :=
      hγ.continuousAt (Metric.ball_mem_nhds _ hε)
    have h2 : ∀ᶠ l' in 𝓝 l, 0 < l' := lt_mem_nhds hl0
    have hev : ∀ᶠ l' in 𝓝 l, decide (UnitAt eT eK o hblk (l • A)) =
        decide (UnitAt eT eK o hblk (l' • A)) := by
      filter_upwards [h1, h2] with l' h1' h2'
      have hbl' := bijective_blk eT eK (bijective_smul hA h2'.ne')
      rw [decide_eq_decide, unitAt_iff eT eK o hblk hbl, unitAt_iff eT eK o hblk hbl']
      rw [Metric.mem_ball, dist_eq_norm] at h1'
      exact (hball _ (hblk _) hbl' h1').symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  have := decide_eq_decide.1
    (isPreconnected_Icc.constant hcont ⟨le_rfl, hs1⟩ ⟨hs1, le_rfl⟩)
  rwa [one_smul] at this

/-- **Sign of an orientation of `DET` at two block isomorphisms**: for an orientation `o` of
`DET` over a convex set `C` of Fredholm operators `E → F` containing all block operators
`A ⊕ id_W` (read through `E ≅ V × W ≅ F`, `V` finite-dimensional) and two isomorphisms
`A₀, A₁` of `V`, `o` is the ray of the unit at `A₁ ⊕ id_W` iff (it is the ray of the unit at
`A₀ ⊕ id_W` iff `det A₀` and `det A₁` have the same sign). -/
theorem ray_eq_unitRay_iff_blk {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    (hC : ∀ T ∈ C, T.IsFredholm) (o : LineOrientation (DetOn C hC))
    (hblk : ∀ A : V →L[ℝ] V, blk eT eK A ∈ C) {A₀ A₁ : V →L[ℝ] V} (hb₀ : Bijective A₀)
    (hb₁ : Bijective A₁) :
    o ⟨blk eT eK A₁, hblk A₁⟩ = unitRay' (bijective_blk eT eK hb₁) ↔
      (o ⟨blk eT eK A₀, hblk A₀⟩ = unitRay' (bijective_blk eT eK hb₀) ↔
        0 < LinearMap.det (A₀ : V →ₗ[ℝ] V) * LinearMap.det (A₁ : V →ₗ[ℝ] V)) := by
  rw [← unitAt_iff eT eK o hblk, ← unitAt_iff eT eK o hblk]
  have hP := isGoodLeftProj_blk eT eK 0
  have := (hP.isFredholm_comp (hC _ (hblk 0))).finite_ker
  obtain ⟨Y, hY⟩ := (Submodule.ClosedComplemented.of_finiteDimensional
    (LinearMap.ker ((projW eK ∘L blk eT eK 0 : E →L[ℝ] F) : E →ₗ[ℝ] F))).exists_isTopCompl
  obtain ⟨ε, hε, h⟩ := lemma_6_5_1 hP hY
  let ch : LocalDetChart E F := ⟨blk eT eK 0, hC _ (hblk 0), projW eK, hP, Y, hY, ε, hε,
    fun S hS => (h S hS).1, fun S hS => (h S hS).2⟩
  have hK : ∀ x, x ∈ ch.K ↔ (eT x).2 = 0 := mem_ker_projW_blk eT eK 0
  have hF0 : finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)) = finrank ℝ ch.K :=
    (cokerW eK).finrank_eq.trans (kerW eT eK 0).finrank_eq.symm
  set K := ‖(eK.symm : V × W →L[ℝ] F)‖ * ‖(eT : E →L[ℝ] V × W)‖ with hK_def
  set X := K * (‖A₀‖ + ‖A₁‖) with hX_def
  have hX : 0 ≤ X := by positivity
  set s := ε / (X + ε) with hs_def
  have hXε : 0 < X + ε := by linarith
  have hs : 0 < s := div_pos hε hXε
  have hs1 : s ≤ 1 := (div_le_one hXε).2 (by linarith)
  have hsX : s * X < ε := by
    rw [hs_def, div_mul_eq_mul_div, div_lt_iff₀ hXε]
    nlinarith
  have hball : ∀ A : V →L[ℝ] V, ‖A‖ ≤ ‖A₀‖ + ‖A₁‖ → ‖blk eT eK (s • A) - ch.T‖ < ch.ε := by
    intro A hA
    change ‖blk eT eK (s • A) - blk eT eK 0‖ < ε
    calc ‖blk eT eK (s • A) - blk eT eK 0‖
        ≤ ‖(eK.symm : V × W →L[ℝ] F)‖ * ‖s • A - 0‖ * ‖(eT : E →L[ℝ] V × W)‖ :=
          norm_blk_sub_le eT eK _ _
      _ = s * (K * ‖A‖) := by
          rw [sub_zero, norm_smul, Real.norm_of_nonneg hs.le, hK_def]; ring
      _ ≤ s * X := by rw [hX_def]; gcongr
      _ < ε := hsX
  have hb₀' := bijective_smul hb₀ hs.ne'
  have hb₁' := bijective_smul hb₁ hs.ne'
  have hε₀ := hball A₀ (by linarith [norm_nonneg A₁])
  have hε₁ := hball A₁ (by linarith [norm_nonneg A₀])
  have key := ray_eq_unitRay_iff_chart ch hF0 hconv hC o (hblk (s • A₀)) (hblk (s • A₁))
    (bijective_blk eT eK hb₀') (bijective_blk eT eK hb₁') hε₀ hε₁
  rw [← unitAt_iff eT eK o hblk, ← unitAt_iff eT eK o hblk,
    unitAt_smul_iff eT eK hconv hC o hblk hb₁ hs hs1,
    unitAt_smul_iff eT eK hconv hC o hblk hb₀ hs hs1] at key
  rw [key]
  refine iff_congr Iff.rfl ?_
  have hPch : ∀ y, ch.P y = eK.symm (0, (eK y).2) := projW_apply eK
  have ht := chartDet_ne_zero ch (S := ⟨_, hC _ (hblk (s • A₀))⟩) hε₀
    (bijective_blk eT eK hb₀') hF0
  change chartDet ch hF0 (blk eT eK (s • A₀)) ≠ 0 at ht
  rw [chartDet_blk eT eK ch hPch hK hF0 (s • A₀), chartDet_blk eT eK ch hPch hK hF0 (s • A₁)]
  rw [chartDet_blk eT eK ch hPch hK hF0 (s • A₀)] at ht
  have ht₁ := right_ne_zero_of_mul ht
  simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  set n := finrank ℝ V
  set t := chartDet ch hF0 (blk eT eK (ContinuousLinearMap.id ℝ V))
  rw [show s ^ n * LinearMap.det (A₀ : V →ₗ[ℝ] V) * t * (s ^ n * LinearMap.det (A₁ : V →ₗ[ℝ] V) * t)
      = (s ^ n * t) ^ 2 * (LinearMap.det (A₀ : V →ₗ[ℝ] V) * LinearMap.det (A₁ : V →ₗ[ℝ] V))
      by ring]
  exact mul_pos_iff_of_pos_left (pow_pos (abs_pos.2 (mul_ne_zero (pow_ne_zero _ hs.ne') ht₁)) 2
    |>.trans_eq (sq_abs _))

end Block

section ConjUnit

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']

/-- **The determinant isomorphism of a conjugation of isomorphisms maps the unit to the unit**:
for `S' ∘ A = Γ ∘ S` with `S`, `S'` bijective, `conjDet (1 ⊗ 1*) = 1 ⊗ 1*`. -/
theorem conjDet_detUnit' (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F} {S' : E' →L[ℝ] F'}
    (h : ∀ v, S' (A v) = Γ (S v)) (hb : Bijective S) (hb' : Bijective S') :
    conjDet A Γ h (detUnit' hb) = detUnit' hb' := by
  have := finiteDimensional_ker_of_injective hb.1
  have := finiteDimensional_ker_of_injective hb'.1
  have := finiteDimensional_coker_of_surjective hb.2
  have := finiteDimensional_coker_of_surjective hb'.2
  unfold detUnit' conjDet
  rw [TensorProduct.congr_tmul, maxPowEquiv_emptyWedge _ _ (finrank_ker_of_injective' hb'.1)]
  congr 1
  rw [emptyWedge, maxPowDualEquiv_dualVec_symm _ linearIndependent_empty_type]
  congr 1

/-- The ray of the unit is carried to the ray of the unit. -/
theorem ray_map_conjDet_unitRay' (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F}
    {S' : E' →L[ℝ] F'} (h : ∀ v, S' (A v) = Γ (S v)) (hb : Bijective S) (hb' : Bijective S') :
    Module.Ray.map (conjDet A Γ h) (unitRay' hb) = unitRay' hb' := by
  rw [unitRay', Module.Ray.map_apply]
  exact rayOfNeZero_congr (conjDet_detUnit' A Γ h hb hb') _ _

end ConjUnit

section ChartPoint

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

variable {x : X} (p : ChartPoint B x) {hf : B.IsScFredholmSection f}

/-- **Positivity at an isomorphism is the ray of the unit**: `o` is positive at the isomorphism
`L ∈ Lin(f, x)` iff `o(L)` is the ray of `1 ⊗ 1* ∈ det L = λ(0) ⊗ λ*(0)`. -/
theorem isPos_iff_eq_unitRay' (o : p.Or f hf) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hb : Bijective L) : p.IsPos o L ↔ o ⟨L, hL⟩ = unitRay' hb := by
  have hN := p.map_ker_eq_bot hb.1
  rw [ChartPoint.isPos_iff hL hb.2 hN, ChartPoint.orKer]
  have hu : surjRay hb.2 p.T.subtypeL Subtype.val_injective hN (unitRay' hb) =
      emptyRay (⊥ : Submodule ℝ (p.c.φ.model.E 0)) (finrank_bot ℝ _) := by
    exact surjRay_unitRay' hb _ _ hN _
  exact (Eq.congr_right hu.symm).trans
    ((surjRay hb.2 p.T.subtypeL Subtype.val_injective hN).apply_eq_iff_eq)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **The sign of an orientation at two block isomorphisms**: for `T_zO ≅ V × W ≅ K_z` with `V`
finite-dimensional, block operators `A ⊕ id_W` in `Lin(f, x)` and isomorphisms `A₀`, `A₁` of `V`,
`o` is positive at `A₁ ⊕ id_W` iff (`o` is positive at `A₀ ⊕ id_W` iff `det A₀` and `det A₁`
have the same sign). -/
theorem isPos_iff_blk (o : p.Or f hf) (eT : ↥p.T ≃L[ℝ] V × W) (eK : ↥p.K ≃L[ℝ] V × W)
    (hblk : ∀ A : V →L[ℝ] V, blk eT eK A ∈ p.linSet f) {A₀ A₁ : V →L[ℝ] V}
    (hb₀ : Bijective A₀) (hb₁ : Bijective A₁) :
    p.IsPos o (blk eT eK A₁) ↔ (p.IsPos o (blk eT eK A₀) ↔
      0 < LinearMap.det (A₀ : V →ₗ[ℝ] V) * LinearMap.det (A₁ : V →ₗ[ℝ] V)) := by
  rw [isPos_iff_eq_unitRay' p o (hblk A₁) (bijective_blk eT eK hb₁),
    isPos_iff_eq_unitRay' p o (hblk A₀) (bijective_blk eT eK hb₀)]
  exact ray_eq_unitRay_iff_blk eT eK (p.convex_linSet hf) (p.isFredholm_of_mem_linSet hf) o
    hblk hb₀ hb₁

/-- Positivity at a second block isomorphism, given positivity at a first one: the determinants
have the same sign. -/
theorem isPos_iff_blk_of_isPos (o : p.Or f hf) (eT : ↥p.T ≃L[ℝ] V × W) (eK : ↥p.K ≃L[ℝ] V × W)
    (hblk : ∀ A : V →L[ℝ] V, blk eT eK A ∈ p.linSet f) {A₀ A₁ : V →L[ℝ] V}
    (hb₁ : Bijective A₁) (h₀ : p.IsPos o (blk eT eK A₀)) :
    p.IsPos o (blk eT eK A₁) ↔
      0 < LinearMap.det (A₀ : V →ₗ[ℝ] V) * LinearMap.det (A₁ : V →ₗ[ℝ] V) := by
  have hb₀ := bijective_of_bijective_blk eT eK (ChartPoint.IsPos.bijective h₀)
  rw [isPos_iff_blk p o eT eK hblk hb₀ hb₁]
  exact iff_true_left h₀

end ChartPoint

end Polyfold.Examples.Classical.Product
