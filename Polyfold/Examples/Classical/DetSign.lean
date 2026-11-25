import Polyfold.Examples.SignDimZeroPush

/-!
# The sign of an orientation at two isomorphisms, in finite dimensions

For an sc-Fredholm section `f`, a chart point `p` at `x` with `T_zO` and `K_z` finite-dimensional
and an orientation `o ∈ Or_x^f` of `DET(f, x)` over `Lin(f, x)` (Proposition 6.6.1 and
Definition 6.6.2, 2021 §6.6), positivity of `o` at two isomorphisms `L₀, L₁ ∈ Lin(f, x)`
(`ChartPoint.IsPos`, the ray of the empty wedge, 2021 pp. 701–702) agrees iff `det L₀` and
`det L₁` have the same sign in given bases.

The proof reads `o` in one chart of `DET(T_zO, K_z)`: in finite dimensions `P = 0` is a good
left projection for every operator, so there is a chart with `P = 0` whose ball contains the
segment `[L₀, L₁]`.  By formula (91) (`gammaProj_wedge_tmul`) the coordinate of the unit
`1 ⊗ 1* ∈ det S = λ(0) ⊗ λ*(0)` of an isomorphism `S` in this chart is the inverse of a
determinant of `S` in constant frames; the sign of an orientation in the chart is constant on the
convex set `Lin(f, x) ∩ ball`.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `isGoodLeftProj_zero`, `zeroChart`: the chart of `DET(E, F)` with `P = 0`, `Y = {0}` and any
  radius, for finite-dimensional `E`, `F`.
* `detUnit`, `unitRay`: the unit of `det S` and its ray, for an isomorphism `S`;
  `surjRay_unitRay`: it corresponds to the ray of the empty wedge.
* `coord_detUnit`: the coordinate of the unit in a chart is the inverse of the determinant of
  `k ↦ [S k]` in the frames of the chart.
* **`ray_eq_unitRay_iff`**: for an orientation of `DET` over a convex set `C` of operators
  between finite-dimensional spaces and isomorphisms `T₀, T₁ ∈ C`, `o(T₁)` is the unit ray iff
  (`o(T₀)` is the unit ray iff `0 < det T₀ · det T₁`).
* `isPos_iff_eq_unitRay`: `o` is positive at an isomorphism `L` iff `o(L)` is the unit ray.
* **`isPos_iff_det`**: `IsPos o L₁ ↔ (IsPos o L₀ ↔ 0 < det L₀ · det L₁)`;
  `isPos_iff_det_of_isPos`, `not_isPos_iff_det_of_isPos`: the forms with `IsPos o L₀` given.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Module Topology Function Bundle TensorProduct

noncomputable section

namespace Polyfold.Examples.Classical

section Abstract

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- In finite dimensions `P = 0` is a good left projection for every operator. -/
theorem isGoodLeftProj_zero (S : E →L[ℝ] F) : IsGoodLeftProj S (0 : F →L[ℝ] F) where
  isProj := by simp
  finite_coker := inferInstance
  range_comp := by
    rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.toLinearMap_zero,
      ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, LinearMap.range_zero]

theorem ker_zero_comp_eq_top (T : E →L[ℝ] F) :
    LinearMap.ker (((0 : F →L[ℝ] F) ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) = ⊤ := by
  ext; simp

instance subsingleton_range_zero : Subsingleton (LinearMap.range ((0 : F →L[ℝ] F) : F →ₗ[ℝ] F)) :=
  ⟨fun a b => by
    obtain ⟨_, x, hx⟩ := a
    obtain ⟨_, y, hy⟩ := b
    apply Subtype.ext
    simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply] at hx hy
    exact hx.symm.trans hy⟩

/-- **The chart with `P = 0`**: centre `T₀`, `Y = {0}` and any radius `ε > 0`. -/
def zeroChart {T₀ : E →L[ℝ] F} (hT₀ : T₀.IsFredholm) (ε : ℝ) (hε : 0 < ε) :
    LocalDetChart E F where
  T := T₀
  isFredholm := hT₀
  P := 0
  isGoodLeftProj := isGoodLeftProj_zero T₀
  Y := ⊥
  isTopCompl := by
    rw [ker_zero_comp_eq_top]
    exact Submodule.isTopCompl_top_bot
  ε := ε
  ε_pos := hε
  isGoodLeftProj_of_lt S _ := isGoodLeftProj_zero S
  exists_equiv_of_lt S _ :=
    ⟨(LinearEquiv.ofSubsingleton _ _).toContinuousLinearEquiv,
      ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _⟩

theorem finrank_ker_of_injective {S : E →L[ℝ] F} (hS : Injective S) :
    finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)) = 0 := by
  rw [LinearMap.ker_eq_bot.2 hS, finrank_bot]

/-- **The unit of `det S`** for an isomorphism `S`: `det S = λ(0) ⊗ λ*(0)` and the unit is the
empty wedge tensored with the dual of the empty wedge. -/
def detUnit {S : E →L[ℝ] F} (hS : Bijective S) : fredholmDet S :=
  emptyWedge _ (finrank_ker_of_injective hS.1) ⊗ₜ
    dualVec (emptyWedge _ (finrank_coker_of_surjective hS.2))

theorem detEquivOfSurjective_detUnit {S : E →L[ℝ] F} (hS : Bijective S) :
    detEquivOfSurjective hS.2 (detUnit hS) = emptyWedge _ (finrank_ker_of_injective hS.1) := by
  rw [detUnit, detEquivOfSurjective_tmul,
    dualVec_self finrank_maxPow (emptyWedge_ne_zero _ _), one_smul]

theorem detUnit_ne_zero {S : E →L[ℝ] F} (hS : Bijective S) : detUnit hS ≠ 0 := fun h =>
  emptyWedge_ne_zero _ (finrank_ker_of_injective hS.1)
    (by rw [← detEquivOfSurjective_detUnit hS, h, LinearEquiv.map_zero])

/-- The ray of the unit of `det S`, for an isomorphism `S`. -/
def unitRay {S : E →L[ℝ] F} (hS : Bijective S) : Module.Ray ℝ (fredholmDet S) :=
  rayOfNeZero ℝ _ (detUnit_ne_zero hS)

/-- `det S ≅ λ(ker S)` maps the ray of the unit to the ray of the empty wedge. -/
theorem map_detEquivOfSurjective_unitRay {S : E →L[ℝ] F} (hS : Bijective S) :
    Module.Ray.map (detEquivOfSurjective hS.2) (unitRay hS) =
      emptyRay _ (finrank_ker_of_injective hS.1) := by
  rw [unitRay, Module.Ray.map_apply]
  exact rayOfNeZero_congr (detEquivOfSurjective_detUnit hS) _ _

/-- `surjRay` maps the ray of the unit to the ray of the empty wedge. -/
theorem surjRay_unitRay {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {S : E →L[ℝ] F}
    (hS : Bijective S) (j : E →L[ℝ] V) (hj : Injective j) {N : Submodule ℝ V}
    (hN : (LinearMap.ker (S : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N) [FiniteDimensional ℝ N]
    (hN0 : finrank ℝ N = 0) :
    surjRay hS.2 j hj hN (unitRay hS) = emptyRay N hN0 := by
  rw [surjRay, Equiv.trans_apply, map_detEquivOfSurjective_unitRay hS]
  exact ray_map_maxPowEquiv_emptyRay _ _ _

/-- **The coordinate of the unit in a chart**: for an isomorphism `S` in the ball,
`γ^P_S(1 ⊗ 1*) = (k(S) ∧ …) ⊗ (S k(S) ∧ …)*` (formula (91)), so the coordinate is the inverse of
the determinant of `k ↦ [S k]` in the frames of the chart. -/
theorem coord_detUnit (c : LocalDetChart E F) {S : FredholmOp E F} (hS' : ‖S.1 - c.T‖ < c.ε)
    (hb : Bijective S.1)
    (h : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = finrank ℝ c.K) :
    c.coord S (detUnit hb) =
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
    (finrank_ker_of_injective hb.1).symm (d := Fin.elim0) linearIndependent_empty_type
    (finrank_coker_of_surjective hb.2).symm hb' hj (c := Fin.elim0) (fun i => i.elim0) hC
  rw [show detUnit hb = wedge (Fin.elim0 : Fin 0 → LinearMap.ker (S.1 : E →ₗ[ℝ] F))
      (finrank_ker_of_injective hb.1).symm ⊗ₜ dualVec (wedge
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

theorem zeroChart_kerMap {T₀ : E →L[ℝ] F} (hT₀ : T₀.IsFredholm) {ε : ℝ} (hε : 0 < ε)
    (S : E →L[ℝ] F) (x : E) : (zeroChart hT₀ ε hε).kerMap S x = x := by
  have h0 := (Submodule.mem_bot ℝ).1 ((zeroChart hT₀ ε hε).ySol_mem S x)
  change x + (zeroChart hT₀ ε hε).ySol S x = x
  rw [h0, add_zero]

/-- A determinant of `q ∘ S₀ ∘ A` on a basis is `det A` times the one of `q ∘ S₀`. -/
theorem basis_det_comp_endo {Q : Type*} [AddCommGroup Q] [Module ℝ Q] {m : ℕ}
    (B : Basis (Fin m) ℝ Q) (q : F →ₗ[ℝ] Q) {g : Fin m → E} (hg : LinearIndependent ℝ g)
    (hm : Fintype.card (Fin m) = finrank ℝ E) (S₀ : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) :
    B.det (fun i => q (S₀ (A (g i)))) = LinearMap.det A * B.det (fun i => q (S₀ (g i))) := by
  set β := basisOfLinearIndependentOfCardEqFinrank' g hg hm
  have hβ : ⇑β = g := coe_basisOfLinearIndependentOfCardEqFinrank' g hg hm
  have key := alternatingMap_eq_det_smul (B.det.compLinearMap (q ∘ₗ S₀)) β (A ∘ β)
  simp only [AlternatingMap.compLinearMap_apply, Basis.det_comp, Basis.det_self, mul_one,
    smul_eq_mul] at key
  rw [hβ] at key
  exact key

/-- The matrix of `S₀ ∘ A` in given bases has determinant `det(S₀) · det A`. -/
theorem det_toMatrix_comp {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (c : Basis ι ℝ F) (S₀ : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) :
    (LinearMap.toMatrix b c (S₀ ∘ₗ A)).det = (LinearMap.toMatrix b c S₀).det * LinearMap.det A := by
  rw [LinearMap.toMatrix_comp b b c, Matrix.det_mul, LinearMap.det_toMatrix]

/-- The matrix of an isomorphism in bases has a nonzero determinant. -/
theorem det_toMatrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E)
    (c : Basis ι ℝ F) (e : E ≃ₗ[ℝ] F) : (LinearMap.toMatrix b c (e : E →ₗ[ℝ] F)).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det
    (LinearMap.toMatrix_comp c b c (e : E →ₗ[ℝ] F) (e.symm : F →ₗ[ℝ] E))
  rw [Matrix.det_mul, h, zero_mul, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
    LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id, Matrix.det_one] at h1
  exact one_ne_zero h1

/-- **Sign of an orientation of `DET` over a convex set at two isomorphisms**: for an orientation
`o` of `DET` over a convex set `C` of operators between finite-dimensional spaces and two
isomorphisms `T₀, T₁ ∈ C`, `o` is the ray of the unit at `T₁` iff (it is the ray of the unit at
`T₀` iff the determinants of `T₀` and `T₁` in given bases have the same sign). -/
theorem ray_eq_unitRay_iff {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    (hC : ∀ T ∈ C, T.IsFredholm) (o : LineOrientation (DetOn C hC)) {T₀ T₁ : E →L[ℝ] F}
    (h₀ : T₀ ∈ C) (h₁ : T₁ ∈ C) (hb₀ : Bijective T₀) (hb₁ : Bijective T₁)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (c : Basis ι ℝ F) :
    o ⟨T₁, h₁⟩ = unitRay hb₁ ↔ (o ⟨T₀, h₀⟩ = unitRay hb₀ ↔
      0 < (LinearMap.toMatrix b c (T₀ : E →ₗ[ℝ] F)).det *
        (LinearMap.toMatrix b c (T₁ : E →ₗ[ℝ] F)).det) := by
  classical
  set ε := ‖T₁ - T₀‖ + 1 with hε_def
  have hε : 0 < ε := by positivity
  set ch := zeroChart (hC T₀ h₀) ε hε with hch
  have hmem : ch.pretriv ∈ (detPrebundle E F).pretrivializationAtlas := ⟨ch, rfl⟩
  let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas hmem
  have : e.IsLinear ℝ := (detPrebundle E F).linear_trivializationOfMemPretrivializationAtlas hmem
  let e' := e.pullback (fredholmIncl hC)
  have hbase : ∀ T (hT : T ∈ C), ‖T - T₀‖ < ε → (⟨T, hT⟩ : C) ∈ e'.baseSet :=
    fun _ _ h => h
  let U : Set C := {T | ‖T.1 - T₀‖ < ε}
  have hU : IsPreconnected U := by
    have himg : Subtype.val '' U = C ∩ Metric.ball T₀ ε := by
      ext T
      simp only [U, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        mem_inter_iff, Metric.mem_ball, dist_eq_norm]
      tauto
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
    exact (hconv.inter (convex_ball T₀ ε)).isPreconnected
  have hcont : ContinuousOn (fun T : C => decide (PosRay e' T (o T))) U := by
    rintro ⟨T, hTC⟩ hT
    have := o.2.eventually_posRay_iff e' (hbase T hTC hT)
    have hev : ∀ᶠ T' in 𝓝 (⟨T, hTC⟩ : C), decide (PosRay e' ⟨T, hTC⟩ (o ⟨T, hTC⟩)) =
        decide (PosRay e' T' (o T')) :=
      this.mono fun T' hT' => (decide_eq_decide.2 hT').symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  have hU₀ : (⟨T₀, h₀⟩ : C) ∈ U := by
    change ‖T₀ - T₀‖ < ε
    rw [sub_self, norm_zero]; exact hε
  have hU₁ : (⟨T₁, h₁⟩ : C) ∈ U := by
    change ‖T₁ - T₀‖ < ε
    linarith
  have hconst := decide_eq_decide.1 (hU.constant hcont hU₀ hU₁)
  have hF0 : finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)) = finrank ℝ ch.K := by
    change finrank ℝ (F ⧸ LinearMap.range ((0 : F →L[ℝ] F) : F →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker (((0 : F →L[ℝ] F) ∘L T₀ : E →L[ℝ] F) : E →ₗ[ℝ] F))
    rw [ker_zero_comp_eq_top, finrank_top, ContinuousLinearMap.toLinearMap_zero,
      LinearMap.range_zero, (Submodule.quotEquivOfEqBot _ rfl).finrank_eq,
      (LinearEquiv.ofBijective (T₀ : E →ₗ[ℝ] F) hb₀).finrank_eq]
  let g : Fin _ → E := fun i => (Module.finBasis ℝ ch.K (Fin.cast hF0 i) : E)
  let B := Module.finBasis ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F))
  let t : (E →L[ℝ] F) → ℝ := fun T => B.det (fun i => Submodule.Quotient.mk (T (g i)))
  have hpos : ∀ T (hT : T ∈ C) (hb : Bijective T), ‖T - T₀‖ < ε →
      (PosRay e' ⟨T, hT⟩ (unitRay hb) ↔ 0 < (t T)⁻¹) := by
    intro T hT hb hTε
    refine (posRay_ray_iff e' (hbase _ _ hTε) (detUnit_ne_zero hb)).trans ?_
    have key := coord_detUnit ch (S := ⟨T, hC T hT⟩) hTε hb hF0
    simp only [hch, zeroChart_kerMap] at key
    rw [← key]
    rfl
  have hne : ∀ T (hT : T ∈ C) (hb : Bijective T), ‖T - T₀‖ < ε → (t T)⁻¹ ≠ 0 := by
    intro T hT hb hTε
    have h1 := coord_ne_zero e' (hbase T hT hTε) (detUnit_ne_zero hb)
    have key := coord_detUnit ch (S := ⟨T, hC T hT⟩) hTε hb hF0
    simp only [hch, zeroChart_kerMap] at key
    rw [← key]
    exact h1
  -- the comparison `T₁ = T₀ ∘ A`
  set A : E →ₗ[ℝ] E := ((LinearEquiv.ofBijective (T₀ : E →ₗ[ℝ] F) hb₀).symm : F →ₗ[ℝ] E) ∘ₗ
    (T₁ : E →ₗ[ℝ] F) with hA_def
  have hA : ∀ x, T₀ (A x) = T₁ x := fun x =>
    (LinearEquiv.ofBijective (T₀ : E →ₗ[ℝ] F) hb₀).apply_symm_apply (T₁ x)
  have hg : LinearIndependent ℝ g :=
    ((Module.finBasis ℝ ch.K).linearIndependent.map' ch.K.subtype ch.K.ker_subtype).comp _
      (Fin.cast_injective _)
  have hm : Fintype.card (Fin (finrank ℝ (F ⧸ LinearMap.range (ch.P : F →ₗ[ℝ] F)))) =
      finrank ℝ E := by
    rw [Fintype.card_fin, hF0]
    change finrank ℝ (LinearMap.ker (((0 : F →L[ℝ] F) ∘L T₀ : E →L[ℝ] F) : E →ₗ[ℝ] F)) = _
    rw [ker_zero_comp_eq_top, finrank_top]
  have ht : t T₁ = LinearMap.det A * t T₀ := by
    refine Eq.trans ?_ (basis_det_comp_endo B (LinearMap.range (ch.P : F →ₗ[ℝ] F)).mkQ hg hm
      (T₀ : E →ₗ[ℝ] F) A)
    change B.det _ = B.det _
    congr 1
    funext i
    exact congrArg _ (hA (g i)).symm
  have hd : (LinearMap.toMatrix b c (T₁ : E →ₗ[ℝ] F)).det =
      (LinearMap.toMatrix b c (T₀ : E →ₗ[ℝ] F)).det * LinearMap.det A := by
    rw [← det_toMatrix_comp]
    congr 2
    exact LinearMap.ext fun x => (hA x).symm
  have hd₀ : (LinearMap.toMatrix b c (T₀ : E →ₗ[ℝ] F)).det ≠ 0 := by
    have := det_toMatrix_ne_zero b c (LinearEquiv.ofBijective (T₀ : E →ₗ[ℝ] F) hb₀)
    rwa [show ((LinearEquiv.ofBijective (T₀ : E →ₗ[ℝ] F) hb₀ : E ≃ₗ[ℝ] F) : E →ₗ[ℝ] F) =
      (T₀ : E →ₗ[ℝ] F) from LinearMap.ext fun x => rfl] at this
  have hsq : ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2 := fun x hx =>
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
  have ht₀ : t T₀ ≠ 0 := fun h => hne T₀ h₀ hb₀ hU₀ (by rw [h, inv_zero])
  have e1 : 0 < (LinearMap.toMatrix b c (T₀ : E →ₗ[ℝ] F)).det *
      (LinearMap.toMatrix b c (T₁ : E →ₗ[ℝ] F)).det ↔ 0 < LinearMap.det A := by
    rw [hd, ← mul_assoc, ← sq]
    exact mul_pos_iff_of_pos_left (hsq _ hd₀)
  have e2 : 0 < (t T₀)⁻¹ * (t T₁)⁻¹ ↔ 0 < LinearMap.det A := by
    rw [← mul_inv, inv_pos, ht, show t T₀ * (LinearMap.det A * t T₀) =
      t T₀ ^ 2 * LinearMap.det A by ring]
    exact mul_pos_iff_of_pos_left (hsq _ ht₀)
  have key := (mul_pos_iff_of_ne (hne T₀ h₀ hb₀ hU₀) (hne T₁ h₁ hb₁ hU₁)).symm.trans
    (e2.trans e1.symm)
  have i1 := (eq_iff_posRay_iff e' (hbase T₁ h₁ hU₁) (o ⟨T₁, h₁⟩) (unitRay hb₁)).trans
    (iff_congr Iff.rfl (hpos T₁ h₁ hb₁ hU₁))
  have i0 := (eq_iff_posRay_iff e' (hbase T₀ h₀ hU₀) (o ⟨T₀, h₀⟩) (unitRay hb₀)).trans
    (iff_congr Iff.rfl (hpos T₀ h₀ hb₀ hU₀))
  have fin : ∀ X₀ X₁ K₀ K₁ D : Prop, (X₀ ↔ X₁) → ((K₀ ↔ K₁) ↔ D) →
      ((X₁ ↔ K₁) ↔ ((X₀ ↔ K₀) ↔ D)) := by
    intro X₀ X₁ K₀ K₁ D h hk
    rw [← hk, h]
    by_cases hX : X₁ <;> by_cases h0 : K₀ <;> by_cases h1 : K₁ <;> simp [hX, h0, h1]
  exact i1.trans ((fin _ _ _ _ _ hconst key).trans (iff_congr i0.symm Iff.rfl))

end Abstract

section ChartPoint

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

variable {x : X} (p : ChartPoint B x) {hf : B.IsScFredholmSection f}

/-- **Positivity at an isomorphism is the ray of the unit**: `o` is positive at the isomorphism
`L ∈ Lin(f, x)` iff `o(L)` is the ray of `1 ⊗ 1* ∈ det L = λ(0) ⊗ λ*(0)`. -/
theorem isPos_iff_eq_unitRay (o : p.Or f hf) [FiniteDimensional ℝ ↥p.T]
    [FiniteDimensional ℝ ↥p.K] {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f)
    (hb : Bijective L) : p.IsPos o L ↔ o ⟨L, hL⟩ = unitRay hb := by
  have hN := p.map_ker_eq_bot hb.1
  rw [ChartPoint.isPos_iff hL hb.2 hN, ChartPoint.orKer]
  have hu : surjRay hb.2 p.T.subtypeL Subtype.val_injective hN (unitRay hb) =
      emptyRay (⊥ : Submodule ℝ (p.c.φ.model.E 0)) (finrank_bot ℝ _) := by
    exact surjRay_unitRay hb _ _ hN _
  exact (Eq.congr_right hu.symm).trans
    ((surjRay hb.2 p.T.subtypeL Subtype.val_injective hN).apply_eq_iff_eq)

/-- **The sign of an orientation at two isomorphisms, in finite dimensions**: for `T_zO` and
`K_z` finite-dimensional and two isomorphisms `L₀, L₁ ∈ Lin(f, x)`, `o` is positive at `L₁` iff
(`o` is positive at `L₀` iff the determinants of `L₀` and `L₁` in given bases have the same
sign). -/
theorem isPos_iff_det (o : p.Or f hf) [FiniteDimensional ℝ ↥p.T] [FiniteDimensional ℝ ↥p.K]
    {L₀ L₁ : ↥p.T →L[ℝ] ↥p.K} (hL₀ : L₀ ∈ p.linSet f) (hL₁ : L₁ ∈ p.linSet f)
    (hb₀ : Bijective L₀) (hb₁ : Bijective L₁) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ ↥p.T) (c : Basis ι ℝ ↥p.K) :
    p.IsPos o L₁ ↔ (p.IsPos o L₀ ↔
      0 < (LinearMap.toMatrix b c (L₀ : ↥p.T →ₗ[ℝ] ↥p.K)).det *
        (LinearMap.toMatrix b c (L₁ : ↥p.T →ₗ[ℝ] ↥p.K)).det) := by
  rw [isPos_iff_eq_unitRay p o hL₁ hb₁, isPos_iff_eq_unitRay p o hL₀ hb₀]
  exact ray_eq_unitRay_iff (p.convex_linSet hf) (p.isFredholm_of_mem_linSet hf) o hL₀ hL₁
    hb₀ hb₁ b c

/-- Positivity at a second isomorphism, given positivity at a first one: the determinants have
the same sign. -/
theorem isPos_iff_det_of_isPos (o : p.Or f hf) [FiniteDimensional ℝ ↥p.T]
    [FiniteDimensional ℝ ↥p.K] {L₀ L₁ : ↥p.T →L[ℝ] ↥p.K} (hL₁ : L₁ ∈ p.linSet f)
    (hb₁ : Bijective L₁) (h₀ : p.IsPos o L₀) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ ↥p.T) (c : Basis ι ℝ ↥p.K) :
    p.IsPos o L₁ ↔ 0 < (LinearMap.toMatrix b c (L₀ : ↥p.T →ₗ[ℝ] ↥p.K)).det *
      (LinearMap.toMatrix b c (L₁ : ↥p.T →ₗ[ℝ] ↥p.K)).det := by
  have hL₀ : L₀ ∈ p.linSet f := let ⟨h, _⟩ := h₀; h
  rw [isPos_iff_det p o hL₀ hL₁ (ChartPoint.IsPos.bijective h₀) hb₁ b c]
  exact iff_true_left h₀

/-- Given positivity at `L₀`, `o` is not positive at the isomorphism `L₁` iff the determinants of
`L₀` and `L₁` have opposite signs. -/
theorem not_isPos_iff_det_of_isPos (o : p.Or f hf) [FiniteDimensional ℝ ↥p.T]
    [FiniteDimensional ℝ ↥p.K] {L₀ L₁ : ↥p.T →L[ℝ] ↥p.K} (hL₁ : L₁ ∈ p.linSet f)
    (hb₁ : Bijective L₁) (h₀ : p.IsPos o L₀) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ ↥p.T) (c : Basis ι ℝ ↥p.K) :
    ¬ p.IsPos o L₁ ↔ (LinearMap.toMatrix b c (L₀ : ↥p.T →ₗ[ℝ] ↥p.K)).det *
      (LinearMap.toMatrix b c (L₁ : ↥p.T →ₗ[ℝ] ↥p.K)).det < 0 := by
  rw [isPos_iff_det_of_isPos p o hL₁ hb₁ h₀ b c, not_lt]
  have h0 := det_toMatrix_ne_zero b c
    (LinearEquiv.ofBijective (L₀ : ↥p.T →ₗ[ℝ] ↥p.K) (ChartPoint.IsPos.bijective h₀))
  have h1 := det_toMatrix_ne_zero b c (LinearEquiv.ofBijective (L₁ : ↥p.T →ₗ[ℝ] ↥p.K) hb₁)
  exact (le_iff_lt_or_eq).trans (or_iff_left (mul_ne_zero h0 h1))

end ChartPoint

end Polyfold.Examples.Classical
