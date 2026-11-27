import Polyfold.Chapter1.CylinderTestDensity

/-!
# The change of disc charts in `H^{k,δ}(ℝ × S¹)`, every `k`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7) and §3.1
(p. 66): the norms on the fibres of `W` and on `H^{3,δ₀}_c(S, u*TQ)` are finite sums of
semi-norms in disc charts, and the passage from one finite choice to another needs the
invariance of `H^k` under a change of disc charts.

* `ChartChange`: a compact set `K` in the open strip `ℝ × (0,1)` and a smooth map `ψ` of the
  plane, injective on `K` with invertible derivative there, mapping `K` into the open strip.
* `ChartChange.compMul b`: for `b` continuous with `tsupport b ⊆ K`, the operator
  `f ↦ b · (f ∘ ψ)` on `L²(ℝ × S¹)`.  It is well defined on classes and bounded, by the change
  of variables `ψ : K → ψ(K)` (`map_le_smul_cyl`: `ψ_*(vol|_K) ≤ C · cyl`).
* `ChartChange.op a k`: **for `a` smooth with `tsupport a ⊆ K`, `v ↦ a · (v ∘ ψ)` is a bounded
  operator `H^{k,δ}(ℝ × S¹) → H^{k,δ'}(ℝ × S¹)`, for every `k` and all weights `δ, δ' ≥ 0`.**
  On compact support the weights are bounded.  For a test function `φ`, the chain rule and the
  Leibniz rule write `∂^α (a · (φ ∘ ψ))` as a finite sum of terms `b · ((∂^β φ) ∘ ψ)`,
  `|β| ≤ |α|`, `b` smooth with `tsupport b ⊆ K` (`pD_ev`, the lists `steps`); classical and weak
  derivatives agree for smooth functions with compact support in the open strip
  (`hasWeakDeriv_of_supp`).  The identity of weak derivatives is closed in `v`, so it extends from
  the test functions (`dense_test`) to all of `H^{k,δ}`.
* `ChartChange.val_op`, `ChartChange.coeFn_op`: the operator on representatives, and
  `ChartChange.inclH_op`: it commutes with the inclusions of the levels.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-- The open strip `ℝ × (0,1)`, on which the cylinder `ℝ × S¹` is cut open. -/
def openStrip : Set (ℝ × ℝ) := univ ×ˢ Ioo 0 1

lemma cyl_eq_vol_restrict : cyl = (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioc 0 1) := by
  rw [cyl, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma openStrip_sub : openStrip ⊆ univ ×ˢ Ioc 0 1 :=
  prod_mono subset_rfl Ioo_subset_Ioc_self

lemma cyl_le_vol : cyl ≤ (volume : Measure (ℝ × ℝ)) := by
  rw [cyl_eq_vol_restrict]; exact Measure.restrict_le_self

/-- **A change of disc charts**: a compact `K` in the open strip, and a smooth `ψ` injective on
`K`, with invertible derivative on `K`, mapping `K` into the open strip. -/
structure ChartChange where
  K : Set (ℝ × ℝ)
  ψ : ℝ × ℝ → ℝ × ℝ
  isCompact : IsCompact K
  sub : K ⊆ openStrip
  smooth : ContDiff ℝ ∞ ψ
  injOn : InjOn ψ K
  det_ne : ∀ x ∈ K, (fderiv ℝ ψ x).det ≠ 0
  mapsTo : MapsTo ψ K openStrip

namespace ChartChange

variable (D : ChartChange)

lemma measurableSet_K : MeasurableSet D.K := D.isCompact.isClosed.measurableSet

lemma continuous_ψ : Continuous D.ψ := D.smooth.continuous

lemma measurable_ψ : Measurable D.ψ := D.continuous_ψ.measurable

/-! ## 1. The change of variables -/

lemma exists_det_lower : ∃ c > 0, ∀ x ∈ D.K, c ≤ |(fderiv ℝ D.ψ x).det| := by
  rcases D.K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  have hc : Continuous fun x => |(fderiv ℝ D.ψ x).det| :=
    (ContinuousLinearMap.continuous_det.comp (D.smooth.continuous_fderiv (by simp))).abs
  obtain ⟨x₀, hx₀, hmin⟩ := D.isCompact.exists_isMinOn h hc.continuousOn
  exact ⟨_, abs_pos.2 (D.det_ne x₀ hx₀), fun x hx => hmin hx⟩

/-- The constant of the change of variables. -/
def C : ℝ≥0∞ := ENNReal.ofReal (D.exists_det_lower.choose)⁻¹

lemma C_ne_top : D.C ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top

/-- The push-forward of Lebesgue measure on `K` under `ψ`. -/
def ν : Measure (ℝ × ℝ) := ((volume : Measure (ℝ × ℝ)).restrict D.K).map D.ψ

/-- **`ψ_*(vol|_K) ≤ C · cyl`**, by the change of variables formula on `K`. -/
theorem map_le_smul_cyl : D.ν ≤ D.C • cyl := by
  obtain ⟨hc0, hc⟩ := D.exists_det_lower.choose_spec
  set c := D.exists_det_lower.choose
  rw [Measure.le_iff]
  intro S hS
  rw [ν, Measure.map_apply D.measurable_ψ hS, Measure.smul_apply, smul_eq_mul]
  have hK := D.measurableSet_K
  have h1 : ((volume : Measure (ℝ × ℝ)).restrict D.K) (D.ψ ⁻¹' S) =
      ∫⁻ x in D.K, S.indicator 1 (D.ψ x) := by
    rw [← lintegral_indicator_one (D.measurable_ψ hS)]
    rfl
  have hder : ∀ x ∈ D.K, HasFDerivWithinAt D.ψ (fderiv ℝ D.ψ x) D.K x := fun x _ =>
    ((D.smooth.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt
  have h2 : ∫⁻ x in D.K, S.indicator 1 (D.ψ x) ≤
      ∫⁻ x in D.K, D.C * (ENNReal.ofReal |(fderiv ℝ D.ψ x).det| * S.indicator 1 (D.ψ x)) := by
    refine setLIntegral_mono' hK fun x hx => ?_
    rw [← mul_assoc]
    refine le_mul_of_one_le_left (by simp) ?_
    rw [C, ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le)]
    refine ENNReal.one_le_ofReal.2 ?_
    rw [inv_mul_eq_div, le_div_iff₀ hc0, one_mul]
    exact hc x hx
  rw [lintegral_const_mul' _ _ D.C_ne_top,
    ← lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK hder D.injOn] at h2
  have h3 : ∫⁻ y in D.ψ '' D.K, S.indicator 1 y ≤ cyl S := by
    rw [lintegral_indicator_one hS, Measure.restrict_apply hS, cyl_eq_vol_restrict,
      Measure.restrict_apply hS]
    refine measure_mono (inter_subset_inter_right _ ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact openStrip_sub (D.mapsTo hx)
  rw [h1]
  exact h2.trans (by gcongr)

lemma ν_ac : D.ν ≪ cyl :=
  (Measure.absolutelyContinuous_of_le_smul D.map_le_smul_cyl)

/-- Almost everywhere equal functions agree almost everywhere on `K` after composing with `ψ`. -/
lemma comp_ae {f f' : ℝ × ℝ → ℝ} (h : f =ᵐ[cyl] f') :
    ∀ᵐ x ∂cyl, x ∈ D.K → f (D.ψ x) = f' (D.ψ x) := by
  have h1 : ∀ᵐ y ∂D.ν, f y = f' y := D.ν_ac h
  have h2 : ∀ᵐ x ∂((volume : Measure (ℝ × ℝ)).restrict D.K), f (D.ψ x) = f' (D.ψ x) :=
    ae_of_ae_map D.continuous_ψ.aemeasurable h1
  rw [ae_restrict_iff' D.measurableSet_K] at h2
  exact Measure.AbsolutelyContinuous.ae_le (Measure.absolutelyContinuous_of_le cyl_le_vol) h2

/-! ## 2. The operators `f ↦ b · (f ∘ ψ)` on `L²` -/

variable {D}

lemma eq_zero_off {b : ℝ × ℝ → ℝ} (hb : tsupport b ⊆ D.K) {x : ℝ × ℝ} (hx : x ∉ D.K) :
    b x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hb h)

lemma comp_congr {b : ℝ × ℝ → ℝ} (hb : tsupport b ⊆ D.K) {f f' : ℝ × ℝ → ℝ}
    (h : f =ᵐ[cyl] f') :
    (fun x => b x * f (D.ψ x)) =ᵐ[cyl] fun x => b x * f' (D.ψ x) := by
  filter_upwards [D.comp_ae h] with x hx
  by_cases hK : x ∈ D.K
  · rw [hx hK]
  · simp [eq_zero_off hb hK]

lemma aesm_comp {b : ℝ × ℝ → ℝ} (hbc : Continuous b) (hb : tsupport b ⊆ D.K)
    {f : ℝ × ℝ → ℝ} (hf : AEStronglyMeasurable f cyl) :
    AEStronglyMeasurable (fun x => b x * f (D.ψ x)) cyl := by
  refine ⟨fun x => b x * hf.mk f (D.ψ x), hbc.stronglyMeasurable.mul
    (hf.stronglyMeasurable_mk.comp_measurable D.measurable_ψ), comp_congr hb hf.ae_eq_mk⟩

lemma exists_bound {b : ℝ × ℝ → ℝ} (hbc : Continuous b) (hb : tsupport b ⊆ D.K) :
    ∃ B, 0 ≤ B ∧ ∀ x, |b x| ≤ B := by
  have hcs : HasCompactSupport b := D.isCompact.of_isClosed_subset (isClosed_tsupport b) hb
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hbc
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩

/-- `‖b · (f ∘ ψ)‖_{L²} ≤ B C^{1/2} ‖f‖_{L²}`. -/
lemma eLpNorm_comp_le {b : ℝ × ℝ → ℝ} (hb : tsupport b ⊆ D.K) {B : ℝ}
    (hB : ∀ x, |b x| ≤ B) {f : ℝ × ℝ → ℝ} (hf : AEStronglyMeasurable f cyl) :
    eLpNorm (fun x => b x * f (D.ψ x)) 2 cyl ≤
      ENNReal.ofReal B * (D.C ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 cyl) := by
  have hsupp : (Function.support fun x => b x * f (D.ψ x)) ⊆ D.K := fun x hx => by
    by_contra hK
    exact hx (by simp [eq_zero_off hb hK])
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  have h1 : eLpNorm (fun x => b x * f (D.ψ x)) 2 (cyl.restrict D.K) ≤
      eLpNorm (fun x => b x * f (D.ψ x)) 2 ((volume : Measure (ℝ × ℝ)).restrict D.K) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono subset_rfl cyl_le_vol)
  have h2 : eLpNorm (fun x => b x * f (D.ψ x)) 2 ((volume : Measure (ℝ × ℝ)).restrict D.K) ≤
      ENNReal.ofReal B * eLpNorm (f ∘ D.ψ) 2 ((volume : Measure (ℝ × ℝ)).restrict D.K) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)) 2
  have h3 : eLpNorm (f ∘ D.ψ) 2 ((volume : Measure (ℝ × ℝ)).restrict D.K) =
      eLpNorm f 2 D.ν :=
    (eLpNorm_map_measure (hf.mono_ac D.ν_ac) D.continuous_ψ.aemeasurable).symm
  have h4 : eLpNorm f 2 D.ν ≤ eLpNorm f 2 (D.C • cyl) := eLpNorm_mono_measure _ D.map_le_smul_cyl
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num), smul_eq_mul] at h4
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := by rw [h3]; gcongr

lemma memLp_comp {b : ℝ × ℝ → ℝ} (hbc : Continuous b) (hb : tsupport b ⊆ D.K)
    {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 cyl) : MemLp (fun x => b x * f (D.ψ x)) 2 cyl := by
  obtain ⟨B, -, hB⟩ := exists_bound hbc hb
  refine ⟨aesm_comp hbc hb hf.1, (eLpNorm_comp_le hb hB hf.1).trans_lt ?_⟩
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ hf.2)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) D.C_ne_top

variable (D) in
open Classical in
/-- The constant of `compMul`. -/
def cB (b : ℝ × ℝ → ℝ) : ℝ := if h : Continuous b ∧ tsupport b ⊆ D.K then
  (exists_bound h.1 h.2).choose * (D.C ^ (1 / (2 : ℝ≥0∞)).toReal).toReal else 0

variable (D) in
open Classical in
/-- **`f ↦ b · (f ∘ ψ)` on `L²(ℝ × S¹)`**, for `b` continuous with `tsupport b ⊆ K` (and `0`
otherwise). -/
def compMul (b : ℝ × ℝ → ℝ) : Lp ℝ 2 cyl →L[ℝ] Lp ℝ 2 cyl :=
  if h : Continuous b ∧ tsupport b ⊆ D.K then
    LinearMap.mkContinuous
      { toFun := fun f => (memLp_comp h.1 h.2 (Lp.memLp f)).toLp _
        map_add' := fun f g => by
          rw [← MemLp.toLp_add]
          apply (MemLp.toLp_eq_toLp_iff _ _).2
          filter_upwards [comp_congr h.2 (Lp.coeFn_add f g)] with x hx
          simp only [hx, Pi.add_apply, mul_add]
        map_smul' := fun r f => by
          rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
          apply (MemLp.toLp_eq_toLp_iff _ _).2
          filter_upwards [comp_congr h.2 (Lp.coeFn_smul r f)] with x hx
          simp only [hx, Pi.smul_apply, smul_eq_mul]; ring }
      (D.cB b) (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [cB, dif_pos h, Lp.norm_toLp]
        obtain ⟨hB0, hB⟩ := (exists_bound h.1 h.2).choose_spec
        have := eLpNorm_comp_le h.2 hB (Lp.aestronglyMeasurable f)
        have hne : ENNReal.ofReal (exists_bound h.1 h.2).choose *
            (D.C ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 cyl) ≠ (⊤ : ℝ≥0∞) :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) D.C_ne_top) (Lp.eLpNorm_ne_top f))
        refine (ENNReal.toReal_mono hne this).trans_eq ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0, ← Lp.norm_def]
        ring)
  else 0

lemma coeFn_compMul {b : ℝ × ℝ → ℝ} (hbc : Continuous b) (hb : tsupport b ⊆ D.K)
    (f : Lp ℝ 2 cyl) : D.compMul b f =ᵐ[cyl] fun x => b x * f (D.ψ x) := by
  have h : Continuous b ∧ tsupport b ⊆ D.K := ⟨hbc, hb⟩
  rw [compMul, dif_pos h]
  exact MemLp.coeFn_toLp (memLp_comp hbc hb (Lp.memLp f))

/-! ## 3. Derivatives of `b · (φ ∘ ψ)` for smooth `φ` -/

/-- A term `b · ((∂_s^i ∂_t^j φ) ∘ ψ)`, recorded as `(b, i, j)`. -/
abbrev Term := (ℝ × ℝ → ℝ) × ℕ × ℕ

/-- `∑_{(b,i,j) ∈ L} b · ((∂_s^i ∂_t^j φ) ∘ ψ)`. -/
def ev (ψ : ℝ × ℝ → ℝ × ℝ) : List Term → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], _ => fun _ => 0
  | T :: L, φ => fun x => T.1 x * pD T.2.1 T.2.2 φ (ψ x) + ev ψ L φ x

/-- The derivative in the direction `w` of a sum of terms, by the chain and product rules:
`∂_w (b · (g ∘ ψ)) = (∂_w b) (g ∘ ψ) + b (∂_w ψ)₁ ((∂_s g) ∘ ψ) + b (∂_w ψ)₂ ((∂_t g) ∘ ψ)`. -/
def step (ψ : ℝ × ℝ → ℝ × ℝ) (w : ℝ × ℝ) : List Term → List Term
  | [] => []
  | T :: L => (fun x => fderiv ℝ T.1 x w, T.2.1, T.2.2) ::
      (fun x => T.1 x * (fderiv ℝ ψ x w).1, T.2.1 + 1, T.2.2) ::
      (fun x => T.1 x * (fderiv ℝ ψ x w).2, T.2.1, T.2.2 + 1) :: step ψ w L

/-- The terms have smooth coefficients supported in `K`, of order `≤ r`. -/
def Good (K : Set (ℝ × ℝ)) (r : ℕ) (L : List Term) : Prop :=
  ∀ T ∈ L, ContDiff ℝ ∞ T.1 ∧ tsupport T.1 ⊆ K ∧ T.2.1 + T.2.2 ≤ r

lemma contDiff_dir {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (w : ℝ × ℝ) :
    ContDiff ℝ ∞ fun x => fderiv ℝ b x w :=
  (hb.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma tsupport_dir_subset (b : ℝ × ℝ → ℝ) (w : ℝ × ℝ) :
    tsupport (fun x => fderiv ℝ b x w) ⊆ tsupport b := by
  refine (closure_mono fun x hx => ?_).trans (tsupport_fderiv_subset ℝ (f := b))
  intro h0
  exact hx (by simp only; rw [h0]; rfl)

lemma Good.step {K : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → ℝ × ℝ} (hψ : ContDiff ℝ ∞ ψ) (w : ℝ × ℝ) :
    ∀ {r : ℕ} {L : List Term}, Good K r L → Good K (r + 1) (step ψ w L)
  | _, [], _ => fun T hT => by simp [GWMemoir.ChartChange.step] at hT
  | r, T :: L, h => by
    obtain ⟨h1, h2, h3⟩ := h T (List.mem_cons_self ..)
    have hL := Good.step hψ w (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
    have hψw : ContDiff ℝ ∞ fun x => fderiv ℝ ψ x w :=
      (hψ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hψ1 : ContDiff ℝ ∞ fun x => (fderiv ℝ ψ x w).1 := contDiff_fst.comp hψw
    have hψ2 : ContDiff ℝ ∞ fun x => (fderiv ℝ ψ x w).2 := contDiff_snd.comp hψw
    intro T' hT'
    simp only [GWMemoir.ChartChange.step, List.mem_cons] at hT'
    rcases hT' with rfl | rfl | rfl | hT'
    · exact ⟨contDiff_dir h1 w, (tsupport_dir_subset _ w).trans h2, by simp only; omega⟩
    · exact ⟨h1.mul hψ1, (tsupport_mul_subset_left).trans h2, by simp only; omega⟩
    · exact ⟨h1.mul hψ2, (tsupport_mul_subset_left).trans h2, by simp only; omega⟩
    · exact hL T' hT'

lemma Good.mono {K : Set (ℝ × ℝ)} {r r' : ℕ} {L : List Term} (h : Good K r L) (hr : r ≤ r') :
    Good K r' L := fun T hT => ⟨(h T hT).1, (h T hT).2.1, (h T hT).2.2.trans hr⟩

lemma Ds_pD (φ : ℝ × ℝ → ℝ) (i j : ℕ) : Ds (pD i j φ) = pD (i + 1) j φ := by
  simp only [pD]; rw [Function.iterate_succ_apply']

lemma Dt_iterate_Ds {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) :
    ∀ i, Dt (Ds^[i] φ) = Ds^[i] (Dt φ)
  | 0 => rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ← Ds_Dt (contDiff_iterate_Ds h i), Dt_iterate_Ds h i]

lemma Dt_pD {φ : ℝ × ℝ → ℝ} (h : ContDiff ℝ ∞ φ) (i j : ℕ) : Dt (pD i j φ) = pD i (j + 1) φ := by
  simp only [pD]
  rw [Dt_iterate_Ds (contDiff_iterate_Dt h j), Function.iterate_succ_apply']

lemma fderiv_apply_eq {g : ℝ × ℝ → ℝ} (y w : ℝ × ℝ) :
    fderiv ℝ g y w = w.1 * Ds g y + w.2 * Dt g y := by
  have hw : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rfl

lemma contDiff_ev {ψ : ℝ × ℝ → ℝ × ℝ} (hψ : ContDiff ℝ ∞ ψ) {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ∀ {L : List Term}, (∀ T ∈ L, ContDiff ℝ ∞ T.1) →
      ContDiff ℝ ∞ (ev ψ L φ)
  | [], _ => contDiff_const
  | T :: _, h => ((h T (List.mem_cons_self ..)).mul ((contDiff_pD hφ _ _).comp hψ)).add
      (contDiff_ev hψ hφ fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

/-- **The derivative of a sum of terms is the sum of the stepped terms.** -/
lemma dir_ev {ψ : ℝ × ℝ → ℝ × ℝ} (hψ : ContDiff ℝ ∞ ψ) {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (w : ℝ × ℝ) : ∀ {L : List Term}, (∀ T ∈ L, ContDiff ℝ ∞ T.1) →
      (fun x => fderiv ℝ (ev ψ L φ) x w) = ev ψ (step ψ w L) φ
  | [], _ => by funext x; simp [ev, step]
  | T :: L, h => by
    funext x
    have hT := h T (List.mem_cons_self ..)
    have hL : ∀ T' ∈ L, ContDiff ℝ ∞ T'.1 := fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    have ih := congrFun (dir_ev hψ hφ w hL) x
    have hG : DifferentiableAt ℝ (pD T.2.1 T.2.2 φ) (ψ x) :=
      ((contDiff_pD hφ _ _).differentiable (by simp)) _
    have hd := ((hT.differentiable (by simp) x).hasFDerivAt.mul
      (hG.hasFDerivAt.comp x ((hψ.differentiable (by simp)) x).hasFDerivAt)).add
      ((contDiff_ev hψ hφ hL).differentiable (by simp) x).hasFDerivAt
    have e : ev ψ (T :: L) φ = fun y => T.1 y * pD T.2.1 T.2.2 φ (ψ y) + ev ψ L φ y := rfl
    rw [e, show (fun y => T.1 y * pD T.2.1 T.2.2 φ (ψ y) + ev ψ L φ y) =
      (T.1 * (pD T.2.1 T.2.2 φ ∘ ψ) + ev ψ L φ) from rfl, hd.fderiv]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Function.comp_apply]
    rw [ih, fderiv_apply_eq (ψ x) (fderiv ℝ ψ x w), Ds_pD, Dt_pD hφ]
    simp only [step, ev]
    ring

lemma smooth_of_good {K : Set (ℝ × ℝ)} {r : ℕ} {L : List Term} (h : Good K r L) :
    ∀ T ∈ L, ContDiff ℝ ∞ T.1 := fun T hT => (h T hT).1

/-- The terms of `∂_s^i ∂_t^j (b · (φ ∘ ψ))`. -/
def terms (ψ : ℝ × ℝ → ℝ × ℝ) (L : List Term) (i j : ℕ) : List Term :=
  (step ψ (1, 0))^[i] ((step ψ (0, 1))^[j] L)

lemma good_terms {K : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → ℝ × ℝ} (hψ : ContDiff ℝ ∞ ψ) {r : ℕ}
    {L : List Term} (h : Good K r L) (i j : ℕ) : Good K (r + (i + j)) (terms ψ L i j) := by
  have ht : ∀ j, Good K (r + j) ((step ψ (0, 1))^[j] L) := by
    intro j
    induction j with
    | zero => exact h
    | succ j ih => rw [Function.iterate_succ_apply']; exact ih.step hψ _
  have hs : ∀ i, Good K (r + j + i) ((step ψ (1, 0))^[i] ((step ψ (0, 1))^[j] L)) := by
    intro i
    induction i with
    | zero => exact ht j
    | succ i ih => rw [Function.iterate_succ_apply']; exact ih.step hψ _
  exact (hs i).mono (by omega)

/-- **`∂_s^i ∂_t^j` of a sum of terms**, for smooth `φ`. -/
theorem pD_ev {K : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → ℝ × ℝ} (hψ : ContDiff ℝ ∞ ψ) {φ : ℝ × ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {r : ℕ} {L : List Term} (h : Good K r L) (i j : ℕ) :
    pD i j (ev ψ L φ) = ev ψ (terms ψ L i j) φ := by
  have ht : ∀ j, Dt^[j] (ev ψ L φ) = ev ψ ((step ψ (0, 1))^[j] L) φ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact dir_ev hψ hφ _ (smooth_of_good (good_terms hψ h 0 j))
  have hs : ∀ i, Ds^[i] (ev ψ ((step ψ (0, 1))^[j] L) φ) = ev ψ (terms ψ L i j) φ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [terms]
      rw [Function.iterate_succ_apply']
      exact dir_ev hψ hφ _ (smooth_of_good (good_terms hψ h i j))
  simp only [pD]; rw [ht, hs]

lemma ev_eq_zero_off {K : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → ℝ × ℝ} {φ : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ K) : ∀ {L : List Term}, (∀ T ∈ L, tsupport T.1 ⊆ K) → ev ψ L φ x = 0
  | [], _ => rfl
  | T :: _, h => by
    simp only [ev]
    rw [image_eq_zero_of_notMem_tsupport fun h' => hx (h T (List.mem_cons_self ..) h'), zero_mul,
      zero_add, ev_eq_zero_off hx fun T' hT' => h T' (List.mem_cons_of_mem _ hT')]

lemma tsupport_ev_subset {K : Set (ℝ × ℝ)} (hK : IsClosed K) (ψ : ℝ × ℝ → ℝ × ℝ)
    (φ : ℝ × ℝ → ℝ) {L : List Term} (h : ∀ T ∈ L, tsupport T.1 ⊆ K) :
    tsupport (ev ψ L φ) ⊆ K :=
  closure_minimal (fun _x hx => by_contra fun hK' => hx (ev_eq_zero_off hK' h)) hK

/-! ## 4. Weak and classical derivatives with compact support in the open strip -/

lemma integral_cyl_eq_vol {K : Set (ℝ × ℝ)} (hK : K ⊆ openStrip) {g : ℝ × ℝ → ℝ}
    (hg : ∀ x ∉ K, g x = 0) : ∫ x, g x ∂cyl = ∫ x, g x := by
  rw [cyl_eq_vol_restrict]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    hg x fun h => hx (openStrip_sub (hK h))

/-- Integration by parts against a test function, for `F` smooth with compact support in the
open strip. -/
lemma ibp_dir {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (hK : K ⊆ openStrip) {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hFK : tsupport F ⊆ K) (w : ℝ × ℝ) {θ : ℝ × ℝ → ℝ} (hθ : IsTest θ) :
    ∫ x, F x * fderiv ℝ θ x w ∂cyl = -∫ x, fderiv ℝ F x w * θ x ∂cyl := by
  have hcs : HasCompactSupport F := hKc.of_isClosed_subset (isClosed_tsupport F) hFK
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hθd : Differentiable ℝ θ := hθ.smooth.differentiable (by simp)
  have hθ' : Continuous fun x => fderiv ℝ θ x w := (contDiff_dir hθ.smooth w).continuous
  have hF' : Continuous fun x => fderiv ℝ F x w := (contDiff_dir hF w).continuous
  have z1 : ∀ x ∉ K, F x * fderiv ℝ θ x w = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hFK h), zero_mul]
  have z2 : ∀ x ∉ K, fderiv ℝ F x w * θ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ F x w)
      fun h => hx (hFK (tsupport_dir_subset F w h)), zero_mul]
  rw [integral_cyl_eq_vol hK z1, integral_cyl_eq_vol hK z2]
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hFd x) (fun x _ => hθd x)
  · exact (hF'.mul hθ.smooth.continuous).integrable_of_hasCompactSupport
      ((hcs.fderiv_apply (𝕜 := ℝ) w).mul_right)
  · exact (hFd.continuous.mul hθ').integrable_of_hasCompactSupport hcs.mul_right
  · exact (hFd.continuous.mul hθ.smooth.continuous).integrable_of_hasCompactSupport
      hcs.mul_right

/-- **Classical derivatives are weak derivatives** for smooth functions with compact support in
the open strip. -/
theorem hasWeakDeriv_of_supp {K : Set (ℝ × ℝ)} (hKc : IsCompact K) (hK : K ⊆ openStrip)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFK : tsupport F ⊆ K) (a b : ℕ) :
    HasWeakDeriv a b F (pD a b F) := by
  have hsupp : ∀ a b, tsupport (pD a b F) ⊆ K := by
    have ht : ∀ b, tsupport (Dt^[b] F) ⊆ K := by
      intro b
      induction b with
      | zero => exact hFK
      | succ b ih => rw [Function.iterate_succ_apply']; exact (tsupport_dir_subset _ _).trans ih
    intro a b
    induction a with
    | zero => exact ht b
    | succ a ih => rw [← Ds_pD]; exact (tsupport_dir_subset _ _).trans ih
  have hs : ∀ G : ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → tsupport G ⊆ K → HasWeakDeriv 1 0 G (Ds G) := by
    intro G hG hGK θ hθ
    simp only [pD, Function.iterate_one, Function.iterate_zero, id]
    simp only [Ds]
    rw [ibp_dir hKc hK hG hGK _ hθ]; simp
  have htt : ∀ G : ℝ × ℝ → ℝ, ContDiff ℝ ∞ G → tsupport G ⊆ K → HasWeakDeriv 0 1 G (Dt G) := by
    intro G hG hGK θ hθ
    simp only [pD, Function.iterate_one, Function.iterate_zero, id]
    simp only [Dt]
    rw [ibp_dir hKc hK hG hGK _ hθ]; simp
  have h0 : ∀ b, HasWeakDeriv 0 b F (pD 0 b F) := by
    intro b
    induction b with
    | zero => exact hasWeakDeriv_zero F
    | succ b ih =>
      have e : pD 0 (b + 1) F = Dt (pD 0 b F) := by
        simp only [pD, Function.iterate_zero, id]; rw [Function.iterate_succ_apply']
      rw [e]; exact ih.succ_t (htt _ (contDiff_pD hF 0 b) (hsupp 0 b))
  induction a with
  | zero => exact h0 b
  | succ a ih => rw [← Ds_pD]; exact ih.succ_s (hs _ (contDiff_pD hF a b) (hsupp a b))

/-! ## 5. The operator on `H^{k,δ}` -/

variable {k : ℕ} {δ δ' : ℝ} {hδ : 0 ≤ δ}

variable (k hδ) in
/-- `u ↦ ∂_s^i ∂_t^j u` on `H^{k,δ}`, and `0` if `i + j > k`. -/
def dvAt (i j : ℕ) : H k hδ →L[ℝ] Lp ℝ 2 cyl :=
  if h : i + j ≤ k then dvCLM k hδ ⟨(i, j), mem_idx.2 h⟩ else 0

lemma coeFn_dvAt {i j : ℕ} (h : i + j ≤ k) (u : H k hδ) :
    dvAt k hδ i j u =ᵐ[cyl] dv (H.toSub u) ⟨(i, j), mem_idx.2 h⟩ := by
  rw [dvAt, dif_pos h]; exact coeFn_dvCLM _ u

lemma dvAt_toH {i j : ℕ} (h : i + j ≤ k) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    dvAt k hδ i j (toH k hδ hφ) =ᵐ[cyl] pD i j φ := by
  refine (coeFn_dvAt h _).trans (dv_unique _ _ ?_ ((hφ.pD i j).memLp 2))
  exact (hφ.smPer.hasWeakDeriv i j).congr_ae (hφ.memLp 2).coeFn_toLp.symm (ae_eq_refl _)

variable (D k hδ) in
/-- The terms `b · ((∂^{(i,j)} u) ∘ ψ)` summed, on `H^{k,δ}`. -/
def evL : List Term → H k hδ →L[ℝ] Lp ℝ 2 cyl
  | [] => 0
  | T :: L => (D.compMul T.1).comp (dvAt k hδ T.2.1 T.2.2) + evL L

/-- The coefficients are continuous and supported in `K`. -/
def CGood (K : Set (ℝ × ℝ)) (L : List Term) : Prop := ∀ T ∈ L, Continuous T.1 ∧ tsupport T.1 ⊆ K

lemma Good.cgood {K : Set (ℝ × ℝ)} {r : ℕ} {L : List Term} (h : Good K r L) : CGood K L :=
  fun T hT => ⟨(h T hT).1.continuous, (h T hT).2.1⟩

lemma evL_toH {r : ℕ} (hr : r ≤ k) {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) :
    ∀ {L : List Term}, Good D.K r L → evL D k hδ L (toH k hδ hφ) =ᵐ[cyl] ev D.ψ L φ
  | [], _ => by
    change ((0 : H k hδ →L[ℝ] Lp ℝ 2 cyl) (toH k hδ hφ) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun _ => 0
    rw [_root_.zero_apply]; exact Lp.coeFn_zero ℝ 2 cyl
  | T :: L, h => by
    obtain ⟨h1, h2, h3⟩ := h T (List.mem_cons_self ..)
    have ih := evL_toH hr hφ (L := L) fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    simp only [evL, ev]
    filter_upwards [Lp.coeFn_add (D.compMul T.1 (dvAt k hδ T.2.1 T.2.2 (toH k hδ hφ)))
      (evL D k hδ L (toH k hδ hφ)),
      coeFn_compMul h1.continuous h2 (dvAt k hδ T.2.1 T.2.2 (toH k hδ hφ)),
      comp_congr h2 (dvAt_toH (hδ := hδ) (by omega : T.2.1 + T.2.2 ≤ k) hφ), ih]
      with x e1 e2 e3 e4
    rw [_root_.add_apply, ContinuousLinearMap.comp_apply, e1, Pi.add_apply, e2, e3,
      e4]

variable (δ') in
/-- The coefficients multiplied by the weight `e^{δ'|s|}`. -/
def wtL (L : List Term) : List Term := L.map fun T => (fun x => wt δ' x * T.1 x, T.2)

lemma CGood.wtL {K : Set (ℝ × ℝ)} {L : List Term} (h : CGood K L) : CGood K (wtL δ' L) := by
  intro T hT
  obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
  exact ⟨(continuous_wt δ').mul (h T₀ hT₀).1, (tsupport_mul_subset_right).trans (h T₀ hT₀).2⟩

lemma evL_wtL : ∀ {L : List Term}, CGood D.K L → ∀ u : H k hδ,
    evL D k hδ (wtL δ' L) u =ᵐ[cyl] fun x => wt δ' x * evL D k hδ L u x
  | [], _, u => by
    simp only [wtL, List.map_nil, evL]
    filter_upwards [Lp.coeFn_zero ℝ 2 cyl] with x hx
    rw [_root_.zero_apply, hx]; simp
  | T :: L, h, u => by
    obtain ⟨h1, h2⟩ := h T (List.mem_cons_self ..)
    have hL : CGood D.K L := fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    have ih := evL_wtL hL u
    have hw : Continuous (fun x => wt δ' x * T.1 x) := (continuous_wt δ').mul h1
    have hwK : tsupport (fun x => wt δ' x * T.1 x) ⊆ D.K := (tsupport_mul_subset_right).trans h2
    have e : wtL δ' (T :: L) = (fun x => wt δ' x * T.1 x, T.2) :: wtL δ' L := rfl
    rw [e]
    simp only [evL]
    filter_upwards [Lp.coeFn_add (D.compMul (fun x => wt δ' x * T.1 x)
      (dvAt k hδ T.2.1 T.2.2 u)) (evL D k hδ (wtL δ' L) u),
      Lp.coeFn_add (D.compMul T.1 (dvAt k hδ T.2.1 T.2.2 u)) (evL D k hδ L u),
      coeFn_compMul hw hwK (dvAt k hδ T.2.1 T.2.2 u), coeFn_compMul h1 h2 (dvAt k hδ T.2.1 T.2.2 u),
      ih] with x e1 e2 e3 e4 e5
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply] at e1 e2 ⊢
    rw [e1, e2, Pi.add_apply, Pi.add_apply, e3, e4, e5]; ring

variable (a : ℝ × ℝ → ℝ)

/-- The single term `a · (u ∘ ψ)`. -/
def L0 : List Term := [(a, 0, 0)]

lemma good_L0 {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) :
    Good D.K 0 (L0 a) := by
  intro T hT
  simp only [L0, List.mem_singleton] at hT
  subst hT
  exact ⟨ha, haK, le_rfl⟩

variable {a}

/-- **The weak derivatives of `a · (u ∘ ψ)`**: `∂^{(i,j)} (a · (u ∘ ψ))` is the sum of the terms
`terms ψ (L0 a) i j` applied to `u`, for every `u ∈ H^{k,δ}` and `i + j ≤ k`. -/
theorem hasWeakDeriv_evL (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) {i j : ℕ}
    (hij : i + j ≤ k) (u : H k hδ) :
    HasWeakDeriv i j (evL D k hδ (L0 a) u) (evL D k hδ (terms D.ψ (L0 a) i j) u) := by
  have hG := good_terms D.smooth (good_L0 (D := D) ha haK) i j
  rw [zero_add] at hG
  set S := {u : H k hδ | HasWeakDeriv i j (evL D k hδ (L0 a) u)
    (evL D k hδ (terms D.ψ (L0 a) i j) u)}
  have hS : IsClosed S := by
    have e : S = ⋂ θ : {θ : ℝ × ℝ → ℝ // IsTest θ}, {u : H k hδ |
        pairing (pD i j θ.1) ((θ.2.pD i j).memLp 2) (evL D k hδ (L0 a) u) =
          (-1) ^ (i + j) * pairing θ.1 (θ.2.memLp 2) (evL D k hδ (terms D.ψ (L0 a) i j) u)} := by
      ext u
      simp only [S, mem_ofPred_eq, mem_iInter, pairing_apply, HasWeakDeriv, Subtype.forall]
    rw [e]
    exact isClosed_iInter fun θ => isClosed_eq (by fun_prop) (by fun_prop)
  have hT : {u : H k hδ | ∃ φ, ∃ hφ : IsTest φ, u = toH k hδ hφ} ⊆ S := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hF := contDiff_ev D.smooth hφ.smooth (smooth_of_good (good_L0 (D := D) ha haK))
    have hFK := tsupport_ev_subset D.isCompact.isClosed D.ψ φ
      (fun T hT => ((good_L0 (D := D) ha haK) T hT).2.1)
    have hw := hasWeakDeriv_of_supp D.isCompact D.sub hF hFK i j
    rw [pD_ev D.smooth hφ.smooth (good_L0 (D := D) ha haK)] at hw
    exact hw.congr_ae (evL_toH (Nat.zero_le k) hφ (good_L0 (D := D) ha haK)).symm
      (evL_toH hij hφ hG).symm
  have := closure_minimal hT hS
  rw [(dense_test k hδ).closure_eq] at this
  exact this (mem_univ u)

lemma memH_evL (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) (hδ' : 0 ≤ δ') (u : H k hδ) :
    evL D k hδ (L0 a) u ∈ Hsub k hδ' := fun i j hij =>
  ⟨_, hasWeakDeriv_evL ha haK hij u,
    (Lp.memLp (evL D k hδ (wtL δ' (terms D.ψ (L0 a) i j)) u)).ae_eq
      (evL_wtL (good_terms D.smooth (good_L0 (D := D) ha haK) i j).cgood u)⟩

/-- `wdv` of the operator, as a bounded operator in `u`. -/
lemma wdv_evL (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) (hδ' : 0 ≤ δ') (u : H k hδ)
    (p : idx k) :
    wdv (⟨evL D k hδ (L0 a) u, memH_evL ha haK hδ' u⟩ : Hsub k hδ') p =
      evL D k hδ (wtL δ' (terms D.ψ (L0 a) p.1.1 p.1.2)) u := by
  have hG := (good_terms D.smooth (good_L0 (D := D) ha haK) p.1.1 p.1.2).cgood
  refine Lp.ext ?_
  have hd := dv_unique (⟨evL D k hδ (L0 a) u, memH_evL ha haK hδ' u⟩ : Hsub k hδ') p
    (hasWeakDeriv_evL ha haK (mem_idx.1 p.2) u) (Lp.memLp _)
  filter_upwards [coeFn_wdv (⟨evL D k hδ (L0 a) u, memH_evL ha haK hδ' u⟩ : Hsub k hδ') p, hd,
    evL_wtL hG u] with x h1 h2 h3
  rw [h1, h2, h3]

variable (D k hδ) in
/-- **The change of disc charts on `H^{k,δ}`**: `u ↦ a · (u ∘ ψ)`, for `a` smooth with
`tsupport a ⊆ K`, bounded `H^{k,δ}(ℝ × S¹) → H^{k,δ'}(ℝ × S¹)`, for every `k`. -/
def op (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) (hδ' : 0 ≤ δ') : H k hδ →L[ℝ] H k hδ' :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u => (⟨evL D k hδ (L0 a) u, memH_evL ha haK hδ' u⟩ : Hsub k hδ')
      map_add' := fun u v => Subtype.ext (map_add (evL D k hδ (L0 a)) u v)
      map_smul' := fun c u => Subtype.ext (map_smul (evL D k hδ (L0 a)) c u) }
    ⟨∑ p : idx k, ‖evL D k hδ (wtL δ' (terms D.ψ (L0 a) p.1.1 p.1.2))‖, fun u => by
      refine (norm_H_le_sum (hδ := hδ') _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun p _ => ?_
      change ‖wdv (⟨evL D k hδ (L0 a) u, memH_evL ha haK hδ' u⟩ : Hsub k hδ') p‖ ≤ _
      rw [wdv_evL ha haK hδ' u p]
      exact ContinuousLinearMap.le_opNorm _ _⟩

lemma evL_L0 (u : H k hδ) :
    evL D k hδ (L0 a) u = D.compMul a (H.val u) := by
  have e : evL D k hδ (L0 a) u = D.compMul a (dvAt k hδ 0 0 u) + 0 := rfl
  rw [e, add_zero, dvAt, dif_pos (Nat.zero_le k)]
  congr 1
  exact (val_eq_dvCLM u).symm

/-- The operator on the underlying `L²` classes: `a · (u ∘ ψ)`. -/
theorem val_op (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) (hδ' : 0 ≤ δ') (u : H k hδ) :
    H.val (op D k hδ ha haK hδ' u) = D.compMul a (H.val u) :=
  evL_L0 u

theorem coeFn_op (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) (hδ' : 0 ≤ δ') (u : H k hδ) :
    (H.val (op D k hδ ha haK hδ' u) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => a x * H.val u (D.ψ x) := by
  rw [val_op]; exact coeFn_compMul ha.continuous haK _

/-- The operators on different levels agree on the inclusions. -/
theorem inclH_op {k' : ℕ} {δ₁ δ₁' : ℝ} {hδ₁ : 0 ≤ δ₁} (ha : ContDiff ℝ ∞ a)
    (haK : tsupport a ⊆ D.K) (hδ' : 0 ≤ δ') (hδ₁' : 0 ≤ δ₁') (hk : k ≤ k') (hd : δ ≤ δ₁)
    (hd' : δ' ≤ δ₁') (u : H k' hδ₁) :
    inclH hδ' hδ₁' hk hd' (op D k' hδ₁ ha haK hδ₁' u) =
      op D k hδ ha haK hδ' (inclH hδ hδ₁ hk hd u) := by
  apply valCLM_injective
  rw [valCLM_inclH, valCLM_apply, valCLM_apply]
  change H.val _ = H.val _
  rw [val_op, val_op]
  congr 1

end ChartChange

end GWMemoir
