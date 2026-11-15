import Polyfold.Chapter9.DimensionJumpBranched

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), gap G.110: the integrals of the branched
ep⁺-subgroupoid `Θ(t, z) = δ₀(z)` of `ℤ/3 ⋉ X`.

# `∮_Θ̂ df = (1/3)(φ(1) − φ(−1))` and the two readings of `∮_{∂Θ̂} f`

## The text, paraphrased
(p. 452) For `f(t, z) = φ(t)`, `♯G^eff_{(t,0)} = 3` on `M = [−1, 1] × {0}` gives
`∮_Θ̂ df = (1/3)(φ(1) − φ(−1))`.  At `x ∈ ∂X = {(−1, 0), (1, 0)}` the effective isotropy is
`ℤ/3` read in `X` and trivial read in `∂X`; with the weights of `X` the boundary integral is
`(1/3)(φ(1) − φ(−1))`, as Stokes' theorem requires, with those of `∂X` it is `φ(1) − φ(−1)`.

## What is formalized
In the namespace `Polyfold.DimensionJump`.
* `gM`, `M_mem_sheets`: one graph chart of `M` (the coordinate `u = p₀ − p₁` of
  `p = arcPt t`), so `M` and its open pieces are sheets of the class of §9.5.
* `R1`, `R2`: natural representations at `(∓1, 0)` on the invariant connected open sets
  `U₁ = {u > −1}`, `U₂ = {u < 1}`; `beta1 + beta2 = 1`, sc-smooth, constant on orbits,
  `supp β_k ⊆ U_k`.
* `boundaryStratum_M = {(−1, 0), (1, 0)}`; the boundary orientation of `M` is negative at
  `(−1, 0)` and positive at `(1, 0)` (`frames_boundaryOp_xm`, `frames_boundaryOp_x₀`).
* **`remark_9_5_20_integral`**: `∮_Θ̂ da = (1/3)(a(1, 0) − a(−1, 0))` for every
  `a ∈ Ω⁰_{ep,∞}`, for the effective branched integral `tameBranchedIntegralEff` of
  Definition 9.5.6; computed with the local formula of Theorem 9.5.5 on `U₁`, `U₂`
  (`stokes_one_structure_all`), without partitions of unity.
* **`remark_9_5_20_boundary`**: the effective boundary measure of Theorem 9.5.16 (weights of
  `X`) gives `∮_{∂Θ̂} a = (1/3)(a(1, 0) − a(−1, 0))`; **`remark_9_5_20_stokes`**: the two agree.
* **`remark_9_5_20_boundary_weights`**: the boundary sum with the weights of `X` is
  `(1/3)(a(1, 0) − a(−1, 0))`, with those of the ep-groupoid `∂X` (`DimensionJump.εB`) it is
  `a(1, 0) − a(−1, 0)`.
* `fForm`, **`remark_9_5_20_df`**: the `0`-forms `f(t, z) = φ(t)`, `φ(t) = ψ(u(t))` for
  smooth `ψ`, and `∮_Θ̂ df = (1/3)(φ(1) − φ(−1))`; **`remark_9_5_20_nondegenerate`**: for
  `ψ = id` the value is `−4/3`, the reading in `∂X` gives `−4`.
* `exists_contDiff_comp_eq`, **`remark_9_5_20_df_of_contDiffOn`**: every `φ` smooth on an open
  `U ⊇ [−1, 1]` is `φ_ψ` on `[−1, 1]` for a smooth `ψ` (`ψ = χ · (φ' ∘ τ)`, `τ` the inverse
  of `u` by `arccos`), so `∮_Θ̂ df = (1/3)(φ(1) − φ(−1))` for `f(t, z) = φ(t)`.
* **`isSmoothSubmanifold_boundary`**: `∂X` is a smooth submanifold of `X` (Definition 4.2.1).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule MeasureTheory
open scoped ContDiff Real

noncomputable section

namespace Polyfold

namespace DimensionJump

open DimensionJump
open ScOneExample hiding E

open RemarkFourThree MPolyfold EpGroupoid EpGroupoid.Examples

/-! ### The coordinate `u = p₀ − p₁` -/

/-- `p ↦ p₀ − p₁` on `ℝ²`. -/
def ell2 : V2 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

@[simp] lemma ell2_apply (p : V2) : ell2 p = p 0 - p 1 := rfl

/-- The sc-operator `(p, a, b) ↦ p₀ − p₁`. -/
def ellOp : ScOperator E (ScBanach.const ℝ) :=
  (ScOperator.ofConst ell2).comp ((ScBanach.const V2).prodFstOp Z2)

lemma ellOp_apply (q : E 0) : ellOp 0 q = ell2 q.1 := rfl

/-- **The coordinate `u(t, z) = p₀ − p₁` of `p = arcPt t`**, decreasing from `2` (`t = −1`) to
`−2` (`t = 1`). -/
def gco (y : XR) : ℝ := ell2 (chart y).1

lemma gco_eq (y : XR) : gco y = ell2 (arcPt y.1.1) := rfl

theorem isScSmoothMap_gco : P.IsScSmoothMap realPolyfold gco := by
  refine isScSmoothMap_real_of_local fun x => ⟨chart, univ, isChart_chart, isOpen_univ,
    mem_univ x, subset_univ _, ?_⟩
  have himg : chart '' univ = O := himg_chart
  rw [himg]
  have key : IsScSmoothRetractMap E (quadrant 2 Z2 0) O (ScBanach.const ℝ) univ univ (ellOp 0) :=
    ellOp.isScSmoothRetractMap Rt.isScRetract (mapsTo_univ _ _)
  refine key.congr fun q hq => ?_
  obtain ⟨x, -, rfl⟩ := himg.symm ▸ hq
  change ellOp 0 (chart x) = gco (chart.symm (chart x))
  rw [chart.symm_apply_apply (mem_univ x)]
  rfl

lemma gco_smul (k : Z3) (y : XR) : gco (k • y) = gco y := rfl

lemma continuous_gco : Continuous gco :=
  continuousOn_univ.1 isScSmoothMap_gco.continuousOn

/-- `u(t) = 2 cos θ − 2 sin θ` is decreasing on `[−1, 1]`. -/
lemma ell2_arcPt_anti {t t' : ℝ} (ht : t ∈ Icc (-1) 1) (ht' : t' ∈ Icc (-1) 1) (h : t ≤ t') :
    ell2 (arcPt t') ≤ ell2 (arcPt t) := by
  have h1 := θ_mem ht
  have h2 := θ_mem ht'
  have hθ : θ t ≤ θ t' := by unfold θ; gcongr
  have hc : Real.cos (θ t') ≤ Real.cos (θ t) :=
    Real.cos_le_cos_of_nonneg_of_le_pi h1.1 (by linarith [h2.2, Real.pi_pos]) hθ
  have hs : Real.sin (θ t) ≤ Real.sin (θ t') :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [h1.1, Real.pi_pos]) h2.2 hθ
  simp only [ell2_apply, arcPt, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-! ### Natural representations on invariant connected neighbourhoods of points of `M` -/

/-- **A natural representation at `x ∈ M`** on an invariant connected open `U ∋ x`: every
`k ∈ ℤ/3` fixes `x`, `Φ(g) = k • ·` and `Γ(g)(y) = (k, y)`. -/
def natRepM {x : XR} (hx : x ∈ Mset) {U : Set XR} (hU : IsOpen U) (hc : IsConnected U)
    (hxU : x ∈ U) (hinv : ∀ (k : Z3) (y : XR), y ∈ U → k • y ∈ U) : ε.NaturalRep x where
  U := U
  isOpen_U := hU
  isConnected_U := hc
  mem_U := hxU
  Φ g y := g.val.1 • y
  Γ g y := (g.val.1, y)
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (isScSmoothMap_smul _).mono hU (subset_univ _)
      isScSmoothOn_inv := (isScSmoothMap_smul _).mono hU (subset_univ _)
      mapsTo := fun y hy => hinv _ y hy
      mapsTo_inv := fun y hy => hinv _ y hy
      left_inv := fun y _ => inv_smul_smul g.val.1 y
      right_inv := fun y _ => smul_inv_smul g.val.1 y }
  Φ_mul g h y _ := mul_smul g.val.1 h.val.1 y
  isScSmoothOn_Γ g := (isScSmoothMap_sheet g.val.1).mono hU (subset_univ _)
  Γ_self g := Prod.ext rfl g.src_val.symm
  src_Γ _ _ _ := rfl
  tgt_Γ _ _ _ := rfl
  existsUnique_Γ h _ _ := by
    refine ⟨⟨(h.1, x), rfl, smul_eq_self_of_snd_eq_zero h.1 hx⟩, rfl, fun g hg => ?_⟩
    have hg' : ((g.val.1, h.2) : Z3 × XR) = h := hg
    have h1 := congrArg Prod.fst hg'
    have h2 : g.val = (h.1, x) := Prod.ext h1 g.src_val
    exact GroupoidStr.Isotropy.ext h2

/-- The end point `(−1, 0)`. -/
def xm : XR := ⟨(-1, 0), mem_Xs_iff.2 (Or.inl rfl)⟩

lemma xm_mem_M : xm ∈ Mset := rfl

lemma x₀_mem_M : x₀ ∈ Mset := rfl

lemma gco_xm : gco xm = 2 := by
  rw [gco_eq]
  change ell2 (arcPt (-1)) = 2
  rw [arcPt_neg_one]; simp

lemma gco_x₀ : gco x₀ = -2 := by
  rw [gco_eq]
  change ell2 (arcPt 1) = -2
  rw [arcPt_one]; simp

/-- `U₁ = {u > −1}`, an invariant open neighbourhood of `(−1, 0)` not containing `(1, 0)`. -/
def U1 : Set XR := {y | -1 < gco y}

/-- `U₂ = {u < 1}`, an invariant open neighbourhood of `(1, 0)` not containing `(−1, 0)`. -/
def U2 : Set XR := {y | gco y < 1}

lemma isOpen_U1 : IsOpen U1 := isOpen_lt continuous_const continuous_gco

lemma isOpen_U2 : IsOpen U2 := isOpen_lt continuous_gco continuous_const

lemma xm_mem_U1 : xm ∈ U1 := by change -1 < gco xm; rw [gco_xm]; norm_num

lemma x₀_mem_U2 : x₀ ∈ U2 := by change gco x₀ < 1; rw [gco_x₀]; norm_num

lemma x₀_not_mem_U1 : x₀ ∉ U1 := by change ¬ (-1 < gco x₀); rw [gco_x₀]; norm_num

lemma xm_not_mem_U2 : xm ∉ U2 := by change ¬ (gco xm < 1); rw [gco_xm]; norm_num

/-- The segment from `(−1, 0)` to `(t, z)`. -/
def segL (y : ℝ × ℂ) (s : ℝ) : ℝ × ℂ := (-1 + s * (y.1 + 1), (s : ℂ) * y.2)

/-- The segment from `(1, 0)` to `(t, z)`. -/
def segR (y : ℝ × ℂ) (s : ℝ) : ℝ × ℂ := (1 - s * (1 - y.1), (s : ℂ) * y.2)

lemma segL_mem {y : XR} (hy : y ∈ U1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : segL y.1 s ∈ Xs := by
  rcases mem_Xs_iff.1 y.2 with h | h | h
  · rw [segL, h]; refine mem_Xs_iff.2 (Or.inl ?_); simp
  · exfalso
    have : y = x₀ := Subtype.ext h
    exact x₀_not_mem_U1 (this ▸ hy)
  · rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [segL, ← h0]; simp only [zero_mul, add_zero, Complex.ofReal_zero]
      exact mem_Xs_iff.2 (Or.inl rfl)
    · refine mem_Xs_iff.2 (Or.inr (Or.inr ⟨⟨?_, ?_⟩, ?_⟩))
      · have : 0 < s * (y.1.1 + 1) := mul_pos h0 (by linarith [h.1.1])
        change -1 < -1 + s * (y.1.1 + 1); linarith
      · change -1 + s * (y.1.1 + 1) < 1
        nlinarith [h.1.1, h.1.2, hs.2]
      · change ‖(s : ℂ) * y.1.2‖ < 1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
        have := h.2
        nlinarith [norm_nonneg y.1.2, hs.2]

lemma segR_mem {y : XR} (hy : y ∈ U2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : segR y.1 s ∈ Xs := by
  rcases mem_Xs_iff.1 y.2 with h | h | h
  · exfalso
    have : y = xm := Subtype.ext h
    exact xm_not_mem_U2 (this ▸ hy)
  · rw [segR, h]; refine mem_Xs_iff.2 (Or.inr (Or.inl ?_)); simp
  · rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [segR, ← h0]; simp only [zero_mul, sub_zero, Complex.ofReal_zero]
      exact mem_Xs_iff.2 (Or.inr (Or.inl rfl))
    · refine mem_Xs_iff.2 (Or.inr (Or.inr ⟨⟨?_, ?_⟩, ?_⟩))
      · change -1 < 1 - s * (1 - y.1.1)
        nlinarith [h.1.1, h.1.2, hs.2]
      · have : 0 < s * (1 - y.1.1) := mul_pos h0 (by linarith [h.1.2])
        change 1 - s * (1 - y.1.1) < 1; linarith
      · change ‖(s : ℂ) * y.1.2‖ < 1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
        have := h.2
        nlinarith [norm_nonneg y.1.2, hs.2]

lemma continuous_segL (y : ℝ × ℂ) : Continuous (segL y) := by
  unfold segL; fun_prop

lemma continuous_segR (y : ℝ × ℂ) : Continuous (segR y) := by
  unfold segR; fun_prop

lemma isConnected_U1 : IsConnected U1 := by
  refine ⟨⟨xm, xm_mem_U1⟩, isPreconnected_of_forall xm fun y hy => ?_⟩
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  let f : Icc (0 : ℝ) 1 → XR := fun s => ⟨segL y.1 s.1, segL_mem hy s.2⟩
  have hf : Continuous f :=
    Continuous.subtype_mk ((continuous_segL y.1).comp continuous_subtype_val) _
  refine ⟨range f, ?_, ⟨⟨0, by norm_num, by norm_num⟩, ?_⟩,
    ⟨⟨1, by norm_num, by norm_num⟩, ?_⟩, isPreconnected_range hf⟩
  · rintro _ ⟨s, rfl⟩
    have ht := fst_mem_Icc_of_mem y.2
    have hle : -1 + s.1 * (y.1.1 + 1) ≤ y.1.1 := by nlinarith [s.2.1, s.2.2, ht.1]
    have hmem : -1 + s.1 * (y.1.1 + 1) ∈ Icc (-1 : ℝ) 1 := fst_mem_Icc_of_mem (segL_mem hy s.2)
    change -1 < ell2 (arcPt (-1 + s.1 * (y.1.1 + 1)))
    exact lt_of_lt_of_le hy (ell2_arcPt_anti hmem ht hle)
  · refine Subtype.ext ?_
    change segL y.1 0 = (-1, 0)
    simp [segL]
  · refine Subtype.ext ?_
    change segL y.1 1 = y.1
    simp [segL]

lemma isConnected_U2 : IsConnected U2 := by
  refine ⟨⟨x₀, x₀_mem_U2⟩, isPreconnected_of_forall x₀ fun y hy => ?_⟩
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  let f : Icc (0 : ℝ) 1 → XR := fun s => ⟨segR y.1 s.1, segR_mem hy s.2⟩
  have hf : Continuous f :=
    Continuous.subtype_mk ((continuous_segR y.1).comp continuous_subtype_val) _
  refine ⟨range f, ?_, ⟨⟨0, by norm_num, by norm_num⟩, ?_⟩,
    ⟨⟨1, by norm_num, by norm_num⟩, ?_⟩, isPreconnected_range hf⟩
  · rintro _ ⟨s, rfl⟩
    have ht := fst_mem_Icc_of_mem y.2
    have hle : y.1.1 ≤ 1 - s.1 * (1 - y.1.1) := by nlinarith [s.2.1, s.2.2, ht.2]
    have hmem : 1 - s.1 * (1 - y.1.1) ∈ Icc (-1 : ℝ) 1 := fst_mem_Icc_of_mem (segR_mem hy s.2)
    change ell2 (arcPt (1 - s.1 * (1 - y.1.1))) < 1
    exact lt_of_le_of_lt (ell2_arcPt_anti ht hmem hle) hy
  · refine Subtype.ext ?_
    change segR y.1 0 = (1, 0)
    simp [segR]
  · refine Subtype.ext ?_
    change segR y.1 1 = y.1
    simp [segR]

lemma smul_mem_U1 (k : Z3) (y : XR) (hy : y ∈ U1) : k • y ∈ U1 := by
  change -1 < gco (k • y); rw [gco_smul]; exact hy

lemma smul_mem_U2 (k : Z3) (y : XR) (hy : y ∈ U2) : k • y ∈ U2 := by
  change gco (k • y) < 1; rw [gco_smul]; exact hy

/-- The natural representation at `(−1, 0)` on `U₁`. -/
def R1 : ε.NaturalRep xm := natRepM xm_mem_M isOpen_U1 isConnected_U1 xm_mem_U1 smul_mem_U1

/-- The natural representation at `(1, 0)` on `U₂`. -/
def R2 : ε.NaturalRep x₀ := natRepM x₀_mem_M isOpen_U2 isConnected_U2 x₀_mem_U2 smul_mem_U2

/-! ### The cut-offs `β₁ + β₂ = 1` -/

/-- `σ(u) = 0` for `u ≤ −1/2`, `= 1` for `u ≥ 1/2`. -/
def sig (u : ℝ) : ℝ := Real.smoothTransition (u + 1 / 2)

lemma contDiff_sig : ContDiff ℝ ∞ sig :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

lemma contDiff_one_sub_sig : ContDiff ℝ ∞ fun u => 1 - sig u :=
  contDiff_const.sub contDiff_sig

/-- `β₁ = σ ∘ u`, supported in `U₁`, `= 1` near `(−1, 0)`. -/
def beta1 (y : XR) : ℝ := sig (gco y)

/-- `β₂ = (1 − σ) ∘ u`, supported in `U₂`, `= 1` near `(1, 0)`. -/
def beta2 (y : XR) : ℝ := 1 - sig (gco y)

lemma isScSmoothMap_beta1 : P.IsScSmoothMap realPolyfold beta1 :=
  isScSmoothMap_gco.comp_contDiff contDiff_sig

lemma isScSmoothMap_beta2 : P.IsScSmoothMap realPolyfold beta2 :=
  isScSmoothMap_gco.comp_contDiff contDiff_one_sub_sig

lemma beta1_inv (φ : Z3 × XR) : beta1 (ε.src φ) = beta1 (ε.tgt φ) := by
  change sig (gco φ.2) = sig (gco (φ.1 • φ.2)); rw [gco_smul]

lemma beta2_inv (φ : Z3 × XR) : beta2 (ε.src φ) = beta2 (ε.tgt φ) := by
  change 1 - sig (gco φ.2) = 1 - sig (gco (φ.1 • φ.2)); rw [gco_smul]

lemma beta1_add_beta2 (y : XR) : beta1 y + beta2 y = 1 := by
  unfold beta1 beta2; ring

lemma beta1_xm : beta1 xm = 1 := by
  unfold beta1 sig
  rw [gco_xm]
  exact Real.smoothTransition.one_of_one_le (by norm_num)

lemma beta2_x₀ : beta2 x₀ = 1 := by
  unfold beta2 sig
  rw [gco_x₀, Real.smoothTransition.zero_of_nonpos (by norm_num)]
  norm_num

lemma tsupport_beta1 : tsupport beta1 ⊆ U1 := by
  have h : support beta1 ⊆ gco ⁻¹' Ici (-1 / 2) := fun y hy => by
    by_contra h
    simp only [mem_preimage, mem_Ici, not_le] at h
    exact hy (by unfold beta1 sig; exact Real.smoothTransition.zero_of_nonpos (by linarith))
  refine (closure_minimal h (isClosed_Ici.preimage continuous_gco)).trans fun y hy => ?_
  change -1 < gco y
  have : -1 / 2 ≤ gco y := hy
  linarith

lemma tsupport_beta2 : tsupport beta2 ⊆ U2 := by
  have h : support beta2 ⊆ gco ⁻¹' Iic (1 / 2) := fun y hy => by
    by_contra h
    simp only [mem_preimage, mem_Iic, not_le] at h
    refine hy ?_
    unfold beta2 sig
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    norm_num
  refine (closure_minimal h (isClosed_Iic.preimage continuous_gco)).trans fun y hy => ?_
  change gco y < 1
  have : gco y ≤ 1 / 2 := hy
  linarith

/-! ### The boundary stratum of `M`: the two end points -/

lemma JpVec_mem_tangentSpace {y : XR} (hy : y ∈ Mset) :
    ((Jp (arcPt y.1.1), 0) : E 0) ∈ tangentSpace chart.model.E chart.model.C
      (chart '' (mData.toSubData.shrink chart ∩ Mset)) (levelLift chart 1 y) := by
  have hp := arcPt_mem_arc (fst_mem_Icc_of_mem y.2)
  have h2 : chart '' (mData.toSubData.shrink chart ∩ Mset) = RM.retract := chart_image_shrink_M
  erw [h2, tangentSpace_Marc hp (levelLift_M hy)]
  refine ⟨((Jp (arcPt y.1.1), 0) : E 0), ?_⟩
  change ((dρ (arcPt y.1.1) (Jp (arcPt y.1.1)), 0) : E 0) = _
  rw [dρ_Jp]

/-- At an end point of `M` the tangent line of `M` is not in `T^R_yX`. -/
theorem not_isTangentReducedAt_M {y : XR} (hy : y ∈ Mset) {i : Fin 2}
    (hi : arcPt y.1.1 i = 0) (hJ : Jp (arcPt y.1.1) i ≠ 0) : ¬ P.IsTangentReducedAt Mset y := by
  intro h
  have hred := h.isReducedChart mData isChart_chart (ScIso.refl _) (by ext; rfl)
    (mem_univ y) (mem_univ y) (toBase_levelLift_M hy)
  have h1 := (mem_minimalSubspaceWith _).1 (hred (JpVec_mem_tangentSpace hy)) i (by
    change (E.toBase 1 (levelLift chart 1 y)).1 i = 0
    rw [levelLift_M hy]; exact hi)
  exact hJ h1

lemma xm_arc : arcPt xm.1.1 = ![2, 0] := arcPt_neg_one

lemma x₀_arc : arcPt x₀.1.1 = ![0, 2] := arcPt_one

theorem not_isTangentReducedAt_xm : ¬ P.IsTangentReducedAt Mset xm :=
  not_isTangentReducedAt_M xm_mem_M (i := 1) (by rw [xm_arc]; rfl)
    (by rw [xm_arc]; simp [Jp])

theorem not_isTangentReducedAt_x₀ : ¬ P.IsTangentReducedAt Mset x₀ :=
  not_isTangentReducedAt_M x₀_mem_M (i := 0) (by rw [x₀_arc]; rfl)
    (by rw [x₀_arc]; simp [Jp])

lemma xm_mem_boundary : xm ∈ P.boundary := by rw [boundary_eq]; exact Or.inl rfl

lemma x₀_mem_boundary : x₀ ∈ P.boundary := by rw [boundary_eq]; exact Or.inr rfl

lemma mem_boundaryStratum_of {y : XR} (hy : y ∈ Mset) (hb : y ∈ P.boundary)
    (hn : ¬ P.IsTangentReducedAt Mset y) : y ∈ P.boundaryStratum Mset := by
  refine (mem_boundaryStratum_iff_subDegIndex isSmoothSubmanifold_M
    hasTameInducedStructure_M hy).2 ?_
  have h1 := (mem_submanifoldBoundary_iff_subDegIndex isSmoothSubmanifold_M hy).1
    ((mem_submanifoldBoundary_iff isSmoothSubmanifold_M).2 ⟨hy, hb, hn⟩)
  have h2 : P.subDegIndex isSmoothSubmanifold_M.isSubMPolyfold ⟨y, hy⟩ ≤ P.degIndex y :=
    subDegIndex_le isSmoothSubmanifold_M.isSubMPolyfold ⟨y, hy⟩
  have h3 : P.degIndex y ≤ 1 := by rw [DimensionJump.degIndex_eq]; split_ifs <;> omega
  omega

/-- **`∂₁M = {(−1, 0), (1, 0)}`.** -/
theorem boundaryStratum_M : P.boundaryStratum Mset = {xm, x₀} := by
  ext y
  constructor
  · intro hb
    have hb' := (mem_boundaryStratum_iff_subDegIndex isSmoothSubmanifold_M
      hasTameInducedStructure_M hb.1).1 hb
    have h2 := subDegIndex_le isSmoothSubmanifold_M.isSubMPolyfold ⟨y, hb.1⟩
    rw [hb'] at h2
    have hby : y ∈ P.boundary := h2
    rw [boundary_eq] at hby
    rcases hby with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact mem_boundaryStratum_of xm_mem_M xm_mem_boundary not_isTangentReducedAt_xm
    · exact mem_boundaryStratum_of x₀_mem_M x₀_mem_boundary not_isTangentReducedAt_x₀

lemma boundaryStratum_M_U1 : P.boundaryStratum (Mset ∩ U1) = {xm} := by
  rw [MPolyfold.boundaryStratum_inter_isOpen isOpen_U1, boundaryStratum_M]
  ext y
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · rfl
    · exact absurd h x₀_not_mem_U1
  · rintro rfl; exact ⟨Or.inl rfl, xm_mem_U1⟩

lemma boundaryStratum_M_U2 : P.boundaryStratum (Mset ∩ U2) = {x₀} := by
  rw [MPolyfold.boundaryStratum_inter_isOpen isOpen_U2, boundaryStratum_M]
  ext y
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · exact absurd h xm_not_mem_U2
    · rfl
  · rintro rfl; exact ⟨Or.inr rfl, x₀_mem_U2⟩

/-! ### The boundary orientation at the end points -/

/-- The chart of `X`, presented with the identity `E ≅ ℝ² ⊕ Z2`. -/
def pChart (y : XR) : P.PresentedChart y :=
  ⟨chart, isChart_chart, mem_univ y, 2, Z2, ScIso.refl _, by ext; rfl⟩

lemma exists_coeff {y : XR} (hy : y ∈ Mset) {e : P.TangentSpace}
    (he : e ∈ P.submanifoldTangent Mset y) :
    ∃ c : ℝ, chartVec isChart_chart e = c • ((Jp (arcPt y.1.1), 0) : E 0) := by
  have h : chartVec isChart_chart e ∈ chartVec isChart_chart '' P.submanifoldTangent Mset y :=
    ⟨e, he, rfl⟩
  rw [chartVec_image_M hy] at h
  obtain ⟨c, hc⟩ := (mem_span_singleton (R := ℝ) (M := E 0) (x := chartVec isChart_chart e)
    (y := ((Jp (arcPt y.1.1), 0) : E 0))).1 h
  exact ⟨c, hc.symm⟩

lemma exists_of_coeff {y : XR} (hy : y ∈ Mset) (c : ℝ) :
    ∃ e ∈ P.submanifoldTangent Mset y,
      chartVec isChart_chart e = c • ((Jp (arcPt y.1.1), 0) : E 0) := by
  have h0 : c • ((Jp (arcPt y.1.1), 0) : E 0) ∈ span ℝ {((Jp (arcPt y.1.1), 0) : E 0)} :=
    mem_span_singleton.2 ⟨c, rfl⟩
  have h : c • ((Jp (arcPt y.1.1), 0) : E 0) ∈
      chartVec isChart_chart '' P.submanifoldTangent Mset y := by
    rw [chartVec_image_M hy]
    exact h0
  obtain ⟨e, he, h'⟩ := h
  exact ⟨e, he, h'⟩

lemma det_span_frameVecM (y : XR) (c : ℝ) (w : Fin 1 → NM y)
    (hw : (w 0 : E 0) = c • ((Jp (arcPt y.1.1), 0) : E 0)) :
    (Basis.span (linearIndependent_frameVecM y)).det w = c := by
  let B := Basis.span (linearIndependent_frameVecM y)
  change B.det w = c
  have hB : w 0 = c • B 0 := by
    apply Subtype.ext
    rw [hw, Submodule.coe_smul, Basis.span_apply]
    rfl
  rw [Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply]
  change B.repr (w 0) 0 = c
  rw [hB, map_smul, B.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_same]

/-- The frames `(e)` of `T_yM`: positive iff the coefficient of `e` on `(J p, 0)` is positive. -/
lemma cons_mem_framesM_iff {y : XR} (hy : y ∈ Mset) {e : P.TangentSpace}
    (he : e ∈ P.submanifoldTangent Mset y) {c : ℝ}
    (hc : chartVec isChart_chart e = c • ((Jp (arcPt y.1.1), 0) : E 0))
    (a : Fin 0 → P.TangentSpace) :
    (Fin.cons e a : Fin 1 → P.TangentSpace) ∈ framesM y ↔ 0 < c := by
  have hmem' : (chartVec isChart_chart e : E 0) ∈ (NM y : Set (E 0)) := by
    rw [NM_eq hy]; exact ⟨e, he, rfl⟩
  have hmem : (chartVec isChart_chart e : E 0) ∈ NM y := hmem'
  have hL : ∀ i, (Fin.cons e a : Fin 1 → P.TangentSpace) i ∈ P.submanifoldTangent Mset y := by
    intro i; rw [Fin.fin_one_eq_zero i]; exact he
  have key := exists_basis_coe_iff_det_pos (Basis.span (linearIndependent_frameVecM y))
    (fun i => chartVec isChart_chart ((Fin.cons e a : Fin 1 → P.TangentSpace) i))
    (fun _ => ⟨chartVec isChart_chart e, hmem⟩) (fun i => by rw [Fin.fin_one_eq_zero i]; rfl)
  have hd := det_span_frameVecM y c (fun _ => ⟨chartVec isChart_chart e, hmem⟩) hc
  rw [hd] at key
  exact ⟨fun h => key.1 h.2, fun h => ⟨hL, key.2 h⟩⟩

lemma isOutward_iff {y : XR} (hy : y ∈ Mset) {e : P.TangentSpace}
    (he : e ∈ P.submanifoldTangent Mset y) :
    P.IsOutwardTangent e ↔ ¬ ∀ i, (arcPt y.1.1) i = 0 → 0 ≤ (chartVec isChart_chart e).1 i := by
  unfold IsOutwardTangent
  rw [he.1, isInwardVec_iff (pChart y) he.1]
  change ¬ (∀ i, (chart y).1 i = 0 → _) ↔ _
  rw [chart_of_mem_M hy]
  rfl

/-- **At `(1, 0)` the boundary orientation is positive**: the outward vectors of `T_{(1,0)}M`
point along `+(J p, 0)`, the direction of increasing `t`. -/
theorem frames_boundaryOp_x₀ : (P.boundaryOp (oM.tangent x₀)).frames.Nonempty := by
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun e he hout => ?_⟩
  obtain ⟨c, hc⟩ := exists_coeff x₀_mem_M he
  refine (cons_mem_framesM_iff x₀_mem_M he hc _).2 ?_
  rw [isOutward_iff x₀_mem_M he, hc, x₀_arc] at hout
  by_contra hneg
  refine hout fun i hi => ?_
  fin_cases i
  · simp [Jp]; nlinarith
  · simp at hi

/-- **At `(−1, 0)` the boundary orientation is negative**: the outward vectors of
`T_{(−1,0)}M` point along `−(J p, 0)`. -/
theorem frames_boundaryOp_xm : ¬ (P.boundaryOp (oM.tangent xm)).frames.Nonempty := by
  rintro ⟨a, -, ha⟩
  obtain ⟨e, he, hc⟩ := exists_of_coeff xm_mem_M (-1)
  have hout : P.IsOutwardTangent e := by
    rw [isOutward_iff xm_mem_M he, hc, xm_arc]
    intro h
    have := h 1 (by simp)
    simp [Jp] at this
    norm_num at this
  have := (cons_mem_framesM_iff xm_mem_M he hc a).1 (ha e he hout)
  norm_num at this

/-! ### A graph chart of `M` -/

lemma nonneg_of_mem_arc {p : V2} (hp : p ∈ arc) (i : Fin 2) : 0 ≤ p i := hp.1 i

lemma sP_pos {p : V2} (hp : p ∈ arc) : 0 < p 0 + p 1 := by
  have h := sq_add_sq_of_mem_arc hp
  have h0 := nonneg_of_mem_arc hp 0
  have h1 := nonneg_of_mem_arc hp 1
  by_contra hneg
  have : p 0 = 0 := by linarith
  have : p 1 = 0 := by linarith
  nlinarith

lemma sqrt_eq_sP {p : V2} (hp : p ∈ arc) : √(8 - (ell2 p) ^ 2) = p 0 + p 1 := by
  have h := sq_add_sq_of_mem_arc hp
  rw [show 8 - (ell2 p) ^ 2 = (p 0 + p 1) ^ 2 by rw [ell2_apply]; nlinarith]
  exact Real.sqrt_sq (sP_pos hp).le

/-- The inverse `u ↦ ((u + √(8 − u²))/2, (√(8 − u²) − u)/2)` of `p ↦ p₀ − p₁` on the quarter
circle. -/
def uPt (u : ℝ) : V2 := ![(u + √(8 - u ^ 2)) / 2, (√(8 - u ^ 2) - u) / 2]

lemma uPt_ell2 {p : V2} (hp : p ∈ arc) : uPt (ell2 p) = p := by
  rw [uPt, sqrt_eq_sP hp]
  ext i; fin_cases i <;> simp

lemma ell2_sq_le {p : V2} (hp : p ∈ arc) : (ell2 p) ^ 2 ≤ 4 := by
  have h := sq_add_sq_of_mem_arc hp
  have h0 := nonneg_of_mem_arc hp 0
  have h1 := nonneg_of_mem_arc hp 1
  rw [ell2_apply]; nlinarith [mul_nonneg h0 h1]

/-- The derivative of `uPt`. -/
def duPt (u : ℝ) : V2 :=
  ![(1 + (-(2 * u)) / (2 * √(8 - u ^ 2))) / 2, ((-(2 * u)) / (2 * √(8 - u ^ 2)) - 1) / 2]

lemma hasDerivAt_uPt {u : ℝ} (hu : u ^ 2 ≤ 4) : HasDerivAt uPt (duPt u) u := by
  have hpos : (8 - u ^ 2) ≠ 0 := by nlinarith
  have hs : HasDerivAt (fun x : ℝ => √(8 - x ^ 2)) ((-(2 * u)) / (2 * √(8 - u ^ 2))) u := by
    have h1 : HasDerivAt (fun x : ℝ => 8 - x ^ 2) (-(2 * u)) u := by
      have := (hasDerivAt_pow 2 u).const_sub 8
      norm_num at this
      exact this
    exact h1.sqrt hpos
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · exact ((hasDerivAt_id u).add hs).div_const 2
  · exact (hs.sub (hasDerivAt_id u)).div_const 2

lemma duPt_eq {p : V2} (hp : p ∈ arc) :
    duPt (ell2 p) = (-(p 0 + p 1)⁻¹) • Jp p := by
  have hs := sP_pos hp
  rw [duPt, sqrt_eq_sP hp]
  ext i; fin_cases i <;> simp [Jp] <;> field_simp <;> ring

/-- The projection `(p, a, b) ↦ p₀ − p₁ ∈ ℝ¹`. -/
def pE : E 0 →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ell2.comp (ContinuousLinearMap.fst ℝ V2 (Z2 0))).smulRight (EuclideanSpace.single 0 1)

lemma pE_apply_zero (q : E 0) : pE q 0 = ell2 q.1 := by simp [pE]

/-- The chart of `X` with values in `E₀`. -/
def cE (y : XR) : E 0 := ψfun y.1

lemma cE_eq (y : XR) : cE y = chart y := rfl

lemma cE_of_mem_M {y : XR} (hy : y ∈ Mset) : cE y = ((arcPt y.1.1, 0) : E 0) := chart_of_mem_M hy

/-- `t` clamped to `[−1, 1]`. -/
def tcl (u : ℝ) : ℝ := max (-1) (min 1 (tOf (uPt u)))

lemma tcl_mem (u : ℝ) : tcl u ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The parametrization `u ↦ (t(u), 0)` of `M`. -/
def qM (u : EuclideanSpace ℝ (Fin 1)) : XR := mPar ⟨tcl (u 0), tcl_mem _⟩

lemma arcPt_mem {y : XR} : arcPt y.1.1 ∈ arc := arcPt_mem_arc (fst_mem_Icc_of_mem y.2)

lemma qM_coord {y : XR} (hy : y ∈ Mset) : qM (pE (cE y)) = y := by
  have ht := fst_mem_Icc_of_mem y.2
  have h1 : tcl (pE (cE y) 0) = y.1.1 := by
    rw [pE_apply_zero, cE_of_mem_M hy]
    change max (-1) (min 1 (tOf (uPt (ell2 (arcPt y.1.1))))) = y.1.1
    rw [uPt_ell2 arcPt_mem, tOf_arcPt ht, min_eq_right ht.2, max_eq_right ht.1]
  refine Subtype.ext (Prod.ext ?_ hy.symm)
  exact h1

/-- The tangent vector `−(p₀ + p₁)⁻¹ (J p, 0)` of `u ↦ (uPt u, 0)`. -/
def wM (y : XR) : E 0 :=
  ((-(arcPt y.1.1 0 + arcPt y.1.1 1)⁻¹) • Jp (arcPt y.1.1), 0)

/-- The derivative `v ↦ v₀ wM y`. -/
def LM (y : XR) : EuclideanSpace ℝ (Fin 1) →L[ℝ] E 0 :=
  (EuclideanSpace.proj (0 : Fin 1)).smulRight (wM y)

lemma continuous_cE : Continuous cE :=
  continuousOn_univ.1 chart.continuousOn_toFun

lemma isCompact_dom : IsCompact ((fun y => pE (cE y)) '' Mset) :=
  isCompact_M.image (pE.continuous.comp continuous_cE)

lemma ell2_Jp (p : V2) : ell2 (Jp p) = -(p 0 + p 1) := by simp [Jp]; ring

lemma wM_eq (y : XR) :
    wM y = (-(arcPt y.1.1 0 + arcPt y.1.1 1)⁻¹) • ((Jp (arcPt y.1.1), 0) : E 0) :=
  Prod.ext rfl (by change (0 : Z2 0) = _ • 0; rw [smul_zero])

lemma LM_apply (y : XR) (v : EuclideanSpace ℝ (Fin 1)) : LM y v = v 0 • wM y := rfl

lemma range_LM {y : XR} (hy : y ∈ Mset) :
    range (LM y) = P.chartTangent isChart_chart Mset y := by
  have hs := sP_pos (arcPt_mem (y := y))
  change _ = chartVec isChart_chart '' P.submanifoldTangent Mset y
  rw [chartVec_image_M hy]
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    refine mem_span_singleton.2 ⟨v 0 * (-(arcPt y.1.1 0 + arcPt y.1.1 1)⁻¹), ?_⟩
    rw [LM_apply, wM_eq, mul_smul]
  · intro hz
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hz
    refine ⟨(-(c * (arcPt y.1.1 0 + arcPt y.1.1 1))) • EuclideanSpace.single 0 1, ?_⟩
    rw [LM_apply, wM_eq, smul_smul]
    congr 1
    simp only [PiLp.smul_apply, PiLp.single_apply, if_true, smul_eq_mul, mul_one]
    field_simp

lemma pE_LM {y : XR} (v : EuclideanSpace ℝ (Fin 1)) : pE (LM y v) = v := by
  have hs := sP_pos (arcPt_mem (y := y))
  ext i
  fin_cases i
  change pE (LM y v) 0 = v 0
  rw [pE_apply_zero]
  change ell2 (v 0 • wM y).1 = v 0
  rw [wM, Prod.smul_mk, map_smul, map_smul, ell2_Jp, smul_eq_mul, smul_eq_mul]
  field_simp

lemma hasFDerivAt_uPt0 (y : XR) :
    HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 1) => ((uPt (u 0), (0 : Z2 0)) : E 0)) (LM y)
      (pE (cE y)) := by
  set a := pE (cE y) 0 with ha
  have ha' : a = ell2 (arcPt y.1.1) := by rw [ha, pE_apply_zero]; rfl
  have hd := hasDerivAt_uPt (u := a) (by rw [ha']; exact ell2_sq_le arcPt_mem)
  have h1 : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin 1) => u 0)
      (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) (pE (cE y)) :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt
  have h2 := hd.hasFDerivAt.comp (pE (cE y)) h1
  let ι : V2 →L[ℝ] E 0 := ContinuousLinearMap.inl ℝ V2 (Z2 0)
  have h3 := ι.hasFDerivAt.comp (pE (cE y)) h2
  refine h3.congr_fderiv ?_
  ext1 v
  change ((v 0 • duPt a, (0 : Z2 0)) : E 0) = v 0 • wM y
  rw [ha', duPt_eq arcPt_mem, wM_eq, smul_smul, ← smul_smul]
  exact Prod.ext rfl (by change (0 : Z2 0) = _ • _ • 0; rw [smul_zero, smul_zero])

lemma continuous_arcPtXR : Continuous fun y : XR => arcPt y.1.1 :=
  continuous_arcPt.comp (continuous_fst.comp continuous_subtype_val)

lemma continuous_wM : Continuous wM := by
  have hs : Continuous fun y : XR => arcPt y.1.1 0 + arcPt y.1.1 1 :=
    ((continuous_apply 0).comp continuous_arcPtXR).add
      ((continuous_apply 1).comp continuous_arcPtXR)
  have hi : Continuous fun y : XR => (arcPt y.1.1 0 + arcPt y.1.1 1)⁻¹ :=
    hs.inv₀ fun y => (sP_pos arcPt_mem).ne'
  exact (hi.neg.smul (continuous_Jp.comp continuous_arcPtXR)).prodMk continuous_const

lemma continuous_LM : Continuous LM :=
  ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin 1)) (E 0))
    (EuclideanSpace.proj (0 : Fin 1))).continuous.comp continuous_wM

/-- **A graph chart of `M`** (the class of sheets of §9.5): the chart of `X`, the projection
`p₀ − p₁`, the parametrization `u ↦ (t(u), 0)`. -/
def gM : P.GraphChart 1 Mset where
  φ := chart
  isChart := isChart_chart
  subset_source _ _ := mem_univ _
  p := pE
  q := qM
  q_coord _ hy := qM_coord hy
  L := LM
  measurableSet_dom := isCompact_dom.isClosed.measurableSet
  p_L _ _ v := pE_LM v
  range_L _ hy := range_LM hy
  hasFDerivWithinAt y hy := by
    refine HasFDerivWithinAt.congr' (hasFDerivAt_uPt0 y).hasFDerivWithinAt ?_
      (mem_image_of_mem _ hy)
    rintro _ ⟨y', hy', rfl⟩
    change cE (qM (pE (cE y'))) = ((uPt (pE (cE y') 0), 0) : E 0)
    rw [qM_coord hy', pE_apply_zero, cE_of_mem_M hy']
    change _ = ((uPt (ell2 (arcPt y'.1.1)), 0) : E 0)
    rw [uPt_ell2 arcPt_mem]
  continuousOn_L := continuous_LM.continuousOn

/-- **`M` is a sheet of the class of §9.5** for every form evaluation of dimension `1`. -/
theorem M_mem_sheets {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : ε.FormEval 1 Ω) :
    Mset ∈ F.sheets := by
  refine ⟨isSubmanifoldOfDim_M, gM, fun η => ?_⟩
  have hcont := F.continuousOn_ev_tvec isSmoothSubmanifold_M gM η
  have hco : ContinuousOn (fun u => F.ev η (gM.tvec (gM.q u))) gM.dom :=
    hcont.comp gM.continuousOn_q fun u hu => gM.q_mem hu
  exact hco.integrableOn_compact isCompact_dom


/-! ### The integral `∮_Θ̂ da` -/

/-- The structures of the class used for `∮_Θ̂`: sheets in the class `F.sheets`, describing
`T̂Θ`, with the property of Definition 7.2.18 on `U(x)`. -/
def GoodM (x : AX.Obj) (C : AX.X.OrientedTameStructure (0 + 1) thetaM x) : Prop :=
  (∀ i, C.M i ∈ (AX.epFormsInftyEval (0 + 1)).sheets) ∧ C.Represents TM ∧ C.rep.HasLUC

/-- The structure at `(−1, 0)` on `U₁`. -/
def C1 : AX.X.OrientedTameStructure (0 + 1) thetaM xm := mTame xm_mem_M R1

/-- The structure at `(1, 0)` on `U₂`. -/
def C2 : AX.X.OrientedTameStructure (0 + 1) thetaM x₀ := mTame x₀_mem_M R2

lemma goodM_C1 : GoodM xm C1 :=
  ⟨fun _ => EpGroupoid.FormEval.inter_mem_sheets (M_mem_sheets _) isOpen_U1,
    mTame_represents xm_mem_M R1, ε.isLUC_iff_forall_naturalRep.1 isLUC_ε xm R1⟩

lemma goodM_C2 : GoodM x₀ C2 :=
  ⟨fun _ => EpGroupoid.FormEval.inter_mem_sheets (M_mem_sheets _) isOpen_U2,
    mTame_represents x₀_mem_M R2, ε.isLUC_iff_forall_naturalRep.1 isLUC_ε x₀ R2⟩


lemma boundarySheet_C1 (i : C1.ι) : C1.boundarySheet i = {xm} := boundaryStratum_M_U1

lemma boundarySheet_C2 (i : C2.ι) : C2.boundarySheet i = {x₀} := boundaryStratum_M_U2

lemma tsupport_beta1_sub : tsupport beta1 ⊆ AX.X.π ⁻¹' (AX.X.π '' C1.U) :=
  fun y hy => ⟨y, tsupport_beta1 hy, rfl⟩

lemma tsupport_beta2_sub : tsupport beta2 ⊆ AX.X.π ⁻¹' (AX.X.π '' C2.U) :=
  fun y hy => ⟨y, tsupport_beta2 hy, rfl⟩


instance : Unique C1.ι := inferInstanceAs (Unique Unit)

instance : Unique C2.ι := inferInstanceAs (Unique Unit)

/-- `∫_{∂₁(M ∩ U₁)} β₁a = −a(−1, 0)`: the boundary point `(−1, 0)` is negatively oriented. -/
lemma integ_C1 (a : AX.epFormsInfty 0) :
    ∑ i, (C1.σ i : ℝ) * AX.zeroFormIntegration.integ
      (AX.epFormsInftySmul beta1 0 isScSmoothMap_beta1 beta1_inv a) (C1.boundarySheet i)
      (C1.boundaryOrient i).tangent (C1.boundarySheet i) = -AX.zeroFormEval a xm := by
  rw [Fintype.sum_unique]
  have hm : xm ∈ C1.boundarySheet default := by rw [boundarySheet_C1]; rfl
  rw [show (C1.σ default : ℝ) = 1 from by change ((1 : ℚ) : ℝ) = 1; norm_num, one_mul,
    EP.zeroFormIntegration_integ, EpGroupoid.pointInteg_of_mem
      (by rw [boundarySheet_C1]; exact subsingleton_singleton) ⟨hm, hm⟩,
    C1.boundaryOrient_tangent _ hm]
  have he := AX.zeroFormEval_epFormsInftySmul isScSmoothMap_beta1 beta1_inv a xm
  rw [he, beta1_xm, one_mul]
  have ht : (C1.orient default).tangent xm = oM.tangent xm :=
    oM.restrict_tangent isOpen_U1 xm_mem_U1
  have hf : ¬ (AX.X.PObj.boundaryOp (oM.tangent xm)).frames.Nonempty := frames_boundaryOp_xm
  rw [ht, EpGroupoid.frameSign, if_neg hf]
  ring

/-- `∫_{∂₁(M ∩ U₂)} β₂a = a(1, 0)`: the boundary point `(1, 0)` is positively oriented. -/
lemma integ_C2 (a : AX.epFormsInfty 0) :
    ∑ i, (C2.σ i : ℝ) * AX.zeroFormIntegration.integ
      (AX.epFormsInftySmul beta2 0 isScSmoothMap_beta2 beta2_inv a) (C2.boundarySheet i)
      (C2.boundaryOrient i).tangent (C2.boundarySheet i) = AX.zeroFormEval a x₀ := by
  rw [Fintype.sum_unique]
  have hm : x₀ ∈ C2.boundarySheet default := by rw [boundarySheet_C2]; rfl
  rw [show (C2.σ default : ℝ) = 1 from by change ((1 : ℚ) : ℝ) = 1; norm_num, one_mul,
    EP.zeroFormIntegration_integ, EpGroupoid.pointInteg_of_mem
      (by rw [boundarySheet_C2]; exact subsingleton_singleton) ⟨hm, hm⟩,
    C2.boundaryOrient_tangent _ hm]
  have he := AX.zeroFormEval_epFormsInftySmul isScSmoothMap_beta2 beta2_inv a x₀
  rw [he, beta2_x₀, one_mul]
  have ht : (C2.orient default).tangent x₀ = oM.tangent x₀ :=
    oM.restrict_tangent isOpen_U2 x₀_mem_U2
  have hf : (AX.X.PObj.boundaryOp (oM.tangent x₀)).frames.Nonempty := frames_boundaryOp_x₀
  rw [ht, EpGroupoid.frameSign, if_pos hf, one_mul]

/-- **The effective branched integral of Remark 9.5.20** (2021 p. 451): for `Θ = 1_M`,
`M = [−1, 1] × {0}`, oriented by `[−1, 1]`, in `ℤ/3 ⋉ X`, and every `a ∈ Ω⁰_{ep,∞}`,
`∮_Θ̂ da = (1/3)(a(1, 0) − a(−1, 0))`: the factor `1/♯G_x^eff = 1/3` of the points of `M`. -/
theorem remark_9_5_20_integral (a : AX.epFormsInfty 0) :
    (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
        isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
        (AX.epFormsInftyD 0 a) =
      (1 / 3 : ℝ) * (AX.zeroFormEval a x₀ - AX.zeroFormEval a xm) := by
  set F := AX.epFormsInftyEval (0 + 1)
  have hcov := EpGroupoid.FormEval.hcovEff_of_tameOpen (F := F)
    (EpGroupoid.FormEval.tameOpen AX.X) m_hloc_LUC
  set Φ := EpGroupoid.branchedMeasureEff (F.sheetIntegration (Nat.succ_pos 0))
    isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM hcov
  change Φ (AX.epFormsInftyD 0 a) univ = _
  let c : AX.Obj → ℝ := fun x => (Nat.card (AX.X.EffIsotropy x) : ℝ)⁻¹
  have hΦ : ∀ (η : AX.epFormsInfty (0 + 1)) (x : AX.Obj)
      (C : AX.X.OrientedTameStructure (0 + 1) thetaM x), GoodM x C →
      ∀ K : Set (AX.X.orbitSupp thetaM),
        MeasurableSet[AX.X.lebesgueSigma F.sheetNull thetaM] K →
        Subtype.val '' K ⊆ AX.X.π '' C.U →
        Φ η K = c x * C.sheetSum (F.sheetIntegration (Nat.succ_pos 0)) η
          (AX.X.π ⁻¹' (Subtype.val '' K)) := fun η x C hC K hK hKU =>
    EpGroupoid.branchedMeasureEff_apply _ _ _ _ hcov η C hC.1 hC.2.1 hC.2.2 hK hKU
  have hGS : ∀ x C, GoodM x C → ∀ i, C.M i ∈ F.sheets := fun _ _ h => h.1
  have hcov' : ∀ x ∈ supp thetaM, ∃ C, GoodM x C := hcov
  have hsplit : AX.epFormsInftySmul beta1 0 isScSmoothMap_beta1 beta1_inv a +
      AX.epFormsInftySmul beta2 0 isScSmoothMap_beta2 beta2_inv a = a := by
    have h := AX.sum_epFormsInftySmul (k := 0) (Finset.univ : Finset Bool)
      (fun j => if j then beta1 else beta2)
      (fun j => by cases j; exacts [isScSmoothMap_beta2, isScSmoothMap_beta1])
      (fun j φ => by cases j; exacts [beta2_inv φ, beta1_inv φ])
      (fun x => by simp [beta1_add_beta2]) a
    rw [Fintype.sum_bool] at h
    exact h
  nth_rewrite 1 [← hsplit]
  rw [map_add, map_add, FunLike.coe_add, Pi.add_apply,
    AX.stokes_one_structure_all Φ c GoodM isCompactBranched_thetaM hGS hcov' hΦ C1 goodM_C1
      isScSmoothMap_beta1 beta1_inv tsupport_beta1_sub a,
    AX.stokes_one_structure_all Φ c GoodM isCompactBranched_thetaM hGS hcov' hΦ C2 goodM_C2
      isScSmoothMap_beta2 beta2_inv tsupport_beta2_sub a,
    AX.sum_boundaryIntegral_smul_eq_dim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
      C1 (hGS _ _ goodM_C1) (fun i => by rw [boundarySheet_C1 i]; exact subsingleton_singleton)
      isScSmoothMap_beta1 beta1_inv tsupport_beta1_sub a,
    AX.sum_boundaryIntegral_smul_eq_dim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
      C2 (hGS _ _ goodM_C2) (fun i => by rw [boundarySheet_C2 i]; exact subsingleton_singleton)
      isScSmoothMap_beta2 beta2_inv tsupport_beta2_sub a]
  rw [integ_C1, integ_C2, show c xm = 1 / 3 by
      change ((Nat.card (ε.EffIsotropy xm) : ℕ) : ℝ)⁻¹ = _
      rw [card_effIsotropy_of_snd_eq_zero xm_mem_M]; norm_num,
    show c x₀ = 1 / 3 by
      change ((Nat.card (ε.EffIsotropy x₀) : ℕ) : ℝ)⁻¹ = _
      rw [card_effIsotropy_of_snd_eq_zero x₀_mem_M]; norm_num]
  ring


/-! ### The boundary integral `∮_{∂Θ̂} a` read in `X` -/

lemma mem_submanifoldBoundary_M {y : XR} (hy : y ∈ Mset) (hb : y ∈ P.boundary)
    (hn : ¬ P.IsTangentReducedAt Mset y) : y ∈ P.submanifoldBoundary (Mset ∩ univ) := by
  rw [inter_univ]
  exact (MPolyfold.mem_submanifoldBoundary_iff isSmoothSubmanifold_M).2 ⟨hy, hb, hn⟩

lemma boundaryTheta_of_mem {y : XR} (hy : y ∈ Mset) (hb : y ∈ P.boundary)
    (hn : ¬ P.IsTangentReducedAt Mset y) : ε.boundaryTheta thetaM y = 1 := by
  classical
  rw [boundaryTheta_eq hasIndependentTangentSums_thetaM
    (mBranching hy isOpen_univ (mem_univ y)).toLocalBranchingStructure (mem_univ y)]
  change ∑ i ∈ Finset.univ.filter fun (_ : Unit) =>
    y ∈ P.submanifoldBoundary (Mset ∩ univ), (1 : ℚ) = 1
  rw [Finset.filter_true_of_mem fun _ _ => mem_submanifoldBoundary_M hy hb hn]
  simp

/-- **`∂Θ(−1, 0) = 1`.** -/
theorem boundaryTheta_xm : ε.boundaryTheta thetaM xm = 1 :=
  boundaryTheta_of_mem xm_mem_M xm_mem_boundary not_isTangentReducedAt_xm

/-- **`∂Θ(1, 0) = 1`.** -/
theorem boundaryTheta_x₀ : ε.boundaryTheta thetaM x₀ = 1 :=
  boundaryTheta_of_mem x₀_mem_M x₀_mem_boundary not_isTangentReducedAt_x₀

lemma xm_mem_supp_boundaryTheta : xm ∈ supp (AX.X.boundaryTheta thetaM) := by
  change (0 : ℚ) < ε.boundaryTheta thetaM xm
  rw [boundaryTheta_xm]; norm_num

lemma x₀_mem_supp_boundaryTheta : x₀ ∈ supp (AX.X.boundaryTheta thetaM) := by
  change (0 : ℚ) < ε.boundaryTheta thetaM x₀
  rw [boundaryTheta_x₀]; norm_num

/-- Structures at the points of `supp ∂Θ` with boundary sheets of at most one point and LUC. -/
theorem m_hcovB : ∀ x ∈ supp (AX.X.boundaryTheta thetaM),
    ∃ C : AX.X.OrientedTameStructure (0 + 1) thetaM x, C.Represents TM ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ EpGroupoid.pointSheets AX.X) ∧
      C.rep.HasLUC := by
  intro x hx
  have hxM : x ∈ Mset := by
    have h := (AX.X.supp_boundaryTheta_subset thetaM hx).2
    rwa [supp_thetaM] at h
  by_cases hg : -1 < gco x
  · let R := natRepM hxM isOpen_U1 isConnected_U1 hg smul_mem_U1
    refine ⟨mTame hxM R, mTame_represents hxM R, fun i hne =>
      (mTame hxM R).boundarySheet_mem_pointSheets isBranchedEpSubgroupoid_thetaM i ?_ hne,
      ε.isLUC_iff_forall_naturalRep.1 isLUC_ε x R⟩
    change (P.boundaryStratum (Mset ∩ U1)).Subsingleton
    rw [boundaryStratum_M_U1]; exact subsingleton_singleton
  · have hg2 : gco x < 1 := by linarith
    let R := natRepM hxM isOpen_U2 isConnected_U2 hg2 smul_mem_U2
    refine ⟨mTame hxM R, mTame_represents hxM R, fun i hne =>
      (mTame hxM R).boundarySheet_mem_pointSheets isBranchedEpSubgroupoid_thetaM i ?_ hne,
      ε.isLUC_iff_forall_naturalRep.1 isLUC_ε x R⟩
    change (P.boundaryStratum (Mset ∩ U2)).Subsingleton
    rw [boundaryStratum_M_U2]; exact subsingleton_singleton

/-- **The effective boundary integral of Remark 9.5.20 read in `X`** (2021 p. 452): with the
effective boundary measure of Theorem 9.5.16 (weights `1/♯G^eff_x` of `X`, `= 1/3` at both
end points), `∮_{∂Θ̂} a = (1/3)(a(1, 0) − a(−1, 0))` for every `a ∈ Ω⁰_{ep,∞}`. -/
theorem remark_9_5_20_boundary (a : AX.epFormsInfty 0) :
    AX.boundaryBranchedMeasureEffDim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
        isOrientation_thetaM m_hloc_LUC a univ =
      (1 / 3 : ℝ) * (AX.zeroFormEval a x₀ - AX.zeroFormEval a xm) := by
  set Φb := AX.boundaryBranchedMeasureEffDim1 isBranchedEpSubgroupoid_thetaM
    isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
  let c : AX.Obj → ℝ := fun x => (Nat.card (AX.X.EffIsotropy x) : ℝ)⁻¹
  let Pr : ∀ x, AX.X.OrientedTameStructure (0 + 1) thetaM x → Prop := fun _ C => C.rep.HasLUC
  have hΦb : EpGroupoid.IsBoundaryLocalI AX.zeroFormIntegration isBranchedEpSubgroupoid_thetaM
      Φb c Pr (T := TM) := fun η x C hCT hx hS hL K hK hKU =>
    (AX.theorem_9_5_16_dim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
      isOrientation_thetaM m_hloc_LUC).exists.choose_spec η x C hCT hx hS hL K hK hKU
  have hnd : AX.X.IsNDimensional thetaM (0 + 1) := EpGroupoid.FormEval.isNDimensional_of_loc m_hloc
  have hsplit : AX.epFormsInftySmul beta1 0 isScSmoothMap_beta1 beta1_inv a +
      AX.epFormsInftySmul beta2 0 isScSmoothMap_beta2 beta2_inv a = a := by
    have h := AX.sum_epFormsInftySmul (k := 0) (Finset.univ : Finset Bool)
      (fun j => if j then beta1 else beta2)
      (fun j => by cases j; exacts [isScSmoothMap_beta2, isScSmoothMap_beta1])
      (fun j φ => by cases j; exacts [beta2_inv φ, beta1_inv φ])
      (fun x => by simp [beta1_add_beta2]) a
    rw [Fintype.sum_bool] at h
    exact h
  have hs1 : ∀ i, (C1.boundarySheet i).Subsingleton := fun i => by
    rw [boundarySheet_C1 i]; exact subsingleton_singleton
  have hs2 : ∀ i, (C2.boundarySheet i).Subsingleton := fun i => by
    rw [boundarySheet_C2 i]; exact subsingleton_singleton
  nth_rewrite 1 [← hsplit]
  rw [map_add, FunLike.coe_add, Pi.add_apply,
    EpGroupoid.boundaryMeasure_univ_eqI AX.zeroFormIntegration isBranchedEpSubgroupoid_thetaM Φb
      c Pr (fun N B => EpGroupoid.point_isNull_iff_isHNull_zero N B)
      (fun η N g B h => AX.zeroFormIntegration_integ_of_empty η g h) isCompactBranched_thetaM hnd
      hΦb m_hcovB _ C1 goodM_C1.2.1 xm_mem_supp_boundaryTheta
      (fun i hne => C1.boundarySheet_mem_pointSheets isBranchedEpSubgroupoid_thetaM i (hs1 i) hne)
      goodM_C1.2.2 (isClosed_tsupport beta1) (EpGroupoid.isSaturated_tsupport beta1_inv)
      tsupport_beta1_sub
      (fun x' C' _ i B _ hBZ => AX.zeroFormIntegration_smul_eq_zero isScSmoothMap_beta1
        beta1_inv a _ _ fun y hy =>
          image_eq_zero_of_notMem_tsupport (Set.disjoint_left.1 hBZ hy.1)),
    EpGroupoid.boundaryMeasure_univ_eqI AX.zeroFormIntegration isBranchedEpSubgroupoid_thetaM Φb
      c Pr (fun N B => EpGroupoid.point_isNull_iff_isHNull_zero N B)
      (fun η N g B h => AX.zeroFormIntegration_integ_of_empty η g h) isCompactBranched_thetaM hnd
      hΦb m_hcovB _ C2 goodM_C2.2.1 x₀_mem_supp_boundaryTheta
      (fun i hne => C2.boundarySheet_mem_pointSheets isBranchedEpSubgroupoid_thetaM i (hs2 i) hne)
      goodM_C2.2.2 (isClosed_tsupport beta2) (EpGroupoid.isSaturated_tsupport beta2_inv)
      tsupport_beta2_sub
      (fun x' C' _ i B _ hBZ => AX.zeroFormIntegration_smul_eq_zero isScSmoothMap_beta2
        beta2_inv a _ _ fun y hy =>
          image_eq_zero_of_notMem_tsupport (Set.disjoint_left.1 hBZ hy.1)),
    integ_C1, integ_C2, show c xm = 1 / 3 by
      change ((Nat.card (ε.EffIsotropy xm) : ℕ) : ℝ)⁻¹ = _
      rw [card_effIsotropy_of_snd_eq_zero xm_mem_M]; norm_num,
    show c x₀ = 1 / 3 by
      change ((Nat.card (ε.EffIsotropy x₀) : ℕ) : ℝ)⁻¹ = _
      rw [card_effIsotropy_of_snd_eq_zero x₀_mem_M]; norm_num]
  ring


/-- **Stokes' formula for Remark 9.5.20** (`∮_Θ̂ da = ∮_{∂Θ̂} a` with the effective boundary
measure of `X`), obtained by computing both sides; no partitions of unity are used. -/
theorem remark_9_5_20_stokes (a : AX.epFormsInfty 0) :
    (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
        isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
        (AX.epFormsInftyD 0 a) =
      AX.boundaryBranchedMeasureEffDim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
        isOrientation_thetaM m_hloc_LUC a univ := by
  rw [remark_9_5_20_integral, remark_9_5_20_boundary]

/-- **The two readings of the boundary weights in Remark 9.5.20** (2021 p. 452): the sum over
the oriented boundary points `p ∈ ∂X = {(−1, 0), (1, 0)}` of `(1/♯G^eff_p) · sign(p) · a(p)` is
`(1/3)(a(1, 0) − a(−1, 0))` when `G^eff_p` is read in `X` and `a(1, 0) − a(−1, 0)` when it is
read in the ep-groupoid `∂X`.  The signs are those of the boundary orientation of `M`. -/
theorem remark_9_5_20_boundary_weights (a : AX.epFormsInfty 0) :
    (Nat.card (ε.EffIsotropy x₀) : ℝ)⁻¹ *
          (EpGroupoid.frameSign (X := ε) (P.boundaryOp (oM.tangent x₀)) * AX.zeroFormEval a x₀) +
        (Nat.card (ε.EffIsotropy xm) : ℝ)⁻¹ *
          (EpGroupoid.frameSign (X := ε) (P.boundaryOp (oM.tangent xm)) * AX.zeroFormEval a xm) =
      (1 / 3 : ℝ) * (AX.zeroFormEval a x₀ - AX.zeroFormEval a xm) ∧
    (Nat.card (εB.EffIsotropy ⟨x₀, x₀_mem_boundary⟩) : ℝ)⁻¹ *
          (EpGroupoid.frameSign (X := ε) (P.boundaryOp (oM.tangent x₀)) * AX.zeroFormEval a x₀) +
        (Nat.card (εB.EffIsotropy ⟨xm, xm_mem_boundary⟩) : ℝ)⁻¹ *
          (EpGroupoid.frameSign (X := ε) (P.boundaryOp (oM.tangent xm)) * AX.zeroFormEval a xm) =
      AX.zeroFormEval a x₀ - AX.zeroFormEval a xm := by
  have h0 : EpGroupoid.frameSign (X := ε) (P.boundaryOp (oM.tangent x₀)) = 1 := by
    exact if_pos frames_boundaryOp_x₀
  have h1 : EpGroupoid.frameSign (X := ε) (P.boundaryOp (oM.tangent xm)) = -1 := by
    exact if_neg frames_boundaryOp_xm
  rw [h0, h1, card_effIsotropy_of_snd_eq_zero x₀_mem_M, card_effIsotropy_of_snd_eq_zero xm_mem_M,
    card_effIsotropy_εB, card_effIsotropy_εB]
  constructor <;> norm_num <;> ring


/-! ### The `0`-forms `f(t, z) = φ(t)` -/

/-- The constant `0`-form `1` in `Ω⁰_{ep,∞}`. -/
def oneForm : AX.epFormsInfty 0 :=
  AX.epFormsInftyOf 0 0 ⟨_, (AX.lift 0).X.constForm_mem_epForms 1⟩

lemma zeroFormEval_oneForm {p : AX.Obj} (hp : p ∈ AX.X.PObj.smoothSet) :
    AX.zeroFormEval oneForm p = 1 := by
  rw [oneForm, EP.zeroFormEval_of, AX.zeroLevelEval_eq 0 _ hp (fun j => Fin.elim0 j)]
  rfl

/-- `φ_ψ(t) = ψ(2 cos θ − 2 sin θ)`, `θ = π(1 + t)/4`: a function of `t` alone. -/
def phiOf (ψ : ℝ → ℝ) (t : ℝ) : ℝ := ψ (ell2 (arcPt t))

lemma phiOf_one (ψ : ℝ → ℝ) : phiOf ψ 1 = ψ (-2) := by
  rw [← gco_x₀]; rfl

lemma phiOf_neg_one (ψ : ℝ → ℝ) : phiOf ψ (-1) = ψ 2 := by
  rw [← gco_xm]; rfl

lemma isScSmoothMap_comp_gco {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    AX.X.PObj.IsScSmoothMap realPolyfold fun y => ψ (gco y) :=
  isScSmoothMap_gco.comp_contDiff hψ

/-- **The `0`-form `f(t, z) = φ_ψ(t)`** of Remark 9.5.20, for a smooth `ψ : ℝ → ℝ`. -/
def fForm {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) : AX.epFormsInfty 0 :=
  AX.epFormsInftySmul (fun y => ψ (gco y)) 0 (isScSmoothMap_comp_gco hψ)
    (fun φ => by change ψ (gco φ.2) = ψ (gco (φ.1 • φ.2)); rw [gco_smul]) oneForm

/-- `f(t, z) = φ_ψ(t)` at the smooth points. -/
theorem zeroFormEval_fForm {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {y : AX.Obj}
    (hy : y ∈ AX.X.PObj.smoothSet) : AX.zeroFormEval (fForm hψ) y = phiOf ψ y.1.1 := by
  have h := AX.zeroFormEval_epFormsInftySmul (isScSmoothMap_comp_gco hψ)
    (fun φ => by change ψ (gco φ.2) = ψ (gco (φ.1 • φ.2)); rw [gco_smul]) oneForm y
  rw [fForm, h, zeroFormEval_oneForm hy, mul_one]
  rfl

/-- **Remark 9.5.20, `∮_Θ̂ df = (1/3)(φ(1) − φ(−1))`** (2021 p. 452) for `f(t, z) = φ(t)`,
`φ = φ_ψ`. -/
theorem remark_9_5_20_df {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
        isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
        (AX.epFormsInftyD 0 (fForm hψ)) =
      (1 / 3 : ℝ) * (phiOf ψ 1 - phiOf ψ (-1)) := by
  rw [remark_9_5_20_integral, zeroFormEval_fForm hψ (mem_smoothSet_of_snd_eq_zero x₀_mem_M),
    zeroFormEval_fForm hψ (mem_smoothSet_of_snd_eq_zero xm_mem_M)]
  rfl

/-- **The two readings differ** (Remark 9.5.20, p. 452): for `ψ = id`, `φ(1) − φ(−1) = −4`, so
`∮_Θ̂ df = ∮_{∂Θ̂} f = −4/3` with the weights of `X`, while the weights read in `∂X` give `−4`. -/
theorem remark_9_5_20_nondegenerate :
    (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
        isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
        (AX.epFormsInftyD 0 (fForm contDiff_id)) = -4 / 3 ∧
      AX.boundaryBranchedMeasureEffDim1 isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM
        isOrientation_thetaM m_hloc_LUC (fForm contDiff_id) univ = -4 / 3 ∧
      AX.zeroFormEval (fForm contDiff_id) x₀ - AX.zeroFormEval (fForm contDiff_id) xm = -4 := by
  have h0 := zeroFormEval_fForm contDiff_id (mem_smoothSet_of_snd_eq_zero x₀_mem_M)
  have h1 := zeroFormEval_fForm contDiff_id (mem_smoothSet_of_snd_eq_zero xm_mem_M)
  have e0 : phiOf id x₀.1.1 = -2 := phiOf_one id
  have e1 : phiOf id xm.1.1 = 2 := phiOf_neg_one id
  refine ⟨?_, ?_, ?_⟩
  · rw [remark_9_5_20_integral, h0, h1, e0, e1]; norm_num
  · rw [remark_9_5_20_boundary, h0, h1, e0, e1]; norm_num
  · rw [h0, h1, e0, e1]; norm_num

/-! ### Every smooth `φ` on `[−1, 1]` -/

/-- A product `χ · f` with `χ` smooth and `f` smooth on an open set containing `tsupport χ` is
smooth. -/
lemma contDiff_mul_of_tsupport_subset {χ f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ fun x => χ x * f x := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have h0 : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hs h)
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    rw [hy, Pi.zero_apply, zero_mul]

/-- **Smooth extension**: a function smooth on an open `U ⊇ [−1, 1]` agrees on `[−1, 1]` with a
function smooth on `ℝ`. -/
lemma exists_contDiff_eqOn_Icc {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc (-1 : ℝ) 1 ⊆ U) (hφ : ContDiffOn ℝ ∞ φ U) :
    ∃ φ' : ℝ → ℝ, ContDiff ℝ ∞ φ' ∧ EqOn φ' φ (Icc (-1) 1) := by
  have hI : Icc (-1 : ℝ) 1 = Metric.closedBall 0 1 := by
    rw [Real.closedBall_eq_Icc]; norm_num
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_cthickening_subset_open hU hIU
  rw [hI, cthickening_closedBall hδ.le zero_le_one] at hδU
  let χ : ContDiffBump (0 : ℝ) := ⟨1, δ + 1, one_pos, by linarith⟩
  refine ⟨fun x => χ x * φ x, contDiff_mul_of_tsupport_subset hU χ.contDiff hφ ?_,
    fun t ht => ?_⟩
  · rw [χ.tsupport_eq]; exact hδU
  · change χ t * φ t = φ t
    rw [χ.one_of_mem_closedBall (by rw [← hI]; exact ht), one_mul]

lemma two_cos_sub_two_sin (x : ℝ) :
    2 * Real.cos x - 2 * Real.sin x = 2 * √2 * Real.cos (x + π / 4) := by
  rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination (Real.sin x - Real.cos x) * h

/-- `τ(v) = (4/π) arccos(v/(2√2)) − 2`, the inverse of `t ↦ u(t) = 2 cos θ − 2 sin θ` on
`[−1, 1]`. -/
def tOfU (v : ℝ) : ℝ := 4 / π * Real.arccos (v / (2 * √2)) - 2

lemma tOfU_eq {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    tOfU (2 * Real.cos (θ t) - 2 * Real.sin (θ t)) = t := by
  have h1 := θ_mem ht
  have hs : (0 : ℝ) < √2 := by positivity
  rw [tOfU, two_cos_sub_two_sin,
    show 2 * √2 * Real.cos (θ t + π / 4) / (2 * √2) = Real.cos (θ t + π / 4) by field_simp,
    Real.arccos_cos (by linarith [h1.1, Real.pi_pos]) (by linarith [h1.2, Real.pi_pos])]
  unfold θ
  field_simp
  ring

lemma abs_two_cos_sub_two_sin_le {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |2 * Real.cos (θ t) - 2 * Real.sin (θ t)| ≤ 2 := by
  have h1 := θ_mem ht
  have hc : 0 ≤ Real.cos (θ t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [h1.1, Real.pi_pos], h1.2⟩
  have hs : 0 ≤ Real.sin (θ t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h1.1 (by linarith [h1.2, Real.pi_pos])
  have hp := Real.sin_sq_add_cos_sq (θ t)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hc hs]

lemma contDiffOn_tOfU : ContDiffOn ℝ ∞ tOfU (Metric.ball 0 (2 * √2)) := by
  intro v hv
  have hs : (0 : ℝ) < 2 * √2 := by positivity
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hv
  have h1 : v / (2 * √2) ≠ -1 := fun h => by
    rw [div_eq_iff hs.ne'] at h
    rw [h, abs_lt] at hv; linarith [hv.1]
  have h2 : v / (2 * √2) ≠ 1 := fun h => by
    rw [div_eq_iff hs.ne'] at h
    rw [h, abs_lt] at hv; linarith [hv.2]
  have hd : ContDiffAt ℝ ∞ (fun w : ℝ => w / (2 * √2)) v := contDiffAt_id.div_const _
  have ha : ContDiffAt ℝ ∞ (fun w : ℝ => Real.arccos (w / (2 * √2))) v :=
    ContDiffAt.comp (g := Real.arccos) v (Real.contDiffAt_arccos h1 h2) hd
  exact ((contDiffAt_const.mul ha).sub contDiffAt_const).contDiffWithinAt

/-- **Every function smooth near `[−1, 1]` is `ψ(2 cos θ − 2 sin θ)` for a smooth `ψ : ℝ → ℝ`**
(`θ = π(1 + t)/4`): `ψ = χ · (φ' ∘ τ)` with `τ` the inverse built from `arccos`, `φ'` a smooth
extension of `φ`, and `χ` a cut-off equal to `1` on `[−2, 2]` and supported in `[−5/2, 5/2]`. -/
theorem exists_contDiff_comp_eq {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc (-1 : ℝ) 1 ⊆ U) (hφ : ContDiffOn ℝ ∞ φ U) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, ψ (2 * Real.cos (θ t) - 2 * Real.sin (θ t)) = φ t := by
  obtain ⟨φ', hφ', hEq⟩ := exists_contDiff_eqOn_Icc hU hIU hφ
  let χ : ContDiffBump (0 : ℝ) := ⟨2, 5 / 2, two_pos, by norm_num⟩
  have h8 : (5 / 2 : ℝ) < 2 * √2 := by
    have h : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  refine ⟨fun v => χ v * φ' (tOfU v), contDiff_mul_of_tsupport_subset Metric.isOpen_ball
    χ.contDiff (hφ'.comp_contDiffOn contDiffOn_tOfU) ?_, fun t ht => ?_⟩
  · rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball h8
  · change χ _ * φ' (tOfU _) = φ t
    rw [χ.one_of_mem_closedBall ?_, one_mul, tOfU_eq ht, hEq ht]
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact abs_two_cos_sub_two_sin_le ht

lemma ell2_arcPt (t : ℝ) : ell2 (arcPt t) = 2 * Real.cos (θ t) - 2 * Real.sin (θ t) := by
  simp [ell2_apply, arcPt]

/-- **Remark 9.5.20, `∮_Θ̂ df = (1/3)(φ(1) − φ(−1))` for every `φ` smooth near `[−1, 1]`**
(2021 p. 452): for `φ` smooth on an open `U ⊇ [−1, 1]` there is a smooth `ψ` with `φ = φ_ψ` on
`[−1, 1]` (`exists_contDiff_comp_eq`), so the `0`-form `f = fForm ψ` satisfies `f(t, z) = φ(t)` at
every smooth point and `∮_Θ̂ df = (1/3)(φ(1) − φ(−1))`. -/
theorem remark_9_5_20_df_of_contDiffOn {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc (-1 : ℝ) 1 ⊆ U) (hφ : ContDiffOn ℝ ∞ φ U) :
    ∃ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ),
      (∀ y ∈ AX.X.PObj.smoothSet, AX.zeroFormEval (fForm hψ) y = φ y.1.1) ∧
      (AX.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0)
          isBranchedEpSubgroupoid_thetaM isCompactBranched_thetaM isOrientation_thetaM m_hloc_LUC
          (AX.epFormsInftyD 0 (fForm hψ)) =
        (1 / 3 : ℝ) * (φ 1 - φ (-1)) := by
  obtain ⟨ψ, hψ, heq⟩ := exists_contDiff_comp_eq hU hIU hφ
  have hphi : ∀ t ∈ Icc (-1 : ℝ) 1, phiOf ψ t = φ t := fun t ht => by
    rw [phiOf, ell2_arcPt, heq t ht]
  refine ⟨ψ, hψ, fun y hy => ?_, ?_⟩
  · rw [zeroFormEval_fForm hψ hy, hphi _ (fst_mem_Icc_of_mem y.2)]
  · rw [remark_9_5_20_df hψ, hphi 1 (by norm_num), hphi (-1) (by norm_num)]

/-! ### `∂X` is a smooth submanifold -/

lemma mem_boundary_iff' (y : XR) : y ∈ P.boundary ↔ y = xm ∨ y = x₀ := by
  rw [boundary_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma isSmoothSubmanifold_boundary_at {a : XR} (ha : a ∈ Mset) {W₀ : Set XR} (hW₀ : IsOpen W₀)
    (haW : a ∈ W₀) (hb : P.boundary ∩ W₀ = {a} ∩ W₀) :
    ∃ V : Set XR, IsOpen V ∧ a ∈ V ∧ ∃ s : XR → XR, P.IsScPlusRetractionOn s V ∧
      s '' V = P.boundary ∩ V := by
  obtain ⟨V, hV, haV, s, hs, himg⟩ :=
    MPolyfold.isSmoothSubmanifold_singleton (mem_smoothSet_of_snd_eq_zero ha) a rfl
  have hsa : ∀ y ∈ V, s y = a := fun y hy => (himg ▸ mem_image_of_mem s hy : s y ∈ {a} ∩ V).1
  refine ⟨V ∩ W₀, hV.inter hW₀, ⟨haV, haW⟩, s,
    hs.mono (hV.inter hW₀) inter_subset_left fun y hy => by rw [hsa y hy.1]; exact ⟨haV, haW⟩, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hsa z hz.1]
    have : a ∈ P.boundary ∩ W₀ := by rw [hb]; exact ⟨rfl, haW⟩
    exact ⟨this.1, haV, haW⟩
  · rintro ⟨hyb, hyV, hyW⟩
    have : y ∈ {a} ∩ W₀ := hb ▸ ⟨hyb, hyW⟩
    rw [this.1]
    exact ⟨a, ⟨haV, haW⟩, hsa a haV⟩

/-- **`∂X = {(−1, 0), (1, 0)}` is a smooth submanifold of `X`** (Remark 9.5.20, p. 452;
Definition 4.2.1): near each of its two points the constant map is an sc⁺-retraction. -/
theorem isSmoothSubmanifold_boundary : P.IsSmoothSubmanifold P.boundary := by
  intro a ha
  rcases (mem_boundary_iff' a).1 ha with rfl | rfl
  · refine isSmoothSubmanifold_boundary_at xm_mem_M isOpen_U1 xm_mem_U1 ?_
    ext y
    simp only [mem_inter_iff, mem_singleton_iff, mem_boundary_iff']
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact ⟨rfl, h⟩
      · exact absurd h x₀_not_mem_U1
    · rintro ⟨rfl, h⟩; exact ⟨Or.inl rfl, h⟩
  · refine isSmoothSubmanifold_boundary_at x₀_mem_M isOpen_U2 x₀_mem_U2 ?_
    ext y
    simp only [mem_inter_iff, mem_singleton_iff, mem_boundary_iff']
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact absurd h xm_not_mem_U2
      · exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact ⟨Or.inr rfl, h⟩

end DimensionJump

end Polyfold
