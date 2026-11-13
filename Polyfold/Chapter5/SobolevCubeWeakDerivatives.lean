import Polyfold.Chapter5.SobolevCubeVolterra

/-!
# The sc-structure `W^{1+m,p}` on a cube, part 2: weak derivatives on `(0,1)`

Continuation of `SobolevCubeVolterra` (2021 §5.5, the remark after Theorem 5.5.5, pp. 230–231).
One-dimensional facts on `I = (0,1)`:

* `IsTestI`: test functions on `I`; `toLpS f`: a continuous `f : ℝ → ℝ` as an element of `Lᵖ(I)`;
  `cst c`: the constant `c`, `‖cst c‖ = |c|`;
* `integral_iteratedDeriv_mul`: integration by parts, `∫_I ψ^{(j)} f = (−1)^j ∫_I ψ f^{(j)}` for `f`
  smooth and `ψ` a test function;
* `denseRange_poly`: polynomials are dense in `Lᵖ(I)` (continuous functions are dense, and
  Weierstrass);
* `V_toLpS`: `V f = ∫₀ˣ f` for continuous `f`; `integral_deriv_mul_V`: `(V g)' = g` weakly;
* `eq_cst_of_weakDeriv_zero` (du Bois-Reymond): a function of `Lᵖ(I)` whose weak derivative
  vanishes is constant;
* **`eq_cst_add_V`**: if `g` is the weak derivative of `v` on `I`, then `v = c + V g`.
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevCube

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-! ### Continuous functions as elements of `Lᵖ(I)` -/

lemma memLp_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (q : ℝ≥0∞) : MemLp f q μI := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx =>
    hC x (Ioo_subset_Icc_self hx))

/-- A continuous function as an element of `Lᵖ(I)`. -/
def toLpS (f : ℝ → ℝ) (hf : Continuous f) : L p := (memLp_of_continuous hf _).toLp f

lemma coeFn_toLpS {f : ℝ → ℝ} (hf : Continuous f) : (toLpS (p := p) f hf : ℝ → ℝ) =ᵐ[μI] f :=
  MemLp.coeFn_toLp _

lemma toLpS_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    toLpS (p := p) (f - g) (hf.sub hg) = toLpS (p := p) f hf - toLpS (p := p) g hg := by
  rw [toLpS, toLpS, toLpS, ← MemLp.toLp_sub]

lemma toLpS_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    toLpS (p := p) (f + g) (hf.add hg) = toLpS (p := p) f hf + toLpS (p := p) g hg := by
  rw [toLpS, toLpS, toLpS, ← MemLp.toLp_add]

/-- The constant function `c` in `Lᵖ(I)`. -/
def cst (c : ℝ) : L p := toLpS (fun _ => c) continuous_const

lemma norm_cst (c : ℝ) : ‖(cst c : L p)‖ = |c| := by
  rw [cst, toLpS, Lp.norm_toLp, eLpNorm_const _ (by simpa using (p_pos (p := p)))
    (by simp [μI] : μI ≠ 0), μI_univ, ENNReal.one_rpow, mul_one]
  simp

/-! ### Test functions on `I` -/

/-- Test functions on `I`: smooth, compactly supported in `I`. -/
def IsTestI (ψ : ℝ → ℝ) : Prop := ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ I

lemma IsTestI.deriv {ψ : ℝ → ℝ} (h : IsTestI ψ) : IsTestI (deriv ψ) :=
  ⟨(contDiff_infty_iff_deriv.1 h.1).2, h.2.1.deriv, tsupport_deriv_subset.trans h.2.2⟩

lemma IsTestI.iteratedDeriv {ψ : ℝ → ℝ} (h : IsTestI ψ) (j : ℕ) :
    IsTestI (iteratedDeriv j ψ) := by
  induction j with
  | zero => simpa using h
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma IsTestI.eq_zero {ψ : ℝ → ℝ} (h : IsTestI ψ) {x : ℝ} (hx : x ∉ I) : ψ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' => hx (h.2.2 h')

lemma IsTestI.continuous {ψ : ℝ → ℝ} (h : IsTestI ψ) : Continuous ψ := h.1.continuous

/-- `∫_I ψ = ∫_ℝ ψ` for a function vanishing outside `I`. -/
lemma integral_μI_eq {f : ℝ → ℝ} (hf : ∀ x, x ∉ I → f x = 0) : ∫ x, f x ∂μI = ∫ x, f x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero hf

lemma integrable_cont_mul {ψ : ℝ → ℝ} (hψ : Continuous ψ) (w : L p) :
    Integrable (fun x => ψ x * w x) μI := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hψ.continuousOn
  exact (integrable_L w).bdd_mul hψ.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx =>
      hC x (Ioo_subset_Icc_self hx)))

/-- The pairing `h ↦ ∫_I w h` with a continuous `w`, a continuous linear form on `Lᵖ(I)`. -/
def pairI (w : ℝ → ℝ) (hw : Continuous w) : L p →L[ℝ] ℝ :=
  (BonicFrampton.wMul 1 SobolevRemark.conjE_hq (memLp_of_continuous hw _)).toContinuousLinearMap
    (fun _ => 0) 0

lemma pairI_apply (w : ℝ → ℝ) (hw : Continuous w) (h : L p) :
    pairI w hw h = ∫ x, w x * h x ∂μI := by
  simp [pairI, BonicFrampton.wMul_apply]

lemma pairI_cst (w : ℝ → ℝ) (hw : Continuous w) (c : ℝ) :
    pairI w hw (cst (p := p) c) = c * ∫ x, w x ∂μI := by
  rw [pairI_apply, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toLpS (p := p) (continuous_const (y := c))] with x hx
  rw [cst, hx]; ring

/-! ### Integration by parts -/

/-- **Integration by parts on `I`**: `∫_I ψ' f = −∫_I ψ f'`. -/
lemma integral_deriv_mul {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {ψ : ℝ → ℝ} (hψ : IsTestI ψ) :
    ∫ x, deriv ψ x * f x ∂μI = -∫ x, ψ x * deriv f x ∂μI := by
  have hψ' := hψ.deriv
  rw [integral_μI_eq fun x hx => by rw [hψ'.eq_zero hx, zero_mul],
    integral_μI_eq fun x hx => by rw [hψ.eq_zero hx, zero_mul]]
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdψ : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    ((hψ.1.differentiable (by simp)) x).hasDerivAt
  have hdf' : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf.differentiable one_ne_zero) x).hasDerivAt
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := ψ) (v := f) (u' := deriv ψ)
    (v' := deriv f) (fun x _ => hdψ x) (fun x _ => hdf' x)
    ((hψ.continuous.mul hdf).integrable_of_hasCompactSupport hψ.2.1.mul_right)
    ((hψ'.continuous.mul hf.continuous).integrable_of_hasCompactSupport hψ'.2.1.mul_right)
    ((hψ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_right)
  linarith

/-- **Iterated integration by parts on `I`**: `∫_I ψ^{(j)} f = (−1)^j ∫_I ψ f^{(j)}`. -/
lemma integral_iteratedDeriv_mul {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ∀ {ψ : ℝ → ℝ}, IsTestI ψ →
      ∫ x, iteratedDeriv j ψ x * f x ∂μI = (-1) ^ j * ∫ x, ψ x * iteratedDeriv j f x ∂μI := by
  induction j with
  | zero => intro ψ _; simp
  | succ j ih =>
    intro ψ hψ
    have hfj : ContDiff ℝ 1 (iteratedDeriv j f) := by
      rw [iteratedDeriv_eq_iterate]; exact (hf.iterate_deriv j).of_le (by simp)
    rw [iteratedDeriv_succ', ih hψ.deriv, integral_deriv_mul hfj hψ, ← iteratedDeriv_succ,
      pow_succ]
    ring

/-! ### The primitive of a continuous function -/

/-- The primitive `x ↦ ∫₀ˣ f`. -/
def prim (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, f t

lemma hasDerivAt_prim {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) : HasDerivAt (prim f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma deriv_prim {f : ℝ → ℝ} (hf : Continuous f) : deriv (prim f) = f :=
  funext fun x => (hasDerivAt_prim hf x).deriv

lemma continuous_prim {f : ℝ → ℝ} (hf : Continuous f) : Continuous (prim f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_prim hf x).continuousAt

lemma contDiff_prim {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (prim f) :=
  contDiff_infty_iff_deriv.2 ⟨fun x => (hasDerivAt_prim hf.continuous x).differentiableAt,
    by rw [deriv_prim hf.continuous]; exact hf⟩

/-- `Vf (toLpS f) x = ∫₀ˣ f` for `0 ≤ x < 1`. -/
lemma Vf_toLpS {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Vf (toLpS (p := p) f hf) x = prim f x := by
  rw [Vf_eq _ h0, prim, intervalIntegral.integral_of_le h0]
  rw [setIntegral_congr_ae measurableSet_Ioc
    ((coeFn_toLpS (p := p) hf).mono fun t ht _ => ht)]
  rw [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Ioo_right h1)]

/-- **`V f = ∫₀ˣ f`** for continuous `f`. -/
lemma V_toLpS {f : ℝ → ℝ} (hf : Continuous f) :
    V (toLpS (p := p) f hf) = toLpS (prim f) (continuous_prim hf) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_V (toLpS (p := p) f hf), coeFn_toLpS (p := p) (continuous_prim hf),
    ae_restrict_mem measurableSet_Ioo] with x e1 e2 hx
  rw [e1, e2, Vf_toLpS hf hx.1.le hx.2]

/-! ### Density of polynomials -/

lemma poly_contDiff (P : Polynomial ℝ) : ContDiff ℝ ∞ (fun x => P.eval x) := by
  simpa using P.contDiff_aeval (𝕜 := ℝ) ∞

/-- **Polynomials are dense in `Lᵖ(I)`.** -/
theorem denseRange_poly :
    DenseRange (fun P : Polynomial ℝ => toLpS (p := p) (fun x => P.eval x) P.continuous) := by
  have hp : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ μI ℝ hp
  refine Metric.denseRange_iff.2 fun g ε hε => ?_
  obtain ⟨F, hF⟩ := Metric.denseRange_iff.1 hd g (ε / 2) (by positivity)
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 F F.continuous.continuousOn
    (ε / 2) (by positivity)
  refine ⟨P, ?_⟩
  have h2 : dist (BoundedContinuousFunction.toLp (ENNReal.ofReal p) μI ℝ F)
      (toLpS (p := p) (fun x => P.eval x) P.continuous) ≤ ε / 2 := by
    rw [dist_eq_norm]
    refine norm_le_of_ae_bound' (by positivity) ?_
    filter_upwards [Lp.coeFn_sub (BoundedContinuousFunction.toLp (ENNReal.ofReal p) μI ℝ F)
      (toLpS (p := p) (fun x => P.eval x) P.continuous),
      BoundedContinuousFunction.coeFn_toLp (ENNReal.ofReal p) μI ℝ F,
      coeFn_toLpS (p := p) P.continuous, ae_restrict_mem measurableSet_Ioo] with x e1 e2 e3 hx
    rw [e1, Pi.sub_apply, e2, e3, Real.norm_eq_abs, abs_sub_comm]
    exact (hP x (Ioo_subset_Icc_self hx)).le
  calc dist g _ ≤ dist g (BoundedContinuousFunction.toLp (ENNReal.ofReal p) μI ℝ F) +
        dist (BoundedContinuousFunction.toLp (ENNReal.ofReal p) μI ℝ F) _ := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hF h2
    _ = ε := add_halves ε

/-! ### `V g` has weak derivative `g` -/

/-- **`(V g)' = g` weakly**: `∫_I ψ' · V g = −∫_I ψ g` for every test function `ψ`. -/
theorem integral_deriv_mul_V {ψ : ℝ → ℝ} (hψ : IsTestI ψ) (g : L p) :
    ∫ x, deriv ψ x * V g x ∂μI = -∫ x, ψ x * g x ∂μI := by
  have key := denseRange_poly (p := p) |>.equalizer
    ((pairI (deriv ψ) hψ.deriv.continuous).comp V).continuous
    (-(pairI (p := p) ψ hψ.continuous)).continuous
    (funext fun P => by
      simp only [comp_apply, ContinuousLinearMap.coe_comp, neg_apply]
      rw [V_toLpS, pairI_apply, pairI_apply]
      have e1 : ∫ x, deriv ψ x * (toLpS (p := p) (prim fun x => P.eval x)
          (continuous_prim P.continuous) : ℝ → ℝ) x ∂μI =
          ∫ x, deriv ψ x * prim (fun x => P.eval x) x ∂μI :=
        integral_congr_ae ((coeFn_toLpS (p := p) (continuous_prim P.continuous)).mono
          fun x hx => by dsimp only; rw [hx])
      have e2 : ∫ x, ψ x * (toLpS (p := p) (fun x => P.eval x) P.continuous : ℝ → ℝ) x ∂μI =
          ∫ x, ψ x * P.eval x ∂μI :=
        integral_congr_ae ((coeFn_toLpS (p := p) P.continuous).mono
          fun x hx => by dsimp only; rw [hx])
      rw [e1, e2, integral_deriv_mul ((contDiff_prim (poly_contDiff P)).of_le (by simp)) hψ,
        deriv_prim P.continuous])
  have := congrFun key g
  simpa [pairI_apply] using this

/-! ### du Bois-Reymond -/

/-- A function of `Lᵖ(I)` integrating to `0` against every test function vanishes. -/
lemma eq_zero_of_test (h : L p) (hh : ∀ φ, IsTestI φ → ∫ x, φ x * h x ∂μI = 0) : h = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hli : LocallyIntegrableOn (h : ℝ → ℝ) I μI :=
    ((Lp.memLp h).locallyIntegrable hP.out).locallyIntegrableOn I
  have := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli
    fun g hg hgc hgs => by simpa [smul_eq_mul] using hh g ⟨hg, hgc, hgs⟩
  filter_upwards [this, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  exact hx hxI

/-- A fixed test function `ψ₀` on `I` with `∫ ψ₀ = 1`. -/
def bump0 : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- `ψ₀`, a normalized bump supported in `[1/4, 3/4]`. -/
def ψ0 : ℝ → ℝ := bump0.normed volume

lemma isTestI_ψ0 : IsTestI ψ0 := by
  refine ⟨bump0.contDiff_normed, bump0.hasCompactSupport_normed, ?_⟩
  rw [ψ0, bump0.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have : bump0.rOut = 1 / 4 := rfl
  rw [this] at hx
  constructor <;> linarith [hx.1, hx.2]

lemma integral_ψ0 : ∫ x, ψ0 x = 1 := bump0.integral_normed

/-- A compact subset of `(0,1)` lies in some `[a, b]` with `0 < a ≤ b < 1`. -/
lemma exists_Icc_of_compact {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ I) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ b < 1 ∧ K ⊆ Icc a b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1 / 2, 1 / 2, by norm_num, le_rfl, by norm_num, empty_subset _⟩
  · refine ⟨sInf K, sSup K, (hKI (hK.sInf_mem hne)).1,
      csInf_le_csSup hne hK.bddBelow hK.bddAbove, (hKI (hK.sSup_mem hne)).2,
      fun x hx => ⟨csInf_le hK.bddBelow hx, le_csSup hK.bddAbove hx⟩⟩

/-- The primitive of a test function with total integral `0` is a test function. -/
lemma isTestI_prim {h : ℝ → ℝ} (hh : IsTestI h) (h0 : ∫ x, h x = 0) : IsTestI (prim h) := by
  obtain ⟨a, b, ha, hab', hb, hab⟩ := exists_Icc_of_compact hh.2.1 hh.2.2
  have hz : ∀ t, t ∉ Icc a b → h t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h' => ht (hab h')
  have hout : ∀ x, x ∉ Icc a b → prim h x = 0 := by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [prim, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_,
        intervalIntegral.integral_zero]
      intro t ht
      refine hz t fun h' => ?_
      rw [uIcc, mem_Icc] at ht
      have : t ≤ max 0 x := ht.2
      rcases le_total 0 x with h0x | h0x
      · rw [max_eq_right h0x] at this; linarith [h'.1]
      · rw [max_eq_left h0x] at this; linarith [h'.1]
    · have hx0 : 0 ≤ x := by linarith
      rw [prim, intervalIntegral.integral_of_le hx0,
        setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 x) fun t ht => hz t fun h' =>
          ht ⟨by linarith [h'.1], by linarith [h'.2]⟩, h0]
  refine ⟨contDiff_prim hh.1, HasCompactSupport.intro isCompact_Icc hout, ?_⟩
  have hsub : tsupport (prim h) ⊆ Icc a b :=
    closure_minimal (fun x hx => by by_contra h'; exact hx (hout x h')) isClosed_Icc
  exact hsub.trans (Icc_subset_Ioo ha hb)

lemma IsTestI.sub_mul {φ ψ : ℝ → ℝ} (hφ : IsTestI φ) (hψ : IsTestI ψ) (a : ℝ) :
    IsTestI (fun x => φ x - a * ψ x) := by
  refine ⟨hφ.1.sub (contDiff_const.mul hψ.1), hφ.2.1.sub hψ.2.1.mul_left, ?_⟩
  refine (closure_minimal (fun x hx => ?_)
    ((isClosed_tsupport φ).union (isClosed_tsupport ψ))).trans (union_subset hφ.2.2 hψ.2.2)
  by_contra h'
  rw [mem_union, not_or] at h'
  have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport h'.1
  have h2 : ψ x = 0 := image_eq_zero_of_notMem_tsupport h'.2
  exact hx (by simp [h1, h2])

lemma integrable_test {φ : ℝ → ℝ} (hφ : IsTestI φ) : Integrable φ :=
  hφ.continuous.integrable_of_hasCompactSupport hφ.2.1

/-- **du Bois-Reymond**: a function of `Lᵖ(I)` with weak derivative `0` is constant,
`w = ∫_I ψ₀ w`. -/
theorem eq_cst_of_weakDeriv_zero (w : L p)
    (hw : ∀ ψ, IsTestI ψ → ∫ x, deriv ψ x * w x ∂μI = 0) :
    w = cst (∫ x, ψ0 x * w x ∂μI) := by
  set c := ∫ x, ψ0 x * w x ∂μI
  rw [← sub_eq_zero]
  refine eq_zero_of_test _ fun φ hφ => ?_
  set a := ∫ x, φ x
  have hh := hφ.sub_mul isTestI_ψ0 a
  have hint : ∫ x, (φ x - a * ψ0 x) = 0 := by
    rw [integral_sub (integrable_test hφ) ((integrable_test isTestI_ψ0).const_mul a),
      integral_const_mul, integral_ψ0, mul_one, sub_self]
  have h1 := hw _ (isTestI_prim hh hint)
  rw [deriv_prim hh.continuous] at h1
  have h2 : ∫ x, (φ x - a * ψ0 x) * w x ∂μI =
      ∫ x, φ x * w x ∂μI - a * ∫ x, ψ0 x * w x ∂μI := by
    rw [← integral_const_mul, ← integral_sub (integrable_cont_mul hφ.continuous w)
      ((integrable_cont_mul isTestI_ψ0.continuous w).const_mul a)]
    congr 1; funext x; ring
  rw [h2] at h1
  rw [← pairI_apply φ hφ.continuous, map_sub, pairI_apply, pairI_cst,
    integral_μI_eq (fun x hx => hφ.eq_zero hx)]
  change ∫ x, φ x * w x ∂μI - a * c = 0 at h1
  linarith

/-- **Weak derivatives on `I` integrate**: if `g` is the weak derivative of `v`
(`∫_I ψ' v = −∫_I ψ g` for every test function `ψ`), then `v = c + V g` for a constant `c`. -/
theorem eq_cst_add_V (v g : L p)
    (h : ∀ ψ, IsTestI ψ → ∫ x, deriv ψ x * v x ∂μI = -∫ x, ψ x * g x ∂μI) :
    ∃ c : ℝ, v = cst c + V g := by
  refine ⟨_, sub_eq_iff_eq_add.1 (eq_cst_of_weakDeriv_zero (v - V g) fun ψ hψ => ?_)⟩
  rw [← pairI_apply _ hψ.deriv.continuous, map_sub, pairI_apply, pairI_apply,
    integral_deriv_mul_V hψ, h ψ hψ, sub_self]

end SobolevCube

end Polyfold
