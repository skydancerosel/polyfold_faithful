import GWMemoir.Skeleton

/-!
Witnesses that the definitions of `GWMemoir.Skeleton` (HWZ, *Applications of Polyfold Theory I*,
Memoirs AMS 248, no. 1179, §1.1) are satisfiable in a non-degenerate case.

* The target: `ℝ²` with `ω₀ = dx ∧ dy` (`omE2`) and the compatible `J₀` (`jE2`,
  `isCompatible_E2`).
* The round sphere `S² ⊂ ℝ³` (Mathlib's stereographic atlas, model `E2`) with its standard almost
  complex structure `j_x v = x × v` (`jStd`): `J² = -1`, and smoothness in tangent coordinates
  (through the radial retraction `ℝ³ ∖ 0 → S²` and `ContMDiffAt.mfderiv`).
* `holChart s`: the stereographic coordinates `σ_s(y) = (y₀ - s i y₁)/(1 - s y₂)`, `s = ±1`, are
  `j`-holomorphic charts onto `ℂ` (`holChart_holo`), as `IsHolChart` asks.
* `memH_cutoff_mul_const`: the cut-off of `IsHlocNear` lies in `H^{k,δ}(ℝ × S¹)`.
* `sphere3 : NodalSurface 3`: `(S², j, (e₀, e₁, e₂), ∅)` (Memoir Definition 1.2).
* `sphereNode : NodalSurface 1`: the sphere with the nodal pair `{e₂, -e₂}` and the marked point
  `e₀`.
* `constStableMap om q k δ : StableMap om 3 k δ` and `nodalStableMap om q k δ : StableMap om 1 k δ`:
  constant maps into any `(Q, ω)` are stable maps of class `(k, δ)` for every `k, δ` (Memoir
  Definition 1.4): of class `(k, δ)` at the nodal points in the charts `σ_{∓1}`, `H^k_loc`
  elsewhere, area zero, and the only component carries three special points.
-/

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Function Metric MeasureTheory Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The target `(ℝ², ω₀, J₀)` -/

/-- `ω₀(v, w) = v₀ w₁ - v₁ w₀` on `ℝ²`. -/
def om0 : E2 →L[ℝ] E2 →L[ℝ] ℝ :=
  (EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).smulRight (EuclideanSpace.proj 1 : E2 →L[ℝ] ℝ) -
    (EuclideanSpace.proj 1 : E2 →L[ℝ] ℝ).smulRight (EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ)

theorem om0_apply (v w : E2) : om0 v w = v 0 * w 1 - v 1 * w 0 := by
  simp [om0]

/-- `J₀ v = (-v₁, v₀)`. -/
def J0 : E2 →L[ℝ] E2 :=
  (EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).smulRight (EuclideanSpace.single 1 1) -
    (EuclideanSpace.proj 1 : E2 →L[ℝ] ℝ).smulRight (EuclideanSpace.single 0 1)

theorem J0_apply_zero (v : E2) : J0 v 0 = -v 1 := by simp [J0]
theorem J0_apply_one (v : E2) : J0 v 1 = v 0 := by simp [J0]

theorem inChart_model (σ : E2 → E2 →L[ℝ] E2 →L[ℝ] ℝ) (x₀ : E2) :
    inChart σ x₀ = σ := by
  funext y
  simp only [inChart, tangentCoordChange, tangentBundleCore_coordChange_model_space]
  ext v w
  simp [chartAt_self_eq]

/-- The standard symplectic form of `ℝ²` (as a manifold). -/
def omE2 : SymplecticForm E2 E2 where
  form _ := om0
  antisymm _ v w := by rw [om0_apply, om0_apply]; ring
  nondeg _ v h := by
    have h0 := h (EuclideanSpace.single 1 1)
    have h1 := h (EuclideanSpace.single 0 1)
    simp [om0_apply] at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  smooth x₀ := by rw [inChart_model]; exact contDiffOn_const
  closed x₀ y _ a b c := by rw [inChart_model]; simp

/-- The standard complex structure of `ℝ²`. -/
def jE2 : AlmostComplexStructure E2 E2 where
  J _ := J0
  sq _ := by
    refine ContinuousLinearMap.ext fun v => ?_
    ext i; fin_cases i <;> simp [J0_apply_zero, J0_apply_one]
  smooth x₀ := by rw [inTangentCoordinates_model_space]; exact contMDiffAt_const

theorem isCompatible_E2 : IsCompatible omE2 jE2 := by
  refine ⟨fun _ v w => ?_, fun _ v hv => ?_⟩
  · show om0 (J0 v) (J0 w) = om0 v w
    rw [om0_apply, om0_apply, J0_apply_zero, J0_apply_one, J0_apply_zero, J0_apply_one]; ring
  · show 0 < om0 v (J0 v)
    rw [om0_apply, J0_apply_zero, J0_apply_one]
    have : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h; push Not at h; apply hv; ext i; fin_cases i <;> simp [h.1, h.2]
    rcases this with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (v 0)]


/-! ## 2. The sphere and its almost complex structure -/

/-- `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The round sphere `S² ⊂ ℝ³`, a smooth surface through Mathlib's stereographic atlas. -/
abbrev S2 := sphere (0 : E3) 1

instance fact_finrank_E3 : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

/-- The charts of `S²` are onto `ℝ²`. -/
theorem S2_target (x : S2) : (extChartAt 𝓘(ℝ, E2) x).target = univ := by
  rw [extChartAt_target]
  have : (chartAt E2 x).target = univ := stereographic'_target (n := 2) (-x)
  simp [this]

/-- `ℝ³ ∖ 0`. -/
def U0 : TopologicalSpace.Opens E3 := ⟨{y | y ≠ 0}, isOpen_ne⟩

theorem norm_normalize (y : U0) : ‖‖(y : E3)‖⁻¹ • (y : E3)‖ = 1 := by
  have : (y : E3) ≠ 0 := y.2
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 this)]

/-- `y ↦ y / ‖y‖` on `ℝ³ ∖ 0`. -/
def retrU : U0 → S2 := Set.codRestrict (fun y : U0 => ‖(y : E3)‖⁻¹ • (y : E3)) _
  (fun y => by simpa using norm_normalize y)

theorem contMDiff_retrU : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ retrU := by
  apply ContMDiff.codRestrict_sphere
  intro y
  rw [contMDiffAt_subtype_iff (f := fun y : E3 => ‖y‖⁻¹ • y)]
  have hy : (y : E3) ≠ 0 := y.2
  apply ContDiffAt.contMDiffAt
  exact ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.2 hy)).smul contDiffAt_id

/-- The unit vectors `e_i` as points of `S²`. -/
def pt (i : Fin 3) : S2 := ⟨EuclideanSpace.single i 1, by simp⟩

open Classical in
/-- The radial retraction `y ↦ y / ‖y‖`, extended by `e₀` at `0`; smooth near `S²`. -/
def retr (y : E3) : S2 := if h : y ≠ 0 then retrU ⟨y, h⟩ else pt 0

theorem retr_coe (x : S2) : retr x = x := by
  have hx : (x : E3) ≠ 0 := ne_zero_of_mem_unit_sphere x
  rw [retr, dif_pos hx]
  apply Subtype.ext
  show ‖(x : E3)‖⁻¹ • (x : E3) = x
  rw [norm_eq_of_mem_sphere x, inv_one, one_smul]

theorem contMDiffAt_retr (x : S2) : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ retr x := by
  have hx : (x : E3) ≠ 0 := ne_zero_of_mem_unit_sphere x
  have : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ (fun y : U0 => retr y) ⟨x, hx⟩ := by
    refine (contMDiff_retrU ⟨x, hx⟩).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    show retr y = retrU y
    have hy : (y : E3) ≠ 0 := y.2
    rw [retr, dif_pos hy]
  exact contMDiffAt_subtype_iff.1 this

/-- The cross product `x × ·` on `ℝ³`. -/
def crossL : E3 →L[ℝ] E3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap
        ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap ∘ₗ crossProduct (WithLp.ofLp x) ∘ₗ
          (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap)
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by ext v; simp }

theorem crossL_apply (x a : E3) :
    crossL x a = WithLp.toLp 2 (crossProduct (WithLp.ofLp x) (WithLp.ofLp a)) := rfl

theorem inner_crossL_self (x a : E3) : inner ℝ x (crossL x a) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, crossL_apply]
  simp only [star_trivial]
  rw [dotProduct_comm]
  exact dot_self_cross _ _

theorem crossL_crossL (x a : E3) :
    crossL x (crossL x a) = inner ℝ x a • x - inner ℝ x x • a := by
  simp only [crossL_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [cross_cross_eq_smul_sub_smul', dotProduct_comm (WithLp.ofLp a) (WithLp.ofLp x)]
  rfl

/-- The tangent map of the inclusion `S² → ℝ³` (onto `x^⊥`). -/
def incD (x : S2) : E2 →L[ℝ] E3 := mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (Subtype.val : S2 → E3) x

/-- The tangent map of the retraction, a left inverse of `incD`. -/
def retrD (x : S2) : E3 →L[ℝ] E2 := mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E2) retr (x : E3)

theorem retrD_incD (x : S2) (v : E2) : retrD x (incD x v) = v := by
  have h := mfderiv_comp x ((contMDiffAt_retr x).mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (m := ∞) (n := 2) x).mdifferentiableAt (by simp))
  have hid : retr ∘ (Subtype.val : S2 → E3) = id := funext retr_coe
  rw [hid, mfderiv_id] at h
  exact (congrArg (fun L => L v) h).symm

set_option linter.deprecated false in
theorem range_incD (x : S2) : (incD x).range = (ℝ ∙ (x : E3))ᗮ :=
  range_mfderiv_coe_sphere (n := 2) x

theorem incD_retrD_of_perp (x : S2) {w : E3} (hw : inner ℝ (x : E3) w = 0) :
    incD x (retrD x w) = w := by
  have : w ∈ (incD x).range := by
    rw [range_incD]; exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 hw
  obtain ⟨e, he⟩ := this
  have he' : incD x e = w := he
  rw [← he', retrD_incD]

theorem inner_incD (x : S2) (v : E2) : inner ℝ (x : E3) (incD x v) = 0 := by
  have : incD x v ∈ (ℝ ∙ (x : E3))ᗮ := by rw [← range_incD]; exact ⟨v, rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 this

/-- The standard almost complex structure of `S²`: `j_x v = x × v` on `T_x S² = x^⊥`, read in the
chart at `x`. -/
def jStdMap (x : S2) : E2 →L[ℝ] E2 := (retrD x).comp ((crossL x).comp (incD x))

theorem jStdMap_sq (x : S2) : (jStdMap x).comp (jStdMap x) = -ContinuousLinearMap.id ℝ _ := by
  refine ContinuousLinearMap.ext fun e => ?_
  show retrD x (crossL x (incD x (retrD x (crossL x (incD x e))))) = -e
  rw [incD_retrD_of_perp x (inner_crossL_self _ _), crossL_crossL, inner_incD,
    real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]
  simp [retrD_incD]

theorem top_add_one_le : (∞ : ℕ∞ω) + 1 ≤ ∞ := by simp

/-- `j` is smooth: in tangent coordinates it is the product of the smooth maps `T retr`, `x × ·`
and `T ι` (`ContMDiffAt.mfderiv`). -/
theorem jStdMap_smooth (x₀ : S2) : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E2 →L[ℝ] E2) ∞
    (inTangentCoordinates 𝓘(ℝ, E2) 𝓘(ℝ, E2) id id jStdMap x₀) x₀ := by
  have hA : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E2 →L[ℝ] E3) ∞
      (inTangentCoordinates 𝓘(ℝ, E2) 𝓘(ℝ, E3) id (Subtype.val : S2 → E3) incD x₀) x₀ :=
    (contMDiff_coe_sphere (m := ∞) (n := 2) x₀).mfderiv_const top_add_one_le
  have hf : ContMDiffAt (𝓘(ℝ, E2).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E2) ∞
      (Function.uncurry fun _ : S2 => retr) (x₀, (x₀ : E3)) :=
    (contMDiffAt_retr x₀).comp (x₀, (x₀ : E3)) contMDiffAt_snd
  have hB := ContMDiffAt.mfderiv (fun _ : S2 => retr) (Subtype.val : S2 → E3) hf
    (contMDiff_coe_sphere (m := ∞) (n := 2) x₀) top_add_one_le
  have hC : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E3 →L[ℝ] E3) ∞ (fun x : S2 => crossL x) x₀ :=
    (crossL.contMDiff.comp (contMDiff_coe_sphere (m := ∞) (n := 2))) x₀
  have hBCA := hB.clm_comp (hC.clm_comp hA)
  have key : (inTangentCoordinates 𝓘(ℝ, E2) 𝓘(ℝ, E2) id id jStdMap x₀) =ᶠ[nhds x₀]
      fun x => (inTangentCoordinates 𝓘(ℝ, E3) 𝓘(ℝ, E2) Subtype.val (fun x : S2 => retr x)
        (fun x : S2 => retrD x) x₀ x).comp ((crossL x).comp
          (inTangentCoordinates 𝓘(ℝ, E2) 𝓘(ℝ, E3) id Subtype.val incD x₀ x)) := by
    filter_upwards [(chartAt E2 x₀).open_source.mem_nhds (mem_chart_source E2 x₀)] with x hx
    have hy : (x : E3) ∈ (chartAt E3 (x₀ : E3)).source := by rw [chartAt_self_eq]; trivial
    have hx' : retr x ∈ (chartAt E2 (retr x₀)).source := by rw [retr_coe, retr_coe]; exact hx
    rw [inTangentCoordinates_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E2)) id id jStdMap hx hx,
      inTangentCoordinates_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E3)) id Subtype.val incD hx hy,
      inTangentCoordinates_eq (I := 𝓘(ℝ, E3)) (I' := 𝓘(ℝ, E2)) Subtype.val (fun x : S2 => retr x)
        (fun x : S2 => retrD x) hy hx']
    simp only [retr_coe, id, tangentBundleCore_coordChange_model_space,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_assoc,
      jStdMap]
  exact hBCA.congr_of_eventuallyEq key


/-! ## 3. Holomorphic stereographic charts -/

theorem S2_sq (y : S2) : (y : E3) 0 ^ 2 + (y : E3) 1 ^ 2 + (y : E3) 2 ^ 2 = 1 := by
  have h := norm_eq_of_mem_sphere y
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three] at h
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- The stereographic coordinate `σ_s(y) = (y₀ - s i y₁) / (1 - s y₂)` (`s = ±1`), centred at
`-s e₂`. -/
def stereoC (s : ℝ) (y : E3) : ℂ :=
  ((y 0 : ℂ) - s * Complex.I * (y 1 : ℂ)) * (((1 - s * y 2)⁻¹ : ℝ) : ℂ)

/-- Its inverse `z ↦ (2 re z, -2 s im z, s (|z|² - 1)) / (|z|² + 1)`. -/
def stereoCInv (s : ℝ) (z : ℂ) : E3 :=
  (Complex.normSq z + 1)⁻¹ • WithLp.toLp 2 ![2 * z.re, -2 * s * z.im, s * (Complex.normSq z - 1)]

theorem stereoCInv_apply (s : ℝ) (z : ℂ) :
    stereoCInv s z 0 = 2 * z.re / (Complex.normSq z + 1) ∧
    stereoCInv s z 1 = -2 * s * z.im / (Complex.normSq z + 1) ∧
    stereoCInv s z 2 = s * (Complex.normSq z - 1) / (Complex.normSq z + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [stereoCInv, div_eq_inv_mul]

theorem stereoCInv_mem (s : ℝ) (hs : s ^ 2 = 1) (z : ℂ) : stereoCInv s z ∈ sphere (0 : E3) 1 := by
  obtain ⟨h0, h1, h2⟩ := stereoCInv_apply s z
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, h0, h1, h2]
  have hn : 0 < Complex.normSq z + 1 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos
  rw [Complex.normSq_apply] at hn ⊢
  field_simp
  linear_combination ((z.re * z.re + z.im * z.im - 1) ^ 2 + 4 * z.im ^ 2) * hs

theorem stereoC_re (s : ℝ) (y : E3) : (stereoC s y).re = y 0 / (1 - s * y 2) := by
  rw [stereoC, Complex.re_mul_ofReal]; simp [div_eq_mul_inv]
theorem stereoC_im (s : ℝ) (y : E3) : (stereoC s y).im = -s * y 1 / (1 - s * y 2) := by
  rw [stereoC, Complex.im_mul_ofReal]; simp [div_eq_mul_inv]

theorem one_sub_ne (s : ℝ) (hs : s ^ 2 = 1) (z : ℂ) : 1 - s * stereoCInv s z 2 ≠ 0 := by
  obtain ⟨-, -, h2⟩ := stereoCInv_apply s z
  have hn : 0 < Complex.normSq z + 1 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos
  rw [h2, mul_div_assoc', ← mul_assoc, ← sq, hs, one_mul, one_sub_div hn.ne']
  exact div_ne_zero (by ring_nf; norm_num) hn.ne'

theorem stereoC_stereoCInv (s : ℝ) (hs : s ^ 2 = 1) (z : ℂ) : stereoC s (stereoCInv s z) = z := by
  have hd := one_sub_ne s hs z
  obtain ⟨h0, h1, h2⟩ := stereoCInv_apply s z
  have hn : 0 < Complex.normSq z + 1 := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos
  apply Complex.ext
  · rw [stereoC_re]
    rw [h2] at hd ⊢
    rw [h0, div_eq_iff hd]
    field_simp
    rw [Complex.normSq_apply]
    linear_combination (z.re * (z.re * z.re + z.im * z.im - 1)) * hs
  · rw [stereoC_im]
    rw [h2] at hd ⊢
    rw [h1, div_eq_iff hd]
    field_simp
    rw [Complex.normSq_apply]
    linear_combination (z.im * (z.re * z.re + z.im * z.im + 1)) * hs

theorem stereoCInv_stereoC (s : ℝ) (hs : s ^ 2 = 1) (y : S2) (hy : s * (y : E3) 2 ≠ 1) :
    stereoCInv s (stereoC s y) = y := by
  have hd : 1 - s * (y : E3) 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hS := S2_sq y
  obtain ⟨h0, h1, h2⟩ := stereoCInv_apply s (stereoC s y)
  have hn : Complex.normSq (stereoC s y) + 1 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) one_pos).ne'
  rw [Complex.normSq_apply, stereoC_re, stereoC_im] at h0 h1 h2 hn
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [h0, div_eq_iff hn]
    field_simp
    linear_combination (-(y : E3) 0) * hS +
      (-((y : E3) 0 * ((y : E3) 1 ^ 2 + (y : E3) 2 ^ 2))) * hs
  · simp only [Fin.mk_one, Fin.isValue]
    rw [h1, div_eq_iff hn]
    field_simp
    linear_combination (-(y : E3) 1) * hS +
      (-((y : E3) 1 * (2 * s * (y : E3) 2 + (y : E3) 1 ^ 2 + (y : E3) 2 ^ 2 - 2))) * hs
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [h2, div_eq_iff hn]
    field_simp
    linear_combination (s - (y : E3) 2) * hS + (s * (y : E3) 1 ^ 2 - s * (y : E3) 2 ^ 2 -
      (y : E3) 1 ^ 2 * (y : E3) 2 - (y : E3) 2 ^ 3 + 2 * (y : E3) 2) * hs

theorem continuous_stereoCInv (s : ℝ) : Continuous (stereoCInv s) := by
  unfold stereoCInv
  have hn : ∀ z : ℂ, Complex.normSq z + 1 ≠ 0 := fun z =>
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos).ne'
  refine ((Complex.continuous_normSq.add continuous_const).inv₀ hn).smul ?_
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)

/-- The holomorphic stereographic chart `σ_s : S² ∖ {s e₂} → ℂ`. -/
def holChart (s : ℝ) (hs : s ^ 2 = 1) : OpenPartialHomeomorph S2 ℂ where
  toFun y := stereoC s y
  invFun z := ⟨stereoCInv s z, stereoCInv_mem s hs z⟩
  source := {y | s * (y : E3) 2 ≠ 1}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := fun h =>
    one_sub_ne s hs z (by rw [show s * stereoCInv s z 2 = 1 from h]; ring)
  left_inv' y hy := Subtype.ext (stereoCInv_stereoC s hs y hy)
  right_inv' z _ := stereoC_stereoCInv s hs z
  open_source := isOpen_ne_fun (by fun_prop) continuous_const
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro y hy
    have hd : 1 - s * (y : E3) 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    unfold stereoC
    refine ContinuousAt.continuousWithinAt ?_
    have : ContinuousAt (fun y : S2 => (1 - s * (y : E3) 2)⁻¹) y :=
      ((continuous_const.sub (continuous_const.mul (by fun_prop))).continuousAt).inv₀ hd
    have hN : Continuous fun y : S2 => ((y : E3) 0 : ℂ) - s * Complex.I * ((y : E3) 1 : ℂ) := by
      fun_prop
    exact hN.continuousAt.mul (Complex.continuous_ofReal.continuousAt.comp this)
  continuousOn_invFun := ((continuous_stereoCInv s).subtype_mk _).continuousOn

/-- The derivative of `σ_s` in the direction `u`. -/
def stereoD (s : ℝ) (y u : E3) : ℂ :=
  ((u 0 : ℂ) - s * Complex.I * (u 1 : ℂ)) * (((1 - s * y 2)⁻¹ : ℝ) : ℂ) +
    ((y 0 : ℂ) - s * Complex.I * (y 1 : ℂ)) * (((s * u 2 / (1 - s * y 2) ^ 2) : ℝ) : ℂ)

theorem hasDerivAt_stereoC_line (s : ℝ) (y u : E3) (hd : 1 - s * y 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => stereoC s (y + t • u)) (stereoD s y u) 0 := by
  have h1 : HasDerivAt
      (fun t : ℝ => (((y 0 + t * u 0 : ℝ)) : ℂ) - s * Complex.I * ((y 1 + t * u 1 : ℝ) : ℂ))
      ((u 0 : ℂ) - s * Complex.I * (u 1 : ℂ)) 0 := by
    have a0 : HasDerivAt (fun t : ℝ => y 0 + t * u 0) (u 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u 0)).const_add (y 0)
    have a1 : HasDerivAt (fun t : ℝ => y 1 + t * u 1) (u 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u 1)).const_add (y 1)
    exact a0.ofReal_comp.sub (a1.ofReal_comp.const_mul _)
  have hg : HasDerivAt (fun t : ℝ => 1 - s * (y 2 + t * u 2)) (-(s * u 2)) 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).mul_const (u 2)).const_add (y 2)).const_mul s |>.const_sub 1
  have h2 := (hg.inv (by simpa using hd)).ofReal_comp
  simp only [zero_mul, add_zero, neg_neg] at h2
  have hfun : (fun t : ℝ => stereoC s (y + t • u)) = fun t : ℝ =>
      ((((y 0 + t * u 0 : ℝ)) : ℂ) - s * Complex.I * ((y 1 + t * u 1 : ℝ) : ℂ)) *
        (((1 - s * (y 2 + t * u 2))⁻¹ : ℝ) : ℂ) := by
    funext t; simp only [stereoC, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hfun]
  refine (h1.mul h2).congr_deriv ?_
  simp only [stereoD, zero_mul, add_zero, Pi.inv_apply]

theorem fderiv_stereoC (s : ℝ) (y u : E3) (hd : 1 - s * y 2 ≠ 0) :
    DifferentiableAt ℝ (stereoC s) y ∧ fderiv ℝ (stereoC s) y u = stereoD s y u := by
  have hdiff : DifferentiableAt ℝ (stereoC s) y := by
    unfold stereoC
    have : DifferentiableAt ℝ (fun y : E3 => (1 - s * y 2)⁻¹) y :=
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul (by fun_prop))).inv hd
    have hN : Differentiable ℝ fun y : E3 => ((y 0 : ℂ) - s * Complex.I * (y 1 : ℂ)) := by
      fun_prop
    exact hN.differentiableAt.mul (Complex.ofRealCLM.differentiableAt.comp y this)
  refine ⟨hdiff, ?_⟩
  have hl : HasDerivAt (fun t : ℝ => y + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add y
  have h2 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h2.unique (hasDerivAt_stereoC_line s y u hd)

/-- `σ_s` is holomorphic for `j_y = y × ·`: `Dσ_s(y)(y × w) = i Dσ_s(y) w` for `w ⊥ y`. -/
theorem stereoD_cross (s : ℝ) (hs : s ^ 2 = 1) (y w : E3)
    (hS : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1) (hP : y 0 * w 0 + y 1 * w 1 + y 2 * w 2 = 0)
    (hd : 1 - s * y 2 ≠ 0) : stereoD s y (crossL y w) = Complex.I * stereoD s y w := by
  have c0 : crossL y w 0 = y 1 * w 2 - y 2 * w 1 := by simp [crossL_apply, cross_apply]
  have c1 : crossL y w 1 = y 2 * w 0 - y 0 * w 2 := by simp [crossL_apply, cross_apply]
  have c2 : crossL y w 2 = y 0 * w 1 - y 1 * w 0 := by simp [crossL_apply, cross_apply]
  have he : (1 - s * y 2) * (1 - s * y 2)⁻¹ = 1 := mul_inv_cancel₀ hd
  apply Complex.ext
  · simp only [stereoD, c0, c1, c2, Complex.add_re, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, Complex.add_im, div_eq_mul_inv, ← inv_pow]
    generalize (1 - s * y 2)⁻¹ = e at he ⊢
    linear_combination (e ^ 2 * (s * w 1)) * hS + (e ^ 2 * (-s * y 1)) * hP +
      (e ^ 2 * (w 1 * y 2 - w 2 * y 1)) * hs - ((-s * w 1 - w 1 * y 2 + w 2 * y 1) * e) * he
  · simp only [stereoD, c0, c1, c2, Complex.add_re, Complex.mul_re, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, Complex.add_im, div_eq_mul_inv, ← inv_pow]
    generalize (1 - s * y 2)⁻¹ = e at he ⊢
    linear_combination (e ^ 2 * (s ^ 2 * w 0)) * hS + (e ^ 2 * (-s ^ 2 * y 0)) * hP +
      (e ^ 2 * w 0) * hs - ((-s * w 0 * y 2 + s * w 2 * y 0 - w 0) * e) * he

theorem inner_E3 (y w : E3) : inner ℝ y w = y 0 * w 0 + y 1 * w 1 + y 2 * w 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, mul_comm]

/-- `σ_s` is a `j`-holomorphic chart on its source. -/
theorem holChart_holo (s : ℝ) (hs : s ^ 2 = 1) (y : S2) (hy : y ∈ (holChart s hs).source) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChart s hs) y ∧ ∀ v : E2,
      (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChart s hs) y (jStdMap y v)) =
        Complex.I * (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChart s hs) y v) := by
  have hd : 1 - s * (y : E3) 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hcoe : (holChart s hs : S2 → ℂ) = stereoC s ∘ Subtype.val := rfl
  have hmd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℂ) (stereoC s) y :=
    (fderiv_stereoC s y 0 hd).1.mdifferentiableAt
  have hval : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) (Subtype.val : S2 → E3) y :=
    (contMDiff_coe_sphere (m := ∞) (n := 2) y).mdifferentiableAt (by simp)
  have hmf : ∀ v, mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChart s hs) y v =
      fderiv ℝ (stereoC s) y (incD y v) := by
    intro v
    rw [hcoe, mfderiv_comp y hmd hval, mfderiv_eq_fderiv]
    rfl
  refine ⟨hcoe ▸ hmd.comp y hval, fun v => ?_⟩
  have hj : incD y (jStdMap y v) = crossL y (incD y v) :=
    incD_retrD_of_perp y (inner_crossL_self _ _)
  have hP := inner_incD y v
  rw [inner_E3] at hP
  have key : fderiv ℝ (stereoC s) y (incD y (jStdMap y v)) =
      Complex.I * fderiv ℝ (stereoC s) y (incD y v) := by
    rw [hj, (fderiv_stereoC s y _ hd).2, (fderiv_stereoC s y _ hd).2]
    exact stereoD_cross s hs y (incD y v) (S2_sq y) hP hd
  exact (hmf _).trans (key.trans (congrArg _ (hmf v).symm))


/-! ## 4. The cut-off of `IsHlocNear` lies in `H^{k,δ}(ℝ × S¹)` -/

/-- The profile `g(s, u) = χ(2 - 16 (s² + u²)) c`. -/
def bumpProfile (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (2 - 16 * (p.1 ^ 2 + p.2 ^ 2)) * c

theorem contDiff_bumpProfile (c : ℝ) : ContDiff ℝ ∞ (bumpProfile c) := by
  unfold bumpProfile
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul contDiff_const

theorem bumpProfile_eq_zero (c : ℝ) {p : ℝ × ℝ} (h : 1 / 8 ≤ p.1 ^ 2 + p.2 ^ 2) :
    bumpProfile c p = 0 := by
  rw [bumpProfile, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

/-- The periodized cut-off `(s, t) ↦ g(s, fract t - 1/2)`. -/
def bumpPer (c : ℝ) (p : ℝ × ℝ) : ℝ := bumpProfile c (p.1, Int.fract p.2 - 1 / 2)

theorem fract_far (n : ℤ) {t : ℝ} (ht : |t - n| < 1 / 10) : 2 / 5 ≤ |Int.fract t - 1 / 2| := by
  rw [abs_lt] at ht
  rcases le_or_gt (n : ℝ) t with h | h
  · have : Int.fract t = t - n := Int.fract_eq_iff.2 ⟨by linarith, by linarith, n, by ring⟩
    rw [this, abs_of_neg (by linarith)]; linarith
  · have : Int.fract t = t - (n - 1 : ℤ) :=
      Int.fract_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith, n - 1, by ring⟩
    push_cast at this
    rw [this, abs_of_pos (by linarith)]; linarith

theorem isTest_bumpPer (c : ℝ) : IsTest (bumpPer c) where
  smooth := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨s₀, t₀⟩
    have hft := Int.self_sub_floor t₀
    rcases eq_or_ne (Int.fract t₀) 0 with h0 | h0
    · -- `t₀ = n`: the function vanishes near `(s₀, t₀)`
      have hn : t₀ = ⌊t₀⌋ := by linarith
      have hnear : ∀ᶠ p : ℝ × ℝ in nhds (s₀, t₀),
          p.2 ∈ Ioo ((⌊t₀⌋ : ℝ) - 1 / 10) (⌊t₀⌋ + 1 / 10) :=
        continuous_snd.continuousAt.preimage_mem_nhds
          (isOpen_Ioo.mem_nhds ⟨by simp only; linarith, by simp only; linarith⟩)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with p hp
      apply bumpProfile_eq_zero
      have := fract_far ⌊t₀⌋ (t := p.2) (by rw [abs_lt]; constructor <;> linarith [hp.1, hp.2])
      have h2 : (2 / 5 : ℝ) ^ 2 ≤ (Int.fract p.2 - 1 / 2) ^ 2 := by
        rw [← sq_abs (Int.fract p.2 - 1 / 2)]; exact pow_le_pow_left₀ (by norm_num) this 2
      dsimp only; nlinarith [sq_nonneg p.1]
    · have hpos : 0 < Int.fract t₀ := lt_of_le_of_ne (Int.fract_nonneg t₀) (Ne.symm h0)
      have hlt := Int.fract_lt_one t₀
      have hnear : ∀ᶠ p : ℝ × ℝ in nhds (s₀, t₀), p.2 ∈ Ioo (⌊t₀⌋ : ℝ) (⌊t₀⌋ + 1) :=
        continuous_snd.continuousAt.preimage_mem_nhds
          (isOpen_Ioo.mem_nhds ⟨by simp only; linarith, by simp only; linarith⟩)
      have hsm : ContDiff ℝ ∞ fun p : ℝ × ℝ => bumpProfile c (p.1, p.2 - ⌊t₀⌋ - 1 / 2) :=
        (contDiff_bumpProfile c).comp (by fun_prop)
      refine hsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [hnear] with p hp
      have : Int.fract p.2 = p.2 - ⌊t₀⌋ :=
        Int.fract_eq_iff.2 ⟨by linarith [hp.1], by linarith [hp.2], ⌊t₀⌋, by ring⟩
      simp only [bumpPer, this]
  periodic s t := by simp [bumpPer, Int.fract_add_one]
  bddSupp := ⟨1, fun s t hs => bumpProfile_eq_zero c (by
    have : 1 < s ^ 2 := by nlinarith [abs_mul_abs_self s, sq_abs s]
    dsimp only; nlinarith [sq_nonneg (Int.fract t - 1 / 2)])⟩

/-- The cut-off of `IsHlocNear`, times a constant, is `bumpPer` on the strip `ℝ × (0, 1]`. -/
theorem bumpPer_ae_eq (c : ℝ) :
    bumpPer c =ᵐ[cyl]
      fun p => Real.smoothTransition (2 - 16 * (p.1 ^ 2 + (p.2 - 1 / 2) ^ 2)) * c := by
  have hnull : cyl {p : ℝ × ℝ | p.2 ∉ Ioc (0 : ℝ) 1} = 0 := by
    have : {p : ℝ × ℝ | p.2 ∉ Ioc (0 : ℝ) 1} = univ ×ˢ (Ioc (0 : ℝ) 1)ᶜ := by ext; simp
    rw [this, cyl, Measure.prod_prod]
    simp [Measure.restrict_apply' measurableSet_Ioc]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
  simp only [not_not] at hp
  obtain ⟨h0, h1⟩ := hp
  rcases h1.lt_or_eq with h1 | h1
  · have : Int.fract p.2 = p.2 := Int.fract_eq_iff.2 ⟨h0.le, h1, 0, by simp⟩
    simp [bumpPer, bumpProfile, this]
  · simp only [bumpPer, bumpProfile, h1]
    norm_num

/-- The cut-off times a constant lies in `H^{k,δ}(ℝ × S¹)`. -/
theorem memH_cutoff_mul_const (k : ℕ) (δ c : ℝ) :
    MemH k δ fun p => Real.smoothTransition (2 - 16 * (p.1 ^ 2 + (p.2 - 1 / 2) ^ 2)) * c :=
  fun a b _ => ⟨pD a b (bumpPer c),
    ((isTest_bumpPer c).smPer.hasWeakDeriv a b).congr_ae (bumpPer_ae_eq c) (ae_eq_refl _),
    ((isTest_bumpPer c).pD a b).memLp_wt δ⟩


/-! ## 5. Noded spheres -/

/-- The standard almost complex structure of `S²`, `j_x v = x × v`. -/
def jStd : AlmostComplexStructure E2 S2 := ⟨jStdMap, jStdMap_sq, jStdMap_smooth⟩

theorem pt_injective : Injective pt := by
  intro i j h
  have := congrArg (fun v : S2 => (v : E3) i) h
  by_contra hij
  simp [pt, hij] at this

instance : ConnectedSpace S2 :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E3) (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)

theorem connectedSpace_quot {X : Type} [TopologicalSpace X] [ConnectedSpace X] (r : X → X → Prop) :
    ConnectedSpace (Quot r) :=
  Quot.mk_surjective.connectedSpace continuous_quot_mk

/-- **Witness for Memoir Definition 1.2**: the sphere `(S², j)` with the three marked points
`e₀, e₁, e₂` and no nodes. -/
def sphere3 : NodalSurface 3 where
  S := S2
  j := jStd
  marked := ⟨pt, pt_injective⟩
  nodes := ∅
  finite_nodes := finite_empty
  not_diag := by simp
  disjoint := by simp
  marked_not_nodal := by simp
  connected := connectedSpace_quot _

theorem pt_ne_neg (i : Fin 3) : pt i ≠ -pt 2 := by
  intro h
  have := congrArg (fun v : S2 => (v : E3) 2) h
  fin_cases i <;> simp [pt] at this
  norm_num at this

theorem pt0_ne_pt2 : pt 0 ≠ pt 2 := fun h => absurd (pt_injective h) (by decide)

/-- **Witness for the nodal pairs of Memoir Definition 1.2**: the sphere with one nodal pair
`{e₂, -e₂}` (an irreducible nodal surface of arithmetic genus one) and the marked point `e₀`. -/
def sphereNode : NodalSurface 1 where
  S := S2
  j := jStd
  marked := ⟨fun _ => pt 0, fun _ _ _ => Subsingleton.elim _ _⟩
  nodes := {s(pt 2, -pt 2)}
  finite_nodes := finite_singleton _
  not_diag p hp := by
    rw [mem_singleton_iff] at hp
    subst hp
    rw [Sym2.mk_isDiag_iff]
    exact pt_ne_neg 2
  disjoint p hp q hq _ _ _ := by rw [mem_singleton_iff] at hp hq; rw [hp, hq]
  marked_not_nodal _ p hp := by
    rw [mem_singleton_iff] at hp
    subst hp
    rw [Sym2.mem_iff]
    rintro (h | h)
    · exact pt0_ne_pt2 h
    · exact pt_ne_neg 0 h
  connected := connectedSpace_quot _

theorem sphereNode_nodes_nonempty : sphereNode.nodes.Nonempty := singleton_nonempty _

/-- The component of `sphereNode` carries three special points `e₀, e₂, -e₂`. -/
theorem sphereNode_not_unstable (x : sphereNode.S) : ¬ sphereNode.IsUnstableComponent x := by
  have hC : connectedComponent x = univ :=
    PreconnectedSpace.connectedComponent_eq_univ (X := S2) x
  have hsp : sphereNode.special ∩ connectedComponent x = ({pt 0, pt 2, -pt 2} : Set S2) := by
    rw [hC, inter_univ]
    ext y
    show y ∈ range (fun _ : Fin 1 => pt 0) ∪ {x | ∃ p ∈ ({s(pt 2, -pt 2)} : Set (Sym2 S2)), x ∈ p} ↔
      y ∈ ({pt 0, pt 2, -pt 2} : Set S2)
    constructor
    · rintro (⟨_, rfl⟩ | ⟨p, hp, hy⟩)
      · exact Or.inl rfl
      · rw [mem_singleton_iff] at hp
        subst hp
        exact Or.inr (Sym2.mem_iff.1 hy)
    · rintro (rfl | h)
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inr ⟨_, rfl, Sym2.mem_iff.2 h⟩
  have h3 : (sphereNode.special ∩ connectedComponent x).ncard = 3 := by
    rw [hsp]
    exact Set.ncard_eq_three.2 ⟨_, _, _, pt0_ne_pt2, pt_ne_neg 0, pt_ne_neg 2, rfl⟩
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · omega
  · rw [h, ncard_empty] at h3; omega

/-- The only domain component of `sphere3` carries three special points: it is stable. -/
theorem sphere3_not_unstable (x : sphere3.S) : ¬ sphere3.IsUnstableComponent x := by
  have hC : connectedComponent x = univ :=
    PreconnectedSpace.connectedComponent_eq_univ (X := S2) x
  have hsp : sphere3.special ∩ connectedComponent x = (range pt : Set S2) := by
    rw [hC, inter_univ]
    ext y
    exact ⟨fun h => h.elim id fun ⟨_, hp, _⟩ => absurd hp (Set.notMem_empty _), Or.inl⟩
  have h3 : (sphere3.special ∩ connectedComponent x).ncard = 3 := by
    rw [hsp]
    exact (ncard_range_of_injective pt_injective).trans (by simp)
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · omega
  · rw [h, ncard_empty] at h3; omega

/-! ## 6. Constant stable maps -/

section ConstMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] in
/-- The area of a constant map vanishes, on every component. -/
theorem NodalSurface.area_const {m : ℕ} (X : NodalSurface m) (om : SymplecticForm E Q) (q : Q)
    (x : X.S) : X.area om (fun _ => q) x = 0 := by
  have hz : X.surfaceIntegral (fun _ => 0) = 0 := by
    simp [NodalSurface.surfaceIntegral, NodalSurface.chartIntegral]
  unfold NodalSurface.area
  convert hz using 2
  ext y v w
  by_cases hy : y ∈ connectedComponent x
  · simp only [Set.indicator_of_mem hy, mfderiv_const]
    change om.form q 0 0 = 0
    simp
  · simp [hy]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
/-- A constant map is of class `H^k_loc` near every point of a surface whose charts are onto
`ℝ²` (the sphere). -/
theorem isHlocNear_const {m : ℕ} (X : NodalSurface m)
    (hX : ∀ x : X.S, (extChartAt 𝓘(ℝ, E2) x).target = univ) (k : ℕ) (q : Q) (x : X.S) :
    X.IsHlocNear (E := E) k (fun _ => q) x :=
  ⟨1, one_pos, fun _ _ => ⟨by rw [hX]; trivial, mem_extChartAt_source q⟩,
    fun ℓ => memH_cutoff_mul_const k 0 _⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
/-- A constant map is of class `(k, δ)` near the pole `-s e₂` of `sphereNode`, through the
holomorphic chart `σ_s`. -/
theorem sphereNode_isClassNear_const (k : ℕ) (δ : ℝ) (q : Q) (s : ℝ) (hs : s ^ 2 = 1)
    (x : S2) (h0 : (x : E3) 0 = 0) (h1 : (x : E3) 1 = 0) (h2 : (x : E3) 2 = -s) :
    sphereNode.IsClassNear (E := E) k δ (fun _ => q) x := by
  have hsrc : x ∈ (holChart s hs).source := by
    show s * (x : E3) 2 ≠ 1
    rw [h2]; nlinarith
  refine ⟨holChart s hs, ⟨hsrc, ?_, fun y hy => holChart_holo s hs y hy⟩, 0,
    fun _ _ => ⟨(holChart s hs).map_target (mem_univ _), mem_extChartAt_source q⟩, fun ℓ => ?_⟩
  · show stereoC s x = 0
    simp [stereoC, h0, h1]
  · convert memH_cutoff_mul_const k δ 0 using 1
    funext p
    simp

/-- **Witness for Memoir Definition 1.4**: the constant map `S² → Q` with three marked points is a
stable map of class `(k, δ)`, for every target `(Q, ω)`, `k` and `δ`. -/
def constStableMap (om : SymplecticForm E Q) (q : Q) (k : ℕ) (δ : ℝ) : StableMap om 3 k δ where
  dom := sphere3
  u _ := q
  continuous := continuous_const
  nodal p hp := absurd hp (Set.notMem_empty p)
  regular x _ := isHlocNear_const sphere3 S2_target k q x
  matching _ _ _ := rfl
  area_nonneg x := (sphere3.area_const om q x).symm.le
  stable x h := absurd h (sphere3_not_unstable x)

/-- **Witness for Memoir Definitions 1.1 and 1.4 with a node**: the constant map from the
noded sphere `sphereNode` (nodal pair `{e₂, -e₂}`, marked point `e₀`) is a stable map of class
`(k, δ)`: at the nodal points it is of class `(k, δ)` in the holomorphic charts `σ_{∓1}`. -/
def nodalStableMap (om : SymplecticForm E Q) (q : Q) (k : ℕ) (δ : ℝ) : StableMap om 1 k δ where
  dom := sphereNode
  u _ := q
  continuous := continuous_const
  nodal p hp x hx := by
    rw [show p = s(pt 2, -pt 2) from hp] at hx
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact sphereNode_isClassNear_const k δ q (-1) (by norm_num) _ (by simp [pt]) (by simp [pt])
        (by simp [pt])
    · exact sphereNode_isClassNear_const k δ q 1 (by norm_num) _ (by simp [pt]) (by simp [pt])
        (by simp [pt])
  regular x _ := isHlocNear_const sphereNode S2_target k q x
  matching _ _ _ := rfl
  area_nonneg x := (sphereNode.area_const om q x).symm.le
  stable x h := absurd h (sphereNode_not_unstable x)

end ConstMap

/-- The stable maps of class `(3, δ₀)` into `(ℝ², ω₀)` with three marked points form a non-empty
type: the objects of `gwCategory` exist. -/
theorem nonempty_stableMap (δ₀ : ℝ) : Nonempty (StableMap omE2 3 3 δ₀) :=
  ⟨constStableMap omE2 0 3 δ₀⟩

/-- A stable map of class `(3, δ₀)` with a node exists. -/
theorem exists_stableMap_with_node (δ₀ : ℝ) :
    ∃ α : StableMap omE2 1 3 δ₀, α.dom.nodes.Nonempty :=
  ⟨nodalStableMap omE2 0 3 δ₀, sphereNode_nodes_nonempty⟩

end GWMemoir
