import GWMemoir.LinearCRNodesOpNeck

/-!
# Gluing data with necks exist

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), continuing `GWMemoir.LinearCRNodesOpNeck`: a witness for the
structure `GlueDataN` of `GWMemoir.LinearCRNodesOp`, so that the kernel theorems there hold
unconditionally on two spheres joined at a node.

* `logE ζ = -(log ζ)/2π`, read as `(s, t)`: `expPolar (logE ζ) = ζ`.
* `exists_chartChange_of_leftInv`: a map smooth on an open set, with a differentiable left
  inverse there, agrees on a compact set of the strip with a `ChartChange`.
* The neck functions `χ(s) = g(e^{-4πs})` (`chiN`) and `χ_j = g(|φ_j|²)` on the surface
  (`chiSN`); the partition `ρ_i = (1 - ∑ χ_j) τ_i` (`exists_rho_neck`).
* The two pieces in the angle (`thetaN`, `tauAng`, `tauT`, `cutT`), and the changes of charts
  between discs and necks: `exists_Dn` (`ψ = -(log(± w))/2π - (s₀, -½)`, `w` the holomorphic
  coordinate of the disc point) and `exists_Dd` (the disc coordinates of `σ(s, t + θ)`).
* **`nonempty_glueDataN`**: gluing data exist on every atlas satisfying `GlueCharts`: the neck
  charts are onto `ℂ`, smooth with smooth inverses, with disjoint sources, and the closed discs
  `r² ≤ 1/8` avoid the nodal points.
* `exists_sectionAtlas_glue`: an atlas with prescribed neck charts, injective node map, and
  closed discs off the nodal points.
* **`exists_glueDataN`**: for every `q`, `twoSpheres` has an atlas of `u ≡ q` with `IsStdNeck`,
  `NeckSmooth` and gluing data.  **`exists_linCRN_ker_equiv`**: on it, `ker D ≅ E` and
  `dim ker D = dim E`, with no hypothesis beyond the weights.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. `e^{-2π(s+it)}` and its logarithm -/

section ExpLog

/-- `-(log ζ)/2π`, read as `(s, t)`. -/
def logE (ζ : ℂ) : ℝ × ℝ :=
  (-(Complex.log ζ).re / (2 * Real.pi), -(Complex.log ζ).im / (2 * Real.pi))

lemma expPolar_logE {ζ : ℂ} (hζ : ζ ≠ 0) : expPolar (logE ζ) = ζ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : -2 * (Real.pi : ℂ) * ((((logE ζ).1 : ℝ) : ℂ) + (((logE ζ).2 : ℝ) : ℂ) * Complex.I) =
      Complex.log ζ := by
    simp only [logE]
    push_cast
    conv_rhs => rw [← Complex.re_add_im (Complex.log ζ)]
    field_simp
    ring
  rw [expPolar_def, e, Complex.exp_log hζ]

lemma expPolar_add_half (s t : ℝ) : expPolar (s, t + 1 / 2) = -expPolar (s, t) := by
  simp only [expPolar_def]
  have e : -2 * (Real.pi : ℂ) * (((s : ℝ) : ℂ) + (((t + 1 / 2 : ℝ)) : ℂ) * Complex.I) =
      -2 * Real.pi * ((s : ℂ) + (t : ℂ) * Complex.I) + (-(Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add]
  have : Complex.exp (-(Real.pi : ℂ) * Complex.I) = -1 := by
    rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  rw [this]; ring

lemma logE_expPolar {s t : ℝ} (h1 : -(1 / 2) ≤ t) (h2 : t < 1 / 2) :
    logE (expPolar (s, t)) = (s, t) := by
  have hπ := Real.pi_pos
  set x : ℂ := -2 * Real.pi * ((s : ℂ) + (t : ℂ) * Complex.I)
  have hxim : x.im = -2 * Real.pi * t := by simp [x]
  have hxre : x.re = -2 * Real.pi * s := by simp [x]
  have hl : Complex.log (Complex.exp x) = x :=
    Complex.log_exp (by rw [hxim]; nlinarith) (by rw [hxim]; nlinarith)
  rw [expPolar_def]
  change logE (Complex.exp x) = (s, t)
  simp only [logE, hl, hxim, hxre]
  ext <;> field_simp

lemma normSq_expPolar (p : ℝ × ℝ) :
    Complex.normSq (expPolar p) = Real.exp (-4 * Real.pi * p.1) := by
  rw [Complex.normSq_eq_norm_sq, norm_expPolar, ← Real.exp_nat_mul]
  congr 1; push_cast; ring

lemma expPolar_injOn {p p' : ℝ × ℝ} (h : expPolar p = expPolar p') :
    p.1 = p'.1 ∧ ∃ n : ℤ, p.2 = p'.2 + n := by
  have h1 : p.1 = p'.1 := by
    have := congrArg norm h
    rw [norm_expPolar, norm_expPolar] at this
    have := Real.exp_injective this
    have hπ := Real.pi_pos
    nlinarith
  refine ⟨h1, ?_⟩
  rw [expPolar_def, expPolar_def, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨-n, ?_⟩
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have := congrArg Complex.im hn
  simp [h1] at this
  have hπ' := Real.pi_pos
  push_cast
  nlinarith

end ExpLog

/-! ## 2. Changes of charts from local inverses -/

section LeftInv

lemma det_ne_of_comp_eq_id {M N : (ℝ × ℝ) →L[ℝ] ℝ × ℝ}
    (h : M.comp N = ContinuousLinearMap.id ℝ (ℝ × ℝ)) : N.det ≠ 0 := by
  have h1 : LinearMap.det ((M : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) ∘ₗ (N : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = 1 := by
    have e : ((M : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) ∘ₗ (N : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) = LinearMap.id :=
      LinearMap.ext fun v => congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ × ℝ => T v) h
    rw [e, LinearMap.det_id]
  rw [LinearMap.det_comp] at h1
  intro h0
  change LinearMap.det (N : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ) = 0 at h0
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

/-- **A change of charts from a local inverse**: a map `f`, smooth on an open `U`, with a left
inverse `g` on `U` differentiable at the points `f(K)`, agrees on a compact `K ⊆ U` of the open
strip, mapped into the open strip, with a `ChartChange`. -/
theorem exists_chartChange_of_leftInv {K U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ × ℝ}
    (hK : IsCompact K) (hKs : K ⊆ openStrip) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hgf : ∀ p ∈ U, g (f p) = p)
    (hg : ∀ p ∈ K, DifferentiableAt ℝ g (f p)) (hmaps : MapsTo f K openStrip) :
    ∃ D : ChartChange, D.K = K ∧ ∀ p ∈ K, D.ψ p = f p := by
  obtain ⟨χ, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, ℝ × ℝ) (n := ⊤)
    hU.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.2 hKU)
  obtain ⟨O, hOo, hVO, hO⟩ := eventually_nhdsSet_iff_exists.1 h0
  obtain ⟨O', hO'o, hKO', hO'⟩ := eventually_nhdsSet_iff_exists.1 h1
  have hχ : ContDiff ℝ ∞ (χ : ℝ × ℝ → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  set ψ : ℝ × ℝ → ℝ × ℝ := fun p => χ p • f p
  have hψ : ContDiff ℝ ∞ ψ := by
    refine contDiff_of_open_cover hU hOo (fun p => ?_) (hχ.contDiffOn.smul hf)
      fun p hp => by simp [ψ, hO p hp]
    by_cases h : p ∈ U
    · exact Or.inl h
    · exact Or.inr (hVO h)
  have hψeq : ∀ p ∈ O', ψ p = f p := fun p hp => by simp [ψ, hO' p hp]
  have hev : ∀ p ∈ K, ψ =ᶠ[𝓝 p] f := fun p hp => by
    filter_upwards [hO'o.mem_nhds (hKO' hp)] with p' hp' using hψeq p' hp'
  refine ⟨{
    K := K
    ψ := ψ
    isCompact := hK
    sub := hKs
    smooth := hψ
    injOn := fun p hp p' hp' h => by
      rw [hψeq p (hKO' hp), hψeq p' (hKO' hp')] at h
      rw [← hgf p (hKU hp), ← hgf p' (hKU hp'), h]
    det_ne := fun p hp => by
      rw [(hev p hp).fderiv_eq]
      have hfd : DifferentiableAt ℝ f p :=
        ((hf.contDiffAt (hU.mem_nhds (hKU hp))).differentiableAt (by simp))
      have hc := fderiv_comp p (hg p hp) hfd
      have hid : (g ∘ f) =ᶠ[𝓝 p] id := by
        filter_upwards [hU.mem_nhds (hKU hp)] with p' hp' using hgf p' hp'
      rw [hid.fderiv_eq, fderiv_id] at hc
      exact det_ne_of_comp_eq_id hc.symm
    mapsTo := fun p hp => by
      rw [hψeq p (hKO' hp)]
      exact hmaps hp }, rfl, fun p hp => hψeq p (hKO' hp)⟩

end LeftInv

/-! ## 3. Functions on the necks -/

section NeckFun

/-- The cut-off `g(r)`, `1` for `r ≤ e^{-4π(s₀+1)}`, `0` for `r ≥ e^{-4π(s₀+1/2)}`; it is read
on `r = |w|²`, `w` the holomorphic coordinate at the nodal point. -/
def gN (s₀ r : ℝ) : ℝ :=
  Real.smoothTransition ((Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - r) /
    (Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - Real.exp (-4 * Real.pi * (s₀ + 1))))

lemma gN_den_pos (s₀ : ℝ) :
    0 < Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) - Real.exp (-4 * Real.pi * (s₀ + 1)) := by
  have := Real.pi_pos
  rw [sub_pos, Real.exp_lt_exp]; nlinarith

lemma contDiff_gN (s₀ : ℝ) : ContDiff ℝ ∞ (gN s₀) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

lemma gN_eq_zero {s₀ r : ℝ} (hr : Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) ≤ r) : gN s₀ r = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (gN_den_pos s₀).le)

lemma gN_eq_one {s₀ r : ℝ} (hr : r ≤ Real.exp (-4 * Real.pi * (s₀ + 1))) : gN s₀ r = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (gN_den_pos s₀)).2 (by linarith))

/-- The neck function `χ(s) = g(e^{-4πs})` of `s` alone. -/
def chiN (s₀ s : ℝ) : ℝ := gN s₀ (Real.exp (-4 * Real.pi * s))

lemma contDiff_chiN (s₀ : ℝ) : ContDiff ℝ ∞ (chiN s₀) :=
  (contDiff_gN s₀).comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma chiN_zero {s₀ s : ℝ} (hs : s ≤ s₀ + 1 / 2) : chiN s₀ s = 0 :=
  gN_eq_zero (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))

lemma chiN_one {s₀ s : ℝ} (hs : s₀ + 1 ≤ s) : chiN s₀ s = 1 :=
  gN_eq_one (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))

/-- The radius `e^{-2π(s₀+1/2)}` beyond which the neck function vanishes. -/
def rN (s₀ : ℝ) : ℝ := Real.exp (-2 * Real.pi * (s₀ + 1 / 2))

lemma rN_sq (s₀ : ℝ) : rN s₀ ^ 2 = Real.exp (-4 * Real.pi * (s₀ + 1 / 2)) := by
  rw [rN, ← Real.exp_nat_mul]; congr 1; push_cast; ring

lemma rN_lt (s₀ : ℝ) : rN s₀ < Real.exp (-2 * Real.pi * s₀) := by
  rw [rN, Real.exp_lt_exp]; nlinarith [Real.pi_pos]

lemma gN_norm_eq_zero {s₀ : ℝ} {ζ : ℂ} (h : rN s₀ < ‖ζ‖) : gN s₀ (‖ζ‖ ^ 2) = 0 := by
  refine gN_eq_zero ?_
  rw [← rN_sq]
  have h0 : 0 ≤ rN s₀ := (Real.exp_pos _).le
  exact pow_le_pow_left₀ h0 h.le 2

lemma norm_expPolar_sq (p : ℝ × ℝ) : ‖expPolar p‖ ^ 2 = Real.exp (-4 * Real.pi * p.1) := by
  rw [← Complex.normSq_eq_norm_sq, normSq_expPolar]

variable {m : ℕ} {X : NodalSurface m}

open Classical in
/-- **The neck function on the surface**: `g(|φ|²)` on the source of the chart `φ`, `0` off it. -/
def chiSN (φ : OpenPartialHomeomorph X.S ℂ) (s₀ : ℝ) (y : X.S) : ℝ :=
  if y ∈ φ.source then gN s₀ (‖φ y‖ ^ 2) else 0

/-- The closed set `φ⁻¹(|w| ≤ e^{-2π(s₀+1/2)})` carrying the neck function. -/
def zSet (φ : OpenPartialHomeomorph X.S ℂ) (s₀ : ℝ) : Set X.S :=
  φ.symm '' Metric.closedBall 0 (rN s₀)

variable {φ : OpenPartialHomeomorph X.S ℂ} {s₀ : ℝ}

lemma chiSN_of_not_mem {y : X.S} (hy : y ∉ φ.source) : chiSN φ s₀ y = 0 := by
  simp [chiSN, hy]

lemma chiSN_of_mem {y : X.S} (hy : y ∈ φ.source) : chiSN φ s₀ y = gN s₀ (‖φ y‖ ^ 2) := by
  simp [chiSN, hy]

lemma chiSN_polar (ht : φ.target = univ) (p : ℝ × ℝ) :
    chiSN φ s₀ (X.polar φ p) = chiN s₀ p.1 := by
  have hp : expPolar p ∈ φ.target := by rw [ht]; trivial
  rw [chiSN_of_mem (X.polar_mem_source hp), NodalSurface.polar_eq, φ.right_inv hp,
    norm_expPolar_sq]
  rfl

lemma zSet_sub (ht : φ.target = univ) : zSet φ s₀ ⊆ φ.source := by
  rintro _ ⟨ζ, -, rfl⟩
  exact φ.map_target (by rw [ht]; trivial)

lemma norm_le_of_mem_zSet (ht : φ.target = univ) {y : X.S} (hy : y ∈ zSet φ s₀) :
    ‖φ y‖ ≤ rN s₀ := by
  obtain ⟨ζ, hζ, rfl⟩ := hy
  rw [φ.right_inv (by rw [ht]; trivial)]
  simpa using hζ

lemma isCompact_zSet (hsym : Continuous φ.symm) :
    IsCompact (zSet φ s₀) :=
  (isCompact_closedBall 0 (rN s₀)).image hsym

lemma mem_zSet_of_chiSN_ne {y : X.S} (h : chiSN φ s₀ y ≠ 0) :
    y ∈ zSet φ s₀ := by
  by_cases hy : y ∈ φ.source
  · rw [chiSN_of_mem hy] at h
    refine ⟨φ y, ?_, φ.left_inv hy⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hc
    exact h (gN_norm_eq_zero (not_le.1 hc))
  · exact absurd (chiSN_of_not_mem hy) h

lemma tsupport_chiSN_sub (hsym : Continuous φ.symm) :
    tsupport (chiSN φ s₀) ⊆ zSet φ s₀ :=
  closure_minimal (fun _ hy => mem_zSet_of_chiSN_ne hy) (isCompact_zSet hsym).isClosed

lemma contMDiff_chiSN (ht : φ.target = univ) (hsym : Continuous φ.symm)
    (hsm : ∀ y ∈ φ.source, ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ φ y) :
    ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ (chiSN φ s₀) := by
  intro y
  by_cases hy : y ∈ φ.source
  · have hg : ContDiff ℝ ∞ fun ζ : ℂ => gN s₀ (‖ζ‖ ^ 2) :=
      (contDiff_gN s₀).comp (contDiff_norm_sq ℝ)
    refine ((hg.contMDiff (φ y)).comp y (hsm y hy)).congr_of_eventuallyEq ?_
    filter_upwards [φ.open_source.mem_nhds hy] with y' hy'
    exact chiSN_of_mem hy'
  · refine (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hz : y ∉ zSet φ s₀ := fun h => hy (zSet_sub ht h)
    filter_upwards [(isCompact_zSet hsym).isClosed.isOpen_compl.mem_nhds hz] with y' hy'
    by_contra hc
    exact hy' (mem_zSet_of_chiSN_ne hc)

end NeckFun

/-! ## 4. The two pieces in the angle -/

section Angle

/-- The rotation of the piece `a` of a neck: `θ 0 = 0`, `θ 1 = ½`. -/
def thetaN (a : Fin 2) : ℝ := if a = 1 then 1 / 2 else 0

/-- The sign `c 0 = -1`, `c 1 = 1` with `e^{-2π(s + i(t + ½ - θ a))} = c a · e^{-2π(s+it)}`. -/
def cSgn (a : Fin 2) : ℂ := if a = 1 then 1 else -1

lemma cSgn_mul_self (a : Fin 2) : cSgn a * cSgn a = 1 := by
  unfold cSgn; split_ifs <;> norm_num

lemma norm_cSgn_mul (a : Fin 2) (ζ : ℂ) : ‖cSgn a * ζ‖ = ‖ζ‖ := by
  unfold cSgn; split_ifs <;> simp

lemma expPolar_theta (a : Fin 2) (x y : ℝ) :
    expPolar (x, y + 1 / 2 - thetaN a) = cSgn a * expPolar (x, y) := by
  unfold thetaN cSgn
  split_ifs
  · simp
  · rw [sub_zero, expPolar_add_half]; ring

lemma cSgn_expPolar_theta (a : Fin 2) (s t : ℝ) :
    cSgn a * expPolar (s, t + thetaN a) = expPolar (s, t - 1 / 2) := by
  unfold thetaN cSgn
  split_ifs
  · rw [one_mul]
    have := expPolar_add_one s (t - 1 / 2)
    rw [show t - 1 / 2 + 1 = t + 1 / 2 by ring] at this
    exact this
  · have := expPolar_add_half s (t - 1 / 2)
    rw [show t - 1 / 2 + 1 / 2 = t + 0 by ring] at this
    rw [this]; ring

/-- The angular cut-off `β(2 Re ζ/|ζ| + 1)`, `0` near the negative axis, `1` on `Re ζ ≥ 0`. -/
def tauW1 (ζ : ℂ) : ℝ := Real.smoothTransition (2 * (ζ.re / ‖ζ‖) + 1)

/-- The angular partition: `tauAng 1 = tauW1`, `tauAng 0 = 1 - tauW1`. -/
def tauAng (a : Fin 2) (ζ : ℂ) : ℝ := if a = 1 then tauW1 ζ else 1 - tauW1 ζ

lemma sum_tauW (ζ : ℂ) : ∑ a, tauAng a ζ = 1 := by
  simp [Fin.sum_univ_two, tauAng]

lemma contDiffAt_tauW (a : Fin 2) {ζ : ℂ} (hζ : ζ ≠ 0) : ContDiffAt ℝ ∞ (tauAng a) ζ := by
  have h1 : ContDiffAt ℝ ∞ tauW1 ζ := by
    unfold tauW1
    refine Real.smoothTransition.contDiff.contDiffAt.comp ζ ?_
    refine (contDiffAt_const.mul ?_).add contDiffAt_const
    exact Complex.reCLM.contDiff.contDiffAt.div (contDiffAt_norm ℝ hζ) (norm_ne_zero_iff.2 hζ)
  unfold tauAng
  split_ifs
  · exact h1
  · exact contDiffAt_const.sub h1

/-- The closed sectors carrying the two pieces. -/
def secT (a : Fin 2) : Set ℂ := if a = 1 then {ζ | -(‖ζ‖ / 2) ≤ ζ.re} else {ζ | ζ.re ≤ 0}

lemma isClosed_secT (a : Fin 2) : IsClosed (secT a) := by
  unfold secT
  split_ifs
  · exact isClosed_le (by fun_prop) Complex.continuous_re
  · exact isClosed_le Complex.continuous_re continuous_const

lemma mem_secT_of_tauW_ne {a : Fin 2} {ζ : ℂ} (h : tauAng a ζ ≠ 0) : ζ ∈ secT a := by
  unfold tauAng at h
  unfold secT
  by_cases hζ : ζ = 0
  · subst hζ; split_ifs <;> simp
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  split_ifs at h ⊢ with ha
  · have h1 : 0 < 2 * (ζ.re / ‖ζ‖) + 1 := by
      by_contra hc
      exact h (Real.smoothTransition.zero_of_nonpos (not_lt.1 hc))
    have h2 : -(1 / 2) < ζ.re / ‖ζ‖ := by linarith
    rw [lt_div_iff₀ hn] at h2
    change -(‖ζ‖ / 2) ≤ ζ.re
    linarith
  · have h1 : 2 * (ζ.re / ‖ζ‖) + 1 < 1 := by
      by_contra hc
      exact h (by rw [tauW1, Real.smoothTransition.one_of_one_le (not_lt.1 hc), sub_self])
    have h2 : ζ.re / ‖ζ‖ < 0 := by linarith
    rw [div_lt_iff₀ hn, zero_mul] at h2
    exact h2.le

lemma slit_of_mem_secT {a : Fin 2} {ζ : ℂ} (h : ζ ∈ secT a) (h0 : ζ ≠ 0) :
    cSgn a * ζ ∈ Complex.slitPlane := by
  unfold secT at h
  unfold cSgn
  rw [Complex.mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hre : ζ = (ζ.re : ℂ) := by
    apply Complex.ext <;> simp
    split_ifs at hc <;> simpa using hc.2
  have hn : ‖ζ‖ = |ζ.re| := by rw [hre, Complex.norm_real, Real.norm_eq_abs]; simp
  apply h0
  rw [hre]
  split_ifs at h hc with ha
  · simp only [one_mul] at hc
    change -(‖ζ‖ / 2) ≤ ζ.re at h
    rw [hn, abs_of_nonpos hc.1] at h
    have : ζ.re = 0 := by linarith
    simp [this]
  · change ζ.re ≤ 0 at h
    have : 0 ≤ ζ.re := by simpa using hc.1
    simp [le_antisymm h this]

/-- The angular partition on the circle, `tauT a t = tauAng a (e^{-2πit})`. -/
def tauT (a : Fin 2) (t : ℝ) : ℝ := tauAng a (expPolar (0, t))

lemma tauT_add_int (a : Fin 2) (t : ℝ) (n : ℤ) : tauT a (t + n) = tauT a t := by
  rw [tauT, tauT, expPolar_add_int]

lemma sum_tauT (t : ℝ) : ∑ a, tauT a t = 1 := sum_tauW _

lemma contDiff_expPolar_sh (α β : ℝ) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => expPolar (p.1 + α, p.2 + β) := by
  simp only [expPolar_def]
  refine Complex.contDiff_exp.comp (contDiff_const.mul ?_)
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_fst.add contDiff_const)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_snd.add contDiff_const)).mul contDiff_const)

lemma contDiff_tauT (a : Fin 2) : ContDiff ℝ ∞ (tauT a) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  have h : ContDiff ℝ ∞ fun t : ℝ => expPolar (0, t) := by
    have := (contDiff_expPolar_sh 0 0).comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ∞ fun t : ℝ => ((0 : ℝ), t))
    simpa [Function.comp_def] using this
  exact (contDiffAt_tauW a (expPolar_ne_zero _)).comp t h.contDiffAt

lemma re_expPolar_zero (t : ℝ) : (expPolar (0, t)).re = Real.cos (2 * Real.pi * t) := by
  rw [expPolar_def, Complex.exp_re]
  simp only [Complex.ofReal_zero, zero_add]
  have e1 : (-2 * (Real.pi : ℂ) * ((t : ℂ) * Complex.I)).re = 0 := by simp
  have e2 : (-2 * (Real.pi : ℂ) * ((t : ℂ) * Complex.I)).im = -(2 * Real.pi * t) := by simp
  rw [e1, e2, Real.exp_zero, one_mul, Real.cos_neg]

lemma norm_expPolar_zero (t : ℝ) : ‖expPolar (0, t)‖ = 1 := by
  rw [norm_expPolar]; simp

lemma cos_le_half {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) (h : Real.cos (2 * Real.pi * r) ≤ 1 / 2) :
    r ∈ Icc (1 / 6 : ℝ) (5 / 6) := by
  have hπ := Real.pi_pos
  obtain ⟨h0, h1⟩ := hr
  by_contra hc
  rw [mem_Icc, not_and_or, not_le, not_le] at hc
  rcases hc with hc | hc
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 2 * Real.pi * r) (y := Real.pi / 3)
      (by positivity) (by linarith) (by nlinarith)
    rw [Real.cos_pi_div_three] at this
    linarith
  · have e : Real.cos (2 * Real.pi * r) = Real.cos (2 * Real.pi * (1 - r)) := by
      rw [show 2 * Real.pi * (1 - r) = 2 * Real.pi - 2 * Real.pi * r by ring, Real.cos_two_pi_sub]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 2 * Real.pi * (1 - r))
      (y := Real.pi / 3) (by nlinarith) (by linarith) (by nlinarith)
    rw [Real.cos_pi_div_three] at this
    linarith

lemma mem_of_tauT_ne {a : Fin 2} {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1)
    (h : tauT a (r + thetaN a) ≠ 0) : r ∈ Icc (1 / 6 : ℝ) (5 / 6) := by
  have hs := mem_secT_of_tauW_ne h
  refine cos_le_half hr ?_
  unfold secT thetaN at hs
  split_ifs at hs with ha
  · rw [expPolar_add_half] at hs
    change -(‖-expPolar (0, r)‖ / 2) ≤ (-expPolar (0, r)).re at hs
    rw [norm_neg, norm_expPolar_zero, Complex.neg_re, re_expPolar_zero] at hs
    linarith
  · change (expPolar (0, r + 0)).re ≤ 0 at hs
    rw [add_zero, re_expPolar_zero] at hs
    linarith

/-- The cut-off `β(12t - 1) β(11 - 12t)` in `t`: `1` on `[1/6, 5/6]`, `0` off `(1/12, 11/12)`. -/
def cutT (t : ℝ) : ℝ := Real.smoothTransition (12 * t - 1) * Real.smoothTransition (11 - 12 * t)

lemma contDiff_cutT : ContDiff ℝ ∞ cutT :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

lemma cutT_eq_one {t : ℝ} (ht : t ∈ Icc (1 / 6 : ℝ) (5 / 6)) : cutT t = 1 := by
  rw [cutT, Real.smoothTransition.one_of_one_le (by linarith [ht.1]),
    Real.smoothTransition.one_of_one_le (by linarith [ht.2]), one_mul]

lemma mem_of_cutT_ne {t : ℝ} (h : cutT t ≠ 0) : t ∈ Icc (1 / 12 : ℝ) (11 / 12) := by
  constructor
  · by_contra hc
    exact h (by rw [cutT, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul])
  · by_contra hc
    exact h (by rw [cutT, Real.smoothTransition.zero_of_nonpos (x := 11 - 12 * t) (by linarith),
      mul_zero])

/-- **The two pieces cover the circle**: `∑_a cutT(t_a) tauT_a(t_a + θ_a) = 1`, where
`t_a = rot θ_a t` is `t - θ_a` read in `(0, 1]`. -/
lemma sum_cutT_tauT (t : ℝ) :
    ∑ a, cutT (Neck.rot (thetaN a) t) * tauT a (Neck.rot (thetaN a) t + thetaN a) = 1 := by
  have e : ∀ a, cutT (Neck.rot (thetaN a) t) * tauT a (Neck.rot (thetaN a) t + thetaN a) =
      tauT a t := by
    intro a
    obtain ⟨k, hk⟩ := Neck.rot_int (thetaN a) t
    have h1 : tauT a (Neck.rot (thetaN a) t + thetaN a) = tauT a t := by
      rw [hk, show t - thetaN a + k + thetaN a = t + k by ring, tauT_add_int]
    by_cases h : tauT a t = 0
    · rw [h1, h, mul_zero]
    · rw [h1, cutT_eq_one (mem_of_tauT_ne (Neck.rot_mem _ _) (h1.symm ▸ h)), one_mul]
  rw [Finset.sum_congr rfl fun a _ => e a, sum_tauT]

end Angle

/-! ## 5. The charts of the necks and the discs -/

section Charts

lemma contDiffAt_logE {ζ : ℂ} (h : ζ ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ logE ζ := by
  have hl : ContDiffAt ℝ ∞ Complex.log ζ := (Complex.contDiffAt_log h).restrict_scalars ℝ
  exact ((Complex.reCLM.contDiff.contDiffAt.comp ζ hl).neg.div_const _).prodMk
    ((Complex.imCLM.contDiff.contDiffAt.comp ζ hl).neg.div_const _)

lemma expPolar_mem_slitPlane {s t : ℝ} (h1 : -(1 / 2) < t) (h2 : t < 1 / 2) :
    expPolar (s, t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨?_, expPolar_ne_zero _⟩
  have := logE_expPolar (s := s) h1.le h2
  have e := congrArg Prod.snd this
  simp only [logE, Complex.log_im] at e
  intro h
  rw [h] at e
  have hπ := Real.pi_pos
  have : -Real.pi / (2 * Real.pi) = -(1 / 2) := by field_simp
  rw [neg_div, ← neg_div, this] at e
  linarith

lemma logE_snd_mem {ζ : ℂ} (h : ζ ∈ Complex.slitPlane) :
    (logE ζ).2 + 1 / 2 ∈ Ioo (0 : ℝ) 1 := by
  have hπ := Real.pi_pos
  have ha := (Complex.mem_slitPlane_iff_arg.1 h).1
  have h1 := Complex.neg_pi_lt_arg ζ
  have h2 := lt_of_le_of_ne (Complex.arg_le_pi ζ) ha
  have h3 : -(1 / 2) < ζ.arg / (2 * Real.pi) := by rw [lt_div_iff₀ (by positivity)]; linarith
  have h4 : ζ.arg / (2 * Real.pi) < 1 / 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
  simp only [logE, Complex.log_im, neg_div]
  constructor <;> linarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- **The conditions on an atlas under which we build gluing data**: the neck charts are onto
`ℂ`, smooth with smooth inverses, with pairwise disjoint sources, and the closed discs
`r² ≤ 1/8` avoid the nodal points. -/
structure GlueCharts : Prop where
  target : ∀ j, (A.hol j).target = univ
  smooth : ∀ j, ∀ y ∈ (A.hol j).source, ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ (A.hol j) y
  smooth_symm : ∀ j, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ (A.hol j).symm
  disjoint : ∀ j j', j ≠ j' → Disjoint (A.hol j).source (A.hol j').source
  avoid : ∀ i, ∀ p ∈ closedDisc, ∀ j, X.discPt (A.center i) (A.ε i) p ≠ A.node j

/-- The holomorphic coordinate `w = φ_j(z)` of the disc point `z = discPt_i(p)`. -/
def wN (i : Fin A.nd) (j : Fin A.nn) (p : ℝ × ℝ) : ℂ :=
  A.hol j (X.discPt (A.center i) (A.ε i) p)

/-- The shifted polar coordinates `σ_j(s + α, t + β)`. -/
def polarSh (j : Fin A.nn) (α β : ℝ) (y : ℝ × ℝ) : X.S :=
  X.polar (A.hol j) (y.1 + α, y.2 + β)

variable {A} (H : GlueCharts A)
include H

lemma contMDiff_polarSh (j : Fin A.nn) (α β : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) ∞ (polarSh A j α β) :=
  (H.smooth_symm j).comp (contDiff_expPolar_sh α β).contMDiff

lemma continuous_polarSh (j : Fin A.nn) (α β : ℝ) : Continuous (polarSh A j α β) :=
  (contMDiff_polarSh H j α β).continuous

lemma polarSh_mem_source (j : Fin A.nn) (α β : ℝ) (y : ℝ × ℝ) :
    polarSh A j α β y ∈ (A.hol j).source :=
  X.polar_mem_source (by rw [H.target j]; trivial)

lemma hol_polarSh (j : Fin A.nn) (α β : ℝ) (y : ℝ × ℝ) :
    A.hol j (polarSh A j α β y) = expPolar (y.1 + α, y.2 + β) :=
  (A.hol j).right_inv (by rw [H.target j]; trivial)

/-- The disc coordinates of the shifted polar coordinates are smooth where they are defined. -/
lemma contDiffAt_chart_polarSh (z : X.S) (ε : ℝ) (j : Fin A.nn) (α β : ℝ) {y : ℝ × ℝ}
    (hy : polarSh A j α β y ∈ (extChartAt 𝓘(ℝ, E2) z).source) :
    ContDiffAt ℝ ∞ (fun y => placeInv z ε (extChartAt 𝓘(ℝ, E2) z (polarSh A j α β y))) y := by
  have h1 : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) ∞ (extChartAt 𝓘(ℝ, E2) z) (polarSh A j α β y) :=
    contMDiffAt_extChartAt' (by rwa [← extChartAt_source 𝓘(ℝ, E2)])
  have h2 := contMDiffAt_iff_contDiffAt.1 (h1.comp y (contMDiff_polarSh H j α β y))
  exact (contDiff_placeInv z ε).contDiffAt.comp y h2

variable (hT : ChartsOnto X)
include hT

lemma contDiffAt_wN (i : Fin A.nd) (j : Fin A.nn) {p : ℝ × ℝ}
    (hp : X.discPt (A.center i) (A.ε i) p ∈ (A.hol j).source) : ContDiffAt ℝ ∞ (wN A i j) p :=
  contMDiffAt_iff_contDiffAt.1 ((H.smooth j _ hp).comp p ((contMDiff_discPt hT _ _) p))

omit H in
lemma continuousOn_wN (i : Fin A.nd) (j : Fin A.nn) :
    ContinuousOn (wN A i j) (X.discPt (A.center i) (A.ε i) ⁻¹' (A.hol j).source) :=
  (A.hol j).continuousOn.comp (continuous_discPt hT _ _).continuousOn fun _ hp => hp

lemma wN_ne_zero {i : Fin A.nd} {j : Fin A.nn} {p : ℝ × ℝ} (hp : p ∈ closedDisc)
    (hs : X.discPt (A.center i) (A.ε i) p ∈ (A.hol j).source) : wN A i j p ≠ 0 := by
  intro h0
  obtain ⟨hn, hn0, -⟩ := A.isHol j
  exact H.avoid i p hp j ((A.hol j).injOn hs hn (h0.trans hn0.symm))

end Charts

lemma discPt_placeInv {m : ℕ} {X : NodalSurface m} {z : X.S} {ε : ℝ} (hε : ε ≠ 0) {x : X.S}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E2) z).source) :
    X.discPt z ε (placeInv z ε (extChartAt 𝓘(ℝ, E2) z x)) = x := by
  rw [NodalSurface.discPt, place_placeInv z hε, (extChartAt 𝓘(ℝ, E2) z).left_inv hx]

lemma tsupport_dCut_sub (d : Fin 2) : tsupport (dCut d) ⊆ closedDisc :=
  (ChartChange.tsupport_dir_subset _ _).trans tsupport_discCut

/-- `s - s₀` at the point `w` of the neck: `-log|w| / 2π - s₀`. -/
def lamN (s₀ : ℝ) (ζ : ℂ) : ℝ := -Real.log ‖ζ‖ / (2 * Real.pi) - s₀

lemma contDiffAt_lamN (s₀ : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) : ContDiffAt ℝ ∞ (lamN s₀) ζ :=
  ((((Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hζ)).comp ζ (contDiffAt_norm ℝ hζ)).neg.div_const
    _).sub contDiffAt_const)

lemma lamN_pos {s₀ : ℝ} {ζ : ℂ} (hζ : ζ ≠ 0) (h : ‖ζ‖ < Real.exp (-2 * Real.pi * s₀)) :
    0 < lamN s₀ ζ := by
  have hπ := Real.pi_pos
  have hl := (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hζ)).2 h
  unfold lamN
  rw [sub_pos, lt_div_iff₀ (by positivity)]
  linarith

/-! ## 6. The changes of charts from the discs to the necks -/

section DiscNeck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- The compact set of the piece `a` of the change from the disc `i` to the neck `j`. -/
def KDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) : Set (ℝ × ℝ) :=
  closedDisc ∩ X.discPt (A.center i) (A.ε i) ⁻¹'
    (tsupport (chiSN (A.hol j) (A.s0 j)) ∩ A.hol j ⁻¹' secT a)

/-- The open set where the piece `a` is defined. -/
def UDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) : Set (ℝ × ℝ) :=
  X.discPt (A.center i) (A.ε i) ⁻¹'
    ((A.hol j).source ∩ A.hol j ⁻¹' ((fun ζ => cSgn a * ζ) ⁻¹' Complex.slitPlane))

/-- The change from the disc `i` to the neck `j` (rotated by `θ a`): `(s - s₀, t)` with
`e^{-2π(s+it)} = c a · w`. -/
def fDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (p : ℝ × ℝ) : ℝ × ℝ :=
  logE (cSgn a * wN A i j p) + (-A.s0 j, 1 / 2)

/-- Its inverse: the disc coordinates of `σ_j(s + s₀, t - θ a)`. -/
def gDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (y : ℝ × ℝ) : ℝ × ℝ :=
  placeInv (A.center i) (A.ε i)
    (extChartAt 𝓘(ℝ, E2) (A.center i) (polarSh A j (A.s0 j) (-thetaN a) y))

/-- The coefficients `∂_d β · χ_j · τ_a(w) / β(s - s₀)` of the neck blocks in the disc rows. -/
def cNf (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (p : ℝ × ℝ) : ℝ :=
  dCut d p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
    (tauAng a (wN A i j p) / Real.smoothTransition (lamN (A.s0 j) (wN A i j p)))

lemma cSgn_ne_zero (a : Fin 2) : cSgn a ≠ 0 := by unfold cSgn; split_ifs <;> norm_num

variable {A} (H : GlueCharts A) (hT : ChartsOnto X)
include H

lemma polarSh_fDn {i : Fin A.nd} {j : Fin A.nn} (a : Fin 2) {p : ℝ × ℝ}
    (hs : X.discPt (A.center i) (A.ε i) p ∈ (A.hol j).source) (hw : wN A i j p ≠ 0) :
    polarSh A j (A.s0 j) (-thetaN a) (fDn A i j a p) = X.discPt (A.center i) (A.ε i) p := by
  set ζ := cSgn a * wN A i j p
  have hζ : ζ ≠ 0 := mul_ne_zero (cSgn_ne_zero a) hw
  have e : ((fDn A i j a p).1 + A.s0 j, (fDn A i j a p).2 + -thetaN a) =
      ((logE ζ).1, (logE ζ).2 + 1 / 2 - thetaN a) := by
    simp only [fDn, Prod.fst_add, Prod.snd_add]; ext <;> simp <;> ring
  rw [polarSh, NodalSurface.polar_eq, e, expPolar_theta, expPolar_logE hζ, ← mul_assoc,
    cSgn_mul_self, one_mul, wN, (A.hol j).left_inv hs]

lemma fDn_fst (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) (p : ℝ × ℝ) :
    (fDn A i j a p).1 = lamN (A.s0 j) (wN A i j p) := by
  simp only [fDn, Prod.fst_add, logE, Complex.log_re, norm_cSgn_mul, lamN]
  ring

include hT

lemma isOpen_UDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) : IsOpen (UDn A i j a) :=
  ((A.hol j).isOpen_inter_preimage (Complex.isOpen_slitPlane.preimage
    (continuous_const.mul continuous_id))).preimage (continuous_discPt hT _ _)

lemma isClosed_KDn_aux (j : Fin A.nn) (a : Fin 2) :
    IsClosed (tsupport (chiSN (A.hol j) (A.s0 j)) ∩ A.hol j ⁻¹' secT a) :=
  ContinuousOn.preimage_isClosed_of_isClosed ((A.hol j).continuousOn.mono
    ((tsupport_chiSN_sub (H.smooth_symm j).continuous).trans (zSet_sub (H.target j))))
    (isClosed_tsupport _) (isClosed_secT a)

lemma isCompact_KDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) : IsCompact (KDn A i j a) :=
  isCompact_closedDisc.inter_right ((isClosed_KDn_aux H hT j a).preimage (continuous_discPt hT _ _))

lemma mem_source_of_tsupport {j : Fin A.nn} {y : X.S}
    (hy : y ∈ tsupport (chiSN (A.hol j) (A.s0 j))) : y ∈ (A.hol j).source :=
  zSet_sub (H.target j) (tsupport_chiSN_sub (H.smooth_symm j).continuous hy)

lemma KDn_sub_UDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) : KDn A i j a ⊆ UDn A i j a := by
  rintro p ⟨hp, hs, ha⟩
  have hsrc := mem_source_of_tsupport H hT hs
  exact ⟨hsrc, slit_of_mem_secT ha (wN_ne_zero H hT hp hsrc)⟩

lemma contDiffAt_fDn {i : Fin A.nd} {j : Fin A.nn} (a : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ UDn A i j a) : ContDiffAt ℝ ∞ (fDn A i j a) p := by
  have hw := contDiffAt_wN H hT i j hp.1
  exact ((contDiffAt_logE hp.2).comp p (contDiffAt_const.mul hw)).add contDiffAt_const

lemma gDn_fDn {i : Fin A.nd} {j : Fin A.nn} (a : Fin 2) {p : ℝ × ℝ} (hp : p ∈ UDn A i j a) :
    gDn A i j a (fDn A i j a p) = p := by
  have h2 : cSgn a * wN A i j p ∈ Complex.slitPlane := hp.2
  have hw : wN A i j p ≠ 0 := right_ne_zero_of_mul (Complex.slitPlane_ne_zero h2)
  rw [gDn, polarSh_fDn H a hp.1 hw, extChartAt_discPt hT, placeInv_place _ (A.ε_pos i).ne']

lemma differentiableAt_gDn {i : Fin A.nd} {j : Fin A.nn} (a : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ UDn A i j a) : DifferentiableAt ℝ (gDn A i j a) (fDn A i j a p) := by
  have h2 : cSgn a * wN A i j p ∈ Complex.slitPlane := hp.2
  have hw : wN A i j p ≠ 0 := right_ne_zero_of_mul (Complex.slitPlane_ne_zero h2)
  have hs : polarSh A j (A.s0 j) (-thetaN a) (fDn A i j a p) ∈
      (extChartAt 𝓘(ℝ, E2) (A.center i)).source := by
    rw [polarSh_fDn H a hp.1 hw]; exact discPt_mem_source hT _ _ _
  exact (contDiffAt_chart_polarSh H _ _ j _ _ hs).differentiableAt (by simp)

lemma mapsTo_fDn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) :
    MapsTo (fDn A i j a) (UDn A i j a) openStrip := fun p hp => by
  refine ⟨mem_univ _, ?_⟩
  have : (logE (cSgn a * wN A i j p)).2 + 1 / 2 ∈ Ioo (0 : ℝ) 1 := logE_snd_mem hp.2
  simpa [fDn] using this

/-- **The change of charts from the disc `i` to the neck `j`, piece `a`.** -/
theorem exists_Dn (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) :
    ∃ D : ChartChange, D.K = KDn A i j a ∧ ∀ p ∈ D.K, D.ψ p = fDn A i j a p := by
  obtain ⟨D, hK, hψ⟩ := exists_chartChange_of_leftInv (isCompact_KDn H hT i j a)
    (fun p hp => closedDisc_sub hp.1) (isOpen_UDn H hT i j a) (KDn_sub_UDn H hT i j a)
    (fun p hp => (contDiffAt_fDn H hT a hp).contDiffWithinAt)
    (fun p hp => gDn_fDn H hT a hp) (fun p hp => differentiableAt_gDn H hT a
      (KDn_sub_UDn H hT i j a hp)) ((mapsTo_fDn H hT i j a).mono_left (KDn_sub_UDn H hT i j a))
  exact ⟨D, hK, fun p hp => hψ p (hK ▸ hp)⟩

lemma contDiff_chiSN_discPt (i : Fin A.nd) (j : Fin A.nn) :
    ContDiff ℝ ∞ fun p => chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) :=
  contMDiff_iff_contDiff.1 ((contMDiff_chiSN (H.target j) (H.smooth_symm j).continuous
    (H.smooth j)).comp (contMDiff_discPt hT _ _))

omit H hT in
lemma mem_KDn_of_ne {d : Fin 2} {i : Fin A.nd} {j : Fin A.nn} {a : Fin 2} {p : ℝ × ℝ}
    (h : dCut d p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
      tauAng a (wN A i j p) ≠ 0) : p ∈ KDn A i j a := by
  obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h12
  exact ⟨tsupport_dCut_sub d (subset_tsupport _ h1), subset_tsupport _ h2,
    mem_secT_of_tauW_ne h3⟩

lemma lamN_pos_of_mem {d : Fin 2} {i : Fin A.nd} {j : Fin A.nn} {p : ℝ × ℝ}
    (h1 : p ∈ tsupport (dCut d))
    (h2 : X.discPt (A.center i) (A.ε i) p ∈ tsupport (chiSN (A.hol j) (A.s0 j))) :
    X.discPt (A.center i) (A.ε i) p ∈ (A.hol j).source ∧ wN A i j p ≠ 0 ∧
      ‖wN A i j p‖ < Real.exp (-2 * Real.pi * A.s0 j) := by
  have hsrc := mem_source_of_tsupport H hT h2
  have hz := tsupport_chiSN_sub (H.smooth_symm j).continuous h2
  exact ⟨hsrc, wN_ne_zero H hT (tsupport_dCut_sub d h1) hsrc,
    (norm_le_of_mem_zSet (H.target j) hz).trans_lt (rN_lt _)⟩

lemma contDiff_cNf (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) :
    ContDiff ℝ ∞ (cNf A d i j a) := by
  set y := X.discPt (A.center i) (A.ε i)
  set V : Set (ℝ × ℝ) := y ⁻¹' ((A.hol j).source ∩
    A.hol j ⁻¹' {ζ | ζ ≠ 0 ∧ ‖ζ‖ < Real.exp (-2 * Real.pi * A.s0 j)})
  have hVo : IsOpen V := ((A.hol j).isOpen_inter_preimage (isOpen_ne.inter
    (isOpen_lt continuous_norm continuous_const))).preimage (continuous_discPt hT _ _)
  set W : Set (ℝ × ℝ) := (tsupport (dCut d) ∩ y ⁻¹' tsupport (chiSN (A.hol j) (A.s0 j)))ᶜ
  have hWo : IsOpen W := ((isClosed_tsupport _).inter
    ((isClosed_tsupport _).preimage (continuous_discPt hT _ _))).isOpen_compl
  refine contDiff_of_open_cover hVo hWo (fun p => ?_) ?_ ?_
  · by_cases hp : p ∈ W
    · exact Or.inr hp
    · left
      rw [mem_compl_iff, not_not] at hp
      obtain ⟨h1, h2, h3⟩ := lamN_pos_of_mem H hT hp.1 hp.2
      exact ⟨h1, h2, h3⟩
  · intro p hp
    obtain ⟨hsrc, hne, hlt⟩ := hp
    have hw := contDiffAt_wN H hT i j hsrc
    have hpos := lamN_pos hne hlt
    refine ContDiffAt.contDiffWithinAt ?_
    have hden : ContDiffAt ℝ ∞
        (fun p => Real.smoothTransition (lamN (A.s0 j) (wN A i j p))) p :=
      Real.smoothTransition.contDiff.contDiffAt.comp p
        ((contDiffAt_lamN (A.s0 j) (ζ := wN A i j p) hne).comp p hw)
    have htau : ContDiffAt ℝ ∞ (fun p => tauAng a (wN A i j p)) p :=
      (contDiffAt_tauW a (ζ := wN A i j p) hne).comp p hw
    exact ((contDiff_dCut d).contDiffAt.mul (contDiff_chiSN_discPt H hT i j).contDiffAt).mul
      (htau.div hden (Real.smoothTransition.pos_of_pos hpos).ne')
  · intro p hp
    rw [mem_compl_iff, mem_inter_iff, not_and_or] at hp
    rcases hp with hp | hp
    · simp [cNf, image_eq_zero_of_notMem_tsupport hp]
    · simp [cNf, y, image_eq_zero_of_notMem_tsupport hp]

lemma tsupport_cNf_sub (d : Fin 2) (i : Fin A.nd) (j : Fin A.nn) (a : Fin 2) :
    tsupport (cNf A d i j a) ⊆ KDn A i j a := by
  refine closure_minimal (fun p hp => mem_KDn_of_ne (d := d) ?_) (isCompact_KDn H hT i j a).isClosed
  intro h
  apply hp
  rcases mul_eq_zero.1 h with h' | h'
  · simp [cNf, h']
  · simp [cNf, h']

lemma cNf_mul {d : Fin 2} {i : Fin A.nd} {j : Fin A.nn} {a : Fin 2} {D : ChartChange}
    (hDK : D.K = KDn A i j a) (hDψ : ∀ p ∈ D.K, D.ψ p = fDn A i j a p) (p : ℝ × ℝ) :
    cNf A d i j a p * Real.smoothTransition (D.ψ p).1 =
      dCut d p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
        tauAng a (wN A i j p) := by
  by_cases h : dCut d p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p) *
      tauAng a (wN A i j p) = 0
  · rw [h]
    rcases mul_eq_zero.1 h with h' | h'
    · simp [cNf, h']
    · simp [cNf, h']
  · have hK := mem_KDn_of_ne h
    obtain ⟨h12, -⟩ := mul_ne_zero_iff.1 h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h12
    obtain ⟨-, hne, hlt⟩ := lamN_pos_of_mem H hT (subset_tsupport _ h1) (subset_tsupport _ h2)
    have hpos := Real.smoothTransition.pos_of_pos (lamN_pos hne hlt)
    rw [hDψ p (hDK ▸ hK), fDn_fst H, cNf, mul_assoc, div_mul_cancel₀ _ hpos.ne']

end DiscNeck

/-! ## 7. The changes of charts from the necks to the discs -/

section NeckDisc

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- The compact set of the piece `a` of the change from the neck `j` to the disc `i`. -/
def KDd (j : Fin A.nn) (a : Fin 2) (ρ : X.S → ℝ) : Set (ℝ × ℝ) :=
  (Icc (A.s0 j) (A.s0 j + 1) ×ˢ Icc (1 / 12 : ℝ) (11 / 12)) ∩
    polarSh A j 0 (thetaN a) ⁻¹' tsupport ρ

/-- The open set where the piece `a` is defined. -/
def UDd (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) : Set (ℝ × ℝ) :=
  (Prod.snd ⁻¹' Ioo (0 : ℝ) 1) ∩
    polarSh A j 0 (thetaN a) ⁻¹' (extChartAt 𝓘(ℝ, E2) (A.center i)).source

/-- The change from the neck `j` (rotated by `θ a`) to the disc `i`. -/
def fDd (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (y : ℝ × ℝ) : ℝ × ℝ :=
  placeInv (A.center i) (A.ε i)
    (extChartAt 𝓘(ℝ, E2) (A.center i) (polarSh A j 0 (thetaN a) y))

/-- Its inverse. -/
def gDd (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (p : ℝ × ℝ) : ℝ × ℝ :=
  logE (cSgn a * wN A i j p) + (0, 1 / 2)

/-- The numerator `cutT(t) τ_a(t + θ_a) β'(s - s₀) ρ_i(σ(s, t + θ_a))` of the coefficients of
the disc blocks in the neck rows. -/
def nDd (j : Fin A.nn) (a : Fin 2) (ρ : X.S → ℝ) (y : ℝ × ℝ) : ℝ :=
  cutT y.2 * tauT a (y.2 + thetaN a) * dTr (y.1 - A.s0 j) * ρ (polarSh A j 0 (thetaN a) y)

/-- The coefficients of the disc blocks in the neck rows. -/
def cDf (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (ρ : X.S → ℝ) (y : ℝ × ℝ) : ℝ :=
  nDd A j a ρ y / discCut (fDd A j i a y)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
lemma mem_KDd_of_ne {j : Fin A.nn} {a : Fin 2} {ρ : X.S → ℝ} {y : ℝ × ℝ}
    (h : nDd A j a ρ y ≠ 0) : y ∈ KDd A j a ρ := by
  obtain ⟨h123, h4⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 h123
  obtain ⟨h1, -⟩ := mul_ne_zero_iff.1 h12
  refine ⟨⟨⟨?_, ?_⟩, mem_of_cutT_ne h1⟩, subset_tsupport _ h4⟩
  · by_contra hc; exact h3 (dTr_eq_zero_of_neg (by linarith [not_le.1 hc]))
  · by_contra hc; exact h3 (dTr_eq_zero_of_one_lt (by linarith [not_le.1 hc]))

variable {A} (H : GlueCharts A) (hT : ChartsOnto X)
include H

lemma discPt_fDd {j : Fin A.nn} {i : Fin A.nd} (a : Fin 2) {y : ℝ × ℝ}
    (hy : polarSh A j 0 (thetaN a) y ∈ (extChartAt 𝓘(ℝ, E2) (A.center i)).source) :
    X.discPt (A.center i) (A.ε i) (fDd A j i a y) = polarSh A j 0 (thetaN a) y :=
  discPt_placeInv (A.ε_pos i).ne' hy

lemma cSgn_wN_fDd {j : Fin A.nn} {i : Fin A.nd} (a : Fin 2) {y : ℝ × ℝ}
    (hy : polarSh A j 0 (thetaN a) y ∈ (extChartAt 𝓘(ℝ, E2) (A.center i)).source) :
    cSgn a * wN A i j (fDd A j i a y) = expPolar (y.1 + 0, y.2 - 1 / 2) := by
  rw [wN, discPt_fDd H a hy, hol_polarSh H, cSgn_expPolar_theta]

include hT

lemma isOpen_UDd (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) : IsOpen (UDd A j i a) :=
  (isOpen_Ioo.preimage continuous_snd).inter
    ((isOpen_extChartAt_source _).preimage (continuous_polarSh H j 0 _))

lemma isCompact_KDd (j : Fin A.nn) (a : Fin 2) (ρ : X.S → ℝ) :
    IsCompact (KDd A j a ρ) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_tsupport ρ).preimage (continuous_polarSh H j 0 _))

lemma KDd_sub_UDd {j : Fin A.nn} {i : Fin A.nd} (a : Fin 2) {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i)) : KDd A j a ρ ⊆ UDd A j i a := by
  rintro y ⟨⟨-, h1, h2⟩, h3⟩
  exact ⟨⟨by linarith, by linarith⟩, (hρ h3).1⟩

lemma KDd_sub_strip (j : Fin A.nn) (a : Fin 2) (ρ : X.S → ℝ) :
    KDd A j a ρ ⊆ openStrip := by
  rintro y ⟨⟨-, h1, h2⟩, -⟩
  exact ⟨mem_univ _, by linarith, by linarith⟩

lemma gDd_fDd {j : Fin A.nn} {i : Fin A.nd} (a : Fin 2) {y : ℝ × ℝ} (hy : y ∈ UDd A j i a) :
    gDd A j i a (fDd A j i a y) = y := by
  obtain ⟨⟨h1, h2⟩, hs⟩ := hy
  rw [gDd, cSgn_wN_fDd H a hs, logE_expPolar (by linarith) (by linarith)]
  ext <;> simp

lemma differentiableAt_gDd {j : Fin A.nn} {i : Fin A.nd} (a : Fin 2) {y : ℝ × ℝ}
    (hy : y ∈ UDd A j i a) : DifferentiableAt ℝ (gDd A j i a) (fDd A j i a y) := by
  obtain ⟨⟨h1, h2⟩, hs⟩ := hy
  have hsrc : X.discPt (A.center i) (A.ε i) (fDd A j i a y) ∈ (A.hol j).source := by
    rw [discPt_fDd H a hs]; exact polarSh_mem_source H j 0 _ y
  have hw := contDiffAt_wN H hT i j hsrc
  have hsl : cSgn a * wN A i j (fDd A j i a y) ∈ Complex.slitPlane := by
    rw [cSgn_wN_fDd H a hs]; exact expPolar_mem_slitPlane (by linarith) (by linarith)
  have hm : ContDiffAt ℝ ∞ (fun p => cSgn a * wN A i j p) (fDd A j i a y) :=
    contDiffAt_const.mul hw
  exact ((ContDiffAt.comp (fDd A j i a y) (g := logE) (f := fun p => cSgn a * wN A i j p)
    (contDiffAt_logE hsl) hm).add contDiffAt_const).differentiableAt (by simp)

lemma mapsTo_fDd {j : Fin A.nn} {i : Fin A.nd} (a : Fin 2) {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i)) :
    MapsTo (fDd A j i a) (KDd A j a ρ) openStrip := fun _ hy =>
  discD_sub (hρ hy.2).2

/-- **The change of charts from the neck `j` to the disc `i`, piece `a`.** -/
theorem exists_Dd (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i)) :
    ∃ D : ChartChange, D.K = KDd A j a ρ ∧ ∀ y ∈ D.K, D.ψ y = fDd A j i a y := by
  obtain ⟨D, hK, hψ⟩ := exists_chartChange_of_leftInv (isCompact_KDd H hT j a ρ)
    (KDd_sub_strip H hT j a ρ) (isOpen_UDd H hT j i a) (KDd_sub_UDd H hT a hρ)
    (fun y hy => (contDiffAt_chart_polarSh H _ _ j 0 _ hy.2).contDiffWithinAt)
    (fun y hy => gDd_fDd H hT a hy)
    (fun y hy => differentiableAt_gDd H hT a (KDd_sub_UDd H hT a hρ hy)) (mapsTo_fDd H hT a hρ)
  exact ⟨D, hK, fun y hy => hψ y (hK ▸ hy)⟩

lemma contDiff_cDf (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (ρ : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i)) : ContDiff ℝ ∞ (cDf A j i a ρ) := by
  set V : Set (ℝ × ℝ) := polarSh A j 0 (thetaN a) ⁻¹' discSet (A.center i) (A.ε i)
  have hVo : IsOpen V := (isOpen_discSet _ _).preimage (continuous_polarSh H j 0 _)
  set W : Set (ℝ × ℝ) := (polarSh A j 0 (thetaN a) ⁻¹' tsupport ρ)ᶜ
  have hWo : IsOpen W := ((isClosed_tsupport _).preimage (continuous_polarSh H j 0 _)).isOpen_compl
  have hN : ContDiff ℝ ∞ (nDd A j a ρ) := by
    have hρc : ContDiff ℝ ∞ fun y => ρ (polarSh A j 0 (thetaN a) y) :=
      contMDiff_iff_contDiff.1 (ρ.contMDiff.comp (contMDiff_polarSh H j 0 _))
    exact (((contDiff_cutT.comp contDiff_snd).mul
      ((contDiff_tauT a).comp (contDiff_snd.add contDiff_const))).mul
      (contDiff_dTr.comp (contDiff_fst.sub contDiff_const))).mul hρc
  refine contDiff_of_open_cover hVo hWo (fun y => ?_) (fun y hy => ?_) (fun y hy => ?_)
  · by_cases h : y ∈ W
    · exact Or.inr h
    · exact Or.inl (hρ (not_not.1 h))
  · have hf := contDiffAt_chart_polarSh H (A.center i) (A.ε i) j 0 (thetaN a) hy.1
    have hpos : 0 < discCut (fDd A j i a y) := discCut_pos hy.2
    exact (hN.contDiffAt.div (contDiff_discCut.contDiffAt.comp y hf) hpos.ne').contDiffWithinAt
  · simp [cDf, nDd, image_eq_zero_of_notMem_tsupport hy]

lemma tsupport_cDf_sub (j : Fin A.nn) (i : Fin A.nd) (a : Fin 2) (ρ : X.S → ℝ) :
    tsupport (cDf A j i a ρ) ⊆ KDd A j a ρ := by
  refine closure_minimal (fun y hy => mem_KDd_of_ne A ?_)
    ((isCompact_KDd H hT j a ρ).isClosed)
  intro h
  exact hy (by simp [cDf, h])

lemma cDf_mul {j : Fin A.nn} {i : Fin A.nd} {a : Fin 2} {ρ : X.S → ℝ}
    (hρ : tsupport ρ ⊆ discSet (A.center i) (A.ε i)) {D : ChartChange}
    (hDK : D.K = KDd A j a ρ) (hDψ : ∀ y ∈ D.K, D.ψ y = fDd A j i a y) (y : ℝ × ℝ) :
    cDf A j i a ρ y * discCut (D.ψ y) = nDd A j a ρ y := by
  by_cases h : nDd A j a ρ y = 0
  · simp [cDf, h]
  · have hK := mem_KDd_of_ne A h
    have hpos : 0 < discCut (fDd A j i a y) := discCut_pos (hρ hK.2).2
    rw [hDψ y (hDK ▸ hK), cDf, div_mul_cancel₀ _ hpos.ne']

omit hT in
lemma polarSh_shT (j : Fin A.nn) (a : Fin 2) (x : ℝ × ℝ) :
    polarSh A j 0 (thetaN a) (Neck.shT 0 (thetaN a) x) = X.polar (A.hol j) x := by
  obtain ⟨k, hk⟩ := Neck.rot_int (thetaN a) x.2
  have e : ((Neck.shT 0 (thetaN a) x).1 + 0, (Neck.shT 0 (thetaN a) x).2 + thetaN a) =
      (x.1, x.2 + k) := by
    simp only [Neck.shT, sub_zero, add_zero, hk]; ext <;> simp; ring
  rw [polarSh, e, polar_add_int]

end NeckDisc

/-! ## 8. The partition and the gluing data -/

section Assembly

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} (A : SectionAtlas (E := E) X (fun _ => q))

/-- The union of the cores `r² ≤ 1/16` of the discs. -/
def coreSet : Set X.S :=
  ⋃ i, X.discPt (A.center i) (A.ε i) '' {p : ℝ × ℝ | p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 16}

lemma isCompact_core : IsCompact {p : ℝ × ℝ | p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 16} :=
  isCompact_closedDisc.of_isClosed_subset (isClosed_le (by fun_prop) continuous_const)
    fun p hp => by simp only [closedDisc, mem_ofPred_eq] at hp ⊢; linarith

variable {A}

lemma isClosed_coreSet (hT : ChartsOnto X) : IsClosed (coreSet A) :=
  isClosed_iUnion_of_finite fun _ => (isCompact_core.image (continuous_discPt hT _ _)).isClosed

lemma core_sub_discSet (hT : ChartsOnto X) :
    coreSet A ⊆ ⋃ i, discSet (A.center i) (A.ε i) := by
  intro y hy
  obtain ⟨i, p, hp, rfl⟩ := mem_iUnion.1 hy
  refine mem_iUnion.2 ⟨i, discPt_mem_source hT _ _ p, ?_⟩
  change placeInv _ _ (extChartAt 𝓘(ℝ, E2) _ (X.discPt _ _ p)) ∈ discD
  rw [extChartAt_discPt hT, placeInv_place _ (A.ε_pos i).ne']
  exact mem_discD_of_core hp

variable (H : GlueCharts A) (hT : ChartsOnto X)

/-- The neck functions as smooth functions on the surface. -/
def chiSb (j : Fin A.nn) : C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯ :=
  ⟨chiSN (A.hol j) (A.s0 j),
    contMDiff_chiSN (H.target j) (H.smooth_symm j).continuous (H.smooth j)⟩

include H

lemma sum_chiSN_of_mem {j : Fin A.nn} {y : X.S} (hy : y ∈ (A.hol j).source) :
    ∑ j', chiSN (A.hol j') (A.s0 j') y = chiSN (A.hol j) (A.s0 j) y :=
  Finset.sum_eq_single j (fun j' _ hj' => chiSN_of_not_mem fun h =>
    Set.disjoint_left.1 (H.disjoint j' j hj') h hy) (by simp)

lemma chiSN_polar_cross (j j' : Fin A.nn) (p : ℝ × ℝ) :
    chiSN (A.hol j') (A.s0 j') (X.polar (A.hol j) p) =
      if j' = j then chiN (A.s0 j) p.1 else 0 := by
  have hs : X.polar (A.hol j) p ∈ (A.hol j).source :=
    X.polar_mem_source (by rw [H.target j]; trivial)
  split_ifs with h
  · subst h; exact chiSN_polar (H.target j') p
  · exact chiSN_of_not_mem fun h' => Set.disjoint_left.1 (H.disjoint j j' (Ne.symm h)) hs h'

lemma support_sub_core :
    support (fun y => 1 - ∑ j, chiSN (A.hol j) (A.s0 j) y) ⊆ coreSet A := by
  intro y hy
  rcases A.cover y with ⟨i, p, hp, rfl⟩ | ⟨j, h | ⟨p, hp, rfl⟩⟩
  · exact mem_iUnion.2 ⟨i, p, hp, rfl⟩
  · exfalso; apply hy
    obtain ⟨hn, hn0, -⟩ := A.isHol j
    rw [h]
    change 1 - ∑ j', chiSN (A.hol j') (A.s0 j') (A.node j) = 0
    rw [sum_chiSN_of_mem H hn, chiSN_of_mem hn, hn0, norm_zero,
      gN_eq_one (by norm_num; positivity), sub_self]
  · exfalso; apply hy
    change 1 - ∑ j', chiSN (A.hol j') (A.s0 j') (X.polar (A.hol j) p) = 0
    rw [sum_chiSN_of_mem H (X.polar_mem_source (by rw [H.target j]; trivial)),
      chiSN_polar (H.target j), chiN_one hp, sub_self]

include hT

/-- **The partition of unity**: `ρ_i = (1 - ∑ χ_j) τ_i`, `τ` subordinate to the discs on the
support of `1 - ∑ χ_j`. -/
theorem exists_rho_neck : ∃ ρ : Fin A.nd → C^∞⟮𝓘(ℝ, E2), X.S; 𝓘(ℝ), ℝ⟯,
    (∀ i, tsupport (ρ i) ⊆ discSet (A.center i) (A.ε i)) ∧
      ∀ y, ∑ i, ρ i y + ∑ j, chiSN (A.hol j) (A.s0 j) y = 1 := by
  set S : X.S → ℝ := fun y => ∑ j, chiSN (A.hol j) (A.s0 j) y with hSdef
  have hS : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ S :=
    contMDiff_finsetSum fun j _ => (chiSb H j).contMDiff
  have hC : tsupport (fun y => 1 - S y) ⊆ ⋃ i, discSet (A.center i) (A.ε i) :=
    (closure_minimal (support_sub_core H) (isClosed_coreSet hT)).trans (core_sub_discSet hT)
  obtain ⟨τ, hτ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E2) (isClosed_tsupport _)
    (fun i => discSet (A.center i) (A.ε i)) (fun i => isOpen_discSet _ _) hC
  have hm : ∀ i, ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ) ∞ fun y => (1 - S y) * τ i y := fun i =>
    (contMDiff_const.sub hS).mul (τ i).contMDiff
  refine ⟨fun i => ⟨fun y => (1 - S y) * τ i y, hm i⟩, fun i => ?_, fun y => ?_⟩
  · exact (tsupport_mul_subset_right (f := fun y => 1 - S y) (g := τ i)).trans (hτ i)
  · change ∑ i, (1 - S y) * τ i y + S y = 1
    by_cases hy : y ∈ tsupport (fun y => 1 - S y)
    · have h := τ.sum_eq_one hy
      rw [finsum_eq_sum_of_fintype] at h
      rw [← Finset.mul_sum, h, mul_one, sub_add_cancel]
    · have h0 : 1 - S y = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => 1 - S y) hy
      simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
      linarith

/-- **Gluing data with necks exist** on an atlas satisfying `GlueCharts`. -/
theorem nonempty_glueDataN : Nonempty (GlueDataN A) := by
  obtain ⟨ρ, hρ, hsum⟩ := exists_rho_neck H hT
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ j)
  choose Dn hDnK hDnψ using fun i j a => exists_Dn H hT i j a
  choose Dd hDdK hDdψ using fun j i a => exists_Dd H hT j i a (hρ i)
  refine ⟨{
    ρ := ρ
    hρ := hρ
    D := D
    hDK := hDK
    hDψ := hDψ
    χ := fun j => chiN (A.s0 j)
    χ_smooth := fun j => contDiff_chiN _
    χ_zero := fun j s hs => chiN_zero hs
    χ_one := fun j s hs => chiN_one hs
    χS := chiSb H
    χS_polar := fun j j' p _ _ => chiSN_polar_cross H j j' p
    sum_one := hsum
    θ := thetaN
    Dn := Dn
    cN := fun d i j a => cNf A d i j a
    cN_smooth := fun d i j a => contDiff_cNf H hT d i j a
    cN_supp := fun d i j a => (hDnK i j a).symm ▸ tsupport_cNf_sub H hT d i j a
    Dn_pt := fun i j a p hp => ?_
    cN_sum := fun d i j p => ?_
    Dd := Dd
    cD := fun j i a => cDf A j i a (ρ i)
    cD_smooth := fun j i a => contDiff_cDf H hT j i a (ρ i) (hρ i)
    cD_supp := fun j i a => (hDdK j i a).symm ▸ tsupport_cDf_sub H hT j i a (ρ i)
    Dd_pt := fun j i a y hy => ?_
    cD_sum := fun j i x => ?_ }⟩
  · have hU := KDn_sub_UDn H hT i j a (hDnK i j a ▸ hp)
    have h2 : cSgn a * wN A i j p ∈ Complex.slitPlane := hU.2
    have hw : wN A i j p ≠ 0 := right_ne_zero_of_mul (Complex.slitPlane_ne_zero h2)
    have := polarSh_fDn H a hU.1 hw
    rw [hDnψ i j a p hp]
    simpa [polarSh, sub_eq_add_neg] using this
  · change ∑ a, cNf A d i j a p * Real.smoothTransition ((Dn i j a).ψ p).1 =
      dCut d p * chiSN (A.hol j) (A.s0 j) (X.discPt (A.center i) (A.ε i) p)
    rw [Finset.sum_congr rfl fun a _ => cNf_mul H hT (hDnK i j a) (hDnψ i j a) p,
      ← Finset.mul_sum, sum_tauW, mul_one]
  · have hU := KDd_sub_UDd H hT a (hρ i) (hDdK j i a ▸ hy)
    rw [hDdψ j i a y hy, discPt_fDd H a hU.2, polarSh, add_zero]
  · change ∑ a, cDf A j i a (ρ i) (Neck.shT 0 (thetaN a) x) *
        discCut ((Dd j i a).ψ (Neck.shT 0 (thetaN a) x)) =
      dTr (x.1 - A.s0 j) * ρ i (X.polar (A.hol j) x)
    rw [Finset.sum_congr rfl fun a _ => cDf_mul H hT (hρ i) (hDdK j i a) (hDdψ j i a) _]
    simp only [nDd, polarSh_shT H]
    simp only [Neck.shT, sub_zero]
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_cutT_tauT, one_mul]

end Assembly

/-! ## 9. An atlas of `twoSpheres` with injective node map and closed discs off the nodes -/

section AtlasGlue

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

open NodalSurface

variable {m : ℕ} (X : NodalSurface m)

/-- **Witness**: an atlas of semi-norms with prescribed holomorphic charts at the nodal points,
one neck chart at each nodal point (the node map is injective), and closed discs `r² ≤ 1/8`
off the nodal points (the proof of `exists_sectionAtlas_of_charts`). -/
theorem exists_sectionAtlas_glue (u : X.S → Q) (hu : Continuous u)
    (φ₀ : X.S → OpenPartialHomeomorph X.S ℂ) (hφ₀ : ∀ x ∈ X.nodalPts, X.IsHolChart (φ₀ x) x) :
    ∃ A : SectionAtlas (E := E) X u, (∀ j, A.hol j = φ₀ (A.node j)) ∧ Injective A.node ∧
      ∀ i, ∀ p ∈ closedDisc, ∀ j, X.discPt (A.center i) (A.ε i) p ≠ A.node j := by
  have hN := X.finite_nodalPts
  have hNc : IsClosed X.nodalPts := hN.isClosed
  have := hN.fintype
  set φ : X.nodalPts → OpenPartialHomeomorph X.S ℂ := fun x => φ₀ x.1
  have hφ : ∀ x : X.nodalPts, X.IsHolChart (φ x) x := fun x => hφ₀ x.1 x.2
  choose s0 hs0 using fun x : X.nodalPts => exists_neck_s0 (E := E) hu (hφ x)
  -- the small discs around the nodal points
  set O : X.nodalPts → Set X.S := fun x =>
    (φ x).source ∩ φ x ⁻¹' Metric.ball 0 (Real.exp (-2 * Real.pi * (s0 x + 1)))
  have hOo : ∀ x, IsOpen (O x) := fun x => (φ x).isOpen_inter_preimage Metric.isOpen_ball
  have hxO : ∀ x, x.1 ∈ O x := fun x =>
    ⟨(hφ x).1, by rw [mem_preimage, (hφ x).2.1]; exact Metric.mem_ball_self (Real.exp_pos _)⟩
  set K : Set X.S := (⋃ x, O x)ᶜ
  have hK : IsCompact K := (isOpen_iUnion hOo).isClosed_compl.isCompact
  have hKN : ∀ z ∈ K, z ∉ X.nodalPts := fun z hz hzN =>
    hz (mem_iUnion.2 ⟨⟨z, hzN⟩, hxO ⟨z, hzN⟩⟩)
  set e := Fintype.equivFin X.nodalPts
  -- the disc charts away from the nodal points
  have hW : ∀ z : X.S, z ∉ X.nodalPts → ∃ ε > 0, ∀ w ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) ε,
      w ∈ (extChartAt 𝓘(ℝ, E2) z).target ∧
        u ((extChartAt 𝓘(ℝ, E2) z).symm w) ∈ (extChartAt 𝓘(ℝ, E) (u z)).source ∧
        (extChartAt 𝓘(ℝ, E2) z).symm w ∉ X.nodalPts := by
    intro z hz
    have h1 : (extChartAt 𝓘(ℝ, E2) z).target ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) :=
      extChartAt_target_mem_nhds z
    have hsc : ContinuousAt (extChartAt 𝓘(ℝ, E2) z).symm (extChartAt 𝓘(ℝ, E2) z z) :=
      continuousAt_extChartAt_symm z
    have h2 : (fun w => u ((extChartAt 𝓘(ℝ, E2) z).symm w)) ⁻¹' (extChartAt 𝓘(ℝ, E) (u z)).source
        ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      refine (hu.continuousAt.comp hsc).preimage_mem_nhds ?_
      rw [Function.comp_apply, extChartAt_to_inv]
      exact extChartAt_source_mem_nhds (u z)
    have h3 : (extChartAt 𝓘(ℝ, E2) z).symm ⁻¹' X.nodalPtsᶜ ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      refine hsc.preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact hNc.isOpen_compl.mem_nhds hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem h1 h2) h3)
    exact ⟨ε, hε, fun w hw => ⟨(hball hw).1.1, (hball hw).1.2, (hball hw).2⟩⟩
  choose! ε hε hball using hW
  set U : X.S → Set X.S := fun z => (extChartAt 𝓘(ℝ, E2) z).source ∩
    (extChartAt 𝓘(ℝ, E2) z) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z / 4) with hU
  have hUo : ∀ z, IsOpen (U z) := fun z =>
    (continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z)
      Metric.isOpen_ball
  have hUz : ∀ z ∈ K, z ∈ U z := fun z hz =>
    ⟨mem_extChartAt_source z, Metric.mem_ball_self (by linarith [hε z (hKN z hz)])⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => U z) (fun z => hUo z)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hUz y hy⟩)
  have hplace : ∀ z (p : ℝ × ℝ), 0 < ε z → p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 8 →
      X.place z (ε z) p ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z) := by
    intro z p hεz hp
    rw [Metric.mem_ball, NodalSurface.place, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hεz.le]
    have hn :
        ‖EuclideanSpace.single (0 : Fin 2) p.1 + EuclideanSpace.single 1 (p.2 - 1 / 2)‖ < 1 := by
      have := norm_sq_single_add_single p.1 (p.2 - 1 / 2)
      nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin 2) p.1 +
        EuclideanSpace.single 1 (p.2 - 1 / 2))]
    nlinarith
  have hcK : ∀ i : Fin t.card, (t.equivFin.symm i).1.1 ∉ X.nodalPts := fun i =>
    hKN _ (t.equivFin.symm i).1.2
  refine ⟨{
    nd := t.card
    center := fun i => (t.equivFin.symm i).1.1
    ε := fun i => ε (t.equivFin.symm i).1.1
    ε_pos := fun i => hε _ (hcK i)
    disc_chart := fun i p hp =>
      ⟨(hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp.le)).1,
        (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp.le)).2.1⟩
    disc_avoid := fun i p hp q hq hmem =>
      (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp.le)).2.2 ⟨q, hq, hmem⟩
    nn := Fintype.card X.nodalPts
    node := fun j => (e.symm j).1
    hol := fun j => φ (e.symm j)
    s0 := fun j => s0 (e.symm j)
    isHol := fun j => hφ (e.symm j)
    neck_chart := fun j => hs0 (e.symm j)
    node_nodal := fun j => (e.symm j).2
    nodal_node := fun q hq x hx => ⟨e ⟨x, q, hq, hx⟩, by simp⟩
    cover := fun y => ?_ }, fun j => rfl, fun j j' h => e.symm.injective (Subtype.ext h),
      fun i p hp j hj => (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.2 (by
        change X.discPt _ _ p ∈ X.nodalPts
        rw [hj]; exact (e.symm j).2)⟩
  by_cases hyK : y ∈ K
  · left
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht hyK)
    obtain ⟨hys, hyb⟩ := hyz
    refine ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    have hεz := hε z.1 (hKN z.1 z.2)
    set w : E2 := (ε z.1)⁻¹ • (extChartAt 𝓘(ℝ, E2) z.1 y - extChartAt 𝓘(ℝ, E2) z.1 z.1) with hw
    have hwn : ‖w‖ < 1 / 4 := by
      rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hεz.le), ← dist_eq_norm]
      rw [mem_preimage, Metric.mem_ball] at hyb
      rw [inv_mul_lt_iff₀ hεz]; linarith
    refine ⟨(w 0, w 1 + 1 / 2), ?_, ?_⟩
    · have h := norm_sq_single_add_single (w 0) (w 1)
      rw [single_add_single_eq] at h
      simp only [add_sub_cancel_right]
      nlinarith [norm_nonneg w]
    · have hpl : X.place z.1 (ε z.1) (w 0, w 1 + 1 / 2) = extChartAt 𝓘(ℝ, E2) z.1 y := by
        rw [NodalSurface.place]
        simp only [add_sub_cancel_right]
        rw [single_add_single_eq, hw, smul_smul, mul_inv_cancel₀ hεz.ne', one_smul,
          add_sub_cancel]
      rw [NodalSurface.discPt, hpl, (extChartAt 𝓘(ℝ, E2) z.1).left_inv hys]
  · right
    obtain ⟨x, hyO⟩ := mem_iUnion.1 (not_not.1 hyK)
    refine ⟨e x, ?_⟩
    simp only [Equiv.symm_apply_apply]
    obtain ⟨hys, hyb⟩ := hyO
    rw [mem_preimage, mem_ball_zero_iff] at hyb
    rcases eq_or_polar_of_small (hφ x) _ hys hyb with h | ⟨p, hp, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp.le, h⟩

end AtlasGlue

/-! ## 10. Two spheres joined at a node -/

section TwoSpheres

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

lemma holChartInl_comp : (holChartInl ∘ Sum.inl : S2 → ℂ) = holChart (-1) (by norm_num) :=
  funext fun _ => OpenPartialHomeomorph.lift_openEmbedding_apply _ _

lemma holChartInr_comp : (holChartInr ∘ Sum.inr : S2 → ℂ) = holChart (-1) (by norm_num) :=
  funext fun _ => OpenPartialHomeomorph.lift_openEmbedding_apply _ _

lemma nodeChart_target (x : S22) : (nodeChart x).target = univ := by
  rcases x with x | x <;> rfl

lemma contMDiffAt_nodeChart (x : S22) :
    ∀ y ∈ (nodeChart x).source, ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ (nodeChart x) y := by
  rcases x with x | x
  · rintro _ ⟨y, hy, rfl⟩
    change ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ (holChartInl : S22 → ℂ) (Sum.inl y)
    rw [contMDiffAt_inl_iff, holChartInl_comp]
    exact contMDiffAt_holChart (-1) (by norm_num) hy
  · rintro _ ⟨y, hy, rfl⟩
    change ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) ∞ (holChartInr : S22 → ℂ) (Sum.inr y)
    rw [contMDiffAt_inr_iff, holChartInr_comp]
    exact contMDiffAt_holChart (-1) (by norm_num) hy

lemma contMDiff_nodeChart_symm (x : S22) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ (nodeChart x).symm := by
  rcases x with x | x
  · change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ holChartInl.symm
    rw [holChartInl, OpenPartialHomeomorph.lift_openEmbedding_symm]
    exact (ContMDiff.inl (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2)).comp
      (contMDiff_holChart_symm (-1) (by norm_num))
  · change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ holChartInr.symm
    rw [holChartInr, OpenPartialHomeomorph.lift_openEmbedding_symm]
    exact (ContMDiff.inr (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2)).comp
      (contMDiff_holChart_symm (-1) (by norm_num))

lemma disjoint_holChartInl_Inr : Disjoint holChartInl.source holChartInr.source := by
  rw [holChartInl, holChartInr, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_source, Set.disjoint_left]
  rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
  exact Sum.inr_ne_inl h

/-- **The atlases with standard necks, injective node map and closed discs off the nodes satisfy
`GlueCharts`.** -/
theorem glueCharts_of_isStdNeck {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
    (hA : IsStdNeck A) (hinj : Injective A.node)
    (hav : ∀ i, ∀ p ∈ closedDisc, ∀ j, twoSpheres.discPt (A.center i) (A.ε i) p ≠ A.node j) :
    GlueCharts A where
  target j := by rw [hA j]; exact nodeChart_target _
  smooth j := by rw [hA j]; exact contMDiffAt_nodeChart _
  smooth_symm j := by rw [hA j]; exact contMDiff_nodeChart_symm _
  disjoint j j' h := by
    rw [hA j, hA j']
    have hne : A.node j ≠ A.node j' := hinj.ne h
    rcases A.node_cases j with h1 | h1 <;> rcases A.node_cases j' with h2 | h2 <;>
      rw [h1, h2] at hne ⊢
    · exact absurd rfl hne
    · exact disjoint_holChartInl_Inr
    · exact disjoint_holChartInl_Inr.symm
    · exact absurd rfl hne
  avoid := hav

/-- **Gluing data with necks exist on two spheres joined at a node** (`exists_glueDataN`): for
every `q` there is an atlas of the constant map `u ≡ q` with the standard neck charts `σ₋₁`
(`IsStdNeck`, hence `NeckSmooth`) carrying gluing data.  The atlas is chosen with one neck
chart at each nodal point and closed discs `r² ≤ 1/8` off the nodal points. -/
theorem exists_glueDataN (q : Q) :
    ∃ A : SectionAtlas (E := E) twoSpheres (fun _ => q),
      IsStdNeck A ∧ NeckSmooth A ∧ Nonempty (GlueDataN A) := by
  obtain ⟨A, hA, hinj, hav⟩ := exists_sectionAtlas_glue (E := E) twoSpheres (fun _ => q)
    continuous_const nodeChart isHolChart_nodeChart
  exact ⟨A, hA, neckSmooth_of_isStdNeck hA,
    nonempty_glueDataN (glueCharts_of_isStdNeck hA hinj hav) twoSpheres_chartsOnto⟩

/-- **The kernel of `D` at a constant map from two spheres joined at a node, unconditionally**
(Memoir Prop 4.23, p. 118, level `0`, `a = 0`): for every `q`, `J` and weights `δ`, there are an
atlas with the standard neck charts and gluing data on which `ker D ≅ E = T_qQ`, the constant
sections, and `dim ker D = dim E`. -/
theorem exists_linCRN_ker_equiv (J : AlmostComplexStructure E Q) (q : Q) (δ : ℕ → ℝ)
    (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) :
    ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
      (G : GlueDataN A), IsStdNeck A ∧
        Nonempty (E ≃ₗ[ℝ] (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J).ker) ∧
        Module.finrank ℝ (linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J).ker =
          Module.finrank ℝ E := by
  obtain ⟨A, hA, hsm, ⟨G⟩⟩ := exists_glueDataN (E := E) q
  exact ⟨A, hsm, G, hA, ⟨linCRN_ker_equiv J hsm G δ h0 hmono⟩,
    finrank_linCRN_ker J hsm G δ h0 hmono⟩

end TwoSpheres

end GWMemoir
