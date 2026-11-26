import GWMemoir.Witnesses
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The three-pointed sphere is stable (Memoir Definition 1.3)

HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179), Definition 1.3, p. 3:
a noded Riemann surface is stable if its automorphism group is finite.  For the witness
`sphere3 = (S², j, (e₀, e₁, e₂), ∅)` of `GWMemoir.Witnesses` the automorphism group is trivial:

* in the stereographic chart `σ = σ₁` (`holChart 1`, centred at `-e₂`, with `e₂ ↦ ∞`), an
  automorphism `φ` reads `f = σ ∘ φ ∘ σ⁻¹ : ℂ → ℂ`; the condition `Tφ ∘ j = j ∘ Tφ` and the
  holomorphy of `σ` make `f` complex differentiable (`differentiable_chartMap`);
* `φ` is smooth at `e₂ = φ(e₂)`, so in the chart `σ₋₁ = 1/σ₁` at `e₂` it is Lipschitz at `0`:
  `|z| ≤ C |f(z)|` for large `|z|` (`exists_growth`), and the same for `φ⁻¹` gives
  `|f(z)| ≤ C' |z|`;
* by Liouville, `(f(z) - f(0))/z` is constant: `f` is affine, and it fixes `σ(e₀) ≠ σ(e₁)`, so
  `f = id` and `φ = id` (`eq_id_of_fix`).

`memoir_definition_1_3_sphere3 : sphere3.IsStable`.
-/

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Topology
open Set Function Metric Filter

noncomputable section

namespace GWMemoir

/-! ## 1. The stereographic charts as maps between manifolds -/

theorem contDiff_stereoCInv (s : ℝ) : ContDiff ℝ ∞ (stereoCInv s) := by
  have hn : ∀ z : ℂ, Complex.normSq z + 1 ≠ 0 := fun z =>
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos).ne'
  have hsq : ContDiff ℝ ∞ fun z : ℂ => Complex.normSq z := by
    have : (fun z : ℂ => Complex.normSq z) = fun z => z.re * z.re + z.im * z.im := by
      funext z; exact Complex.normSq_apply z
    rw [this]
    have hre : ContDiff ℝ ∞ fun z : ℂ => z.re := Complex.reCLM.contDiff
    have him : ContDiff ℝ ∞ fun z : ℂ => z.im := Complex.imCLM.contDiff
    exact (hre.mul hre).add (him.mul him)
  have hre : ContDiff ℝ ∞ fun z : ℂ => z.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ fun z : ℂ => z.im := Complex.imCLM.contDiff
  unfold stereoCInv
  refine ((hsq.add contDiff_const).inv hn).smul ?_
  have hv : (fun z : ℂ => WithLp.toLp 2 ![2 * z.re, -2 * s * z.im, s * (Complex.normSq z - 1)]) =
      fun z : ℂ => (2 * z.re) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (-2 * s * z.im) • EuclideanSpace.single 1 1 +
        (s * (Complex.normSq z - 1)) • EuclideanSpace.single 2 1 := by
    funext z
    ext i
    fin_cases i <;> simp
  rw [hv]
  exact (((contDiff_const.mul hre).smul contDiff_const).add
    ((contDiff_const.mul him).smul contDiff_const)).add
    ((contDiff_const.mul (hsq.sub contDiff_const)).smul contDiff_const)

/-- `σ_s⁻¹ : ℂ → S²` is smooth. -/
theorem contMDiff_holChart_symm (s : ℝ) (hs : s ^ 2 = 1) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) ∞ (holChart s hs).symm :=
  ContMDiff.codRestrict_sphere (n := 2) (contDiff_stereoCInv s).contMDiff
    (stereoCInv_mem s hs)

theorem mdifferentiable_holChart_symm (s : ℝ) (hs : s ^ 2 = 1) :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (holChart s hs).symm :=
  (contMDiff_holChart_symm s hs).mdifferentiable (by simp)

/-- The chart `σ = σ₁ = holChart 1` (centred at `-e₂`, missing `e₂`). -/
abbrev sig : OpenPartialHomeomorph S2 ℂ := holChart 1 (by norm_num)

theorem mem_sig_source_iff (y : S2) : y ∈ sig.source ↔ y ≠ pt 2 := by
  change 1 * (y : E3) 2 ≠ 1 ↔ _
  rw [one_mul]
  constructor
  · rintro h rfl; exact h (by simp [pt])
  · intro h h2
    apply h
    have hS := S2_sq y
    rw [h2] at hS
    have h0 : (y : E3) 0 = 0 := by nlinarith [sq_nonneg ((y : E3) 0), sq_nonneg ((y : E3) 1)]
    have h1 : (y : E3) 1 = 0 := by nlinarith [sq_nonneg ((y : E3) 0), sq_nonneg ((y : E3) 1)]
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [pt, h0, h1, h2]

theorem sig_symm_mem (z : ℂ) : sig.symm z ∈ sig.source := sig.map_target (mem_univ z)

theorem sig_sig_symm (z : ℂ) : sig (sig.symm z) = z := sig.right_inv (mem_univ z)

theorem stereoCInv_neg_inv (z : ℂ) (hz : z ≠ 0) : stereoCInv (-1) z⁻¹ = stereoCInv 1 z := by
  have hn : Complex.normSq z ≠ 0 := Complex.normSq_eq_zero.not.2 hz
  have hn1 : Complex.normSq z + 1 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos).ne'
  have hn2 : (Complex.normSq z)⁻¹ + 1 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (inv_nonneg.2 (Complex.normSq_nonneg z)) one_pos).ne'
  obtain ⟨a0, a1, a2⟩ := stereoCInv_apply (-1) z⁻¹
  obtain ⟨b0, b1, b2⟩ := stereoCInv_apply 1 z
  simp only [Complex.normSq_inv, Complex.inv_re, Complex.inv_im] at a0 a1 a2
  have hn1' : 1 + Complex.normSq z ≠ 0 := by rwa [add_comm]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [a0, b0]; field_simp; ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [a1, b1]; field_simp; ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [a2, b2]; field_simp; ring

theorem holChart_neg_symm_inv (z : ℂ) (hz : z ≠ 0) :
    (holChart (-1) (by norm_num)).symm z⁻¹ = sig.symm z :=
  Subtype.ext (stereoCInv_neg_inv z hz)

theorem holChart_neg_symm_zero : (holChart (-1) (by norm_num)).symm 0 = pt 2 := by
  apply Subtype.ext
  change stereoCInv (-1) 0 = EuclideanSpace.single 2 1
  obtain ⟨a0, a1, a2⟩ := stereoCInv_apply (-1) 0
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; rw [a0]; simp
  · simp only [Fin.mk_one, Fin.isValue]; rw [a1]; simp
  · simp only [Fin.reduceFinMk, Fin.isValue]; rw [a2]; simp

/-! ## 2. Growth at `e₂` -/

/-- For `y ∈ S² ∖ {e₂}` with `‖y - e₂‖ ≤ C/t` and `t ≥ C > 0`: `t ≤ C |σ(y)|`
(`|σ(y)|² = (1 + y₂)/(1 - y₂)` and `‖y - e₂‖² = 2(1 - y₂)`). -/
theorem le_mul_norm_sig (y : S2) (hy : y ≠ pt 2) {C t : ℝ} (hC : 0 < C) (ht : C ≤ t)
    (hyt : ‖(y : E3) - (pt 2 : E3)‖ ≤ C / t) : t ≤ C * ‖sig y‖ := by
  have hS := S2_sq y
  have hc1 : (y : E3) 2 ≠ 1 := by
    have h := (mem_sig_source_iff y).2 hy
    change 1 * (y : E3) 2 ≠ 1 at h
    rwa [one_mul] at h
  have ht0 : 0 < t := hC.trans_le ht
  have hc_le : (y : E3) 2 ≤ 1 := by nlinarith [sq_nonneg ((y : E3) 0), sq_nonneg ((y : E3) 1)]
  have hd : 0 < 1 - (y : E3) 2 := sub_pos.2 (lt_of_le_of_ne hc_le hc1)
  have hnorm : ‖(y : E3) - (pt 2 : E3)‖ ^ 2 = 2 * (1 - (y : E3) 2) := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [pt]
    linear_combination hS
  have hsig : ‖sig y‖ ^ 2 * (1 - (y : E3) 2) = 1 + (y : E3) 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change ((stereoC 1 y).re * (stereoC 1 y).re + (stereoC 1 y).im * (stereoC 1 y).im) *
      (1 - (y : E3) 2) = _
    rw [stereoC_re, stereoC_im]
    field_simp
    linear_combination hS
  set d := 1 - (y : E3) 2
  set N := ‖sig y‖ ^ 2
  have h1 : 2 * d * t ^ 2 ≤ C ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hyt 2
    rw [hnorm, div_pow, le_div_iff₀ (by positivity)] at this
    linarith
  have hCt : C ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hC.le ht 2
  have ht2 : 0 < t ^ 2 := by positivity
  have hd2 : d ≤ 1 / 2 := by nlinarith
  have h2 : t ^ 2 * d ≤ C ^ 2 * N * d := by
    have : C ^ 2 * N * d = C ^ 2 * (2 - d) := by rw [mul_assoc, hsig]; ring
    rw [this]; nlinarith
  have h3 : t ^ 2 ≤ (C * ‖sig y‖) ^ 2 := by
    rw [mul_pow]; exact le_of_mul_le_mul_right h2 hd
  exact (pow_le_pow_iff_left₀ ht0.le (by positivity) two_ne_zero).1 h3

/-- **Growth at `e₂`**: a map `ψ : S² → S²`, injective, differentiable at `e₂ = ψ(e₂)`, reads
in the chart `σ` with `|z| ≤ C |σ(ψ(σ⁻¹ z))|` for `|z| ≥ R` (Lipschitz at `0` in the chart
`σ₋₁ = 1/σ₁` centred at `e₂`). -/
theorem exists_growth (ψ : S2 → S2) (hψ : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ (pt 2))
    (h2 : ψ (pt 2) = pt 2) (hinj : Injective ψ) :
    ∃ C > 0, ∃ R > 0, ∀ z : ℂ, R ≤ ‖z‖ → ‖z‖ ≤ C * ‖sig (ψ (sig.symm z))‖ := by
  have hρ : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E3)
      (fun w => (ψ ((holChart (-1) (by norm_num)).symm w) : E3)) 0 := by
    have h1 := mdifferentiable_holChart_symm (-1) (by norm_num) 0
    have h2' : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ ((holChart (-1) (by norm_num)).symm 0) := by
      rw [holChart_neg_symm_zero]; exact hψ
    have h3 : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) (Subtype.val : S2 → E3)
        (ψ ((holChart (-1) (by norm_num)).symm 0)) :=
      (contMDiff_coe_sphere (m := ∞) (n := 2) _).mdifferentiableAt (by simp)
    exact h3.comp 0 (h2'.comp 0 h1)
  obtain ⟨C, hC, hO⟩ := (mdifferentiableAt_iff_differentiableAt.1 hρ).isBigO_sub.exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hO.bound
  have hRpos : 0 < max (2 / ε) C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hC, max (2 / ε) C, hRpos, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := norm_pos_iff.1 (hRpos.trans_le hz)
  have hw : dist z⁻¹ 0 < ε := by
    rw [dist_zero_right, norm_inv]
    have : 2 / ε ≤ ‖z‖ := (le_max_left _ _).trans hz
    calc ‖z‖⁻¹ ≤ (2 / ε)⁻¹ := inv_anti₀ (by positivity) this
      _ = ε / 2 := by rw [inv_div]
      _ < ε := half_lt_self hε
  have hb := hball hw
  simp only [sub_zero] at hb
  rw [holChart_neg_symm_inv z hz0, holChart_neg_symm_zero, h2, norm_inv] at hb
  refine le_mul_norm_sig _ ?_ hC ((le_max_right _ _).trans hz) (by rwa [div_eq_mul_inv])
  intro h
  rw [← h2] at h
  exact (mem_sig_source_iff _).1 (sig_symm_mem z) (hinj h)

/-! ## 3. The automorphism in the chart is holomorphic -/

/-- `ψ` read in the chart `σ`: `z ↦ σ(ψ(σ⁻¹ z))`. -/
def chartMap (ψ : S2 → S2) (z : ℂ) : ℂ := sig (ψ (sig.symm z))

theorem mem_source_of_injective {ψ : S2 → S2} (hinj : Injective ψ) (h2 : ψ (pt 2) = pt 2)
    {x : S2} (hx : x ∈ sig.source) : ψ x ∈ sig.source := by
  rw [mem_sig_source_iff] at hx ⊢
  intro h
  rw [← h2] at h
  exact hx (hinj h)

/-- `Dσ(y)` as a map `ℝ² → ℂ`. -/
def Dsig (y : S2) : E2 →L[ℝ] ℂ := mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) sig y

/-- `Dσ⁻¹(z)` as a map `ℂ → ℝ²`. -/
def Dtau (z : ℂ) : ℂ →L[ℝ] E2 := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) sig.symm z

theorem Dsig_Dtau (z v : ℂ) : Dsig (sig.symm z) (Dtau z v) = v := by
  have h : (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) sig (sig.symm z)).comp
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) sig.symm z) = ContinuousLinearMap.id ℝ ℂ := by
    have hσ := (holChart_holo 1 (by norm_num) _ (sig_symm_mem z)).1
    rw [← mfderiv_comp z hσ (mdifferentiable_holChart_symm 1 (by norm_num) z)]
    have : (sig ∘ sig.symm) = id := funext sig_sig_symm
    rw [this, mfderiv_id]
    rfl
  exact congrArg (fun L => L v) h

theorem injective_Dsig (z : ℂ) : Injective (Dsig (sig.symm z)) := by
  have hsurj : Surjective (Dsig (sig.symm z)) := fun v => ⟨Dtau z v, Dsig_Dtau z v⟩
  have hfin : Module.finrank ℝ E2 = Module.finrank ℝ ℂ := by
    simp [Complex.finrank_real_complex]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := ((Dsig (sig.symm z) : E2 →L[ℝ] ℂ) : E2 →ₗ[ℝ] ℂ))).2 hsurj

theorem Dsig_j (y : S2) (hy : y ∈ sig.source) (u : E2) :
    Dsig y (jStdMap y u) = Complex.I * Dsig y u :=
  (holChart_holo 1 (by norm_num) y hy).2 u

/-- `σ⁻¹` is holomorphic: `Dσ⁻¹(z)(i v) = j Dσ⁻¹(z) v`. -/
theorem Dtau_I (z v : ℂ) : Dtau z (Complex.I * v) = jStdMap (sig.symm z) (Dtau z v) := by
  apply injective_Dsig z
  rw [Dsig_Dtau, Dsig_j _ (sig_symm_mem z), Dsig_Dtau]

variable (ψ : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) S2 S2 ∞)

/-- **The chart map of a `j`-preserving diffeomorphism fixing `e₂` is entire.** -/
theorem differentiableAt_chartMap (h2 : ψ (pt 2) = pt 2)
    (hholo : ∀ x, (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x).comp (jStdMap x) =
      (jStdMap (ψ x)).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x)) (z : ℂ) :
    DifferentiableAt ℂ (chartMap ψ) z := by
  set x := sig.symm z
  have hψx : ψ x ∈ sig.source := mem_source_of_injective ψ.injective h2 (sig_symm_mem z)
  have hσ := (holChart_holo 1 (by norm_num) _ hψx).1
  have hψ' : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x := ψ.contMDiff.mdifferentiable (by simp) x
  have hτ := mdifferentiable_holChart_symm 1 (by norm_num) z
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartMap ψ) z := hσ.comp z (hψ'.comp z hτ)
  have hdiff : DifferentiableAt ℝ (chartMap ψ) z := mdifferentiableAt_iff_differentiableAt.1 hcomp
  set L := fderiv ℝ (chartMap ψ) z
  have hmf : ∀ v, L v = Dsig (ψ x) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x (Dtau z v)) := by
    intro v
    have h : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (chartMap ψ) z : ℂ →L[ℝ] ℂ) =
        (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) sig (ψ x)).comp ((mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x).comp
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) sig.symm z)) := by
      rw [show chartMap ψ = sig ∘ (ψ ∘ sig.symm) from rfl, mfderiv_comp z hσ (hψ'.comp z hτ),
        mfderiv_comp z hψ' hτ]
      rfl
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun T => T v) h
  have hCR : ∀ v, L (Complex.I * v) = Complex.I * L v := by
    intro v
    rw [hmf, hmf, Dtau_I]
    have h' : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x (jStdMap x (Dtau z v)) =
        jStdMap (ψ x) (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x (Dtau z v)) :=
      congrArg (fun T => T (Dtau z v)) (hholo x)
    rw [h']
    exact Dsig_j _ hψx _
  refine (hasFDerivAt_of_restrictScalars ℝ hdiff.hasFDerivAt
    (f' := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L 1)) ?_).differentiableAt
  refine ContinuousLinearMap.ext fun v => ?_
  change v • L 1 = L v
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hI := hCR 1
  rw [mul_one] at hI
  conv_rhs => rw [hv]
  rw [map_add, map_smul, map_smul, hI]
  simp only [smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im v]
  ring

/-! ## 4. Liouville: the chart map is affine, hence the identity -/

theorem chartMap_symm_chartMap (h2 : ψ (pt 2) = pt 2) (z : ℂ) :
    chartMap ψ.symm (chartMap ψ z) = z := by
  unfold chartMap
  rw [sig.left_inv (mem_source_of_injective (ψ := ⇑ψ) ψ.injective h2 (sig_symm_mem z)),
    ψ.symm_apply_apply, sig_sig_symm]

/-- `|σψσ⁻¹(z)| ≤ K |z|` for `|z| ≥ 1`: the growth of `ψ⁻¹` at `e₂`. -/
theorem exists_linear_bound (h2 : ψ (pt 2) = pt 2) :
    ∃ K, ∀ z : ℂ, 1 ≤ ‖z‖ → ‖chartMap ψ z‖ ≤ K * ‖z‖ := by
  have h2' : ψ.symm (pt 2) = pt 2 := by
    conv_lhs => rw [← h2]
    exact ψ.symm_apply_apply _
  obtain ⟨C, -, R, hR, hg⟩ := exists_growth ψ.symm
    (ψ.symm.contMDiff.mdifferentiable (by simp) _) h2' ψ.symm.injective
  refine ⟨max C R, fun z hz => ?_⟩
  by_cases h : R ≤ ‖chartMap ψ z‖
  · have := hg _ h
    rw [show sig (ψ.symm (sig.symm (chartMap ψ z))) = chartMap ψ.symm (chartMap ψ z) from rfl,
      chartMap_symm_chartMap ψ h2] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · push Not at h
    calc ‖chartMap ψ z‖ ≤ R := h.le
      _ ≤ R * ‖z‖ := le_mul_of_one_le_right hR.le hz
      _ ≤ max C R * ‖z‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

variable {ψ} in
/-- **The chart map is affine** (Liouville for `(f(z) − f(0))/z`). -/
theorem chartMap_affine (h2 : ψ (pt 2) = pt 2)
    (hholo : ∀ x, (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x).comp (jStdMap x) =
      (jStdMap (ψ x)).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x)) :
    ∃ a b : ℂ, ∀ z, chartMap ψ z = b + z * a := by
  have hf : Differentiable ℂ (chartMap ψ) := differentiableAt_chartMap ψ h2 hholo
  set g := dslope (chartMap ψ) 0
  have hg : Differentiable ℂ g :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope univ_mem).2 hf.differentiableOn)
  obtain ⟨K, hK⟩ := exists_linear_bound ψ h2
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hg.continuous.continuousOn
  have hb : Bornology.IsBounded (range g) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max M (K + ‖chartMap ψ 0‖), ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ 1
    · exact (hM z (by simpa using hz)).trans (le_max_left _ _)
    · push Not at hz
      have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
      rw [show g z = dslope (chartMap ψ) 0 z from rfl, dslope_of_ne _ hz0, slope_def_field,
        sub_zero, norm_div]
      have hzpos : 0 < ‖z‖ := by linarith
      have h1 := hK z hz.le
      have : ‖chartMap ψ z - chartMap ψ 0‖ / ‖z‖ ≤ K + ‖chartMap ψ 0‖ := by
        rw [div_le_iff₀ hzpos]
        have := norm_sub_le (chartMap ψ z) (chartMap ψ 0)
        nlinarith [norm_nonneg (chartMap ψ 0)]
      exact this.trans (le_max_right _ _)
  refine ⟨g 0, chartMap ψ 0, fun z => ?_⟩
  by_cases hz0 : z = 0
  · simp [hz0]
  · have := hg.apply_eq_apply_of_bounded hb z 0
    rw [show g z = dslope (chartMap ψ) 0 z from rfl, dslope_of_ne _ hz0, slope_def_field,
      sub_zero] at this
    rw [← this]
    field_simp
    ring

variable {ψ} in
/-- **A `j`-preserving diffeomorphism of `S²` fixing `e₀, e₁, e₂` is the identity.** -/
theorem eq_id_of_fix (hfix : ∀ i, ψ (pt i) = pt i)
    (hholo : ∀ x, (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x).comp (jStdMap x) =
      (jStdMap (ψ x)).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) ψ x)) (x : S2) : ψ x = x := by
  obtain ⟨a, b, hab⟩ := chartMap_affine (hfix 2) hholo
  have src : ∀ i : Fin 3, i ≠ 2 → pt i ∈ sig.source := fun i hi =>
    (mem_sig_source_iff _).2 fun h => hi (pt_injective h)
  have hpt : ∀ i : Fin 3, i ≠ 2 → chartMap ψ (sig (pt i)) = sig (pt i) := by
    intro i hi
    unfold chartMap
    rw [sig.left_inv (src i hi), hfix i]
  have hne : sig (pt 0) ≠ sig (pt 1) := fun h =>
    absurd (pt_injective (sig.injOn (src 0 (by decide)) (src 1 (by decide)) h)) (by decide)
  have e0 := (hab _).symm.trans (hpt 0 (by decide))
  have e1 := (hab _).symm.trans (hpt 1 (by decide))
  have ha : a = 1 := by
    have : (sig (pt 0) - sig (pt 1)) * a = (sig (pt 0) - sig (pt 1)) * 1 := by
      linear_combination e0 - e1
    exact mul_left_cancel₀ (sub_ne_zero.2 hne) this
  have hb : b = 0 := by subst ha; linear_combination e0
  by_cases hx : x = pt 2
  · rw [hx, hfix]
  · have hxs := (mem_sig_source_iff x).2 hx
    have h := hab (sig x)
    rw [ha, hb, zero_add, mul_one] at h
    unfold chartMap at h
    rw [sig.left_inv hxs] at h
    exact sig.injOn (mem_source_of_injective (ψ := ⇑ψ) ψ.injective (hfix 2) hxs) hxs h

/-! ## 5. Stability of `sphere3` -/

/-- Every automorphism of `sphere3` is the identity. -/
theorem sphere3_iso_apply (φ : sphere3.Iso sphere3) (x : sphere3.S) : φ.φ x = x :=
  eq_id_of_fix (ψ := φ.φ) (fun i => φ.marked i) φ.holo x

instance : Subsingleton (sphere3.Iso sphere3) :=
  ⟨fun a b => by
    have h : a.φ = b.φ :=
      Diffeomorph.ext fun x => (sphere3_iso_apply a x).trans (sphere3_iso_apply b x).symm
    cases a
    cases b
    subst h
    rfl⟩

/-- **Memoir Definition 1.3, p. 3, for the witness `sphere3`**: the sphere with three marked
points is stable; its automorphism group is trivial. -/
theorem memoir_definition_1_3_sphere3 : sphere3.IsStable := Finite.of_subsingleton

/-- The constant stable maps on `sphere3` have finitely many automorphisms (one). -/
theorem finite_iso_constStableMap {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q]
    [IsManifold 𝓘(ℝ, E) ∞ Q] (om : SymplecticForm E Q) (q : Q) (k : ℕ) (δ : ℝ) :
    Finite (StableMap.Iso (constStableMap om q k δ) (constStableMap om q k δ)) := by
  have : Subsingleton (StableMap.Iso (constStableMap om q k δ) (constStableMap om q k δ)) :=
    ⟨fun a b => by
      cases a with | mk φa _ => cases b with | mk φb _ =>
      have : φa = φb := Subsingleton.elim (α := sphere3.Iso sphere3) φa φb
      subst this
      rfl⟩
  exact Finite.of_subsingleton

end GWMemoir
