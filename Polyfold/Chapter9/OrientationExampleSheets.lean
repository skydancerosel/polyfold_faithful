import Polyfold.Chapter9.OrientationExampleSigns
import Polyfold.Chapter9.OrientationAnyDim
import Polyfold.Chapter9.OrientationRn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.3, **Example 9.3.5**, p. 425 (2017: Example 9.1, p. 313).

# Example 9.3.5: the sheets inside `supp(Θ)` and their oriented tangent spaces

`supp(Θ) = G⁺⁺ ∪ G⁻⁻` (`supp_example935Theta`).  For the classification of all orientations of
`Θ` (`Chapter9/OrientationExampleClasses.lean`) we need what every one-dimensional submanifold `M`
inside `supp(Θ)` looks like infinitesimally:

* `submanifoldTangent_eq_of_subset_Z`: at `z ∈ M ∩ G_b`, `T_zM = T_zG_b`.  Every curve in
  `supp(Θ)` through `z` has velocity in `ℝ (1, β_b'(z₀))`: off the origin it runs in `G_b`; at the
  origin the flatness of `β⁺⁺` forces a horizontal velocity (`hasDerivAt_snd_eq_of_mem_Z`).
* `orTan e z`: the two oriented tangent lines `± (1, β'(z₀))` at a point of `supp(Θ)`;
  `tangent_eq_orTan_or`: every orientation of `M` is one of them at every point;
  `exists_isOpen_tangent_eq_orTan_iff`: the sign is locally constant along `M`.
* `exists_mem_fst_eq`: `M` meets every vertical line `{s} × ℝ`, `|s|` small, if `0 ∈ M` (the
  graph representation `isGraphBallAt_rn` over `T_0M = ℝ × 0`).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

open MPolyfold EpGroupoid

namespace Ex935

/-! ### The support of `Θ` -/

/-- `supp(Θ) = G⁺⁺ ∪ G⁻⁻`. -/
def Z : Set (Fin 2 → ℝ) := graph2 (beta1 true) ∪ graph2 (beta1 false)

theorem mem_Z_iff {y : Fin 2 → ℝ} : y ∈ Z ↔ ∃ b, y ∈ graph2 (beta1 b) := by
  constructor
  · rintro (h | h)
    exacts [⟨true, h⟩, ⟨false, h⟩]
  · rintro ⟨b, h⟩
    cases b
    exacts [Or.inr h, Or.inl h]

theorem isClosed_Z : IsClosed Z :=
  (isClosed_graph2 (contDiff_beta1 true).continuous).union
    (isClosed_graph2 (contDiff_beta1 false).continuous)

open scoped Classical in
theorem example935Theta_apply (y : Fin 2 → ℝ) :
    example935Theta y = (if y ∈ graph2 (beta1 true) then 1 else 0) +
      (if y ∈ graph2 (beta1 false) then 1 else 0) := by
  rw [example935Theta, Finset.sum_filter, Fintype.sum_bool]

theorem supp_example935Theta : supp example935Theta = Z := by
  classical
  ext y
  change 0 < example935Theta y ↔ _
  rw [example935Theta_apply]
  by_cases h1 : y ∈ graph2 (beta1 true) <;> by_cases h2 : y ∈ graph2 (beta1 false) <;>
    simp [h1, h2, Z]

theorem beta1_true_apply (s : ℝ) : beta1 true s = betaPP s := rfl

theorem beta1_false_apply (s : ℝ) : beta1 false s = -betaPP s := rfl

/-- Off the vertical axis the two graphs `G⁺⁺`, `G⁻⁻` are disjoint. -/
theorem not_mem_graph2_not {b : Bool} {y : Fin 2 → ℝ} (hy : y ∈ graph2 (beta1 b))
    (h0 : y 0 ≠ 0) : y ∉ graph2 (beta1 (!b)) := by
  intro h
  have hp := betaPP_pos h0
  rw [mem_graph2_iff] at hy h
  cases b <;> simp only [Bool.not_true, Bool.not_false, beta1_true_apply,
    beta1_false_apply] at hy h <;> linarith

theorem eq_zero_of_mem_both {y : Fin 2 → ℝ} (h1 : y ∈ graph2 (beta1 true))
    (h2 : y ∈ graph2 (beta1 false)) : y = 0 := by
  have h0 : y 0 = 0 := by
    by_contra h0
    exact not_mem_graph2_not h1 h0 h2
  have h1' := h1
  rw [mem_graph2_iff, h0, beta1_true_apply, betaPP_zero] at h1'
  funext i
  fin_cases i
  · exact h0
  · exact h1'

theorem example935Theta_eq_one {y : Fin 2 → ℝ} (hy : y ∈ Z) (h0 : y 0 ≠ 0) :
    example935Theta y = 1 := by
  classical
  rw [example935Theta_apply]
  rcases mem_Z_iff.1 hy with ⟨b, hb⟩
  have hn := not_mem_graph2_not hb h0
  cases b
  · simp only [Bool.not_false] at hn
    simp [hn, hb]
  · simp only [Bool.not_true] at hn
    simp [hn, hb]

theorem example935Theta_zero : example935Theta 0 = 2 := by
  classical
  rw [example935Theta_apply, if_pos (zero_mem_graph2_beta1 true),
    if_pos (zero_mem_graph2_beta1 false)]
  norm_num

/-! ### The two oriented tangent lines at a point of `supp(Θ)` -/

/-- The orientation `ε (1, β_b')` of `G_b` (`b = true`: `G⁺⁺`, `b = false`: `G⁻⁻`). -/
def gOr (b e : Bool) : (rnPolyfold 2).SubmanifoldOrientation (graph2 (beta1 b)) 1 :=
  graphOrientation (contDiff_beta1 b) (boolSign e) (boolSign_ne_zero e)

/-- **The oriented tangent line `e · (1, β'(y₀))` at `y`**, read on `G⁺⁺` if `y₁ ≥ 0` and on `G⁻⁻`
otherwise (at the origin both give `e · (1, 0)`). -/
def orTan (e : Bool) (y : Fin 2 → ℝ) : (rnPolyfold 2).OrTangent :=
  (gOr (decide (0 ≤ y 1)) e).tangent y

theorem deriv_beta1_eq_of_mem {b b' : Bool} {y : Fin 2 → ℝ} (hb : y ∈ graph2 (beta1 b))
    (hb' : y ∈ graph2 (beta1 b')) : deriv (beta1 b) (y 0) = deriv (beta1 b') (y 0) := by
  by_cases h0 : y 0 = 0
  · rw [h0, deriv_beta1_zero, deriv_beta1_zero]
  · have : b' = b := by
      by_contra hne
      have : b' = !b := by cases b <;> cases b' <;> simp_all
      exact not_mem_graph2_not hb h0 (this ▸ hb')
    rw [this]

theorem gOr_tangent_eq {b b' : Bool} (e : Bool) {y : Fin 2 → ℝ} (hb : y ∈ graph2 (beta1 b))
    (hb' : y ∈ graph2 (beta1 b')) : (gOr b e).tangent y = (gOr b' e).tangent y :=
  graphOrientation_tangent_eq (contDiff_beta1 b) (contDiff_beta1 b') (boolSign_ne_zero e) hb hb'
    (deriv_beta1_eq_of_mem hb hb')

theorem mem_graph2_decide {b : Bool} {y : Fin 2 → ℝ} (hb : y ∈ graph2 (beta1 b)) :
    y ∈ graph2 (beta1 (decide (0 ≤ y 1))) := by
  have hnn : 0 ≤ betaPP (y 0) := add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)
  rw [mem_graph2_iff] at hb
  cases b
  · rw [beta1_false_apply] at hb
    by_cases h : 0 ≤ y 1
    · have h' : y 1 = 0 := by linarith
      have hp : betaPP (y 0) = 0 := by linarith
      simp only [h, decide_true]
      rw [mem_graph2_iff, beta1_true_apply, h', hp]
    · simp only [h, decide_false]
      rw [mem_graph2_iff, beta1_false_apply, hb]
  · rw [beta1_true_apply] at hb
    have h : 0 ≤ y 1 := by rw [hb]; exact hnn
    simp only [h, decide_true]
    rw [mem_graph2_iff, beta1_true_apply, hb]

/-- `T_y(G_b, e) = orTan e y` at every `y ∈ G_b`. -/
theorem gOr_tangent_eq_orTan {b : Bool} (e : Bool) {y : Fin 2 → ℝ} (hb : y ∈ graph2 (beta1 b)) :
    (gOr b e).tangent y = orTan e y :=
  gOr_tangent_eq e hb (mem_graph2_decide hb)

theorem orTan_ne {y : Fin 2 → ℝ} (hy : y ∈ Z) : orTan true y ≠ orTan false y := by
  obtain ⟨b, hb⟩ := mem_Z_iff.1 hy
  rw [← gOr_tangent_eq_orTan true hb, ← gOr_tangent_eq_orTan false hb]
  exact graphOrientation_tangent_ne' (contDiff_beta1 b) (b := true) (b' := false) (by decide) hb

/-- The graphs of the second structure: `G⁺⁻`, `G⁻⁺` agree near each of their points with a
graph of the first, with the same slope. -/
theorem exists_beta1_of_mem_beta2 {b : Bool} {y : Fin 2 → ℝ} (hy : y ∈ graph2 (beta2 b)) :
    ∃ b', y ∈ graph2 (beta1 b') ∧ deriv (beta2 b) (y 0) = deriv (beta1 b') (y 0) := by
  rcases lt_trichotomy (y 0) 0 with h | h | h
  · refine ⟨b, ?_, ?_⟩
    · cases b
      · change y 1 = betaMP (y 0) at hy
        change y 1 = betaMM (y 0)
        rwa [← betaMP_of_nonpos h.le]
      · change y 1 = betaPM (y 0) at hy
        change y 1 = betaPP (y 0)
        rwa [← betaPM_of_nonpos h.le]
    · cases b
      · exact deriv_eq_of_eqOn_Iio (fun t ht => betaMP_of_nonpos ht.le) h
      · exact deriv_eq_of_eqOn_Iio (fun t ht => betaPM_of_nonpos ht.le) h
  · refine ⟨true, ?_, ?_⟩
    · have : y 1 = 0 := by
        rw [mem_graph2_iff, h] at hy
        rw [hy]; cases b
        · change betaMP 0 = 0; simp [betaMP, betaPM]
        · change betaPM 0 = 0; simp [betaPM]
      rw [mem_graph2_iff, h, this, beta1_true_apply, betaPP_zero]
    · rw [h, deriv_beta2_zero, deriv_beta1_zero]
  · refine ⟨!b, ?_, ?_⟩
    · cases b
      · change y 1 = betaMP (y 0) at hy
        change y 1 = betaPP (y 0)
        rwa [← betaMP_of_pos h]
      · change y 1 = betaPM (y 0) at hy
        change y 1 = betaMM (y 0)
        rwa [← betaPM_of_pos h]
    · cases b
      · exact deriv_eq_of_eqOn_Ioi (fun t ht => betaMP_of_pos ht) h
      · exact deriv_eq_of_eqOn_Ioi (fun t ht => betaPM_of_pos ht) h

/-- `T_y(G⁺⁻ or G⁻⁺, e) = orTan e y` at every point `y` of the graph. -/
theorem orient2_tangent_eq_orTan (b e : Bool) {y : Fin 2 → ℝ} (hy : y ∈ graph2 (beta2 b)) :
    (graphOrientation (contDiff_beta2 b) (boolSign e) (boolSign_ne_zero e)).tangent y =
      orTan e y := by
  obtain ⟨b', hb', hd⟩ := exists_beta1_of_mem_beta2 hy
  rw [← gOr_tangent_eq_orTan e hb']
  exact graphOrientation_tangent_eq (contDiff_beta2 b) (contDiff_beta1 b') (boolSign_ne_zero e)
    hy hb' hd

theorem graph2_beta2_subset_Z (b : Bool) : graph2 (beta2 b) ⊆ Z := fun _ hy =>
  mem_Z_iff.2 ((exists_beta1_of_mem_beta2 hy).imp fun _ h => h.1)

/-! ### Curves in `supp(Θ)` -/

theorem betaPP_nonneg (s : ℝ) : 0 ≤ betaPP s :=
  add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem abs_snd_eq_of_mem_Z {y : Fin 2 → ℝ} (hy : y ∈ Z) : |y 1| = betaPP (y 0) := by
  rcases hy with h | h
  · rw [mem_graph2_iff, beta1_true_apply] at h
    rw [h, abs_of_nonneg (betaPP_nonneg _)]
  · rw [mem_graph2_iff, beta1_false_apply] at h
    rw [h, abs_neg, abs_of_nonneg (betaPP_nonneg _)]

theorem hasDerivAt_betaPP (s : ℝ) : HasDerivAt betaPP (deriv betaPP s) s :=
  ((contDiff_betaPP.differentiable (by simp)) s).hasDerivAt

theorem hasDerivAt_beta1 (b : Bool) (s : ℝ) : HasDerivAt (beta1 b) (deriv (beta1 b) s) s :=
  (((contDiff_beta1 b).differentiable (by simp)) s).hasDerivAt

/-- **Velocities of curves in `supp(Θ)`**: if `γ(0) = z ∈ G_b` and `γ(t) ∈ supp(Θ)` near `0`,
then `γ'(0)₁ = β_b'(z₀) γ'(0)₀`.  Off the origin `γ` runs in `G_b`; at the origin
`|γ₁| = β⁺⁺(γ₀) = o(t)` since `β⁺⁺` is flat. -/
theorem hasDerivAt_snd_eq_of_mem_Z {γ : ℝ → Fin 2 → ℝ} {v : Fin 2 → ℝ} (hγ : HasDerivAt γ v 0)
    {b : Bool} (hz : γ 0 ∈ graph2 (beta1 b)) (hZ : ∀ᶠ t in 𝓝 0, γ t ∈ Z) :
    v 1 = deriv (beta1 b) (γ 0 0) * v 0 := by
  have h0 := hasDerivAt_pi.1 hγ 0
  have h1 := hasDerivAt_pi.1 hγ 1
  by_cases hz0 : γ 0 0 = 0
  · -- at the origin
    have hz1 : γ 0 1 = 0 := by
      have := hz; rw [mem_graph2_iff, hz0] at this
      rw [this]; cases b
      · rw [beta1_false_apply, betaPP_zero, neg_zero]
      · rw [beta1_true_apply, betaPP_zero]
    rw [hz0, deriv_beta1_zero, zero_mul]
    have hg : HasDerivAt (fun t => betaPP (γ t 0)) (deriv betaPP (γ 0 0) * v 0) 0 :=
      (hasDerivAt_betaPP _).comp 0 h0
    rw [hz0, deriv_betaPP_zero, zero_mul] at hg
    have hg' := hasDerivAt_iff_isLittleO.1 hg
    have h1' : HasDerivAt (fun t => γ t 1) 0 0 := by
      refine hasDerivAt_iff_isLittleO.2 (Asymptotics.IsBigO.trans_isLittleO ?_ hg')
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [hZ] with t ht
      have := abs_snd_eq_of_mem_Z ht
      simp only [hz1, hz0, betaPP_zero, sub_zero, smul_zero, Real.norm_eq_abs, one_mul]
      rw [this, abs_of_nonneg (betaPP_nonneg _)]
    exact h1.unique h1'
  · -- off the origin `γ` stays in `G_b`
    have hnot := not_mem_graph2_not hz hz0
    have hcont : ContinuousAt γ 0 := hγ.continuousAt
    have hopen : IsOpen (graph2 (beta1 (!b)))ᶜ :=
      (isClosed_graph2 (contDiff_beta1 (!b)).continuous).isOpen_compl
    have hev : ∀ᶠ t in 𝓝 0, γ t ∈ (graph2 (beta1 (!b)))ᶜ :=
      hcont.preimage_mem_nhds (hopen.mem_nhds hnot)
    have hg : HasDerivAt (fun t => beta1 b (γ t 0)) (deriv (beta1 b) (γ 0 0) * v 0) 0 :=
      (hasDerivAt_beta1 b _).comp 0 h0
    have heq : (fun t => γ t 1) =ᶠ[𝓝 0] fun t => beta1 b (γ t 0) := by
      filter_upwards [hZ, hev] with t ht hn
      obtain ⟨b', hb'⟩ := mem_Z_iff.1 ht
      have : b' = b := by
        by_contra hne
        exact hn (by have : b' = !b := by cases b <;> cases b' <;> simp_all
                     exact this ▸ hb')
      exact this ▸ hb'
    exact h1.unique (hg.congr_of_eventuallyEq heq)

/-! ### Tangent spaces of one-dimensional submanifolds inside `supp(Θ)` -/

/-- The chart image of `T_zM` lies on the line `ℝ (1, β_b'(z₀))`. -/
theorem chartTangent_subset_of_subset_Z {M : Set (Fin 2 → ℝ)}
    (hM : (rnPolyfold 2).IsSmoothSubmanifold M) (hMZ : M ⊆ Z) {z : Fin 2 → ℝ} (hz : z ∈ M)
    {b : Bool} (hzb : z ∈ graph2 (beta1 b)) :
    (rnPolyfold 2).chartTangent (isChart_rnChart 0) M z ⊆
      (span ℝ {graphDirR (beta1 b) z} : Set (Fin 2 → ℝ)) := by
  obtain ⟨W, hWo, hzW, s, hsm, hmaps, hidem, himg, hT⟩ := MPolyfold.rn_exists_retraction hM hz
  have hsz : s z = z := by
    have : z ∈ s '' W := by rw [himg]; exact ⟨hzW, hz⟩
    obtain ⟨w, hw, hwz⟩ := this
    rw [← hwz, hidem w hw]
  rw [hT]
  rintro _ ⟨w, rfl⟩
  have hds : HasFDerivAt s (fderiv ℝ s z) z :=
    ((hsm.contDiffAt (hWo.mem_nhds hzW)).differentiableAt (by simp)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have hγ : HasDerivAt (fun t : ℝ => s (z + t • w)) (fderiv ℝ s z w) 0 :=
    hds.comp_hasDerivAt_of_eq (f := fun t : ℝ => z + t • w) 0 hline (by simp)
  have hZ : ∀ᶠ t in 𝓝 (0 : ℝ), s (z + t • w) ∈ Z := by
    have hc : ContinuousAt (fun t : ℝ => z + t • w) 0 := hline.continuousAt
    have : ∀ᶠ t in 𝓝 (0 : ℝ), z + t • w ∈ W :=
      hc.preimage_mem_nhds (hWo.mem_nhds (by simpa using hzW))
    filter_upwards [this] with t ht
    have : s (z + t • w) ∈ s '' W := ⟨_, ht, rfl⟩
    rw [himg] at this
    exact hMZ this.2
  have hv := hasDerivAt_snd_eq_of_mem_Z hγ (b := b) (by simpa [hsz] using hzb) hZ
  simp only [zero_smul, add_zero, hsz] at hv
  show (fderiv ℝ s z w : Fin 2 → ℝ) ∈
    ((span ℝ {graphDirR (beta1 b) z} : Submodule ℝ (Fin 2 → ℝ)) : Set (Fin 2 → ℝ))
  rw [SetLike.mem_coe, mem_span_singleton]
  refine ⟨fderiv ℝ s z w 0, funext fun i => ?_⟩
  fin_cases i
  · simp [graphDirR]
  · simp [graphDirR, hv, mul_comm]

/-- **`T_zM = T_zG_b`** for a one-dimensional submanifold `M ⊆ supp(Θ)` and `z ∈ M ∩ G_b`. -/
theorem submanifoldTangent_eq_of_subset_Z {M : Set (Fin 2 → ℝ)}
    (hM : (rnPolyfold 2).IsSubmanifoldOfDim M 1) (hMZ : M ⊆ Z) {z : Fin 2 → ℝ} (hz : z ∈ M)
    {b : Bool} (hzb : z ∈ graph2 (beta1 b)) :
    (rnPolyfold 2).submanifoldTangent M z =
      (rnPolyfold 2).submanifoldTangent (graph2 (beta1 b)) z := by
  obtain ⟨N, hN, hfin, hrank⟩ := exists_submodule_chartVec_image idChart2 hM.1 (hM.2 z hz)
    (mem_univ z)
  have hsub : N ≤ span ℝ {graphDir (beta1 b) z} := by
    intro v hv
    have : v ∈ chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent M z := by
      rw [← hN]; exact hv
    exact chartTangent_subset_of_subset_Z hM.1 hMZ hz hzb this
  have hne : graphDir (beta1 b) z ≠ 0 := graphDir_ne_zero (beta1 b) z
  have : FiniteDimensional ℝ (span ℝ {graphDir (beta1 b) z}) :=
    FiniteDimensional.span_of_finite ℝ (finite_singleton _)
  have hEq : N = span ℝ {graphDir (beta1 b) z} :=
    Submodule.eq_of_le_of_finrank_eq hsub (by rw [hrank, finrank_span_singleton hne])
  refine ((chartVec_injOn idChart2 (mem_univ z)).image_eq_image_iff (fun α hα => hα.1)
    (fun α hα => hα.1)).1 ?_
  rw [chartVec_image_graph2 (contDiff_beta1 b) hzb, ← hN, hEq]

/-- **Every orientation of a one-dimensional `M ⊆ supp(Θ)` is `± (1, β')` at every point.** -/
theorem tangent_eq_orTan_or {M : Set (Fin 2 → ℝ)} (hM : (rnPolyfold 2).IsSubmanifoldOfDim M 1)
    (hMZ : M ⊆ Z) {n : ℕ} (o : (rnPolyfold 2).SubmanifoldOrientation M n) (hn : n = 1)
    {z : Fin 2 → ℝ} (hz : z ∈ M) : o.tangent z = orTan true z ∨ o.tangent z = orTan false z := by
  subst hn
  obtain ⟨b, hb⟩ := mem_Z_iff.1 (hMZ hz)
  have hT := submanifoldTangent_eq_of_subset_Z hM hMZ hz hb
  obtain ⟨O₁, O₂, hne, hO⟩ := exists_two_orientations_submanifoldTangent
    (rnPolyfold_isSubmanifoldOfDim_graph2 (contDiff_beta1 b)) hb
  have ho : (rnPolyfold 2).IsOrientedAt z ⟨1, (rnPolyfold 2).submanifoldTangent
      (graph2 (beta1 b)) z, o.frames z⟩ := by
    have := o.isOrientedAt z hz; rwa [hT] at this
  have hfr : ∀ e : Bool, (rnPolyfold 2).IsOrientedAt z ⟨1, (rnPolyfold 2).submanifoldTangent
      (graph2 (beta1 b)) z, graphFrames (beta1 b) (boolSign e) z⟩ := fun e =>
    isOrientedAt_graphFrames (contDiff_beta1 b) (boolSign_ne_zero e) hb
  have hfne : graphFrames (beta1 b) (boolSign true) z ≠ graphFrames (beta1 b) (boolSign false) z :=
    by
    intro h
    apply graphOrientation_tangent_ne' (contDiff_beta1 b) (b := true) (b' := false) (by decide) hb
    rw [graphOrientation_tangent, graphOrientation_tangent, h]
  have key : o.frames z = graphFrames (beta1 b) (boolSign true) z ∨
      o.frames z = graphFrames (beta1 b) (boolSign false) z := by
    rcases (hO _).1 ho with h | h <;> rcases (hO _).1 (hfr true) with h1 | h1 <;>
      rcases (hO _).1 (hfr false) with h2 | h2
    all_goals first
      | exact absurd (h1.trans h2.symm) hfne
      | exact Or.inl (h.trans h1.symm)
      | exact Or.inr (h.trans h2.symm)
  have htan : ∀ e, o.frames z = graphFrames (beta1 b) (boolSign e) z → o.tangent z = orTan e z :=
    fun e he => by
    rw [← gOr_tangent_eq_orTan e hb]
    change (⟨1, (rnPolyfold 2).submanifoldTangent M z, o.frames z⟩ :
      (rnPolyfold 2).OrTangent) = ⟨1, (rnPolyfold 2).submanifoldTangent (graph2 (beta1 b)) z,
        graphFrames (beta1 b) (boolSign e) z⟩
    rw [hT, he]
  rcases key with h | h
  exacts [Or.inl (htan true h), Or.inr (htan false h)]

/-- **The sign of an orientation of `M ⊆ supp(Θ)` is locally constant along `M`.** -/
theorem exists_isOpen_tangent_eq_orTan_iff {M : Set (Fin 2 → ℝ)}
    (hM : (rnPolyfold 2).IsSubmanifoldOfDim M 1) (hMZ : M ⊆ Z) {n : ℕ}
    (o : (rnPolyfold 2).SubmanifoldOrientation M n) (hn : n = 1) {x : Fin 2 → ℝ} (hx : x ∈ M) :
    ∃ O : Set (Fin 2 → ℝ), IsOpen O ∧ x ∈ O ∧ ∀ z ∈ M ∩ O,
      (o.tangent z = orTan true z ↔ o.tangent x = orTan true x) := by
  subst hn
  have hb : ∀ b : Bool, ∃ O : Set (Fin 2 → ℝ), IsOpen O ∧ x ∈ O ∧ ∀ z ∈ M ∩ O,
      z ∈ graph2 (beta1 b) → (o.tangent z = orTan true z ↔ o.tangent x = orTan true x) := by
    intro b
    by_cases hxb : x ∈ graph2 (beta1 b)
    · obtain ⟨O, hO, hxO, hOz⟩ := SubmanifoldOrientation.exists_isOpen_tangent_eq_iff one_pos o
        (gOr b true) (hasContinuousLevelOneOn_rn _) hx hxb
        (submanifoldTangent_eq_of_subset_Z hM hMZ hx hxb)
      refine ⟨O, hO, hxO, fun z hz hzb => ?_⟩
      have h := hOz z ⟨⟨hz.1, hzb⟩, hz.2⟩ (submanifoldTangent_eq_of_subset_Z hM hMZ hz.1 hzb)
      rwa [gOr_tangent_eq_orTan true hzb, gOr_tangent_eq_orTan true hxb] at h
    · exact ⟨(graph2 (beta1 b))ᶜ, (isClosed_graph2 (contDiff_beta1 b).continuous).isOpen_compl,
        hxb, fun z hz hzb => (hz.2 hzb).elim⟩
  obtain ⟨O₁, hO₁, hx₁, h₁⟩ := hb true
  obtain ⟨O₂, hO₂, hx₂, h₂⟩ := hb false
  refine ⟨O₁ ∩ O₂, hO₁.inter hO₂, ⟨hx₁, hx₂⟩, fun z hz => ?_⟩
  obtain ⟨b, hzb⟩ := mem_Z_iff.1 (hMZ hz.1)
  cases b
  exacts [h₂ z ⟨hz.1, hz.2.2⟩ hzb, h₁ z ⟨hz.1, hz.2.1⟩ hzb]

/-- **A one-dimensional `M ⊆ supp(Θ)` through the origin meets every vertical line near `0`**:
the graph representation of `M` over `T_0M = ℝ × 0`. -/
theorem exists_mem_fst_eq {M : Set (Fin 2 → ℝ)} (hM : (rnPolyfold 2).IsSubmanifoldOfDim M 1)
    (hMZ : M ⊆ Z) (h0 : (0 : Fin 2 → ℝ) ∈ M) :
    ∃ r > 0, ∀ s : ℝ, |s| < r → ∃ a ∈ M, a 0 = s := by
  have hT := submanifoldTangent_eq_of_subset_Z hM hMZ h0 (zero_mem_graph2_beta1 true)
  have hct : ∀ v : Fin 2 → ℝ,
      v ∈ (rnPolyfold 2).chartTangent (isChart_rnChart 0) M 0 ↔ v 1 = 0 := by
    intro v
    have h := chartVec_image_graph2' (contDiff_beta1 true) (zero_mem_graph2_beta1 true)
    have h2 : (rnPolyfold 2).chartTangent (isChart_rnChart 0) M 0 =
        chartVec idChart2 '' (rnPolyfold 2).submanifoldTangent (graph2 (beta1 true)) 0 := by
      rw [← chartVec_image_eq_chartTangent, hT]
    refine (Set.ext_iff.1 (h2.trans h) v).trans ?_
    show v ∈ ((span ℝ {graphDirR (beta1 true) 0} : Submodule ℝ (Fin 2 → ℝ)) :
      Set (Fin 2 → ℝ)) ↔ _
    have hdir : graphDirR (beta1 true) 0 = ![1, 0] := by
      simp [graphDirR, deriv_beta1_zero]
    rw [hdir, SetLike.mem_coe, mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩; simp
    · intro hv
      refine ⟨v 0, funext fun i => ?_⟩
      fin_cases i
      · simp
      · simp [hv]
  let Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).smulRight ![1, 0]
  have hQ : ∀ v, Q v = v 0 • ![1, 0] := fun v => rfl
  have hQT : ∀ v, Q v ∈ (rnPolyfold 2).chartTangent (isChart_rnChart 0) M 0 := fun v =>
    (hct _).2 (by rw [hQ]; simp)
  have hQid : ∀ v ∈ (rnPolyfold 2).chartTangent (isChart_rnChart 0) M 0, Q v = v := by
    refine fun (v : Fin 2 → ℝ) hv => ?_
    have hv1 := (hct v).1 hv
    rw [hQ]
    funext i
    fin_cases i
    · simp
    · simp [hv1]
  obtain ⟨r, hr, hball⟩ := (isGraphBallAt_rn hM.1 h0).ball Q hQT hQid 1 one_pos
  refine ⟨r, hr, fun s hs => ?_⟩
  have hu : (![s, 0] : Fin 2 → ℝ) ∈ (rnPolyfold 2).chartTangent (isChart_rnChart 0) M 0 :=
    (hct _).2 (by simp)
  have hur : ‖(![s, 0] : Fin 2 → ℝ)‖ < r := by
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (abs_nonneg s)).2 fun i => ?_) hs
    fin_cases i <;> simp
  obtain ⟨a, ha, hQa, -⟩ := hball _ hu hur
  refine ⟨a, ha.1, ?_⟩
  have h1 : Q (a - 0) = (![s, 0] : Fin 2 → ℝ) := by
    have := hQa
    rwa [MPolyfold.rnChart_zero_apply', MPolyfold.rnChart_zero_apply'] at this
  have := congrFun h1 0
  rw [hQ] at this
  simpa using this

end Ex935

end Polyfold
