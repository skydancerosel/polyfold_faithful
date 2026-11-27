import GWMemoir.CokernelSphere
import GWMemoir.NodalPair
import GWMemoir.SectionAtlasNodes

/-!
# Functions of `e^{-2π(s+it)}` and the neck charts of `twoSpheres`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1, p. 66 (the neck
semi-norms), at the nodal points of `twoSpheres`.

* `ePol s₀ (s, t) = e^{-2π((s + s₀) + it)}` and the class `NeckCls r` of smooth `H : ℂ → ℝ` with
  `H(0) = 0`, vanishing for `|w| > r`.  It is closed under `w ↦ dH(w)(c w)`, which is how `∂_s`
  and `∂_t` act on `H ∘ ePol s₀` (`pD_comp_ePol`), and `|H(w)| ≤ M |w|`.  Hence
  **`memH_comp_ePol`**: for `δ < 2π`, `H ∘ ePol s₀` lies in every `H^{k,δ}(ℝ × S¹)`.
* `exists_sectionAtlas_of_charts`: an atlas of semi-norms with prescribed holomorphic charts at
  the nodal points; `IsStdNeck A`: the neck charts of `A` are `σ₋₁` on the sphere containing the
  nodal point (`holChartInl`, `holChartInr`); witness `exists_stdNeck_atlas`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Functions of `e^{-2π(s+it)}` -/

section Neck

/-- `ePol s₀ (s, t) = e^{-2π((s + s₀) + it)}`. -/
def ePol (s₀ : ℝ) (p : ℝ × ℝ) : ℂ := expPolar (p.1 + s₀, p.2)

/-- The derivative of the exponent, `(a, b) ↦ -2π (a + ib)`. -/
def ePolL : ℝ × ℝ →L[ℝ] ℂ :=
  ((-2 * Real.pi : ℝ) : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma hasFDerivAt_ePol (s₀ : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (ePol s₀) (ePol s₀ p • ePolL) p := by
  have a := ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasFDerivAt
    (x := p)).add_const (s₀ : ℂ)
  have b := ((Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).hasFDerivAt
    (x := p)).const_smul Complex.I
  have h := ((a.add b).const_smul (((-2 * Real.pi : ℝ) : ℂ))).cexp
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · ext <;> simp [ePol, expPolar, ePolL] <;> ring_nf
  · simp [ePol, expPolar]; ring_nf

lemma contDiff_ePol (s₀ : ℝ) : ContDiff ℝ ∞ (ePol s₀) :=
  Complex.contDiff_exp.comp (contDiff_const.mul
    ((Complex.ofRealCLM.contDiff.comp (contDiff_fst.add contDiff_const)).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)))

lemma fderiv_ePol_s (s₀ : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (ePol s₀) p (1, 0) = -2 * Real.pi * ePol s₀ p := by
  rw [(hasFDerivAt_ePol s₀ p).fderiv]; simp [ePolL]; ring

lemma fderiv_ePol_t (s₀ : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (ePol s₀) p (0, 1) = -2 * Real.pi * Complex.I * ePol s₀ p := by
  rw [(hasFDerivAt_ePol s₀ p).fderiv]; simp [ePolL]; ring

lemma norm_ePol (s₀ : ℝ) (p : ℝ × ℝ) : ‖ePol s₀ p‖ = Real.exp (-2 * Real.pi * (p.1 + s₀)) :=
  norm_expPolar _

lemma ePol_add_one (s₀ s t : ℝ) : ePol s₀ (s, t + 1) = ePol s₀ (s, t) :=
  expPolar_add_one _ _

/-- The neck class: `H` smooth, `H(0) = 0`, and `H(w) = 0` for `|w| > r`. -/
structure NeckCls (r : ℝ) (H : ℂ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ H
  zero : H 0 = 0
  vanish : ∀ w : ℂ, r < ‖w‖ → H w = 0

lemma NeckCls.hasCompactSupport {r : ℝ} {H : ℂ → ℝ} (h : NeckCls r H) : HasCompactSupport H := by
  refine (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset (isClosed_tsupport H) ?_
  refine closure_minimal (fun w hw => ?_) Metric.isClosed_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hc
  exact hw (h.vanish w (not_le.1 hc))

/-- `|H(w)| ≤ M |w|`. -/
lemma NeckCls.bound {r : ℝ} {H : ℂ → ℝ} (h : NeckCls r H) : ∃ M, ∀ w, |H w| ≤ M * ‖w‖ := by
  obtain ⟨M, hM⟩ := (h.smooth.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (h.hasCompactSupport.fderiv ℝ)
  refine ⟨M, fun w => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (x := 0) (y := w)
    (fun x _ => (h.smooth.differentiable (by simp)).differentiableAt) (fun x _ => hM x)
    convex_univ (mem_univ _) (mem_univ _)
  rw [h.zero, sub_zero, sub_zero, Real.norm_eq_abs] at this
  exact this

/-- `w ↦ dH(w)(c w)`. -/
def dirH (c : ℂ) (H : ℂ → ℝ) (w : ℂ) : ℝ := fderiv ℝ H w (c * w)

lemma NeckCls.dir {r : ℝ} {H : ℂ → ℝ} (h : NeckCls r H) (c : ℂ) : NeckCls r (dirH c H) where
  smooth := (h.smooth.fderiv_right (m := ∞) le_rfl).clm_apply (contDiff_const.mul contDiff_id)
  zero := by simp [dirH]
  vanish w hw := by
    have hev : H =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with x hx
      exact h.vanish x hx
    simp [dirH, hev.fderiv_eq]

lemma Ds_comp_ePol {H : ℂ → ℝ} (hH : Differentiable ℝ H) (s₀ : ℝ) :
    Ds (H ∘ ePol s₀) = dirH (-2 * Real.pi) H ∘ ePol s₀ := by
  funext p
  simp only [Ds, Function.comp_apply, dirH]
  rw [fderiv_comp p (hH _) (hasFDerivAt_ePol s₀ p).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_ePol_s]

lemma Dt_comp_ePol {H : ℂ → ℝ} (hH : Differentiable ℝ H) (s₀ : ℝ) :
    Dt (H ∘ ePol s₀) = dirH (-2 * Real.pi * Complex.I) H ∘ ePol s₀ := by
  funext p
  simp only [Dt, Function.comp_apply, dirH]
  rw [fderiv_comp p (hH _) (hasFDerivAt_ePol s₀ p).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_ePol_t]

/-- `∂_s^a ∂_t^b (H ∘ ePol s₀) = G ∘ ePol s₀` with `G` again in the neck class. -/
lemma pD_comp_ePol {r : ℝ} {H : ℂ → ℝ} (hH : NeckCls r H) (s₀ : ℝ) (a b : ℕ) :
    ∃ G, NeckCls r G ∧ pD a b (H ∘ ePol s₀) = G ∘ ePol s₀ := by
  have ht : ∀ b, ∃ G, NeckCls r G ∧ Dt^[b] (H ∘ ePol s₀) = G ∘ ePol s₀ := by
    intro b
    induction b with
    | zero => exact ⟨H, hH, rfl⟩
    | succ b ih =>
      obtain ⟨G, hG, e⟩ := ih
      refine ⟨_, hG.dir (-2 * Real.pi * Complex.I), ?_⟩
      rw [Function.iterate_succ_apply', e, Dt_comp_ePol (hG.smooth.differentiable (by simp))]
  obtain ⟨G₀, hG₀, e₀⟩ := ht b
  induction a with
  | zero => exact ⟨G₀, hG₀, e₀⟩
  | succ a ih =>
    obtain ⟨G, hG, e⟩ := ih
    refine ⟨_, hG.dir (-2 * Real.pi), ?_⟩
    rw [pD, Function.iterate_succ_apply', ← pD, e,
      Ds_comp_ePol (hG.smooth.differentiable (by simp))]

/-- `e^{-b s}` on `s ≥ 0` (and `0` for `s < 0`) is in `L²(ℝ × S¹)` for `b > 0`. -/
lemma memLp_expDecay {b : ℝ} (hb : 0 < b) :
    MemLp (fun x : ℝ × ℝ => (Ici (0 : ℝ)).indicator (fun s => Real.exp (-b * s)) x.1) 2 cyl := by
  have h1 : MemLp (fun s : ℝ => Real.exp (-b * s)) 2 (volume.restrict (Ici 0)) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    have : (fun s : ℝ => Real.exp (-b * s) ^ 2) = fun s => Real.exp (-(2 * b) * s) := by
      funext s; rw [← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi 0 (by linarith))
  exact ((memLp_indicator_iff_restrict measurableSet_Ici).2 h1).comp_fst _

/-- **The weighted bound**: for `G` in the neck class of radius `e^{-2πs₀}`,
`e^{δ|s|} |G(e^{-2π((s+s₀)+it))})| ≤ C e^{-(2π - δ)s}` on `s ≥ 0`, and the function vanishes
for `s < 0`. -/
lemma wt_mul_comp_ePol_le {s₀ : ℝ} {G : ℂ → ℝ} (hG : NeckCls (Real.exp (-2 * Real.pi * s₀)) G)
    (δ : ℝ) : ∃ C, ∀ x : ℝ × ℝ, |wt δ x * G (ePol s₀ x)| ≤
      C * (Ici (0 : ℝ)).indicator (fun s => Real.exp (-(2 * Real.pi - δ) * s)) x.1 := by
  obtain ⟨M, hM⟩ := hG.bound
  refine ⟨M * Real.exp (-2 * Real.pi * s₀), fun x => ?_⟩
  obtain ⟨s, t⟩ := x
  by_cases hs : 0 ≤ s
  · rw [indicator_of_mem (show s ∈ Ici 0 from hs), abs_mul, abs_of_pos (wt_pos _ _), wt,
      abs_of_nonneg hs]
    have h1 := hM (ePol s₀ (s, t))
    rw [norm_ePol] at h1
    calc Real.exp (δ * s) * |G (ePol s₀ (s, t))|
        ≤ Real.exp (δ * s) * (M * Real.exp (-2 * Real.pi * (s + s₀))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = M * Real.exp (-2 * Real.pi * s₀) * Real.exp (-(2 * Real.pi - δ) * s) := by
          rw [mul_left_comm, ← Real.exp_add, mul_assoc M (Real.exp _), ← Real.exp_add]
          congr 2; ring
  · have hv : G (ePol s₀ (s, t)) = 0 := hG.vanish _ (by
      rw [norm_ePol, Real.exp_lt_exp]; nlinarith [Real.pi_pos])
    rw [hv, mul_zero, abs_zero, indicator_of_notMem (show s ∉ Ici 0 from hs), mul_zero]

/-- **`H ∘ ePol s₀ ∈ H^{k,δ}(ℝ × S¹)` for `0 ≤ δ < 2π`**, for `H` in the neck class of radius
`e^{-2πs₀}` (the classical derivatives are the weak ones, and all are `O(e^{-2πs})`). -/
theorem memH_comp_ePol {s₀ : ℝ} {H : ℂ → ℝ} (hH : NeckCls (Real.exp (-2 * Real.pi * s₀)) H)
    (k : ℕ) {δ : ℝ} (hδ : δ < 2 * Real.pi) : MemH k δ (H ∘ ePol s₀) := by
  have hsp : SmPer (H ∘ ePol s₀) :=
    ⟨hH.smooth.comp (contDiff_ePol s₀), fun s t => by simp only [comp_apply, ePol_add_one]⟩
  intro a b _
  refine ⟨pD a b (H ∘ ePol s₀), hsp.hasWeakDeriv a b, ?_⟩
  obtain ⟨G, hG, e⟩ := pD_comp_ePol hH s₀ a b
  obtain ⟨C, hC⟩ := wt_mul_comp_ePol_le hG δ
  rw [e]
  refine ((memLp_expDecay (b := 2 * Real.pi - δ) (by linarith)).const_mul C).of_le
    (((continuous_wt δ).mul (hG.smooth.continuous.comp
      (contDiff_ePol s₀).continuous)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, comp_apply]
  refine (hC x).trans (le_abs_self _)

lemma memLp_comp_ePol {s₀ : ℝ} {H : ℂ → ℝ} (hH : NeckCls (Real.exp (-2 * Real.pi * s₀)) H) :
    MemLp (H ∘ ePol s₀) 2 cyl := by
  obtain ⟨C, hC⟩ := wt_mul_comp_ePol_le hH 0
  refine ((memLp_expDecay (b := 2 * Real.pi - 0) (by linarith [Real.pi_pos])).const_mul C).of_le
    ((hH.smooth.continuous.comp (contDiff_ePol s₀).continuous).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have := hC x
  simp only [wt, zero_mul, Real.exp_zero, one_mul] at this
  simp only [Real.norm_eq_abs, comp_apply]
  exact this.trans (le_abs_self _)

end Neck

/-! ## 2. Atlases with prescribed neck charts -/

section Atlas

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

open NodalSurface

variable {m : ℕ} (X : NodalSurface m)

/-- **Witness**: an atlas of semi-norms (Memoir p. 66) with prescribed holomorphic charts at the
nodal points, for every continuous `u` (the proof of `exists_sectionAtlas_of_hol`, with the
charts given). -/
theorem exists_sectionAtlas_of_charts (u : X.S → Q) (hu : Continuous u)
    (φ₀ : X.S → OpenPartialHomeomorph X.S ℂ) (hφ₀ : ∀ x ∈ X.nodalPts, X.IsHolChart (φ₀ x) x) :
    ∃ A : SectionAtlas (E := E) X u, ∀ j, A.hol j = φ₀ (A.node j) := by
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
  have hplace : ∀ z (p : ℝ × ℝ), 0 < ε z → p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
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
      ⟨(hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).1,
        (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.1⟩
    disc_avoid := fun i p hp q hq hmem =>
      (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.2 ⟨q, hq, hmem⟩
    nn := Fintype.card X.nodalPts
    node := fun j => (e.symm j).1
    hol := fun j => φ (e.symm j)
    s0 := fun j => s0 (e.symm j)
    isHol := fun j => hφ (e.symm j)
    neck_chart := fun j => hs0 (e.symm j)
    node_nodal := fun j => (e.symm j).2
    nodal_node := fun q hq x hx => ⟨e ⟨x, q, hq, hx⟩, by simp⟩
    cover := fun y => ?_ }, fun j => rfl⟩
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

end Atlas

/-! ## 3. The neck charts of `twoSpheres` -/

section StdNeck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- The chart `σ₋₁` (centred at `e₂`) on the sphere containing the point. -/
def nodeChart : S22 → OpenPartialHomeomorph S22 ℂ :=
  Sum.elim (fun _ => holChartInl) (fun _ => holChartInr)

theorem twoSpheres_nodal_cases {x : twoSpheres.S} (hx : x ∈ twoSpheres.nodalPts) :
    x = Sum.inl (pt 2) ∨ x = Sum.inr (pt 2) := by
  obtain ⟨p, hp, hxp⟩ := hx
  obtain rfl : p = s(Sum.inl (pt 2), Sum.inr (pt 2)) := hp
  exact Sym2.mem_iff.1 hxp

theorem isHolChart_nodeChart (x : twoSpheres.S) (hx : x ∈ twoSpheres.nodalPts) :
    twoSpheres.IsHolChart (nodeChart x) x := by
  rcases twoSpheres_nodal_cases hx with rfl | rfl
  exacts [isHolChart_inl, isHolChart_inr]

/-- The neck charts of `A` are `σ₋₁` on the sphere containing the nodal point. -/
def IsStdNeck {q : Q} (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) : Prop :=
  ∀ j, A.hol j = nodeChart (A.node j)

/-- **Witness**: the constant map from `twoSpheres` has an atlas with these neck charts. -/
theorem exists_stdNeck_atlas (q : Q) :
    ∃ A : SectionAtlas (E := E) twoSpheres (fun _ => q), IsStdNeck A :=
  exists_sectionAtlas_of_charts twoSpheres _ continuous_const nodeChart isHolChart_nodeChart

variable {q : Q} (A : SectionAtlas (E := E) twoSpheres (fun _ => q))

theorem SectionAtlas.node_cases (j : Fin A.nn) :
    A.node j = Sum.inl (pt 2) ∨ A.node j = Sum.inr (pt 2) := by
  obtain ⟨p, hp, hxp⟩ := A.node_nodal j
  exact twoSpheres_nodal_cases ⟨p, hp, hxp⟩

/-- The nodal point `inl e₂` has a neck chart. -/
theorem SectionAtlas.exists_node_inl : ∃ j, A.node j = Sum.inl (pt 2) :=
  A.nodal_node _ rfl _ (Sym2.mem_mk_left _ _)

lemma polar_nodeChart_inl (p : ℝ × ℝ) :
    twoSpheres.polar (nodeChart (Sum.inl (pt 2))) p =
      Sum.inl ((holChart (-1) (by norm_num)).symm (expPolar p)) := rfl

lemma polar_nodeChart_inr (p : ℝ × ℝ) :
    twoSpheres.polar (nodeChart (Sum.inr (pt 2))) p =
      Sum.inr ((holChart (-1) (by norm_num)).symm (expPolar p)) := rfl

end StdNeck

end GWMemoir
