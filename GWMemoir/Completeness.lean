import GWMemoir.SectionSpaces

/-!
# Completeness of the section spaces (Memoir pp. 66–68)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1, pp. 66–68.

The memoir states that a suitable finite choice of the semi-norms of p. 66 defines complete norms
on `H^{3,δ₀}_c(S, u*TQ)`, and uses that the point evaluations at the stabilizing points are
continuous, so that `E_u` (p. 68) is a closed subspace.  In `GWMemoir.SectionSpaces` these are the
named propositions `SectionsClosed` (the representatives of the continuous sections form a closed
subset of the block space) and `ConstraintsClosed`.  Both are the memoir's statements, not
stronger ones: the norm of p. 66 is the norm of the block space restricted to the representatives,
so its completeness is the closedness of their set.

This file holds the analysis used for both: they are proved, for a continuous map `u` on a
surface without nodes and every atlas, in `GWMemoir.CompletenessForms`.

* **Sobolev embedding** (`exists_continuous_rep`): every `u ∈ H^{2,δ}(ℝ × S¹)` has a continuous
  representative with `|u| ≤ 3 ‖u‖_{2,δ}`.  For a test function `φ`, `φ²(x)` is bounded by the
  integral of `|∂_s(φ²)| + |∂_s ∂_t(φ²)|` (one integration in `s`, an average over the circle in
  `t`), and `2|ab| ≤ a² + b²` gives `φ² ≤ 8 ‖φ‖²`; the general case follows from the density of
  the test functions in `H^{2,δ}` (Example 1.1.3, 2021 p. 6; `dense_test`) and uniform limits.
  `abs_le_of_ae_eq`: the same bound for any representative continuous on an open subset of
  `ℝ × (0, 1)`.
* The disc charts: `discD` (`r² < 1/8`), `continuousOn_discRep` (the disc representatives of a
  continuous section along a continuous map are continuous on `discD`), `placeInv`,
  `continuousAt_coord_transfer` (reading a section in another chart of `Q`), `tendsto_of_crd`.

The limit of representatives and the propositions themselves are in
`GWMemoir.CompletenessForms` (`exists_limit_section`, `sectionsClosed_of_nodes_empty`,
`constraintsClosed_of_nodes_empty`).

At nodal points the neck blocks lie in `H^{3,δ₀}(ℝ × S¹)`, also covered by the embedding.  Not
done there: the continuity of the neck representatives (the atlas asks `σ(s, t) ∈ φ.source` for
`s ≥ s₀`, not `e^{-2π(s+it)} ∈ φ.target`, so `σ` need not be continuous on that range), and the
continuity of the limit at the nodal point itself.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. A Sobolev bound on the cylinder -/

section Embedding

/-- On a line: a `C¹` function vanishing for large `|s|` is bounded by `∫ |k'|`. -/
lemma abs_le_integral_abs_deriv {k k' : ℝ → ℝ} (hk : ∀ s, HasDerivAt k (k' s) s)
    (hc : Continuous k') {R : ℝ} (hR : ∀ s, R < |s| → k s = 0) (s : ℝ) :
    |k s| ≤ ∫ σ, |k' σ| := by
  have hk'0 : ∀ σ, R < |σ| → k' σ = 0 := by
    intro σ hσ
    have hopen : IsOpen {y : ℝ | R < |y|} := isOpen_lt continuous_const continuous_abs
    have : k =ᶠ[𝓝 σ] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hσ] with y hy using hR y hy
    exact (hk σ).unique ((hasDerivAt_const σ (0 : ℝ)).congr_of_eventuallyEq this)
  have hcs : HasCompactSupport k' :=
    HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun σ hσ => hk'0 σ (by
      simp only [mem_Icc, not_and_or, not_le] at hσ
      rw [lt_abs]; rcases hσ with h | h
      · right; linarith
      · left; exact h)
  have hint : Integrable (fun σ => |k' σ|) :=
    hc.abs.integrable_of_hasCompactSupport (hcs.comp_left (g := abs) abs_zero)
  set a := -|R| - |s| - 1 with ha_def
  have ha : k a = 0 := hR a (by
    rw [abs_of_neg (by linarith [abs_nonneg R, abs_nonneg s])]
    linarith [le_abs_self R, abs_nonneg s])
  have has : a ≤ s := by linarith [neg_abs_le s, abs_nonneg R]
  have hFTC : k s - k a = ∫ σ in a..s, k' σ :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hk x)
      (hc.intervalIntegrable a s)).symm
  rw [ha, sub_zero] at hFTC
  rw [hFTC]
  calc |∫ σ in a..s, k' σ| ≤ ∫ σ in a..s, |k' σ| :=
        intervalIntegral.abs_integral_le_integral_abs has
    _ = ∫ σ in Ioc a s, |k' σ| := intervalIntegral.integral_of_le has
    _ ≤ ∫ σ, |k' σ| := setIntegral_le_integral hint (ae_of_all _ fun _ => abs_nonneg _)

/-- On a circle: a `1`-periodic `C¹` function is bounded by `∫₀¹ (|g| + |g'|)`. -/
lemma abs_le_integral_periodic {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hc : Continuous g') (hp : Function.Periodic g 1) (hp' : Function.Periodic g' 1) (t : ℝ) :
    |g t| ≤ ∫ τ in Ioc (0 : ℝ) 1, (|g τ| + |g' τ|) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  set I := ∫ σ in (t - 1)..t, |g' σ|
  have key : ∀ τ ∈ Icc (t - 1) t, |g t| ≤ |g τ| + I := by
    intro τ hτ
    have h1 : g t - g τ = ∫ σ in τ..t, g' σ :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
        (hc.intervalIntegrable τ t)).symm
    have h2 : |∫ σ in τ..t, g' σ| ≤ I :=
      calc _ ≤ ∫ σ in τ..t, |g' σ| := intervalIntegral.abs_integral_le_integral_abs hτ.2
        _ ≤ I := intervalIntegral.integral_mono_interval hτ.1 hτ.2 le_rfl
            (ae_of_all _ fun _ => abs_nonneg _) (hc.abs.intervalIntegrable _ _)
    calc |g t| = |g τ + (g t - g τ)| := by ring_nf
      _ ≤ |g τ| + |g t - g τ| := abs_add_le _ _
      _ ≤ _ := by rw [h1]; linarith
  have hI : ∫ τ in (t - 1)..t, |g t| ≤ ∫ τ in (t - 1)..t, (|g τ| + I) :=
    intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      ((hgc.abs.add continuous_const).intervalIntegrable _ _) key
  rw [intervalIntegral.integral_add (hgc.abs.intervalIntegrable _ _) intervalIntegrable_const]
    at hI
  simp only [intervalIntegral.integral_const, sub_sub_cancel, one_smul] at hI
  have hpa : Function.Periodic (fun τ => |g τ|) 1 := fun τ => by simp only [hp τ]
  have hpa' : Function.Periodic (fun τ => |g' τ|) 1 := fun τ => by simp only [hp' τ]
  have e1 : ∫ τ in (t - 1)..t, |g τ| = ∫ τ in (0 : ℝ)..1, |g τ| := by
    have := hpa.intervalIntegral_add_eq (t - 1) 0
    simpa using this
  have e2 : I = ∫ τ in (0 : ℝ)..1, |g' τ| := by
    have := hpa'.intervalIntegral_add_eq (t - 1) 0
    simpa using this
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_add (hgc.abs.intervalIntegrable _ _) (hc.abs.intervalIntegrable _ _)]
  linarith


lemma slice_hasCompactSupport {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (t : ℝ) :
    HasCompactSupport (fun s => φ (s, t)) := by
  obtain ⟨R, hR⟩ := h.bddSupp
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs => hR s t ?_
  simp only [mem_Icc, not_and_or, not_le] at hs
  rw [lt_abs]
  rcases hs with hs | hs
  · right; linarith
  · left; exact hs

lemma slice_integrable {φ : ℝ × ℝ → ℝ} (h : IsTest φ) (t : ℝ) :
    Integrable (fun s => |φ (s, t)|) :=
  (h.smooth.continuous.comp (by fun_prop : Continuous fun s : ℝ => (s, t))).abs
    |>.integrable_of_hasCompactSupport ((slice_hasCompactSupport h t).comp_left (g := abs) abs_zero)

/-- The slice bound: `|ψ(s,τ)| ≤ ∫ |∂_s ψ(σ,τ)| dσ` for a test function `ψ`. -/
lemma slice_abs_le {ψ : ℝ × ℝ → ℝ} (h : IsTest ψ) (s τ : ℝ) :
    |ψ (s, τ)| ≤ ∫ σ, |Ds ψ (σ, τ)| := by
  have hd : Differentiable ℝ ψ := h.smooth.differentiable (by simp)
  obtain ⟨R, hR⟩ := h.bddSupp
  exact abs_le_integral_abs_deriv (k := fun s => ψ (s, τ)) (fun s => hasDerivAt_s hd s τ)
    (h.ds.smooth.continuous.comp (by fun_prop)) (fun s hs => hR s τ hs) s

/-- The pointwise bound for a test function `F`: `|F(x)| ≤ ∫_cyl (|∂_s F| + |∂_s ∂_t F|)`. -/
lemma test_abs_le_integral {F : ℝ × ℝ → ℝ} (h : IsTest F) (x : ℝ × ℝ) :
    |F x| ≤ ∫ y, (|Ds F y| + |Ds (Dt F) y|) ∂cyl := by
  obtain ⟨s, t⟩ := x
  have hd : Differentiable ℝ F := h.smooth.differentiable (by simp)
  have h1 := abs_le_integral_periodic (g := fun τ => F (s, τ)) (g' := fun τ => Dt F (s, τ))
    (fun τ => hasDerivAt_t hd s τ) (h.dt.smooth.continuous.comp (by fun_prop))
    (fun τ => h.periodic s τ) (fun τ => h.dt.periodic s τ) t
  have hint : Integrable (fun y => |Ds F y| + |Ds (Dt F) y|) cyl :=
    (memLp_one_iff_integrable.1 (h.ds.memLp 1)).abs.add
      (memLp_one_iff_integrable.1 (h.dt.ds.memLp 1)).abs
  rw [cyl, integral_prod_symm _ hint]
  refine h1.trans (integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
    (hint.integral_prod_right) (ae_of_all _ fun τ => ?_))
  simp only
  rw [integral_add (slice_integrable h.ds τ) (slice_integrable h.dt.ds τ)]
  exact add_le_add (slice_abs_le h s τ) (slice_abs_le h.dt s τ)

variable {δ : ℝ} {hδ : 0 ≤ δ}

/-- `∫ (∂_s^a ∂_t^b φ)² ≤ ‖φ‖²_{H^{2,δ}}` for a test function and `a + b ≤ 2`. -/
lemma integral_sq_pD_le {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (a b : ℕ) (hab : a + b ≤ 2) :
    ∫ x, pD a b φ x ^ 2 ∂cyl ≤ ‖toH 2 hδ hφ‖ ^ 2 := by
  set u := toH 2 hδ hφ
  set p : idx 2 := ⟨(a, b), mem_idx.2 hab⟩
  have hg : HasWeakDeriv p.1.1 p.1.2 ((H.toSub u : Hsub 2 hδ) : Lp ℝ 2 cyl) (pD a b φ) :=
    (hφ.smPer.hasWeakDeriv a b).congr_ae (hφ.memLp 2).coeFn_toLp.symm (ae_eq_refl _)
  have hdv : dv (H.toSub u) p =ᵐ[cyl] pD a b φ :=
    dv_unique (H.toSub u) p hg ((hφ.pD a b).memLp 2)
  have h1 : ‖wdv (H.toSub u) p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have := norm_wdv_le u p
    gcongr
  have h2 : ‖wdv (H.toSub u) p‖ ^ 2 = ∫ x, (wt δ x * dv (H.toSub u) p x) ^ 2 ∂cyl := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_wdv (H.toSub u) p] with x hx
    rw [hx]
  refine le_trans ?_ (h2 ▸ h1)
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
    (dv_spec (H.toSub u) p).2.integrable_sq ?_
  filter_upwards [hdv] with x hx
  rw [← hx, mul_pow]
  have : 1 ≤ wt δ x ^ 2 := one_le_pow₀ (one_le_wt hδ x)
  nlinarith [sq_nonneg (dv (H.toSub u) p x)]

/-- **The Sobolev bound for test functions**: `|φ(x)| ≤ 3 ‖φ‖_{H^{2,δ}}`. -/
theorem test_abs_le_norm {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (x : ℝ × ℝ) :
    |φ x| ≤ 3 * ‖toH 2 hδ hφ‖ := by
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hdt : Differentiable ℝ (Dt φ) := hφ.dt.smooth.differentiable (by simp)
  set F : ℝ × ℝ → ℝ := fun y => φ y * φ y
  have hF : IsTest F := hφ.mul_smPer hφ.smPer
  have hDsF : ∀ y, Ds F y = 2 * (φ y * Ds φ y) := fun y => by
    rw [Ds_mul hd hd]; ring
  have hDtF : Dt F = fun y => (fun _ => (2 : ℝ)) y * (φ y * Dt φ y) := by
    funext y; rw [Dt_mul hd hd]; ring
  have hDsDtF : ∀ y, Ds (Dt F) y = 2 * (Ds φ y * Dt φ y + φ y * Ds (Dt φ) y) := fun y => by
    rw [hDtF, Ds_mul (F := fun _ => (2 : ℝ)) (G := fun y => φ y * Dt φ y)
      (differentiable_const _) (hd.mul hdt), Ds_mul hd hdt]
    simp [Ds]
  have hpt : ∀ y, |Ds F y| + |Ds (Dt F) y| ≤
      2 * (φ y ^ 2 + Ds φ y ^ 2 + Dt φ y ^ 2 + Ds (Dt φ) y ^ 2) := fun y => by
    rw [hDsF, hDsDtF]
    have e1 : |2 * (φ y * Ds φ y)| ≤ φ y ^ 2 + Ds φ y ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (φ y - Ds φ y), sq_nonneg (φ y + Ds φ y)]
    have e2 : |2 * (Ds φ y * Dt φ y + φ y * Ds (Dt φ) y)| ≤
        Ds φ y ^ 2 + Dt φ y ^ 2 + φ y ^ 2 + Ds (Dt φ) y ^ 2 := by
      rw [abs_le]; constructor <;>
        nlinarith [sq_nonneg (Ds φ y - Dt φ y), sq_nonneg (Ds φ y + Dt φ y),
          sq_nonneg (φ y - Ds (Dt φ) y), sq_nonneg (φ y + Ds (Dt φ) y)]
    nlinarith [sq_nonneg (Dt φ y), sq_nonneg (Ds (Dt φ) y)]
  have hsq : ∀ ψ : ℝ × ℝ → ℝ, IsTest ψ → Integrable (fun y => ψ y ^ 2) cyl :=
    fun ψ hψ => (hψ.memLp 2).integrable_sq
  have hmain : φ x ^ 2 ≤ 2 * (∫ y, φ y ^ 2 ∂cyl + ∫ y, Ds φ y ^ 2 ∂cyl + ∫ y, Dt φ y ^ 2 ∂cyl +
      ∫ y, Ds (Dt φ) y ^ 2 ∂cyl) := by
    have h1 := test_abs_le_integral hF x
    have hI : Integrable (fun y => φ y ^ 2 + Ds φ y ^ 2 + Dt φ y ^ 2 + Ds (Dt φ) y ^ 2) cyl :=
      (((hsq _ hφ).add (hsq _ hφ.ds)).add (hsq _ hφ.dt)).add (hsq _ hφ.dt.ds)
    have h2 : ∫ y, (|Ds F y| + |Ds (Dt F) y|) ∂cyl ≤
        ∫ y, 2 * (φ y ^ 2 + Ds φ y ^ 2 + Dt φ y ^ 2 + Ds (Dt φ) y ^ 2) ∂cyl :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity) (hI.const_mul 2)
        (ae_of_all _ hpt)
    have i2 : Integrable (fun y => φ y ^ 2 + Ds φ y ^ 2) cyl := (hsq _ hφ).add (hsq _ hφ.ds)
    have i3 : Integrable (fun y => φ y ^ 2 + Ds φ y ^ 2 + Dt φ y ^ 2) cyl := i2.add (hsq _ hφ.dt)
    rw [integral_const_mul, integral_add i3 (hsq _ hφ.dt.ds), integral_add i2 (hsq _ hφ.dt),
      integral_add (hsq _ hφ) (hsq _ hφ.ds)] at h2
    have h0 : φ x ^ 2 = |F x| := by
      simp only [F]; rw [abs_of_nonneg (mul_self_nonneg _)]; ring
    linarith
  have b00 := integral_sq_pD_le (hδ := hδ) hφ 0 0 (by norm_num)
  have b10 := integral_sq_pD_le (hδ := hδ) hφ 1 0 (by norm_num)
  have b01 := integral_sq_pD_le (hδ := hδ) hφ 0 1 (by norm_num)
  have b11 := integral_sq_pD_le (hδ := hδ) hφ 1 1 (by norm_num)
  simp only [pD, Function.iterate_zero, Function.iterate_one, id] at b00 b10 b01 b11
  have hN := norm_nonneg (toH 2 hδ hφ)
  nlinarith [abs_nonneg (φ x), sq_abs (φ x)]

lemma toH_sub {φ ψ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ) (m : ℕ) :
    toH m hδ (hφ.add (hψ.const_mul (-1))) = toH m hδ hφ - toH m hδ hψ := by
  apply Subtype.ext
  change ((hφ.add (hψ.const_mul (-1))).memLp 2).toLp _ =
    (hφ.memLp 2).toLp φ - (hψ.memLp 2).toLp ψ
  refine Lp.ext ?_
  filter_upwards [((hφ.add (hψ.const_mul (-1))).memLp 2).coeFn_toLp,
    Lp.coeFn_sub ((hφ.memLp 2).toLp φ) ((hψ.memLp 2).toLp ψ), (hφ.memLp 2).coeFn_toLp,
    (hψ.memLp 2).coeFn_toLp] with x h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4, Pi.add_apply]; ring

/-- If `f n → g` in `L²` and `f n = F n` a.e., with `F n → G` a.e., then `g = G` a.e. -/
lemma ae_eq_of_tendsto_Lp {f : ℕ → Lp ℝ 2 cyl} {g : Lp ℝ 2 cyl} (hf : Tendsto f atTop (𝓝 g))
    {F : ℕ → ℝ × ℝ → ℝ} {G : ℝ × ℝ → ℝ} (hF : ∀ n, (f n : ℝ × ℝ → ℝ) =ᵐ[cyl] F n)
    (hFG : ∀ᵐ x ∂cyl, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    (g : ℝ × ℝ → ℝ) =ᵐ[cyl] G := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂cyl, ∀ n, (f n : ℝ × ℝ → ℝ) x = F n x := ae_all_iff.2 hF
  filter_upwards [hae, hall, hFG] with x h1 h2 h3
  have h4 : Tendsto (fun i => F (ns i) x) atTop (𝓝 (G x)) := h3.comp hns.tendsto_atTop
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 h4

/-- **Sobolev embedding `H^{2,δ}(ℝ × S¹) ⊂ C⁰`**: every element has a continuous representative,
bounded by `3 ‖u‖`. -/
theorem exists_continuous_rep (u : H 2 hδ) : ∃ g : ℝ × ℝ → ℝ, Continuous g ∧
    (H.val u : ℝ × ℝ → ℝ) =ᵐ[cyl] g ∧ ∀ x, |g x| ≤ 3 * ‖u‖ := by
  have hdense := dense_test 2 hδ
  have hex : ∀ n : ℕ, ∃ φ, ∃ hφ : IsTest φ, dist (toH 2 hδ hφ) u < 1 / ((n : ℝ) + 1) :=
    fun n => by
      obtain ⟨w, hw, φ, hφ, rfl⟩ := Metric.dense_iff.1 hdense u (1 / ((n : ℝ) + 1))
        (by positivity)
      exact ⟨φ, hφ, by rw [Metric.mem_ball] at hw; exact hw⟩
  choose φ hφ hdist using hex
  have hdiff : ∀ n k x, |φ n x - φ k x| ≤ 3 * (1 / ((n : ℝ) + 1) + 1 / ((k : ℝ) + 1)) := by
    intro n k x
    have h1 := test_abs_le_norm (hδ := hδ) ((hφ n).add ((hφ k).const_mul (-1))) x
    rw [toH_sub (hφ n) (hφ k)] at h1
    have h3 : ‖toH 2 hδ (hφ n) - toH 2 hδ (hφ k)‖ ≤ 1 / ((n : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
      have := dist_triangle_right (toH 2 hδ (hφ n)) (toH 2 hδ (hφ k)) u
      rw [dist_eq_norm] at this; linarith [hdist n, hdist k]
    have e : (φ n + fun y => -1 * φ k y) x = φ n x - φ k x := by
      simp only [Pi.add_apply]; ring
    rw [e] at h1
    linarith
  have hcauchy : ∀ x, CauchySeq (fun n => φ n x) := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (6 / ε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hN' : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have h2 : 6 / ((N : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hN; nlinarith
    calc |φ n x - φ N x| ≤ 3 * (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) := hdiff n N x
      _ ≤ 6 / ((N : ℝ) + 1) := by rw [div_eq_mul_one_div 6]; nlinarith
      _ < ε := h2
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hunif : ∀ n x, |φ n x - g x| ≤ 3 * (1 / ((n : ℝ) + 1)) := by
    intro n x
    have h1 : Tendsto (fun k => |φ n x - φ k x|) atTop (𝓝 |φ n x - g x|) :=
      (tendsto_const_nhds.sub (hg x)).abs
    have h2 : Tendsto (fun k : ℕ => 3 * (1 / ((n : ℝ) + 1) + 1 / ((k : ℝ) + 1))) atTop
        (𝓝 (3 * (1 / ((n : ℝ) + 1) + 0))) :=
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).const_mul 3
    have := le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun k => hdiff n k x)
    simpa using this
  have hcont : Continuous g := by
    refine TendstoUniformly.continuous (p := atTop) (F := fun n x => φ n x) ?_
      (Frequently.of_forall fun n => (hφ n).smooth.continuous)
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    rw [dist_comm, Real.dist_eq]
    have h1 : (3 : ℝ) / ε < n + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h2 : 3 * (1 / ((n : ℝ) + 1)) < ε := by
      rw [div_lt_iff₀ hε] at h1
      rw [mul_one_div, div_lt_iff₀ (by positivity)]; linarith
    exact (hunif n x).trans_lt h2
  have hconv : Tendsto (fun n => toH 2 hδ (hφ n)) atTop (𝓝 u) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨g, hcont, ?_, fun x => ?_⟩
  · refine ae_eq_of_tendsto_Lp (f := fun n => valCLM 2 hδ (toH 2 hδ (hφ n)))
      (((valCLM 2 hδ).continuous.tendsto u).comp hconv) (F := φ)
      (fun n => ((hφ n).memLp 2).coeFn_toLp) (ae_of_all _ hg)
  · have h1 : Tendsto (fun n => |φ n x|) atTop (𝓝 |g x|) := (hg x).abs
    have h2 : Tendsto (fun n => 3 * ‖toH 2 hδ (hφ n)‖) atTop (𝓝 (3 * ‖u‖)) :=
      (hconv.norm).const_mul 3
    exact le_of_tendsto_of_tendsto h1 h2
      (Eventually.of_forall fun n => test_abs_le_norm (hφ n) x)

lemma cyl_eq_restrict : cyl = (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioc 0 1) := by
  rw [cyl, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- **The sup bound on an open set**: if `u ∈ H^{2,δ}` agrees a.e. with `h`, continuous on an open
set `U ⊆ ℝ × (0,1)`, then `|h| ≤ 3 ‖u‖` on `U`. -/
theorem abs_le_of_ae_eq (w : H 2 hδ) {h : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUs : U ⊆ univ ×ˢ Ioo 0 1) (hh : ContinuousOn h U)
    (hw : (H.val w : ℝ × ℝ → ℝ) =ᵐ[cyl] h) : ∀ x ∈ U, |h x| ≤ 3 * ‖w‖ := by
  obtain ⟨g, hg, hwg, hb⟩ := exists_continuous_rep w
  have hae : h =ᵐ[(volume : Measure (ℝ × ℝ)).restrict U] g := by
    have h1 : h =ᵐ[cyl] g := hw.symm.trans hwg
    rw [cyl_eq_restrict] at h1
    exact ae_restrict_of_ae_restrict_of_subset
      (hUs.trans (prod_mono le_rfl Ioo_subset_Ioc_self)) h1
  intro x hx
  rw [Measure.eqOn_open_of_ae_eq hae hU hh hg.continuousOn hx]
  exact hb x

/-- The bound for `H^{3,δ}`, through the inclusion into `H^{2,δ}`. -/
theorem abs_le_of_ae_eq_three (w : H 3 hδ) {h : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hUs : U ⊆ univ ×ˢ Ioo 0 1) (hh : ContinuousOn h U)
    (hw : (H.val w : ℝ × ℝ → ℝ) =ᵐ[cyl] h) : ∀ x ∈ U, |h x| ≤ 3 * ‖w‖ := fun x hx =>
  (abs_le_of_ae_eq (inclL hδ hδ (by norm_num : 2 ≤ 3) le_rfl w) hU hUs hh hw x hx).trans
    (by gcongr; exact norm_inclL_le hδ hδ _ le_rfl w)

lemma val_sub_ae {k : ℕ} (a b : H k hδ) :
    (H.val (a - b) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => H.val a x - H.val b x :=
  Lp.coeFn_sub (H.val a) (H.val b)

end Embedding

/-! ## 2. Sections without nodes: the limit of representatives -/

section Sections

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q}

/-- The open disc `r² < 1/8` of the disc charts. -/
def discD : Set (ℝ × ℝ) := {p | p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8}

lemma isOpen_discD : IsOpen discD := isOpen_lt (by fun_prop) continuous_const

lemma discD_sub : discD ⊆ univ ×ˢ Ioo 0 1 := by
  intro p hp
  simp only [discD, mem_ofPred_eq] at hp
  refine ⟨mem_univ _, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg (p.2 - 1 / 2)]

lemma discCut_pos {p : ℝ × ℝ} (hp : p ∈ discD) : 0 < discCut p :=
  Real.smoothTransition.pos_of_pos (by simp only [discD, mem_ofPred_eq] at hp; linarith)

lemma discCut_eq_one {p : ℝ × ℝ} (hp : p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 16) : discCut p = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma mem_discD_of_core {p : ℝ × ℝ} (hp : p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 1 / 16) : p ∈ discD := by
  simp only [discD, mem_ofPred_eq]; linarith

lemma discD_of_discCut_ne {p : ℝ × ℝ} (hp : discCut p ≠ 0) : p ∈ discD := by
  by_contra h
  simp only [discD, mem_ofPred_eq, not_lt] at h
  exact hp (Real.smoothTransition.zero_of_nonpos (by linarith))

lemma continuous_discCut : Continuous discCut := by
  unfold discCut; exact Real.smoothTransition.continuous.comp (by fun_prop)

lemma continuous_single2 (i : Fin 2) : Continuous fun a : ℝ => EuclideanSpace.single i a :=
  (Isometry.of_dist_eq fun a b => PiLp.dist_single_same 2 (fun _ : Fin 2 => ℝ) i a b).continuous

lemma continuous_place (c : X.S) (ε : ℝ) : Continuous (X.place c ε) := by
  unfold NodalSurface.place
  have h0 := continuous_single2 0
  have h1 := continuous_single2 1
  fun_prop

lemma continuousAt_discPt (A : SectionAtlas (E := E) X u) (i : Fin A.nd) {p : ℝ × ℝ}
    (hp : p ∈ discD) : ContinuousAt (X.discPt (A.center i) (A.ε i)) p :=
  (continuousAt_extChartAt_symm'' (A.disc_chart i p hp).1).comp
    (continuous_place (A.center i) (A.ε i)).continuousAt

/-- The inverse of the placement in the strip. -/
def placeInv (c : X.S) (ε : ℝ) (w : E2) : ℝ × ℝ :=
  ((ε⁻¹ • (w - extChartAt 𝓘(ℝ, E2) c c)) 0, (ε⁻¹ • (w - extChartAt 𝓘(ℝ, E2) c c)) 1 + 1 / 2)

lemma place_placeInv (c : X.S) {ε : ℝ} (hε : ε ≠ 0) (w : E2) :
    X.place c ε (placeInv c ε w) = w := by
  rw [NodalSurface.place, placeInv]
  simp only [add_sub_cancel_right]
  rw [single_add_single_eq, smul_smul, mul_inv_cancel₀ hε, one_smul, add_sub_cancel]

lemma placeInv_place (c : X.S) {ε : ℝ} (hε : ε ≠ 0) (p : ℝ × ℝ) :
    placeInv c ε (X.place c ε p) = p := by
  obtain ⟨a, b⟩ := p
  simp [NodalSurface.place, placeInv, smul_smul, inv_mul_cancel₀ hε]

lemma continuous_placeInv (c : X.S) (ε : ℝ) : Continuous (placeInv (X := X) c ε) := by
  unfold placeInv
  have hp : ∀ j : Fin 2, Continuous fun w : E2 => w j := fun j =>
    (EuclideanSpace.proj j).continuous
  have hs : Continuous fun w : E2 => ε⁻¹ • (w - extChartAt 𝓘(ℝ, E2) c c) :=
    (continuous_id.sub continuous_const).const_smul ε⁻¹
  exact ((hp 0).comp hs).prodMk (((hp 1).comp hs).add continuous_const)

/-- Changing the chart of `Q` in which a section is read preserves continuity. -/
lemma continuousAt_coord_transfer (hu : Continuous u) {η : X.S → E} {y0 : X.S} {a b : Q}
    (ha : u y0 ∈ (extChartAt 𝓘(ℝ, E) a).source) (hb : u y0 ∈ (extChartAt 𝓘(ℝ, E) b).source)
    (h : ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) a (u y) (η y)) y0) :
    ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) b (u y) (η y)) y0 := by
  have hO : IsOpen ((extChartAt 𝓘(ℝ, E) a).source ∩ (extChartAt 𝓘(ℝ, E) b).source) :=
    (isOpen_extChartAt_source a).inter (isOpen_extChartAt_source b)
  have hev : ∀ᶠ y in 𝓝 y0, u y ∈ (extChartAt 𝓘(ℝ, E) a).source ∩ (extChartAt 𝓘(ℝ, E) b).source :=
    hu.continuousAt.preimage_mem_nhds (hO.mem_nhds ⟨ha, hb⟩)
  have heq : (fun y => tangentCoordChange 𝓘(ℝ, E) a b (u y)
      (tangentCoordChange 𝓘(ℝ, E) (u y) a (u y) (η y))) =ᶠ[𝓝 y0]
      (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) b (u y) (η y)) := by
    filter_upwards [hev] with y hy
    exact tangentCoordChange_comp ⟨⟨mem_extChartAt_source _, hy.1⟩, hy.2⟩
  refine ContinuousAt.congr ?_ heq
  have hM : ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) a b (u y)) y0 :=
    ((continuousOn_tangentCoordChange (I := 𝓘(ℝ, E)) a b).continuousAt (hO.mem_nhds ⟨ha, hb⟩)).comp
      hu.continuousAt
  exact hM.clm_apply h

/-- The disc representatives of a continuous section are continuous on the disc. -/
lemma continuousOn_discRep (A : SectionAtlas (E := E) X u) (hu : Continuous u)
    {η : Section E X} (hη : IsContSection u η) (i : Fin A.nd) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (discRep A i k η) discD := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u (A.center i)) (u y) (η y))
      (X.discPt (A.center i) (A.ε i) p) :=
    continuousAt_coord_transfer hu (mem_extChartAt_source _) (A.disc_chart i p hp).2 (hη _)
  have h2 := h1.comp (continuousAt_discPt A i hp)
  exact continuous_discCut.continuousAt.mul
    ((crd k).continuous_of_finiteDimensional.continuousAt.comp h2)

/-- A sequence in `E` whose coordinates converge converges. -/
lemma tendsto_of_crd {a : ℕ → E} {c : Fin (Module.finrank ℝ E) → ℝ}
    (h : ∀ k, Tendsto (fun n => crd k (a n)) atTop (𝓝 (c k))) :
    Tendsto a atTop (𝓝 (∑ k, c k • Module.finBasis ℝ E k)) := by
  have e : a = fun n => ∑ k, crd k (a n) • Module.finBasis ℝ E k := by
    funext n
    conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr (a n)]
    rfl
  rw [e]
  exact tendsto_finsetSum _ fun k _ => (h k).smul_const _

/-- `Γ⁻¹ Γ = id` for the tangent coordinate change of `Q`. -/
lemma tcc_inv {y b : Q} (hy : y ∈ (extChartAt 𝓘(ℝ, E) b).source) (v : E) :
    tangentCoordChange 𝓘(ℝ, E) b y y (tangentCoordChange 𝓘(ℝ, E) y b y v) = v := by
  rw [tangentCoordChange_comp ⟨⟨mem_extChartAt_source _, hy⟩, mem_extChartAt_source _⟩,
    tangentCoordChange_self (mem_extChartAt_source _)]

end Sections



end GWMemoir
