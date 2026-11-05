import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_49

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_49
open Polyfold

/-- The project's statement: `lemma_3_55` (the model `ℝⁿ ⊕ W`), `lemma_3_55_core` (coordinates,
an arbitrary normed space; universe instantiated at `0`) and `fderivWithin_mem_of_mapsTo`
(universes `0, 0`). -/
def A : Prop :=
  type_of% @Polyfold.lemma_3_55 ∧ type_of% @Polyfold.lemma_3_55_core.{0} ∧
    type_of% @Polyfold.fderivWithin_mem_of_mapsTo.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.lemma_3_55, @Polyfold.lemma_3_55_core.{0}, @Polyfold.fderivWithin_mem_of_mapsTo.{0, 0}⟩

/-- `{n + (ι₁ ∘ L) n}` is the blind `N_v`. -/
lemma graphSpace_eq_Nv {E : ScBanach} (N : Submodule ℝ (E.lvl 0)) (L : N →L[ℝ] E.lvl 1) :
    graphSpace N ((E.toBase 1).comp L) = Nv N L := rfl

/-- A ⇒ B, through the coordinate conjunct `lemma_3_55_core` of `A` (with the coordinate
functionals `ℓ_i = (T ·)_i` of the presentation): `τ` is extended from the relatively open `V` to
the whole cone `N ∩ C` by a bump (`σ ∘ (b · id)`, the device of the project's
`lemma_3_55_relOpen`, re-done here from the hypothesis), and set to `0` off the cone so that it
takes values in `Y` everywhere. -/
theorem A_to_B : A → B := by
  rintro ⟨-, hcore, -⟩
  intro E W n T N Y _ V τ hNs hint hY hVrel h0V hτY hτ hτ0 hDτ
  classical
  obtain ⟨⟨-, hYsc, hsplit⟩, ε, hε, hgood⟩ := hY
  have hNY : IsCompl N Y := by simpa using hsplit 0
  have hYc : IsClosed (Y : Set (E.lvl 0)) := hYsc.1
  obtain ⟨O, hO, hVeq⟩ := hVrel
  set ℓ := coordCLMWith T with hℓdef
  set D : Set N := Subtype.val ⁻¹' quadOf T with hDdef
  have hD : quadCone (ℓlin ℓ) N = D := by ext v; exact Iff.rfl
  have hVD : V = D ∩ O := by rw [hVeq, inter_comm]
  have hVsub : V ⊆ D := by rw [hVeq]; exact inter_subset_right
  have h0O : (0 : N) ∈ O := (hVeq ▸ h0V : (0 : N) ∈ O ∩ _).1
  have hCconv : Convex ℝ (quadOf T) := by
    intro x hx y hy a b ha hb _ i
    show 0 ≤ ((T.lvl 0) (a • x + b • y)).1 i
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have hDconv : Convex ℝ D := hCconv.linear_preimage N.subtype
  have hint' : (interior (quadCone (ℓlin ℓ) N)).Nonempty := by rw [hD]; exact hint
  have hUD : UniqueDiffOn ℝ D := uniqueDiffOn_convex hDconv hint
  have hUV : UniqueDiffOn ℝ V := by rw [hVD]; exact hUD.inter hO
  -- `σ = ι₁ ∘ τ`, with values in `E₀`
  set σ : N → E.lvl 0 := fun v => E.toBase 1 (τ v) with hσdef
  have hσC : ContDiffOn ℝ 1 σ V := (E.toBase 1).contDiff.comp_contDiffOn hτ
  have hσ0 : σ 0 = 0 := by simp [hσdef, hτ0]
  have hDσ : fderivWithin ℝ σ V 0 = 0 := by
    have h1 := (E.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt (0 : N) hDτ
    rw [ContinuousLinearMap.comp_zero] at h1
    exact h1.fderivWithin (hUV 0 h0V)
  have hDσv : ∀ v ∈ V, fderivWithin ℝ σ V v = (E.toBase 1).comp (fderivWithin ℝ τ V v) := by
    intro v hv
    have h1 := ((hτ.differentiableOn one_ne_zero v hv).hasFDerivWithinAt)
    exact ((E.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt v h1).fderivWithin (hUV v hv)
  -- the bump `Φ(v) = b(v) v` maps `D` into `V` and is the identity near `0`
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO 0 h0O
  let b : ContDiffBump (0 : N) := ⟨r / 2, r, by positivity, by linarith⟩
  let Φ : N → N := fun v => b v • v
  have hΦsm : ContDiff ℝ 1 Φ := b.contDiff.smul contDiff_id
  have hΦeq : ∀ v : N, ‖v‖ < r / 2 → Φ v = v := fun v hv => by
    have : b v = 1 := b.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le)
    show b v • v = v
    rw [this, one_smul]
  have hΦV : ∀ v ∈ D, Φ v ∈ V := by
    intro v hv
    rw [hVD]
    refine ⟨?_, ?_⟩
    · show ((b v • v : N) : E.lvl 0) ∈ quadOf T
      intro i
      have hvi : 0 ≤ ((T.lvl 0) (v : E.lvl 0)).1 i := hv i
      rw [Submodule.coe_smul, map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg b.nonneg hvi
    · apply hrO
      rw [Metric.mem_ball, dist_zero_right]
      by_cases hvr : ‖v‖ < r
      · calc ‖(b v • v : N)‖ = b v * ‖v‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
          _ ≤ 1 * ‖v‖ := by gcongr; exact b.le_one
          _ = ‖v‖ := one_mul _
          _ < r := hvr
      · have : b v = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact not_lt.1 hvr)
        show ‖b v • v‖ < r
        rw [this, zero_smul, norm_zero]; exact hr
  -- the extension `τe`: `σ ∘ Φ` on the cone, `0` off it
  set τe : N → E.lvl 0 := fun v => if v ∈ D then σ (Φ v) else 0 with hτedef
  have hτeY : ∀ v, τe v ∈ Y := fun v => by
    by_cases hv : v ∈ D
    · simp only [hτedef, if_pos hv]; exact hτY _ (hΦV v hv)
    · simp only [hτedef, if_neg hv]; exact Y.zero_mem
  have hτeσ : ∀ v ∈ D, ‖v‖ < r / 2 → τe v = σ v := fun v hv hvr => by
    simp only [hτedef, if_pos hv, hΦeq v hvr]
  have hfderiv : ∀ v ∈ V, ‖v‖ < r / 2 →
      fderivWithin ℝ τe (quadCone (ℓlin ℓ) N) v = fderivWithin ℝ σ V v := by
    intro v hv hvr
    have hev : τe =ᶠ[𝓝[D] v] σ := by
      have hball : Metric.ball (0 : N) (r / 2) ∈ 𝓝 v :=
        Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hvr)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with w hwD hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact hτeσ w hwD hw
    rw [hD, hev.fderivWithin_eq (hτeσ v (hVsub hv) hvr), hVD,
      fderivWithin_inter (hO.mem_nhds (hVD ▸ hv : v ∈ D ∩ O).2)]
  have hτe : ContDiffOn ℝ 1 τe (quadCone (ℓlin ℓ) N) := by
    rw [hD]
    exact (hσC.comp hΦsm.contDiffOn hΦV).congr fun v hv => by simp only [hτedef, if_pos hv]; rfl
  have hτe0 : τe 0 = 0 := by
    rw [hτeσ 0 (hVsub h0V) (by rw [norm_zero]; positivity), hσ0]
  have hDτe0 : fderivWithin ℝ τe (quadCone (ℓlin ℓ) N) 0 = 0 := by
    rw [hfderiv 0 h0V (by rw [norm_zero]; positivity), hDσ]
  have hℓs : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : E.lvl 0, ∀ i ∈ s, ℓ i v = k i :=
    fun s k => ⟨(T.lvl 0).symm (k, 0), fun i _ => by
      rw [hℓdef, coordCLMWith_apply]
      show ((T.lvl 0) ((T.lvl 0).symm (k, 0))).1 i = k i
      rw [ContinuousLinearEquiv.apply_symm_apply]⟩
  -- the coordinate conjunct of `A`
  obtain ⟨ρ₁, hρ₁, hmain⟩ := hcore ℓ N Y hNY hYc hε (fun x hx p hp hle => hgood x hx p hp hle)
    hℓs hint' τe hτeY hτe hτe0 hDτe0
  set ρ := min ρ₁ (r / 2) with hρdef
  refine ⟨(Metric.ball 0 ρ ∩ O) ∩ D, ⟨Metric.ball 0 ρ ∩ O, Metric.isOpen_ball.inter hO, rfl⟩,
    ⟨⟨by rw [Metric.mem_ball, dist_self]; positivity, h0O⟩, hVsub h0V⟩, ?_, ?_⟩
  · rintro v ⟨⟨-, hvO⟩, hvD⟩
    rw [hVeq]; exact ⟨hvO, hvD⟩
  rintro v ⟨⟨hvρ, hvO⟩, hvD⟩
  rw [Metric.mem_ball, dist_zero_right] at hvρ
  have hv : v ∈ V := by rw [hVeq]; exact ⟨hvO, hvD⟩
  have hvρ₁ : ‖v‖ < ρ₁ := hvρ.trans_le (min_le_left _ _)
  have hvr : ‖v‖ < r / 2 := hvρ.trans_le (min_le_right _ _)
  have hvD' : v ∈ quadCone (ℓlin ℓ) N := by rw [hD]; exact hvD
  obtain ⟨hmem, hcompl, γ, hγ, hgoodv⟩ := hmain v hvD' hvρ₁
  rw [hτeσ v hvD hvr] at hmem hgoodv
  rw [hfderiv v hv hvr, hDσv v hv, graphSpace_eq_Nv] at hcompl hgoodv
  refine ⟨⟨fun i => hmem i, ?_⟩, hcompl, γ, hγ, fun m hm y hy hle => hgoodv m hm y hy hle⟩
  -- `v` is smooth, so `v + τ(v)` lies on level `1`
  have hvs : (v : E.lvl 0) ∈ E.smooth := hNs v.2
  have hv1 : (v : E.lvl 0) ∈ LinearMap.range (E.toBase 1 : E.lvl 1 →ₗ[ℝ] E.lvl 0) :=
    (Submodule.mem_iInf _).1 hvs 1
  obtain ⟨v₁, hv₁⟩ := hv1
  exact ⟨v₁ + τ v, by rw [map_add]; exact congrArg (· + E.toBase 1 (τ v)) hv₁⟩

#rt_check RoundTrip.V3_49.A_to_B [Polyfold.lemma_3_55, Polyfold.lemma_3_55_core,
  Polyfold.fderivWithin_mem_of_mapsTo]
#rt_overlap RoundTrip.V3_49.A_to_B [Polyfold.lemma_3_55, Polyfold.lemma_3_55_core,
  Polyfold.fderivWithin_mem_of_mapsTo]

end RoundTrip.V3_49

end
