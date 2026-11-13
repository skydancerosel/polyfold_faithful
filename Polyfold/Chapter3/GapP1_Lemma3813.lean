import Polyfold.Chapter3.GoodPositionGraph

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.1: **Proposition
3.8.12** (preprint 3.69) and **Lemma 3.8.13** (preprint 3.70), p. 154, for an arbitrary partial
quadrant `C` of an sc-Banach space `E` (any presentation `T : E ≅ ℝⁿ ⊕ W`), not only the model
`C = [0, ∞)ⁿ ⊕ W`.

# The degeneracy index along a graph, in a general presentation

## The text, paraphrased

(Lemma 3.8.13) `N ⊆ E = ℝⁿ ⊕ W` finite-dimensional in good position to `C = [0, ∞)ⁿ ⊕ W` with good
complement `Y`, `τ : N ∩ C → Y₁` of class `C¹` with `τ(0) = 0`, `Dτ(0) = 0`.  Then
`d_{N ∩ C}(v) = d_C(v + τ(v))` for `v ∈ N ∩ C ∖ N ∩ W` close to `0`.

## What is formalized

The text states the lemma in the model; its uses (the proof of Theorem 3.5.11, the degeneracy index
of solution sets) are in charts whose partial quadrant has an arbitrary presentation.  Here `C` is
any partial quadrant of `E`, and "`v ∉ N ∩ W`" is read intrinsically: `W = C ∩ (−C)` is the
lineality space of `C` (in the model `{0} ⊕ W`), so for `v ∈ C` it says `−v ∉ C`.

* `Polyfold.mem_lineality_iff`: in a presentation, `v ∈ C ∩ (−C)` iff all coordinates of `Tv`
  vanish.
* `Polyfold.proposition_3_8_12_general`: **Proposition 3.8.12** for any partial quadrant:
  (1) `d_{N ∩ C}(x) = d_C(x)` if `−x ∉ C`; (2) `d_{N ∩ C}(x) + dim(N ∩ C ∩ (−C)) = dim N` otherwise.
* `Polyfold.lemma_3_8_13_general`: **Lemma 3.8.13** for any partial quadrant: near `0`,
  `v + τ(v) ∈ C`, and `d_{N ∩ C}(v) = d_C(v + τ(v))` if `−v ∉ C`.

Both are the model proofs (`proposition_3_8_12`, `lemma_3_8_13`) run with the coordinate
functionals `x ↦ (T x)_i` of a presentation in place of the model coordinates; the cores
(`exists_quadrantNormalForm`, `lemma_3_8_13_core`) are already stated for jointly onto functionals.
As in the model, `τ` is asked to take values in `Y` (the text's `Y₁`: the level plays no role in
the degeneracy index) and the good complement is the algebraic one (`IsGoodComplement`, implied by
the text's sc-complement, `IsScGoodComplement.toIsGoodComplement`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E : ScBanach} {n : ℕ} {W : ScBanach}

/-- The continuous coordinate functionals `x ↦ (T x)_i` of a presentation. -/
def coordCLMOf (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) (i : Fin n) :
    E 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T : E 0 →L[ℝ] _))

@[simp] lemma coordCLMOf_apply (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0)
    (i : Fin n) (x : E 0) : coordCLMOf T i x = (T x).1 i := rfl

lemma ℓlin_coordCLMOf (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) :
    ℓlin (coordCLMOf T) = coordFun T := rfl

/-- In a presentation `C = T⁻¹([0,∞)ⁿ ⊕ W)`, a point of `C` lies in the lineality space `C ∩ (−C)`
iff all its coordinates vanish. -/
theorem mem_lineality_iff (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {x : E 0}
    (hx : x ∈ T 0 ⁻¹' quadrant n W 0) :
    -x ∈ T 0 ⁻¹' quadrant n W 0 ↔ ∀ i, (T 0 x).1 i = 0 := by
  have hx' : ∀ i, 0 ≤ (T 0 x).1 i := hx
  change (∀ i, 0 ≤ (T 0 (-x)).1 i) ↔ _
  simp only [map_neg, Prod.fst_neg, Pi.neg_apply, neg_nonneg]
  exact ⟨fun h i => le_antisymm (h i) (hx' i), fun h i => (h i).le⟩

/-- For `x ∈ N ∩ C`: `x` lies in the null space of the coordinates iff `−x ∈ C`. -/
lemma mem_nullSpace_coordFun_iff (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    {N : Submodule ℝ (E 0)} {x : N} (hx : (x : E 0) ∈ T 0 ⁻¹' quadrant n W 0) :
    x ∈ nullSpace (coordFun (T 0)) N ↔ -(x : E 0) ∈ T 0 ⁻¹' quadrant n W 0 := by
  rw [mem_nullSpace, mem_lineality_iff T hx]
  rfl

/-- **Proposition 3.8.12 (preprint 3.69) for any partial quadrant** (2021 p. 152): for `N` in good
position to the partial quadrant `C ⊆ E` and `x ∈ N ∩ C`: (1) if `−x ∉ C` (`x` outside the
lineality space `W = C ∩ (−C)`), `d_{N ∩ C}(x) = d_C(x)`; (2) otherwise
`d_{N ∩ C}(x) = dim N − dim(N ∩ W)`, stated additively for any submodule `K` of `N` with carrier
`N ∩ W`. -/
theorem proposition_3_8_12_general {C : Set (E 0)} (hC : IsPartialQuadrant E C)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hN : IsInGoodPosition E C N) {x : N}
    (hx : (x : E 0) ∈ C) :
    (-(x : E 0) ∉ C → degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) x = degIndex E C x) ∧
    (-(x : E 0) ∈ C → ∀ K : Submodule ℝ N, (∀ y : N, y ∈ K ↔ (y : E 0) ∈ C ∧ -(y : E 0) ∈ C) →
      degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) x + finrank ℝ K = finrank ℝ N) := by
  classical
  obtain ⟨n, W, T, rfl⟩ := hC
  obtain ⟨k, N₀, e, h1, h2, h3, h4⟩ := hN.quadrantNormalForm T
  have hT := preimage_eq_of_normalForm T e h1
  have hdeg : degIndex (ScBanach.const N) (Subtype.val ⁻¹' (T 0 ⁻¹' quadrant n W 0)) x =
      (Finset.univ.filter fun j => (e x).1 j = 0).card := by
    rw [degIndex_eq (scIsoOfLinearEquiv e) hT hx]
    rfl
  have hdegC : degIndex E (T 0 ⁻¹' quadrant n W 0) (x : E 0) =
      (Finset.univ.filter fun i => coordFun (T 0) i (x : E 0) = 0).card := by
    rw [degIndex_eq T rfl hx]; rfl
  refine ⟨fun hx1 => ?_, fun hx1 K hK => ?_⟩
  · rw [hdeg, hdegC]
    exact h2 x hx fun hmem => hx1 ((mem_nullSpace_coordFun_iff T hx).1 hmem)
  · have hKeq : K = nullSpace (coordFun (T 0)) N := by
      ext y
      rw [hK y]
      constructor
      · rintro ⟨hy, hy'⟩; exact (mem_nullSpace_coordFun_iff T hy).2 hy'
      · intro hy
        have hy0 : ∀ i, coordFun (T 0) i (y : E 0) = 0 := (mem_nullSpace _ _).1 hy
        have hyC : (y : E 0) ∈ T 0 ⁻¹' quadrant n W 0 := fun i => (hy0 i).ge
        exact ⟨hyC, (mem_nullSpace_coordFun_iff T hyC).1 hy⟩
    have hmem : x ∈ nullSpace (coordFun (T 0)) N := (mem_nullSpace_coordFun_iff T hx).2 hx1
    rw [hdeg, (h3 x).2 hmem, hKeq, ← h4]
    congr 1
    simp

/-- **Lemma 3.8.13 (preprint 3.70) for any partial quadrant** (2021 p. 154): let `C` be a partial
quadrant of `E`, `N` finite-dimensional in good position to `C` with good complement `Y`, and
`τ : N → E` with values in `Y`, of class `C¹` on `N ∩ C`, `τ(0) = 0`, `Dτ(0) = 0`.  Then for
`v ∈ N ∩ C` close to `0`: `v + τ(v) ∈ C`, and `d_{N ∩ C}(v) = d_C(v + τ(v))` if `−v ∉ C` (the
text's `v ∉ N ∩ W`). -/
theorem lemma_3_8_13_general {C : Set (E 0)} (hC : IsPartialQuadrant E C)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hN : IsInGoodPosition E C N)
    {Y : Submodule ℝ (E 0)} (hY : IsGoodComplement E C N Y) (τ : N → E 0) (hτY : ∀ v, τ v ∈ Y)
    (hτ : ContDiffOn ℝ 1 τ (Subtype.val ⁻¹' C)) (hτ0 : τ 0 = 0)
    (hDτ0 : fderivWithin ℝ τ (Subtype.val ⁻¹' C) 0 = 0) :
    ∃ ρ > 0, ∀ v : N, (v : E 0) ∈ C → ‖v‖ < ρ →
      ((v : E 0) + τ v ∈ C) ∧
      (-(v : E 0) ∉ C →
        degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) v = degIndex E C ((v : E 0) + τ v)) := by
  classical
  have hC' := hC
  obtain ⟨n, W, T, rfl⟩ := hC
  obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
  have hDeq : quadCone (ℓlin (coordCLMOf (T 0))) N =
      (Subtype.val ⁻¹' (T 0 ⁻¹' quadrant n W 0) : Set N) := rfl
  have hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ),
      ∃ v : E 0, ∀ i ∈ s, coordCLMOf (T 0) i v = k i :=
    coordFun_surj (T 0)
  rw [← hDeq] at hτ hDτ0
  have hint : (interior (quadCone (ℓlin (coordCLMOf (T 0))) N)).Nonempty := by
    rw [hDeq]; exact hN.interior_nonempty
  obtain ⟨ρ, hρ, hmain⟩ := lemma_3_8_13_core (coordCLMOf (T 0)) N Y hY.isCompl hε hgood hℓ hint τ
    hτY hτ hτ0 hDτ0
  refine ⟨ρ, hρ, fun v hv hvρ => ?_⟩
  obtain ⟨hmem', hiff⟩ := hmain v hv hvρ
  have hmem : (v : E 0) + τ v ∈ T 0 ⁻¹' quadrant n W 0 := hmem'
  refine ⟨hmem, fun hv1 => ?_⟩
  have hvW : v ∉ nullSpace (ℓlin (coordCLMOf (T 0))) N := fun h =>
    hv1 ((mem_nullSpace_coordFun_iff T hv).1 h)
  rw [(proposition_3_8_12_general hC' hN hv).1 hv1, degIndex_eq T rfl hv, degIndex_eq T rfl hmem]
  change (Finset.univ.filter fun i => (T 0 (v : E 0)).1 i = 0).card =
    (Finset.univ.filter fun i => (T 0 ((v : E 0) + τ v)).1 i = 0).card
  congr 1
  exact Finset.filter_congr fun i _ => hiff hvW i

/-- A partial quadrant contains `0`. -/
lemma IsPartialQuadrant.zero_mem' {C : Set (E 0)} (hC : IsPartialQuadrant E C) : (0 : E 0) ∈ C := by
  obtain ⟨n, W, T, rfl⟩ := hC
  show ∀ i, 0 ≤ (T 0 0).1 i
  intro i; simp

/-- A partial quadrant is closed under `t • ·` for `0 ≤ t ≤ 1`. -/
lemma IsPartialQuadrant.smul_mem_of_le_one {C : Set (E 0)} (hC : IsPartialQuadrant E C) {x : E 0}
    (hx : x ∈ C) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t • x ∈ C := by
  have := hC.convex hx hC.zero_mem' h0 (sub_nonneg.2 h1) (by ring)
  simpa using this

/-- **Lemma 3.8.13 (preprint 3.70), local form, for any partial quadrant**: as
`lemma_3_8_13_general`, with `σ` of class `C¹` only on a relatively open neighbourhood `V` of `0`
in `N ∩ C` (the form in which the lemma is applied to graphs, e.g. in Theorems 3.2.3 and 3.5.11):
for `v ∈ V` close to `0`, `v + σ(v) ∈ C` and `d_{N ∩ C}(v) = d_C(v + σ(v))` if `−v ∉ C`.  The
proof extends `σ` to `N ∩ C` by a radial bump and applies `lemma_3_8_13_general`. -/
theorem lemma_3_8_13_local {C : Set (E 0)} (hC : IsPartialQuadrant E C)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hN : IsInGoodPosition E C N)
    {Y : Submodule ℝ (E 0)} (hY : IsGoodComplement E C N Y) {V : Set N}
    (hVrel : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' C) (h0V : (0 : N) ∈ V)
    (σ : N → E 0) (hσY : ∀ v, σ v ∈ Y) (hσ : ContDiffOn ℝ 1 σ V) (hσ0 : σ 0 = 0)
    (hDσ : fderivWithin ℝ σ V 0 = 0) :
    ∃ ρ > 0, ∀ v ∈ V, ‖v‖ < ρ →
      ((v : E 0) + σ v ∈ C) ∧
      (-(v : E 0) ∉ C →
        degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) v = degIndex E C ((v : E 0) + σ v)) := by
  obtain ⟨O, hO, hVeq⟩ := hVrel
  set D : Set N := Subtype.val ⁻¹' C with hDdef
  have hVD : V = D ∩ O := by rw [hVeq, inter_comm]
  have h0O : (0 : N) ∈ O := (hVeq ▸ h0V : (0 : N) ∈ O ∩ _).1
  -- the bump: `Φ(v) = b(v) v` maps `D` into `V` and is the identity on the ball of radius `r/2`
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
    · show ((b v • v : N) : E 0) ∈ C
      rw [Submodule.coe_smul]
      exact hC.smul_mem_of_le_one hv b.nonneg b.le_one
    · apply hrO
      rw [mem_ball_zero_iff]
      by_cases hvr : ‖v‖ < r
      · calc ‖(b v • v : N)‖ = b v * ‖v‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
          _ ≤ 1 * ‖v‖ := by gcongr; exact b.le_one
          _ = ‖v‖ := one_mul _
          _ < r := hvr
      · have : b v = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact not_lt.1 hvr)
        change ‖b v • v‖ < r
        rw [this, zero_smul, norm_zero]; exact hr
  set τ : N → E 0 := fun v => σ (Φ v) with hτdef
  have hτσ : ∀ v : N, ‖v‖ < r / 2 → τ v = σ v := fun v hv => by
    change σ (Φ v) = σ v; rw [hΦeq v hv]
  have hτev : τ =ᶠ[𝓝 (0 : N)] σ := by
    have : Metric.ball (0 : N) (r / 2) ∈ 𝓝 (0 : N) := Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [this] with w hw
    exact hτσ w (mem_ball_zero_iff.1 hw)
  have hτ : ContDiffOn ℝ 1 τ D := hσ.comp hΦsm.contDiffOn hΦV
  have hτ0 : τ 0 = 0 := by rw [hτσ 0 (by rw [norm_zero]; positivity), hσ0]
  have hDτ0 : fderivWithin ℝ τ D 0 = 0 := by
    rw [(hτev.filter_mono nhdsWithin_le_nhds).fderivWithin_eq
      (hτσ 0 (by rw [norm_zero]; positivity)),
      ← hDσ, hVD, fderivWithin_inter (hO.mem_nhds h0O)]
  obtain ⟨ρ₁, hρ₁, hmain⟩ := lemma_3_8_13_general hC hN hY τ (fun v => hσY _) hτ hτ0 hDτ0
  refine ⟨min ρ₁ (r / 2), lt_min hρ₁ (by positivity), fun v hv hvρ => ?_⟩
  have hvD : (v : E 0) ∈ C := by rw [hVD] at hv; exact hv.1
  have h := hmain v hvD (hvρ.trans_le (min_le_left _ _))
  rw [hτσ v (hvρ.trans_le (min_le_right _ _))] at h
  exact h

end Polyfold
