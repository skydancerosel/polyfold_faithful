import Polyfold.Chapter3.GlobalIFT
import Polyfold.Chapter3.SolutionLinearization
import Polyfold.Chapter3.GoodPositionOpen
import Polyfold.Chapter3.LocalSolvabilityClosed

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.54 (1)** ("at every point `y ∈ S` the sc-Fredholm germ `(f, y)` is in good position"),
in the chart at `x₀`: property (4) of the proof of Theorem 3.54, from Corollary 3.41 and
Lemma 3.55.

# Theorem 3.54: good position at the nearby zeros

## The text, paraphrased

(Proof of Theorem 3.54, (4)) "For every `y ∈ V` satisfying `f(y) = 0`, so that
`ψ ∘ ϕ(y) = v + σ(v)`, the kernel `ker f'(y)` is in good position to the partial cone
`C_yX ⊆ T_yX`, and `f'(y) : T_yX → Y_y` is surjective.  Property (4) follows from Corollary 3.41
and from Lemma 3.55."  (Lemma 3.55) For `v ∈ N ∩ C` near `0`, `v + τ(v) ∈ C`, and `Y` is a good
complement of `N_v = {n + Dτ(v)n | n ∈ N}` with respect to the partial quadrant `C_{v + τ(v)}`.

## What is formalized

* `Polyfold.lemma_3_55_relOpen`: **Lemma 3.55 for a relatively open domain `V ⊆ N ∩ C` and a
  general presentation `T` of `C`** (the form in which it is applied: `σ` is defined on the
  neighbourhood `V'` of Theorem 3.47, and `C' = C̃ ⊕ W` is presented by `T`); for `v ∈ V` close to
  `0` and `z = v + σ(v)`: `z ∈ C`, `Y` is a good complement of `N_v` with respect to `C_z`
  (`partialQuadrantAtWith T z`), and `N_v` is in good position to `C_z`.
* `Polyfold.StabilityData.exists_surjective_Dfs'_graph`: **Corollary 3.41 at the graph points**:
  `v + σ(v)` lies on level `1` and `D(h + s)(v + σ(v))` is a surjective Fredholm operator of index
  `n − N` for `v` close to `0`.
* `Polyfold.theorem_3_54_nearby_wholeChart`: **Theorem 3.54 (1) in the chart at `x₀`**: the data of
  `theorem_3_54_graph_wholeChart` together with a presentation `T` of `C'` and an open neighbourhood
  `Vx₁ ⊆ Vx` of `x₀` such that for every zero `y ∈ Vx₁` of `f`, with `z = ψ ∘ ϕ(y) = v + σ(v)`:
  `D(h + t)(z)` is a surjective Fredholm operator of index `n − N`, `z ∈ C'`, and the tangent
  space `N_v` of the graph at `z` is in good position to `C'_z` with the closed good complement
  `Y`.

## What the text leaves implicit, and the choices made (the findings)

* **Lemma 3.55 is stated for `τ` on all of `N ∩ C`**, but `σ` is given on the relatively open
  `V' ⊆ N ∩ C` only.  `σ` is extended to the cone by `σ ∘ Φ`, `Φ(v) = b(v) v` with a smooth bump
  `b` (`= 1` near `0`, `0` outside a ball inside `V'`); `Φ` maps the cone into `V'`, and the
  extension agrees with `σ` near `0`, so the derivatives at the points near `0` are those of `σ`
  within `V'` (`fderivWithin_inter`).
* **"`N_v` is in good position"** needs the interior of `N_v ∩ C_z` in `N_v` to be nonempty, which
  Lemma 3.55 does not state: `n ↦ n + Dσ(v)n` carries the interior of `N ∩ C` into `C ⊆ C_z` as
  soon as `‖Dσ(v)‖ ≤ ε` (the good-complement constant of `(N, Y)`), which holds for `v` near `0`
  by the continuity of `Dσ` and `Dσ(0) = 0`.
* **The closedness of `Y`** (added hypothesis of Lemma 3.55, Finding 49) is taken from
  `theorem_3_47_closed` (`LocalSolvabilityClosed.lean`).
* **Done in later files** (this file stops at the chart at `x₀`): (a) the identification
  `N_v = ker D(h + t)(z)` (the text passes from Lemma 3.55, which concerns `N_v`, to "`ker f'(y)`
  is in good position" without comment) is `StabilityData.graphSpace_eq_ker_Dfs'`
  (`GlobalIFTNearbyGraph.lean`, Finding 101), through the `C¹`-lift `σ₁ : V₁ → E'₁` of Theorem
  3.47 (1) since `h + t` is differentiable on level `1` only, and the dimension count
  `dim N_v = dim ker D(h + t)(0) = ind = dim ker D(h + t)(z)`; the kernel of `f'(y)` in the chart
  at `x₀` is `theorem_3_54_nearby_kernel_wholeChart` (`GlobalIFTNearbyKernel.lean`, `GlobalIFTNearbySurj.lean`,
  Findings 101–104), and its identification with the tangent space of the solution set is
  `theorem_3_54_ker_eq_tangent_wholeChart` (`GlobalIFTIndex.lean`).  (b) The passage from the chart at `x₀`
  to Definition 3.53 at `y` (`IsGoodPositionGermWholeChart f y`): the chart independence of the
  linearization `f'(y)` and of the good position of its kernel (the local form of Definition 2.38,
  gap G.13) is `LinearizationCharts.lean` (`linAt_chart_independence`,
  `isGoodPositionGerm_of_chart_dense`, Findings 110–117); the surjectivity of `f'(y)` is not a
  consequence of the surjectivity of `Dg(y)` for the filler `g` at `x₀` (condition (3) of
  Definition 3.4 is imposed at `0` only, Finding 100), and is proved with the text's hypotheses by
  an implicit function theorem at the nearby zero (`theorem_3_54_one'_wholeChart`,
  `GlobalIFTNearbyOnto*.lean`, Findings 180–189).  The assembled theorems are in
  `GlobalIFTTheorems.lean` and `GlobalIFTNearbyOnto.lean`.
-/

open Set Filter Topology Function Module Metric ContinuousLinearMap

noncomputable section

namespace Polyfold

/-! ### Lemma 3.55 for a relatively open domain and a general presentation -/

section Lemma355

variable {E : ScBanach} {n : ℕ} {W' : ScBanach}

/-- The coordinate functionals `x ↦ (Tx)_i` of a presentation `T`, as continuous linear maps. -/
def coordCLMWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W')) (i : Fin n) :
    E 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W' 0)).comp
    (T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W') 0))

@[simp] lemma coordCLMWith_apply (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W')) (i : Fin n)
    (x : E 0) : coordCLMWith T i x = (T 0 x).1 i := rfl

lemma mem_iff_coordCLMWith {C : Set (E 0)} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W'))
    (hT : C = T 0 ⁻¹' quadrant n W' 0) (x : E 0) : x ∈ C ↔ ∀ i, 0 ≤ coordCLMWith T i x := by
  rw [hT]; exact Iff.rfl

lemma mem_partialQuadrantAtWith_iff_coordCLMWith
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W')) (z h : E 0) :
    h ∈ partialQuadrantAtWith T z ↔ ∀ i, coordCLMWith T i z = 0 → 0 ≤ coordCLMWith T i h :=
  Iff.rfl

/-- `C ⊆ C_z` for every `z`. -/
lemma subset_partialQuadrantAtWith {C : Set (E 0)}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W')) (hT : C = T 0 ⁻¹' quadrant n W' 0)
    (z : E 0) : C ⊆ partialQuadrantAtWith T z := fun h hh i _ =>
  ((mem_iff_coordCLMWith T hT h).1 hh) i

/-- **Lemma 3.55 for a relatively open domain `V ⊆ N ∩ C` and a general presentation `T` of the
partial quadrant `C`**: `N` in good position to `C` with the closed good complement `Y`, and
`σ : V → Y` of class `C¹` on the relatively open neighbourhood `V` of `0` in `N ∩ C` with
`σ(0) = 0`, `Dσ(0) = 0`.  Then for `v ∈ V` close to `0`, with `z = v + σ(v)`:
(1) `z ∈ C`; (2), (3) `Y` is a good complement of `N_v = {n + Dσ(v)n | n ∈ N}` with respect to the
partial quadrant `C_z` (`partialQuadrantAtWith T z`), and `N_v` is in good position to `C_z`.
The text's `τ` is defined on all of `N ∩ C`; here `σ` is extended from `V` to the cone by a
smooth bump (`σ ∘ (b · id)`, equal to `σ` near `0`), so that `lemma_3_55_core` applies.  The
interior of `N_v ∩ C_z` is nonempty because `n ↦ n + Dσ(v)n` carries the interior of `N ∩ C`
into `C ⊆ C_z` once `‖Dσ(v)‖ ≤ ε` (the good-complement constant of `(N, Y)`). -/
theorem lemma_3_55_relOpen {C : Set (E 0)} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W'))
    (hT : C = T 0 ⁻¹' quadrant n W' 0) {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : IsInGoodPosition E C N) {Y : Submodule ℝ (E 0)} (hY : IsGoodComplement E C N Y)
    (hYc : IsClosed (Y : Set (E 0))) {V : Set N}
    (hVrel : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' C) (h0V : (0 : N) ∈ V)
    (σ : N → E 0) (hσY : ∀ v, σ v ∈ Y) (hσC : ContDiffOn ℝ 1 σ V) (hσ0 : σ 0 = 0)
    (hDσ : fderivWithin ℝ σ V 0 = 0) :
    ∃ ρ > 0, ∀ v ∈ V, ‖v‖ < ρ →
      ((v : E 0) + σ v ∈ C) ∧
      IsGoodComplement E (partialQuadrantAtWith T ((v : E 0) + σ v))
        (graphSpace N (fderivWithin ℝ σ V v)) Y ∧
      IsInGoodPosition E (partialQuadrantAtWith T ((v : E 0) + σ v))
        (graphSpace N (fderivWithin ℝ σ V v)) := by
  classical
  obtain ⟨O, hO, hVeq⟩ := hVrel
  set ℓ := coordCLMWith T with hℓdef
  set D : Set N := Subtype.val ⁻¹' C with hDdef
  have hmemC : ∀ x : E 0, x ∈ C ↔ ∀ i, 0 ≤ ℓ i x := mem_iff_coordCLMWith T hT
  have hD : quadCone (ℓlin ℓ) N = D := by
    ext v; exact (hmemC v).symm
  have hVD : V = D ∩ O := by rw [hVeq, inter_comm]
  have hVsub : V ⊆ D := by rw [hVeq]; exact inter_subset_right
  have h0O : (0 : N) ∈ O := (hVeq ▸ h0V : (0 : N) ∈ O ∩ _).1
  have h0D : (0 : N) ∈ D := hVsub h0V
  -- convexity of `D` and unique differentiability on `V`
  have hDconv : Convex ℝ D := by
    have hCconv : Convex ℝ C := by
      rw [hT]
      exact (quadrant_convex n W' 0).linear_preimage
        ((T 0 : E 0 →L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W') 0) : E 0 →ₗ[ℝ] _)
    exact hCconv.linear_preimage N.subtype
  have hint : (interior (quadCone (ℓlin ℓ) N)).Nonempty := by rw [hD]; exact hN.interior_nonempty
  have hintD : (interior D).Nonempty := by rw [← hD]; exact hint
  have hUD : UniqueDiffOn ℝ D := uniqueDiffOn_convex hDconv hintD
  have hUV : UniqueDiffOn ℝ V := by rw [hVD]; exact hUD.inter hO
  -- the bump: `Φ(v) = b(v) v` maps `D` into `V` and is the identity on the ball of radius `r/2`
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO 0 h0O
  let b : ContDiffBump (0 : N) := ⟨r / 2, r, by positivity, by linarith⟩
  let Φ : N → N := fun v => b v • v
  have hΦsm : ContDiff ℝ 1 Φ := b.contDiff.smul contDiff_id
  have hΦeq : ∀ v : N, ‖v‖ < r / 2 → Φ v = v := fun v hv => by
    have : b v = 1 := b.one_of_mem_closedBall (by
      rw [mem_closedBall_zero_iff]; exact hv.le)
    show b v • v = v
    rw [this, one_smul]
  have hΦV : ∀ v ∈ D, Φ v ∈ V := by
    intro v hv
    rw [hVD]
    refine ⟨?_, ?_⟩
    · -- `b(v) v ∈ D`: the cone is closed under nonnegative scaling
      show ((b v • v : N) : E 0) ∈ C
      rw [hmemC]
      intro i
      rw [Submodule.coe_smul, map_smul, smul_eq_mul]
      exact mul_nonneg b.nonneg ((hmemC _).1 hv i)
    · apply hrO
      rw [mem_ball_zero_iff]
      by_cases hvr : ‖v‖ < r
      · calc ‖(b v • v : N)‖ = b v * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
          _ ≤ 1 * ‖v‖ := by gcongr; exact b.le_one
          _ = ‖v‖ := one_mul _
          _ < r := hvr
      · have : b v = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact not_lt.1 hvr)
        show ‖b v • v‖ < r
        rw [this, zero_smul, norm_zero]; exact hr
  -- the extended map `τ = σ ∘ Φ`
  set τ : N → E 0 := fun v => σ (Φ v) with hτdef
  have hτσ : ∀ v : N, ‖v‖ < r / 2 → τ v = σ v := fun v hv => by
    show σ (Φ v) = σ v; rw [hΦeq v hv]
  have hτev : ∀ v : N, ‖v‖ < r / 2 → τ =ᶠ[𝓝 v] σ := fun v hv => by
    have : ball (0 : N) (r / 2) ∈ 𝓝 v := isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
    filter_upwards [this] with w hw
    exact hτσ w (mem_ball_zero_iff.1 hw)
  have hfderiv : ∀ v : N, v ∈ V → ‖v‖ < r / 2 →
      fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) v = fderivWithin ℝ σ V v := by
    intro v hv hvr
    rw [hD, ((hτev v hvr).filter_mono nhdsWithin_le_nhds).fderivWithin_eq (hτσ v hvr), hVD,
      fderivWithin_inter (hO.mem_nhds ?_)]
    exact (hVD ▸ hv : v ∈ D ∩ O).2
  have hτ : ContDiffOn ℝ 1 τ (quadCone (ℓlin ℓ) N) := by
    rw [hD]
    exact hσC.comp hΦsm.contDiffOn hΦV
  have hτ0 : τ 0 = 0 := by
    show σ (Φ 0) = 0
    rw [hΦeq 0 (by rw [norm_zero]; positivity), hσ0]
  have hDτ0 : fderivWithin ℝ τ (quadCone (ℓlin ℓ) N) 0 = 0 := by
    rw [hfderiv 0 h0V (by rw [norm_zero]; positivity), hDσ]
  -- the good-complement constant and the surjectivity of the coordinates
  obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
  have hgood' : ∀ x ∈ N, ∀ p ∈ Y, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)) := fun x hx p hp hle => by
    rw [← hmemC, ← hmemC]; exact hgood x hx p hp hle
  have hℓs : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : E 0, ∀ i ∈ s, ℓ i v = k i :=
    fun s k => ⟨(T 0).symm (k, 0), fun i _ => by
      rw [hℓdef, coordCLMWith_apply, ContinuousLinearEquiv.apply_symm_apply]⟩
  -- Lemma 3.55 in coordinates
  obtain ⟨ρ₁, hρ₁, hmain⟩ := lemma_3_55_core ℓ N Y hY.isCompl hYc hε hgood' hℓs hint τ
    (fun v => hσY _) hτ hτ0 hDτ0
  -- continuity of `Dσ` at `0`: `‖Dσ(v)‖ < ε` for `v` small
  have hcont : ContinuousWithinAt (fderivWithin ℝ σ V) V 0 :=
    (hσC.continuousOn_fderivWithin hUV (le_refl _)) 0 h0V
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := hcont ε hε
  refine ⟨min (min ρ₁ (r / 2)) ρ₂, by positivity, fun v hv hvρ => ?_⟩
  have hvD : v ∈ quadCone (ℓlin ℓ) N := by rw [hD]; exact hVsub hv
  have hvρ₁ : ‖v‖ < ρ₁ := hvρ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hvr : ‖v‖ < r / 2 := hvρ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hvρ₂ : ‖v‖ < ρ₂ := hvρ.trans_le (min_le_right _ _)
  obtain ⟨hmem, hcompl, γ, hγ, hgoodv⟩ := hmain v hvD hvρ₁
  rw [hτσ v hvr] at hmem hgoodv
  rw [hfderiv v hv hvr] at hcompl hgoodv
  set L := fderivWithin ℝ σ V v with hLdef
  set z : E 0 := (v : E 0) + σ v with hzdef
  have hzC : z ∈ C := (hmemC z).2 hmem
  have hgc : IsGoodComplement E (partialQuadrantAtWith T z) (graphSpace N L) Y :=
    ⟨hcompl, γ, hγ, fun h hh y hy hle => hgoodv h hh y hy hle⟩
  refine ⟨hzC, hgc, ⟨?_, Y, hgc⟩⟩
  -- the interior of `N_v ∩ C_z` is nonempty
  have hLnorm : ‖L‖ < ε := by
    have := hρ₂' hv (by rw [dist_zero_right]; exact hvρ₂)
    rwa [hDσ, dist_zero_right] at this
  have hLY : ∀ w : N, L w ∈ Y := fun w =>
    fderivWithin_mem_of_mapsTo ((hσC.differentiableOn one_ne_zero v hv).hasFDerivWithinAt) (hUV v hv)
      hYc (fun x _ => hσY x) hv w
  -- the linear equivalence `N ≃ N_v`, `w ↦ w + L w`
  set A : N →ₗ[ℝ] E 0 := N.subtype + (L : N →ₗ[ℝ] E 0) with hAdef
  have hAinj : Injective A := by
    intro w₁ w₂ hw
    have hw' : (w₁ : E 0) + L w₁ = (w₂ : E 0) + L w₂ := hw
    have h1 : (w₁ : E 0) - w₂ = L w₂ - L w₁ := by
      rw [sub_eq_sub_iff_add_eq_add, hw', add_comm]
    have hmemN : (w₁ : E 0) - w₂ ∈ N := N.sub_mem w₁.2 w₂.2
    have hmemY : (w₁ : E 0) - w₂ ∈ Y := by rw [h1]; exact Y.sub_mem (hLY w₂) (hLY w₁)
    have : (w₁ : E 0) - w₂ = 0 :=
      (Submodule.disjoint_def.1 hY.isCompl.disjoint) _ hmemN hmemY
    exact Subtype.ext (sub_eq_zero.1 this)
  let e : N ≃ₗ[ℝ] graphSpace N L := LinearEquiv.ofInjective A hAinj
  have he : ∀ w : N, ((e w : graphSpace N L) : E 0) = (w : E 0) + L w := fun w =>
    LinearEquiv.ofInjective_apply A (h := hAinj) w
  let eh : N ≃ₜ graphSpace N L := e.toContinuousLinearEquiv.toHomeomorph
  have heh : ∀ w : N, eh w = e w := fun _ => rfl
  obtain ⟨w₀, hw₀⟩ := hintD
  have hopen : IsOpen (eh '' interior D) := eh.isOpenMap _ isOpen_interior
  have hsub : eh '' interior D ⊆ Subtype.val ⁻¹' partialQuadrantAtWith T z := by
    rintro _ ⟨w, hw, rfl⟩
    have hwC : (w : E 0) ∈ C := (interior_subset hw : w ∈ D)
    rw [mem_preimage, heh, he]
    apply subset_partialQuadrantAtWith T hT z
    refine (hgood w w.2 (L w) (hLY w) ?_).1 hwC
    exact (L.le_opNorm w).trans (mul_le_mul_of_nonneg_right hLnorm.le (norm_nonneg _))
  exact ⟨eh w₀, (hopen.subset_interior_iff.2 hsub) ⟨w₀, hw₀, rfl⟩⟩

end Lemma355

/-! ### Corollary 3.41 at the points of the graph -/

section Cor341

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}
  {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  (𝒮 : StabilityData Ct W) {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}

/-- **Corollary 3.41 at the points `v + σ(v)` of the solution graph** (Theorem 3.54 (4), the
surjectivity part): for `v ∈ V` close to `0` the zero `v + σ(v)` of `h + s` lies on level `1` and
`D(h + s)(v + σ(v)) : E₀ → F₀` is a surjective Fredholm operator of index `n − N`. -/
theorem StabilityData.exists_surjective_Dfs'_graph (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hf : IsBasicGerm Ct 𝒮.G f B) (hsurj : Surjective (𝒮.Dfs f))
    {V : Set (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0))}
    {σ : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) → P × W 0} (h0V : 0 ∈ V)
    (hσC : ContinuousOn σ V) (hσ0 : σ 0 = 0)
    (hsol : ∀ y ∈ V, (y : P × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum f ((y : P × W 0) + σ y) = 0) :
    ∃ ρ > 0, ∀ v ∈ V, ‖v‖ < ρ → ∃ x₁ : (ScBanach.paramProd P W) 1,
      (ScBanach.paramProd P W).toBase 1 x₁ = (v : P × W 0) + σ v ∧ x₁ ∈ 𝒮.G.U 1 ∧
      IsFredholm (𝒮.Dfs' f x₁) ∧
      fredholmIndex (𝒮.Dfs' f x₁) = Module.finrank ℝ P - Module.finrank ℝ Q ∧
      Surjective (𝒮.Dfs' f x₁) := by
  obtain ⟨r, hr, hr'⟩ := 𝒮.corollary_3_41 hC hf hsurj
  have hΓ : ContinuousWithinAt (fun v : LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) =>
      (v : P × W 0) + σ v) V 0 :=
    (continuous_subtype_val.continuousOn.add hσC) 0 h0V
  rw [Metric.continuousWithinAt_iff] at hΓ
  obtain ⟨ρ, hρ, hρ'⟩ := hΓ r hr
  refine ⟨ρ, hρ, fun v hv hvρ => ?_⟩
  have h1 := hρ' hv (by rw [dist_zero_right]; exact hvρ)
  rw [Submodule.coe_zero, hσ0, add_zero, dist_zero_right] at h1
  exact hr' _ (hsol v hv).1 h1 (hsol v hv).2

end Cor341

/-! ### Theorem 3.54 (1) in the chart at `x₀`: the nearby zeros -/

section Thm354Nearby

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

set_option maxHeartbeats 800000 in
/-- **Theorem 3.54 (1) in the chart at `x₀`** (the text's property (4) in the proof of Theorem
3.54: "for every `y ∈ V` with `f(y) = 0`, so that `ψ ∘ ϕ(y) = v + σ(v)`, the kernel `ker f'(y)`
is in good position to the partial cone `C_yX` and `f'(y)` is surjective", from Corollary 3.41
and Lemma 3.55).  In the data of `theorem_3_54_graph_wholeChart` (chart `c` at `x₀`, conjugating
sc-diffeomorphism `ψ`, the germ `h + t = 𝒮.fsum h'` with kernel `K = ker D(h + t)(0)`, closed
good complement `Y`, `σ : V' → Y`) there are a presentation `T` of the partial quadrant
`C' = C̃ ⊕ W` and an open neighbourhood `Vx₁ ⊆ Vx` of `x₀` such that for every zero `y ∈ Vx₁` of
`f`, with `z = ψ ∘ ϕ(y) = v + σ(v)`, `v ∈ V'`:
(i) `z` lies on level `1` and `D(h + t)(z) : E'₀ → F'₀` is a surjective Fredholm operator of index
`n − N` (Corollary 3.41);
(ii) `z ∈ C'`, and the tangent space `N_v = {n + Dσ(v)n | n ∈ K}` of the graph at `z` is in good
position to the partial quadrant `C'_z` (`partialQuadrantAtWith T z`) with `Y` as a good
complement (Lemma 3.55).
What is **not** formalized (see the module docstring): the identification `N_v = ker D(h + t)(z)`
and the passage from these statements in the chart at `x₀` to Definition 3.53 at `y`
(`IsGoodPositionGermWholeChart f y`), which needs the chart-independence of the linearization `f'(y)` and
of good position (Definition 2.38 in `T_yX`). -/
theorem theorem_3_54_nearby_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsGoodPositionGermTameWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (Pn Q : Type) (_ : NormedAddCommGroup Pn) (_ : NormedSpace ℝ Pn) (_ : FiniteDimensional ℝ Pn)
      (_ : NormedAddCommGroup Q) (_ : NormedSpace ℝ Q) (_ : FiniteDimensional ℝ Q)
      (W : ScBanach) (Ct : Set Pn) (_ : IsPartialQuadrant (ScBanach.const Pn) Ct)
      (U' : Set ((ScBanach.paramProd Pn W) 0))
      (_ : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
      (ψ : c.φ.model.E 0 → (ScBanach.paramProd Pn W) 0) (_ : IsScSmooth c.U ψ) (_ : ψ 0 = 0)
      (_ : MapsTo ψ c.U U') (𝒮 : StabilityData Ct W) (h' : Pn × W 0 → Q × W 0)
      (Bc : Pn × W 0 → W 0) (_ : IsBasicGerm Ct 𝒮.G h' Bc) (_ : Surjective (𝒮.Dfs h'))
      (_ : IsInGoodPosition (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (Yc : Submodule ℝ (Pn × W 0))
      (V' : Set (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)))
      (σ : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) → Pn × W 0) (Vx : Set X)
      (n' : ℕ) (W' : ScBanach)
      (T : ScIso (ScBanach.paramProd Pn W) ((ScBanach.const (Fin n' → ℝ)).prod W')) (Vx₁ : Set X),
      IsGoodComplement (ScBanach.paramProd Pn W) (Ct ×ˢ univ)
        (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc ∧
      IsClosed (Yc : Set (Pn × W 0)) ∧
      (∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ 0 ∈ V' ∧
      (∀ y, σ y ∈ Yc) ∧ (∀ y, (σ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 σ V' ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V' 0 = 0 ∧
      (∀ y ∈ V', (y : Pn × W 0) + σ y ∈ 𝒮.G.U 0 ∧ 𝒮.fsum h' ((y : Pn × W 0) + σ y) = 0) ∧
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧ InjOn (ψ ∘ c.φ) Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y ↔ 𝒮.fsum h' (ψ (c.φ y)) = 0) ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} =
        (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) => (v : Pn × W 0) + σ v) '' V' ∧
      Ct ×ˢ (univ : Set (W 0)) = T 0 ⁻¹' quadrant n' W' 0 ∧
      IsOpen Vx₁ ∧ x₀ ∈ Vx₁ ∧ Vx₁ ⊆ Vx ∧
      ∀ y ∈ Vx₁, IsZeroAt P f y → ∃ v ∈ V', ψ (c.φ y) = (v : Pn × W 0) + σ v ∧
        (∃ x₁ : (ScBanach.paramProd Pn W) 1,
          (ScBanach.paramProd Pn W).toBase 1 x₁ = (v : Pn × W 0) + σ v ∧ x₁ ∈ 𝒮.G.U 1 ∧
          IsFredholm (𝒮.Dfs' h' x₁) ∧
          fredholmIndex (𝒮.Dfs' h' x₁) = Module.finrank ℝ Pn - Module.finrank ℝ Q ∧
          Surjective (𝒮.Dfs' h' x₁)) ∧
        ((v : Pn × W 0) + σ v ∈ Ct ×ˢ univ) ∧
        IsGoodComplement (ScBanach.paramProd Pn W)
          (partialQuadrantAtWith T ((v : Pn × W 0) + σ v))
          (graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
            (fderivWithin ℝ σ V' v)) Yc ∧
        IsInGoodPosition (ScBanach.paramProd Pn W)
          (partialQuadrantAtWith T ((v : Pn × W 0) + σ v))
          (graphSpace (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
            (fderivWithin ℝ σ V' v)) := by
  classical
  obtain ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    -, -, -, -, -,
    𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hYc, hYcc, -, hV'rel, h0V', hσY, hσ1, hσC, hσ0,
    hDσ, hsol, -, hVxo, hx₀Vx, hVxsub, hinj, hzero, himage⟩ := theorem_3_54_graph_wholeChart hf hg hx₀
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh').1.finite_ker
  obtain ⟨n', W', T, hT⟩ := hCt.prod_univ W
  -- Corollary 3.41 and Lemma 3.55 at the graph points
  obtain ⟨ρ₁, hρ₁, hA⟩ := 𝒮.exists_surjective_Dfs'_graph hCt hh' hsurj h0V' hσC.continuousOn hσ0
    hsol
  obtain ⟨ρ₂, hρ₂, hB⟩ := lemma_3_55_relOpen T hT hpos hYc hYcc hV'rel h0V' σ hσY hσC hσ0 hDσ
  -- the projection onto `K` along `Y`
  have hTC : Submodule.IsTopCompl (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) Yc :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hYc.isCompl.symm hYcc).symm
  set π : Pn × W 0 →L[ℝ] LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) :=
    (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)).projectionOntoL Yc hTC with hπdef
  have hπ : ∀ v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0), ∀ y ∈ Yc,
      π ((v : Pn × W 0) + y) = v := fun v y hy => by
    rw [map_add, Submodule.projectionOntoL_apply_left hTC v,
      (Submodule.projectionOntoL_apply_eq_zero_iff hTC).2 hy, add_zero]
  set ρ := min ρ₁ ρ₂ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  set ρ' := ρ / (‖π‖ + 1) with hρ'def
  have hρ' : 0 < ρ' := by positivity
  -- the neighbourhood `Vx₁`
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have hψφ : ContinuousOn (ψ ∘ c.φ) Vx :=
    (hψsc.isSc1.isSc0.continuousOn_base.comp (c.φ.continuousOn_toFun.mono hVxsub)
      fun y hy => hOU (c.φ.mapsTo_model y (hVxsub hy)))
  refine ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, n', W', T, Vx ∩ (ψ ∘ c.φ) ⁻¹' ball 0 ρ',
    hYc, hYcc, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hVxo, hx₀Vx, hVxsub, hinj, hzero, himage,
    hT,
    hψφ.isOpen_inter_preimage hVxo isOpen_ball, ⟨hx₀Vx, ?_⟩, inter_subset_left, ?_⟩
  · show ψ (c.φ x₀) ∈ ball 0 ρ'
    rw [h0, hψ0]; exact mem_ball_self hρ'
  · rintro y ⟨hyVx, hyball⟩ hy0
    have hz : ψ (c.φ y) ∈ (fun v : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0) =>
        (v : Pn × W 0) + σ v) '' V' := by
      rw [← himage]; exact ⟨y, ⟨hyVx, hy0⟩, rfl⟩
    obtain ⟨v, hv, hveq⟩ := hz
    have hvnorm : ‖v‖ < ρ := by
      have h1 : π (ψ (c.φ y)) = v := by rw [← hveq]; exact hπ v _ (hσY v)
      have h2 : ‖ψ (c.φ y)‖ < ρ' := by
        have := hyball; rwa [mem_preimage, Function.comp_apply, mem_ball_zero_iff] at this
      calc ‖v‖ = ‖π (ψ (c.φ y))‖ := by rw [h1]
        _ ≤ ‖π‖ * ‖ψ (c.φ y)‖ := π.le_opNorm _
        _ ≤ ‖π‖ * ρ' := by gcongr
        _ < (‖π‖ + 1) * ρ' := by gcongr; linarith
        _ = ρ := by rw [hρ'def]; field_simp
    obtain ⟨hzC, hgc, hgp⟩ := hB v hv (hvnorm.trans_le (min_le_right _ _))
    exact ⟨v, hv, hveq.symm, hA v hv (hvnorm.trans_le (min_le_left _ _)), hzC, hgc, hgp⟩

end Thm354Nearby

end Polyfold
