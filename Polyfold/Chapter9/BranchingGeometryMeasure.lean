import Mathlib

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.4 "The Geometry of Local Branching Structures" (2021 pp. 429–436; 2017
pp. 316–321): the measure-theoretic core of the proof of **Lemma 9.4.6** (2021 p. 431; 2017:
Lemma 9.14), in a finite-dimensional real normed space.  Numbers and pages are the 2021 text's,
the 2017 ones in parentheses.

# Points where a set is "thin" have measure zero

## The text, paraphrased

(Proof of Lemma 9.4.6, pp. 431–432, "similarly as Lemma 2.8 in [57]") At a point `0` of
`K ⊆ ℝⁿ` where the linear hull `Σ` of the limits of `zₖ/|zₖ|`, `zₖ ∈ K ∖ {0}`, `zₖ → 0`, lies in
a hyperplane `ℝⁿ⁻¹ × {0}`, `K` is contained near `0` in every cone `Γ_δ = {(a, b) | |b| ≤ δ|a|}`,
so `ε⁻ⁿ μ(B_ε ∩ K) ≤ C(δ) → 0`: `0` is a point of Lebesgue density `0`.  A set all of whose
points have density `0` has measure zero.

## What is formalized

* `unitDirections A x` (the limits `e = lim (zₖ - x)/‖zₖ - x‖` of the text, with `zₖ ∈ A ∖ {x}`,
  `zₖ → x`) and `span_unitDirections` (its linear hull is the span of Mathlib's tangent cone
  `tangentConeAt ℝ A x`).
* `eventually_abs_le_of_tangentConeAt` (near `x`, `A` lies in every cone
  `{|ℓ(y - x)| ≤ δ‖y - x‖}` around the kernel of a functional `ℓ` vanishing on the tangent
  cone), `exists_pos_measure_cone_lt` (`C(δ) < 1` for small `δ`, since `ker ℓ` is a null set).
* `addHaar_setOf_span_tangentConeAt_ne_top`: for every `A ⊆ E` and every additive Haar measure
  `μ` on `E`, `μ {x ∈ A | span(tangentConeAt ℝ A x) ≠ E} = 0`.

## The choices made

* The text argues with the density at every point of the non-essential set; we use the Lebesgue
  density theorem (`Besicovitch.ae_tendsto_measure_inter_div`, valid for arbitrary, not
  necessarily measurable, sets) in the contrapositive: almost every point of `A` has density `1`,
  and at a point of density `1` the cone estimate forces the tangent cone to span `E`.  The
  constant `C(δ)` is not computed: `C(δ) → 0` follows from continuity of `μ` from above and
  `μ(ker ℓ) = 0` (`Measure.addHaar_submodule`).
* The norm of `E` is arbitrary (for `Fin n → ℝ` the sup norm); the span of the unit directions
  does not depend on it (`span_unitDirections`).
-/

open Set Filter Topology MeasureTheory Metric Module
open scoped Pointwise

noncomputable section

namespace Polyfold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The unit directions of the text -/

/-- **The unit vectors of Definition 9.4.1 (1)**: the limits `e = lim (zₖ - x)/‖zₖ - x‖` for
sequences `zₖ ∈ A ∖ {x}` with `zₖ → x` (in the text `x = ϕ(z) = 0`). -/
def unitDirections (A : Set E) (x : E) : Set E :=
  {e | ∃ u : ℕ → E, (∀ k, u k ∈ A \ {x}) ∧ Tendsto u atTop (𝓝 x) ∧
    Tendsto (fun k => ‖u k - x‖⁻¹ • (u k - x)) atTop (𝓝 e)}

theorem unitDirections_subset_tangentConeAt (A : Set E) (x : E) :
    unitDirections A x ⊆ tangentConeAt ℝ A x := by
  rintro e ⟨u, hu, hlim, he⟩
  refine mem_tangentConeAt_of_seq atTop (fun k => ‖u k - x‖⁻¹) (fun k => u k - x) ?_ ?_ he
  · simpa using hlim.sub_const x
  · exact Eventually.of_forall fun k => by simpa using (hu k).1

/-- A nonzero vector of the tangent cone has, up to sign, its unit vector among the unit
directions. -/
theorem exists_unitDirections_of_mem_tangentConeAt {A : Set E} {x v : E}
    (hv : v ∈ tangentConeAt ℝ A x) (hv0 : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ unitDirections A x ∨ -(‖v‖⁻¹ • v) ∈ unitDirections A x := by
  obtain ⟨c, d, hd0, hds, hcd⟩ := (mem_tangentConeAt_iff_exists_seq).1 hv
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
  -- eventually `c k • d k ≠ 0`
  have hne : ∀ᶠ k in atTop, c k • d k ≠ 0 :=
    hcd.eventually (isOpen_ne.mem_nhds hv0)
  -- the normalised vectors converge to `v/‖v‖`
  have hnorm : Tendsto (fun k => ‖c k • d k‖⁻¹ • (c k • d k)) atTop (𝓝 (‖v‖⁻¹ • v)) :=
    ((hcd.norm.inv₀ hnv.ne').smul hcd)
  have hsign : ∀ᶠ k in atTop, c k • d k ≠ 0 ∧ x + d k ∈ A := hne.and hds
  -- the unit vector of `d k` is `± ` that of `c k • d k`
  have hunit : ∀ k, c k • d k ≠ 0 → ‖d k‖⁻¹ • d k =
      (if 0 < c k then (1 : ℝ) else -1) • (‖c k • d k‖⁻¹ • (c k • d k)) := by
    intro k hk
    have hc : c k ≠ 0 := fun h => hk (by simp [h])
    have hd : d k ≠ 0 := fun h => hk (by simp [h])
    rw [norm_smul, smul_smul, smul_smul]
    congr 1
    have hnd : ‖d k‖ ≠ 0 := norm_ne_zero_iff.2 hd
    rw [Real.norm_eq_abs, mul_inv]
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hc)]; field_simp
  by_cases hfreq : ∃ᶠ k in atTop, 0 < c k
  · left
    obtain ⟨φ, hφ, hpos⟩ := extraction_of_frequently_atTop hfreq
    have hev := hφ.tendsto_atTop.eventually hsign
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨fun k => x + d (φ (k + N)), fun k => ?_, ?_, ?_⟩
    · refine ⟨(hN (k + N) (by omega)).2, ?_⟩
      intro h
      have h' : d (φ (k + N)) = 0 := by simpa using h
      exact (hN (k + N) (by omega)).1 (by simp [h'])
    · have := (hd0.comp hφ.tendsto_atTop).comp (tendsto_add_atTop_nat N)
      simpa using tendsto_const_nhds.add this
    · have h1 := (hnorm.comp hφ.tendsto_atTop).comp (tendsto_add_atTop_nat N)
      refine h1.congr fun k => ?_
      simp only [Function.comp_apply, add_sub_cancel_left]
      rw [hunit _ (hN (k + N) (by omega)).1, if_pos (hpos (k + N)), one_smul]
  · right
    rw [not_frequently] at hfreq
    have hneg : ∀ᶠ k in atTop, c k < 0 := (hfreq.and hne).mono fun k ⟨h1, h2⟩ =>
      lt_of_le_of_ne (not_lt.1 h1) fun h => h2 (by simp [h])
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hneg.and hsign)
    refine ⟨fun k => x + d (k + N), fun k => ?_, ?_, ?_⟩
    · refine ⟨(hN (k + N) (by omega)).2.2, ?_⟩
      intro h
      have h' : d (k + N) = 0 := by simpa using h
      exact (hN (k + N) (by omega)).2.1 (by simp [h'])
    · have := hd0.comp (tendsto_add_atTop_nat N)
      simpa using tendsto_const_nhds.add this
    · have h1 := (hnorm.comp (tendsto_add_atTop_nat N)).neg
      refine h1.congr fun k => ?_
      simp only [Function.comp_apply, add_sub_cancel_left]
      rw [hunit _ (hN (k + N) (by omega)).2.1,
        if_neg (not_lt.2 (hN (k + N) (by omega)).1.le), neg_one_smul]

/-- **The linear hull of the unit directions is the span of the tangent cone**: Definition
9.4.1 (1) of the text agrees with the span of Mathlib's `tangentConeAt`. -/
theorem span_unitDirections (A : Set E) (x : E) :
    Submodule.span ℝ (unitDirections A x) = Submodule.span ℝ (tangentConeAt ℝ A x) := by
  refine le_antisymm (Submodule.span_mono (unitDirections_subset_tangentConeAt A x))
    (Submodule.span_le.2 fun v hv => ?_)
  by_cases hv0 : v = 0
  · rw [hv0]; exact Submodule.zero_mem _
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  have hv' : v = ‖v‖ • (‖v‖⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hnv, one_smul]
  rcases exists_unitDirections_of_mem_tangentConeAt hv hv0 with h | h
  · rw [hv']; exact Submodule.smul_mem _ _ (Submodule.subset_span h)
  · rw [hv', ← neg_neg (‖v‖⁻¹ • v)]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.subset_span h))

/-! ### The cone estimate -/

/-- **Near `x`, `A` lies in every cone around `ker ℓ`** (proof of Lemma 9.4.6, p. 432): if the
continuous functional `ℓ` vanishes on the tangent cone of `A` at `x`, then for every `δ > 0`,
eventually near `x`, the points `y ∈ A` satisfy `|ℓ(y - x)| ≤ δ‖y - x‖`. -/
theorem eventually_abs_le_of_tangentConeAt [FiniteDimensional ℝ E] {A : Set E} {x : E}
    {ℓ : E →L[ℝ] ℝ} (hℓ : ∀ v ∈ tangentConeAt ℝ A x, ℓ v = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, y ∈ A → |ℓ (y - x)| ≤ δ * ‖y - x‖ := by
  by_contra h
  rw [not_eventually] at h
  obtain ⟨u, hu, hP⟩ := exists_seq_forall_of_frequently h
  simp only [Classical.not_imp, not_le] at hP
  have hne : ∀ k, u k - x ≠ 0 := fun k h0 => by
    have := (hP k).2
    rw [h0] at this
    simp at this
  have hw : ∀ k, ‖u k - x‖⁻¹ • (u k - x) ∈ sphere (0 : E) 1 := fun k => by
    simp [norm_smul, hne k]
  obtain ⟨e, -, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hw
  have hmem : e ∈ tangentConeAt ℝ A x := by
    refine mem_tangentConeAt_of_seq atTop (fun k => ‖u (φ k) - x‖⁻¹) (fun k => u (φ k) - x) ?_
      ?_ hlim
    · simpa using (hu.comp hφ.tendsto_atTop).sub_const x
    · exact Eventually.of_forall fun k => by simpa using (hP (φ k)).1
  have hge : δ ≤ |ℓ e| := by
    have hc : Tendsto (fun k => |ℓ (‖u (φ k) - x‖⁻¹ • (u (φ k) - x))|) atTop (𝓝 |ℓ e|) :=
      ((ℓ.continuous.tendsto e).comp hlim).abs
    refine ge_of_tendsto hc (Eventually.of_forall fun k => ?_)
    have h1 := (hP (φ k)).2
    have hn : 0 < ‖u (φ k) - x‖ := norm_pos_iff.2 (hne _)
    rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm, le_inv_mul_iff₀ hn]
    linarith
  rw [hℓ e hmem, abs_zero] at hge
  linarith

/-- The cone `{v | |ℓ v| ≤ δ‖v‖}`. -/
def coneAround (ℓ : E →L[ℝ] ℝ) (δ : ℝ) : Set E := {v | |ℓ v| ≤ δ * ‖v‖}

theorem isClosed_coneAround (ℓ : E →L[ℝ] ℝ) (δ : ℝ) : IsClosed (coneAround ℓ δ) :=
  isClosed_le (continuous_abs.comp ℓ.continuous) (continuous_const.mul continuous_norm)

/-- **`C(δ) < 1` for small `δ`** (proof of Lemma 9.4.6, p. 432): for `ℓ ≠ 0`, the part of the unit
ball in the cone `{|ℓ v| ≤ δ‖v‖}` has smaller measure than the ball for some `δ > 0` (the cones
decrease to `ker ℓ`, a null set). -/
theorem exists_pos_measure_cone_lt [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ δ > 0, μ (coneAround ℓ δ ∩ closedBall 0 1) < μ (closedBall 0 1) := by
  set C : ℕ → Set E := fun k => coneAround ℓ (1 / ((k : ℝ) + 1)) ∩ closedBall 0 1 with hC
  have hanti : Antitone C := by
    intro k m hkm v hv
    refine ⟨?_, hv.2⟩
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkm 1)
    exact hv.1.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg v))
  have hmeas : ∀ k, NullMeasurableSet (C k) μ := fun k =>
    ((isClosed_coneAround ℓ _).inter isClosed_closedBall).measurableSet.nullMeasurableSet
  have hfin : ∃ k, μ (C k) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right)⟩
  have hlim := tendsto_measure_iInter_atTop hmeas hanti hfin
  have hker : ((LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)) : Submodule ℝ E) ≠ ⊤ := by
    intro h
    apply hℓ
    ext v
    have : v ∈ LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) := by rw [h]; exact Submodule.mem_top
    simpa using this
  have hsub : (⋂ k, C k) ⊆ (LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ) : Set E) := by
    intro v hv
    simp only [mem_iInter] at hv
    change ℓ v = 0
    have hle : ∀ k : ℕ, |ℓ v| ≤ 1 / ((k : ℝ) + 1) * ‖v‖ := fun k => (hv k).1
    have ht : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * ‖v‖) atTop (𝓝 (0 * ‖v‖)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
    rw [zero_mul] at ht
    have : |ℓ v| ≤ 0 := ge_of_tendsto' ht hle
    exact abs_nonpos_iff.1 this
  have hzero : μ (⋂ k, C k) = 0 := measure_mono_null hsub (Measure.addHaar_submodule μ _ hker)
  have hpos : 0 < μ (closedBall (0 : E) 1) := measure_closedBall_pos μ 0 one_pos
  rw [hzero] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hpos)).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-! ### The main estimate -/

/-- **The non-full points of a set are a null set** (the measure-theoretic content of Lemma
9.4.6, 2021 p. 431; 2017: Lemma 9.14): for every `A ⊆ E` (`E` finite-dimensional) and every
additive Haar measure `μ`, the set of `x ∈ A` at which the tangent cone of `A` does not span `E`
has measure zero.  No measurability of `A` is needed. -/
theorem addHaar_setOf_span_tangentConeAt_ne_top [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) :
    μ {x | x ∈ A ∧ Submodule.span ℝ (tangentConeAt ℝ A x) ≠ ⊤} = 0 := by
  set B : Set E := {x | x ∈ A ∧ Submodule.span ℝ (tangentConeAt ℝ A x) ≠ ⊤} with hBdef
  by_contra hB
  have hdens := Besicovitch.ae_tendsto_measure_inter_div μ B
  set P : E → Prop := fun x => Tendsto (fun r => μ (B ∩ closedBall x r) / μ (closedBall x r))
    (𝓝[>] 0) (𝓝 1) with hPdef
  have hex : ∃ x ∈ B, P x := by
    by_contra hcon
    push Not at hcon
    have h0 : μ ({x | ¬ P x} ∩ B) = 0 :=
      le_antisymm ((Measure.le_restrict_apply B _).trans (ae_iff.1 hdens).le) bot_le
    exact hB (measure_mono_null (fun x hx => (⟨hcon x hx, hx⟩ : x ∈ {x | ¬ P x} ∩ B)) h0)
  obtain ⟨x, ⟨hxA, hspan⟩, hx⟩ := hex
  obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hspan)
  set ℓ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f with hℓdef
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    apply hf0
    ext v
    have := congrArg (fun g : E →L[ℝ] ℝ => g v) h
    simpa [hℓdef] using this
  have hℓB : ∀ v ∈ tangentConeAt ℝ B x, ℓ v = 0 := fun v hv =>
    hfle (Submodule.subset_span (tangentConeAt_mono (fun y hy => hy.1) hv))
  obtain ⟨δ, hδ, hlt⟩ := exists_pos_measure_cone_lt μ hℓ0
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (eventually_abs_le_of_tangentConeAt hℓB hδ)
  set c : ENNReal := μ (coneAround ℓ δ ∩ closedBall 0 1) / μ (closedBall 0 1) with hcdef
  have hratio : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (B ∩ closedBall x r) / μ (closedBall x r) ≤ c := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
    have hsub : B ∩ closedBall x r ⊆
        (fun y => y + -x) ⁻¹' (r • (coneAround ℓ δ ∩ closedBall 0 1)) := by
      intro y hy
      have hdist : dist y x < ρ := lt_of_le_of_lt (mem_closedBall.1 hy.2) hr.2
      have hcone := hball y hdist hy.1
      refine ⟨r⁻¹ • (y - x), ⟨?_, ?_⟩, ?_⟩
      · change |ℓ (r⁻¹ • (y - x))| ≤ δ * ‖r⁻¹ • (y - x)‖
        rw [map_smul, smul_eq_mul, abs_mul, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hr.1]
        calc r⁻¹ * |ℓ (y - x)| ≤ r⁻¹ * (δ * ‖y - x‖) :=
              mul_le_mul_of_nonneg_left hcone (inv_nonneg.2 hr.1.le)
          _ = δ * (r⁻¹ * ‖y - x‖) := by ring
      · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hr.1, ← dist_eq_norm]
        exact inv_mul_le_one_of_le₀ (mem_closedBall.1 hy.2) hr.1.le
      · change r • r⁻¹ • (y - x) = y + -x
        rw [smul_inv_smul₀ hr.1.ne', sub_eq_add_neg]
    have h1 : μ (B ∩ closedBall x r) ≤
        ENNReal.ofReal (r ^ finrank ℝ E) * μ (coneAround ℓ δ ∩ closedBall 0 1) := by
      calc μ (B ∩ closedBall x r)
          ≤ μ ((fun y => y + -x) ⁻¹' (r • (coneAround ℓ δ ∩ closedBall 0 1))) := measure_mono hsub
        _ = μ (r • (coneAround ℓ δ ∩ closedBall 0 1)) := measure_preimage_add_right μ (-x) _
        _ = _ := Measure.addHaar_smul_of_nonneg μ hr.1.le _
    have h2 : μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 1) :=
      Measure.addHaar_closedBall' μ x hr.1.le
    have hr0 : ENNReal.ofReal (r ^ finrank ℝ E) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos hr.1 _
    calc μ (B ∩ closedBall x r) / μ (closedBall x r)
        ≤ ENNReal.ofReal (r ^ finrank ℝ E) * μ (coneAround ℓ δ ∩ closedBall 0 1) /
            (ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 1)) := by
          rw [h2]; exact ENNReal.div_le_div_right h1 _
      _ = c := ENNReal.mul_div_mul_left _ _ hr0 ENNReal.ofReal_ne_top
  have hle : (1 : ENNReal) ≤ c := le_of_tendsto hx hratio
  have hc1 : c < 1 := by
    rw [hcdef]
    exact ENNReal.div_lt_of_lt_mul (by rw [one_mul]; exact hlt)
  exact absurd hle (not_le.2 hc1)

end Polyfold
