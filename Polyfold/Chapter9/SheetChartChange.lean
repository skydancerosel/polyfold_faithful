import Polyfold.Chapter9.SheetNull

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Definitions 9.4.1 and 9.4.5, pp. 429–431 ("the definition is independent of the choice of
`ϕ`"; 2017: Definitions 9.12, 9.13), for submanifolds of a general M-polyfold.

# Chart changes along a finite-dimensional submanifold

On level `0` a chart change `τ = ψ ∘ φ⁻¹` of an M-polyfold is only continuous.  Along a smooth
finite-dimensional submanifold `M` it is differentiable for the level-`0` norms: the points of
`φ(M)` lie on level `1`, their level-`1` distance is controlled by the level-`0` distance (the
chart retraction of `M` is sc⁺), and `τ` is differentiable from level `1` to level `0`
(Proposition 1.2.1).  Hence the two notions read in M-polyfold charts, `T_z^K M = T_zM`
(Definition 9.4.1) and measure zero (Definition 9.4.5), do not depend on the chart.

## What is formalized

* `ScRetraction.exists_lift_lipschitz`: on the image of an sc⁺-retraction, near `x₀ = ι z`,
  `‖a¹ − z‖₁ ≤ K ‖a − x₀‖₀` for the level-`1` lifts.
* `ScRetraction.hasFDerivWithinAt_of_isSc1`: an sc¹ map `f` is differentiable at `x₀` within the
  image of an sc⁺-retraction, for the level-`0` norms, with derivative `Df(z)`.
* `MPolyfold.exists_hasFDerivWithinAt_transition`: the chart change `ψ ∘ φ⁻¹` is differentiable
  within `φ(M)` at every point of `φ(M)`.
* `MPolyfold.exists_clm_tangentCone_chart_change`: the derivative maps the tangent cone of `φ(K)`
  into the tangent cone of `ψ(K)`, for every `K ⊆ M`.
* `MPolyfold.isRelTangentFull_of_chart` (**Definition 9.4.1 is independent of the chart**):
  `T_z^K M = T_zM` in one M-polyfold chart implies it in every chart.
* `hNull_image_of_pointwise_lipschitz`: a map that is Lipschitz at each point of `S` (with a
  constant and a radius depending on the point) sends separable `d`-null subsets of `S` to
  `d`-null sets.
* `MPolyfold.isHNull_of_forall_exists_chart` (**Definition 9.4.5 is independent of the chart**):
  a subset `C` of a smooth submanifold that is `n`-null in one chart near each of its points is
  `n`-null (`IsHNull`, all charts).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory Metric Module TopologicalSpace Submodule
open scoped NNReal ENNReal

noncomputable section

namespace Polyfold

universe u

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}

/-- **The level-`1` distance on an sc⁺-retract is controlled by the level-`0` distance**: for
`a` in the retract near `x₀ = ι z`, the lift `a¹ = (1₀¹ ∘ r)(a)` satisfies
`‖a¹ − z‖₁ ≤ K ‖a − x₀‖₀` (strict differentiability of the lift on level `1`,
`exists_strict_plusLift`, with `ε = ½`). -/
theorem exists_lift_lipschitz (hR : R.IsScPlus) {z : E 1} (hz : E.toBase 1 z ∈ R.retract) :
    ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ R.retract, ‖a - E.toBase 1 z‖ < δ →
      ‖R.plusLift a - z‖ ≤ K * ‖a - E.toBase 1 z‖ := by
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  set L := R.plusDeriv z with hLdef
  obtain ⟨δS, hδS, hS⟩ := exists_strict_plusLift hR hzU (ε := 1 / 2) (by norm_num)
  have hc := continuousOn_plusLift hR _ (R.retract_subset hz)
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδc⟩ := hc δS hδS
  rw [plusLift_toBase_of_mem_retract hz] at hδc
  refine ⟨δ, hδ, 2 * ‖L‖, by positivity, fun a ha hax => ?_⟩
  have haU := R.retract_subset ha
  set pa := R.plusLift a with hpa
  have hιa : E.toBase 1 pa = a := toBase_plusLift_of_mem_retract hR ha
  have hpaU : pa ∈ E.lvlSet R.U 1 := plusLift_mem_lvlSet hR haU
  have hpaz : ‖pa - z‖ < δS := by
    have := hδc haU (by rw [dist_eq_norm]; exact hax); rwa [dist_eq_norm] at this
  have h := hS pa hpaU z hzU hpaz (by rw [sub_self, norm_zero]; exact hδS)
  have e1 : R.plusLift (E.toBase 1 pa) = pa := by rw [hιa]
  have e2 : R.plusLift (E.toBase 1 z) = z := plusLift_toBase_of_mem_retract hz
  have e3 : E.toBase 1 (pa - z) = a - E.toBase 1 z := by rw [map_sub, hιa]
  rw [e1, e2, e3] at h
  have h1 : ‖pa - z‖ ≤ ‖L (a - E.toBase 1 z)‖ + 1 / 2 * ‖pa - z‖ := by
    calc ‖pa - z‖ = ‖(pa - z - L (a - E.toBase 1 z)) + L (a - E.toBase 1 z)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖pa - z - L (a - E.toBase 1 z)‖ + ‖L (a - E.toBase 1 z)‖ := norm_add_le _ _
      _ ≤ 1 / 2 * ‖pa - z‖ + ‖L (a - E.toBase 1 z)‖ := by gcongr
      _ = _ := by ring
  have h2 := L.le_opNorm (a - E.toBase 1 z)
  linarith

/-- **An sc¹ map is differentiable along an sc⁺-retract, for the level-`0` norms**: if `f` is sc¹
on an sc-domain `U` and `S` lies in `U` and in the image of an sc⁺-retraction, then `f` has the
derivative `Df(z)` within `S` at `x₀ = ι z ∈ S`.  (Proposition 1.2.1 gives the differentiability
of `f : U₁ → F₀` at `z`; `exists_lift_lipschitz` turns the level-`1` remainder into a level-`0`
one.) -/
theorem hasFDerivWithinAt_of_isSc1 (hR : R.IsScPlus) {F : ScBanach} {U : Set (E 0)}
    (hU : IsScDomain E U) {f : E 0 → F 0} (hf : IsSc1 U f) {z : E 1}
    (hz : E.toBase 1 z ∈ R.retract) (hzU : E.toBase 1 z ∈ U) {S : Set (E 0)}
    (hS : S ⊆ R.retract ∩ U) :
    HasFDerivWithinAt f (scDeriv U f z) S (E.toBase 1 z) := by
  obtain ⟨δ, hδ, K, hK, hlip⟩ := exists_lift_lipschitz hR hz
  have h1 := hf.isSc1With_scDeriv.hasFDerivWithinAt_level hU (m := 0) (x := z) hzU
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h1 ⊢
  intro c hc
  have hK1 : 0 < K + 1 := by positivity
  have hc' : 0 < c / (K + 1) := by positivity
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (h1 hc')
  have hsmall : 0 < min δ (ρ / (K + 1)) := lt_min hδ (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hsmall)] with a haS had
  rw [Metric.mem_ball, dist_eq_norm] at had
  have ha := (hS haS).1
  have haU := (hS haS).2
  set pa := R.plusLift a with hpa
  have hιa : E.toBase 1 pa = a := toBase_plusLift_of_mem_retract hR ha
  have hle := hlip a ha (lt_of_lt_of_le had (min_le_left _ _))
  have hlt : ‖a - E.toBase 1 z‖ < ρ / (K + 1) := lt_of_lt_of_le had (min_le_right _ _)
  have hpaρ : pa ∈ Metric.ball z ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖pa - z‖ ≤ K * ‖a - E.toBase 1 z‖ := hle
      _ ≤ (K + 1) * ‖a - E.toBase 1 z‖ := by gcongr; linarith
      _ < (K + 1) * (ρ / (K + 1)) := mul_lt_mul_of_pos_left hlt hK1
      _ = ρ := by field_simp
  have hpaU : pa ∈ E.lvlSet U 1 := by change E.toBase 1 pa ∈ U; rw [hιa]; exact haU
  have h := hball ⟨hpaρ, hpaU⟩
  simp only [mem_ofPred_eq, Function.comp_apply, levelMap_zero, levelDeriv_zero,
    ContinuousLinearMap.comp_apply] at h
  have e0 : ∀ y : E 1, E.incl 0 y = E.toBase 1 y := fun _ => rfl
  rw [e0, e0, e0, map_sub, hιa] at h
  calc ‖f a - f (E.toBase 1 z) - scDeriv U f z (a - E.toBase 1 z)‖
      ≤ c / (K + 1) * ‖pa - z‖ := h
    _ ≤ c / (K + 1) * (K * ‖a - E.toBase 1 z‖) := by gcongr
    _ = c * (K / (K + 1)) * ‖a - E.toBase 1 z‖ := by ring
    _ ≤ c * 1 * ‖a - E.toBase 1 z‖ := by
        gcongr
        rw [div_le_one hK1]; linarith
    _ = c * ‖a - E.toBase 1 z‖ := by ring

end ScRetraction

/-! ### Pointwise Lipschitz maps and null sets -/

section PointwiseLipschitz

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- **A map that is Lipschitz at each point of `A` sends `d`-null sets to `d`-null sets**: if for
every `a ∈ A` there are `C`, `δ` with `dist (f b) (f a) ≤ C dist b a` for `b ∈ A`, `dist b a < δ`,
and `A` is separable and `d`-null, then `f '' A` is `d`-null.  (`A` is the countable union of
pieces of small diameter on which `f` is Lipschitz.) -/
theorem hNull_image_of_pointwise_lipschitz {f : E → F} {A : Set E} {d : ℝ} (hd : 0 ≤ d)
    (hf : ∀ a ∈ A, ∃ C : ℝ≥0, ∃ δ > 0, ∀ b ∈ A, dist b a < δ → dist (f b) (f a) ≤ C * dist b a)
    (hsep : IsSeparable A) (hA : HNull d A) : HNull d (f '' A) := by
  have := hsep.separableSpace
  obtain ⟨s, hs, hsd⟩ := exists_countable_dense ↥A
  have : Countable ↥s := hs.to_subtype
  let Pc : ℕ × ↥s → Set E := fun kq => {a | a ∈ A ∧
    (∀ b ∈ A, dist b a < 1 / ((kq.1 : ℝ) + 1) → dist (f b) (f a) ≤ ((kq.1 : ℝ) + 1) * dist b a) ∧
    dist a (kq.2.1 : E) < 1 / (2 * ((kq.1 : ℝ) + 1))}
  have hcov : f '' A ⊆ ⋃ kq, f '' Pc kq := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨C, δ, hδ, hC⟩ := hf a ha
    obtain ⟨k, hk⟩ := exists_nat_gt (max (C : ℝ) (1 / δ))
    have hk1 : (C : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
    have hk2 : 1 / δ < k := lt_of_le_of_lt (le_max_right _ _) hk
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkδ : 1 / ((k : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hkpos]
      have := (div_lt_iff₀ hδ).1 hk2
      nlinarith
    obtain ⟨q, hq, hdq⟩ := hsd.exists_dist_lt ⟨a, ha⟩
      (show (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) by positivity)
    refine mem_iUnion.2 ⟨(k, ⟨q, hq⟩), a, ⟨ha, fun b hb hba => ?_, hdq⟩, rfl⟩
    refine (hC b hb (hba.trans hkδ)).trans ?_
    gcongr
    linarith
  refine (hNull_iUnion fun kq => ?_).mono hcov
  refine (hA.mono fun a ha => ha.1).image_lipschitzOn (K := ⟨(kq.1 : ℝ) + 1, by positivity⟩) hd
    (LipschitzOnWith.of_dist_le_mul fun b hb a ha => ?_)
  refine hb.2.1 |> fun _ => ha.2.1 b hb.1 ?_
  have h1 := hb.2.2
  have h2 := ha.2.2
  have hkpos : (0 : ℝ) < (kq.1 : ℝ) + 1 := by positivity
  have e : 1 / ((kq.1 : ℝ) + 1) = 1 / (2 * ((kq.1 : ℝ) + 1)) + 1 / (2 * ((kq.1 : ℝ) + 1)) := by
    field_simp; norm_num
  rw [e]
  calc dist b a ≤ dist b (kq.2.1 : E) + dist (kq.2.1 : E) a := dist_triangle _ _ _
    _ < _ := by rw [dist_comm (kq.2.1 : E) a]; exact add_lt_add h1 h2

end PointwiseLipschitz

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

omit [T2Space X] [ParacompactSpace X] in
/-- `φ⁻¹` tends to `z` along chart images. -/
theorem tendsto_symm_nhdsWithin_image (φ : MChart X) {D : Set X} (hD : D ⊆ φ.source) {z : X}
    (hz : z ∈ φ.source) : Tendsto φ.symm (𝓝[φ '' D] (φ z)) (𝓝 z) := by
  have hsO : φ '' D ⊆ φ.model.O := by
    rintro _ ⟨k, hk, rfl⟩; exact φ.mapsTo_model k (hD hk)
  have h := (φ.continuousOn_invFun (φ z) (φ.mapsTo_model z hz)).mono hsO
  rw [ContinuousWithinAt] at h
  rwa [show φ.toPartialEquiv.symm (φ z) = z from φ.symm_apply_apply hz] at h

omit [T2Space X] [ParacompactSpace X] in
/-- The tangent cone of `φ(K)` at `φ(z)` only sees the part of `K` in the domain of a second
chart at `z`. -/
theorem tangentConeAt_image_subset_inter_source (φ ψ : MChart X) (K : Set X) {z : X}
    (hzφ : z ∈ φ.source) (hzψ : z ∈ ψ.source) :
    tangentConeAt ℝ (φ '' (K ∩ φ.source)) (φ z) ⊆
      tangentConeAt ℝ (φ '' (K ∩ ψ.source ∩ φ.source)) (φ z) := by
  refine tangentConeAt_mono_nhds (nhdsWithin_le_iff.2 ?_)
  have hc := tendsto_symm_nhdsWithin_image φ (D := K ∩ φ.source) inter_subset_right hzφ
  filter_upwards [hc (ψ.isOpen_source.mem_nhds hzψ), self_mem_nhdsWithin] with p hp hpS
  obtain ⟨k, hk, rfl⟩ := hpS
  rw [mem_preimage, φ.symm_apply_apply hk.2] at hp
  exact ⟨k, ⟨⟨hk.1, hp⟩, hk.2⟩, rfl⟩

/-- **Chart changes are differentiable along a smooth finite-dimensional submanifold**, for the
level-`0` norms: for charts `φ`, `ψ` at `z ∈ M`, the transition `ψ ∘ φ⁻¹` has a derivative at
`φ(z)` within `φ(M ∩ dom ψ ∩ dom φ)` (`ScRetraction.hasFDerivWithinAt_of_isSc1` for the chart
sc⁺-retraction of `M` and the sc-smooth map `(ψ ∘ φ⁻¹) ∘ r` on the overlap). -/
theorem exists_hasFDerivWithinAt_transition {φ ψ : MChart X} (hφ : P.IsChart φ)
    (hψ : P.IsChart ψ) {M : Set X} (hM : P.IsSmoothSubmanifold M) {z : X} (hz : z ∈ M)
    (hzφ : z ∈ φ.source) (hzψ : z ∈ ψ.source) :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
      HasFDerivWithinAt (φ.transition ψ) L (φ '' (M ∩ ψ.source ∩ φ.source)) (φ z) := by
  set d := hM.data hz
  have hzV : z ∈ d.V := hM.mem_data_V hz
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hφ d hz hzV
  obtain ⟨hz1, hzt, -⟩ := chartTangent_eq_range hφ d ht hz hzV hzφ
  obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
  have hf : IsScSmooth R.U (φ.transition ψ ∘ R) :=
    (hφ.compatible hψ (P := P)).1.comp_isScSmooth R hR
  have hzR : φ z ∈ R.retract := hR ▸ φ.mem_overlap ψ hzφ hzψ
  have hd := ScRetraction.hasFDerivWithinAt_of_isSc1 htp R.isScDomain hf.isSc1
    (z := levelLift φ 1 z) (by rw [hz1]; exact hzt) (by rw [hz1]; exact R.retract_subset hzR)
    (S := t.retract ∩ R.retract) (fun a ha => ⟨ha.1, R.retract_subset ha.2⟩)
  rw [hz1] at hd
  refine ⟨_, (hd.congr (fun a ha => ?_) ?_).mono_of_mem_nhdsWithin ?_⟩
  · change φ.transition ψ a = φ.transition ψ (R a)
    rw [R.apply_eq_self_of_mem_retract ha.2]
  · change φ.transition ψ (φ z) = φ.transition ψ (R (φ z))
    rw [R.apply_eq_self_of_mem_retract hzR]
  · have hev := eventually_mem_retract d ht (K := M ∩ ψ.source) inter_subset_left
      (d.toSubData.mem_shrink φ hz hzV hzφ) hzφ
    filter_upwards [hev, self_mem_nhdsWithin] with p hp hpS
    refine ⟨hp, ?_⟩
    obtain ⟨k, hk, rfl⟩ := hpS
    rw [hR]
    exact φ.mem_overlap ψ hk.2 hk.1.2

/-- **The derivative of the chart change maps tangent cones to tangent cones**: for `K ⊆ M`, the
limit directions of `φ(K)` at `φ(z)` are sent to limit directions of `ψ(K)` at `ψ(z)`. -/
theorem exists_clm_tangentCone_chart_change {φ ψ : MChart X} (hφ : P.IsChart φ)
    (hψ : P.IsChart ψ) {M : Set X} (hM : P.IsSmoothSubmanifold M) {z : X} (hz : z ∈ M)
    (hzφ : z ∈ φ.source) (hzψ : z ∈ ψ.source) :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0,
      HasFDerivWithinAt (φ.transition ψ) L (φ '' (M ∩ ψ.source ∩ φ.source)) (φ z) ∧
      ∀ K ⊆ M, MapsTo L (tangentConeAt ℝ (φ '' (K ∩ φ.source)) (φ z))
        (tangentConeAt ℝ (ψ '' (K ∩ ψ.source)) (ψ z)) := by
  obtain ⟨L, hL⟩ := exists_hasFDerivWithinAt_transition hφ hψ hM hz hzφ hzψ
  refine ⟨L, hL, fun K hKM v hv => ?_⟩
  have hsub : φ '' (K ∩ ψ.source ∩ φ.source) ⊆ φ '' (M ∩ ψ.source ∩ φ.source) :=
    image_mono (inter_subset_inter_left _ (inter_subset_inter_left _ hKM))
  have h1 := (hL.mono hsub).mapsTo_tangent_cone
    (tangentConeAt_image_subset_inter_source φ ψ K hzφ hzψ hv)
  rw [φ.transition_apply ψ hzφ] at h1
  refine tangentConeAt_mono ?_ h1
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [φ.transition_apply ψ hk.2]
  exact ⟨k, ⟨hk.1.1, hk.1.2⟩, rfl⟩

/-- **`T_z^K M = T_zM` does not depend on the chart** (Definition 9.4.1 (1), 2021 p. 429: "the
definition is independent of the choice of `ϕ`"), from one M-polyfold chart `φ` to another `ψ`.
The derivative `L₁` of the chart change maps `T_z^K M` in `φ` into `T_z^K M` in `ψ`, and is
injective on `T_zM` since the derivative `L₂` of the inverse chart change inverts it there
(uniqueness of derivatives on tangent cones); the tangent spaces in the two charts have the same
dimension. -/
theorem chartRelTangent_eq_of_chart {M K : Set X} (hM : P.IsSmoothSubmanifold M) (hKM : K ⊆ M)
    {z : X} (hzK : z ∈ K) {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    (hzφ : z ∈ φ.source) (hzψ : z ∈ ψ.source)
    (h : (P.chartRelTangent hφ K z : Set (φ.model.E 0)) = P.chartTangent hφ M z) :
    (P.chartRelTangent hψ K z : Set (ψ.model.E 0)) = P.chartTangent hψ M z := by
  have hz := hKM hzK
  obtain ⟨Nφ, hNφ, hfinφ⟩ := exists_submodule_chartTangent hφ hM hz hzφ
  obtain ⟨Nψ, hNψ, hfinψ⟩ := exists_submodule_chartTangent hψ hM hz hzψ
  obtain ⟨L₁, hL₁, hc₁⟩ := exists_clm_tangentCone_chart_change hφ hψ hM hz hzφ hzψ
  obtain ⟨L₂, hL₂, -⟩ := exists_clm_tangentCone_chart_change hψ hφ hM hz hzψ hzφ
  set S := φ '' (M ∩ ψ.source ∩ φ.source) with hS
  have hmaps : MapsTo (φ.transition ψ) S (ψ '' (M ∩ φ.source ∩ ψ.source)) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [φ.transition_apply ψ hk.2]
    exact ⟨k, ⟨⟨hk.1.1, hk.2⟩, hk.1.2⟩, rfl⟩
  have hL₂' : HasFDerivWithinAt (ψ.transition φ) L₂ (ψ '' (M ∩ φ.source ∩ ψ.source))
      (φ.transition ψ (φ z)) := by rw [φ.transition_apply ψ hzφ]; exact hL₂
  have hcomp := hL₂'.comp (φ z) hL₁ hmaps
  have hid : HasFDerivWithinAt (ψ.transition φ ∘ φ.transition ψ)
      (ContinuousLinearMap.id ℝ (φ.model.E 0)) S (φ z) := by
    refine (hasFDerivWithinAt_id (φ z) S).congr (fun a ha => ?_) ?_
    · obtain ⟨k, hk, rfl⟩ := ha
      change ψ.transition φ (φ.transition ψ (φ k)) = φ k
      rw [φ.transition_apply ψ hk.2, ψ.transition_apply φ hk.1.2]
    · change ψ.transition φ (φ.transition ψ (φ z)) = φ z
      rw [φ.transition_apply ψ hzφ, ψ.transition_apply φ hzψ]
  have heq := hcomp.unique_on hid
  -- `L₂ L₁ = id` on `T_zM`
  have hspan : (Nφ : Set (φ.model.E 0)) ⊆ span ℝ (tangentConeAt ℝ S (φ z)) := by
    rw [hNφ]
    refine (chartTangent_subset_chartRelTangent hM hz hφ hzφ).trans ?_
    exact SetLike.coe_subset_coe.2
      (span_mono (tangentConeAt_image_subset_inter_source φ ψ M hzφ hzψ))
  have hinv : ∀ v ∈ Nφ, L₂ (L₁ v) = v := fun v hv =>
    LinearMap.eqOn_span (f := ((L₂.comp L₁ : φ.model.E 0 →L[ℝ] φ.model.E 0) :
      φ.model.E 0 →ₗ[ℝ] φ.model.E 0)) (g := LinearMap.id) heq (hspan hv)
  have hrel : P.chartRelTangent hφ K z = Nφ := SetLike.coe_injective (h.trans hNφ.symm)
  have hle : P.chartRelTangent hψ K z ≤ Nψ := chartRelTangent_le hM hKM hzK hψ hzψ hNψ
  have hmap : Nφ.map (L₁ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0) ≤ P.chartRelTangent hψ K z := by
    rw [← hrel, chartRelTangent, chartRelTangent, Submodule.map_span]
    exact span_mono (image_subset_iff.2 (hc₁ K hKM))
  have hinj : Function.Injective ((L₁ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0).domRestrict Nφ) := by
    intro v w hvw
    have h1 : L₁ (v : φ.model.E 0) = L₁ (w : φ.model.E 0) := hvw
    have h2 := congrArg L₂ h1
    rw [hinv v v.2, hinv w w.2] at h2
    exact Subtype.ext h2
  have hfr : finrank ℝ (Nφ.map (L₁ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0)) = finrank ℝ Nφ := by
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj hinj
  obtain ⟨-, e, -⟩ := exists_linearEquiv_chartTangent hφ hψ M hzφ hzψ hNφ hNψ
  have hfinrel : FiniteDimensional ℝ (P.chartRelTangent hψ K z) :=
    Submodule.finiteDimensional_of_le hle
  have hge : finrank ℝ Nψ ≤ finrank ℝ (P.chartRelTangent hψ K z) := by
    rw [← e.finrank_eq, ← hfr]
    exact Submodule.finrank_mono hmap
  rw [← hNψ, Submodule.eq_of_le_of_finrank_le hle hge]

/-- **Definition 9.4.1 in one chart**: if `T_z^K M = T_zM` in one M-polyfold chart at `z`, then
in every chart (`IsRelTangentFull`). -/
theorem isRelTangentFull_of_chart {M K : Set X} (hM : P.IsSmoothSubmanifold M) (hKM : K ⊆ M)
    {z : X} (hzK : z ∈ K) {φ : MChart X} (hφ : P.IsChart φ) (hzφ : z ∈ φ.source)
    (h : (P.chartRelTangent hφ K z : Set (φ.model.E 0)) = P.chartTangent hφ M z) :
    P.IsRelTangentFull M K z := fun _ hψ hzψ =>
  chartRelTangent_eq_of_chart hM hKM hzK hφ hψ hzφ hzψ h

/-- **Measure zero does not depend on the chart** (Definition 9.4.5, 2021 p. 431): a subset `C`
of a smooth finite-dimensional submanifold `M` which near each of its points is `n`-null in one
M-polyfold chart has `n`-dimensional measure zero (`IsHNull`: in all charts).  Chart changes are
differentiable along `M` (`exists_hasFDerivWithinAt_transition`), hence Lipschitz at each point
of `φ(M)`, and `φ(M)` is locally separable. -/
theorem isHNull_of_forall_exists_chart {M C : Set X} (hM : P.IsSmoothSubmanifold M) (hC : C ⊆ M)
    {n : ℕ} (h : ∀ z ∈ C, ∃ φ : MChart X, P.IsChart φ ∧ z ∈ φ.source ∧ ∃ V, IsOpen V ∧ z ∈ V ∧
      HNull (n : ℝ) (φ '' (C ∩ V ∩ φ.source))) : P.IsHNull n C := by
  refine isHNull_of_local fun z hz => ?_
  obtain ⟨φ, hφ, hzφ, V, hV, hzV, hnull⟩ := h z hz
  obtain ⟨δ, hδ, hsep⟩ := isSeparable_chart_ball hφ hM (hC hz) hzφ
  obtain ⟨V', hV', hVe⟩ := exists_isOpen_chartBall φ M z δ
  have hzV' : z ∈ V' := by
    have : z ∈ chartBall φ M z δ := ⟨⟨hC hz, hzφ⟩, by rw [sub_self, norm_zero]; exact hδ⟩
    rw [hVe] at this
    exact this.2
  refine ⟨V ∩ V' ∩ φ.source, (hV.inter hV').inter φ.isOpen_source, ⟨⟨hzV, hzV'⟩, hzφ⟩, ?_⟩
  intro ψ hψ D hD hDψ _
  have hDsub : D ⊆ C ∩ V ∩ φ.source := fun w hw => ⟨⟨(hD hw).1, (hD hw).2.1.1⟩, (hD hw).2.2⟩
  have hA : HNull (n : ℝ) (φ '' D) := hnull.mono (image_mono hDsub)
  have hAsep : IsSeparable (φ '' D) := hsep.mono (image_mono fun w hw => by
    rw [hVe]; exact ⟨hC (hD hw).1, (hD hw).2.1.2⟩)
  have himg : ψ '' D = φ.transition ψ '' (φ '' D) := by
    rw [image_image]
    exact image_congr fun w hw => (φ.transition_apply ψ (hD hw).2.2).symm
  rw [himg]
  refine hNull_image_of_pointwise_lipschitz (Nat.cast_nonneg n) (fun a ha => ?_) hAsep hA
  obtain ⟨w, hw, rfl⟩ := ha
  obtain ⟨L, hL⟩ := exists_hasFDerivWithinAt_transition hφ hψ hM (hC (hD hw).1) (hD hw).2.2
    (hDψ hw)
  have hsub : φ '' D ⊆ φ '' (M ∩ ψ.source ∩ φ.source) :=
    image_mono fun w' hw' => ⟨⟨hC (hD hw').1, hDψ hw'⟩, (hD hw').2.2⟩
  obtain ⟨Cst, hCst⟩ := (hL.mono hsub).isBigO_sub.bound
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hCst
  refine ⟨Real.toNNReal Cst, ρ, hρ, fun b hb hbd => ?_⟩
  have hb' : ‖φ.transition ψ b - φ.transition ψ (φ w)‖ ≤ Cst * ‖b - φ w‖ := hball ⟨hbd, hb⟩
  rw [dist_eq_norm, dist_eq_norm]
  exact hb'.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal Cst) (norm_nonneg _))

end MPolyfold

end Polyfold
