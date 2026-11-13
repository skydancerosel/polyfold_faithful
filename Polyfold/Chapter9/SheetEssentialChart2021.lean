import Polyfold.Chapter9.PropertyTShrinking2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
§9.4, Definition 9.4.1, p. 429, and Lemma 9.4.4, p. 431 (2017: Definition 9.12, p. 315, and
Lemma 9.13, p. 317), for submanifolds of an M-polyfold.

# Essential points of `K ⊆ M` in M-polyfold charts, and Lemma 9.4.4

Definition 9.4.1 reads the relative tangent space `T_z^K M` (the linear hull of the limit
directions of `K` at `z`) in a chart of the manifold `M`, and calls `z ∈ K` essential if it is a
limit of points `z_k ∈ K` with `T_{z_k}^K M = T_{z_k} M`.  The proof of Lemma 9.4.4 reads the same
space in an M-polyfold chart `ψ` of the ambient space: with `D = ψ(K ∩ U(z))` it is the linear
hull of the limit directions of `D` at `ψ(z)`.  This file takes that reading for submanifolds of
an M-polyfold, which carry no manifold charts of their own in this project.

## What is formalized

* `chartRelTangent hψ K z`: the span of the tangent cone of `ψ(K)` at `ψ(z)` in `E₀` (Mathlib's
  `tangentConeAt`; its span is the linear hull of the limit unit directions, as in the Mathlib
  reading `relTangent` of `Chapter9/BranchingGeometryManifold.lean`).
* `chartRelTangent_le`: for `K ⊆ M`, `T_z^K M ⊆ T_zM` in every chart (the chords of the chart
  retract of `M` are approximated by its tangent space, `ScRetraction.exists_approx`).
* `chartTangent_subset_chartRelTangent`: conversely `T_zM ⊆ T_z^M M` (for level-`1` directions
  `p` into the quadrant, `Dr(z)(ι p)` is a limit direction of the retract, and these span
  `range Dr(z)` since `E₁` is dense in `E₀`;
  `ScRetraction.range_scDeriv_subset_span_tangentConeAt`).
* `IsRelTangentFull M K z` (`T_z^K M = T_zM` in every chart around `z`) and
  `chartEssentialSet M K` (Definition 9.4.1 (2) in this reading); every point of `M` is essential
  for `M ⊆ M` (`chartEssentialSet_self`), so the reading is not degenerate.
* **Lemma 9.4.4** (`lemma_9_4_4_chart`): for `n`-dimensional submanifolds `M`, `M'` of an
  M-polyfold, `K = M ∩ M'` has the same essential points as a subset of `M` and of `M'`.  The
  pointwise statement (`isRelTangentFull_iff`) holds in each chart separately.  For different
  dimensions the lemma does not hold as we read it (`lemma_9_4_4_mixed_dim`).
* **The note in Definition 9.4.7, p. 432** (`submanifoldTangent_eq_of_mem_chartEssentialSet`): at
  an essential point of `M ∩ M'` the tangent spaces agree (they agree at the approximating points by
  dimension, and the set where they agree is closed, `exists_isOpen_submanifoldTangent_ne`).

## Not formalized

The comparison with Definition 9.4.1 in the induced manifold structure of a sheet (for tame sheets,
`MathlibManifoldBridge.cornerChartedSpace`), i.e. the change of charts between the corner chart
of the sheet and the M-polyfold chart, and Lemma 9.4.6 in this reading; so the fields of
`SheetGeometry` for M-polyfold sheets are not built from this file.  Since 2026-11-12 Lemma 9.4.6
in this reading is `MPolyfold.lemma_9_4_6_chart` and the `SheetGeometry` of the `n`-dimensional
submanifolds is `MPolyfold.sheetGeometry` (`SheetEssential.lean`); measure zero in the
M-polyfold charts agrees with the corner-chart reading on tame sheets
(`isHNull_iff_isMeasureZero_sheet`, `SheetNullBridge.lean`).
-/

open Set Module Submodule Filter Topology

universe u

namespace Polyfold

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}

/-- **The tangent space of an sc⁺-retract is spanned by its limit directions** (on level `0`): for
`z ∈ E₁` with `ι z` in the retract, `range Dr(z)` lies in the span of the tangent cone of the
retract at `ι z`.  (For level-`1` vectors `p` with nonnegative quadrant coordinates, `z + s p`
stays in `U₁` for small `s > 0`, and `ι ∘ (1₀¹ ∘ r) ∘ ι` is differentiable there with derivative
`Dr(z) ∘ ι`, so `Dr(z)(ι p)` is a limit direction; every vector of `range Dr(z)` is `Dr(z)(ι q)`,
and `q = (q + c e) − c e` with `e` of quadrant coordinates `> 1`, which exists since `E₁` is dense
in `E₀`.) -/
theorem range_scDeriv_subset_span_tangentConeAt (hR : R.IsScPlus) {z : E 1}
    (hz : E.toBase 1 z ∈ R.retract) :
    range (scDeriv R.U R z) ⊆ span ℝ (tangentConeAt ℝ R.retract (E.toBase 1 z)) := by
  obtain ⟨n, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  obtain ⟨O, hO, hUO⟩ := R.relOpen.relOpen
  set ι := E.toBase 1 with hιdef
  set D := scDeriv R.U R z with hDdef
  let ℓ : Fin n → E 0 →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T 0 : E 0 →L[ℝ] _))
  have hmemC : ∀ e, e ∈ C ↔ ∀ j, 0 ≤ ℓ j e := fun e => by rw [hT]; exact Iff.rfl
  have hzU : z ∈ E.lvlSet R.U 1 := R.retract_subset hz
  have hxU : ι z ∈ O ∩ C := hUO ▸ R.retract_subset hz
  -- positive level-`1` directions give limit directions of the retract
  have hf := ι.hasFDerivAt.comp_hasFDerivWithinAt z (hasFDerivWithinAt_plusLift hR hzU)
  have hfz : (ι ∘ (R.plusLift ∘ ι)) z = ι z := by
    change ι (R.plusLift (ι z)) = ι z
    rw [toBase_plusLift hR (R.retract_subset hz), R.apply_eq_self_of_mem_retract hz]
  have himg : (ι ∘ (R.plusLift ∘ ι)) '' E.lvlSet R.U 1 ⊆ R.retract := by
    rintro _ ⟨q, hq, rfl⟩
    change ι (R.plusLift (ι q)) ∈ R.retract
    rw [toBase_plusLift hR hq]
    exact R.apply_mem_retract hq
  have hcone : ∀ p : E 1, (∀ j, 0 ≤ ℓ j (ι p)) →
      D (ι p) ∈ tangentConeAt ℝ R.retract (ι z) := by
    intro p hp
    have hpS : p ∈ tangentConeAt ℝ (E.lvlSet R.U 1) z := by
      refine mem_tangentConeAt_of_add_smul_mem (l := 𝓝[>] (0 : ℝ)) (c := _root_.id)
        (tendsto_id'.2 (nhdsWithin_mono _ fun s (hs : 0 < s) => hs.ne')) ?_
      have hcont : Continuous fun s : ℝ => ι z + s • ι p := by fun_prop
      have h0 := hcont.tendsto 0
      rw [zero_smul, add_zero] at h0
      filter_upwards [(h0.eventually (hO.mem_nhds hxU.1)).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs1 hs2
      change ι (z + s • p) ∈ R.U
      rw [hUO, map_add, map_smul]
      refine ⟨hs1, (hmemC _).2 fun j => ?_⟩
      rw [map_add, map_smul, smul_eq_mul]
      exact add_nonneg ((hmemC _).1 hxU.2 j) (mul_nonneg (le_of_lt hs2) (hp j))
    have h := tangentConeAt_mono himg (hfz ▸ hf.mapsTo_tangent_cone hpS)
    have hD : (ι.comp ((R.plusDeriv z).comp ι)) p = D (ι p) := by
      change ι (R.plusDeriv z (ι p)) = D (ι p)
      exact toBase_plusDeriv hR hzU (ι p)
    rwa [hD] at h
  -- a level-`1` vector with quadrant coordinates `> 1`
  obtain ⟨e, he⟩ : ∃ e : E 1, ∀ j, 1 < ℓ j (ι e) := by
    have hG : IsOpen {u : E 0 | ∀ j, 1 < ℓ j u} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (ℓ j).continuous
    have hne : ({u : E 0 | ∀ j, 1 < ℓ j u}).Nonempty :=
      ⟨(T 0).symm ((fun _ => (2 : ℝ)), 0), fun j => by
        change (1 : ℝ) < (T 0 ((T 0).symm ((fun _ => (2 : ℝ)), 0))).1 j
        rw [ContinuousLinearEquiv.apply_symm_apply]
        norm_num⟩
    exact (E.denseRange_inclK 0 1).exists_mem_open hG hne
  -- every vector of `range D`
  rintro w ⟨u, rfl⟩
  have hw : D u ∈ range D := ⟨u, rfl⟩
  set q := R.plusDeriv z (D u)
  have hιq : ι q = D u := toBase_plusDeriv_of_mem_range hR hz hw
  have hDD : D (D u) = D u :=
    congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (R.scDeriv_comp_self hz)
  set c : ℝ := ∑ j, |ℓ j (ι q)|
  have hc : 0 ≤ c := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hcj : ∀ j, |ℓ j (ι q)| ≤ c := fun j =>
    Finset.single_le_sum (f := fun j => |ℓ j (ι q)|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
  have h1 : D (ι (q + c • e)) ∈ tangentConeAt ℝ R.retract (ι z) := hcone _ fun j => by
    rw [map_add, map_smul, map_add, map_smul, smul_eq_mul]
    have := neg_abs_le (ℓ j (ι q))
    nlinarith [hcj j, he j]
  have h2 : D (ι (c • e)) ∈ tangentConeAt ℝ R.retract (ι z) := hcone _ fun j => by
    rw [map_smul, map_smul, smul_eq_mul]
    exact mul_nonneg hc (by linarith [he j])
  have heq : D u = D (ι (q + c • e)) - D (ι (c • e)) := by
    rw [map_add, map_add, add_sub_cancel_right, hιq, hDD]
  rw [SetLike.mem_coe, heq]
  exact sub_mem (subset_span h1) (subset_span h2)

end ScRetraction

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- Points of `ψ(K)` near `ψ(z)` lie in the chart retract `ψ(W ∩ M)` of `M` (`K ⊆ M`,
`z ∈ W`). -/
theorem eventually_mem_retract {M K : Set X} (d : P.SubmanifoldData M) {ψ : MChart X}
    {t : ScRetraction ψ.model.E ψ.model.C} (ht : t.retract = ψ '' (d.toSubData.shrink ψ ∩ M))
    (hKM : K ⊆ M) {z : X} (hzW : z ∈ d.toSubData.shrink ψ) (hzψ : z ∈ ψ.source) :
    ∀ᶠ p in 𝓝[ψ '' (K ∩ ψ.source)] (ψ z), p ∈ t.retract := by
  have hsO : ψ '' (K ∩ ψ.source) ⊆ ψ.model.O := by
    rintro _ ⟨k, hk, rfl⟩; exact ψ.mapsTo_model k hk.2
  have hc : Tendsto ψ.symm (𝓝[ψ '' (K ∩ ψ.source)] (ψ z)) (𝓝 z) := by
    have h := (ψ.continuousOn_invFun (ψ z) (ψ.mapsTo_model z hzψ)).mono hsO
    rw [ContinuousWithinAt] at h
    rwa [show ψ.toPartialEquiv.symm (ψ z) = z from ψ.symm_apply_apply hzψ] at h
  filter_upwards [hc ((d.toSubData.isOpen_shrink ψ).mem_nhds hzW), self_mem_nhdsWithin]
    with p hpW hps
  obtain ⟨k, hk, rfl⟩ := hps
  rw [mem_preimage, ψ.symm_apply_apply hk.2] at hpW
  rw [ht]
  exact ⟨k, ⟨hpW, hKM hk.1⟩, rfl⟩

/-- `v = w` if `‖v − w‖ ≤ ε ‖v‖` for every `ε > 0`. -/
theorem eq_of_forall_norm_sub_le {E : Type*} [NormedAddCommGroup E] {v w : E}
    (h : ∀ ε > 0, ‖v - w‖ ≤ ε * ‖v‖) : v = w := by
  by_contra hne
  have hpos : 0 < ‖v - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h1 := h (‖v - w‖ / (2 * (‖v‖ + 1))) (by positivity)
  have h2 : ‖v - w‖ / (2 * (‖v‖ + 1)) * ‖v‖ < ‖v - w‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  linarith

/-- **Limit directions of `K ⊆ M` are tangent to `M`**: in an M-polyfold chart `ψ` around
`z ∈ K`, the tangent cone of `ψ(K)` at `ψ(z)` lies in the chart image of `T_zM`.  (For `v` in the
cone, `ψ(z) + d_k ∈ ψ(K)` with `c_k d_k → v`; the chord estimate gives
`‖d_k − Dt(z) d_k‖ ≤ ε ‖d_k‖`, so `v = Dt(z) v`.) -/
theorem tangentConeAt_subset_chartTangent {M K : Set X} (hM : P.IsSmoothSubmanifold M)
    (hKM : K ⊆ M) {z : X} (hzK : z ∈ K) {ψ : MChart X} (hψ : P.IsChart ψ)
    (hzψ : z ∈ ψ.source) :
    tangentConeAt ℝ (ψ '' (K ∩ ψ.source)) (ψ z) ⊆ P.chartTangent hψ M z := by
  have hzM := hKM hzK
  set d := hM.data hzM
  have hzV : z ∈ d.V := hM.mem_data_V hzM
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hψ d hzM hzV
  obtain ⟨hz, hzt, hTr⟩ := chartTangent_eq_range hψ d ht hzM hzV hzψ
  have hev := eventually_mem_retract d ht hKM (d.toSubData.mem_shrink ψ hzM hzV hzψ) hzψ
  set D := scDeriv t.U t (levelLift ψ 1 z)
  intro v hv
  rw [hTr]
  refine ⟨v, (eq_of_forall_norm_sub_le fun ε hε => ?_).symm⟩
  obtain ⟨δ, hδ, happ⟩ := ScRetraction.exists_approx htp (by rw [hz]; exact hzt) hε
  obtain ⟨c, dd, hd0, hds, hcd⟩ := mem_tangentConeAt_iff_exists_seq.1 hv
  have hlim : Tendsto (fun k => ψ z + dd k) atTop (𝓝[ψ '' (K ∩ ψ.source)] (ψ z)) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd0, hds⟩
  have hsmall : ∀ᶠ k in atTop, ‖dd k‖ < δ :=
    (tendsto_norm_zero.comp hd0).eventually (gt_mem_nhds hδ)
  have hineq : ∀ᶠ k in atTop, ‖c k • dd k - D (c k • dd k)‖ - ε * ‖c k • dd k‖ ≤ 0 := by
    filter_upwards [hlim.eventually hev, hsmall] with k h1 h2
    have h := happ (ψ z + dd k) h1 (ψ z) hzt (by rw [hz, add_sub_cancel_left]; exact h2)
      (by rw [hz, sub_self, norm_zero]; exact hδ)
    rw [add_sub_cancel_left] at h
    rw [map_smul, ← smul_sub, norm_smul, norm_smul]
    nlinarith [norm_nonneg (c k)]
  have hg : Continuous fun u => ‖u - D u‖ - ε * ‖u‖ := by fun_prop
  have := le_of_tendsto ((hg.tendsto v).comp hcd) hineq
  linarith

/-- **`T_z^K M`, read in the M-polyfold chart `ψ`** (Definition 9.4.1 (1) as in the proof of
Lemma 9.4.4, 2021 p. 431): the span of the tangent cone of `ψ(K)` at `ψ(z)`. -/
def chartRelTangent {ψ : MChart X} (_hψ : P.IsChart ψ) (K : Set X) (z : X) :
    Submodule ℝ (ψ.model.E 0) :=
  span ℝ (tangentConeAt ℝ (ψ '' (K ∩ ψ.source)) (ψ z))

/-- `T_z^K M ⊆ T_zM` in every chart, for `K ⊆ M`. -/
theorem chartRelTangent_le {M K : Set X} (hM : P.IsSmoothSubmanifold M) (hKM : K ⊆ M) {z : X}
    (hzK : z ∈ K) {ψ : MChart X} (hψ : P.IsChart ψ) (hzψ : z ∈ ψ.source)
    {N : Submodule ℝ (ψ.model.E 0)} (hN : (N : Set (ψ.model.E 0)) = P.chartTangent hψ M z) :
    P.chartRelTangent hψ K z ≤ N :=
  span_le.2 (hN ▸ tangentConeAt_subset_chartTangent hM hKM hzK hψ hzψ)

variable (P) in
/-- **`T_z^K M = T_zM`**, read in every M-polyfold chart around `z`. -/
def IsRelTangentFull (M K : Set X) (z : X) : Prop :=
  ∀ (ψ : MChart X) (hψ : P.IsChart ψ), z ∈ ψ.source →
    (P.chartRelTangent hψ K z : Set (ψ.model.E 0)) = P.chartTangent hψ M z

variable (P) in
/-- **The essential points of `K ⊆ M`** (Definition 9.4.1 (2), 2021 p. 429): the points of `K`
that are limits of points `z_k ∈ K` with `T_{z_k}^K M = T_{z_k} M`, in M-polyfold charts. -/
def chartEssentialSet (M K : Set X) : Set X :=
  {z | z ∈ K ∧ ∃ u : ℕ → X, (∀ k, u k ∈ K ∧ P.IsRelTangentFull M K (u k)) ∧
    Tendsto u atTop (𝓝 z)}

theorem chartEssentialSet_subset (M K : Set X) : P.chartEssentialSet M K ⊆ K := fun _ h => h.1

/-- **Every vector of `T_zM` is in `T_z^M M`** (in every chart; from
`ScRetraction.range_scDeriv_subset_span_tangentConeAt`). -/
theorem chartTangent_subset_chartRelTangent {M : Set X} (hM : P.IsSmoothSubmanifold M) {z : X}
    (hz : z ∈ M) {ψ : MChart X} (hψ : P.IsChart ψ) (hzψ : z ∈ ψ.source) :
    P.chartTangent hψ M z ⊆ P.chartRelTangent hψ M z := by
  set d := hM.data hz
  have hzV := hM.mem_data_V hz
  obtain ⟨t, ht, htp⟩ := exists_plusRetraction hψ d hz hzV
  obtain ⟨hz', hzt, hTr⟩ := chartTangent_eq_range hψ d ht hz hzV hzψ
  have h := ScRetraction.range_scDeriv_subset_span_tangentConeAt htp (by rw [hz']; exact hzt)
  rw [hz'] at h
  rw [hTr]
  refine h.trans (SetLike.coe_subset_coe.2 (span_mono (tangentConeAt_mono ?_)))
  rw [ht]
  exact image_mono fun q hq => ⟨hq.2, d.toSubData.shrink_subset_source ψ hq.1⟩

/-- **Every point of `M` is essential for `M ⊆ M`**: `T_z^M M = T_zM` in every chart, so the
reading of Definition 9.4.1 in M-polyfold charts is not degenerate (the field `ess_self` of a
`SheetGeometry`). -/
theorem isRelTangentFull_self {M : Set X} (hM : P.IsSmoothSubmanifold M) {z : X} (hz : z ∈ M) :
    P.IsRelTangentFull M M z := fun ψ hψ hzψ => by
  obtain ⟨N, hN, -⟩ := exists_submodule_chartTangent hψ hM hz hzψ
  refine subset_antisymm ?_ (chartTangent_subset_chartRelTangent hM hz hψ hzψ)
  rw [← hN]
  exact chartRelTangent_le hM subset_rfl hz hψ hzψ hN

theorem chartEssentialSet_self {M : Set X} (hM : P.IsSmoothSubmanifold M) :
    P.chartEssentialSet M M = M :=
  subset_antisymm (chartEssentialSet_subset M M) fun z hz =>
    ⟨hz, fun _ => z, fun _ => ⟨hz, isRelTangentFull_self hM hz⟩, tendsto_const_nhds⟩

/-- The chart core of Lemma 9.4.4: if `K ⊆ M ∩ M'`, both `n`-dimensional, and `T_z^K M = T_zM` in
the chart `ψ`, then `T_zM' = T_zM` in `ψ` (both are `n`-dimensional and contain `T_z^K M`). -/
theorem chartTangent_eq_of_chartRelTangent_eq {M M' K : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (hM' : P.IsSubmanifoldOfDim M' n) (hK : K ⊆ M ∩ M') {z : X}
    (hzK : z ∈ K) {ψ : MChart X} (hψ : P.IsChart ψ) (hzψ : z ∈ ψ.source)
    (h : (P.chartRelTangent hψ K z : Set (ψ.model.E 0)) = P.chartTangent hψ M z) :
    P.chartTangent hψ M' z = P.chartTangent hψ M z := by
  obtain ⟨N, hN, hfin⟩ := exists_submodule_chartTangent hψ hM.1 (hK hzK).1 hzψ
  obtain ⟨N', hN', hfin'⟩ := exists_submodule_chartTangent hψ hM'.1 (hK hzK).2 hzψ
  have hRN : P.chartRelTangent hψ K z = N := SetLike.coe_injective (h.trans hN.symm)
  have hle : N ≤ N' := hRN ▸ chartRelTangent_le hM'.1 (fun _ h => (hK h).2) hzK hψ hzψ hN'
  have hNN : N = N' := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_chartTangent hψ (hM.2 z (hK hzK).1) hM.1 hzψ hN,
      finrank_chartTangent hψ (hM'.2 z (hK hzK).2) hM'.1 hzψ hN'])
  rw [← hN', ← hN, hNN]

/-- **Lemma 9.4.4 pointwise**: for `K ⊆ M ∩ M'` with `M`, `M'` `n`-dimensional,
`T_z^K M = T_zM` iff `T_z^K M' = T_zM'` (in each M-polyfold chart). -/
theorem isRelTangentFull_iff {M M' K : Set X} {n : ℕ} (hM : P.IsSubmanifoldOfDim M n)
    (hM' : P.IsSubmanifoldOfDim M' n) (hK : K ⊆ M ∩ M') {z : X} (hzK : z ∈ K) :
    P.IsRelTangentFull M K z ↔ P.IsRelTangentFull M' K z := by
  have hK' : K ⊆ M' ∩ M := fun _ h => ⟨(hK h).2, (hK h).1⟩
  constructor
  · intro h ψ hψ hzψ
    rw [chartTangent_eq_of_chartRelTangent_eq hM hM' hK hzK hψ hzψ (h ψ hψ hzψ)]
    exact h ψ hψ hzψ
  · intro h ψ hψ hzψ
    rw [chartTangent_eq_of_chartRelTangent_eq hM' hM hK' hzK hψ hzψ (h ψ hψ hzψ)]
    exact h ψ hψ hzψ

/-- **Lemma 9.4.4, 2021 p. 431 (2017: Lemma 9.13, p. 317)**, for `n`-dimensional submanifolds
`M`, `M'` of an M-polyfold, with Definition 9.4.1 read in M-polyfold charts: a point of
`K = M ∩ M'` is essential for `K ⊆ M` iff it is essential for `K ⊆ M'`.  As in the book for
sheets of one dimension (for different dimensions it does not hold as we read it,
`lemma_9_4_4_mixed_dim`). -/
theorem lemma_9_4_4_chart {M M' : Set X} {n : ℕ} (hM : P.IsSubmanifoldOfDim M n)
    (hM' : P.IsSubmanifoldOfDim M' n) :
    P.chartEssentialSet M (M ∩ M') = P.chartEssentialSet M' (M' ∩ M) := by
  rw [inter_comm M' M]
  ext z
  simp only [chartEssentialSet, mem_ofPred_eq]
  refine and_congr_right fun _ => exists_congr fun u => and_congr_left fun _ =>
    forall_congr' fun k => and_congr_right fun hk => isRelTangentFull_iff hM hM' subset_rfl hk

/-- At a point of `M ∩ M'` (both `n`-dimensional) with `T_z^K M = T_zM`, `K = M ∩ M'`, the tangent
spaces agree. -/
theorem submanifoldTangent_eq_of_isRelTangentFull {M M' : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (hM' : P.IsSubmanifoldOfDim M' n) {z : X} (hz : z ∈ M ∩ M')
    (h : P.IsRelTangentFull M (M ∩ M') z) :
    P.submanifoldTangent M z = P.submanifoldTangent M' z := by
  obtain ⟨ψ, hψ, hzψ⟩ := P.exists_isChart_mem_source z
  exact (chartTangent_eq_iff hψ hzψ).1
    (chartTangent_eq_of_chartRelTangent_eq hM hM' subset_rfl hz hψ hzψ (h ψ hψ hzψ)).symm

/-- **The note in Definition 9.4.7, 2021 p. 432**: at an essential point `z` of `M ∩ M'` (both
`n`-dimensional), `T_zM = T_zM'`.  (They agree at the approximating points `z_k`, and the set of
common points with equal tangent spaces is closed in `M ∩ M'`.) -/
theorem submanifoldTangent_eq_of_mem_chartEssentialSet {M M' : Set X} {n : ℕ}
    (hM : P.IsSubmanifoldOfDim M n) (hM' : P.IsSubmanifoldOfDim M' n) {z : X}
    (hz : z ∈ P.chartEssentialSet M (M ∩ M')) :
    P.submanifoldTangent M z = P.submanifoldTangent M' z := by
  obtain ⟨hzK, u, hu, hlim⟩ := hz
  by_contra hne
  obtain ⟨O, hO, hzO, hOne⟩ := exists_isOpen_submanifoldTangent_ne hM hM' hzK.1 hzK.2 hne
  obtain ⟨k, hk⟩ := (hlim.eventually (hO.mem_nhds hzO)).exists
  exact hOne (u k) ⟨(hu k).1, hk⟩
    (submanifoldTangent_eq_of_isRelTangentFull hM hM' (hu k).1 (hu k).2)

end MPolyfold

end Polyfold
