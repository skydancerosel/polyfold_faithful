import Polyfold.Chapter9.GeneralLevelZero

/-!
# Chapter 9 at boundary points: the good points of Lemma 9.3.4

HWZ, *Polyfold and Fredholm Theory* (Springer 2021), §9.2–§9.3, pp. 412–424 (2017: §9.1–§9.2).

The good-point input of Lemma 9.3.4 (`HasOrientedGoodPointsAt`, `OrientationUniqueness.lean`)
was derived in `OrientationRn.lean` from the ball form of the graph representation
(`HasGraphBallAt`): every small `u` of the tangent space `T = T_xA` is the projection of a point
of `A`.  The project's earlier hypothesis `HasGraphBallAt` was stronger than the text needs: the
argument only uses the points of `A` over a small ball `S` around `t h₀` for one direction `h₀`
of `T`.  Here `h₀` is chosen in the cone of admissible directions of the partial quadrant at
`φ(x)` (`goodDirections`), and the points over `S` come from the uniform form of the ray graph
representation (`ScRetraction.exists_graph_unif`).

## Main results

* `MPolyfold.exists_graph_unif_chart`: Lemmas 9.2.10, 9.2.11 (2021 pp. 414–417) uniformly in
  the direction, for every smooth finite-dimensional submanifold in every chart.
* `MPolyfold.exists_small_cone`: an admissible direction with its cone, of norm at most `1/2`.
* `MPolyfold.hasOrientedGoodPointsAt`: the good-point input of Lemma 9.3.4 (Proposition 9.2.8
  for oriented families with the continuity of orientations) at every point of every M-polyfold,
  in every dimension.
* `EpGroupoid.lemma_9_3_4_general`: Lemma 9.3.4 (2021 p. 423; 2017: Lemma 9.10) for every
  branched ep⁺-subgroupoid, with no hypothesis on the boundary.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **2021 Lemmas 9.2.10, 9.2.11 (pp. 414–417; 2017: Lemmas 9.7, 9.8), uniformly in the
direction**: for a smooth finite-dimensional submanifold `A` through `x`, a chart `φ` at `x` and
a projection `Q` onto `T = T_xA`, one `t₀` serves every direction `h ∈ T` of norm at most `1`
whose ball of radius `r` in `T` is admissible with the factor `s`: for `0 < t < t₀` there is
`a ∈ A` with `Q(φ(a) − φ(x)) = t h` and `‖φ(a) − φ(x) − t h‖ ≤ ε t`
(`ScRetraction.exists_graph_unif` for the chart sc⁺-retraction). -/
theorem exists_graph_unif_chart {φ : MChart X} (hφ : P.IsChart φ) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {x : X} (hxA : x ∈ A) (hxφ : x ∈ φ.source)
    (Q : φ.model.E 0 →L[ℝ] φ.model.E 0) (hQT : ∀ v, Q v ∈ P.chartTangent hφ A x)
    (hQid : ∀ v ∈ P.chartTangent hφ A x, Q v = v) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ > (0 : ℝ), ∀ h ∈ P.chartTangent hφ A x, ‖h‖ ≤ 1 →
      (∀ h' ∈ P.chartTangent hφ A x, ‖h' - h‖ ≤ r → φ x + s • h' ∈ φ.model.C) →
      ∀ t, 0 < t → t < t₀ → ∃ a ∈ A ∩ φ.source,
        Q (φ a - φ x) = t • h ∧ ‖(φ a - φ x) - t • h‖ ≤ ε * t := by
  set d := hA.data hxA
  have hxV : x ∈ d.V := hA.mem_data_V hxA
  obtain ⟨R, hR, hRp⟩ := exists_plusRetraction hφ d hxA hxV
  obtain ⟨hz, hxt, hT⟩ := chartTangent_eq_range hφ d hR hxA hxV hxφ
  have hzt : φ.model.E.toBase 1 (levelLift φ 1 x) ∈ R.retract := by rw [hz]; exact hxt
  obtain ⟨t₀, ht₀, hgr⟩ := ScRetraction.exists_graph_unif hRp hzt Q
    (fun v => by rw [← hT]; exact hQT v) (fun v hv => hQid v (by rw [hT]; exact hv)) hr hs hε
  refine ⟨t₀, ht₀, fun h hh hh1 hcone τ hτ hτt => ?_⟩
  obtain ⟨a', ha', hQa, hest⟩ := hgr h (by rw [← hT]; exact hh) hh1
    (fun h' hh' hd => by rw [hz]; exact hcone h' (by rw [hT]; exact hh') hd) τ hτ hτt
  rw [hR] at ha'
  obtain ⟨a, ⟨haW, haA⟩, rfl⟩ := ha'
  rw [hz] at hQa hest
  exact ⟨a, ⟨haA, d.toSubData.shrink_subset_source φ haW⟩, hQa, hest⟩

/-- **An admissible direction of norm at most `1/2`, with its cone**: for a smooth
finite-dimensional submanifold `A` through `x` and a chart `φ` at `x` there are `h₁ ∈ T_xA`,
`r, s > 0` with `‖h₁‖ + r ≤ 1/2` and `φ(x) + s h' ∈ C` for all `h' ∈ T_xA` with
`‖h' − h₁‖ ≤ r` (`isGraphChartAt_goodDirections`, rescaled). -/
theorem exists_small_cone {φ : MChart X} (hφ : P.IsChart φ) {A : Set X}
    (hA : P.IsSmoothSubmanifold A) {x : X} (hxA : x ∈ A) (hxφ : x ∈ φ.source) :
    ∃ h₁ ∈ P.chartTangent hφ A x, ∃ r > (0 : ℝ), ∃ s > (0 : ℝ), ‖h₁‖ + r ≤ 1 / 2 ∧
      ∀ h' ∈ P.chartTangent hφ A x, ‖h' - h₁‖ ≤ r → φ x + s • h' ∈ φ.model.C := by
  obtain ⟨N, hN, -⟩ := exists_submodule_chartTangent hφ hA hxA hxφ
  obtain ⟨⟨h, hh, r', hr', hK⟩, -, -⟩ := isGraphChartAt_goodDirections hφ hA hxA hxφ
  obtain ⟨r, hr, s, hs, hcone⟩ := hK h hh (by rw [sub_self, norm_zero]; exact hr')
  have hpos : 0 < ‖h‖ + r + 1 := by positivity
  set c : ℝ := 1 / (2 * (‖h‖ + r + 1)) with hcdef
  have hc : 0 < c := by positivity
  refine ⟨c • h, ?_, c * r, by positivity, s / c, by positivity, ?_, fun h' hh' hd => ?_⟩
  · rw [← hN] at hh ⊢; exact N.smul_mem c hh
  · rw [norm_smul, Real.norm_of_nonneg hc.le]
    have e : c * (‖h‖ + r + 1) = 1 / 2 := by rw [hcdef]; field_simp
    nlinarith
  · have hmem : c⁻¹ • h' ∈ P.chartTangent hφ A x := by
      rw [← hN] at hh' ⊢; exact N.smul_mem _ hh'
    have hd' : ‖c⁻¹ • h' - h‖ ≤ r := by
      have e : c⁻¹ • h' - h = c⁻¹ • (h' - c • h) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), inv_mul_le_iff₀ hc]
      exact hd
    have h2 := hcone _ hmem hd'
    rwa [smul_smul, ← div_eq_mul_inv] at h2

open scoped Classical in
/-- **The good-point input of Lemma 9.3.4 at every point** (Proposition 9.2.8 for oriented
families, 2021 p. 413, with the continuity of orientations; the hypothesis
`HasOrientedGoodPointsAt` of `lemma_9_3_4`): it holds at every point of every M-polyfold, in
every dimension, boundary points included.

The proof is that of `hasOrientedGoodPointsAt_of_hasGraphBallAt`, with one change.  The
direction `h₀ ∈ T = T_xA_{k₀}` off the other tangent spaces is chosen near an admissible
direction `h₁` (`exists_small_cone`), so that every `h` near `h₀` is admissible with one radius
and one factor; the sheets `A_k` tangent to `A_{k₀}` are then graphs over the small ball
`S = {u ∈ T | ‖u − t h₀‖ < τ t}` for `t` below the uniform `t₀` of `exists_graph_unif_chart`.
The level-`1` continuity along the sheets is `hasContinuousLevelOneOn`. -/
theorem hasOrientedGoodPointsAt (x : X) (n : ℕ) : P.HasOrientedGoodPointsAt x n := by
  intro κ _ A d o hd hA hx k₀ W hW hxW
  obtain rfl : d = fun _ => n := funext hd
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  have hGk : ∀ k, P.IsGraphChartAt hφ (goodDirections φ x (P.chartTangent hφ (A k) x)) (A k) x :=
    fun k => isGraphChartAt_goodDirections hφ (hA k).1 (hx k) hxφ
  -- the tangent spaces
  choose N hN hfin using fun k => exists_submodule_chartTangent hφ (hA k).1 (hx k) hxφ
  have hrank : ∀ k, finrank ℝ (N k) = n := fun k =>
    finrank_chartTangent hφ ((hA k).2 x (hx k)) (hA k).1 hxφ (hN k)
  set C : κ → Prop := fun k =>
    P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x with hCdef
  have hC₀ : C k₀ := rfl
  have hCN : ∀ k, C k ↔ N k = N k₀ := fun k => by
    change P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x ↔ _
    rw [← chartTangent_eq_iff hφ hxφ, ← hN k, ← hN k₀, SetLike.coe_set_eq]
  set N₀ := N k₀ with hN₀def
  have : FiniteDimensional ℝ N₀ := hfin k₀
  have hTC : ∀ k, C k → P.chartTangent hφ (A k) x = (N₀ : Set (φ.model.E 0)) := fun k hk => by
    rw [← hN k, (hCN k).1 hk]
  -- the projection `Q` onto `T`
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional N₀
  set Q : φ.model.E 0 →L[ℝ] φ.model.E 0 := N₀.subtypeL.comp Q' with hQdef
  have hQN : ∀ v, Q v ∈ N₀ := fun v => (Q' v).2
  have hQid : ∀ v ∈ N₀, Q v = v := fun v hv => congrArg Subtype.val (hQ' ⟨v, hv⟩)
  set η : ℝ := 1 / (2 * (‖Q‖ + 1)) with hηdef
  have hη : 0 < η := by positivity
  -- the direction `h₀` and the distances `ρ k` to the other tangent spaces
  have hnle : ∀ k, ¬ C k → ¬ N₀ ≤ N k := fun k hk hle => by
    have := hfin k
    exact hk ((hCN k).2 (Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, hrank])).symm)
  have hclosed : ∀ k, IsClosed (N k : Set (φ.model.E 0)) := fun k => by
    have := hfin k
    exact Submodule.closed_of_finiteDimensional _
  -- an admissible direction `h₁` of `T` (the cone of `C` at `φ(x)`), and `h₀` near it
  obtain ⟨h₁, hh₁, r₁, hr₁, s₁, hs₁, hh₁r, hcone₁⟩ := exists_small_cone hφ (hA k₀).1 (hx k₀) hxφ
  rw [hTC k₀ hC₀] at hh₁ hcone₁
  obtain ⟨h₀, hh₀N, hh₀h₁, hh₀S⟩ := exists_mem_ball_forall_not_mem (N := N₀) (ι := {k // ¬ C k})
    (fun k => N k.1) (fun k => hclosed k.1) (fun k => hnle k.1 k.2) (SetLike.mem_coe.1 hh₁)
    (half_pos hr₁)
  have hh₀half : ‖h₀‖ ≤ 1 / 2 := by
    calc ‖h₀‖ = ‖(h₀ - h₁) + h₁‖ := by rw [sub_add_cancel]
      _ ≤ ‖h₀ - h₁‖ + ‖h₁‖ := norm_add_le _ _
      _ ≤ 1 / 2 := by linarith
  have hcone₀ : ∀ h' ∈ N₀, ‖h' - h₀‖ ≤ r₁ / 2 → φ x + s₁ • h' ∈ φ.model.C := fun h' hh' hd =>
    hcone₁ h' hh' (by
      calc ‖h' - h₁‖ = ‖(h' - h₀) + (h₀ - h₁)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖h' - h₀‖ + ‖h₀ - h₁‖ := norm_add_le _ _
        _ ≤ r₁ := by linarith)
  have hrad : ∀ k, ¬ C k → ∃ ρ > 0, ∀ v ∈ N k, ρ ≤ ‖h₀ - v‖ := fun k hk => by
    have hmem : h₀ ∈ (N k : Set (φ.model.E 0))ᶜ := hh₀S ⟨k, hk⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hclosed k).isOpen_compl h₀ hmem
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hv
  choose! ρ hρ hρv using hrad
  have hρev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 ∧ ε ≤ r₁ / 2 ∧ ∀ k, ¬ C k → ε ≤ ρ k := by
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_
      (Filter.eventually_all.2 fun k => ?_))
    · exact ((eventually_lt_nhds one_pos).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    · exact ((eventually_lt_nhds (half_pos hr₁)).mono fun _ h => h.le).filter_mono
        nhdsWithin_le_nhds
    · by_cases hk : ¬ C k
      · exact ((eventually_lt_nhds (hρ k hk)).mono fun _ h _ => h.le).filter_mono
          nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
  obtain ⟨ρ₀, ⟨hρ₀1, hρ₀r, hρ₀ρ⟩, hρ₀⟩ := (hρev.and self_mem_nhdsWithin).exists
  have hρ₀ : (0 : ℝ) < ρ₀ := hρ₀
  -- the constants
  set H : ℝ := ‖h₀‖ + 1 with hHdef
  have hH : 0 < H := by positivity
  set τ : ℝ := ρ₀ / 3 with hτdef
  have hτ13 : τ ≤ 1 / 3 := by rw [hτdef]; linarith
  have hτr : τ ≤ r₁ / 6 := by rw [hτdef]; linarith
  set εg : ℝ := min 1 (ρ₀ / (3 * H)) with hεgdef
  have hεg : 0 < εg := lt_min one_pos (by positivity)
  have hεg1 : εg ≤ 1 := min_le_left _ _
  have hεgH : εg * H ≤ ρ₀ / 3 := by
    calc εg * H ≤ ρ₀ / (3 * H) * H := mul_le_mul_of_nonneg_right (min_le_right _ _) hH.le
      _ = ρ₀ / 3 := by field_simp
  set ε₁ : ℝ := ρ₀ / (6 * H) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  -- the graph maps over the admissible directions near `h₀`, uniformly; the approximation radii
  have hgr : ∀ k, C k → ∃ t₀ > (0 : ℝ), ∀ h ∈ N₀, ‖h‖ ≤ 1 →
      (∀ h' ∈ N₀, ‖h' - h‖ ≤ r₁ / 4 → φ x + s₁ • h' ∈ φ.model.C) →
      ∀ t, 0 < t → t < t₀ → ∃ a ∈ A k ∩ φ.source,
        Q (φ a - φ x) = t • h ∧ ‖(φ a - φ x) - t • h‖ ≤ εg * H * t := fun k hk => by
    obtain ⟨t₀, ht₀, hgk⟩ := exists_graph_unif_chart hφ (hA k).1 (hx k) hxφ Q
      (fun v => by rw [hTC k hk]; exact hQN v)
      (fun v hv => hQid v (by rw [hTC k hk] at hv; exact hv)) (by positivity : (0 : ℝ) < r₁ / 4)
      hs₁ (by positivity : (0 : ℝ) < εg * H)
    exact ⟨t₀, ht₀, fun h hh hh1 hc t ht htt => hgk h (by rw [hTC k hk]; exact hh) hh1
      (fun h' hh' hd => hc h' (by rw [hTC k hk] at hh'; exact hh') hd) t ht htt⟩
  choose! t₀ ht₀ hgr using hgr
  choose δ₁ hδ₁ happ₁ using fun k => (hGk k).approx η hη
  choose δ₂ hδ₂ happ₂ using fun k => (hGk k).approx ε₁ hε₁
  have hlip : ∀ k, C k → ∀ a ∈ A k ∩ φ.source, ∀ b ∈ A k ∩ φ.source,
      ‖φ a - φ x‖ < δ₁ k → ‖φ b - φ x‖ < δ₁ k →
        ‖φ a - φ b‖ ≤ 2 * ‖Q (φ a - φ x) - Q (φ b - φ x)‖ := by
    intro k hk a ha b hb hax hbx
    obtain ⟨v, hv, hvab⟩ := happ₁ k a ha b hb hax hbx
    rw [hTC k hk] at hv
    have h := norm_le_two_mul_of_approx hQid hv hvab
    rwa [show Q (φ a - φ b) = Q (φ a - φ x) - Q (φ b - φ x) by
      rw [← map_sub]; congr 1; abel] at h
  -- the orientation neighbourhoods
  have hor : ∀ k k', ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ (0 < n → C k → C k' →
      ∀ z ∈ A k ∩ A k' ∩ O, P.submanifoldTangent (A k) z = P.submanifoldTangent (A k') z →
        ((o k).tangent z = (o k').tangent z ↔ (o k).tangent x = (o k').tangent x)) := by
    intro k k'
    by_cases h : 0 < n ∧ C k ∧ C k'
    · obtain ⟨O, hO, hxO, hOp⟩ := SubmanifoldOrientation.exists_isOpen_tangent_eq_iff h.1
        (o k) (o k') (hasContinuousLevelOneOn (hA k').1) (hx k) (hx k') (h.2.1.trans h.2.2.symm)
      exact ⟨O, hO, hxO, fun _ _ _ => hOp⟩
    · exact ⟨univ, isOpen_univ, mem_univ x, fun hn hk hk' => (h ⟨hn, hk, hk'⟩).elim⟩
  choose O hO hxO hOp using hor
  set W₁ : Set X := W ∩ ⋂ k, ⋂ k', O k k' with hW₁def
  have hW₁ : IsOpen W₁ := hW.inter (isOpen_iInter_of_finite fun k =>
    isOpen_iInter_of_finite fun k' => hO k k')
  have hxW₁ : x ∈ W₁ := ⟨hxW, mem_iInter.2 fun k => mem_iInter.2 fun k' => hxO k k'⟩
  obtain ⟨ρW, hρW, hρWsub⟩ := exists_pos_forall_mem_of_mem_nhds hxφ (hW₁.mem_nhds hxW₁)
  -- the radius `R` and the parameter `t`
  have hRev : ∀ᶠ R in 𝓝[>] (0 : ℝ), (∀ k, C k → R < 2 * H * t₀ k) ∧ (∀ k, R < δ₁ k) ∧
      (∀ k, R < δ₂ k) ∧ R < ρW := by
    refine (Filter.eventually_all.2 fun k => ?_).and ((Filter.eventually_all.2 fun k => ?_).and
      ((Filter.eventually_all.2 fun k => ?_).and ?_))
    · by_cases hk : C k
      · exact ((eventually_lt_nhds (mul_pos (mul_pos two_pos hH) (ht₀ k hk))).mono
          fun _ h _ => h).filter_mono nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
    · exact (eventually_lt_nhds (hδ₁ k)).filter_mono nhdsWithin_le_nhds
    · exact (eventually_lt_nhds (hδ₂ k)).filter_mono nhdsWithin_le_nhds
    · exact (eventually_lt_nhds hρW).filter_mono nhdsWithin_le_nhds
  obtain ⟨R, ⟨hRr, hRδ₁, hRδ₂, hRW⟩, hR0⟩ := (hRev.and self_mem_nhdsWithin).exists
  have hR0 : (0 : ℝ) < R := hR0
  set t : ℝ := R / (2 * H) with htdef
  have ht : 0 < t := by positivity
  have htH : 2 * (t * H) = R := by rw [htdef]; field_simp
  have htt₀ : ∀ k, C k → t < t₀ k := fun k hk => by
    rw [htdef, div_lt_iff₀ (by positivity)]; linarith [hRr k hk]
  -- the parameter set `S`
  set S : Set N₀ := {u | ‖(u : φ.model.E 0) - t • h₀‖ < τ * t} with hSdef
  have hSo : IsOpen S := isOpen_lt ((continuous_subtype_val.sub continuous_const).norm)
    continuous_const
  have hSnorm : ∀ u ∈ S, ‖(u : φ.model.E 0)‖ < t * H := fun u hu => by
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    have hτ1 : τ ≤ 1 := by rw [hτdef]; linarith
    calc ‖(u : φ.model.E 0)‖ = ‖((u : φ.model.E 0) - t • h₀) + t • h₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖(u : φ.model.E 0) - t • h₀‖ + ‖t • h₀‖ := norm_add_le _ _
      _ < τ * t + t * ‖h₀‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]; linarith
      _ ≤ t * H := by rw [hHdef]; nlinarith
  have hg : ∀ k, C k → ∀ u : N₀, u ∈ S → ∃ a ∈ A k ∩ φ.source,
      Q (φ a - φ x) = u ∧ ‖(φ a - φ x) - u‖ ≤ εg * (t * H) := fun k hk u hu => by
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    set h : φ.model.E 0 := t⁻¹ • (u : φ.model.E 0) with hhdef
    have hut : t • h = u := by rw [hhdef, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hhh₀ : ‖h - h₀‖ < τ := by
      have e : h - h₀ = t⁻¹ • ((u : φ.model.E 0) - t • h₀) := by
        rw [hhdef, smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht]
      linarith
    have hhN : h ∈ N₀ := N₀.smul_mem _ u.2
    have hh1 : ‖h‖ ≤ 1 := by
      calc ‖h‖ = ‖(h - h₀) + h₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖h - h₀‖ + ‖h₀‖ := norm_add_le _ _
        _ ≤ 1 := by linarith
    have hc : ∀ h' ∈ N₀, ‖h' - h‖ ≤ r₁ / 4 → φ x + s₁ • h' ∈ φ.model.C := fun h' hh' hd =>
      hcone₀ h' hh' (by
        calc ‖h' - h₀‖ = ‖(h' - h) + (h - h₀)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖h' - h‖ + ‖h - h₀‖ := norm_add_le _ _
          _ ≤ r₁ / 2 := by linarith)
    obtain ⟨a, ha, hQa, hest⟩ := hgr k hk h hhN hh1 hc t ht (htt₀ k hk)
    rw [hut] at hQa hest
    exact ⟨a, ha, hQa, hest.trans_eq (by ring)⟩
  have : Nonempty X := ⟨x⟩
  choose! g hgA hgQ hgest using hg
  have hgR : ∀ k, C k → ∀ u ∈ S, ‖φ (g k u) - φ x‖ < R := fun k hk u hu => by
    have h1 := hgest k hk u hu
    have h2 := hSnorm u hu
    have h3 : εg * (t * H) ≤ t * H := mul_le_of_le_one_left (by positivity) hεg1
    calc ‖φ (g k u) - φ x‖ = ‖((φ (g k u) - φ x) - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖(φ (g k u) - φ x) - u‖ + ‖(u : φ.model.E 0)‖ := norm_add_le _ _
      _ < R := by linarith
  -- uniqueness of the graph point
  have huniq : ∀ k, C k → ∀ u ∈ S, ∀ a ∈ A k ∩ φ.source, ‖φ a - φ x‖ < R →
      Q (φ a - φ x) = u → a = g k u := by
    intro k hk u hu a ha haR hQa
    have h := hlip k hk a ha (g k u) (hgA k hk u hu) (haR.trans (hRδ₁ k))
      ((hgR k hk u hu).trans (hRδ₁ k))
    rw [hQa, hgQ k hk u hu, sub_self, norm_zero, mul_zero] at h
    exact φ.toPartialEquiv.injOn ha.2 (hgA k hk u hu).2 (sub_eq_zero.1 (norm_le_zero_iff.1 h))
  -- the graph points over `S` miss the sheets of the other classes
  have havoid : ∀ j, C j → ∀ u ∈ S, ∀ k, ¬ C k → g j u ∉ A k := by
    intro j hj u hu k hk hjk
    set a := g j u with hadef
    have hxA : x ∈ A k ∩ φ.source := ⟨hx k, hxφ⟩
    obtain ⟨w, hw, hwa⟩ := happ₂ k a ⟨hjk, (hgA j hj u hu).2⟩ x hxA
      ((hgR j hj u hu).trans (hRδ₂ k)) (by rw [sub_self, norm_zero]; exact hδ₂ k)
    rw [← hN k] at hw
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    have h1 : ‖(φ a - φ x) - w‖ ≤ ε₁ * (2 * (t * H)) := by
      calc ‖(φ a - φ x) - w‖ ≤ ε₁ * ‖φ a - φ x‖ := hwa
        _ ≤ ε₁ * (2 * (t * H)) :=
            mul_le_mul_of_nonneg_left (by rw [htH]; exact (hgR j hj u hu).le) hε₁.le
    have h1' : ε₁ * (2 * (t * H)) = ρ₀ / 3 * t := by rw [hε₁def]; field_simp; ring
    have h2 : ‖(φ a - φ x) - u‖ ≤ ρ₀ / 3 * t := by
      calc ‖(φ a - φ x) - u‖ ≤ εg * (t * H) := hgest j hj u hu
        _ = εg * H * t := by ring
        _ ≤ ρ₀ / 3 * t := mul_le_mul_of_nonneg_right hεgH ht.le
    have h3 : ‖t • h₀ - w‖ < ρ₀ * t := by
      calc ‖t • h₀ - w‖ = ‖(t • h₀ - u) + (u - (φ a - φ x)) + ((φ a - φ x) - w)‖ := by
            congr 1; abel
        _ ≤ ‖t • h₀ - u‖ + ‖(u : φ.model.E 0) - (φ a - φ x)‖ + ‖(φ a - φ x) - w‖ :=
            norm_add₃_le
        _ < τ * t + ρ₀ / 3 * t + ρ₀ / 3 * t := by
            have e1 : ‖t • h₀ - u‖ = ‖(u : φ.model.E 0) - t • h₀‖ := norm_sub_rev _ _
            have e2 : ‖(u : φ.model.E 0) - (φ a - φ x)‖ = ‖(φ a - φ x) - u‖ := norm_sub_rev _ _
            linarith
        _ = ρ₀ * t := by rw [hτdef]; ring
    have hw' : t⁻¹ • w ∈ N k := (N k).smul_mem _ hw
    have h4 := hρv k hk _ hw'
    have h5 : ‖h₀ - t⁻¹ • w‖ = t⁻¹ * ‖t • h₀ - w‖ := by
      have : h₀ - t⁻¹ • w = t⁻¹ • (t • h₀ - w) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
    have h6 : t⁻¹ * ‖t • h₀ - w‖ < ρ₀ := by rw [inv_mul_lt_iff₀ ht]; linarith
    linarith [hρ₀ρ k hk]
  -- continuity of the graph maps on `S`
  have hGc : ∀ k, C k → ContinuousOn (fun u => φ (g k u)) S := by
    intro k hk
    refine Metric.continuousOn_iff.2 fun u hu ε hε => ⟨ε / 2, by positivity, fun u' hu' hd => ?_⟩
    have h := hlip k hk (g k u') (hgA k hk u' hu') (g k u) (hgA k hk u hu)
      ((hgR k hk u' hu').trans (hRδ₁ k)) ((hgR k hk u hu).trans (hRδ₁ k))
    rw [hgQ k hk u' hu', hgQ k hk u hu] at h
    rw [Subtype.dist_eq, dist_eq_norm] at hd
    rw [dist_eq_norm]
    linarith
  -- the shrinking step
  let ι := {p : κ × κ // C p.1 ∧ C p.2}
  let M : ι → Set N₀ := fun p => {u | φ (g p.1.1 u) = φ (g p.1.2 u)}
  have hMo : ∀ p : ι, IsOpen (S \ M p) := fun p => by
    have hc := (hGc p.1.1 p.2.1).sub (hGc p.1.2 p.2.2)
    have h := hc.isOpen_inter_preimage hSo (isOpen_compl_singleton (x := (0 : φ.model.E 0)))
    convert h using 1
    ext u
    simp only [M, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff, Pi.sub_apply, sub_eq_zero]
  have hS0 : (⟨t • h₀, N₀.smul_mem t hh₀N⟩ : N₀) ∈ S := by
    change ‖t • h₀ - t • h₀‖ < τ * t
    rw [sub_self, norm_zero]; positivity
  obtain ⟨S', hS'S, hS'o, ⟨v, hvS', -⟩, hS'M⟩ :=
    exists_isOpen_subset_inter_eq_empty_or_subset M hMo hSo subset_rfl
      (Y := univ) ⟨_, hS0, mem_univ _⟩
  have hvS : v ∈ S := hS'S hvS'
  -- the points `y_e`
  set pts : Finset X := (Finset.univ.filter C).image (fun k => g k v) with hptsdef
  have hmem : ∀ k, C k → g k v ∈ pts := fun k hk =>
    Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩, rfl⟩
  set enum := pts.equivFin with henum
  refine ⟨pts.card, fun k => if hk : C k then enum ⟨g k v, hmem k hk⟩
    else enum ⟨g k₀ v, hmem k₀ hC₀⟩, fun e => (enum.symm e : X), fun e => ?_⟩
  obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 (enum.symm e).2
  have hjC : C j := (Finset.mem_filter.1 hj).2
  set ye : X := (enum.symm e : X) with hyedef
  have hyeA : ye ∈ A j ∩ φ.source := hjv ▸ hgA j hjC v hvS
  have hyeQ : Q (φ ye - φ x) = v := hjv ▸ hgQ j hjC v hvS
  have hyeR : ‖φ ye - φ x‖ < R := hjv ▸ hgR j hjC v hvS
  have hyeW₁ : ye ∈ W₁ := hρWsub ye hyeA.2 (hyeR.trans hRW)
  -- the sheets through `y_e`
  have hsheet : ∀ k, ye ∈ A k ↔ C k ∧ (if hk : C k then enum ⟨g k v, hmem k hk⟩
      else enum ⟨g k₀ v, hmem k₀ hC₀⟩) = e := by
    intro k
    constructor
    · intro hk
      by_cases hCk : C k
      · have hyk : ye = g k v := huniq k hCk v hvS ye ⟨hk, hyeA.2⟩ hyeR hyeQ
        refine ⟨hCk, ?_⟩
        rw [dif_pos hCk]
        have : (⟨g k v, hmem k hCk⟩ : pts) = enum.symm e := Subtype.ext hyk.symm
        rw [this, Equiv.apply_symm_apply]
      · exact absurd (hjv ▸ hk) (havoid j hjC v hvS k hCk)
    · rintro ⟨hCk, hbk⟩
      rw [dif_pos hCk] at hbk
      have h1 : (⟨g k v, hmem k hCk⟩ : pts) = enum.symm e := by
        rw [← hbk, Equiv.symm_apply_apply]
      have h2 : g k v = ye := congrArg Subtype.val h1
      rw [← h2]
      exact (hgA k hCk v hvS).1
  have hsame : ∀ k, ye ∈ A k → C k ∧ g k v = ye := fun k hk =>
    have hCk := ((hsheet k).1 hk).1
    ⟨hCk, (huniq k hCk v hvS ye ⟨hk, hyeA.2⟩ hyeR hyeQ).symm⟩
  -- the neighbourhood `V` of `y_e`
  obtain ⟨G, hGo, hGS'⟩ := isOpen_induced_iff.1 hS'o
  set G' : Set (φ.model.E 0) := {w | ‖w - φ x‖ < R ∧ Q (w - φ x) ∈ G} with hG'def
  have hG'o : IsOpen G' := (isOpen_lt (continuous_id.sub continuous_const).norm
    continuous_const).inter (hGo.preimage (Q.continuous.comp (continuous_id.sub continuous_const)))
  set V : Set X := φ.source ∩ φ ⁻¹' G' with hVdef
  have hVo : IsOpen V := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hG'o
  have hmemS' : ∀ u : N₀, (u : φ.model.E 0) ∈ G ↔ u ∈ S' := fun u => by
    rw [← hGS']; rfl
  have hyeV : ye ∈ V := ⟨hyeA.2, hyeR, by rw [hyeQ]; exact (hmemS' v).2 hvS'⟩
  have hcoinc : ∀ k k', ye ∈ A k → ye ∈ A k' → V ∩ A k ⊆ A k' := by
    intro k k' hk hk' a ⟨haV, hak⟩
    obtain ⟨hCk, hgk⟩ := hsame k hk
    obtain ⟨hCk', hgk'⟩ := hsame k' hk'
    have hM : S' ∩ univ ⊆ M ⟨(k, k'), hCk, hCk'⟩ := by
      rcases hS'M ⟨(k, k'), hCk, hCk'⟩ with h | h
      · exact absurd h (Set.nonempty_iff_ne_empty.1 ⟨v, ⟨hvS', mem_univ _⟩,
          show φ (g k v) = φ (g k' v) by rw [hgk, hgk']⟩)
      · exact h
    set u : N₀ := ⟨Q (φ a - φ x), hQN _⟩
    have huS' : u ∈ S' := (hmemS' u).1 haV.2.2
    have huS : u ∈ S := hS'S huS'
    have ha : a = g k u := huniq k hCk u huS a ⟨hak, haV.1⟩ haV.2.1 rfl
    have hkk' : φ (g k u) = φ (g k' u) := hM ⟨huS', mem_univ _⟩
    have hgg : g k u = g k' u :=
      φ.toPartialEquiv.injOn (hgA k hCk u huS).2 (hgA k' hCk' u huS).2 hkk'
    rw [ha, hgg]
    exact (hgA k' hCk' u huS).1
  have hVeq : ∀ k k', ye ∈ A k → ye ∈ A k' → V ∩ A k = V ∩ A k' := fun k k' hk hk' =>
    Subset.antisymm (fun a ha => ⟨ha.1, hcoinc k k' hk hk' ha⟩)
      (fun a ha => ⟨ha.1, hcoinc k' k hk' hk ha⟩)
  refine ⟨hyeW₁.1, hsheet, ⟨V, hVo, hyeV, hVeq⟩, fun k k' hk hk' => ?_⟩
  -- the relative orientations
  by_cases hn : n = 0
  · have hv0 : (v : φ.model.E 0) = 0 := by
      have : Subsingleton N₀ := Module.finrank_zero_iff.1 ((hrank k₀).trans hn)
      rw [Subsingleton.elim v 0]; rfl
    have hye : ye = x := by
      have h2 := huniq j hjC v hvS x ⟨hx j, hxφ⟩ (by rw [sub_self, norm_zero]; exact hR0)
        (by rw [sub_self, map_zero, hv0])
      rw [← hjv]
      exact h2.symm
    change (o k).tangent ye = (o k').tangent ye ↔ _
    rw [hye]
  · have hTye : P.submanifoldTangent (A k) ye = P.submanifoldTangent (A k') ye := by
      rw [← submanifoldTangent_inter_isOpen hVo hyeV, ← submanifoldTangent_inter_isOpen hVo hyeV
        (A := A k'), inter_comm, hVeq k k' hk hk', inter_comm]
    exact hOp k k' (Nat.pos_of_ne_zero hn) (hsame k hk).1 (hsame k' hk').1 ye
      ⟨⟨hk, hk'⟩, mem_iInter.1 (mem_iInter.1 hyeW₁.2 k) k'⟩ hTye

/-- **Satisfiability check**: the good-point input holds at the point of `ℝ⁰`
(`hasOrientedGoodPointsAt_rn_zero`), as an instance of `hasOrientedGoodPointsAt`. -/
example (x : Fin 0 → ℝ) (n : ℕ) : (rnPolyfold 0).HasOrientedGoodPointsAt x n :=
  hasOrientedGoodPointsAt x n

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
variable {Θ : Obj → ℚ}

/-- **2021 Lemma 9.3.4, p. 423 (2017: Lemma 9.10)**: for a branched ep⁺-subgroupoid `Θ`, two
`n`-dimensional orientations which agree at the good points agree on `X_∞`.  No hypothesis on
the boundary: the good-point input holds at every point (`MPolyfold.hasOrientedGoodPointsAt`). -/
theorem lemma_9_3_4_general (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂) (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  lemma_9_3_4 hΘ h₁ h₂ (fun x _ => MPolyfold.hasOrientedGoodPointsAt x n) hagree

end EpGroupoid

end Polyfold
