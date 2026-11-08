import Polyfold.Chapter9.TangentSlicesBasic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.2: **Lemmas 9.2.9–9.2.11** (pp. 414–417; 2017: Lemmas 9.6–9.8) and
**Proposition 9.2.8** (p. 413; 2017: Proposition 9.3) for the M-polyfold `ℝᵐ`, and the
resulting cases of **Theorem 9.2.1** (p. 409; 2017: Theorem 9.1, p. 298).

# The graph representation in `ℝᵐ`

## What is formalized

* `exists_mem_graph_of_hasStrictFDerivAt`: a retraction strictly differentiable at a fixed
  point `x`, with derivative the identity on a finite-dimensional `N`, is near `x` a graph over
  `N` for any projection `Q` onto `N` (inverse function theorem on `N`), with the estimate of
  Lemma 9.2.10 (`DB(0) = 0`).
* `rn_exists_retraction` (a smooth submanifold of `ℝᵐ` near a point: a `C^∞` retraction `s` of
  an open `W`, with chart tangent space `range Ds(x)`), `isGraphChartAt_rn`,
  `hasGraphChartsAt_rn` (the graph representation at every point, in every dimension, with
  `K = ℝᵐ`) and `hasTangentSlicesAt_rn` (Proposition 9.2.8 in slice form).
* Theorem 9.2.1: `hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt` and
  `..._of_proposition_9_1_12_of_hasGraphChartsAt` (general object M-polyfold, graph
  representation as hypothesis); for object M-polyfold `ℝᵐ` without it:
  `LocalBranchingStructure.tangentSum_eq_of_isOfDim_rn`, `hasIndependentTangentSums_of_isOfDim_rn`,
  `hasIndependentTangentSums_of_proposition_9_1_12_rn`.
* A nontrivial instance: the two local branching structures of Remark 9.1.3 (b) (p. 402), which
  differ near the origin, have the same tangent sums at every point
  (`Remark913Hyp.tangentSum_structureβ_eq_structureγ`).

## The choices made

* In `ℝᵐ` the partial quadrant is the whole space, so Lemma 9.2.9 is trivial (`K = ℝᵐ`) and
  the cones of Lemmas 9.2.10, 9.2.11 can be replaced by full neighbourhoods in `T_xA`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Module
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### A graph lemma in a normed space -/

section GraphLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The graph representation of a `C¹` retraction over its tangent space**: let `s` be strictly
differentiable at a fixed point `x` with derivative `D`, `N` a finite-dimensional subspace on which
`D` is the identity, and `Q` a projection onto `N`.  Then every small `u ∈ N` is
`u = Q(s(x + c) − x)` for a small `c ∈ N`, with `‖s(x + c) − x − u‖ ≤ ε ‖u‖` (inverse function
theorem for `c ↦ Q(s(x + c) − x)` on `N`, whose derivative at `0` is the identity). -/
theorem exists_mem_graph_of_hasStrictFDerivAt {s : E → E} {D : E →L[ℝ] E} {x : E}
    (hs : HasStrictFDerivAt s D x) (hsx : s x = x) {N : Submodule ℝ E} [FiniteDimensional ℝ N]
    (hDN : ∀ c ∈ N, D c = c) {Q : E →L[ℝ] E} (hQN : ∀ v, Q v ∈ N) (hQid : ∀ v ∈ N, Q v = v)
    {ε : ℝ} (hε : 0 < ε) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r > 0, ∀ u ∈ N, ‖u‖ < r → ∃ c ∈ N, ‖c‖ < ρ ∧ Q (s (x + c) - x) = u ∧
      ‖(s (x + c) - x) - u‖ ≤ ε * ‖u‖ := by
  set q := ‖Q‖ + 1 with hqdef
  have hq : 0 < q := by positivity
  set ε' := min (1 / (2 * q)) (ε / (4 * q)) with hε'def
  have hε' : 0 < ε' := lt_min (by positivity) (by positivity)
  have hqε1 : q * ε' ≤ 1 / 2 := by
    calc q * ε' ≤ q * (1 / (2 * q)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hq.le
      _ = 1 / 2 := by field_simp
  have hqε2 : q * ε' ≤ ε / 4 := by
    calc q * ε' ≤ q * (ε / (4 * q)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hq.le
      _ = ε / 4 := by field_simp
  obtain ⟨δ, hδ, hδest⟩ := Metric.eventually_nhds_iff.1 (hs.hasFDerivAt.isLittleO.def hε')
  -- the map `Φ : N → N`
  let Φ : N → N := fun c => ⟨Q (s (x + c) - x), hQN _⟩
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ N : N ≃L[ℝ] N) : N →L[ℝ] N) 0 := by
    have h1 : HasStrictFDerivAt (fun c : N => x + (c : E)) N.subtypeL 0 :=
      N.subtypeL.hasStrictFDerivAt.const_add x
    have h2 : HasStrictFDerivAt s D (x + ((0 : N) : E)) := by
      rw [Submodule.coe_zero, add_zero]; exact hs
    have h3 := (h2.comp (0 : N) h1).sub_const x
    have h4 := (Q.codRestrict N hQN).hasStrictFDerivAt.comp (0 : N) h3
    have h5 : HasStrictFDerivAt Φ ((Q.codRestrict N hQN).comp (D.comp N.subtypeL)) 0 := h4
    refine h5.congr_fderiv ?_
    ext c
    simp [hDN c c.2, hQid c c.2]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hΦ0 : Φ 0 = 0 := by
    ext
    simp [Φ, hsx]
  rw [hΦ0] at hmap
  set U : Set N := {c | ‖(c : E)‖ < min δ ρ} with hUdef
  have hU : U ∈ 𝓝 (0 : N) := by
    have : IsOpen U := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
    refine this.mem_nhds ?_
    simp only [hUdef, mem_ofPred_eq, Submodule.coe_zero, norm_zero]
    exact lt_min hδ hρ
  have hΦU : Φ '' U ∈ 𝓝 (0 : N) := hmap ▸ image_mem_map hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hΦU
  refine ⟨r, hr, fun u hu hur => ?_⟩
  obtain ⟨c, hcU, hΦc⟩ := hball (show (⟨u, hu⟩ : N) ∈ Metric.ball 0 r by
    rw [Metric.mem_ball, dist_zero_right]; exact hur)
  have hQc : Q (s (x + c) - x) = u := congrArg Subtype.val hΦc
  have hcU' : ‖(c : E)‖ < min δ ρ := hcU
  have hcδ : ‖(c : E)‖ < δ := lt_of_lt_of_le hcU' (min_le_left _ _)
  have hcρ : ‖(c : E)‖ < ρ := lt_of_lt_of_le hcU' (min_le_right _ _)
  set e := s (x + c) - x - c with hedef
  have he : ‖e‖ ≤ ε' * ‖(c : E)‖ := by
    have := hδest (y := x + c) (by rw [dist_eq_norm, add_sub_cancel_left]; exact hcδ)
    rwa [hsx, add_sub_cancel_left, hDN c c.2] at this
  have hQe : ‖Q e‖ ≤ q * ε' * ‖(c : E)‖ := by
    calc ‖Q e‖ ≤ ‖Q‖ * ‖e‖ := Q.le_opNorm e
      _ ≤ q * ‖e‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ q * (ε' * ‖(c : E)‖) := mul_le_mul_of_nonneg_left he hq.le
      _ = q * ε' * ‖(c : E)‖ := by ring
  have hsplit : s (x + c) - x = c + e := by rw [hedef]; abel
  have hu' : u = c + Q e := by rw [← hQc, hsplit, map_add, hQid c c.2]
  have hcu : ‖(c : E)‖ ≤ 2 * ‖u‖ := by
    have : ‖(c : E)‖ ≤ ‖u‖ + ‖Q e‖ := by
      calc ‖(c : E)‖ = ‖u - Q e‖ := by rw [hu', add_sub_cancel_right]
        _ ≤ ‖u‖ + ‖Q e‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (c : E)]
  refine ⟨c, c.2, hcρ, hQc, ?_⟩
  have hdiff : (s (x + c) - x) - u = e - Q e := by rw [hsplit, hu']; abel
  rw [hdiff]
  calc ‖e - Q e‖ ≤ ‖e‖ + ‖Q e‖ := norm_sub_le _ _
    _ ≤ ε' * ‖(c : E)‖ + q * ε' * ‖(c : E)‖ := add_le_add he hQe
    _ ≤ q * ε' * ‖(c : E)‖ + q * ε' * ‖(c : E)‖ := by
        have : ε' ≤ q * ε' :=
          le_mul_of_one_le_left hε'.le (by rw [hqdef]; linarith [norm_nonneg Q])
        nlinarith [norm_nonneg (c : E)]
    _ = 2 * (q * ε') * ‖(c : E)‖ := by ring
    _ ≤ 2 * (ε / 4) * (2 * ‖u‖) := by
        apply mul_le_mul (by linarith) hcu (norm_nonneg _) (by positivity)
    _ = ε * ‖u‖ := by ring

end GraphLemma

/-! ### The graph representation in `ℝᵐ` -/

namespace MPolyfold

variable {m : ℕ}

/-- The chart `rnChart m 0` is the identity. -/
theorem rnChart_zero_apply' (r : Fin m → ℝ) : rnChart m 0 r = r := by
  rw [rnChart_apply, sub_zero]

/-- Images under the chart `rnChart m 0`. -/
theorem rnChart_zero_image (S : Set (Fin m → ℝ)) : rnChart m 0 '' S = S :=
  (image_congr fun r _ => rnChart_zero_apply' r).trans (image_id _)

/-- **A smooth submanifold of `ℝᵐ` near a point** (Definition 4.13 in the chart `id`): there are
an open `W ∋ x` and a `C^∞` retraction `s : W → W` with `s(W) = W ∩ A`, and the chart image of
`T_xA` is the range of `Ds(x)` (Remark 4.14). -/
theorem rn_exists_retraction {A : Set (Fin m → ℝ)} (hA : (rnPolyfold m).IsSmoothSubmanifold A)
    {x : Fin m → ℝ} (hx : x ∈ A) :
    ∃ W : Set (Fin m → ℝ), IsOpen W ∧ x ∈ W ∧ ∃ s : (Fin m → ℝ) → Fin m → ℝ,
      ContDiffOn ℝ ∞ s W ∧ MapsTo s W W ∧ (∀ y ∈ W, s (s y) = s y) ∧ s '' W = W ∩ A ∧
      (rnPolyfold m).chartTangent (isChart_rnChart 0) A x = range (fderiv ℝ s x) := by
  obtain ⟨d, hxV⟩ := isSmoothSubmanifold_iff.1 hA x hx
  have hφ : (rnPolyfold m).IsChart (rnChart m 0) := isChart_rnChart 0
  set W := d.toSubData.shrink (rnChart m 0) with hWdef
  have hWo : IsOpen W := d.toSubData.isOpen_shrink _
  have hxW : x ∈ W := d.toSubData.mem_shrink _ hx hxV (mem_univ x)
  have hmaps : MapsTo d.s W W := d.toSubData.mapsTo_shrink _
  have hU : IsRelOpenInQuadrant (rnSc m) univ W :=
    ⟨isPartialQuadrant_univ _, W, hWo, (inter_univ _).symm⟩
  have hsm := d.isScPlusRetractionOn.isScSmoothOn.smooth (rnChart m 0) (rnChart m 0) hφ hφ W hWo
    (fun y hy => ⟨d.toSubData.shrink_subset_V _ hy, mem_univ y⟩) (fun y _ => mem_univ _)
  have hR : (ScRetraction.id hU).retract = (rnChart m 0) '' W := by
    rw [rnChart_zero_image]; exact image_id W
  have h1 := hsm.comp_isScSmooth (ScRetraction.id hU) hR
  have h2' := (isScSmooth_iff_contDiffOn_const (V := Fin m → ℝ) (W := Fin m → ℝ) hU.isScDomain
    (((rnChart m 0) ∘ d.s ∘ (rnChart m 0).symm) ∘ (ScRetraction.id hU))).1 h1
  have h2 : ContDiffOn ℝ ∞ d.s W := h2'.congr fun y _ => by
    change d.s y = d.s (y + 0) - 0
    rw [add_zero, sub_zero]
  have hidem : ∀ y ∈ W, d.s (d.s y) = d.s y := fun y hy =>
    d.isScPlusRetractionOn.idem y (d.toSubData.shrink_subset_V _ hy)
  have himg : d.s '' W = W ∩ A := d.toSubData.image_shrink _
  refine ⟨W, hWo, hxW, d.s, h2, hmaps, hidem, himg, ?_⟩
  -- the tangent space
  let R : ScRetraction (rnSc m) univ := ⟨W, d.s, hU, hmaps,
    (isScSmooth_iff_contDiffOn_const (V := Fin m → ℝ) (W := Fin m → ℝ) hU.isScDomain d.s).2 h2,
    hidem⟩
  have hRr : R.retract = W ∩ A := himg
  have hset : (rnChart m 0) '' (W ∩ A) = R.retract := by rw [rnChart_zero_image, hRr]
  have hx1 : x ∈ (rnPolyfold m).levelSet 1 := by rw [rnPolyfold_levelSet]; exact mem_univ x
  have hl : (rnChart m 0).model.E.toBase 1 (levelLift (rnChart m 0) 1 x) = rnChart m 0 x :=
    (rnPolyfold m).toBase_levelLift hφ (mem_univ x) hx1
  have hl' : (levelLift (rnChart m 0) 1 x : Fin m → ℝ) = x := by
    rw [rnChart_zero_apply'] at hl
    exact (ScBanach.const_toBase (Fin m → ℝ) 1 _).symm.trans hl
  have hz : (x : (rnSc m) 1) ∈ (rnSc m).lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, ScBanach.const_toBase, hRr]; exact ⟨hxW, hx⟩
  have hd : HasFDerivWithinAt d.s (scDeriv (E := rnSc m) (F := rnSc m) W d.s x) W x :=
    hasFDerivWithinAt_scDeriv_const' (V := Fin m → ℝ) (F := rnSc m) (U := W) (f := d.s)
      R.isSc1 hxW
  have hfd : fderiv ℝ d.s x = scDeriv (E := rnSc m) (F := rnSc m) W d.s x :=
    (hd.hasFDerivAt (hWo.mem_nhds hxW)).fderiv
  rw [chartTangent_eq hφ d hx hxV (mem_univ x)]
  have hl'' : levelLift (rnChart m 0) 1 x = (show (rnChart m 0).model.E 1 from x) := hl'
  rw [hl'']
  erw [hset, tangentSpace_eq_range R hz, hfd]

/-- **Lemmas 9.2.9–9.2.11 in `ℝᵐ`** (2021 pp. 414–417): every smooth submanifold `A` of `ℝᵐ`
through `x` has the graph representation at `x` in the chart `id`, with all directions
admissible (`K = ℝᵐ`).  The retraction `s` with `s(W) = W ∩ A` is strictly differentiable at
`x`, `D = Ds(x)` is a projection onto `T_xA`, and `A` is near `x` the graph of a map over `T_xA`
(`exists_mem_graph_of_hasStrictFDerivAt`). -/
theorem isGraphChartAt_rn {A : Set (Fin m → ℝ)} (hA : (rnPolyfold m).IsSmoothSubmanifold A)
    {x : Fin m → ℝ} (hx : x ∈ A) :
    (rnPolyfold m).IsGraphChartAt (isChart_rnChart 0) univ A x := by
  obtain ⟨W, hWo, hxW, s, hsm, hmaps, hidem, himg, hT⟩ := rn_exists_retraction hA hx
  have hfix : ∀ a ∈ W ∩ A, s a = a := fun a ha => by
    rw [← himg] at ha
    obtain ⟨w, hw, rfl⟩ := ha
    exact hidem w hw
  have hsx : s x = x := hfix x ⟨hxW, hx⟩
  have hstrict : HasStrictFDerivAt s (fderiv ℝ s x) x :=
    (hsm.contDiffAt (hWo.mem_nhds hxW)).hasStrictFDerivAt (by simp)
  set D := fderiv ℝ s x with hDdef
  have hDD : D.comp D = D := by
    have h' : HasFDerivAt s D (s x) := by rw [hsx]; exact hstrict.hasFDerivAt
    have hcomp : HasFDerivAt (s ∘ s) (D.comp D) x := h'.comp x hstrict.hasFDerivAt
    have hev : s =ᶠ[𝓝 x] s ∘ s :=
      Filter.eventually_of_mem (hWo.mem_nhds hxW) fun y hy => (hidem y hy).symm
    exact (hcomp.congr_of_eventuallyEq hev).unique hstrict.hasFDerivAt
  have hDfix : ∀ c ∈ range D, D c = c := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hDD
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hWo x hxW
  have hφ : ∀ r : Fin m → ℝ, rnChart m 0 r = r := rnChart_zero_apply'
  refine ⟨⟨0, ?_, 1, one_pos, fun _ _ _ => mem_univ _⟩, ?_, ?_⟩
  · rw [hT]; exact ⟨0, map_zero D⟩
  · -- the approximation by `T_xA`
    intro ε hε
    obtain ⟨δ₀, hδ₀, hest⟩ := Metric.eventually_nhds_iff.1 (hstrict.isLittleO.def hε)
    refine ⟨min δ₀ ρ, lt_min hδ₀ hρ, fun a ha b hb hax hbx => ?_⟩
    rw [hφ, hφ] at hax hbx
    rw [hφ, hφ]
    have haW : a ∈ W := hρW (by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hax (min_le_right _ _))
    have hbW : b ∈ W := hρW (by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hbx (min_le_right _ _))
    have h := hest (y := (a, b)) (by
      rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_lt (lt_of_lt_of_le hax (min_le_left _ _)) (lt_of_lt_of_le hbx (min_le_left _ _)))
    dsimp only at h
    rw [hfix a ⟨haW, ha.1⟩, hfix b ⟨hbW, hb.1⟩] at h
    exact ⟨D (a - b), by rw [hT]; exact ⟨_, rfl⟩, h⟩
  · -- the graph over `T_xA`
    intro Q hQT hQid h hh _ ε hε
    rw [hT] at hQT hQid hh
    set N : Submodule ℝ (Fin m → ℝ) := LinearMap.range (D : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
      with hNdef
    have hmemN : ∀ v, v ∈ N ↔ v ∈ range D := fun v => by
      rw [hNdef, LinearMap.mem_range]; rfl
    have hε' : 0 < ε / (‖h‖ + 1) := by positivity
    obtain ⟨r, hr, hgr⟩ := exists_mem_graph_of_hasStrictFDerivAt hstrict hsx (N := N)
      (fun c hc => hDfix c ((hmemN c).1 hc)) (fun v => (hmemN _).2 (hQT v))
      (fun v hv => hQid v ((hmemN v).1 hv)) hε' hρ
    refine ⟨r / (‖h‖ + 1), by positivity, fun t ht htt => ?_⟩
    have hu : t • h ∈ N := N.smul_mem t ((hmemN h).2 hh)
    have hur : ‖t • h‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      calc t * ‖h‖ ≤ t * (‖h‖ + 1) := by nlinarith
        _ < r := by rwa [lt_div_iff₀ (by positivity)] at htt
    obtain ⟨c, -, hcρ, hQc, hest⟩ := hgr _ hu hur
    have hxc : x + c ∈ W := hρW (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hcρ)
    have haA : s (x + c) ∈ A := by
      have : s (x + c) ∈ s '' W := ⟨x + c, hxc, rfl⟩
      rw [himg] at this
      exact this.2
    refine ⟨s (x + c), ⟨haA, mem_univ _⟩, ?_, ?_⟩
    · rw [hφ, hφ]; exact hQc
    · rw [hφ, hφ]
      refine hest.trans ?_
      have key : ∀ u : Fin m → ℝ, ε / (‖u‖ + 1) * ‖t • u‖ ≤ ε * t := fun u => by
        rw [norm_smul, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg u, mul_pos hε ht]
      exact key h

/-- **The graph representation holds at every point of `ℝᵐ`**, in every dimension (nontrivial
witness of `HasGraphChartsAt`). -/
theorem hasGraphChartsAt_rn (x : Fin m → ℝ) (n : ℕ) : (rnPolyfold m).HasGraphChartsAt x n :=
  ⟨rnChart m 0, isChart_rnChart 0, mem_univ x, univ, fun _ hA hx => isGraphChartAt_rn hA.1 hx⟩

/-- **Proposition 9.2.8 in `ℝᵐ`** (2021 p. 413, slice form): tangent slices exist at every point of
`ℝᵐ`, in every dimension. -/
theorem hasTangentSlicesAt_rn (x : Fin m → ℝ) (n : ℕ) : (rnPolyfold m).HasTangentSlicesAt x n :=
  hasTangentSlicesAt_of_hasGraphChartsAt (hasGraphChartsAt_rn x n)

end MPolyfold

/-! ### Consequences for Theorem 9.2.1 -/

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **The hypothesis of Theorem 9.2.1 in the equidimensional case**, from the graph
representation (Lemmas 9.2.9–9.2.11) at the points of `supp(Θ)`. -/
theorem hasIndependentTangentSums_of_isOfDim_of_hasGraphChartsAt {Θ : Obj → ℚ} {n : ℕ}
    (hdim : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x), B.IsOfDim n)
    (hG : ∀ x ∈ supp Θ, X.PObj.HasGraphChartsAt x n) : X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_isOfDim hdim fun x hx =>
    MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt (hG x hx)

/-- **The hypothesis of Theorem 9.2.1 in general**, from Proposition 9.1.12, dimension
labellings and the graph representation. -/
theorem hasIndependentTangentSums_of_proposition_9_1_12_of_hasGraphChartsAt
    (hP : X.Proposition_9_1_12) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hlab : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x),
      ∃ dim : B.ι → ℕ, ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hG : ∀ x ∈ supp Θ, ∀ n, X.PObj.HasGraphChartsAt x n) : X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_proposition_9_1_12 hP hΘ hlab fun x hx n =>
    MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt (hG x hx n)

end EpGroupoid

namespace EpGroupoid

variable {m : ℕ} {Mor : Type} [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid (Fin m → ℝ) Mor}

/-- **Two `n`-dimensional local branching structures give the same tangent sum** when the object
M-polyfold is `ℝᵐ` (Proposition 9.2.8 holds there, `hasTangentSlicesAt_rn`), for functors
agreeing near the base point (the fibre count after Lemma 9.2.11). -/
theorem LocalBranchingStructure.tangentSum_eq_of_isOfDim_rn (hX : X.PObj = rnPolyfold m)
    {Θ Θ' : (Fin m → ℝ) → ℚ} {x : Fin m → ℝ} (B : X.LocalBranchingStructure Θ x)
    (B' : X.LocalBranchingStructure Θ' x) {n : ℕ} (hB : B.IsOfDim n) (hB' : B'.IsOfDim n)
    {W : Set (Fin m → ℝ)} (hW : IsOpen W) (hxW : x ∈ W) (hΘ : ∀ y ∈ W, Θ y = Θ' y) :
    B.tangentSum = B'.tangentSum :=
  B.tangentSum_eq_of_eqOn B' hB hB' (hX ▸ MPolyfold.hasTangentSlicesAt_rn x n) hW hxW hΘ

/-- **Theorem 9.2.1 needs no further hypothesis in the equidimensional case over `ℝᵐ`**: if all
local branching structures of `Θ` are `n`-dimensional, the sums `∑ σᵢ · T_xMᵢ` are independent
of the structure. -/
theorem hasIndependentTangentSums_of_isOfDim_rn (hX : X.PObj = rnPolyfold m) {Θ : (Fin m → ℝ) → ℚ}
    {n : ℕ} (hdim : ∀ (x : Fin m → ℝ) (B : X.LocalBranchingStructure Θ x), B.IsOfDim n) :
    X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_isOfDim hdim fun x _ => hX ▸ MPolyfold.hasTangentSlicesAt_rn x n

/-- The same through Proposition 9.1.12 and dimension labellings (no equidimensionality). -/
theorem hasIndependentTangentSums_of_proposition_9_1_12_rn (hX : X.PObj = rnPolyfold m)
    (hP : X.Proposition_9_1_12) {Θ : (Fin m → ℝ) → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hlab : ∀ (x : Fin m → ℝ) (B : X.LocalBranchingStructure Θ x),
      ∃ dim : B.ι → ℕ, ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) :
    X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_proposition_9_1_12 hP hΘ hlab fun x _ n =>
    hX ▸ MPolyfold.hasTangentSlicesAt_rn x n

end EpGroupoid

namespace EpGroupoid.Remark913Hyp

variable {β₁ β₂ : ℝ → ℝ} (h : Remark913Hyp β₁ β₂)
include h

/-- The structure by the graphs of `β₁`, `β₂` is `1`-dimensional. -/
theorem structureβ_isOfDim (x : Fin 2 → ℝ) : (h.structureβ x).IsOfDim 1 := fun i =>
  (graphs2_isSubmanifoldOfDim h.contDiff₁ h.contDiff₂ i.1).inter_isOpen (h.structureβ x).isOpen_U

/-- The structure by the graphs of `γ₁ = 0`, `γ₂ = β₁ + β₂` is `1`-dimensional. -/
theorem structureγ_isOfDim (x : Fin 2 → ℝ) : (h.structureγ x).IsOfDim 1 := fun i =>
  (graphs2_isSubmanifoldOfDim contDiff_const (h.contDiff₁.add h.contDiff₂) i.1).inter_isOpen
    (h.structureγ x).isOpen_U

/-- **The tangent sums of the two local branching structures of Remark 9.1.3 (b) agree** at every
point of `ℝ²`, also at the origin, where no submanifold of the one agrees near `0` with a
submanifold of the other (`remark_9_1_3_b`): a nontrivial instance of Theorem 9.2.1 (1) through
Proposition 9.2.8 (`hasTangentSlicesAt_rn`). -/
theorem tangentSum_structureβ_eq_structureγ (x : Fin 2 → ℝ) :
    (h.structureβ x).tangentSum = (h.structureγ x).tangentSum :=
  (h.structureβ x).tangentSum_eq_of_eqOn (h.structureγ x) (h.structureβ_isOfDim x)
    (h.structureγ_isOfDim x) (MPolyfold.hasTangentSlicesAt_rn x 1)
    ((h.structureβ x).isOpen_U.inter (h.structureγ x).isOpen_U)
    ⟨(h.structureβ x).mem_U, (h.structureγ x).mem_U⟩ fun _ _ => rfl

end EpGroupoid.Remark913Hyp

end Polyfold
