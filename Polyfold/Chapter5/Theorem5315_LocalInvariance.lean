import Polyfold.Chapter5.Theorem5315_MorseTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15 (2)** (p. 223; 2017: Theorem 5.8; preprint: Theorem 5.22): "Morse-type critical
point" does not depend on the chart.  Gap G.48.

# Independence of the parametrization

## The text, paraphrased

(Theorem 5.3.15 (2)) `t : S_{f+s₀} → [0, 1]` has only Morse-type critical points.

## What is formalized

* `MPolyfold.IsSmoothParam.transition`: for two smooth parametrizations `p`, `p'` of `A` through
  the same point, `θ = q' ∘ p` is `C^∞` near `u`, `p' ∘ θ = p` near `u`, and `dθ(u)` is bijective.
* `MPolyfold.IsSmoothParam.hessian_injective_congr`: at an interior point of both
  parametrizations, the clause "critical ⟹ injective Hessian" for `t ∘ p'` gives it for `t ∘ p`:
  the clause of `MPolyfold.IsMorseOrRegularPoint` does not depend on the parametrization.
* The regular alternative at boundary points and the whole clause in every parametrization are in
  `Theorem5315_LocalInvarianceClause.lean` (`MPolyfold.IsSmoothParam.fderivWithin_ne_zero_congr`,
  `MPolyfold.IsMorseOrRegularPoint.morseClause`, 2026-11-12).
-/

open Set Function Module Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {A : Set X} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {Ω : Set E} {p : E → X}
  {q : X → E} {G : Set X} {Ω' : Set E'} {p' : E' → X} {q' : X → E'} {G' : Set X}

omit [FiniteDimensional ℝ E] in
/-- The transition `θ = q' ∘ p` of two smooth parametrizations through the same point. -/
theorem MPolyfold.IsSmoothParam.transition (h : PX.IsSmoothParam A Ω p q G)
    (h' : PX.IsSmoothParam A Ω' p' q' G') (hΩ : IsOpen Ω) {u : E} (hu : u ∈ Ω) {u' : E'}
    (hu' : u' ∈ Ω') (hpu : p u = p' u') :
    ContDiffOn ℝ ∞ (q' ∘ p) Ω ∧ (q' ∘ p) u = u' ∧ ∀ᶠ w in 𝓝 u, p' ((q' ∘ p) w) = p w := by
  refine ⟨h.contDiffOn_comp h'.smooth_q, ?_, ?_⟩
  · change q' (p u) = u'
    rw [hpu, h'.left_inv u' hu']
  · have hc : ContinuousAt p u := h.continuousOn_p.continuousAt (hΩ.mem_nhds hu)
    have hG : p u ∈ G' := hpu ▸ h'.mem_G hu'
    filter_upwards [hc.preimage_mem_nhds (h'.isOpen_G.mem_nhds hG), hΩ.mem_nhds hu] with w hw hwΩ
    exact (h'.p_q (h.mem_A hwΩ) hw).2

/-- **The clause of `IsMorseOrRegularPoint` does not depend on the parametrization**: let `p`,
`p'` be smooth parametrizations of `A` by open sets, `p(u) = p'(u')`, and `t` sc-smooth.  If a
critical point `u'` of `t ∘ p'` has an injective Hessian, so has a critical point `u` of
`t ∘ p`. -/
theorem MPolyfold.IsSmoothParam.hessian_injective_congr (h : PX.IsSmoothParam A Ω p q G)
    (h' : PX.IsSmoothParam A Ω' p' q' G') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') {u : E}
    (hu : u ∈ Ω) {u' : E'} (hu' : u' ∈ Ω') (hpu : p u = p' u') {t : X → ℝ}
    (ht : PX.IsScSmoothMap realPolyfold t)
    (hcl : fderiv ℝ (t ∘ p') u' = 0 → Injective (fderiv ℝ (fderiv ℝ (t ∘ p')) u'))
    (hcrit : fderiv ℝ (t ∘ p) u = 0) : Injective (fderiv ℝ (fderiv ℝ (t ∘ p)) u) := by
  obtain ⟨hθc, hθu, hθev⟩ := h.transition h' hΩ hu hu' hpu
  obtain ⟨hθ'c, hθ'u, hθ'ev⟩ := h'.transition h hΩ' hu' hu hpu.symm
  set θ : E → E' := q' ∘ p with hθ
  set θ' : E' → E := q ∘ p' with hθ'
  have hθ2 : ContDiffAt ℝ 2 θ u := (hθc.contDiffAt (hΩ.mem_nhds hu)).of_le (by decide)
  have hθ'2 : ContDiffAt ℝ 2 θ' u' := (hθ'c.contDiffAt (hΩ'.mem_nhds hu')).of_le (by decide)
  have hθd : HasFDerivAt θ (fderiv ℝ θ u) u := (hθ2.differentiableAt (by norm_num)).hasFDerivAt
  have hθ'd : HasFDerivAt θ' (fderiv ℝ θ' u') u' :=
    (hθ'2.differentiableAt (by norm_num)).hasFDerivAt
  -- `θ' ∘ θ = id` near `u`, `θ ∘ θ' = id` near `u'`
  have hid : θ' ∘ θ =ᶠ[𝓝 u] id := by
    filter_upwards [hθev, hΩ.mem_nhds hu] with w hw hwΩ
    change q (p' (θ w)) = w
    rw [hw, h.left_inv w hwΩ]
  have hid' : θ ∘ θ' =ᶠ[𝓝 u'] id := by
    filter_upwards [hθ'ev, hΩ'.mem_nhds hu'] with w hw hwΩ
    change q' (p (θ' w)) = w
    rw [hw, h'.left_inv w hwΩ]
  have hθ'at : HasFDerivAt θ' (fderiv ℝ θ' u') (θ u) := by rw [hθu]; exact hθ'd
  have hθat : HasFDerivAt θ (fderiv ℝ θ u) (θ' u') := by rw [hθ'u]; exact hθd
  have e1 : (fderiv ℝ θ' u').comp (fderiv ℝ θ u) = ContinuousLinearMap.id ℝ E :=
    ((hθ'at.comp u hθd).congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id u)
  have e2 : (fderiv ℝ θ u).comp (fderiv ℝ θ' u') = ContinuousLinearMap.id ℝ E' :=
    ((hθat.comp u' hθ'd).congr_of_eventuallyEq hid'.symm).unique (hasFDerivAt_id u')
  have hinjθ : Injective (fderiv ℝ θ u) := fun x y hxy => by
    have hx := congrArg (fun L : E →L[ℝ] E => L x) e1
    have hy := congrArg (fun L : E →L[ℝ] E => L y) e1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hsurjθ : Surjective (fderiv ℝ θ u) := fun y =>
    ⟨fderiv ℝ θ' u' y, congrArg (fun L : E' →L[ℝ] E' => L y) e2⟩
  -- `t ∘ p = (t ∘ p') ∘ θ` near `u`
  set g := t ∘ p with hg
  set g' := t ∘ p' with hg'
  have hgeq : g =ᶠ[𝓝 u] g' ∘ θ := by
    filter_upwards [hθev] with w hw
    simp only [hg, hg', Function.comp_apply, hw]
  have hg'2 : ContDiffAt ℝ 2 g' (θ u) := by
    rw [hθu]
    exact ((h'.smooth_p t ht).contDiffAt (hΩ'.mem_nhds hu')).of_le (by decide)
  have hd1 : fderiv ℝ g u = (fderiv ℝ g' (θ u)).comp (fderiv ℝ θ u) := by
    rw [hgeq.fderiv_eq]
    exact fderiv_comp u (hg'2.differentiableAt (by norm_num)) hθd.differentiableAt
  have hg'0 : fderiv ℝ g' (θ u) = 0 := by
    refine ContinuousLinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hsurjθ y
    have := congrArg (fun L : E →L[ℝ] ℝ => L x) (hd1.symm.trans hcrit)
    simpa using this
  have hinj' : Injective (fderiv ℝ (fderiv ℝ g') (θ u)) := by
    rw [hθu]; exact hcl (by rw [← hθu]; exact hg'0)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hH : ∀ y, fderiv ℝ (fderiv ℝ g') (θ u) (fderiv ℝ θ u x) (fderiv ℝ θ u y) = 0 := by
    intro y
    have h3 := fderiv_fderiv_comp_apply hg'2 hθ2 x y
    rw [hg'0] at h3
    have h4 : fderiv ℝ (fderiv ℝ g) u = fderiv ℝ (fderiv ℝ (g' ∘ θ)) u := hgeq.fderiv.fderiv_eq
    rw [← h4, hx] at h3
    simpa using h3.symm
  have h5 : fderiv ℝ (fderiv ℝ g') (θ u) (fderiv ℝ θ u x) = 0 := by
    refine ContinuousLinearMap.ext fun y => ?_
    obtain ⟨y₀, rfl⟩ := hsurjθ y
    exact hH y₀
  exact hinjθ ((hinj' (h5.trans (map_zero _).symm)).trans (map_zero _).symm)

end Polyfold
