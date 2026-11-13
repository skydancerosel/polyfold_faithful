import Polyfold.Chapter5.Theorem5315_LocalData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15** (p. 223; preprint: Theorem 5.22), conclusion (2): the reading of "Morse-type
critical points" does not depend on the parametrization.  Gap G.48.

# Independence of the parametrization, with boundary points

## The text, paraphrased

(Theorem 5.3.15 (2)) The function `t : S → [0, 1]` on the solution manifold has only Morse-type
critical points.

## What is formalized

`MPolyfold.IsMorseOrRegularPoint A t x` asks for one smooth parametrization `p` of `A` around
`x = p(u)` (by a set with unique derivatives) such that a critical point `u` of `t ∘ p` is
interior with injective Hessian.  Here:

* `MPolyfold.IsSmoothParam.hasFDerivWithinAt_transition`: the chain rule through the transition
  `θ = q' ∘ p` of two parametrizations, within sets with unique derivatives.
* `MPolyfold.IsSmoothParam.fderivWithin_transition_comp`: `Dθ'(u') ∘ Dθ(u) = 1`.
* `MPolyfold.IsSmoothParam.fderivWithin_ne_zero_congr` (**the regular alternative**): if `x` is
  not a critical point of `t` in one parametrization, it is not one in any other (boundary
  points included).
* `MPolyfold.IsSmoothParam.mem_nhds_congr`: if `u'` is an interior point of `Ω'`, then `u` is an
  interior point of `Ω` (inverse function theorem for the transition).
* `MPolyfold.IsSmoothParam.morseClause_congr` and
  **`MPolyfold.IsMorseOrRegularPoint.morseClause`**: the clause holds in *every* smooth
  parametrization of `A` around `x` by a set with unique derivatives, once it holds in one.
  With `MPolyfold.IsSmoothParam.hessian_injective_congr` (`Theorem5315_LocalInvariance.lean`)
  for the Hessian.
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

namespace MPolyfold.IsSmoothParam

omit [FiniteDimensional ℝ E] in
/-- **The chain rule through the transition** `θ = q' ∘ p` of two smooth parametrizations
through the point `p(u) = p'(u')`: if `ψ ∘ θ = φ₀` on `Ω` near `u`, then
`Dφ₀(u) = Dψ(u') ∘ Dθ(u)` (derivatives within `Ω`, `Ω'`). -/
theorem hasFDerivWithinAt_transition (h : PX.IsSmoothParam A Ω p q G)
    (h' : PX.IsSmoothParam A Ω' p' q' G') {u : E} (hu : u ∈ Ω) {u' : E'} (hu' : u' ∈ Ω')
    (hpu : p u = p' u') {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ψ : E' → F}
    {φ₀ : E → F} (hψ : DifferentiableWithinAt ℝ ψ Ω' u')
    (heq : ∀ w ∈ Ω, p w ∈ G' → ψ (q' (p w)) = φ₀ w) :
    HasFDerivWithinAt φ₀ ((fderivWithin ℝ ψ Ω' u').comp (fderivWithin ℝ (q' ∘ p) Ω u)) Ω u := by
  have hG' : p u ∈ G' := hpu ▸ h'.mem_G hu'
  have hθu : (q' ∘ p) u = u' := by
    change q' (p u) = u'
    rw [hpu, h'.left_inv u' hu']
  have hs : Ω ∩ p ⁻¹' G' ∈ 𝓝[Ω] u :=
    inter_mem self_mem_nhdsWithin
      ((h.continuousOn_p u hu).preimage_mem_nhdsWithin (h'.isOpen_G.mem_nhds hG'))
  have hθd : HasFDerivWithinAt (q' ∘ p) (fderivWithin ℝ (q' ∘ p) Ω u) Ω u :=
    (((h.contDiffOn_comp h'.smooth_q).differentiableOn (by simp)) u hu).hasFDerivWithinAt
  have hψd : HasFDerivWithinAt ψ (fderivWithin ℝ ψ Ω' u') Ω' ((q' ∘ p) u) := by
    rw [hθu]; exact hψ.hasFDerivWithinAt
  have hmaps : MapsTo (q' ∘ p) (Ω ∩ p ⁻¹' G') Ω' := fun w hw =>
    (h'.p_q (h.mem_A hw.1) hw.2).1
  have hcomp := hψd.comp u (hθd.mono inter_subset_left) hmaps
  exact (hcomp.congr (fun w hw => (heq w hw.1 hw.2).symm)
    (heq u hu hG').symm).mono_of_mem_nhdsWithin hs

/-- The derivatives of the two transitions are inverse to each other:
`D(q ∘ p')(u') ∘ D(q' ∘ p)(u) = 1`. -/
theorem fderivWithin_transition_comp (h : PX.IsSmoothParam A Ω p q G)
    (h' : PX.IsSmoothParam A Ω' p' q' G') (hΩ : UniqueDiffOn ℝ Ω) {u : E} (hu : u ∈ Ω)
    {u' : E'} (hu' : u' ∈ Ω') (hpu : p u = p' u') :
    (fderivWithin ℝ (q ∘ p') Ω' u').comp (fderivWithin ℝ (q' ∘ p) Ω u) =
      ContinuousLinearMap.id ℝ E := by
  have hψ : DifferentiableWithinAt ℝ (q ∘ p') Ω' u' :=
    ((h'.contDiffOn_comp h.smooth_q).differentiableOn (by simp)) u' hu'
  have h1 := h.hasFDerivWithinAt_transition h' hu hu' hpu (φ₀ := _root_.id) hψ
    (fun w hw hwG => by
      change q (p' (q' (p w))) = w
      rw [(h'.p_q (h.mem_A hw) hwG).2, h.left_inv w hw])
  exact (hΩ u hu).eq h1 (hasFDerivWithinAt_id u Ω)

/-- **The regular alternative does not depend on the parametrization**: let `p`, `p'` be smooth
parametrizations of `A` by sets with unique derivatives, `p(u) = p'(u')`, and `t` sc-smooth.
If `d(t ∘ p')(u') ≠ 0` then `d(t ∘ p)(u) ≠ 0`. -/
theorem fderivWithin_ne_zero_congr (h : PX.IsSmoothParam A Ω p q G)
    (h' : PX.IsSmoothParam A Ω' p' q' G') (hΩ : UniqueDiffOn ℝ Ω) (hΩ' : UniqueDiffOn ℝ Ω')
    {u : E} (hu : u ∈ Ω) {u' : E'} (hu' : u' ∈ Ω') (hpu : p u = p' u') {t : X → ℝ}
    (ht : PX.IsScSmoothMap realPolyfold t) (hreg : fderivWithin ℝ (t ∘ p') Ω' u' ≠ 0) :
    fderivWithin ℝ (t ∘ p) Ω u ≠ 0 := by
  intro h0
  have hψ : DifferentiableWithinAt ℝ (t ∘ p') Ω' u' :=
    ((h'.smooth_p t ht).differentiableOn (by simp)) u' hu'
  have h1 := h.hasFDerivWithinAt_transition h' hu hu' hpu (φ₀ := t ∘ p) hψ
    (fun w hw hwG => by
      change t (p' (q' (p w))) = t (p w)
      rw [(h'.p_q (h.mem_A hw) hwG).2])
  have h2 : (fderivWithin ℝ (t ∘ p') Ω' u').comp (fderivWithin ℝ (q' ∘ p) Ω u) = 0 := by
    rw [← h0]; exact ((hΩ u hu).eq h1 ((((h.smooth_p t ht).differentiableOn (by simp)) u
      hu).hasFDerivWithinAt))
  have h3 := h'.fderivWithin_transition_comp h hΩ' hu' hu hpu.symm
  refine hreg ?_
  calc fderivWithin ℝ (t ∘ p') Ω' u'
      = (fderivWithin ℝ (t ∘ p') Ω' u').comp
          ((fderivWithin ℝ (q' ∘ p) Ω u).comp (fderivWithin ℝ (q ∘ p') Ω' u')) := by
        rw [h3]; rfl
    _ = ((fderivWithin ℝ (t ∘ p') Ω' u').comp (fderivWithin ℝ (q' ∘ p) Ω u)).comp
          (fderivWithin ℝ (q ∘ p') Ω' u') := rfl
    _ = 0 := by rw [h2, ContinuousLinearMap.zero_comp]

/-- **Interior points do not depend on the parametrization**: if `u'` is an interior point of
`Ω'`, then `u` is an interior point of `Ω` (the transition `q ∘ p'` has an invertible derivative
at `u'`, and the inverse function theorem applies). -/
theorem mem_nhds_congr (h : PX.IsSmoothParam A Ω p q G) (h' : PX.IsSmoothParam A Ω' p' q' G')
    (hΩ : UniqueDiffOn ℝ Ω) (hΩ' : UniqueDiffOn ℝ Ω') {u : E} (hu : u ∈ Ω) {u' : E'}
    (hu' : u' ∈ Ω') (hpu : p u = p' u') (hint : Ω' ∈ 𝓝 u') : Ω ∈ 𝓝 u := by
  set θ' : E' → E := q ∘ p' with hθ'
  have hc : ContDiffAt ℝ ∞ θ' u' := (h'.contDiffOn_comp h.smooth_q).contDiffAt hint
  have e1 := h.fderivWithin_transition_comp h' hΩ hu hu' hpu
  have e2 := h'.fderivWithin_transition_comp h hΩ' hu' hu hpu.symm
  set e : E' ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse (fderivWithin ℝ θ' Ω' u')
    (fderivWithin ℝ (q' ∘ p) Ω u)
    (fun x => congrArg (fun L : E' →L[ℝ] E' => L x) e2)
    (fun x => congrArg (fun L : E →L[ℝ] E => L x) e1) with he
  have hstrict : HasStrictFDerivAt θ' (e : E' →L[ℝ] E) u' := by
    have h1 := hc.hasStrictFDerivAt (by simp)
    have h2 : fderiv ℝ θ' u' = (e : E' →L[ℝ] E) := (fderivWithin_of_mem_nhds hint).symm
    rwa [h2] at h1
  have hmap := hstrict.map_nhds_eq_of_equiv
  have hθ'u : θ' u' = u := by
    change q (p' u') = u
    rw [← hpu, h.left_inv u hu]
  have hG : p' u' ∈ G := hpu ▸ h.mem_G hu
  have hs : Ω' ∩ p' ⁻¹' G ∈ 𝓝 u' :=
    inter_mem hint ((h'.continuousOn_p.continuousAt hint).preimage_mem_nhds
      (h.isOpen_G.mem_nhds hG))
  have himg : θ' '' (Ω' ∩ p' ⁻¹' G) ∈ 𝓝 u := by
    rw [← hθ'u, ← hmap]; exact image_mem_map hs
  refine mem_of_superset himg ?_
  rintro _ ⟨w, hw, rfl⟩
  exact (h.p_q (h'.mem_A hw.1) hw.2).1

/-- **The clause of `IsMorseOrRegularPoint` does not depend on the parametrization**: let `p`,
`p'` be smooth parametrizations of `A` by sets with unique derivatives, `p(u) = p'(u')`.  If in
`p'` a critical point is interior with injective Hessian, the same holds in `p`. -/
theorem morseClause_congr (h : PX.IsSmoothParam A Ω p q G) (h' : PX.IsSmoothParam A Ω' p' q' G')
    (hΩ : UniqueDiffOn ℝ Ω) (hΩ' : UniqueDiffOn ℝ Ω') {u : E} (hu : u ∈ Ω) {u' : E'}
    (hu' : u' ∈ Ω') (hpu : p u = p' u') {t : X → ℝ} (ht : PX.IsScSmoothMap realPolyfold t)
    (hcl : fderivWithin ℝ (t ∘ p') Ω' u' = 0 →
      Ω' ∈ 𝓝 u' ∧ Injective (fderiv ℝ (fderiv ℝ (t ∘ p')) u'))
    (hcrit : fderivWithin ℝ (t ∘ p) Ω u = 0) :
    Ω ∈ 𝓝 u ∧ Injective (fderiv ℝ (fderiv ℝ (t ∘ p)) u) := by
  have hcrit' : fderivWithin ℝ (t ∘ p') Ω' u' = 0 := by
    by_contra hne
    exact h.fderivWithin_ne_zero_congr h' hΩ hΩ' hu hu' hpu ht hne hcrit
  obtain ⟨hint', hinj'⟩ := hcl hcrit'
  have hint : Ω ∈ 𝓝 u := h.mem_nhds_congr h' hΩ hΩ' hu hu' hpu hint'
  refine ⟨hint, ?_⟩
  obtain ⟨Ω₁, G₁, h₁, hΩ₁, hu₁, -⟩ := h.exists_isOpen_of_mem_nhds hint
  obtain ⟨Ω₁', G₁', h₁', hΩ₁', hu₁', -⟩ := h'.exists_isOpen_of_mem_nhds hint'
  refine h₁.hessian_injective_congr h₁' hΩ₁ hΩ₁' hu₁ hu₁' hpu ht (fun _ => hinj') ?_
  rw [← fderivWithin_of_mem_nhds hint]; exact hcrit

end MPolyfold.IsSmoothParam

/-- **"Regular point or Morse-type critical point" in every parametrization** (2021 Theorem
5.3.15 (2), p. 223): if `IsMorseOrRegularPoint A t x` holds (in one smooth parametrization),
then in every smooth parametrization `p` of `A` around `x = p(u)` by a set with unique
derivatives, a critical point `u` of `t ∘ p` is an interior point of the parameter set and the
Hessian of `t ∘ p` at `u` is injective. -/
theorem MPolyfold.IsMorseOrRegularPoint.morseClause {t : X → ℝ} {x : X}
    (hx : PX.IsMorseOrRegularPoint A t x) (ht : PX.IsScSmoothMap realPolyfold t)
    (h : PX.IsSmoothParam A Ω p q G) (hΩ : UniqueDiffOn ℝ Ω) {u : E} (hu : u ∈ Ω)
    (hpu : p u = x) (hcrit : fderivWithin ℝ (t ∘ p) Ω u = 0) :
    Ω ∈ 𝓝 u ∧ Injective (fderiv ℝ (fderiv ℝ (t ∘ p)) u) := by
  obtain ⟨n, Ω', p', q', G', u', h', hΩ', hu', hpu', hcl⟩ := hx
  exact h.morseClause_congr h' hΩ hΩ' hu hu' (hpu.trans hpu'.symm) ht hcl hcrit

end Polyfold
