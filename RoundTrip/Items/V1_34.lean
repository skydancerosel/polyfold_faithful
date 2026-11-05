import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_34

/-! Round trip for V1_34 (after Definition 1.14: `x ↦ Df(x)` is continuous for the compact-open
topology, in general not for the operator norm).

`A` is the conjunction of the types of `Polyfold.continuousOn_apply_iff_uniformOnCompact`
(universe-polymorphic in `X Y Z : Type*`; instantiated at `.{0,0,0}` since `B` lives in `Type`),
`Polyfold.IsSc1With.deriv_uniformOnCompact` and (refresh 2026-11-02, added to the row)
`Polyfold.exists_isSc1_not_continuousOn_deriv` (no universe parameters).

* `A → B` is proved: `A` gives `B`'s first conjunct (`A_to_B_given_counterexample`, via Mathlib's
  description of the compact-open topology as uniform convergence on compacts), and `B`'s second
  conjunct (an sc¹ map whose `Df` is not norm-continuous) is `A`'s new
  `exists_isSc1_not_continuousOn_deriv` (the example `f(t, x)_k = cos(k t) x_k` on `ℝ ⊕ X`, `X` a
  weighted `c₀`), taking for `D` the witness of `IsSc1`.
* `B → A` fails because `A` is more general: `deriv_uniformOnCompact` holds for every `U`
  (no partial quadrant), and `continuousOn_apply_iff_uniformOnCompact` is a general lemma about
  `A : X → L(Y, Z)` (both directions, any metric `X`) that `B` does not address.  We prove
  `B_to_A_quadrant`: `B` gives `deriv_uniformOnCompact` for `U` relatively open in a partial
  quadrant, and `B_to_A_example`: `B`'s second conjunct gives `exists_isSc1_not_continuousOn_deriv`
  (for EVERY derivative family, since `Df` is unique on `U₁` for a relatively open subset of a
  partial quadrant: `IsSc1With.eq_of_uniqueDiffWithinAt`, `IsRelOpenInQuadrant.isScDomain`). -/

namespace RoundTrip.V1_34
open Polyfold Filter Topology

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.continuousOn_apply_iff_uniformOnCompact.{0, 0, 0}) ∧
  (type_of% @Polyfold.IsSc1With.deriv_uniformOnCompact) ∧
  (type_of% @Polyfold.exists_isSc1_not_continuousOn_deriv)

theorem A_holds : A :=
  ⟨@Polyfold.continuousOn_apply_iff_uniformOnCompact.{0, 0, 0},
    @Polyfold.IsSc1With.deriv_uniformOnCompact, @Polyfold.exists_isSc1_not_continuousOn_deriv⟩

/-- `A` gives `B`'s positive claim (compact-open continuity of `Df` on `U₁`, via Mathlib's
description of the compact-open topology as uniform convergence on compacts); `B`'s negative
claim must be supplied. -/
theorem A_to_B_given_counterexample : A →
    (∃ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
      (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0),
      IsRelOpenInQuadrant E C U ∧ IsSc1With U f D ∧ ¬ ContinuousOn D (E.lvlSet U 1)) → B := by
  intro hA hcex
  refine ⟨fun E F C U f D _ hD x hx => ?_, hcex⟩
  change Tendsto (fun x' => ((D x' : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0)))
    (𝓝[E.lvlSet U 1] x) (𝓝 ((D x : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0)))
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hA.2.1 hD hx hK hε] with x' hx' w hw
  rw [dist_eq_norm, norm_sub_rev]
  exact hx' w hw

/-- `A → B`: the counterexample is `A`'s `exists_isSc1_not_continuousOn_deriv`. -/
theorem A_to_B : A → B := by
  intro hA
  refine A_to_B_given_counterexample hA ?_
  obtain ⟨E, F, C, U, f, hU, ⟨D, hD⟩, hnc⟩ := hA.2.2
  exact ⟨E, F, C, U, f, D, hU, hD, hnc D hD⟩

/-- `B` gives `deriv_uniformOnCompact` on relatively open subsets of partial quadrants. -/
theorem B_to_A_quadrant : B → ∀ {E F : ScBanach} {C U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
    {D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0}, IsRelOpenInQuadrant E C U → IsSc1With U f D →
    ∀ {x : E.lvl 1}, x ∈ E.lvlSet U 1 → ∀ {K : Set (E.lvl 0)}, IsCompact K → ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x' in 𝓝[E.lvlSet U 1] x, ∀ w ∈ K, ‖D x' w - D x w‖ < ε := by
  intro hB E F C U f D hU hD x hx K hK ε hε
  have h := hB.1 E F C U f D hU hD x hx
  change Tendsto (fun x' => ((D x' : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0)))
    (𝓝[E.lvlSet U 1] x) (𝓝 ((D x : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0))) at h
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at h
  have h2 := Metric.tendstoUniformlyOn_iff.1 (h K hK) ε hε
  filter_upwards [h2] with x' hx' w hw
  have := hx' w hw
  rw [dist_eq_norm, norm_sub_rev] at this
  exact this

/-- `B`'s second conjunct gives `exists_isSc1_not_continuousOn_deriv`: `Df` is unique on `U₁`. -/
theorem B_to_A_example : B → type_of% @Polyfold.exists_isSc1_not_continuousOn_deriv := by
  intro hB
  obtain ⟨E, F, C, U, f, D, hU, hD, hnc⟩ := hB.2
  refine ⟨E, F, C, U, f, hU, ⟨D, hD⟩, fun D' hD' hc => hnc (hc.congr fun x hx => ?_)⟩
  exact hD.eq_of_uniqueDiffWithinAt hD' hx (hU.isScDomain.uniqueDiffWithinAt_one x hx)

#rt_check RoundTrip.V1_34.A_to_B
  [Polyfold.continuousOn_apply_iff_uniformOnCompact, Polyfold.IsSc1With.deriv_uniformOnCompact,
    Polyfold.exists_isSc1_not_continuousOn_deriv]
#rt_check RoundTrip.V1_34.B_to_A_quadrant
  [Polyfold.continuousOn_apply_iff_uniformOnCompact, Polyfold.IsSc1With.deriv_uniformOnCompact,
    Polyfold.exists_isSc1_not_continuousOn_deriv]
#rt_check RoundTrip.V1_34.B_to_A_example
  [Polyfold.continuousOn_apply_iff_uniformOnCompact, Polyfold.IsSc1With.deriv_uniformOnCompact,
    Polyfold.exists_isSc1_not_continuousOn_deriv]
#rt_overlap RoundTrip.V1_34.B_to_A_quadrant
  [Polyfold.continuousOn_apply_iff_uniformOnCompact, Polyfold.IsSc1With.deriv_uniformOnCompact,
    Polyfold.exists_isSc1_not_continuousOn_deriv]
#rt_overlap RoundTrip.V1_34.B_to_A_example
  [Polyfold.continuousOn_apply_iff_uniformOnCompact, Polyfold.IsSc1With.deriv_uniformOnCompact,
    Polyfold.exists_isSc1_not_continuousOn_deriv]

end RoundTrip.V1_34
