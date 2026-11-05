import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_51

/-!
Round trip for V5_51 (Definition 5.33: the sc-smooth bump function property of a local model).

Listed: the definition `Polyfold.LocalModel.HasBumpProperty` and the lemma
`Polyfold.closure_inter_ball_subset` ("a retract is closed near each of its points", which the
project uses to produce neighbourhoods `U(x)` with `cl_E(U(x)) ⊆ O`).  So
`A := type_of% @Polyfold.closure_inter_ball_subset` (no universe parameters).

B is the equivalence `M.HasBumpProperty ↔ HasBumpPropertyB M` for every local model, with
Definition 5.33's "`f ≠ 0`" read literally (`f` not identically zero on `O`); the project reads it
as `f(x) ≠ 0`.

* project ⇒ literal (`hasBumpPropertyB_of_hasBumpProperty`): proved; `f(x) ≠ 0` gives a point of
  `O` where `f ≠ 0`, and "`U = O ∩ W` open in `O`, `cl_E(U) ⊆ O`, `supp_O f ⊆ U`" is the project's
  "`W` open, `cl_E(O ∩ W) ⊆ O`, `supp_O f ⊆ W`".
* literal ⇒ project: NOT proved, and not glue: it is "a bump that is merely not identically zero
  near `x` gives one with `f(x) ≠ 0`" on an arbitrary sc-retract, where there are no translations
  (the project's own reason for the pointwise reading).  Hence `A → B` is not proved (A, a lemma
  about retracts, says nothing about bump functions).  Neither is `¬ B`: a counterexample would
  need a local model with weak but not pointwise bumps, i.e. deep Banach-space geometry.
* `B → A` holds only because `A` is true: `A_outright` re-proves the lemma (the project's argument,
  the retraction is continuous on `C ∩ W'` and `C` is closed), without the hypothesis.
* The blind file's pointwise reading `BPointwise` is the project's notion exactly
  (`BPointwise_holds`).
-/

namespace RoundTrip.V5_51
open Polyfold Set Function

/-- The project's statement: the type of `closure_inter_ball_subset`. -/
def A : Prop := type_of% @Polyfold.closure_inter_ball_subset

theorem A_holds : A := @Polyfold.closure_inter_ball_subset

/-- `A` re-proved without the listed lemma (its statement is unrelated to B). -/
theorem A_outright : A := by
  intro M z r R hR W' hW' hball p hp
  have hOC : M.O ⊆ M.C := fun y hy => by
    rw [← hR] at hy
    have := R.retract_subset hy
    rw [hW'] at this; exact this.2
  have hpC : p ∈ M.C :=
    R.relOpen.isPartialQuadrant.isClosed.closure_subset_iff.2 (inter_subset_left.trans hOC)
      hp
  have hpb : p ∈ Metric.closedBall z (r / 2) :=
    (closure_mono inter_subset_right).trans Metric.closure_ball_subset_closedBall hp
  have hr : 0 ≤ r := by
    have := Metric.mem_closedBall.1 hpb
    linarith [dist_nonneg (x := p) (y := z)]
  have hpW' : p ∈ W' := by
    refine hball (Metric.mem_ball.2 ?_)
    have := Metric.mem_closedBall.1 hpb
    rcases hr.lt_or_eq with hr' | hr'
    · linarith
    · subst hr'
      have hO : M.O ∩ Metric.ball z (0 / 2) = ∅ := by
        rw [zero_div, Metric.ball_zero, inter_empty]
      rw [hO, closure_empty] at hp
      exact absurd hp (notMem_empty p)
  have hpU : p ∈ R.U := by rw [hW']; exact ⟨hpW', hpC⟩
  have hsub : M.O ∩ Metric.ball z (r / 2) ⊆ R.U := fun y hy => R.retract_subset (hR ▸ hy.1)
  have hfix : EqOn R id (insert p (M.O ∩ Metric.ball z (r / 2))) := by
    refine EqOn.of_subset_closure (s := M.O ∩ Metric.ball z (r / 2))
      (fun y hy => R.apply_eq_self_of_mem_retract (hR ▸ hy.1))
      (R.isSc1.isSc0.continuousOn_base.mono (insert_subset hpU hsub)) continuousOn_id
      (subset_insert _ _) (insert_subset hp subset_closure)
  rw [← hR]
  exact R.mem_retract_iff.2 ⟨hpU, hfix (mem_insert p _)⟩

/-- The project's (pointwise) bump property implies B's literal one. -/
theorem hasBumpPropertyB_of_hasBumpProperty {M : LocalModel} (h : M.HasBumpProperty) :
    HasBumpPropertyB M := by
  rintro x hx _ - hxU ⟨W, hW, rfl⟩ hcl
  obtain ⟨f, hf, hfx, hsupp⟩ := h x hx W hW hxU.2 hcl
  exact ⟨f, hf, ⟨x, hx, hfx⟩, fun z hz => ⟨hz.2, hsupp hz⟩⟩

/-- The blind file's pointwise reading is exactly the project's notion. -/
theorem BPointwise_holds : BPointwise := by
  intro M
  constructor
  · rintro h x hx _ - hxU ⟨W, hW, rfl⟩ hcl
    obtain ⟨f, hf, hfx, hsupp⟩ := h x hx W hW hxU.2 hcl
    exact ⟨f, hf, hfx, fun z hz => ⟨hz.2, hsupp hz⟩⟩
  · intro h x hx W hW hxW hcl
    obtain ⟨f, hf, hfx, hsupp⟩ :=
      h x hx (M.O ∩ W) inter_subset_left ⟨hx, hxW⟩ ⟨W, hW, rfl⟩ hcl
    exact ⟨f, hf, hfx, hsupp.trans inter_subset_right⟩

/-- Vacuous: `A` is re-proved outright (`A_outright`), without using `B`. -/
theorem B_to_A : B → A := fun _ => A_outright

#rt_check RoundTrip.V5_51.B_to_A [Polyfold.closure_inter_ball_subset]
#rt_check RoundTrip.V5_51.hasBumpPropertyB_of_hasBumpProperty [Polyfold.closure_inter_ball_subset]
#rt_check RoundTrip.V5_51.BPointwise_holds [Polyfold.closure_inter_ball_subset]
#rt_overlap RoundTrip.V5_51.B_to_A [Polyfold.closure_inter_ball_subset]

end RoundTrip.V5_51
