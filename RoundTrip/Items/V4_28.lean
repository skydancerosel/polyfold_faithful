import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_28

/-! Round trip for V4_28 (Theorem 4.2, (ii) ⇒ (i)).

`A` is the conjunction of the types of `Polyfold.exists_proj_goodComplement`,
`Polyfold.exists_cornerChartData`, `Polyfold.CornerChartData.chart_isCornerChart`,
`Polyfold.CornerChartData.chart_isChart`, `Polyfold.MPolyfold.theorem_4_1_2_chart` and
`Polyfold.MPolyfold.hasCornerStructure_of_centred` (universe `0` for the M-polyfold `X`; the
`CornerChartData` structure and `CornerChartData.chart` are definitions).

`A → B`: `hasCornerStructure_of_centred` (A).  Glue: a junk value `x₀ ∈ X₁` from any point (all
points are smooth); the empty case by `hasCornerStructure_iff`; B's `T₀O = Dr(0)E` (for some `R`
onto `O`) is the project's `tangentSpace` (`tangentSpace_eq_coe_submodule`); B's good position
(an sc-complement) gives the project's `IsInGoodPosition` (an algebraic complement) through
level `0` of the sc-splitting.  B's tameness hypotheses (of `X` and of the charts) are not needed.

`B → A` fails for a genuine reason: `hasCornerStructure_of_centred` (and `theorem_4_1_2_chart`) assume
neither that `X` is tame nor that the centred charts are tame, and only an algebraic good complement;
B assumes all three, so it cannot be applied under A's hypotheses.  The other conjuncts
(`exists_proj_goodComplement`, the normal form of Proposition 3.22; `exists_cornerChartData`,
Proposition 4.9 in a chart; the chart lemmas) are local statements B says nothing about. -/

namespace RoundTrip.V4_28
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.exists_proj_goodComplement) ∧
    (type_of% @Polyfold.exists_cornerChartData.{0}) ∧
    (type_of% @Polyfold.CornerChartData.chart_isCornerChart.{0}) ∧
    (type_of% @Polyfold.CornerChartData.chart_isChart.{0}) ∧
    (type_of% @Polyfold.MPolyfold.theorem_4_1_2_chart.{0}) ∧
    (type_of% @Polyfold.MPolyfold.hasCornerStructure_of_centred.{0})

theorem A_holds : A :=
  ⟨@Polyfold.exists_proj_goodComplement, @Polyfold.exists_cornerChartData.{0},
    @Polyfold.CornerChartData.chart_isCornerChart.{0}, @Polyfold.CornerChartData.chart_isChart.{0},
    @Polyfold.MPolyfold.theorem_4_1_2_chart.{0}, @Polyfold.MPolyfold.hasCornerStructure_of_centred.{0}⟩

/-- B's good position (with an sc-complement) gives the project's (an algebraic complement). -/
theorem isInGoodPosition_of_B {E : ScBanach} {C : Set (E 0)} {N : Submodule ℝ (E 0)}
    (h : IsGoodPositionB E C N) : IsInGoodPosition E C N := by
  obtain ⟨hint, Y, hY, ε, hε, hgood⟩ := h
  refine ⟨hint, Y, ⟨?_, ε, hε, hgood⟩⟩
  have := hY.2.2 0
  rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this

theorem A_to_B : A → B := by
  intro hA X _ _ _ P _hT hsm hmap hc
  by_cases hX : Nonempty X
  · obtain ⟨y⟩ := hX
    have hy : y ∈ P.smoothSet := by rw [hsm]; exact mem_univ y
    let x₀ : P.Level 1 := ⟨y, MPolyfold.smoothSet_subset_levelSet 1 hy⟩
    refine hA.2.2.2.2.2 x₀ (fun x => by rw [hsm]; exact mem_univ x) (hmap x₀) fun x => ?_
    obtain ⟨ψ, hψ, -, hx, h0, R, hR, hfin, hgood⟩ := hc x
    have h0O : (0 : ψ.model.E 0) ∈ ψ.model.O := h0 ▸ ψ.mapsTo_model x hx
    have h0R : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, map_zero, hR]; exact h0O
    have hN := tangentSpace_eq_coe_submodule R h0R
    rw [hR] at hN
    exact ⟨ψ, hψ, hx, h0, tangentAtZero R, hN.symm, hfin, isInGoodPosition_of_B hgood⟩
  · exact MPolyfold.hasCornerStructure_iff.2 fun x => (hX ⟨x⟩).elim

#rt_check RoundTrip.V4_28.A_to_B [Polyfold.exists_proj_goodComplement,
  Polyfold.exists_cornerChartData, Polyfold.CornerChartData.chart_isCornerChart,
  Polyfold.CornerChartData.chart_isChart, Polyfold.MPolyfold.theorem_4_1_2_chart,
  Polyfold.MPolyfold.hasCornerStructure_of_centred]

end RoundTrip.V4_28
