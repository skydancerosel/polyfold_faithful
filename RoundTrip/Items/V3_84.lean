import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_84

/-!
Round trip for V3_84 (Theorem 3.54 (2) at the centre: the data of Definition 3.25 at `x₀`).  `A` is
the conjunction of the types of `Polyfold.theorem_3_54_tangentGermChart_proj`,
`Polyfold.theorem_3_54_tangentGermChart` (universes `0, 0`), `Polyfold.MChart.compDiffeo_isChart`,
`Polyfold.MPolyfold.TangentGermChart.π_mem_of_projectsInto` (universe `0`),
`Polyfold.isScInftyGermAt_of_lifts` and `Polyfold.StabilityData.ker_Dfs_le_smooth`
(`MChart.compDiffeo` is vocabulary).  Since the germ reading (refresh 2026-11-02) the two
`theorem_3_54_tangentGermChart…` assume good position in the text's germ reading
(`IsGoodPositionGermTame`); nothing else changed.

Neither direction is proved.  What is proved (`A_to_B_weak`, from the hypothesis `A`): under `B`'s
hypotheses, an open `V ∋ x`, a dimension `d` and the project's data of Definition 3.25 (2) for
`S(f, V)` **at the centre `x` only** (`TangentGermChart`, with `π(O) ⊆ C`).  Glue:
`isGoodPositionGermTame_of_sc` (from V3_94; `B`'s whole-chart good position at `x` gives
`IsGoodPositionGermTameWholeChart`, hence the germ `IsGoodPositionGermTame`).

Gaps to `A → B` (`B`: the `d`-dimensional tangent germ property of `S(f, V)` at **every** point,
with `d = dim ker f'(x)` read in every chart):
* `A` gives the data only at `x` (the item's title); data at the other points of `S` need good
  position at the nearby zeros (Theorem 3.54 (1)) and the local constancy of the dimension
  (`theorem_3_54_two` / `exists_isRegular_of_locally`), none of which is in `A`.
* `A`'s `d` is existential; `A` does not identify it with `dim ker f'(x)` in any chart.
* `B`'s Definition 3.25 differs in its notions: the good complement must give an sc-splitting
  (`A`: a closed algebraic complement; for a smooth finite-dimensional `N` this upgrade is true and
  routine) and `δ` must be an sc-smooth germ on one germ of neighbourhoods with `Dδ(0) = 0`
  (`A`: `IsScInftyGermAt`, `C^k`-lifts on `k`-dependent neighbourhoods).
-/

namespace RoundTrip.V3_84
open Polyfold Set

/-- The project's statement: the data of Definition 3.25 (2) at the centre (with and without
`π(O) ⊆ C`) and four lemmas of its proof. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_tangentGermChart_proj.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_tangentGermChart.{0, 0} ∧
    type_of% @Polyfold.MChart.compDiffeo_isChart.{0} ∧
    type_of% @Polyfold.MPolyfold.TangentGermChart.π_mem_of_projectsInto.{0} ∧
    type_of% @Polyfold.isScInftyGermAt_of_lifts ∧
    type_of% @Polyfold.StabilityData.ker_Dfs_le_smooth

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_tangentGermChart_proj.{0, 0},
    @Polyfold.theorem_3_54_tangentGermChart.{0, 0}, @Polyfold.MChart.compDiffeo_isChart.{0},
    @Polyfold.MPolyfold.TangentGermChart.π_mem_of_projectsInto.{0},
    @Polyfold.isScInftyGermAt_of_lifts, @Polyfold.StabilityData.ker_Dfs_le_smooth⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- (From V3_94/V3_95.)  B's good position (sc-complement, cone `T ∩ C`) gives the project's (algebraic
complement, cone `C`). -/
theorem isInGoodPositionIn_of_sc {E : ScBanach} {T : Submodule ℝ (E 0)} {C : Set (E 0)}
    {N : Submodule ℝ (E 0)} (h : IsInGoodPositionSc E T ((T : Set (E 0)) ∩ C) N) :
    IsInGoodPositionIn E T C N := by
  obtain ⟨hNT, hint, Pc, hPT, -, hsplit, ε, hε, hgood⟩ := h
  have hpre : (Subtype.val ⁻¹' ((T : Set (E 0)) ∩ C) : Set N) = Subtype.val ⁻¹' C := by
    ext ⟨n, hn⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hNT hn, h⟩⟩
  have h0 := hsplit 0
  simp only [ScBanach.levelSub_zero] at h0
  refine ⟨hNT, hpre ▸ hint, Pc, hPT, h0.1, h0.2, ε, hε, fun n hn p hp hle => ?_⟩
  have h := hgood n hn p hp hle
  have hnT : n ∈ T := hNT hn
  have hnpT : n + p ∈ T := T.add_mem hnT (hPT hp)
  simp only [Set.mem_inter_iff, SetLike.mem_coe] at h
  exact ⟨fun hc => (h.1 ⟨hnT, hc⟩).2, fun hc => (h.2 ⟨hnpT, hc⟩).2⟩

/-- **B's hypothesis gives A's**: `B`'s (whole-chart) `IsGoodPositionGermSc` at a zero of an
sc-Fredholm section with tame germ data gives the project's whole-chart
`IsGoodPositionGermTameWholeChart` in the same centred tame chart, hence `IsGoodPositionGermTame`
(germ reading). -/
theorem isGoodPositionGermTame_of_sc {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (h : IsGoodPositionGermSc Bd f x) : Bd.IsGoodPositionGermTame f x := by
  obtain ⟨c, h0, g, s, ⟨hct, hxV, hφ0, hfill, hs, hs0, hsurj, hgp⟩, hconj⟩ := h
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx
  have h0O : (0 : c.φ.model.E 0) ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hf.isScSmooth.1 hxV).1 hx
    rwa [hφ0] at this
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  have hfK : ∀ z ∈ StrongRetr.r c.R '' c.U,
      (z, c.principal f z) ∈ c.R '' (c.U ×ˢ (univ : Set (c.F 0))) :=
    fun z hz => c.principal_mem_K hf.isScSmooth.1 (c.r_image ▸ hz)
  have hker : LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤
      rangeS (scDeriv c.U (StrongRetr.r c.R) 0) :=
    hfill.filler.ker_deriv_le_range hfill.isScSmooth hg0 h0O hfK
  refine StrongBundle.IsGoodPositionGermTameWholeChart.isGoodPositionGermTame
    ⟨hxs, c, hct, hxV, hφ0, h0, g, s, hfill, hs, hs0,
    isConjugateToBasicGerm_iff_nonempty.2 hconj, ⟨fun k hk => ?_, ?_⟩⟩
  · exact hsurj k ((mem_rangeS_ρCLM_iff c.isRetraction h0O h0).1 hk)
  · by_cases hd : 1 ≤ PX.degIndex x
    · have h1 := isInGoodPositionIn_of_sc (hgp hd)
      rwa [inf_eq_left.2 hker] at h1
    · -- `d_X(x) = 0`: in the tame chart no quadrant coordinate vanishes at `φ(x) = 0`, `C = E₀`
      have hd0 : PX.degIndex x = 0 := by omega
      obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
      have htameO : IsTameRetract c.φ.model.E c.φ.model.C c.φ.model.O :=
        ⟨c.isRetraction.baseRetraction c.relOpen, c.base_retract, hct.2⟩
      have hdeg : degIndexWith T (c.φ x) = 0 := by
        have h1 := PX.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart htameO hxV
        rw [hd0, MPolyfold.chartDegIndex, degIndex_eq T hT (c.φ.apply_mem_C hxV)] at h1
        exact h1.symm
      have hcoord : ∀ i, (T 0 (c.φ x)).1 i ≠ 0 := by
        simp only [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
          Finset.mem_univ, true_implies] at hdeg
        exact hdeg
      have huniv : partialQuadrantAtWith T (c.φ x) = univ :=
        eq_univ_of_forall fun v i hi => absurd hi (hcoord i)
      rw [hφ0, partialQuadrantAtWith_zero, ← hT] at huniv
      exact isInGoodPositionIn_of_subset hker (by rw [huniv]; exact subset_univ _)

end Glue

/-- **What `A` gives under `B`'s hypotheses**: the data of Definition 3.25 (2) for `S(f, V)` at the
centre `x` (with `π(O) ⊆ C`), of some dimension `d`. -/
theorem A_to_B_weak (hA : A) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (x : X),
      IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
      IsGoodPositionGermSc Bd f x →
        ∃ (V : Set X) (d : ℕ), IsOpen V ∧ x ∈ V ∧
          ∃ D : PX.TangentGermChart (zeroSetIn P f V) x d,
            ∀ z ∈ D.φ.model.O, ((D.π z : D.N) : D.φ.model.E 0) ∈ D.φ.model.C := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgsc
  have hg := isGoodPositionGermTame_of_sc hf hx hgsc
  exact hA.1 hf.isScSmooth.1 hg hx

#rt_check RoundTrip.V3_84.A_to_B_weak [Polyfold.theorem_3_54_tangentGermChart_proj,
  Polyfold.theorem_3_54_tangentGermChart, Polyfold.MChart.compDiffeo_isChart,
  Polyfold.MPolyfold.TangentGermChart.π_mem_of_projectsInto, Polyfold.isScInftyGermAt_of_lifts,
  Polyfold.StabilityData.ker_Dfs_le_smooth]

end RoundTrip.V3_84
