import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_82
import RoundTrip.Blind.V3_82_r2

/-!
Round trip for V3_82 (Theorem 3.54 (1) at the nearby zeros, first form), against the **second
blind statement** `RoundTrip.V3_82_r2.B` (2026-11-02).  `A` is the conjunction of the types of
`Polyfold.theorem_3_6_8_one`, `Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm`
(universes `0, 0`) and `Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ`
(`IsGoodPositionGermFilled` is vocabulary), all in the text's germ reading.

* `A_to_B` (proved from the hypothesis `A`, its first conjunct): `B`'s hypothesis
  `Bd.IsGoodPositionGermSc f x` (the project's Definition 3.53 with the sc-complement, germ
  reading) gives `IsGoodPositionGermTame` (forgetful), hence the filler condition of
  `theorem_3_6_8_one` (the non-banned `isGoodPositionGermFilled_of_isGoodPositionGerm`);
  `theorem_3_6_8_one` gives `IsGoodPositionGermTame` at the zeros near `x`, and the non-banned
  `IsGoodPositionGermTame.isGoodPositionGermSc` upgrades it to `B`'s sc-complement form.  `B`'s
  tame-bundle hypothesis is not needed.
* `B → A` fails genuinely: `theorem_3_6_8_one` assumes no tame strong bundle (only tame germ data
  at the smooth points) — getting it from `B` would need restricting the bundle to an open set
  covered by tame charts, a construction neither side states — and `A`'s other two conjuncts (the
  forgetful projection of the filler condition and a chart-level surjectivity lemma) are not
  statements of `B`.

The results against the first blind statement (`RoundTrip.V3_82.B`, whose good-position notion was
whole-chart) are kept with the suffix `_r1`.
-/
namespace RoundTrip.V3_82
open Polyfold Set

/-- The project's statement: Theorem 3.54 (1) under the filler condition, its corollary that the
strengthened good position is good position, and the surjectivity of `Tf̃(z₀)` from condition (3)
of Definition 3.4 (germ reading). -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_6_8_one.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm.{0, 0} ∧
    type_of% @Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_6_8_one.{0, 0},
    @Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm.{0, 0},
    @Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ⟩

/-- **`A ⇒ B`** (second blind statement), from the first conjunct of `A`. -/
theorem A_to_B (hA : A) : RoundTrip.V3_82_r2.B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgsc
  have hfill := isGoodPositionGermFilled_of_isGoodPositionGerm hf hgsc.isGoodPositionGermTame hx
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := hA.1 hf hfill hx
  exact ⟨Vx, hVxo, hxVx, fun y hy => (hall y hy.1 hy.2).isGoodPositionGermSc hf hy.2⟩

/-! ### Results against the first blind statement `RoundTrip.V3_82.B` (`_r1`) -/

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
theorem isGoodPositionGermTame_of_sc_r1 {Bd : StrongBundle PX P} {f : X → Y}
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


/-- `B` with the conclusion read in the text's germ sense: at the zeros near `x` the germ is in
good position with the sc-complement in the project's germ reading (`StrongBundle.IsGoodPositionGermSc`),
instead of `B`'s whole-chart `IsGoodPositionGermSc`.  The hypotheses are `B`'s. -/
def Bgerm_r1 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ zeroSetIn P f V, Bd.IsGoodPositionGermSc f y

/-- **What `A` gives under `B`'s hypotheses**: `Bgerm_r1` (the text's germ reading of the
conclusion), from the first conjunct of `A`. -/
theorem A_to_Bgerm_r1 (hA : A) : Bgerm_r1 := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgsc
  have hg := isGoodPositionGermTame_of_sc_r1 hf hx hgsc
  have hfill := isGoodPositionGermFilled_of_isGoodPositionGerm hf hg hx
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := hA.1 hf hfill hx
  exact ⟨Vx, hVxo, hxVx, fun y hy =>
    (hall y hy.1 hy.2).isGoodPositionGermSc hf hy.2⟩

/-- `B`'s conclusion (whole-chart good position) implies the germ one: `B ⇒ Bgerm_r1`. -/
theorem B_to_Bgerm_r1 (hB : B) : Bgerm_r1 := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x htame hf hx hgsc
  obtain ⟨V, hVo, hxV, hall⟩ := hB PX P Bd f x htame hf hx hgsc
  exact ⟨V, hVo, hxV, fun y hy =>
    (isGoodPositionGermTame_of_sc_r1 hf hy.2 (hall y hy)).isGoodPositionGermSc hf hy.2⟩


#rt_check RoundTrip.V3_82.A_to_B [Polyfold.theorem_3_6_8_one,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm,
  Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ]
#rt_overlap RoundTrip.V3_82.A_to_B [Polyfold.theorem_3_6_8_one,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm,
  Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ]
#rt_check RoundTrip.V3_82.A_to_Bgerm_r1 [Polyfold.theorem_3_6_8_one,
  Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm,
  Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ]

end RoundTrip.V3_82
