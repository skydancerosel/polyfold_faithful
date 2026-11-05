import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_100
import RoundTrip.Blind.V3_100_r2

/-!
Round trip for V3_100 (good position is surjectivity at a zero with `d_X = 0`), against the
**second blind statement** `RoundTrip.V3_100_r2.B` (2026-11-02).  `A` is the conjunction of the
types of the theorems among the decls (`StrongBundle.IsLinSurjAt` is a definition, vocabulary):
`isInGoodPositionIn_of_subset`, `StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero`,
`StrongBundle.isGoodPositionGerm_of_isLinSurjAt`, `StrongBundle.IsGoodPositionGerm.isLinSurjAt`,
`StrongBundle.isGoodPositionGerm_iff_isLinSurjAt`, `StrongBundle.IsLinSurjAt.linAt_surjective`,
universes instantiated at `0`, all in the germ reading.

* `A_to_B` (proved from the hypothesis `A`, its conjunct `isGoodPositionGerm_iff_isLinSurjAt`):
  at a zero with `d_X(x) = 0`, `B`'s `IsGoodPositionGermSc` (the project's Definition 3.53 with the
  sc-complement) is equivalent to `IsGoodPositionGermTame` by the non-banned
  `StrongBundle.isGoodPositionGermSc_iff` (sc-complement upgrade at a zero), and `A` makes the
  latter equivalent to `IsLinSurjAt`.  The `∂X = ∅` conjunct reduces to the `d_X(x) = 0` one by
  `MPolyfold.isWithoutBoundary_iff`.  `B`'s tame-bundle hypothesis is not needed.
* `B → A` fails genuinely: `B` speaks only of tame strong bundles and sections with tame germ data
  at a zero; `A` also states `IsGoodPositionGerm.isLinSurjAt` (any `d_X`, only an sc-smooth
  section, no tame chart), the non-centred-chart criterion
  `isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero` (only `IsScFredholmGerm` at the point),
  the chart independence `IsLinSurjAt.linAt_surjective` and the linear-algebra lemma
  `isInGoodPositionIn_of_subset`, and its equivalence needs no tame strong bundle.

The results against the first blind statement (`RoundTrip.V3_100.B`, whose good-position notion
was whole-chart) are kept with the suffix `_r1`.
-/

namespace RoundTrip.V3_100
open Polyfold Set

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isInGoodPositionIn_of_subset ∧
    type_of% @Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.isInGoodPositionIn_of_subset,
    @Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero.{0, 0},
    @Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt.{0, 0},
    @Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt.{0, 0},
    @Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt.{0, 0},
    @Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective.{0, 0}⟩

/-- **`A ⇒ B`** (second blind statement), from `A`'s `isGoodPositionGerm_iff_isLinSurjAt` and the
project's `isGoodPositionGermSc_iff` (sc-complement ⟺ algebraic complement at a zero). -/
theorem A_to_B (hA : A) : RoundTrip.V3_100_r2.B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx
  have key : PX.degIndex x = 0 → (Bd.IsGoodPositionGermSc f x ↔ Bd.IsLinSurjAt f x) := fun hd =>
    (StrongBundle.isGoodPositionGermSc_iff hf hx).trans (hA.2.2.2.2.1 hf hx hd)
  exact ⟨fun hb => key ((MPolyfold.isWithoutBoundary_iff PX).2 hb x), key⟩

/-! ### Results against the first blind statement `RoundTrip.V3_100.B` (`_r1`) -/

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- (From V3_94.)  B's good position (sc-complement, cone `T ∩ C`) gives the project's (algebraic
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

/-- (From V3_94, with `A`'s `isInGoodPositionIn_of_subset` taken from the hypothesis.)  `B`'s
`IsGoodPositionGermSc` (whole-chart data) at a zero of an sc-Fredholm section with tame germ data
gives `IsGoodPositionGermTameWholeChart`, in the same centred tame chart. -/
theorem isGoodPositionGermTameWholeChart_of_sc_r1
    (hsub : type_of% @Polyfold.isInGoodPositionIn_of_subset)
    {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (h : IsGoodPositionGermSc Bd f x) : Bd.IsGoodPositionGermTameWholeChart f x := by
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
  refine ⟨hxs, c, hct, hxV, hφ0, h0, g, s, hfill, hs, hs0,
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
      exact hsub hker (by rw [huniv]; exact subset_univ _)

/-- `B`'s `IsGoodPositionGermSc` gives the project's (germ-reading) `IsGoodPositionGermTame`. -/
theorem isGoodPositionGermTame_of_sc_r1 (hsub : type_of% @Polyfold.isInGoodPositionIn_of_subset)
    {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (h : IsGoodPositionGermSc Bd f x) : Bd.IsGoodPositionGermTame f x :=
  (isGoodPositionGermTameWholeChart_of_sc_r1 hsub hf hx h).isGoodPositionGermTame

end Glue

/-- **The `→` half of conjunct (a) of `B`**, from the hypothesis `A` (its conjuncts
`isInGoodPositionIn_of_subset` and `isGoodPositionGerm_iff_isLinSurjAt`). -/
theorem A_to_B_a_mp_r1 (hA : A) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (x : X),
      IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → PX.boundary = ∅ →
      IsZeroAt P f x →
        IsGoodPositionGermSc Bd f x → Bd.IsLinSurjAt f x := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hb hx hgp
  have hd : PX.degIndex x = 0 := (MPolyfold.isWithoutBoundary_iff PX).2 hb x
  exact (hA.2.2.2.2.1 hf hx hd).1 (isGoodPositionGermTame_of_sc_r1 hA.1 hf hx hgp)

/-- **The `←` half of conjunct (a) of `B` for sections with whole-chart tame germ data**, from the
hypothesis `A` (its conjunct `IsLinSurjAt.linAt_surjective`): with
`IsScFredholmSectionTameWholeChart f` (the audit's reading, stronger than B's germ-reading
hypothesis), `f'(x)` onto at a zero with `d_X(x) = 0` gives `B`'s whole-chart good position in the
tame chart of the data at `x`. -/
theorem A_to_B_a_mpr_wholeChart_r1 (hA : A) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X) (hfW : Bd.IsScFredholmSectionTameWholeChart f)
    (hd : PX.degIndex x = 0) (hx : IsZeroAt P f x) (hsurj : Bd.IsLinSurjAt f x) :
    IsGoodPositionGermSc Bd f x := by
  have hfs : Bd.IsScSmoothSection f := hfW.isScSmooth
  have hxs : x ∈ PX.smoothSet :=
    hfW.isScFredholmSectionTame.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hx
  obtain ⟨-, c, hct, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := hfW.germTame x hxs
  have h0O : (0 : c.φ.model.E 0) ∈ StrongRetr.r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x hxV
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x := by rw [map_zero, hφ0]
  have hlin := hA.2.2.2.2.2 hfs hx hsurj hct.1 hxV hz
  have hfr : IsSc1 c.U (c.principal f ∘ StrongRetr.r c.R) := hfs.isSc1_principal_comp_r hct.1
  refine ⟨c, h0, g, s, ⟨hct, hxV, hφ0, hfill, hs, hs0, fun k hk => ?_,
    fun h1 => absurd h1 (by omega)⟩, isConjugateToBasicGerm_iff_nonempty.1 hconj⟩
  have hk' : (c.φ x, k) ∈ c.K := by rw [hφ0]; exact hk
  obtain ⟨v, hv⟩ := hlin k hk'
  refine ⟨v.1, v.2, ?_⟩
  rw [← hv, linAt_eq_scDeriv c.relOpen c.isRetraction hfr hfill.isScSmooth.isSc1
    (by rw [map_zero]; exact h0O) (by rw [map_zero]; exact hfill.filler.eq_on) v]

#rt_check RoundTrip.V3_100.A_to_B [Polyfold.isInGoodPositionIn_of_subset,
  Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero,
  Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt,
  Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt,
  Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt,
  Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective]
#rt_overlap RoundTrip.V3_100.A_to_B [Polyfold.isInGoodPositionIn_of_subset,
  Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero,
  Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt,
  Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt,
  Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt,
  Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective]
#rt_check RoundTrip.V3_100.A_to_B_a_mp_r1 [Polyfold.isInGoodPositionIn_of_subset,
  Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero,
  Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt,
  Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt,
  Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt,
  Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective]
#rt_check RoundTrip.V3_100.A_to_B_a_mpr_wholeChart_r1 [Polyfold.isInGoodPositionIn_of_subset,
  Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero,
  Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt,
  Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt,
  Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt,
  Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective]

end RoundTrip.V3_100
