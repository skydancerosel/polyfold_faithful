import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_94
import RoundTrip.Blind.V3_94_r2

/-!
Round trip for V3_94 (Theorem 3.54 (1)–(2) with the text's hypotheses), against the **second
blind statement** `RoundTrip.V3_94_r2.B` (2026-11-02).  `A` is the conjunction of the types of
`Polyfold.theorem_3_54_one'`, `Polyfold.theorem_3_54'`,
`Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense`, `Polyfold.theorem_3_54_two`,
`Polyfold.StrongBundle.IsGoodPositionGerm.toTame`, `Polyfold.theorem_3_54_one_sc_of_tame`,
`Polyfold.theorem_3_54_one_sc` and `Polyfold.theorem_3_54_sc`, universes instantiated at `0`, all
in the text's germ reading; the last three use the text's sc-complement
(`StrongBundle.IsGoodPositionGermSc`), the notion `B` uses.

* `A_to_B` (proved from the hypothesis `A`): `A`'s `theorem_3_54_sc` applied to `B`'s hypotheses
  gives (1) verbatim and regular tangent germ data on `U = D.φ.source`; (2) is
  `theorem_3_23_of_nearby`'s argument run on `A`'s `theorem_3_54_two` at each zero (fed with
  `IsGoodPositionGermSc.isGoodPositionGermTame`, a forgetful projection),
  `TangentGermChart.shrink(_isRegular)` and Theorem 3.27, then
  `IsManifoldWithCorners.hasCornerStructure`.  `B`'s tame-bundle hypothesis is not needed.
* `B → A` fails genuinely: `A` needs no tame strong bundle, accepts the weaker (algebraic) good
  position at `x` (`theorem_3_54_one'`, `theorem_3_54'`, `theorem_3_54_one_sc_of_tame`), and
  contains chart-level lemmas (transfer to a tame chart, chart independence, regular tangent germ
  data of a common dimension) that `B` does not state.

The results against the first blind statement (`RoundTrip.V3_94.B`, whose good-position notion was
whole-chart) are kept with the suffix `_r1`.
-/
namespace RoundTrip.V3_94
open Polyfold Set

/-- The project's statement: Theorem 3.54 (1), (1)–(2), the chart independence of good position,
Theorem 3.54 (2), the transfer to a tame chart, and Theorem 3.54 (1)–(2) with the sc-complement,
universes at `0` (germ reading). -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_one'.{0, 0} ∧ type_of% @Polyfold.theorem_3_54'.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_two.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGerm.toTame.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_one_sc_of_tame.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_one_sc.{0, 0} ∧ type_of% @Polyfold.theorem_3_54_sc.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_one'.{0, 0}, @Polyfold.theorem_3_54'.{0, 0},
    @Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense.{0, 0},
    @Polyfold.theorem_3_54_two.{0, 0}, @Polyfold.StrongBundle.IsGoodPositionGerm.toTame.{0, 0},
    @Polyfold.theorem_3_54_one_sc_of_tame.{0, 0}, @Polyfold.theorem_3_54_one_sc.{0, 0},
    @Polyfold.theorem_3_54_sc.{0, 0}⟩

/-- **`A ⇒ B`** (second blind statement): (1) and the regular data from `A`'s `theorem_3_54_sc`;
(2) from `A`'s `theorem_3_54_two` at each zero and Theorem 3.27. -/
theorem A_to_B (hA : A) : RoundTrip.V3_94_r2.B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgsc
  obtain ⟨Vx, hVxo, hxVx, hall, d, D, hreg, hsub, hdim⟩ := hA.2.2.2.2.2.2.2 hf hgsc hx
  set U := D.φ.source with hU
  set S' := RoundTrip.V3_94_r2.zeroSetIn P f U with hS'
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := hA.2.2.2.1 hf.isScSmooth.1
      (hall y (hsub hy.1) hy.2).isGoodPositionGermTame hy.2 (D.φ.isOpen_source.inter hVxo)
      ⟨hy.1, hsub hy.1⟩ fun z hz hz0 => (hall z hz.2 hz0).isGoodPositionGermTame
    have hdy : dy = d := hdim y ⟨hy.2, hy.1⟩ dy Dy
    subst hdy
    have himage : Dy.φ '' (S' ∩ Dy.φ.source) =
        (fun v : Dy.N => (v : Dy.φ.model.E 0) + Dy.δ v) '' Dy.V := by
      rw [← Dy.image_eq]
      congr 1
      ext z
      constructor
      · rintro ⟨⟨-, hz0⟩, hzsrc⟩; exact ⟨hz0, hzsrc⟩
      · rintro ⟨hz0, hzsrc⟩; exact ⟨⟨(hsuby hzsrc).1, hz0⟩, hzsrc⟩
    exact ⟨Dy.shrink S' subset_rfl Dy.φ.isOpen_source Dy.mem_source Dy.V_relOpen Dy.zero_mem_V
      subset_rfl himage, Dy.shrink_isRegular S' subset_rfl Dy.φ.isOpen_source Dy.mem_source
      Dy.V_relOpen Dy.zero_mem_V subset_rfl himage hregy.isScSmooth hregy.π_mem⟩
  have hne : S'.Nonempty := ⟨x, D.mem_source, hx⟩
  obtain ⟨hsubM, -, hman, -⟩ := theorem_3_27 PX hne hS'reg
  have := PX.paracompactSpace_subtype S'
  exact ⟨U, D.φ.isOpen_source, D.mem_source, fun y hy => hall y (hsub hy.1) hy.2,
    hsubM, inferInstance, hman.hasCornerStructure⟩

/-! ### Results against the first blind statement `RoundTrip.V3_94.B` (`_r1`) -/

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- (From V3_95.)  B's good position (sc-complement, cone `T ∩ C`) gives the project's (algebraic
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

/-- `B` with conclusion (1) read in the text's germ sense (`StrongBundle.IsGoodPositionGermSc`,
the project's Definition 3.53 with the sc-complement, germ reading) instead of `B`'s whole-chart
`IsGoodPositionGermSc`; hypotheses and conclusion (2) are `B`'s. -/
def Bgerm_r1 : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        (∀ y ∈ zeroSetIn P f V, Bd.IsGoodPositionGermSc f y) ∧
        ∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f V)) (_ : ParacompactSpace (zeroSetIn P f V)),
          (PX.subPolyfold hS).HasCornerStructure

/-- **What `A` gives under `B`'s hypotheses**: `Bgerm_r1`.  (1) from `theorem_3_54'` and
`theorem_3_54_one_sc_of_tame`; (2) is `theorem_3_23_of_nearby`'s argument with `theorem_3_54'` and
`theorem_3_54_two` taken from the hypothesis `A`. -/
theorem A_to_Bgerm_r1 (hA : A) : Bgerm_r1 := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgsc
  have hg := isGoodPositionGermTame_of_sc_r1 hf hx hgsc
  obtain ⟨Vx, hVxo, hxVx, hall, d, D, hreg, hsub, hdim⟩ := hA.2.1 hf hg hx
  set U := D.φ.source with hU
  set S' := zeroSetIn P f U with hS'
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := hA.2.2.2.1 hf.isScSmooth.1 (hall y (hsub hy.1) hy.2)
      hy.2 (D.φ.isOpen_source.inter hVxo) ⟨hy.1, hsub hy.1⟩ fun z hz hz0 => hall z hz.2 hz0
    have hdy : dy = d := hdim y ⟨hy.2, hy.1⟩ dy Dy
    subst hdy
    have himage : Dy.φ '' (S' ∩ Dy.φ.source) =
        (fun v : Dy.N => (v : Dy.φ.model.E 0) + Dy.δ v) '' Dy.V := by
      rw [← Dy.image_eq]
      congr 1
      ext z
      constructor
      · rintro ⟨⟨-, hz0⟩, hzsrc⟩; exact ⟨hz0, hzsrc⟩
      · rintro ⟨hz0, hzsrc⟩; exact ⟨⟨(hsuby hzsrc).1, hz0⟩, hzsrc⟩
    exact ⟨Dy.shrink S' subset_rfl Dy.φ.isOpen_source Dy.mem_source Dy.V_relOpen Dy.zero_mem_V
      subset_rfl himage, Dy.shrink_isRegular S' subset_rfl Dy.φ.isOpen_source Dy.mem_source
      Dy.V_relOpen Dy.zero_mem_V subset_rfl himage hregy.isScSmooth hregy.π_mem⟩
  have hne : S'.Nonempty := ⟨x, D.mem_source, hx⟩
  obtain ⟨hsubM, -, hman, -⟩ := theorem_3_27 PX hne hS'reg
  have := PX.paracompactSpace_subtype S'
  have hsc : ∀ y ∈ S', Bd.IsGoodPositionGermSc f y := fun y hy => by
    obtain ⟨Vy, -, hyVy, hally⟩ := hA.2.2.2.2.2.1 hf (hall y (hsub hy.1) hy.2) hy.2
    exact hally y hyVy hy.2
  exact ⟨U, D.φ.isOpen_source, D.mem_source, hsc, hsubM, inferInstance, hman.hasCornerStructure⟩

/-- `B`'s conclusion (1) (whole-chart good position) implies the germ one: `B ⇒ Bgerm_r1`. -/
theorem B_to_Bgerm_r1 (hB : B) : Bgerm_r1 := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x htame hf hx hgsc
  obtain ⟨V, hVo, hxV, hall, hrest⟩ := hB PX P Bd f x htame hf hx hgsc
  exact ⟨V, hVo, hxV, fun y hy =>
    (isGoodPositionGermTame_of_sc_r1 hf hy.2 (hall y hy)).isGoodPositionGermSc hf hy.2, hrest⟩


#rt_check RoundTrip.V3_94.A_to_B [Polyfold.theorem_3_54_one', Polyfold.theorem_3_54',
  Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense, Polyfold.theorem_3_54_two,
  Polyfold.StrongBundle.IsGoodPositionGerm.toTame, Polyfold.theorem_3_54_one_sc_of_tame,
  Polyfold.theorem_3_54_one_sc, Polyfold.theorem_3_54_sc]
#rt_overlap RoundTrip.V3_94.A_to_B [Polyfold.theorem_3_54_one', Polyfold.theorem_3_54',
  Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense, Polyfold.theorem_3_54_two,
  Polyfold.StrongBundle.IsGoodPositionGerm.toTame, Polyfold.theorem_3_54_one_sc_of_tame,
  Polyfold.theorem_3_54_one_sc, Polyfold.theorem_3_54_sc]
#rt_check RoundTrip.V3_94.A_to_Bgerm_r1 [Polyfold.theorem_3_54_one', Polyfold.theorem_3_54',
  Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense, Polyfold.theorem_3_54_two,
  Polyfold.StrongBundle.IsGoodPositionGerm.toTame, Polyfold.theorem_3_54_one_sc_of_tame,
  Polyfold.theorem_3_54_one_sc, Polyfold.theorem_3_54_sc]

end RoundTrip.V3_94
