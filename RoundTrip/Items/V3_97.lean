import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_97

/-!
Round trip for V3_97 (the dimension of the solution set is the Fredholm index), refreshed
2026-11-02 against HEAD (germ reading).  `A` is the conjunction of the types of
`theorem_3_54_tangentGermChart_index`, `theorem_3_54_tangentGermChart_solutionSet_index`,
`theorem_3_54_two_index`, `theorem_3_23_index`, `theorem_3_19_index`, `theorem_3_57_index`,
`theorem_3_54_graph_proj_conj`, `theorem_3_54_tangentGermChart_proj_conj` and
`StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`, universes instantiated at `0`.

Neither direction is proved.  What is proved from the hypothesis `A`:
* `A_to_B_354_part`: under the hypotheses of `B`'s second conjunct (3.54), an open `V ∋ x` and `d`
  with `dim ker f'(x) = d` in **every** strong bundle chart around `x` (`B`'s `KerDimInChart`,
  exactly), and the project's tangent germ datum (Definition 3.25 (2), `TangentGermChart`) of
  `S(f, V)` at `x` of dimension `d`.  Glue: `B`'s `IsGoodPositionGermSc` (whole-chart data) gives
  the project's `IsGoodPositionGermTameWholeChart`, hence the germ-reading
  `IsGoodPositionGermTame` (from V3_94); `A`'s `theorem_3_54_tangentGermChart_index` gives the
  datum and `IsSurjLinOfIndex f x d`; the latter gives `KerDimInChart`.
* `chartLinScFredholm_of_isSurjLinOfIndex` (new conjunct
  `linAt_isScFredholm_of_isSurjLinOfIndex`): at a zero of an sc-Fredholm section with
  `IsSurjLinOfIndex f x d`, `f'(x)` is sc-Fredholm of index `d` in every chart in B's sense
  (`ChartLinScFredholm`).  This closes the audit's "level-0 only" gap of B's (3.19) conjunct.

The gaps to `A → B`:
* (3.54) `B` asks for the text's `d`-dimensional tangent germ property of `S(f, V)` at **every**
  point (`HasTangentGermPropertyB`: an sc-complement `Yc` of `N`, one sc-smooth germ `δ`), while
  the project's `TangentGermChart` has a closed algebraic complement and a level/order-dependent
  germ reading; the translation is the open half of V3_22 (needs a germ form of Proposition 1.19),
  not glue.
* (3.19) `B` assumes only `IsScFredholmSection` (germ data in some chart, no tameness) and
  `IsLinSurjAt`, while `A`'s `theorem_3_19_index` needs tame germ data (`IsScFredholmSectionTame`)
  and good position in a tame chart, which the project cannot produce from `B`'s hypotheses (as in
  V3_68/V3_101).
-/

namespace RoundTrip.V3_97
open Polyfold Set StrongRetr

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_tangentGermChart_index.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_tangentGermChart_solutionSet_index.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_two_index.{0, 0} ∧
    type_of% @Polyfold.theorem_3_23_index.{0, 0} ∧
    type_of% @Polyfold.theorem_3_19_index.{0, 0} ∧
    type_of% @Polyfold.theorem_3_57_index.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_graph_proj_conj.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_tangentGermChart_proj_conj.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_tangentGermChart_index.{0, 0},
    @Polyfold.theorem_3_54_tangentGermChart_solutionSet_index.{0, 0},
    @Polyfold.theorem_3_54_two_index.{0, 0}, @Polyfold.theorem_3_23_index.{0, 0},
    @Polyfold.theorem_3_19_index.{0, 0}, @Polyfold.theorem_3_57_index.{0, 0},
    @Polyfold.theorem_3_54_graph_proj_conj.{0, 0},
    @Polyfold.theorem_3_54_tangentGermChart_proj_conj.{0, 0},
    @Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex.{0, 0}⟩

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

/-- (From V3_94.)  `B`'s `IsGoodPositionGermSc` (whole-chart data) at a zero of an sc-Fredholm
section with tame germ data gives `IsGoodPositionGermTameWholeChart`, in the same centred tame
chart. -/
theorem isGoodPositionGermTameWholeChart_of_sc {Bd : StrongBundle PX P} {f : X → Y}
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
    · have hd0 : PX.degIndex x = 0 := by omega
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

/-- `B`'s `IsGoodPositionGermSc` gives the project's (germ-reading) `IsGoodPositionGermTame`. -/
theorem isGoodPositionGermTame_of_sc {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (h : IsGoodPositionGermSc Bd f x) : Bd.IsGoodPositionGermTame f x :=
  (isGoodPositionGermTameWholeChart_of_sc hf hx h).isGoodPositionGermTame

/-- **`dim ker f'(x) = d` in every chart** (`B`'s `KerDimInChart`) from the project's
`IsSurjLinOfIndex f x d` at a smooth zero. -/
theorem kerDimInChart_of_isSurjLinOfIndex {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScSmoothSection f) {x : X} (hx : IsZeroAt P f x) (hxs : x ∈ PX.smoothSet)
    {d : ℕ} (hI : Bd.IsSurjLinOfIndex f x d) {c : StrongBundleChart PX P} (hc : Bd.IsChart c)
    (hxV : x ∈ c.φ.source) : KerDimInChart c f x d := by
  have hx1 : x ∈ PX.levelSet 1 := mem_iInter.1 hxs 1
  obtain ⟨z, hz⟩ := (PX.mem_levelSet_iff c.isChart hxV).1 hx1
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model x hxV
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨L, -, hL, -⟩ := StrongBundle.linAt_chart_independence hf hc hc hxV hxV hx hz hz hzU hzU
    T hT T hT
  obtain ⟨-, hF, -, hdim⟩ := hI c hc hxV z hz hzU L hL
  have hker : linKerB c f z = (LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
      ↥(rangeS (ρCLM c.isRetraction hzU)))).map (rangeS (scDeriv c.U (r c.R) z)).subtype := by
    ext v
    simp only [linKerB, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      Submodule.mem_map, Submodule.subtype_apply]
    constructor
    · rintro ⟨hv, hvT⟩
      refine ⟨⟨v, hvT⟩, Subtype.ext ?_, rfl⟩
      rw [hL]
      exact hv
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, w.2⟩
      have := congrArg Subtype.val hw
      rw [hL] at this
      exact this
  have hfin : FiniteDimensional ℝ (LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
      ↥(rangeS (ρCLM c.isRetraction hzU)))) := hF.finite_ker
  have he := Submodule.equivMapOfInjective _ (rangeS (scDeriv c.U (r c.R) z)).injective_subtype
    (LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
      ↥(rangeS (ρCLM c.isRetraction hzU))))
  refine ⟨z, hz, ?_, ?_⟩
  · rw [hker]; exact LinearEquiv.finiteDimensional he
  · rw [hker, ← he.finrank_eq, hdim]

omit [T2Space Y] [ParacompactSpace Y] in
/-- The conclusion of `linAt_isScFredholm(_of_isSurjLinOfIndex)` in a chart gives B's
`ChartLinScFredholm` there. -/
lemma chartLin_of (f : X → Y) (x : X) (c : StrongBundleChart PX P) (hxV : x ∈ c.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
    (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
    (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
    (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
    (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU))
    (hsc : IsScFredholm (hD.toScOperator.restrict hT hK hTK)) :
    ChartLinScFredholm c f x (fredholmIndex (hD.toScOperator.restrict hT hK hTK 0)) := by
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model x hxV
  set T := hD.toScOperator.restrict hT hK hTK with hTdef
  have hL : IsScOperator (T 0) := T.isScOperator
  have hLT : hL.toScOperator = T := ScOperator.ext_base (by rw [hL.toScOperator_zero])
  refine ⟨z, hz, rangeS (ρCLM c.isRetraction hzU), ?_, hT, hK, T 0, ?_, hL, ?_, ?_⟩
  · ext h
    rw [SetLike.mem_coe, mem_rangeS_ρCLM_iff c.isRetraction hzO hzU, hz]
    rfl
  · intro v
    change hD.toScOperator 0 v.1 = _
    rw [hD.toScOperator_zero]
  · rw [hLT]; exact hsc
  · rw [hLT, scIndex_eq_fredholmIndex]

end Glue

/-- **`f'(x)` is sc-Fredholm of index `d` in every chart** (B's `ChartLinScFredholm c f x d`), from
the hypothesis `A` (conjunct `linAt_isScFredholm_of_isSurjLinOfIndex`), at a zero of an
sc-Fredholm section with `IsSurjLinOfIndex f x d`. -/
theorem chartLinScFredholm_of_isSurjLinOfIndex (hA : A) {X : Type} [TopologicalSpace X]
    [T2Space X] [ParacompactSpace X] {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y]
    [T2Space Y] [ParacompactSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSection f) {x : X} (hx0 : IsZeroAt P f x) {d : ℕ}
    (hI : Bd.IsSurjLinOfIndex f x d) {c : StrongBundleChart PX P} (hc : Bd.IsChart c)
    (hxV : x ∈ c.φ.source) : ChartLinScFredholm c f x d := by
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  have hz : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) = c.φ x :=
    PX.toBase_levelLift c.isChart hxV (Set.mem_iInter.1 hxs 1)
  have hzU : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) ∈ c.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model x hxV)
  obtain ⟨hD, hT, hK, hTK, -, hsc, hlvl⟩ := hA.2.2.2.2.2.2.2.2 hf hx0 hI hc hxV hz hzU
  have := chartLin_of f x c hxV _ hz hzU hD hT hK hTK hsc
  rwa [(hlvl 0).2.2] at this

/-- **What `A` gives under the hypotheses of `B`'s (3.54) conjunct**: `dim ker f'(x) = d` in every
chart (`B`'s `KerDimInChart`) and the project's tangent germ datum of `S(f, V)` at `x` of
dimension `d` (in place of `B`'s `HasTangentGermPropertyB` at every point). -/
theorem A_to_B_354_part (hA : A) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (x : X),
      IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
      IsGoodPositionGermSc Bd f x →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
          ∃ d : ℕ, (∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
              KerDimInChart c f x d) ∧
            Nonempty (PX.TangentGermChart (zeroSetIn P f V) x d) := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgsc
  have hg := isGoodPositionGermTame_of_sc hf hx hgsc
  obtain ⟨Vx, d, hVo, hxV, ⟨D, -⟩, hI⟩ := hA.1 hf.isScSmooth hg hx
  exact ⟨Vx, hVo, hxV, d, fun c hc hxc => kerDimInChart_of_isSurjLinOfIndex hf.isScSmooth hx
    (hf.mem_smoothSet_of_isZeroAt hx) hI hc hxc, ⟨D⟩⟩

#rt_check RoundTrip.V3_97.A_to_B_354_part [Polyfold.theorem_3_54_tangentGermChart_index,
  Polyfold.theorem_3_54_tangentGermChart_solutionSet_index, Polyfold.theorem_3_54_two_index,
  Polyfold.theorem_3_23_index, Polyfold.theorem_3_19_index, Polyfold.theorem_3_57_index,
  Polyfold.theorem_3_54_graph_proj_conj, Polyfold.theorem_3_54_tangentGermChart_proj_conj,
  Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex]
#rt_check RoundTrip.V3_97.chartLinScFredholm_of_isSurjLinOfIndex [
  Polyfold.theorem_3_54_tangentGermChart_index,
  Polyfold.theorem_3_54_tangentGermChart_solutionSet_index, Polyfold.theorem_3_54_two_index,
  Polyfold.theorem_3_23_index, Polyfold.theorem_3_19_index, Polyfold.theorem_3_57_index,
  Polyfold.theorem_3_54_graph_proj_conj, Polyfold.theorem_3_54_tangentGermChart_proj_conj,
  Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex]

end RoundTrip.V3_97
