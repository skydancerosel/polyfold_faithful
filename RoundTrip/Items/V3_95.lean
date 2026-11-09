import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_95

/-!
Round trip for V3_95 (Theorems 3.23 and 3.19 with the text's hypotheses).  `A` is the conjunction of
the types of `Polyfold.theorem_3_1_26'`, `Polyfold.theorem_3_1_22'`, `Polyfold.theorem_3_1_26_of_nearby`
and `Polyfold.lemma_2_4_6`, universes instantiated at `0`.

Glue for `A → B`:
* (3.23) B's `IsSurjGoodPosAt` (in a not necessarily centred tame chart, sc-complement) gives A's
  `IsGoodPositionGermTame` (`StrongBundle.isGoodPositionGerm_of_linAt_surj` on `Lin(z)`,
  `IsGoodPositionGerm.toTame`); `IsManifoldWithCorners d` gives `HasCornerStructure`; B's
  uniqueness clause `CornerStructureUnique` holds for every M-polyfold (two atlases equivalent to
  the same atlas are equivalent: their charts are charts of the structure, `IsChart.compatible`).
* (3.19) `IsLinSurjAt` at `x₀` with `d_X ≡ 0` gives `IsGoodPositionGermTame`
  (`StrongBundle.isGoodPositionGerm_of_isLinSurjAt`); `IsManifoldWithCorners d` and `d_S ≡ 0` give
  B's atlas of charts onto open subsets of finite-dimensional spaces (`boundaryless_of_loc`).

**Refresh 2026-11-02 (germ reading at HEAD).**  `theorem_3_1_26'`, `theorem_3_1_22'` and
`theorem_3_1_26_of_nearby` now state the germ reading, and A gains `theorem_3_1_26_sc` (good position
with the text's sc-complement).  A ⇒ B still goes through `theorem_3_1_26'` and `theorem_3_1_22'`; the
chart change `isGoodPositionGermTame_of_B` was repaired (`isGoodPositionGerm_of_linAt_surj` on
`Lin(z)`).  B ⇒ A still fails.
-/

namespace RoundTrip.V3_95
open Polyfold Set

/-- The project's statement: Theorems 3.23', 3.19', 3.23 (nearby form), Lemma 2.26 and Theorem 3.23
with the sc-complement form of good position (all germ reading), universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_1_26'.{0, 0} ∧ type_of% @Polyfold.theorem_3_1_22'.{0, 0} ∧
    type_of% @Polyfold.theorem_3_1_26_of_nearby.{0, 0} ∧ type_of% @Polyfold.lemma_2_4_6.{0} ∧
    type_of% @Polyfold.theorem_3_1_26_sc.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_1_26'.{0, 0}, @Polyfold.theorem_3_1_22'.{0, 0},
    @Polyfold.theorem_3_1_26_of_nearby.{0, 0}, @Polyfold.lemma_2_4_6.{0},
    @Polyfold.theorem_3_1_26_sc.{0, 0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- B's good position (sc-complement, cone `T ∩ C`) gives the project's (algebraic complement,
cone `C`). -/
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

/-- B's hypothesis at a zero gives the project's `IsGoodPositionGermTame` (germ reading): the
chart-change lemma `StrongBundle.isGoodPositionGerm_of_linAt_surj` (hypotheses on
`Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}` in the not necessarily centred chart `c`; its kernel, pushed into
`E₀`, is `ker D(f̂ ∘ r)(z) ∩ T_zO`), then `IsGoodPositionGerm.toTame` with the tame germ data. -/
theorem isGoodPositionGermTame_of_B {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (h : IsSurjGoodPosAt Bd f x) : Bd.IsGoodPositionGermTame f x := by
  obtain ⟨c, hct, hxV, z₁, hz, hsurj, n, W, Tp, hC, hgp⟩ := h
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx
  have hker : (LinearMap.ker (linAt c.U c.R (c.principal f) z₁ :
        ↥(rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)).subtype =
        LinearMap.ker (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
          c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) := by
    ext w
    simp only [Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      Submodule.mem_map, Submodule.subtype_apply, linAt_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, v.2⟩
    · rintro ⟨hw, hwT⟩
      exact ⟨⟨w, hwT⟩, hw, rfl⟩
  refine (StrongBundle.isGoodPositionGerm_of_linAt_surj hf.isScSmooth (hf.germ x hxs) hx hct.1
    hxV hz Tp hC (fun k hk => ?_) (hker ▸ isInGoodPositionIn_of_sc hgp)).toTame hf.isScSmooth
    (hf.germTame x hxs) hx
  obtain ⟨v, hv, hvk⟩ := hsurj k hk
  exact ⟨⟨v, hv⟩, hvk⟩

end Glue

section Glue2

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {QZ : MPolyfold Z}

/-- A chart of `QZ` modelled on a relatively open subset of a partial quadrant in a
finite-dimensional space, at a point `z` with `d(z) = 0`, gives a chart of `QZ` around `z` onto an
open subset of `E₀` with the constant structure and `C = univ`. -/
theorem exists_open_chart {χ : MChart Z} (hχ : QZ.IsChart χ)
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O)
    (hfin : FiniteDimensional ℝ (χ.model.E 0)) {z : Z} (hz : z ∈ χ.source)
    (hd : QZ.degIndex z = 0) :
    ∃ χ' : MChart Z, QZ.IsChart χ' ∧ z ∈ χ'.source ∧
      ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
        (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
        χ'.model = LocalModel.ofRelOpen hU := by
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨G, hG, hOG⟩ := hU.relOpen
  -- `d_C(χ z) = 0`: the chart is a tame retract
  have htame : IsTameRetract χ.model.E χ.model.C χ.model.O :=
    ⟨ScRetraction.id hU, image_id _, ScRetraction.id_isTame _⟩
  have hdeg : degIndexWith T (χ z) = 0 := by
    have h1 := QZ.degIndex_eq_chartDegIndex_of_isTameRetract hχ htame hz
    rw [hd, MPolyfold.chartDegIndex, degIndex_eq T hT (χ.apply_mem_C hz)] at h1
    exact h1.symm
  have hcoord : ∀ i, (T 0 (χ z)).1 i ≠ 0 := by
    simp only [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies] at hdeg
    exact hdeg
  -- the open set where all quadrant coordinates are positive
  set W' : Set (χ.model.E 0) := {v | ∀ i, 0 < (T 0 v).1 i} with hW'
  have hW'o : IsOpen W' := by
    have : W' = ⋂ i, (fun v => (T 0 v).1 i) ⁻¹' Ioi 0 := by ext v; simp [hW']
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage
      ((continuous_apply i).comp (continuous_fst.comp (T 0).continuous))
  have hW'C : W' ⊆ χ.model.C := fun v hv => by
    rw [hT]; exact fun i => (hv i).le
  have hzW' : χ z ∈ W' := by
    have hzC := χ.apply_mem_C hz
    rw [hT] at hzC
    exact fun i => lt_of_le_of_ne (hzC i) (hcoord i).symm
  -- restrict the chart
  set s : Set Z := χ.source ∩ χ ⁻¹' W' with hs
  have hss : s ⊆ χ.source := inter_subset_left
  have hso : IsOpen s := χ.continuousOn_toFun.isOpen_inter_preimage χ.isOpen_source hW'o
  have himg : χ '' s = χ.model.O ∩ W' := by
    rw [hs, image_inter_preimage, χ.image_source]
  have hopen : IsOpen (χ '' s) := by
    rw [himg, hOG, inter_assoc, inter_eq_right.2 hW'C]
    exact hG.inter hW'o
  set χ₁ := χ.restrict hss hso with hχ₁
  have hχ₁c : QZ.IsChart χ₁ := MPolyfold.IsChart.restrict QZ hχ hss hso
  -- the identity onto the constant structure with `C = univ`
  have hU₁ : IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' s) :=
    ⟨hU.isPartialQuadrant, χ '' s, hopen,
      (inter_eq_left.2 ((χ.image_subset_model hss).trans χ.model.O_subset_C)).symm⟩
  have hU₂ : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) univ (χ '' s) :=
    ⟨isPartialQuadrant_univ _, χ '' s, hopen, (inter_univ _).symm⟩
  have d := hU₁.isScDiffeoQuadrant_toConst
  have h : IsScDiffeoQuadrant hU₁ hU₂ (id : χ.model.E 0 → (ScBanach.const (χ.model.E 0)) 0)
      (id : (ScBanach.const (χ.model.E 0)) 0 → χ.model.E 0) :=
    ⟨d.isScSmooth, d.isScSmooth_inv, d.mapsTo, d.mapsTo_inv, d.left_inv, d.right_inv⟩
  have hU₃ : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) univ
      ((id : χ.model.E 0 → (ScBanach.const (χ.model.E 0)) 0) '' (χ '' s)) := by
    rw [image_id]; exact hU₂
  refine ⟨χ₁.compDiffeo h subset_rfl hU₃.isScRetract, MChart.compDiffeo_isChart hχ₁c h subset_rfl _,
    ⟨hz, hzW'⟩, χ.model.E 0, inferInstance, inferInstance, hfin, _, hU₃, rfl⟩

/-- `IsManifoldWithCornersLoc` and `d ≡ 0` give B's boundaryless manifold structure. -/
theorem boundaryless_of_loc (hc : QZ.IsManifoldWithCornersLoc) (hb : QZ.IsWithoutBoundary) :
    HasBoundarylessManifoldStructure QZ := by
  obtain ⟨A, hA, hcA⟩ := hc
  let A' : MAtlas Z :=
    { charts := {χ | QZ.IsChart χ ∧ ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
        (_ : FiniteDimensional ℝ V) (U : Set V)
        (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U), χ.model = LocalModel.ofRelOpen hU}
      compatible := fun φ hφ ψ hψ => MPolyfold.IsChart.compatible QZ hφ.1 hψ.1
      cover := fun z => by
        obtain ⟨χ, hχA, hz⟩ := A.cover z
        obtain ⟨χ', hχ', hz', hrest⟩ := exists_open_chart (QZ.isChart_of_mem_equiv hA hχA)
          (hcA χ hχA).1 (hcA χ hχA).2 hz (hb z)
        exact ⟨χ', ⟨hχ', hrest⟩, hz'⟩ }
  exact ⟨A', (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩

/-- B's uniqueness clause holds for every M-polyfold. -/
theorem cornerStructureUnique (QZ : MPolyfold Z) : CornerStructureUnique QZ :=
  fun _ _ h₁ h₂ _ _ => (MAtlas.equiv_iff _ _).2 fun _ hφ _ hψ =>
    MPolyfold.IsChart.compatible QZ (QZ.isChart_of_mem_equiv h₁ hφ) (QZ.isChart_of_mem_equiv h₂ hψ)

end Glue2

theorem A_to_B : A → B := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgood
    obtain ⟨U, hUo, hxU, -, hsm, d, hsub, h1, h2⟩ :=
      hA.1 hf hx (isGoodPositionGermTame_of_B hf hx hgood)
    have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
    exact ⟨U, hUo, hxU, fun y hy => hsm y hy.1 hy.2, hsub, inferInstance, h1,
      h2.hasCornerStructure, cornerStructureUnique _⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd f x₀ _ hf hX hx₀ hsurj
    obtain ⟨U, hUo, hxU, -, -, d, hsub, h1, h2⟩ :=
      hA.2.1 hX hf hx₀ (StrongBundle.isGoodPositionGerm_of_isLinSurjAt hf hx₀ (hX x₀) hsurj)
    have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
    exact ⟨U, hUo, hxU, hsub, inferInstance, boundaryless_of_loc h1.isManifoldWithCornersLoc h2⟩

#rt_check RoundTrip.V3_95.A_to_B [Polyfold.theorem_3_1_26', Polyfold.theorem_3_1_22',
  Polyfold.theorem_3_1_26_of_nearby, Polyfold.lemma_2_4_6, Polyfold.theorem_3_1_26_sc]

end RoundTrip.V3_95
