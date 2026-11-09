import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_69

/-!
Round trip for V3_69 (Theorem 3.23).  `A` is the conjunction of the types of
`Polyfold.theorem_3_1_26_of_nearby`, `Polyfold.theorem_3_1_26`, `Polyfold.theorem_3_6_8_two` and
`Polyfold.theorem_3_2_3_of_isRegular`, universes instantiated at `0` (`subPolyfold`, `IsManifoldWithCorners` are
vocabulary).

Glue for `A → B` (through A's `theorem_3_1_26`):
* B's hypothesis `IsSurjGoodPosAt` (surjectivity onto `K_z` and good position with an
  *sc*-complement, in some tame chart around `x`) gives `IsGoodPositionGermTame` at `x` by the
  project's chart-change lemma `StrongBundle.isGoodPositionGerm_of_linAt_surj` (on `Lin(z)`) and
  `IsGoodPositionGerm.toTame` (as in V3_70).
* A's `theorem_3_1_26` assumes `IsGoodPositionGermFilled`; it follows from the tame good position
  by the project lemma `isGoodPositionGermFilled_of_isGoodPositionGerm` (Finding 174).
* `IsManifoldWithCorners d` gives `HasCornerStructure` (`hasCornerStructure_iff_finiteDimensional`).
* B's `CornerStructureUnique` holds for every M-polyfold: two atlases equivalent to the same atlas
  consist of charts of the structure, which are pairwise compatible (`IsChart.compatible`).

**Refresh 2026-11-02 (germ reading at HEAD).**  `theorem_3_1_26_of_nearby`, `theorem_3_1_26` and
`theorem_3_6_8_two` now state the germ reading (the former `…_germ` statements); B's
`IsScFredholmSectionTame` is the germ reading too.  The chart change `isGoodPositionGermTame_of_B`
was repaired (germ form: `isGoodPositionGerm_of_linAt_surj` on `Lin(z)`); the rest of the proof
(germ form of `isGoodPositionGermFilled_of_isGoodPositionGerm`, then A's `theorem_3_1_26`) is
unchanged.  B ⇒ A still fails.
-/

namespace RoundTrip.V3_69
open Polyfold

/-- The project's statement: the theorems listed for Theorem 3.23, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_1_26_of_nearby.{0, 0} ∧ type_of% @Polyfold.theorem_3_1_26.{0, 0} ∧
    type_of% @Polyfold.theorem_3_6_8_two.{0, 0} ∧ type_of% @Polyfold.theorem_3_2_3_of_isRegular.{0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_1_26_of_nearby.{0, 0}, @Polyfold.theorem_3_1_26.{0, 0},
    @Polyfold.theorem_3_6_8_two.{0, 0}, @Polyfold.theorem_3_2_3_of_isRegular.{0}⟩

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

/-- B's uniqueness clause holds for every M-polyfold. -/
theorem cornerStructureUnique_all {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) : CornerStructureUnique QZ := by
  intro A₁ A₂ h₁ h₂ _ _
  rw [MAtlas.equiv_iff]
  intro φ hφ ψ hψ
  exact MPolyfold.IsChart.compatible QZ (QZ.isChart_of_mem_equiv h₁ hφ)
    (QZ.isChart_of_mem_equiv h₂ hψ)

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx hgood
  have hg : Bd.IsGoodPositionGermTame f x := isGoodPositionGermTame_of_B hf hx hgood
  have hfill := isGoodPositionGermFilled_of_isGoodPositionGerm hf hg hx
  obtain ⟨U, hUo, hxU, -, hsm, d, hsub, h1, h2⟩ := hA.2.1 hf hx hfill
  have := PX.paracompactSpace_subtype {y | y ∈ U ∧ IsZeroAt P f y}
  exact ⟨U, hUo, hxU, fun y hy => hsm y hy.1 hy.2, hsub, inferInstance, h1,
    MPolyfold.hasCornerStructure_iff_finiteDimensional.2 h2.isManifoldWithCornersLoc,
    cornerStructureUnique_all _⟩

#rt_check RoundTrip.V3_69.A_to_B [Polyfold.theorem_3_1_26_of_nearby, Polyfold.theorem_3_1_26,
  Polyfold.theorem_3_6_8_two, Polyfold.theorem_3_2_3_of_isRegular]

end RoundTrip.V3_69
