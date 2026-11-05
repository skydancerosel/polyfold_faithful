import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_87

/-!
Round trip for V3_87 (Theorem 3.57).  `A` is the conjunction of the types of
`Polyfold.theorem_3_57`, `Polyfold.theorem_3_57_dim` and `Polyfold.theorem_3_27_loc`, universes
instantiated at `0` (`solutionSetDim` is vocabulary).

Glue for `A → B`:
* B's hypothesis `IsSurjGoodPosAt` (surjectivity of `D(f̂ ∘ r)(z)|_{T_zO}` onto `K_z` and good
  position of `ker ∩ T_zO` with an *sc*-complement, in some tame chart around `x`, not necessarily
  centred) gives A's `IsGoodPositionGermTame` at `x` by the project's chart-change lemma
  `StrongBundle.isGoodPositionGerm_of_linAt_surj` (on `Lin(z)`) and `IsGoodPositionGerm.toTame`
  (with the tame germ data of `IsScFredholmSectionTame`); an sc-complement is in particular an
  algebraic complement (level `0`).
* A assumes `S ≠ ∅`; for `S = ∅` B's conclusion holds with the empty atlas.
* `IsManifoldWithCornersLoc` is `HasCornerStructure` (`hasCornerStructure_iff_finiteDimensional`).

**Refresh 2026-11-02 (germ reading at HEAD).**  `theorem_3_57` and `theorem_3_57_dim` now state
the germ reading, and A gains `theorem_3_57_sc` (good position with the text's sc-complement).
A ⇒ B still goes through `theorem_3_57`; the chart change `isGoodPositionGermTame_of_B` was
repaired (`isGoodPositionGerm_of_linAt_surj` on `Lin(z)`).  B ⇒ A still fails.
-/

namespace RoundTrip.V3_87
open Polyfold

/-- The project's statement: Theorem 3.57 (germ reading), its fixed-dimension form, Theorem 3.27
with locally constant dimension, and Theorem 3.57 with the sc-complement form of good position,
universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_57.{0, 0} ∧ type_of% @Polyfold.theorem_3_57_dim.{0, 0} ∧
    type_of% @Polyfold.theorem_3_27_loc.{0} ∧ type_of% @Polyfold.theorem_3_57_sc.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_57.{0, 0}, @Polyfold.theorem_3_57_dim.{0, 0}, @Polyfold.theorem_3_27_loc.{0},
    @Polyfold.theorem_3_57_sc.{0, 0}⟩

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

/-- B's conclusion for an empty set: the empty atlas. -/
theorem empty_case {S : Set X} (hS : ¬ S.Nonempty) :
    ∃ (hsub : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
      (PX.subPolyfold hsub).IsTame ∧ (PX.subPolyfold hsub).HasCornerStructure := by
  have hsub : PX.IsSubMPolyfold S := fun a ha => absurd ⟨a, ha⟩ hS
  have hpc := PX.paracompactSpace_subtype S
  have hcorner : (PX.subPolyfold hsub).HasCornerStructure := by
    refine ⟨⟨∅, fun φ hφ => absurd hφ (Set.notMem_empty φ), fun y => absurd ⟨y.1, y.2⟩ hS⟩,
      (MAtlas.equiv_iff _ _).2 fun φ hφ => absurd hφ (Set.notMem_empty φ),
      fun φ hφ => absurd hφ (Set.notMem_empty φ)⟩
  exact ⟨hsub, hpc, hcorner.isTame, hcorner⟩

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f _ hf hgood
  have hall : ∀ x, IsZeroAt P f x → Bd.IsGoodPositionGermTame f x := fun x hx =>
    isGoodPositionGermTame_of_B hf hx (hgood x hx)
  by_cases hne : (solutionSet P f).Nonempty
  · have := PX.paracompactSpace_subtype (solutionSet P f)
    obtain ⟨hsub, h1, h2, -⟩ := hA.1 hf.toIsScFredholmSection hall hne
    exact ⟨hsub, inferInstance, h1, MPolyfold.hasCornerStructure_iff_finiteDimensional.2 h2⟩
  · exact empty_case hne

#rt_check RoundTrip.V3_87.A_to_B [Polyfold.theorem_3_57, Polyfold.theorem_3_57_dim,
  Polyfold.theorem_3_27_loc, Polyfold.theorem_3_57_sc]

end RoundTrip.V3_87
